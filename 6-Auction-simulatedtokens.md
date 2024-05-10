# Auction Contract (with Tokens)

## Description

This is a smart contract that represents an auction (while being slightly naive by implementing all core logic, including the use of a token to be auctioned). The creator begins the auction with the initial bid, subsequent bids are accepted by the contract if they're higher than the specific increment defined in the contract (10). If a new bid is accepted, the previous bid is returned to the original bidder. Once the defined end auction timeslot has passed, the collect endpoint pays the winning bid to the auction creator and sends the token(s) to the winner of the auction.

This example like the tokenless auction, showcases datum, intervals, and scirpt validations combined with different spending paths, but adds also token handling that forces to split the total value into the ada component and token component.

### Tokens

This example creates a new currency with symbol "66" (corresponding to `ValidatorHash "f"` ) and token name "ValuableToken"  (corresponding to `TokenName "ValuableToken"`)
which is the token to be auctioned.

## Code

(NOTE: use plutus playground commit 47bee0d683857655d60c230a8b25ab7058c54d55)

```haskell
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE BangPatterns               #-}

import qualified Data.ByteString.Char8     as C

import qualified Prelude

import           Control.Monad                     (void, when, fmap)
import qualified Data.Map                          as Map
import qualified Data.Text                         as T
import           Data.Maybe                        (fromJust, catMaybes)

import           Plutus.Contract          hiding (when)
import qualified Plutus.Contract.Typed.Tx as Typed
import qualified PlutusTx                
import           PlutusTx.Prelude         hiding (Semigroup (..), fold)
import           Ledger                            
import qualified Ledger.Ada                        as Ada
import           Ledger.Constraints                (TxConstraints, mustBeSignedBy, mustPayToTheScript, mustValidateIn, mustPayToPubKey)
import           Ledger.Contexts                   (TxInfo (..), ScriptContext (..), TxInInfo(..), findOwnInput, ownHash)
import qualified Ledger.Contexts                   as Validation
import qualified Ledger.Interval                   as Interval
import           Ledger.Interval                   (before, after, ivFrom, ivTo, interval)
import qualified Ledger.Slot                       as Slot
import qualified Ledger.Tx                         as Tx
import qualified Ledger.Typed.Scripts              as Scripts
import           Ledger.Value                      (Value, currencySymbol, tokenName, CurrencySymbol, TokenName, valueOf)
import qualified Ledger.Value                      as Value
import           Playground.Contract
import           Wallet.Emulator.Types             (walletPubKey)

import           Data.Aeson           (ToJSON, FromJSON)
import           Data.Void            (Void)
import           GHC.Generics         (Generic)
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Ada           as Ada
import           Playground.Contract  (printJson, printSchemas, ensureKnownCurrencies, stage, ToSchema)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (Semigroup (..))

import           Text.Printf          (printf)

------------------------------------------------------------


-- | Auction config parameters
bidIncrease  = 10
auctionFinish = Slot 20

-- | Helper functions

--
lovelaceValue :: Value -> Integer
lovelaceValue value = Ada.getLovelace $ Ada.fromValue value

--
extractComponent :: Value -> CurrencySymbol -> TokenName -> Value
extractComponent value currency token = Value.singleton currency token $ valueOf value currency token

--
extractAdaValue :: Value -> Value
extractAdaValue value =  extractComponent value adaSymbol adaToken

-- 
datumToData :: (PlutusTx.IsData a) => Datum -> Maybe a
datumToData datum = PlutusTx.fromData (getDatum datum)

-- | Datum and redeemer parameter types
data Auction
instance Scripts.ScriptType Auction where
    type instance RedeemerType Auction = ()
    type instance DatumType Auction = AuctionData


data AuctionData = AuctionData{
      owner          :: PubKeyHash
    , previousBidder :: PubKeyHash
    , cpCurrency :: !CurrencySymbol
    , cpToken    :: !TokenName
    } deriving (Generic)

PlutusTx.makeLift ''AuctionData
PlutusTx.makeIsDataIndexed ''AuctionData [('AuctionData,0)]

{-# INLINABLE extractValue #-}
extractValue :: Maybe TxInInfo -> Value
extractValue (Just TxInInfo{txInInfoResolved=Tx.TxOut{txOutValue=value}}) = value

{-# INLINABLE validate #-}
validate :: AuctionData -> () -> ScriptContext -> Bool
validate AuctionData{owner=ownerInDatum,previousBidder, cpCurrency, cpToken} () ctx@ScriptContext{scriptContextTxInfo=txInfo@TxInfo{txInfoValidRange=txValidRange@Interval.Interval{ivFrom, ivTo}}} =
    let
        -- extract the start and end slots of the transaction
        -- (in this example, is easier to read the interval logic comparing the actual start/end slots)
        Interval.LowerBound (Interval.Finite txValidFrom) _ = ivFrom
        Interval.UpperBound (Interval.Finite txValidTo) _ = ivTo

        -- find the output for this validation script (it should be only one)
        [auctionOuputUtxo] = Validation.scriptOutputsAt (ownHash ctx) txInfo

    
        -- amount of the previous transaction
        currentBid =  lovelaceValue $ extractValue $ findOwnInput ctx
        
    in
        -- if the transaction start slot is after the auction finish slot, pay to owner
        -- if  txValidRange `after` auctionFinish then 
       if auctionFinish `before` txValidRange then
            -- collect spending path
            let
                -- amount paid in this transaction to the owner of the auction
                paidToOwner = lovelaceValue $ Validation.valuePaidTo txInfo ownerInDatum
                winner = previousBidder
                paidToWinner = Validation.valuePaidTo txInfo winner
                tokenValue = Value.singleton cpCurrency cpToken 1
            in                  
                (traceIfFalse "Winning bid not paid to owner" $ paidToOwner == currentBid )
                 && (traceIfFalse "Token not paid to winner" $ tokenValue == paidToWinner )
        else
            let 
                -- new bid is the value paid to this script in this transaction
                newBid  =   lovelaceValue $ Validation.valueLockedBy txInfo (ownHash ctx)
                -- amount paid in this transaction to the previous bidder
                paidToPrevBidder = lovelaceValue $ Validation.valuePaidTo txInfo previousBidder                     
                -- get current token 
                preservedToken =  valueOf (extractValue $ findOwnInput ctx) cpCurrency cpToken
                -- extract the owner in the new datum
                Just AuctionData{owner=currentOwnerInDatum} =  do
                                datum <- Validation.findDatum (fst $  auctionOuputUtxo ) txInfo
                                datumToData datum
            in 
                --bid spending path
                -- ensure the new bid is greater than current + delta
                (traceIfFalse "Not enough bid increase" $ newBid > (currentBid + bidIncrease))
                -- ensure the current bid is returned to the bidder that placed it
                && (traceIfFalse "Previous bid not paid" $ currentBid == paidToPrevBidder  )
                -- the transaction end slot should be before the auction end slot
                &&  (traceIfFalse "Auction already over" $ txValidTo <= auctionFinish )
                -- the owner of the auction is preserved in the datum
                &&  (traceIfFalse "Owner not preserved" $ ownerInDatum == currentOwnerInDatum )
                -- ensure token is kept
                &&  (traceIfFalse "Token not preserved" $ preservedToken == 1 )



auctionInstance :: Scripts.ScriptInstance Auction
auctionInstance  = Scripts.validator @Auction
    $$(PlutusTx.compile [|| validate ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @AuctionData @()

auctionAddress :: Address
auctionAddress = Ledger.scriptAddress (Scripts.validatorScript auctionInstance)


data StartParams = StartParams
    { startBidAmount :: Integer
      , aCurrency :: !CurrencySymbol
      , aToken    :: !TokenName
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON,  ToSchema)

data BidParams = BidParams
    { bidAmount :: Integer
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON,  ToSchema)

type AuctionSchema =
    BlockchainActions
        .\/ Endpoint "1-startAuction" StartParams
        .\/ Endpoint "2-bid" BidParams
        .\/ Endpoint "3-collect" ()


{-# INLINABLE extractData #-}
extractData :: (PlutusTx.IsData a) => TxOutTx -> Maybe a
extractData txOut = do
                        datum <- txOutTxDatum txOut
                        datumToData datum

-- | Start the auction
startAuction :: Contract () AuctionSchema T.Text ()
startAuction = do
                StartParams basePrice cpCurrency cpToken <- endpoint @"1-startAuction" @StartParams
                owner <- pubKeyHash <$> ownPubKey            
                let 
                    tokenValue = Value.singleton cpCurrency cpToken 1
                    value = ( Ada.lovelaceValueOf basePrice) <> tokenValue
                    tx = mustPayToTheScript AuctionData{owner,previousBidder=owner, cpCurrency, cpToken} value 
                ledgerTx <- submitTxConstraints auctionInstance tx
                void $ awaitTxConfirmed $ txId ledgerTx    


-- | Bid in the auction
bid :: Contract () AuctionSchema T.Text ()
bid = do
    BidParams newBid <- endpoint @"2-bid" @BidParams
    unspentOutputs <- utxoAt auctionAddress
    let
        txOuts = Map.elems unspentOutputs    
        AuctionData{owner, previousBidder, cpCurrency, cpToken} = head $ catMaybes ( map extractData  txOuts )  -- Even if there's more than one utxo, they should all have the same datum
        previousBid  = lovelaceValue $ Prelude.foldl1 (<>) $ map (txOutValue.txOutTxOut) txOuts
    if newBid > (previousBid + bidIncrease) then
        do
            newBidder <- pubKeyHash <$> ownPubKey
            let
                newBidAndToken  = ( Ada.lovelaceValueOf newBid) <> Value.singleton cpCurrency cpToken 1
                txAddBid        = mustPayToTheScript AuctionData{owner,previousBidder=newBidder, cpCurrency, cpToken} newBidAndToken
                txPayToPrevious = mustPayToPubKey previousBidder (Ada.lovelaceValueOf previousBid)
                txValidRange    = mustValidateIn $ interval (Slot 1) auctionFinish
                txCollect       = collectFromScript unspentOutputs ()
                tx = txCollect <> txAddBid <> txPayToPrevious <> txValidRange
            void (submitTxConstraintsSpending auctionInstance unspentOutputs tx)
    else
        throwError $ T.unwords
            [ "Bid must be greater than"
            , T.pack (show (previousBid + bidIncrease)) `T.append` "."
            ]

-- | Collect the winning bid and pay to owner
collect :: Contract () AuctionSchema T.Text ()
collect = do
            endpoint @"3-collect" @()
            unspentOutputs <- utxoAt auctionAddress
            logInfo @String "Collect"
            let
                txOuts = Map.elems unspentOutputs
                AuctionData{owner, previousBidder=winner, cpCurrency, cpToken} = head $ catMaybes ( map extractData  txOuts )                
                winningBid   = Prelude.foldl1 (<>) $ map (txOutValue.txOutTxOut) txOuts
                txCollect    = collectFromScript unspentOutputs ()
                payToOwner   = mustPayToPubKey owner $ extractComponent winningBid adaSymbol adaToken -- only the Ada component
                tokenValue = Value.singleton cpCurrency cpToken 1
                payToWinner  = mustPayToPubKey winner tokenValue
                txValidRange = mustValidateIn $  Interval.from (auctionFinish + 1)
                tx           = txCollect <> payToOwner <> txValidRange <> payToWinner
            void (submitTxConstraintsSpending auctionInstance unspentOutputs tx)

endpoints :: Contract () AuctionSchema T.Text ()
endpoints = startAuction `select` bid `select` collect

mkSchemaDefinitions ''AuctionSchema

myToken :: KnownCurrency
myToken = KnownCurrency (ValidatorHash "f") "Token" (TokenName "ValuableToken" :| [])

mkKnownCurrencies ['myToken]

```

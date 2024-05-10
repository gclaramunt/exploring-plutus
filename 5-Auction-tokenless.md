# Auction Contract (Tokenless)

## Description

This is a smart contract that represents an auction (while being slightly naive by implementing all core logic, but not including the use of tokens). The creator begins the auction with the initial bid, subsequent bids are accepted by the contract if they're higher than the specific increment defined in the contract (10). If a new bid is accepted, the previous bid is returned to the original bidder. Once the defined end auction timeslot has passed, the collect endpoint pays the winning bid to the auction creator. Because this is tokenless, the winning bidder does not receive anything. In the future a full-fledged auction example will be implemented with proper token support as well.

This example showcases datum, intervals, and scirpt validations combined with different spending paths.

## Code

(NOTE: use plutus playground commit 47bee0d683857655d60c230a8b25ab7058c54d55)

```haskell
import qualified Data.ByteString.Char8     as C

import qualified Prelude

import           Control.Monad                     (void, when)
import qualified Data.Map                          as Map
import qualified Data.Text                         as T
import           Data.Maybe                        (catMaybes)

import           Plutus.Contract          hiding (when)
import qualified Plutus.Contract.Typed.Tx as Typed
import           PlutusTx
import           PlutusTx.Prelude         
import           Ledger                            (Address, Slot (Slot), Validator, pubKeyHash, txOutTxDatum, txOutValue, txOutTxOut, TxOut, ScriptContext, Value, scriptAddress, PubKeyHash, Datum(..), TxOutTx, PubKeyHash (..) )
import qualified Ledger.Ada                        as Ada
import           Ledger.Constraints                (TxConstraints, mustBeSignedBy, mustPayToTheScript, mustValidateIn, mustPayToPubKey)
import           Ledger.Contexts                   (TxInfo (..), ScriptContext (..), TxInInfo(..), findOwnInput, ownHash)
import qualified Ledger.Contexts                   as Validation
import qualified Ledger.Interval                   as Interval
import           Ledger.Interval                   (before, after, ivFrom, ivTo, interval)
import qualified Ledger.Slot                       as Slot
import qualified Ledger.Tx                         as Tx
import qualified Ledger.Typed.Scripts              as Scripts
import           Ledger.Value                      (Value, currencySymbol, tokenName)
import qualified Ledger.Value                      as Value
import           Playground.Contract
import           Wallet.Emulator.Types             (walletPubKey)
------------------------------------------------------------

-- | Auction config parameters
bidIncrease  = 10
auctionFinish = Slot 20

-- | Helper functions
{-# INLINABLE lovelaceValue #-}
lovelaceValue :: Value -> Integer
lovelaceValue value = Ada.getLovelace $ Ada.fromValue value

{-# INLINABLE datumToData #-}
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
    } deriving (Generic)

PlutusTx.makeLift ''AuctionData
PlutusTx.unstableMakeIsData ''AuctionData

{-# INLINABLE validate #-}
validate :: AuctionData -> () -> ScriptContext -> Bool
validate AuctionData{owner=ownerInDatum,previousBidder} () ctx@ScriptContext{scriptContextTxInfo=txInfo@TxInfo{txInfoValidRange=txValidRange@Interval.Interval{ivFrom, ivTo}}} =
    let
        -- extract the start and end slots of the transaction
        -- (in this example, is easier to read the interval logic comparing the actual start/end slots)
        Interval.LowerBound (Interval.Finite txValidFrom) _ = ivFrom
        Interval.UpperBound (Interval.Finite txValidTo) _ = ivTo

        -- find the output for this validation script (it should be only one)
        [auctionOuputUtxo] = Validation.scriptOutputsAt (ownHash ctx) txInfo

        -- new bid is the value paid to this script in this transaction
        newBid  =   lovelaceValue $ Validation.valueLockedBy txInfo (ownHash ctx)

        -- amount paid in this transaction to the previous bidder
        paidToPrevBidder = lovelaceValue $ Validation.valuePaidTo txInfo previousBidder

        -- amount of the previous transaction
        Just ownInput = findOwnInput ctx
        currentBid = lovelaceValue $ txOutValue $ txInInfoResolved ownInput


        Just AuctionData{owner=currentOwnerInDatum} =  do
                                datum <- Validation.findDatum (fst $  auctionOuputUtxo ) txInfo
                                datumToData datum
    in
        -- if the transaction start slot is after the auction finish slot, pay to owner
        if auctionFinish `before` txValidRange then
            -- collect spending path
            let
                -- amount paid in this transaction to the owner of the auction
                paidToOwner = lovelaceValue $ Validation.valuePaidTo txInfo ownerInDatum
                -- ensure all of the current bid is paid to the owner
            in
                traceIfFalse "Winning bid not paid to owner" $ paidToOwner == currentBid
        else
           --bid spending path
           -- ensure the new bid is greater than current + delta
           (traceIfFalse "Not enough bid increase" $ newBid > (currentBid + bidIncrease))
           -- ensure the current bid is returned to the bidder that placed it
           && (traceIfFalse "Previous bid not paid" $ currentBid == paidToPrevBidder)
           -- the transaction end slot should be before the auction end slot
           &&  (traceIfFalse "Bid period expired" $ txValidTo <= auctionFinish)
           -- the owner of the auction is preserved in the datum
           &&  (traceIfFalse "Owner not preserved" $ ownerInDatum == currentOwnerInDatum)


auctionInstance :: Scripts.ScriptInstance Auction
auctionInstance  = Scripts.validator @Auction
    $$(PlutusTx.compile [|| validate ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @AuctionData @()

auctionAddress :: Address
auctionAddress = Ledger.scriptAddress (Scripts.validatorScript auctionInstance)

-- | Parameters for the "bid" endpoint
data BidParams = BidParams
    { bidAmount :: Integer
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)


type AuctionSchema =
    BlockchainActions
        .\/ Endpoint "1-startAuction" BidParams
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
                BidParams basePrice <- endpoint @"1-startAuction" @BidParams
                owner <- pubKeyHash <$> ownPubKey
                let tx = mustPayToTheScript AuctionData{owner,previousBidder=owner} ( Ada.lovelaceValueOf basePrice)
                void (submitTxConstraints auctionInstance tx)


-- | Bid in the auction
bid :: Contract () AuctionSchema T.Text ()
bid = do
    BidParams newBid <- endpoint @"2-bid" @BidParams
    unspentOutputs <- utxoAt auctionAddress
    let
        txOuts = Map.elems unspentOutputs
        AuctionData{owner, previousBidder} = head $ catMaybes ( map extractData  txOuts )  -- Even if there's more than one utxo, they should all have the same datum
        previousBid  = lovelaceValue $ Prelude.foldl1 (Prelude.<>) $ map (txOutValue.txOutTxOut) txOuts
    if newBid > (previousBid + bidIncrease) then
        do
            newBidder <- pubKeyHash <$> ownPubKey
            let
                txAddBid        = mustPayToTheScript AuctionData{owner,previousBidder=newBidder} $ ( Ada.lovelaceValueOf newBid)
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
            let
                txOuts = Map.elems unspentOutputs
                AuctionData{owner} = head $ catMaybes ( map extractData  txOuts )
                winningBid   = Prelude.foldl1 (<>) $ map (txOutValue.txOutTxOut) txOuts
                txCollect    = collectFromScript unspentOutputs ()
                payToOwner   = mustPayToPubKey owner winningBid
                txValidRange = mustValidateIn $  Interval.from (auctionFinish + 1)
                tx           = txCollect <> payToOwner <> txValidRange
            void (submitTxConstraintsSpending auctionInstance unspentOutputs tx)

endpoints :: Contract () AuctionSchema T.Text ()
endpoints = startAuction `select` bid `select` collect

mkSchemaDefinitions ''AuctionSchema

```

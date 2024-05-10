# Governance (voting power with tokens)

## Description

This is a smart contract that represent a governance voting scheme with tokens, where participants vote for an address (either a wallet or a script), and the winning choice gets paid all the treasury.
Participants must use special tokens to vote and can vote for many options with more than one token for each.

First, the organizer sets up the treasury with the desired funds, and then the group votes for the address that will take over the all the funds.
People submits the vote to the voting contract, and then, the votes are collected and submitted to the treasury, where after validation, transfer all the treasury to the winner choice.
Votes are preserved and can be recalled or retrieved after the voting.

### Structure

#### Validator scripts

The governance uses two validator scripts:
`voteScript` where votes are sent and held until the agreed quorum is reached
`treasuryScript` where the initial funds of the treasury are held and from where the reward is paid.

#### Endpoints

- 1-setup treasury
    Transfer funds to the treasury
- 2-vote wallet
    Locks the user choice of a wallet into a utxo
- 3-vote script
    Locks the user choice of a script into a utxo
- 5-collect
    If it finds enough votes, pays the money from the treasury while rebuilding the votes utxo
- 6-return vote
    Returns the vote to the originator, can be either before or after the final count.
    (Due limitations of the simulator, the origin wallet must be specified)

## Code

(NOTE: use plutus playground commit 47bee0d683857655d60c230a8b25ab7058c54d55)

```haskell
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}

import qualified Data.Text                 as T
import           Plutus.Contract  hiding (when)
-- ScriptLookups semigroup is defined based on the standard prelude <> and doesn't like the plutus one
import           PlutusTx.Prelude hiding  ((<>)) 
import qualified PlutusTx                 as PlutusTx
import           PlutusTx.AssocMap        (fromList, member)
import           Playground.Contract
import           Control.Monad                     (void, when) 
import           Ledger                            (Address (..), Slot (Slot), Validator, txOutTxDatum, txOutValue, txOutTxOut, TxOut, ScriptContext (..), Value, scriptAddress, Datum(..), TxOutTx, PubKeyHash (..), validatorHash, outValue, TxInfo (..), DatumHash, TxInInfo(..), toValidatorHash, pubKeyHash, toPubKeyHash, unitDatum ) 
import qualified Ledger.Value                      as Value 
import           Ledger.Value                      (Value, currencySymbol, tokenName, CurrencySymbol, TokenName)
import qualified Ledger.Typed.Scripts              as Scripts
import qualified Data.Map                          as Map
import           Data.List                         (groupBy, maximumBy, partition, sortBy) 
import           Data.Ord                          (comparing)
import qualified Data.Set                          as Set 
import qualified Ledger.Ada                        as Ada
import           Data.Maybe                        (catMaybes)
import           Ledger.Constraints                (TxConstraints, mustBeSignedBy, mustPayToTheScript, mustValidateIn, mustPayToPubKey, mustPayToOtherScript, scriptInstanceLookups,SomeLookupsAndConstraints (..), mkSomeTx, unspentOutputs, ScriptLookups(..) )
import qualified Ledger.Contexts                   as Validation
import           Ledger.Contexts                   (TxOut(..), findOwnInput)
import           Wallet.Emulator.Types             (Wallet, walletPubKey)
import qualified Wallet.Emulator.Wallet            as Wallet
import qualified Prelude
import qualified Data.Foldable  as Foldable 
import           Control.Lens

import           Data.Semigroup                   

import Data.List.Extra (notNull)

-- minimum number of agreement votes required
quorum = 4

currency = "66" 
token = "VotingToken"

-- Vote
buildVote :: Integer -> Value
buildVote weight =  Value.singleton currency token weight

-- UTILITY FUNCTIONS

-- onchain

-- the standard Maybe.fromJust don't work onchain
{-# INLINABLE fromJust #-}
fromJust :: Maybe a -> a
fromJust (Just a) = a

{-# INLINABLE datumToData #-}
datumToData :: (PlutusTx.IsData a) => Datum -> Maybe a
datumToData datum = PlutusTx.fromData (getDatum datum)


{-# INLINABLE extractData #-}
extractData :: (PlutusTx.IsData a) => TxOutTx -> Maybe a
extractData txOut = do
                        datum <- txOutTxDatum txOut
                        datumToData datum   


{-# INLINABLE validatorHashOf #-}
validatorHashOf :: TxInInfo -> Maybe ValidatorHash
validatorHashOf = toValidatorHash . txOutAddress . txInInfoResolved

{-# INLINABLE datumHashOf #-}
datumHashOf :: TxInInfo -> DatumHash
datumHashOf = fromJust . txOutDatumHash . txInInfoResolved

{-# INLINABLE valueOf #-}
valueOf :: TxInInfo -> Value
valueOf = txOutValue . txInInfoResolved

data VoteDatum = VoteDatum {   
      votedAddress    :: Address,
      weight          :: Integer,
      owner           :: PubKeyHash
    } deriving (Generic, Show)

PlutusTx.makeLift ''VoteDatum
PlutusTx.makeIsDataIndexed ''VoteDatum [('VoteDatum,0)]


{-# INLINABLE extractVote #-}
extractVote :: TxOutTx -> VoteDatum
extractVote txo = fromJust (extractData txo)

{-# INLINABLE findExtractData #-}
findExtractData :: DatumHash -> TxInfo -> VoteDatum
findExtractData dh txInfo = fromJust(datumToData (fromJust (Validation.findDatum dh txInfo)))

-- offchain
extractAddress :: TxOutTx -> Address 
extractAddress tx = votedAddress (extractVote tx)

extractOwner :: TxOutTx -> PubKeyHash 
extractOwner tx = owner (extractVote tx)

extractComponent :: Value -> CurrencySymbol -> TokenName -> Value
extractComponent value currency token = Value.singleton currency token $ Value.valueOf value currency token

findMostVotedGroupGeneric :: Prelude.Ord c => ([a]->c) -> (a -> a -> Ordering) -> [a] -> [a]
findMostVotedGroupGeneric groupEval orderer elements = 
                let 
                    -- create an equality comparation from an ordering
                    grouper a b = isEq (a `orderer` b) 
                                    where 
                                        isEq EQ = True
                                        isEq _ = False
                    -- group by equality ( sorting first, as it only groups adjacents)
                    groups  = groupBy grouper $ sortBy orderer elements
                in
                    -- get the "top" list
                    maximumBy (comparing groupEval) groups


-- instance PlutusTx.Ord Address where                    

findMostVotedGroup = findMostVotedGroupGeneric sumVotes compareWalletAndPayout where 
                        compareWalletAndPayout (_,x) (_,y) = extractAddress x `Prelude.compare` extractAddress y

sumVotes :: [(TxOutRef, TxOutTx)] -> Integer
sumVotes votes = Value.valueOf value currency token where value = mconcat $ fmap (txOutValue.txOutTxOut.snd) votes

-- ONCHAIN VALIDATORS

-- toy target script 
-- | Datum and redeemer parameter types
data TargetScript
instance Scripts.ScriptType TargetScript where
    type instance RedeemerType TargetScript = Integer
    type instance DatumType TargetScript = Integer

-- | The script instance is the compiled validator (ready to go onto the chain)
targetInstance :: Scripts.ScriptInstance TargetScript
targetInstance = Scripts.validator @TargetScript
    $$(PlutusTx.compile [|| targetValidator ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @Integer @Integer

-- | This method is the spending validator (which gets lifted to
--   its on-chain representation).
--   validate that the square of the proposed value is the expected solution
targetValidator :: Integer -> Integer -> ScriptContext -> Bool
targetValidator y x _ = x == y

targetScriptAddress :: Address
targetScriptAddress = Ledger.scriptAddress (Scripts.validatorScript targetInstance)

-- Vote script

data Vote
instance Scripts.ScriptType Vote where
    type instance RedeemerType Vote = ()
    type instance DatumType Vote = VoteDatum


{-# INLINABLE voteScript #-}
voteScript  ::  CurrencySymbol -> TokenName -> ValidatorHash -> VoteDatum -> () -> ScriptContext -> Bool 
voteScript currency token treasury VoteDatum{owner=voteOwner, weight=votePower} _ ctx@ScriptContext{scriptContextTxInfo=txInfo@TxInfo{txInfoInputs}} =              
                        let 
                            buildVote weight = Value.singleton currency token weight
                            -- Spending path 1: The vote must be spent with the treasury in the same transaction
                            -- (check that the treasury hash is present in the inputs)
                            collectVotesAction = traceIfFalse " **** Must be spent together with the treasury" $ any (\txInInfo -> validatorHashOf txInInfo == Just treasury) txInfoInputs 
                            -- or
                            -- Spending path 2: The vote must be returned to the owner
                            returnVoteAction =  traceIfFalse " **** Vote must be paid back to owner" $ Validation.valuePaidTo txInfo voteOwner == buildVote votePower
                        in
                             collectVotesAction || returnVoteAction 
                        

voteScriptInstance :: ValidatorHash -> Scripts.ScriptInstance Vote
voteScriptInstance treasuryHash = Scripts.validator @Vote
    ($$(PlutusTx.compile [|| voteScript ||]) `PlutusTx.applyCode` PlutusTx.liftCode currency `PlutusTx.applyCode` PlutusTx.liftCode token `PlutusTx.applyCode` PlutusTx.liftCode treasuryHash)
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @VoteDatum @()


voteScriptAddress :: ValidatorHash -> Address
voteScriptAddress treasuryHash = Ledger.scriptAddress (Scripts.validatorScript ( voteScriptInstance treasuryHash))

-- Treasury script
data Treasury
instance Scripts.ScriptType Treasury where
    type instance RedeemerType Treasury = ()
    type instance DatumType Treasury = ()


{-# INLINABLE treasuryScript #-}
treasuryScript  :: CurrencySymbol -> TokenName -> () -> () -> ScriptContext -> Bool 
treasuryScript currency token _ _ ctx@ScriptContext{scriptContextTxInfo=txInfo@TxInfo{txInfoInputs, txInfoOutputs}} = 
                    let                         


                        -- split the inputs by partition looking for the input that has the hash of the current script (treasury)
                        -- first, filter the wallet that pays the fee
                        onlyScriptsUtxos = filter ( isJust . validatorHashOf) txInfoInputs 
                        -- the result should be a list of votes (all the for the same address and amount) and one input from the treasury                
                        ([treasury], allVotes@(aVote:_) ) = partition (\txInInfo -> Just (Validation.ownHash ctx) == validatorHashOf txInInfo) onlyScriptsUtxos
                        -- extract the datum from the first vote 
                        aVoteDatum = fromJust (Validation.findDatum (datumHashOf aVote) txInfo)

                        sumAllVotes = Value.valueOf value currency token where value = mconcat $ fmap (txOutValue.txInInfoResolved) allVotes

                        -- validate all the votes have the same voted wallet and same payout
                        compareDatums d1 d2 = 
                                let 
                                    data1 = findExtractData d1 txInfo
                                    data2 = findExtractData d2 txInfo
                                in
                                    votedAddress data1 == votedAddress data2 

                        allVotesAreTheSame =  traceIfFalse " **** Not all votes are the same" $ all (True == ) $ 
                            fmap (\voteTxInfo -> compareDatums (datumHashOf (aVote)) (datumHashOf voteTxInfo)  ) allVotes         

                        -- validate the voted address is paid with the voted amount
                        voteData = fromJust(datumToData aVoteDatum)
                        votedAddressFromData = votedAddress voteData       

                        valueInTreasury = valueOf treasury

                        paidToVotedUtxos = filter (\TxOut{txOutAddress, txOutValue} -> txOutAddress == votedAddressFromData && txOutValue ==  valueInTreasury ) txInfoOutputs
                        ensureVotedIsPaid =  traceIfFalse " **** Voted address is not paid the amount in treasury" $ length paidToVotedUtxos  == 1


                        -- validate the votes are preserved (input votes == output votes)    
                        outVotes = Validation.scriptOutputsAt ( fromJust (validatorHashOf aVote)) txInfo 
                        inVotesDatumAndValues =  fmap (\vote -> ( datumHashOf vote, valueOf vote))  allVotes
                        votesPreserved = let
                                            mapInVotes = fromList $ zip inVotesDatumAndValues inVotesDatumAndValues
                                            mapOutVotes = fromList $ zip outVotes outVotes
                                            inContainsAllOuts = all (\x -> member x mapInVotes) mapOutVotes  
                                            outContainsAllIns = all (\x -> member x mapOutVotes) mapInVotes
                                         in
                                            (traceIfFalse " **** Votes are not preserved: not all output votes have a corresponding input" $ inContainsAllOuts)
                                            && (traceIfFalse " **** Votes are not preserved: not all input votes have a corresponding output" $ outContainsAllIns)

                        -- validate enough votes    
                        quorumCheck = traceIfFalse " **** Not enough votes" (sumAllVotes >= quorum )

                    in 
                        quorumCheck 
                        && allVotesAreTheSame 
                        && ensureVotedIsPaid 
                        && votesPreserved
                        

treasuryScriptInstance :: Scripts.ScriptInstance Treasury
treasuryScriptInstance  = Scripts.validator @Treasury
    ($$(PlutusTx.compile [|| treasuryScript ||]) `PlutusTx.applyCode` PlutusTx.liftCode currency `PlutusTx.applyCode` PlutusTx.liftCode token )
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @() @()


treasuryScriptHash :: ValidatorHash
treasuryScriptHash = validatorHash $ Scripts.validatorScript treasuryScriptInstance

treasuryScriptAddress :: Address
treasuryScriptAddress = Ledger.scriptAddress (Scripts.validatorScript treasuryScriptInstance)


-- OFFCHAIN ENDPOINTS

type VotingSchema =
    BlockchainActions
        .\/ Endpoint "1-setup treasury" Integer
        .\/ Endpoint "2-vote wallet" VoteWalletParams
        .\/ Endpoint "3-vote script" VoteScriptParams
        .\/ Endpoint "4-collect" ()
        .\/ Endpoint "5-return vote" Wallet

-- Initialize the treasury with some value
setupTreasury :: Contract () VotingSchema T.Text ()
setupTreasury = do
                    trasuryAmount <- endpoint @"1-setup treasury" @Integer
                    let            
                        tx = mustPayToTheScript () ( Ada.lovelaceValueOf trasuryAmount) 
                    void (submitTxConstraints treasuryScriptInstance tx)


-- | Parameters for the "vote wallet" endpoint
data VoteWalletParams = VoteWalletParams
    { votedFor :: Wallet
    , votes    :: Integer
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

-- Vote for wallet
voteWallet :: Contract () VotingSchema T.Text ()
voteWallet= do
        VoteWalletParams votedFor votes <- endpoint @"2-vote wallet" @VoteWalletParams
        voter <- pubKeyHash <$> ownPubKey
        let
          votedforAddress = Wallet.walletAddress votedFor
          txAddVote = mustPayToTheScript VoteDatum{votedAddress=votedforAddress, weight = votes, owner=voter} $ buildVote votes
        void (submitTxConstraints (voteScriptInstance treasuryScriptHash) txAddVote)


-- | Parameters for the "vote script" endpoint
data VoteScriptParams = VoteScriptParams
    { scriptVotes    :: Integer
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

-- Vote for script
voteForScript :: Contract () VotingSchema T.Text ()
voteForScript= do
        VoteScriptParams votes <- endpoint @"3-vote script" @VoteScriptParams
        voter <- pubKeyHash <$> ownPubKey
        let
          txAddVote = mustPayToTheScript VoteDatum{votedAddress=targetScriptAddress, weight = votes, owner=voter} $ buildVote votes
        void (submitTxConstraints (voteScriptInstance treasuryScriptHash) txAddVote)

-- Tally votes endpoint
-- collect enough votes and spend the voted amount from the treasury to the winning choice
tally :: Contract () VotingSchema T.Text ()
tally = do        
            endpoint @"4-collect" @()
            votesUtxo <- utxoAt (voteScriptAddress treasuryScriptHash)
            treasuryUtxo <- utxoAt treasuryScriptAddress              
            collector <- pubKeyHash <$> ownPubKey
            let
                utxoList = Map.toList votesUtxo                 
                winningVotes = findMostVotedGroup utxoList
                winningUtxos = Map.fromList winningVotes 
                count = sumVotes winningVotes
        
            if count >= quorum then 
                let 
                    Just voteScriptHash = toValidatorHash $ voteScriptAddress treasuryScriptHash

                    -- collect from the winning utxos and the treasury
                    txVotesUtxos = collectFromScript winningUtxos ()
                    txInputTreasury = collectFromScript treasuryUtxo () 
                    
                    votedAddress = extractAddress (snd $ head winningVotes) 
                    datum = Datum $ PlutusTx.toData $ VoteDatum{votedAddress=votedAddress, weight=count, owner=collector}
                                
                    -- pay the voted amount from the treasury (and keep the remainder in the treasury)           
                    totalTreasury = foldMap (txOutValue . txOutTxOut) $  Map.elems treasuryUtxo 

                    -- pay to either a public key or a script address,     
                    payWinner (Just winningAddress) _ = mustPayToPubKey winningAddress totalTreasury
                    -- We use an empty datum, but we can require a datum from the voters or lookup an existing datum
                    payWinner  _ (Just winningScript) = mustPayToOtherScript winningScript unitDatum totalTreasury

                    txPayWinner = payWinner (toPubKeyHash votedAddress) (toValidatorHash votedAddress) 

                    -- rebuild spent votes
                    rebuildVote utxo =  mustPayToOtherScript voteScriptHash (fromJust (txOutTxDatum utxo)) $ txOutValue (txOutTxOut utxo)
                    txRebuildVotes = foldMap (rebuildVote.snd) winningVotes
                              
                    -- treasury script constraints          
                    treasuryUtxosConstraint = txInputTreasury <> txPayWinner 
                    treasuryLookups = (scriptInstanceLookups treasuryScriptInstance) <> (unspentOutputs treasuryUtxo)

                    -- vote script constraints
                    votesUtxosConstraint = txVotesUtxos <> txRebuildVotes
                    votesLookups = (scriptInstanceLookups (voteScriptInstance treasuryScriptHash) ) <> (unspentOutputs votesUtxo)

                    -- Since the treasury and vote's constraints and spends have to be on the same transaction, 
                    -- we can't use the standard submitTxConstraintsXXXX and we need to manually create the transaction  
                    treasurySpend = SomeLookupsAndConstraints treasuryLookups treasuryUtxosConstraint
                    voteSpend = SomeLookupsAndConstraints votesLookups votesUtxosConstraint
                    tx = mkSomeTx [treasurySpend, voteSpend]
                in                     
                  do
                    void $ do
                        tx <- either (throwError . review _ConstraintResolutionError) pure tx
                        submitUnbalancedTx tx
            else
                do 
                    logInfo @String "NOT ENOUGH VOTES"                                       
                    throwError $ T.pack "Not enough votes"

returnVote :: Contract () VotingSchema T.Text ()
returnVote = do
                    -- Should be 
                    -- voter <- pubKeyHash <$> ownPubKey
                    -- but the simulator doesn't allow multiple actions on wallets                    
                    wallet <- endpoint @"5-return vote" @Wallet
                    voteUtxos <- utxoAt (voteScriptAddress treasuryScriptHash)                     
                    let            
                        voteScript = voteScriptInstance treasuryScriptHash
                        voter = (pubKeyHash . walletPubKey) wallet                        
                        votesToReturnUtxos = Map.filter (\txOut -> voter == (extractOwner txOut)) voteUtxos                        
                        txPayToVoter = Foldable.fold $  Map.map  ( \utxo -> mustPayToPubKey voter ((txOutValue.txOutTxOut) utxo) ) votesToReturnUtxos
                        txVotesUtxos = collectFromScript votesToReturnUtxos ()
                        tx = txPayToVoter <> txVotesUtxos
                    void (submitTxConstraintsSpending voteScript votesToReturnUtxos tx)



endpoints :: Contract () VotingSchema T.Text ()
endpoints = setupTreasury  `select` voteWallet `select` voteForScript `select` tally `select` returnVote

mkSchemaDefinitions ''VotingSchema

votingToken :: KnownCurrency
votingToken = KnownCurrency (ValidatorHash "f") "Token" (TokenName "VotingToken" :| [])

mkKnownCurrencies ['votingToken]
```

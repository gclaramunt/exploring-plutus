# Governance (simple voting)

## Description

This is a smart contract that represent a simple governance with voting scheme where participants vote for a wallet and an amount, and the winning choice gets paid from a treasury.

First, the organizer sets up the treasury with enough funds for the reward and then the group votes for the wallet to award and the amount of funds.
People submits the vote to the voting contract, and then, the votes are collected and submitted to the treasury, where after validation, pays the winner.
Votes are preserved and can be recalled or retrieved after the voting.

### Structure

#### Validator scripts

The governance uses two validator scripts:
`voteScript` where votes are sent and held until the agreed quorum is reached
`treasuryScript` where the initial funds of the treasury are held and from where the reward is paid.

#### Endpoints

- 1-setup treasury
    Transfer funds to the treasury
- 2-vote
    Locks the user choice into a utxo
- 3-collect
    If it finds enough votes, pays the money from the treasury while rebuilding the votes utxo
- 4-return vote
    Returns the vote to the originator, can be either before or after the final count.
    (Due limitations of the simulator, the origin wallet must be specified)

## Code

(NOTE: use plutus playground commit 47bee0d683857655d60c230a8b25ab7058c54d55)

```haskell
import qualified Data.Text                 as T
import           Plutus.Contract  hiding (when)
-- ScriptLookups semigroup is defined based on the standard prelude <> and doesn't like the plutus one
import           PlutusTx.Prelude hiding  ((<>)) 
import qualified PlutusTx                 as PlutusTx
import           Playground.Contract
import           Control.Monad                     (void, when) 
import           Ledger                            (Address (..), Slot (Slot), Validator, pubKeyHash, txOutTxDatum, txOutValue, txOutTxOut, TxOut, ScriptContext (..), Value, scriptAddress, PubKeyHash, Datum(..), TxOutTx, PubKeyHash (..), validatorHash, outValue, TxInfo (..), DatumHash, TxInInfo(..), toValidatorHash, pubKeyHash, toPubKeyHash ) 
import qualified Ledger.Value                      as Value 
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
import qualified Prelude
import qualified Data.Foldable  as Foldable 
import           Control.Lens

import           Data.Semigroup                   

import Data.List.Extra (notNull)

-- minimum number of agreement votes required
quorum = 3
-- cost of one vote
oneVote = Ada.lovelaceValueOf 1

-- UTILITY FUNCTIONS

-- onchain

-- the standard Maybe.fromJust and List.sortOn don't work onchain
{-# INLINABLE fromJust #-}
fromJust :: Maybe a -> a
fromJust (Just a) = a

-- Classic Haskell fake quicksort (not a real quicksort, but is good enough)
{-# INLINABLE sort #-}
sort :: (Ord a) => [a] -> [a]
sort [] = []
sort (x:xs) =
  let smallerSorted = sort [a | a <- xs, a <= x]
      biggerSorted = sort [a | a <- xs, a > x]
  in  smallerSorted ++ [x] ++ biggerSorted

{-# INLINABLE datumToData #-}
datumToData :: (PlutusTx.IsData a) => Datum -> Maybe a
datumToData datum = PlutusTx.fromData (getDatum datum)

{-# INLINABLE findExtractData #-}
findExtractData :: DatumHash -> TxInfo -> VoteDatum
findExtractData dh txInfo = fromJust(datumToData (fromJust (Validation.findDatum dh txInfo)))

{-# INLINABLE extractData #-}
extractData :: (PlutusTx.IsData a) => TxOutTx -> Maybe a
extractData txOut = do
                        datum <- txOutTxDatum txOut
                        datumToData datum   

{-# INLINABLE extractVote #-}
extractVote :: TxOutTx -> VoteDatum
extractVote txo = fromJust (extractData txo)

{-# INLINABLE validatorHashOf #-}
validatorHashOf :: TxInInfo -> Maybe ValidatorHash
validatorHashOf = toValidatorHash . txOutAddress . txInInfoResolved

{-# INLINABLE datumHashOf #-}
datumHashOf :: TxInInfo -> DatumHash
datumHashOf = fromJust . txOutDatumHash . txInInfoResolved

{-# INLINABLE valueOf #-}
valueOf :: TxInInfo -> Value
valueOf = txOutValue . txInInfoResolved


-- offchain
extractWallet :: TxOutTx -> PubKeyHash 
extractWallet tx = votedWallet (extractVote tx)

extractPayout :: TxOutTx -> Integer 
extractPayout tx = payout (extractVote tx)

extractOwner :: TxOutTx -> PubKeyHash 
extractOwner tx = owner (extractVote tx)

findMostVotedGroup :: (a -> a -> Ordering) -> [a] -> [a]
findMostVotedGroup orderer elements = 
                let 
                    -- create an equality comparation from an ordering
                    grouper a b = isEq (a `orderer` b) 
                                    where 
                                        isEq EQ = True
                                        isEq _ = False
                    -- group by equality ( sorting first, as it only groups adjacents)
                    groups  = groupBy grouper $ sortBy orderer elements
                in
                    -- get the longest list
                    maximumBy (comparing length) groups

pubKeyHashOf :: Wallet -> PubKeyHash
pubKeyHashOf = pubKeyHash . walletPubKey


-- ONCHAIN VALIDATORS

-- Vote script
data VoteDatum = VoteDatum {   
      votedWallet     :: PubKeyHash,
      payout          :: Integer, 
      owner           :: PubKeyHash
    } deriving (Generic, Show)

PlutusTx.makeLift ''VoteDatum
PlutusTx.makeIsDataIndexed ''VoteDatum [('VoteDatum,0)]


data Vote
instance Scripts.ScriptType Vote where
    type instance RedeemerType Vote = ()
    type instance DatumType Vote = VoteDatum


{-# INLINABLE voteScript #-}
voteScript  ::  ValidatorHash -> VoteDatum -> () -> ScriptContext -> Bool 
voteScript treasury VoteDatum{owner=voteOwner} _ ctx@ScriptContext{scriptContextTxInfo=txInfo@TxInfo{txInfoInputs}} =                  
                        let 
                            -- Spending path 1: The vote must be spent with the treasury in the same transaction
                            -- (check that the treasury hash is present in the inputs)
                            collectVotesAction = traceIfFalse " **** Must be spent together with the treasury" $ any (\txInInfo -> validatorHashOf txInInfo == Just treasury) txInfoInputs 
                            -- or
                            -- Spending path 2: The vote must be returned to the owner
                            returnVoteAction =  traceIfFalse " **** Vote must be paid back to owner" $ Validation.valuePaidTo txInfo voteOwner == oneVote
                        in
                             collectVotesAction || returnVoteAction 

                        

voteScriptInstance :: ValidatorHash -> Scripts.ScriptInstance Vote
voteScriptInstance treasuryHash = Scripts.validator @Vote
    ($$(PlutusTx.compile [|| voteScript ||]) `PlutusTx.applyCode` PlutusTx.liftCode treasuryHash)
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
treasuryScript  ::  () -> () -> ScriptContext -> Bool 
treasuryScript _ _ ctx@ScriptContext{scriptContextTxInfo=txInfo@TxInfo{txInfoInputs, txInfoOutputs}} =                     
                    let                         


                        -- split the inputs by partition looking for the input that has the hash of the current script (treasury)
                        -- first, filter the wallet that pays the fee
                        onlyScriptsUtxos = filter ( isJust . validatorHashOf) txInfoInputs 
                        -- the result should be a list of votes (all the for the same address and amount) and one input from the treasury                
                        ([treasury], allVotes@(aVote:_) ) = partition (\txInInfo -> Just (Validation.ownHash ctx) == validatorHashOf txInInfo) onlyScriptsUtxos
                        -- extract the datum from the first vote 
                        aVoteDatum = fromJust (Validation.findDatum (datumHashOf aVote) txInfo)

                        -- validate all the votes have the same voted wallet and same payout
                        compareDatums d1 d2 = 
                                let 
                                    data1 = findExtractData d1 txInfo
                                    data2 = findExtractData d2 txInfo
                                in
                                    votedWallet data1 == votedWallet data2 && payout data1 == payout data2

                        allVotesAreTheSame =  traceIfFalse " **** Not all votes are the same" $ all (True == ) $ 
                            fmap (\voteTxInfo -> compareDatums (datumHashOf (aVote)) (datumHashOf voteTxInfo)  ) allVotes         

                        -- validate the voted wallet is paid with the voted amount
                        votedAddress = votedWallet (fromJust(datumToData aVoteDatum))          -- add PKH to be explicit 
                        votedAmount  = payout (fromJust(datumToData aVoteDatum))                           

                        paidToVotedUtxos = filter (\TxOut{txOutAddress, txOutValue} -> toPubKeyHash txOutAddress == Just votedAddress && txOutValue ==  Ada.lovelaceValueOf votedAmount )  txInfoOutputs
                        ensureVotedIsPaid =  traceIfFalse " **** Voted wallet is not paid the amount" $ length paidToVotedUtxos  == 1

                        -- validate the value is spent from the treasury
                        remainingInTreasury = Validation.valueLockedBy txInfo (Validation.ownHash ctx)
                        valueInTreasury = valueOf treasury
                        validTreasurySpend = traceIfFalse " **** Remainder value must be spend in the treasury" $ valueInTreasury == ( Ada.lovelaceValueOf votedAmount + remainingInTreasury)

                        -- validate the votes are preserved (input votes == output votes)    
                        outVotes = Validation.scriptOutputsAt ( fromJust (validatorHashOf aVote)) txInfo 
                        -- compare values
                        sameVotesValues = (fmap valueOf allVotes) == (fmap snd outVotes)
                        -- compare datums
                        sameVotesDatums = sort ( fmap datumHashOf allVotes)  == sort  (fmap fst outVotes)
                        votesPreserved = traceIfFalse " **** Votes are not preserved" $ sameVotesDatums && sameVotesValues

                        -- validate enough votes    
                        quorumCheck = traceIfFalse " **** Not enough votes" (length allVotes >= quorum )

                    in 
                        quorumCheck 
                        && allVotesAreTheSame 
                        && ensureVotedIsPaid 
                        && validTreasurySpend 
                        && votesPreserved
                       
                        

treasuryScriptInstance :: Scripts.ScriptInstance Treasury
treasuryScriptInstance  = Scripts.validator @Treasury
    $$(PlutusTx.compile [|| treasuryScript ||])
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
        .\/ Endpoint "2-vote" VoteParams
        .\/ Endpoint "3-collect" ()
        .\/ Endpoint "4-return vote" Wallet

-- Initialize the treasury with some value
setupTreasury :: Contract () VotingSchema T.Text ()
setupTreasury = do
                    trasuryAmount <- endpoint @"1-setup treasury" @Integer
                    let            
                        tx = mustPayToTheScript () ( Ada.lovelaceValueOf trasuryAmount) 
                    void (submitTxConstraints treasuryScriptInstance tx)


-- | Parameters for the "vote" endpoint
data VoteParams = VoteParams
    { votedFor :: Wallet
    , amount :: Integer
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

-- Vote 
vote :: Contract () VotingSchema T.Text ()
vote= do
        VoteParams votedFor amount <- endpoint @"2-vote" @VoteParams
        voter <- pubKeyHash <$> ownPubKey
        let
          votedforPKH = pubKeyHashOf votedFor
          txAddVote = mustPayToTheScript VoteDatum{votedWallet=votedforPKH, payout=amount, owner=voter} oneVote
        void (submitTxConstraints (voteScriptInstance treasuryScriptHash) txAddVote)


-- Tally votes endpoint
-- collect enough votes and spend the voted amount from the treasury to the winning choice
tally :: Contract () VotingSchema T.Text ()
tally = do        
            endpoint @"3-collect" @()
            votesUtxo <- utxoAt (voteScriptAddress treasuryScriptHash)
            treasuryUtxo <- utxoAt treasuryScriptAddress              
            collector <- pubKeyHash <$> ownPubKey
            let
                utxoList = Map.toList votesUtxo
                comparator (_,x) (_,y) = (extractWallet x,extractPayout x) `compare` (extractWallet y, extractPayout y) 
                winningVotes = findMostVotedGroup comparator utxoList
                winningUtxos = Map.fromList winningVotes 
                count = length winningVotes
        
            if count >= quorum then 
                let 
                    Just voteScriptHash = toValidatorHash $ voteScriptAddress treasuryScriptHash

                    -- collect from the winning utxos and the treasury
                    txVotesUtxos = collectFromScript winningUtxos ()
                    txInputTreasury = collectFromScript treasuryUtxo () 
                    
                    votedPayout = extractPayout $ snd.head $ winningVotes
                    winningWallet = extractWallet (snd $ head winningVotes) 
                    datum = Datum $ PlutusTx.toData $ VoteDatum{votedWallet=winningWallet, payout=votedPayout,owner=collector}
                                
                    -- pay the voted amount from the treasury (and keep the remainder in the treasury)           
                    totalTreasury = sum $ fmap (Ada.getLovelace. Ada.fromValue . txOutValue . txOutTxOut) $  Map.elems treasuryUtxo                                       
                    txPayWinner = mustPayToPubKey winningWallet ( Ada.lovelaceValueOf votedPayout)
                    txRepayTreasury = mustPayToOtherScript treasuryScriptHash datum ( Ada.lovelaceValueOf ( totalTreasury - votedPayout ))

                    -- rebuild spent votes
                    rebuildVote utxo =  mustPayToOtherScript voteScriptHash (fromJust (txOutTxDatum utxo)) oneVote 

                    rebuildVoteTxs = map (rebuildVote.snd) winningVotes
                    txRebuildVotes = Prelude.foldl1 (<>) rebuildVoteTxs
                              
                    -- treasury script constraints          
                    treasuryUtxosConstraint = txInputTreasury <> txPayWinner  <> txRepayTreasury
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
                    logInfo @String "Submit TX"
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
                    wallet <- endpoint @"4-return vote" @Wallet
                    voteUtxos <- utxoAt (voteScriptAddress treasuryScriptHash)                     
                    let            
                        voteScript = voteScriptInstance treasuryScriptHash
                        voter = pubKeyHashOf wallet                        
                        votesToReturnUtxos = Map.filter (\txOut -> voter == (extractOwner txOut)) voteUtxos                        
                        txPayToVoter = Foldable.fold $  Map.map  ( \utxo -> mustPayToPubKey voter ((txOutValue.txOutTxOut) utxo) ) votesToReturnUtxos
                        txVotesUtxos = collectFromScript votesToReturnUtxos ()
                        tx = txPayToVoter <> txVotesUtxos
                    void (submitTxConstraintsSpending voteScript votesToReturnUtxos tx)



endpoints :: Contract () VotingSchema T.Text ()
endpoints = setupTreasury `select` vote `select` tally `select` returnVote

mkSchemaDefinitions ''VotingSchema
```
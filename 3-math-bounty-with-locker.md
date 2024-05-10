# Multi-Stage Protocol - Math Bounty Into Pin Lock

## Description

This is combination of the math bounty contract (as stage 1) and the pin/pass lock contract (as stage 2). Do note, this example only provides the off-chain logic to perform the transition between the stages and to go in/out of the protocol. There is no on-chain check that forces the user to go from stage 1 (math bounty) to stage 2 (pin/pass lock), and as such this is not a "true" multi-stage protocol. Future examples will cover how to specifically enforce this on-chain.

This example showcases how to use a different script once a certain condition is met (note that the change is made off-chain).

First, a user locks deposited funds under a math bounty (specifically figuring out what number squared matches a given value). The user who solves the problem then locks the awarded funds into a password protected contract that can be collected later by providing the unlock password.

The user who locks their ada under this contract provides a `target` which is the number that must be the result of the squaring.

In other words:

```
x * x = target
```

This `target` is an integer and is placed within the Datum of the locked output UTXO.

Once the funds are locked under the contract with the datum, anyone can solve the math bounty by providing the correct number (providing the correct `x`). They do this by submitting a transaction with their answer for `x` as the Redeemer and a lock password. If their answer is correct and the UTXO can be spent, the endpoint will lock the funds into a new contract that will validate that the hash of the passwords match, and then they get to spend the locked bounty UTXO, and take the funds from within it.

The contract provides three endpoints:

* Publish the problem and prize
* Send a solution and lock the funds (if solved)
* Unlock the funds

## Code

(NOTE: use plutus playground commit 47bee0d683857655d60c230a8b25ab7058c54d55)

```haskell

import           Control.Monad             (void)
import qualified Data.ByteString.Char8     as C
import           Plutus.Contract
import           PlutusTx         
import           PlutusTx.Prelude hiding (pure, (<$>))
import           Ledger                    (Address (..), Validator, ScriptContext(..), TxInfo(..), TxOut (..), TxOutTx (..), Value, scriptAddress)
import           Plutus.V1.Ledger.Scripts   (Datum (..), DatumHash, MonetaryPolicyHash, Redeemer, ValidatorHash)
import qualified Ledger.Constraints        as Constraints
import qualified Ledger.Typed.Scripts      as Scripts
import           Playground.Contract
import qualified Prelude
import           Data.Map (elems)

------------------------------------------------------------

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''ClearString


-- | Datum and redeemer parameter types for math bounty
data MathBounty
instance Scripts.ScriptType MathBounty where
    type instance RedeemerType MathBounty = Integer
    type instance DatumType MathBounty = Integer

-- | Datum and redeemer parameter types for the pin lock
data PinLock
instance Scripts.ScriptType PinLock where
    type instance RedeemerType PinLock = ClearString
    type instance DatumType PinLock = HashedString



-- create a data script for unlocking by hashing the string
-- and lifting the hash to its on-chain representation
hashString :: String -> HashedString
hashString = HashedString . sha2_256 . C.pack

-- create a redeemer script for unlocking by lifting the
-- string to its on-chain representation
clearString :: String -> ClearString
clearString = ClearString . C.pack


-- | Spending validators 
-- (which gets lifted to its on-chain representation).

-- | The math problem validator: the square of the proposed value is the expected solution
validateSolution :: Integer -> Integer -> ScriptContext -> Bool
validateSolution y x _ = x*x == y

-- | The pinlock validator
validatePinLock :: HashedString -> ClearString -> ScriptContext -> Bool
validatePinLock (HashedString lockPin) (ClearString unlockPin) _ = lockPin == sha2_256 unlockPin



-- | The script instance is the compiled pinlock validator (ready to go onto the chain)
pinlockInstance :: Scripts.ScriptInstance PinLock
pinlockInstance = Scripts.validator @PinLock
    $$(PlutusTx.compile [|| validatePinLock ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @HashedString @ClearString


-- | The script instance is the compiled bounty validator (ready to go onto the chain)
bountyInstance :: Scripts.ScriptInstance MathBounty
bountyInstance = Scripts.validator @MathBounty
    $$(PlutusTx.compile [|| validateSolution ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @Integer @Integer


-- | The address of the bounty script (the hash of its validator script)
bountyAddress :: Address
bountyAddress = Ledger.scriptAddress (Scripts.validatorScript bountyInstance)

-- | The address of the pin lock script (the hash of its validator script)
pinlockHash :: ValidatorHash
pinlockHash = Scripts.scriptHash pinlockInstance

pinlockAddress :: Address
pinlockAddress = Ledger.scriptAddress (Scripts.validatorScript pinlockInstance)


-- | Endpoints

-- | The schema of the contract, with one endpoint to publish the problem with a bounty and another to submit solutions
type MathBountyWithLockSchema =
    BlockchainActions
        .\/ Endpoint "bounty" BountyParams
        .\/ Endpoint "solveAndLock" SolutionLockParams
        .\/ Endpoint "unlock" UnlockParams


-- | Parameters for the "bounty" endpoint
data BountyParams = BountyParams
    { target :: Integer
    , amount :: Value
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

--  | Parameters for the "solution" endpoint
data SolutionLockParams = SolutionParams
    { proposed_solution :: Integer
    , lockPin :: String
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

--  | Parameters for the "unlock" endpoint
newtype UnlockParams = UnlockParams
    { unlockPin :: String
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

-- | The "bounty" contract endpoint.
bounty :: AsContractError e => Contract () MathBountyWithLockSchema e ()
bounty = do
    BountyParams target amt <- endpoint @"bounty" @BountyParams
    let tx         = Constraints.mustPayToTheScript target amt
    void (submitTxConstraints bountyInstance tx)

-- | The "solution" contract endpoint.
solution :: AsContractError e => Contract () MathBountyWithLockSchema e ()
solution = do
    SolutionParams theProposal lockPin <- endpoint @"solveAndLock" @SolutionLockParams
    unspentOutputs <- utxoAt bountyAddress
    let txCollect = (collectFromScript unspentOutputs theProposal) 
    -- calculate the total amount in the bounty
    let amt = Prelude.foldl1 (<>) $ map (txOutValue.txOutTxOut) (elems unspentOutputs)
    -- lock the amount 
    let txLock = Constraints.mustPayToOtherScript pinlockHash (Datum $ PlutusTx.toData (hashString lockPin)) amt
    
    let tx = txCollect <> txLock
    void (submitTxConstraintsSpending bountyInstance unspentOutputs tx)

-- | The "unlock" contract endpoint. See note [Contract endpoints]
unlock :: AsContractError e => Contract () MathBountyWithLockSchema e ()
unlock = do
    UnlockParams unlockPin <- endpoint @"unlock" @UnlockParams
    unspentOutputs <- utxoAt pinlockAddress
    let redeemer = clearString unlockPin
        tx       = collectFromScript unspentOutputs redeemer
    void (submitTxConstraintsSpending pinlockInstance unspentOutputs tx)

-- | join all endpoints.
endpoints :: AsContractError e => Contract () MathBountyWithLockSchema e ()
endpoints = bounty `select` solution `select` unlock

mkSchemaDefinitions ''MathBountyWithLockSchema

```

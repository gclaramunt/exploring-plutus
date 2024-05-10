# Math Bounty with split pin lock contract

## Description

This is a variation of the math bounty with lock example where the person that solves the problem can collect a portion of the prize from the math bounty validator, and then lock the rest in the pin lock(aka guessing game) validator.

This example showcases how to work with different outputs from the same script (combined with the use of different contracts).

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
import qualified Ledger.Contexts           as Validation
import qualified Ledger.Value              as Value
import qualified Ledger.Typed.Scripts      as Scripts
import           Playground.Contract
import qualified Prelude
import           Data.Map (elems)

------------------------------------------------------------

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''ClearString

data BountyConfig = BountyConfig 
    { target        :: Integer
    , lockScript    :: ValidatorHash
    } deriving Generic

PlutusTx.makeLift ''BountyConfig    


-- | Datum and redeemer parameter types for math bounty
data MathBounty
instance Scripts.ScriptType MathBounty where
    type instance RedeemerType MathBounty = (Value,Integer)
    type instance DatumType MathBounty = ()

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
validateSolution :: BountyConfig -> () -> (Value,Integer) -> ScriptContext -> Bool
validateSolution BountyConfig{ target, lockScript} () (amountToLock, x)  ScriptContext{scriptContextTxInfo=txInfo} = 
    let 
        toPinlockValidator = Validation.valueLockedBy txInfo lockScript
    in
        x*x == target && toPinlockValidator == amountToLock

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
bountyInstance :: BountyConfig -> Scripts.ScriptInstance MathBounty
bountyInstance params = Scripts.validator @MathBounty
    ($$(PlutusTx.compile [|| validateSolution ||]) `PlutusTx.applyCode` PlutusTx.liftCode params)
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @() @(Value, Integer)


-- | The address of the bounty script (the hash of its validator script)
bountyAddress :: BountyConfig ->  Address
bountyAddress config = Ledger.scriptAddress (Scripts.validatorScript (bountyInstance config))

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
    { problem_target :: Integer
    , amount :: Value
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

--  | Parameters for the "solution" endpoint
data SolutionLockParams = SolutionParams
    { goal :: Integer
    , proposed_solution :: Integer
    , lockPin :: String
    , amountToLock :: Value
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
    let tx         = Constraints.mustPayToTheScript () amt
    void (submitTxConstraints (bountyInstance BountyConfig{ target = target, lockScript= pinlockHash }) tx)

-- | The "solution" contract endpoint.
solution :: AsContractError e => Contract () MathBountyWithLockSchema e ()
solution = do
    SolutionParams target theProposal lockPin amountToLock <- endpoint @"solveAndLock" @SolutionLockParams
    unspentOutputs <- utxoAt (bountyAddress BountyConfig{ target = target, lockScript= pinlockHash })

    -- calculate the total amount in the bounty by collecting the utxos locked under this contract
    let totalBounty = Prelude.foldl1 (<>) $ map (txOutValue.txOutTxOut) (elems unspentOutputs)
    -- select the amount to lock, must not be greater than the total bounty
    let amt = if (amountToLock `Value.geq` totalBounty) then totalBounty else amountToLock

    let txCollect = (collectFromScript unspentOutputs (amt, theProposal)) 
    -- pay the amount to the pinlock script 
    let txLock = Constraints.mustPayToOtherScript pinlockHash (Datum $ PlutusTx.toData (hashString lockPin)) amt
    let tx = txCollect <> txLock
    void (submitTxConstraintsSpending (bountyInstance BountyConfig{ target = target, lockScript= pinlockHash }) unspentOutputs tx) 

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

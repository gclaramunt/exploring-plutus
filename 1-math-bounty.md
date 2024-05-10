# Math Bounty Contract

## Description

This is a simple smart contract which locks deposited funds under a math bounty (specifically figuring out what number squared matches a given value). The user who locks their ada under this contract provides a `target` which is the number that must be the result of the squaring.

In other words:

```
x * x = target
```

This `target` is an integer and is placed within the Datum of the locked output UTXO.

Once the funds are locked under the contract with the datum, anyone can solve the math bounty by providing the correct number (providing the correct `x`). They do this by submitting a transaction with their answer for `x` as the Redeemer. If their answer is correct, then they get to spend the locked bounty UTXO, and take the funds from within it.

## Code

(NOTE: use plutus playground commit 47bee0d683857655d60c230a8b25ab7058c54d55)


```haskell
-- Simple implementation of a math bounty contract

import           Control.Monad             (void)
import qualified Data.ByteString.Char8     as C
import           Playground.Contract
import qualified PlutusTx         as PlutusTx
import           PlutusTx.Prelude hiding (pure, (<$>))

import           Plutus.Contract
import           Ledger                    (Address, Validator, ScriptContext, Value, scriptAddress)
import qualified Ledger.Constraints        as Constraints
import qualified Ledger.Typed.Scripts      as Scripts
import           Playground.Contract
import qualified Prelude

------------------------------------------------------------

-- | The schema of the contract, with one endpoint to publish the problem with a bounty and another to sbumit solutions
type MathBountySchema =
    BlockchainActions
        .\/ Endpoint "bounty" BountyParams
        .\/ Endpoint "solution" SolutionParams

-- | Datum and redeemer parameter types
data MathBounty
instance Scripts.ScriptType MathBounty where
    type instance RedeemerType MathBounty = Integer
    type instance DatumType MathBounty = Integer

-- | The script instance is the compiled validator (ready to go onto the chain)
bountyInstance :: Scripts.ScriptInstance MathBounty
bountyInstance = Scripts.validator @MathBounty
    $$(PlutusTx.compile [|| validateSolution ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @Integer @Integer

-- | This method is the spending validator (which gets lifted to
--   its on-chain representation).
--   validate that the square of the proposed value is the expected solution
validateSolution :: Integer -> Integer -> ScriptContext -> Bool
validateSolution y x _ = x*x == y

-- | The address of the bounty (the hash of its validator script)
bountyAddress :: Address
bountyAddress = Ledger.scriptAddress (Scripts.validatorScript bountyInstance)

-- | Parameters for the "bounty" endpoint
data BountyParams = BountyParams
    { target :: Integer
    , amount :: Value
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

--  | Parameters for the "solution" endpoint
newtype SolutionParams = SolutionParams
    { proposed_solution :: Integer
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)


-- | The "bounty" contract endpoint.
bounty :: AsContractError e => Contract () MathBountySchema e ()
bounty = do
    BountyParams target amt <- endpoint @"bounty" @BountyParams
    let tx         = Constraints.mustPayToTheScript target amt
    void (submitTxConstraints bountyInstance tx)

-- | The "solution" contract endpoint.
solution :: AsContractError e => Contract () MathBountySchema e ()
solution = do
    SolutionParams theProposal <- endpoint @"solution" @SolutionParams
    unspentOutputs <- utxoAt bountyAddress
    let tx = collectFromScript unspentOutputs theProposal
    void (submitTxConstraintsSpending bountyInstance unspentOutputs tx)

-- | Math bounty endpoints.
endpoints :: AsContractError e => Contract () MathBountySchema e ()
endpoints = bounty `select` solution

mkSchemaDefinitions ''MathBountySchema

```

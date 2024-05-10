# Guessing game with script parameters

## Description

This is the same guessing the secret word game contract as the example in the Plutus Playground, but taking a different approach to store the secret word.
In the original contract the secret hash was stored in the datum, while here in this example it is part of the validator script as a parameter to the function that builds the validator. This becomes part of the script address, and as such is hard-coded into the validator script.

## Code

(NOTE: use plutus playground commit 47bee0d683857655d60c230a8b25ab7058c54d55)


```haskell
-- A game with two players. Player 1 thinks of a secret word
-- and uses its hash, and the game validator script, to lock
-- some funds (the prize) in a pay-to-script transaction output.
-- Player 2 guesses the word by attempting to spend the transaction
-- output. If the guess is correct, the validator script releases the funds.
-- If it isn't, the funds stay locked.
import           Control.Monad             (void)
import qualified Data.ByteString.Char8     as C
import           Plutus.Contract
import           PlutusTx
import           PlutusTx.Prelude hiding (pure, (<$>))
import           Ledger                    (Address, Validator, ScriptContext, Value, scriptAddress)
import qualified Ledger.Constraints        as Constraints
import qualified Ledger.Typed.Scripts      as Scripts
import           Playground.Contract
import qualified Prelude

------------------------------------------------------------

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''ClearString

type GameSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockParams
        .\/ Endpoint "guess" GuessParams

data Game
instance Scripts.ScriptType Game where
    type instance RedeemerType Game = ClearString
    type instance DatumType Game = () -- HashedString

gameInstance :: String -> Scripts.ScriptInstance Game
gameInstance lockPin = Scripts.validator @Game
    ($$(PlutusTx.compile [|| validateGuess ||])  `PlutusTx.applyCode` PlutusTx.liftCode (hashString lockPin) )
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @() @ClearString

-- create a data script for the guessing game by hashing the string
-- and lifting the hash to its on-chain representation
hashString :: String -> HashedString
hashString = HashedString . sha2_256 . C.pack

-- create a redeemer script for the guessing game by lifting the
-- string to its on-chain representation
clearString :: String -> ClearString
clearString = ClearString . C.pack

-- | The validation function (Datum -> Redeemer -> ScriptContext -> Bool)
validateGuess :: HashedString -> (() -> ClearString -> ScriptContext -> Bool)
validateGuess (HashedString actual) () (ClearString guess') _ = actual == sha2_256 guess'

-- | The validator script of the game.
gameValidator :: String -> Validator
gameValidator pinLock = Scripts.validatorScript $ gameInstance pinLock

-- | The address of the game (the hash of its validator script)
gameAddress :: String -> Address
gameAddress pinLock = Ledger.scriptAddress $ gameValidator pinLock

-- | Parameters for the "lock" endpoint
data LockParams = LockParams
    { secretWord :: String
    , amount     :: Value
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

--  | Parameters for the "guess" endpoint
newtype GuessParams = GuessParams
    { guessWord :: String
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

-- | The "lock" contract endpoint. See note [Contract endpoints]
lock :: AsContractError e => Contract () GameSchema e ()
lock = do
    LockParams secret amt <- endpoint @"lock" @LockParams
    let tx         = Constraints.mustPayToTheScript () amt
    void (submitTxConstraints (gameInstance secret) tx)

-- | The "guess" contract endpoint. See note [Contract endpoints]
guess :: AsContractError e => Contract () GameSchema e ()
guess = do
    GuessParams theGuess <- endpoint @"guess" @GuessParams  -- hash guess == secret 
    unspentOutputs <- utxoAt $ gameAddress theGuess
    let redeemer = clearString theGuess
        tx       = collectFromScript unspentOutputs redeemer
    void (submitTxConstraintsSpending ( gameInstance theGuess) unspentOutputs tx)

game :: AsContractError e => Contract () GameSchema e ()
game = lock `select` guess


endpoints :: AsContractError e => Contract () GameSchema e ()
endpoints = game

mkSchemaDefinitions ''GameSchema

```

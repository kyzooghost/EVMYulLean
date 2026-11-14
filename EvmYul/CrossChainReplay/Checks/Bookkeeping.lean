import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Rollback
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

private def logObservation : EngineObservation :=
  { toyObservation with instruction := "LOG0", rawLogs := [[7]] }
private def LogToy : EvmModel :=
  { Toy with primitiveStep := fun w f _ action w' f' obs =>
      action = .continue ∧ w' = w ∧ f' = f ∧ obs = logObservation }
private def start : ExecutionState LogToy :=
  { world := initialToyWorld, environment := (), frames := [(0 : Nat)], roles := [.application], protocol := toyContext, driverIndex := 0, phase := .inTransaction, attempted := [], scopes := [], liveLogs := [], checkpoints := [], pendingOutcome := none, probe := none }
private def afterLog : ExecutionState LogToy :=
  { start with attempted := [.engine logObservation], liveLogs := [[7]] }

example : Step LogToy toyParams start [.engine logObservation] afterLog := by
  apply Step.engineContinue start (0 : Nat) (0 : Nat) [] .application [] initialToyWorld logObservation
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · simp [LogToy, Toy, start]

#check ExecutionState.nextInvocation

private def restored : ExecutionState LogToy :=
  restore LogToy (checkpoint LogToy start) { afterLog with nextInvocation := 5 }
#guard restored.liveLogs.isEmpty
#guard restored.attempted == [.engine logObservation]
#guard restored.nextInvocation == 5

private def lookup : TopLevelLookup :=
  { declaredPeerRollup := EvmYul.UInt256.ofNat 1, crossChainCallHash := zeroHash,
    returnData := [], failed := false, incomingCalls := [], expectedOutgoingCalls := [],
    expectedLookups := [], callCount := EvmYul.UInt256.ofNat 0, rollingHash := zeroHash,
    crossChainRollingHash := zeroHash }
private def loadedState : ProtocolState :=
  { lookups := [{ row := lookup, loadedBlock := 11, id := .topLevelLookup 0 zeroHash }] }
private def attemptedScope (serial : Nat) : Option ScopeId :=
  match advanceProtocol toyParams { toyContext with invocationSerial := serial } loadedState
      (.resolveTopLookup zeroHash lookup.declaredPeerRollup true) with
  | .local _ next _ => next.activeScope
  | _ => none
#guard attemptedScope 10 == some { entry := .topLevelLookup 0 zeroHash, invocationPath := [10] }
#guard attemptedScope 11 == some { entry := .topLevelLookup 0 zeroHash, invocationPath := [11] }
#guard attemptedScope 10 != attemptedScope 11

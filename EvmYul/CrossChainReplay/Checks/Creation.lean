import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

#check CreationResult
#check Step.engineCreate2
#check Step.resumeCreation

/-- This toy uses steps as the factory nonce; it does not model a fork or install code. -/
private def nonceObservation : EngineObservation :=
  { toyObservation with instruction := "CREATE2_SETUP", accounts := [0], resources := [.incrementNonce 0] }
private def createObservation : EngineObservation := { toyObservation with instruction := "CREATE2" }
private def childObservation : EngineObservation := { toyObservation with instruction := "CHILD_EFFECT" }
private def exitObservation : EngineObservation := { toyObservation with instruction := "REVERT" }
private def value : Word := EvmYul.UInt256.ofNat 0
private def target : Address := create2Address toyParams.keccak 0 zeroHash [0]
private def CreationToy : EvmModel :=
  { Toy with
    accountView := fun w address => if address == 0 then { toyAccount with nonce := w.steps } else toyAccount
    primitiveStep := fun w f _ action w' f' obs =>
      f' = f ∧ match action with
      | .create2 salt code amount => salt = zeroHash ∧ code = [0] ∧ amount = value ∧ w' = w ∧ obs = createObservation
      | .continue => w' = { w with steps := 99 } ∧ obs = childObservation
      | .frameExit (.reverted [9]) => w' = w ∧ obs = exitObservation
      | _ => False
    enterCreation := fun w f address salt code amount saved childWorld suspended child events =>
      address = target ∧ salt = zeroHash ∧ code = [0] ∧ amount = value ∧
      saved = { w with steps := w.steps + 1 } ∧ childWorld = saved ∧ suspended = f ∧ child = (1 : Nat) ∧ events = [nonceObservation]
    exitCreation := fun saved _ _ parent _ outcome final resumed result events =>
      outcome = .reverted [9] ∧ final = saved ∧ resumed = parent ∧ result = .reverted [9] ∧ events = [] }

private def start : ExecutionState CreationToy :=
  { world := { initialToyWorld with steps := 1 }, environment := (), frames := [(0 : Nat)], roles := [.application], protocol := toyContext, driverIndex := 0, phase := .inTransaction, attempted := [], scopes := [], liveLogs := [], checkpoints := [], pendingOutcome := none, probe := none }
private def savedWorld : ToyWorld := { initialToyWorld with steps := 2 }
private def saved : FrameCheckpoint CreationToy :=
  { kind := .applicationCreation target, world := savedWorld, frames := [(0 : Nat)], roles := [.application], protocol := toyContext, scopes := [], liveLogs := [], probe := none }
private def entered : ExecutionState CreationToy :=
  { start with world := savedWorld, frames := [(1 : Nat), (0 : Nat)], roles := [.application, .application], attempted := [.engine createObservation, .engine nonceObservation], checkpoints := [saved] }

example : Step CreationToy toyParams start [.engine createObservation, .engine nonceObservation] entered := by
  apply Step.engineCreate2 start (0 : Nat) (0 : Nat) (0 : Nat) (1 : Nat) [] .application []
    zeroHash [0] value start.world savedWorld savedWorld createObservation [nonceObservation]
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · simp [CreationToy, Toy]
  · simp [CreationToy, Toy, start, savedWorld, initialToyWorld, target, toyMachine]

private def changed : ExecutionState CreationToy :=
  { entered with world := { savedWorld with steps := 99 }, attempted := entered.attempted ++ [.engine childObservation] }
example : Step CreationToy toyParams entered [.engine childObservation] changed := by
  apply Step.engineContinue entered (1 : Nat) (1 : Nat) [(0 : Nat)] .application [.application]
    { savedWorld with steps := 99 } childObservation
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · simp [CreationToy, Toy, entered]

private def exiting : ExecutionState CreationToy :=
  { changed with attempted := changed.attempted ++ [.engine exitObservation], pendingOutcome := some (.reverted [9]) }
example : Step CreationToy toyParams changed [.engine exitObservation] exiting := by
  apply Step.engineExit changed (1 : Nat) (1 : Nat) [(0 : Nat)] .application [.application]
    changed.world exitObservation (.reverted [9])
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · simp [CreationToy, Toy]

private def resumed : ExecutionState CreationToy :=
  { exiting with world := savedWorld, frames := [(0 : Nat)], roles := [.application], checkpoints := [], pendingOutcome := none }
example : Step CreationToy toyParams exiting [] resumed := by
  apply Step.resumeCreation exiting saved [] (1 : Nat) (0 : Nat) (0 : Nat) [] target
    (.reverted [9]) savedWorld (.reverted [9]) []
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [CreationToy, Toy, saved]

#guard (CreationToy.accountView start.world 0).nonce == 1
#guard (CreationToy.accountView resumed.world 0).nonce == 2
#guard resumed.world.steps != changed.world.steps
#guard resumed.attempted.length == 4
#guard resumed.pendingOutcome == none

private def RejectedToy : EvmModel :=
  { CreationToy with rejectCreation := fun w f address salt code amount final resumed result events =>
      address = target ∧ salt = zeroHash ∧ code = [0] ∧ amount = value ∧
      final = { w with steps := w.steps + 1 } ∧ resumed = f ∧
      result = .exceptional (.other "collision") ∧ events = [nonceObservation] }
private def rejectedStart : ExecutionState RejectedToy :=
  { world := { initialToyWorld with steps := 1 }, environment := (), frames := [(0 : Nat)], roles := [.application], protocol := toyContext, driverIndex := 0, phase := .inTransaction, attempted := [], scopes := [], liveLogs := [], checkpoints := [], pendingOutcome := none, probe := none }
private def rejected : ExecutionState RejectedToy :=
  { rejectedStart with world := savedWorld, attempted := [.engine createObservation, .engine nonceObservation] }

example : Step RejectedToy toyParams rejectedStart [.engine createObservation, .engine nonceObservation] rejected := by
  apply Step.rejectCreate2 rejectedStart (0 : Nat) (0 : Nat) (0 : Nat) [] .application []
    zeroHash [0] value rejectedStart.world savedWorld createObservation
    (.exceptional (.other "collision")) [nonceObservation]
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · simp [RejectedToy, CreationToy, Toy]
  · simp [RejectedToy, CreationToy, Toy, rejectedStart, savedWorld, initialToyWorld, target, toyMachine]
  · rfl
#guard rejected.frames.length == 1
#guard rejected.checkpoints.isEmpty
#guard rejected.pendingOutcome == none
#guard (RejectedToy.accountView rejected.world 0).nonce == 2

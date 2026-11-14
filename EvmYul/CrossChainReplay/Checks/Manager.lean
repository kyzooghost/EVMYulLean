import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

#check ManagerInvocation
#check Step.managerCall
#check Step.dispatchSystem

private def registered : ProxyRegistration :=
  { proxy := 2, originalAddress := 1, originalRollup := EvmYul.UInt256.ofNat 1 }
private def invocation : ManagerInvocation :=
  { proxy := 2, source := 6, value := EvmYul.UInt256.ofNat 7, data := [8], isStatic := false }
private def state : ProtocolState := { registry := [registered] }
private def context : ProtocolContext := { toyContext with control := .invoke invocation }

#guard match advanceProtocol toyParams context {} context.control with
  | .failed _ _ .unauthorizedProxy [] => true
  | _ => false

private def systemBeforeRoute : Bool :=
  match advanceProtocol toyParams context state context.control with
  | .dispatchSystem unchanged next value [] =>
      unchanged == state && value == invocation.value &&
      match next.control with
      | .resumeSystem call proxy false => call == invocation && proxy == registered
      | _ => false
  | _ => false
#guard systemBeforeRoute

#guard match advanceProtocol toyParams context state (.resumeSystem invocation registered false) with
  | .failed _ _ .etherTransferFailed [] => true
  | _ => false

#guard match advanceProtocol toyParams context state (.managerRoute invocation registered) with
  | .local _ next [] => next.control == .selectProxy (managerCallHash toyParams invocation registered) registered.originalRollup
  | _ => false

private def failedProbe (cause : HaltCause) : ProbeResult :=
  { proxy := 0, depth := 1, outcome := .exceptional cause }
#guard (managerRequest toyParams (toyMachine 0) (failedProbe .outOfGas)).staticPermission
#guard (managerRequest toyParams (toyMachine 0) (failedProbe .outOfGas)).kind == .staticcall
#guard childFrameRole toyParams state
  { target := toyParams.manager, value := EvmYul.UInt256.ofNat 0, data := [], gasCap := none, staticPermission := false, kind := .delegatecall } == .application
#guard (managerRequest toyParams (toyMachine 0) (failedProbe .staticViolation)).data ==
  (managerRequest toyParams (toyMachine 0) (failedProbe .outOfGas)).data
#guard (managerRequest toyParams { (toyMachine 0) with value := EvmYul.UInt256.ofNat 7 }
  (failedProbe .outOfGas)).value.toNat == 0

private def successfulProbe : ProbeResult := { proxy := 0, depth := 1, outcome := .returned [] }
private def CallToy : EvmModel :=
  { Toy with primitiveStep := fun w f _ action w' f' obs =>
      action = .call (managerRequest toyParams (toyMachine 0) successfulProbe) ∧
      w' = w ∧ f' = f ∧ obs = toyObservation }
private def callStart : ExecutionState CallToy :=
  { world := initialToyWorld, environment := (), frames := [(0 : Nat)], roles := [.proxy], protocol := toyContext, driverIndex := 0, phase := .inTransaction, attempted := [], scopes := [], liveLogs := [], checkpoints := [], pendingOutcome := none, probe := some successfulProbe }

example : ∃ next, Step CallToy toyParams callStart [.engine toyObservation] next := by
  refine ⟨_, Step.managerCall callStart (0 : Nat) (0 : Nat) (0 : Nat) [] []
    successfulProbe initialToyWorld initialToyWorld toyObservation ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨rfl, rfl⟩
  · simp [CallToy, Toy, callStart, toyMachine]
  · simp [CallToy, Toy]

private def systemStart : ExecutionState Toy :=
  { toyState with world := { initialToyWorld with protocol := state }, roles := [.manager], protocol := context }
private def systemContext : ProtocolContext :=
  { context with control := .resumeSystem invocation registered false }

example : ∃ next, Step Toy toyParams systemStart
    [.engine (systemCallObservation toyParams 0 invocation.value)] next := by
  refine ⟨_, Step.dispatchSystem systemStart state systemContext invocation.value []
    (0 : Nat) (0 : Nat) [] systemStart.world ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Toy, systemStart, state, initialToyWorld]

private def topHash : Hash32 := toyHash [5, 6]
private def top : TopLevelLookup :=
  { declaredPeerRollup := registered.originalRollup, crossChainCallHash := topHash,
    returnData := [9], failed := false, incomingCalls := [], expectedOutgoingCalls := [],
    expectedLookups := [], callCount := EvmYul.UInt256.ofNat 0, rollingHash := zeroHash,
    crossChainRollingHash := foldBoundary toyHash zeroHash
      { callHash := topHash, success := true, returnData := [9] } }
private def topState : ProtocolState :=
  { state with lookups := [{ row := top, loadedBlock := 11, id := .topLevelLookup 5 topHash }] }

private def staticTopLookup : Bool :=
  match advanceProtocol toyParams context topState (.resolveTopLookup topHash registered.originalRollup true) with
  | .local unchanged selected [] =>
      unchanged == topState && selected.activeScope.any (fun scope => scope.entry == .topLevelLookup 5 topHash) &&
      match advanceProtocol toyParams selected unchanged selected.control with
      | .returned _ _ [9] [.check _ .structuralHash true, .boundary _ h true [9], .check _ .crossChainHash true] => h == topHash
      | _ => false
  | _ => false
#guard staticTopLookup
#guard match advanceProtocol toyParams context topState (.resolveTopLookup topHash registered.originalRollup false) with
  | .failed _ _ .executionNotFound _ => true
  | _ => false
#guard match advanceProtocol toyParams { context with height := 11 } topState
    (.resolveTopLookup topHash registered.originalRollup true) with
  | .failed _ _ .executionNotFound _ => true
  | _ => false
#guard (encodeBytesReturn [9]).length == 96
#guard (encodeBytesReturn [9]).take 32 == wordBytes 32

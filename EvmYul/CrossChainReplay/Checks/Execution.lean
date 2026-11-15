import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Rollback
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

namespace ExecutionCheck

#check advanceProtocol
#check Step
#check Step.proxyProbe
#check Step.resumeProbe
#check probeUsesLookup
#check failureTrace

#guard FrameOutcome.exceptional .outOfGas != FrameOutcome.exceptional .staticViolation
#guard (proxyProbeRequest toyParams 0 false).gasCap == some 1000
#guard (proxyProbeRequest toyParams 0 true).staticPermission
#guard (proxyProbeRequest toyParams 0 false).data == selector toyParams.keccak "staticCheck()"
#guard probeUsesLookup (.exceptional .outOfGas)
#guard probeUsesLookup (.exceptional .staticViolation)
#guard probeUsesLookup (.reverted [1])
#guard !probeUsesLookup (.returned [])
#guard toyState.roles.head? != some .manager
#guard failureTrace toyContext .executionNotFound [] ==
  [.protocol (.failure none "ExecutionNotFound()")]

def missingEntryStart : ExecutionState Toy :=
  { toyState with roles := [.manager], protocol := { toyContext with control := .selectProxy zeroHash (EvmYul.UInt256.ofNat 1) } }

def missingEntryFallback : ExecutionState Toy :=
  { missingEntryStart with protocol := { missingEntryStart.protocol with control := .resolveTopLookup zeroHash (EvmYul.UInt256.ofNat 1) false } }

example : Step Toy toyParams missingEntryStart [] missingEntryFallback := by
  apply Step.protocolLocal missingEntryStart initialToyWorld.protocol missingEntryFallback.protocol []
  · rfl
  · rfl
  · rfl
  · rfl

example : ∃ next, Step Toy toyParams missingEntryFallback
    [.protocol (.failure none "ExecutionNotFound()")] next := by
  refine ⟨_, Step.protocolFailed missingEntryFallback initialToyWorld.protocol
    missingEntryFallback.protocol .executionNotFound [] ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl

def toyAfterStep : ExecutionState Toy :=
  { toyState with world := { initialToyWorld with steps := 1 }, attempted := [.engine toyObservation] }

example : Step Toy toyParams toyState [.engine toyObservation] toyAfterStep := by
  unfold toyAfterStep
  apply Step.engineContinue toyState (0 : Nat) (0 : Nat) []
    .application [] { initialToyWorld with steps := 1 } toyObservation
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · simp [Toy, toyState, initialToyWorld]

/-- A finite call adapter for composition checks; it does not model TSTORE or a fork. -/
def ProbeToy : EvmModel :=
  { Toy with primitiveStep := fun w f _ action w' f' obs =>
      action = .call (proxyProbeRequest toyParams 0 false) ∧
      w' = w ∧ f' = f ∧ obs = toyObservation }

def probeStart : ExecutionState ProbeToy :=
  { world := initialToyWorld, environment := (), frames := [(0 : Nat)], roles := [.proxy],
    protocol := toyContext, driverIndex := 0, phase := .inTransaction, attempted := [],
    scopes := [], liveLogs := [], checkpoints := [], pendingOutcome := none, probe := none }

example : ∃ next, Step ProbeToy toyParams probeStart [.engine toyObservation] next := by
  refine ⟨_, Step.proxyProbe probeStart (0 : Nat) (0 : Nat) (0 : Nat) [] [] initialToyWorld initialToyWorld toyObservation ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [ProbeToy, Toy, probeStart, toyMachine]
  · simp [ProbeToy, Toy]

def probeCheckpoint : FrameCheckpoint ProbeToy :=
  checkpointWithKind ProbeToy .proxyProbe probeStart

def probeExited (outcome : FrameOutcome) : ExecutionState ProbeToy :=
  { probeStart with frames := [(0 : Nat), (0 : Nat)], roles := [.proxy, .proxy], checkpoints := [probeCheckpoint], pendingOutcome := some outcome, attempted := [.engine toyObservation] }

def resumedProbe (outcome : FrameOutcome) : ExecutionState ProbeToy :=
  { (probeExited outcome) with frames := [(0 : Nat)], roles := [.proxy], scopes := if exitSuccess outcome then (probeExited outcome).scopes else probeCheckpoint.scopes, liveLogs := if exitSuccess outcome then (probeExited outcome).liveLogs else probeCheckpoint.liveLogs, liveValidations := if exitSuccess outcome then (probeExited outcome).liveValidations else probeCheckpoint.liveValidations, checkpoints := [], pendingOutcome := none, probe := some { proxy := 0, depth := 1, outcome := outcome } }

/-- `staticProbeFailureCauses`: both failure causes resume through the same source branch
    while the resumed probe retains the distinct cause. -/
theorem staticProbeFailureCauses (outcome : FrameOutcome) : ∃ next,
    Step ProbeToy toyParams (probeExited outcome) [] next ∧
    next.probe = some { proxy := 0, depth := 1, outcome := outcome } ∧
    next.attempted = [.engine toyObservation] := by
  refine ⟨resumedProbe outcome, ?_, ?_, ?_⟩
  · apply Step.resumeProbe (probeExited outcome) probeCheckpoint [] (0 : Nat) (0 : Nat) (0 : Nat) [] outcome initialToyWorld
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [ProbeToy, Toy, probeCheckpoint, checkpointWithKind, probeStart]
  · rfl
  · rfl

end ExecutionCheck

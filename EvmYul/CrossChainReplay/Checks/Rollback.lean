import EvmYul.CrossChainReplay.Rollback
import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

namespace RollbackCheck

#check checkpoint
#check restore
#check adoptTransport

def sampleScope : ScopeRecord :=
  { id := { entry := .preloaded 0, invocationPath := [] }, effective := [],
    structural := [], staticOutcomes := [], transportedWitness := none }

def changedState : ExecutionState Toy :=
  { toyState with world := { initialToyWorld with steps := 1 }, attempted := [.engine toyObservation], scopes := [sampleScope], liveLogs := [[1]], completedScopes := [sampleScope] }

def restored : ExecutionState Toy := restore Toy (checkpoint Toy toyState) changedState

#guard restored.world.steps == 0
#guard restored.scopes.isEmpty
#guard restored.liveLogs.isEmpty
#guard restored.attempted.length == 1
#guard restored.completedScopes == [sampleScope]

def transported : ContextResult :=
  { rollingHash := toyHash [3], outgoingCursor := EvmYul.UInt256.ofNat 5,
    incomingCursor := EvmYul.UInt256.ofNat 7, ignoredFlagWord := EvmYul.UInt256.ofNat 2,
    crossChainHash := toyHash [4] }

def adopted : ExecutionState Toy := adoptTransport Toy transported changedState

#guard (Toy.readProtocol adopted.world).structuralHash == toyHash [3]
#guard (Toy.readProtocol adopted.world).outgoingCursor == 5
#guard (Toy.readProtocol adopted.world).incomingCursor == 7
#guard (Toy.readProtocol adopted.world).crossChainHash == toyHash [4]
#guard (adopted.scopes.head?).bind ScopeRecord.transportedWitness == none
#guard adopted.attempted.length == 1

def hashA : Hash32 := toyHash [1]
def hashQ : Hash32 := toyHash [2, 3]
def recordQ : BoundaryRecord := { callHash := hashQ, success := true, returnData := [8] }
def beforeA : ExecutionState Toy :=
  { toyState with roles := [.manager], protocol := { toyContext with activeScope := some sampleScope.id, control := .resumeIncoming sampleScope.id 1 1 .entryValidation hashA false [] }, scopes := [sampleScope] }
def savedA : FrameCheckpoint Toy := checkpointWithKind Toy .protocolIncoming beforeA
def duringA : ExecutionState Toy :=
  { beforeA with world := { initialToyWorld with protocol := { initialToyWorld.protocol with crossChainHash := foldBoundary toyHash zeroHash recordQ, outgoingCursor := 1 }, steps := 1 }, frames := [(0 : Nat), (0 : Nat)], roles := [.proxy, .manager], scopes := [{ sampleScope with effective := [recordQ] }], liveLogs := [[8]], checkpoints := [savedA], pendingOutcome := some (.reverted [9]), attempted := [.protocol (.boundary sampleScope.id hashQ true [8])] }
def resumedA : ExecutionState Toy :=
  { duringA with world := beforeA.world, frames := [(0 : Nat)], roles := [.manager], protocol := { beforeA.protocol with control := .resumeIncoming sampleScope.id 1 1 .entryValidation hashA false [9] }, scopes := beforeA.scopes, liveLogs := [], checkpoints := [], pendingOutcome := none, probe := none }

theorem rollbackStep : Step Toy toyParams duringA [] resumedA := by
  apply Step.resumeIncoming duringA savedA [] (0 : Nat) (0 : Nat) (0 : Nat) []
    (.reverted [9]) sampleScope.id 1 1 .entryValidation hashA beforeA.world
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨.proxy, rfl⟩
  · rfl
  · rfl
  · simp [Toy, savedA, checkpointWithKind]

#guard (Toy.readProtocol resumedA.world).outgoingCursor == 0
#guard resumedA.liveLogs.isEmpty
#guard resumedA.attempted == [.protocol (.boundary sampleScope.id hashQ true [8])]

def onlyAFailureSurvives : Bool :=
  match advanceProtocol toyParams resumedA.protocol (Toy.readProtocol resumedA.world)
      resumedA.protocol.control with
  | .local state _ events =>
      state.crossChainHash == foldBoundary toyHash zeroHash
        { callHash := hashA, success := false, returnData := [9] } &&
      ((appendScopeEvents resumedA.scopes events).head?).map ScopeRecord.effective ==
        some [{ callHash := hashA, success := false, returnData := [9] }]
  | _ => false
#guard onlyAFailureSurvives

/-- `ordinaryRollback`: after A reverts, Q leaves the effective transcript and the restored
    accumulator, while Q's attempted observation remains. Witnessed by `rollbackStep`. -/
def ordinaryRollback : Bool :=
  onlyAFailureSurvives && (Toy.readProtocol resumedA.world).outgoingCursor == 0 &&
  resumedA.scopes.all (·.effective.isEmpty) &&
  resumedA.attempted == [.protocol (.boundary sampleScope.id hashQ true [8])]
#guard ordinaryRollback

/-- `transportWithoutProvenance`: accepted decoded values change actual state, but no transcript
    witness is manufactured. -/
def transportWithoutProvenance : Bool :=
  (Toy.readProtocol adopted.world).crossChainHash == toyHash [4] &&
  (Toy.readProtocol adopted.world).incomingCursor == 7 &&
  (adopted.scopes.head?).bind ScopeRecord.transportedWitness == none
#guard transportWithoutProvenance

end RollbackCheck

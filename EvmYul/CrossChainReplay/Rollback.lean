import EvmYul.CrossChainReplay.ExecutionState

namespace EvmYul.CrossChainReplay

def checkpointWithKind (M : EvmModel) (kind : FrameCheckpointKind)
    (state : ExecutionState M) : FrameCheckpoint M :=
  { kind := kind, world := state.world, frames := state.frames, roles := state.roles, protocol := state.protocol, scopes := state.scopes, liveLogs := state.liveLogs, probe := state.probe, pendingTransport := state.pendingTransport, liveValidations := state.liveValidations }

def checkpoint (M : EvmModel) (state : ExecutionState M) : FrameCheckpoint M :=
  checkpointWithKind M .applicationCall state

/-- Revert EVM-visible state and effective scopes; retain the full attempted history. -/
def restore (M : EvmModel) (saved : FrameCheckpoint M)
    (state : ExecutionState M) : ExecutionState M :=
  { state with world := saved.world, frames := saved.frames, roles := saved.roles, protocol := saved.protocol, scopes := saved.scopes, liveLogs := saved.liveLogs, pendingOutcome := none, probe := saved.probe, pendingTransport := saved.pendingTransport, liveValidations := saved.liveValidations }

/-- Source decoder output becomes actual state, without inventing transcript provenance. -/
def adoptTransport (M : EvmModel) (result : ContextResult)
    (state : ExecutionState M) : ExecutionState M :=
  let protocol := M.readProtocol state.world
  let protocol := { protocol with structuralHash := result.rollingHash, outgoingCursor := result.outgoingCursor.toNat, incomingCursor := result.incomingCursor.toNat, crossChainHash := result.crossChainHash }
  { state with world := M.writeProtocol state.world protocol }

end EvmYul.CrossChainReplay

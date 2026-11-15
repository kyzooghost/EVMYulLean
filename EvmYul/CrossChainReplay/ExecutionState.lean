import EvmYul.CrossChainReplay.EvmInterface

namespace EvmYul.CrossChainReplay

structure ScopeRecord where
  id : ScopeId
  effective : List BoundaryRecord
  structural : List StructuralEvent
  staticOutcomes : List (Bool × Bytes)
  transportedWitness : Option (List BoundaryRecord)
  deriving Repr, BEq

inductive DriverPhase where
  | beforeTransaction | inTransaction | done
  deriving Repr, DecidableEq

/-- One settled driver transaction. Validations and logs are retained only when committed. -/
structure TransactionResult where
  index : Nat
  envelope : DriverEnvelope
  outcome : FrameOutcome
  committedValidations : List ValidationResult
  committedLogs : List Bytes
  settlement : List EngineObservation
  deriving Repr, BEq

inductive FrameRole where
  | application | proxy | manager | system
  deriving Repr, BEq, DecidableEq

inductive FrameCheckpointKind where
  | applicationCall | protocolIncoming | protocolStatic | proxyProbe | protocolSystem | protocolSpan
  | applicationCreation (target : Address)
  | proxyCreation (row : IncomingCall)
  deriving Repr, BEq

/-- A completed self-probe belongs to the resumed proxy frame at this stack depth. -/
structure ProbeResult where
  proxy : Address
  depth : Nat
  outcome : FrameOutcome
  deriving Repr, BEq

/-- Candidate provenance produced only by the concrete span executor, not by raw bytes. -/
structure TransportEvidence where
  result : ContextResult
  scopes : List ScopeRecord
  deriving Repr, BEq

structure FrameCheckpoint (M : EvmModel) where
  kind : FrameCheckpointKind
  world : M.World
  frames : List M.Frame
  roles : List FrameRole
  protocol : ProtocolContext
  scopes : List ScopeRecord
  liveLogs : List Bytes
  probe : Option ProbeResult
  pendingTransport : Option TransportEvidence := none
  /-- Protocol validation events live at this checkpoint; restored with logs on rollback. -/
  liveValidations : List ValidationResult := []

structure ExecutionState (M : EvmModel) where
  world : M.World
  environment : M.Environment
  frames : List M.Frame
  roles : List FrameRole
  protocol : ProtocolContext
  driverIndex : Nat
  phase : DriverPhase
  attempted : Trace
  scopes : List ScopeRecord
  liveLogs : List Bytes
  checkpoints : List (FrameCheckpoint M)
  pendingOutcome : Option FrameOutcome
  probe : Option ProbeResult
  pendingTransport : Option TransportEvidence := none
  completedScopes : List ScopeRecord := []
  /-- Audit numbering is monotonic across reverted attempts; it is not EVM storage. -/
  nextInvocation : Nat := 0
  /-- Protocol-generated validation events not yet rolled back. Raw logs never populate this. -/
  liveValidations : List ValidationResult := []
  /-- Ordered driver envelopes; `driverIndex` selects the next one. -/
  envelopes : List DriverEnvelope := []
  /-- World after transaction initialization; a failed top-level frame settles from here. -/
  transactionStart : Option M.World := none
  /-- Settled driver transactions, in order. -/
  transactions : List TransactionResult := []

structure Configuration (M : EvmModel) where
  initialWorld : M.World
  environment : M.Environment
  envelopes : List DriverEnvelope
  height : Nat
  blockCapacity : Nat
  bundle : Bundle
  selected : EntryId
  /-- Bundle entry whose expected hashes the selected occurrence must validate. -/
  selectedEntry : Entry
  request : LogicalRequest

def configurationHeight {M : EvmModel} (config : Configuration M) : Nat := config.height

end EvmYul.CrossChainReplay

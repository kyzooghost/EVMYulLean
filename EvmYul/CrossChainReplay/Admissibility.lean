import EvmYul.CrossChainReplay.Resources

/-!
Spec sections 5.8 and 6: the state relation and the A1-A8 admissibility conjunction.
Every predicate reads the reference record, the two configurations, or current states. None
mentions a replay run, a replay trace, or replay success.
-/

namespace EvmYul.CrossChainReplay

/-! ## Observation restrictions (spec section 6) -/

/-- Spec section 6.1. `SLOTNUM` is listed unconditionally; banning a disabled opcode is vacuous. -/
def bannedInstructions : List String :=
  ["BLOCKHASH", "COINBASE", "TIMESTAMP", "NUMBER", "PREVRANDAO", "DIFFICULTY", "GASLIMIT",
   "BASEFEE", "BLOBBASEFEE", "GASPRICE", "BLOBHASH", "BALANCE", "SELFBALANCE", "CREATE",
   "SELFDESTRUCT", "SLOTNUM"]

def gasForwardingCalls : List String := ["CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"]

def gasInstruction : String := "GAS"

def engineEvents (trace : Trace) : List EngineObservation :=
  trace.filterMap fun
    | .engine event => some event
    | .protocol _ => none

/-- Spec section 6.2. The frame's next instruction after `GAS` is a call. A call pops its gas
    operand first, so adjacency means the `GAS` result is exactly that operand and is consumed. -/
def GasForwardingOnly (events : List EngineObservation) : Prop :=
  ∀ (i : Nat) event, events[i]? = some event → event.instruction = gasInstruction →
    ∃ next, events[i + 1]? = some next ∧ next.frame = event.frame ∧
      next.instruction ∈ gasForwardingCalls

/-- `TraceAllowed(V, t_X)`: every attempted instruction, including initialization code and
    reverted frames, is enabled, unbanned, and uses only declared native operations. -/
def TraceAllowed (p : Parameters) (trace : Trace) : Prop :=
  (∀ event ∈ engineEvents trace,
    event.instruction ∉ bannedInstructions ∧
    event.instruction ∈ p.revision.enabledOperations ∧
    ∀ operation, event.nativeOperation = some operation →
      operation ∈ p.revision.nativeOperations) ∧
  GasForwardingOnly (engineEvents trace)

/-- Spec section 5.6, conservatively: application code does not access protocol-owned
    coordinates, so no normalized-away freshness value is observable. -/
def NoProtocolCoordinateAccess (M : EvmModel) (trace : Trace) : Prop :=
  ∀ event ∈ engineEvents trace, ∀ access ∈ event.accesses, ¬ M.protocolOwned access.location

/-! ## Driver shape (spec sections 2 and 3.2) -/

/-- `DriverAllowed(V, C)`: a nonempty sequence of call transactions with destinations, no
    contract creation or EIP-7702 authorization, at consecutive positions in one block. -/
def DriverAllowed (M : EvmModel) (_p : Parameters) (config : Configuration M) : Prop :=
  config.envelopes ≠ [] ∧
  (∀ envelope ∈ config.envelopes, envelope.kind = .call ∧ envelope.destination.isSome) ∧
  (∀ (i : Nat) envelope, config.envelopes[i]? = some envelope →
    envelope.blockPosition = (config.envelopes.head?.map (·.blockPosition)).getD 0 + i)

/-- Fields of an envelope fixed by the logical request; nonce, fees, gas, and position may vary. -/
def logicalEnvelope (envelope : DriverEnvelope) :
    TransactionKind × Address × Option Address × Word × Bytes :=
  (envelope.kind, envelope.sender, envelope.destination, envelope.value, envelope.data)

/-- A1 and A7 inputs: the same request, semantic bundle, selected occurrence, and driver. -/
def SameLogicalInputs {M : EvmModel} (reference replay : Configuration M) : Prop :=
  reference.request = replay.request ∧ reference.bundle = replay.bundle ∧
  reference.selected = replay.selected ∧ reference.selectedEntry = replay.selectedEntry ∧
  reference.envelopes.map logicalEnvelope = replay.envelopes.map logicalEnvelope

/-! ## Protocol state normalization (spec sections 4.4 and 5.6) -/

inductive Freshness where
  | current | absent | stale | consumed
  deriving Repr, BEq, DecidableEq

def stampFreshness (height stamp : Nat) : Freshness :=
  if stamp == 0 then .absent else if stamp == currentStamp height then .current else .stale

def entryFreshness (height : Nat) (row : LoadedEntry) : Freshness :=
  if row.consumed then .consumed else stampFreshness height row.loadedBlock

/-- Rows at or after the head, by logical occurrence and freshness class. Physical indices and
    passed prefixes are dropped; an absent bucket and a drained bucket are both empty. Only a
    current row's contents are compared: the source deletes consumed rows. -/
def bucketView (height : Nat) (state : ProtocolState) (hash : Hash32) :
    List (EntryId × Option Entry × Freshness) :=
  ((bucketFor hash state).map fun bucket =>
    (bucket.rows.drop bucket.head).map fun row =>
      let freshness := entryFreshness height row
      (row.id, if freshness == .current then some row.row else none, freshness)).getD []

def lookupView (height : Nat) (state : ProtocolState) (hash : Hash32) :
    Option (EntryId × TopLevelLookup × Freshness) :=
  (state.lookups.find? (·.row.crossChainCallHash == hash)).map fun loaded =>
    (loaded.id, loaded.row, stampFreshness height loaded.loadedBlock)

def registryView (state : ProtocolState) (proxy : Address) : Option ProxyRegistration :=
  state.registry.find? (·.proxy == proxy)

/-- Equal semantic records and occurrences, freshness classes, registry, active entry,
    cursors, and accumulators. Stamps are compared only through their classes. -/
def ProtocolRelated (heightX heightY : Nat) (x y : ProtocolState) : Prop :=
  (∀ hash, bucketView heightX x hash = bucketView heightY y hash) ∧
  (∀ hash, lookupView heightX x hash = lookupView heightY y hash) ∧
  (∀ proxy, registryView x proxy = registryView y proxy) ∧
  x.activeEntry = y.activeEntry ∧
  -- The active row is read through `activeEntryRow` even after `bucketView` drops it.
  (∀ id, x.activeEntry = some id →
    (activeEntryRow x id).map Prod.snd = (activeEntryRow y id).map Prod.snd) ∧
  x.incomingCursor = y.incomingCursor ∧
  x.outgoingCursor = y.outgoingCursor ∧ x.structuralHash = y.structuralHash ∧
  x.crossChainHash = y.crossChainHash

def normalizeLoadContext (context : LoadContext) : LoadContext := { context with height := 0 }

/-- Remove heights from suspended controls; a pending inbound load is related separately. -/
def normalizeControl : ProtocolControl → ProtocolControl
  | .load batch context => .load batch (normalizeLoadContext context)
  | .inboundEntry hash batch context => .inboundEntry hash batch (normalizeLoadContext context)
  | .selectInbound hash loaded =>
      .selectInbound hash { loaded with state := {}, context := normalizeLoadContext loaded.context }
  | other => other

def normalizeContext (context : ProtocolContext) : ProtocolContext :=
  { context with height := 0, control := normalizeControl context.control }

def pendingLoadedState : ProtocolControl → Option ProtocolState
  | .selectInbound _ loaded => some loaded.state
  | _ => none

/-- A suspended load stamps rows with its own height, so it must equal the context height. -/
def loadHeightMatches (context : ProtocolContext) : Prop :=
  match context.control with
  | .load _ load | .inboundEntry _ _ load => load.height = context.height
  | .selectInbound _ loaded => loaded.context.height = context.height
  | _ => True

def ContextRelated (heightX heightY : Nat) (x y : ProtocolContext) : Prop :=
  normalizeContext x = normalizeContext y ∧ loadHeightMatches x ∧ loadHeightMatches y ∧
  match pendingLoadedState x.control, pendingLoadedState y.control with
  | some a, some b => ProtocolRelated heightX heightY a b
  | none, none => True
  | _, _ => False

/-! ## State relation (spec section 5.8) -/

/-- Storage at non-protocol footprint locations, account projections, and protocol state. -/
def WorldRelated (M : EvmModel) (footprint : Footprint) (heightX heightY : Nat)
    (x y : M.World) : Prop :=
  (∀ location ∈ footprint.storageReads, ¬ M.protocolOwned location →
    M.storageValue x location = M.storageValue y location) ∧
  (∀ address ∈ footprint.accounts,
    accountProjection (M.accountView x address) = accountProjection (M.accountView y address)) ∧
  ProtocolRelated heightX heightY (M.readProtocol x) (M.readProtocol y)

/-- An allowed `GAS` result is the only stack word exempt from equality, until its call. -/
def gasOperandPending (trace : Trace) : Bool :=
  ((engineEvents trace).getLast?.map (·.instruction == gasInstruction)).getD false

def MachineRelated (pending : Bool) (x y : MachineView) : Prop :=
  if pending then { x with stack := x.stack.drop 1 } = { y with stack := y.stack.drop 1 } else x = y

def FramesRelated (M : EvmModel) (pending : Bool) (envX envY : M.Environment)
    (x y : List M.Frame) : Prop :=
  x.length = y.length ∧
  ∀ (i : Nat) fx fy, x[i]? = some fx → y[i]? = some fy →
    MachineRelated (pending && i == 0) (M.machineView fx envX) (M.machineView fy envY)

def CheckpointRelated (M : EvmModel) (footprint : Footprint) (heightX heightY : Nat)
    (envX envY : M.Environment) (x y : FrameCheckpoint M) : Prop :=
  x.kind = y.kind ∧ x.roles = y.roles ∧ FramesRelated M false envX envY x.frames y.frames ∧
  WorldRelated M footprint heightX heightY x.world y.world ∧
  ContextRelated heightX heightY x.protocol y.protocol ∧
  x.scopes = y.scopes ∧ x.probe = y.probe ∧ x.pendingTransport = y.pendingTransport ∧
  x.liveValidations = y.liveValidations

/-- `Related(F, s_X, s_Y)`. Balances, nonzero nonce magnitudes, gas, fees, logs, and envelope
    resource fields are not compared; the resource plan constrains them. -/
def Related (M : EvmModel) (_p : Parameters) (footprint : Footprint)
    (x y : ExecutionState M) : Prop :=
  let hx := x.protocol.height
  let hy := y.protocol.height
  x.phase = y.phase ∧ x.driverIndex = y.driverIndex ∧ x.roles = y.roles ∧
  M.chainId x.environment = M.chainId y.environment ∧
  FramesRelated M (gasOperandPending x.attempted) x.environment y.environment x.frames y.frames ∧
  WorldRelated M footprint hx hy x.world y.world ∧
  ContextRelated hx hy x.protocol y.protocol ∧
  x.checkpoints.length = y.checkpoints.length ∧
  (∀ (i : Nat) cx cy, x.checkpoints[i]? = some cx → y.checkpoints[i]? = some cy →
    CheckpointRelated M footprint hx hy x.environment y.environment cx cy) ∧
  (∀ wx wy, x.transactionStart = some wx → y.transactionStart = some wy →
    WorldRelated M footprint hx hy wx wy) ∧
  x.transactionStart.isSome = y.transactionStart.isSome ∧
  x.scopes = y.scopes ∧ x.completedScopes = y.completedScopes ∧
  x.liveValidations = y.liveValidations ∧ x.pendingOutcome = y.pendingOutcome ∧
  x.probe = y.probe ∧ x.pendingTransport = y.pendingTransport ∧
  x.nextInvocation = y.nextInvocation ∧
  x.transactions.map (fun t => (t.outcome, t.committedValidations)) =
    y.transactions.map (fun t => (t.outcome, t.committedValidations))

/-- `InitialRelated`: the relation at the two driver prestates. -/
def InitialRelated (M : EvmModel) (p : Parameters) (footprint : Footprint)
    (reference replay : Configuration M) : Prop :=
  Related M p footprint (initialState reference) (initialState replay)

/-- `SetupCompatible`: related initial queues and records under the concrete loader and
    selector rules, and an available intended occurrence. Successful loading is not assumed. -/
def SetupCompatible (M : EvmModel) (_p : Parameters) (reference replay : Configuration M) : Prop :=
  ProtocolRelated reference.height replay.height
    (M.readProtocol reference.initialWorld) (M.readProtocol replay.initialWorld) ∧
  match reference.selected with
  | .driverLoaded _ _ => True
  | id => ∃ hash, (id, some reference.selectedEntry, Freshness.current) ∈
      bucketView reference.height (M.readProtocol reference.initialWorld) hash

/-- Manager entry points without a modeled transition (public getters exposing freshness
    stamps, permissionless proxy creation, malformed calldata) are excluded from the reference. -/
def NoUnmodeledManagerEntry {M : EvmModel} (reference : Configuration M)
    (referenceRun : ExecutionRecord M) : Prop :=
  ∀ state ∈ referenceStates reference referenceRun, state.protocol.control ≠ .rejectEntry

/-! ## A6 reference restrictions and A8 bounds -/

/-- The first theorem excludes reference gas-induced inner failures, including probe failures. -/
def NoGasInducedFailure {M : EvmModel} (reference : Configuration M)
    (referenceRun : ExecutionRecord M) : Prop :=
  ∀ state ∈ referenceStates reference referenceRun,
    state.pendingOutcome ≠ some (.exceptional .outOfGas) ∧
    ∀ probe, state.probe = some probe → probe.outcome ≠ .exceptional .outOfGas

/-- Spec section 5.7: 256-bit freshness arithmetic and `uint64` lookup-key casts. -/
def HeightBounds (M : EvmModel) (reference : Configuration M) (referenceRun : ExecutionRecord M)
    (replay : Configuration M) : Prop :=
  reference.height + 1 < 2 ^ 256 ∧ replay.height + 1 < 2 ^ 256 ∧
  ∀ state ∈ referenceStates reference referenceRun,
    (M.readProtocol state.world).incomingCursor < 2 ^ 64 ∧
    (M.readProtocol state.world).outgoingCursor < 2 ^ 64 ∧
    state.protocol.lookupContext < 2 ^ 64

/-! ## Admissibility -/

/-- Spec section 5.8 `AllowedReplay`. Reference validity is a separate theorem premise. -/
def AllowedReplay (M : EvmModel) (p : Parameters) (reference : Configuration M)
    (referenceRun : ExecutionRecord M) (replay : Configuration M) : Prop :=
  let footprint := replayFootprint M reference referenceRun replay
  let trace := (recordFinal reference referenceRun).attempted
  p.revision.isPinned ∧
  DriverAllowed M p reference ∧ DriverAllowed M p replay ∧
  SameLogicalInputs reference replay ∧
  TraceAllowed p trace ∧ NoProtocolCoordinateAccess M trace ∧
  InitialRelated M p footprint reference replay ∧
  SetupCompatible M p reference replay ∧
  HeightBounds M reference referenceRun replay ∧
  NoGasInducedFailure reference referenceRun ∧ NoUnmodeledManagerEntry reference referenceRun ∧
  (∃ plan, BudgetOK M p reference referenceRun reference plan) ∧
  ∃ plan, BudgetOK M p reference referenceRun replay plan

end EvmYul.CrossChainReplay

import EvmYul.CrossChainReplay.Hashing

namespace EvmYul.CrossChainReplay

structure StorageLocation where
  chain : Word
  owner : Address
  slot : Word
  deriving Repr, BEq

inductive AccessKind where
  | functionalRead | meteringRead | write
  deriving Repr, BEq

structure StorageAccess where
  location : StorageLocation
  kind : AccessKind
  readValue : Option Word := none
  deriving Repr, BEq

inductive ResourceAction where
  | chargeGas (amount : Nat)
  | forwardGas (amount : Nat)
  | transfer (source target : Address) (amount : Word)
  | incrementNonce (address : Address)
  | accessAccount (address : Address)
  | refund (amount : Nat)
  deriving Repr, BEq

structure EngineObservation where
  frame : Nat
  instruction : String
  accesses : List StorageAccess
  accounts : List Address
  nativeOperation : Option String
  resources : List ResourceAction
  rawLogs : List Bytes
  deriving Repr, BEq

inductive CheckId where
  | authorization | peer | callHash | staticMode | value | revertSpan
  | structuralHash | crossChainHash | incomingConsumed | outgoingConsumed
  | lookupFreshness | lookupHash | transportSelector | transportLength
  deriving Repr, BEq

structure ValidationResult where
  selected : EntryId
  structuralHash : Hash32
  crossChainHash : Hash32
  incomingConsumed : Nat
  outgoingConsumed : Nat
  deriving Repr, BEq

inductive ProtocolObservation where
  | access (access : StorageAccess) (accounts : List Address)
  | check (scope : ScopeId) (predicate : CheckId) (passed : Bool)
  | boundary (scope : ScopeId) (hash : Hash32) (success : Bool) (data : Bytes)
  | structural (scope : ScopeId) (event : StructuralEvent)
  | staticResult (scope : ScopeId) (success : Bool) (data : Bytes)
  | validation (result : ValidationResult)
  | failure (scope : Option ScopeId) (reason : String)
  deriving Repr, BEq

inductive Observation where
  | engine (event : EngineObservation)
  | protocol (event : ProtocolObservation)
  deriving Repr, BEq

abbrev Trace := List Observation

/-- Functional state at an instruction checkpoint, apart from resources. -/
structure MachineView where
  code : Bytes
  pc : Nat
  stack : List Word
  memory : Bytes
  returnData : Bytes
  depth : Nat
  address : Address
  caller : Address
  origin : Address
  calldata : Bytes
  value : Word
  staticPermission : Bool
  deriving Repr, BEq

structure AccountView where
  present : Bool
  balance : Nat
  nonce : Nat
  storedCode : Bytes
  resolvedCode : Bytes
  delegationTarget : Option Address
  empty : Bool
  creationEligible : Bool
  deriving Repr, BEq

structure AccountProjection where
  present : Bool
  storedCode : Bytes
  resolvedCode : Bytes
  delegationTarget : Option Address
  nonceZero : Bool
  empty : Bool
  creationEligible : Bool
  deriving Repr, BEq

def accountProjection (view : AccountView) : AccountProjection :=
  { present := view.present, storedCode := view.storedCode,
    resolvedCode := view.resolvedCode, delegationTarget := view.delegationTarget,
    nonceZero := view.nonce == 0, empty := view.empty,
    creationEligible := view.creationEligible }

end EvmYul.CrossChainReplay

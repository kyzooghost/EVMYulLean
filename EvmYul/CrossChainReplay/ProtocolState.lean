import EvmYul.CrossChainReplay.Hashing

namespace EvmYul.CrossChainReplay

structure LoadedEntry where
  id : EntryId
  row : Entry
  loadedBlock : Nat
  consumed : Bool
  deriving Repr, BEq

structure EntryBucket where
  hash : Hash32
  rows : List LoadedEntry
  head : Nat
  deriving Repr, BEq

structure LoadedLookup where
  row : TopLevelLookup
  loadedBlock : Nat
  id : EntryId := .preloaded 0
  deriving Repr, BEq

structure ProxyRegistration where
  proxy : Address
  originalAddress : Address
  originalRollup : Word
  deriving Repr, BEq

structure ProtocolState where
  buckets : List EntryBucket := []
  lookups : List LoadedLookup := []
  registry : List ProxyRegistration := []
  activeEntry : Option EntryId := none
  incomingCursor : Nat := 0
  outgoingCursor : Nat := 0
  structuralHash : Hash32 := zeroHash
  crossChainHash : Hash32 := zeroHash
  deriving Repr, BEq

structure LoadBatch where
  entries : List Entry
  lookups : List TopLevelLookup
  deriving Repr, BEq

structure LoadContext where
  height : Nat
  loadIndex : Nat
  route : RequestRoute
  caller : Address
  attachedValue : Word
  deriving Repr, BEq

structure LoadResult where
  state : ProtocolState
  newlyLoaded : List EntryId
  batch : LoadBatch
  context : LoadContext
  deriving Repr, BEq

structure LookupKey where
  callHash : Hash32
  callNumber : Nat
  outgoingCursor : Nat
  contextIndex : Nat
  deriving Repr, BEq

/-- Decoded arguments and actual caller/value at the manager boundary. -/
structure ManagerInvocation where
  proxy : Address
  source : Address
  value : Word
  data : Bytes
  isStatic : Bool
  deriving Repr, BEq

inductive ProcessDestination where
  | entryValidation
  | lookupValidation (lookup : NestedLookup)
  | outgoingCompletion (callHash : Hash32) (returnData : Bytes) (number : Nat)
  | spanTransport
  deriving Repr, BEq

inductive ProtocolControl where
  | idle
  | invoke (invocation : ManagerInvocation)
  | managerRoute (invocation : ManagerInvocation) (registered : ProxyRegistration)
  | resumeSystem (invocation : ManagerInvocation) (registered : ProxyRegistration) (success : Bool)
  | resolveTopLookup (hash : Hash32) (peer : Word) (staticMode : Bool)
  | load (batch : LoadBatch) (context : LoadContext)
  | selectProxy (hash : Hash32) (peer : Word)
  | selectInbound (hash : Hash32) (loaded : LoadResult)
  | processIncoming (scope : ScopeId) (count processed : Nat) (destination : ProcessDestination)
  | readyIncoming (row : IncomingCall) (scope : ScopeId) (count processed : Nat)
      (destination : ProcessDestination) (callHash : Hash32)
  | resumeIncoming (scope : ScopeId) (count processed : Nat) (destination : ProcessDestination) (callHash : Hash32)
      (success : Bool) (returnData : Bytes)
  | resumeSpan (scope : ScopeId) (count processed : Nat) (destination : ProcessDestination)
      (savedCursor span : Nat) (success : Bool) (data : Bytes)
  | consumeOutgoing (scope : ScopeId) (callHash : Hash32) (callerPeer : Word)
  | resolveLookup (scope : ScopeId) (key : LookupKey) (staticMode : Bool)
      (callerPeer : Word)
  | staticRows (scope : ScopeId) (lookup : NestedLookup) (index : Nat)
      (rollingHash crossChainHash : Hash32)
  | resumeStatic (scope : ScopeId) (lookup : NestedLookup) (index : Nat)
      (rollingHash crossChainHash callHash : Hash32) (success : Bool) (data : Bytes)
  | validate (scope : ScopeId)
  | validateLookup (scope : ScopeId) (lookup : NestedLookup)
  | finished
  deriving Repr, BEq

structure ProtocolContext where
  activeScope : Option ScopeId
  hostEntry : Option EntryId
  route : RequestRoute
  height : Nat
  lookupContext : Nat
  control : ProtocolControl
  activeLookupIndex : Option Nat := none
  activeLookupPeer : Option Word := none
  lookupHost : Option Hash32 := none
  invocationSerial : Nat := 0
  deriving Repr, BEq

end EvmYul.CrossChainReplay

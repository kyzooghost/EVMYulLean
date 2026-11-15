import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul.CrossChainReplay

abbrev Bytes := List UInt8
abbrev Address := EvmYul.AccountAddress
abbrev Word := EvmYul.UInt256
abbrev Hash32 := Vector UInt8 32
abbrev HashFn := Bytes → Hash32

def zeroHash : Hash32 := Vector.replicate 32 0
def maxRollupId : Nat := 2 ^ 63 - 1
def nonceLimit : Nat := 2 ^ 64 - 1
def proxyProbeGas : Nat := 1000

/-- The eight ABI fields hashed for a logical cross-chain call. Gas is fixed to zero. -/
structure CallIdentity where
  isStatic : Bool
  sourceAddress : Address
  sourceRollupId : Word
  targetAddress : Address
  targetRollupId : Word
  value : Word
  data : Bytes
  deriving Repr, BEq

/-- One local call in the flat incoming table. Operational loadedBlock is absent. -/
structure IncomingCall where
  isStatic : Bool
  targetAddress : Address
  value : Word
  data : Bytes
  sourceAddress : Address
  sourceRollupId : Word
  revertSpan : Word
  deriving Repr, BEq

structure OutgoingCall where
  crossChainCallHash : Hash32
  callCount : Word
  returnData : Bytes
  deriving Repr, BEq

structure NestedLookup where
  crossChainCallHash : Hash32
  returnData : Bytes
  failed : Bool
  callNumber : Nat
  lastOutgoingCallConsumed : Nat
  executingLookupIndex : Nat
  incomingCalls : List IncomingCall
  expectedOutgoingCalls : List OutgoingCall
  callCount : Word
  rollingHash : Hash32
  crossChainRollingHash : Hash32
  deriving Repr, BEq

structure TopLevelLookup where
  declaredPeerRollup : Word
  crossChainCallHash : Hash32
  returnData : Bytes
  failed : Bool
  incomingCalls : List IncomingCall
  expectedOutgoingCalls : List OutgoingCall
  expectedLookups : List NestedLookup
  callCount : Word
  rollingHash : Hash32
  crossChainRollingHash : Hash32
  deriving Repr, BEq

structure Entry where
  declaredPeerRollup : Word
  proxyEntryHash : Hash32
  incomingCalls : List IncomingCall
  expectedOutgoingCalls : List OutgoingCall
  expectedLookups : List NestedLookup
  callCount : Word
  returnData : Bytes
  rollingHash : Hash32
  crossChainRollingHash : Hash32
  deriving Repr, BEq

structure Bundle where
  entries : List Entry
  lookups : List TopLevelLookup
  deriving Repr, BEq

/-- Logical identity is independent of a hash bucket's physical index. -/
inductive EntryId where
  | preloaded (bucketOccurrence : Nat)
  | driverLoaded (loadIndex rowIndex : Nat)
  | topLevelLookup (loadIndex : Nat) (hash : Hash32)
  deriving Repr, BEq, DecidableEq

structure ScopeId where
  entry : EntryId
  invocationPath : List Nat
  deriving Repr, BEq, DecidableEq

inductive RequestRoute where
  | proxy | systemInbound | staticLookup
  deriving Repr, BEq, DecidableEq

inductive TransactionKind where
  | call | contractCreation | authorization
  deriving Repr, BEq, DecidableEq

structure LogicalRequest where
  route : RequestRoute
  caller : Address
  originalCaller : Address
  target : Address
  value : Word
  data : Bytes
  isStatic : Bool
  deriving Repr, BEq

structure DriverEnvelope where
  kind : TransactionKind
  sender : Address
  /-- Concrete nonce; a re-signed replay envelope may differ (spec section 3.1). -/
  nonce : Nat
  destination : Option Address
  value : Word
  data : Bytes
  gasLimit : Nat
  gasPrice : Nat
  blockPosition : Nat
  deriving Repr, BEq

/-- An immutable execution-spec revision must identify all enabled native mechanisms. -/
structure RevisionDescriptor where
  name : String
  specificationId : String
  enabledOperations : List String
  nativeOperations : List String
  deriving Repr, BEq

def RevisionDescriptor.isPinned (v : RevisionDescriptor) : Prop :=
  v.specificationId ≠ ""

/-- Decoded manager calldata for the external entry points used by drivers and proxies. -/
inductive ManagerEntryCall where
  | loadTable (entries : List Entry) (lookups : List TopLevelLookup)
  | executeInbound (expectedHash : Hash32) (entries : List Entry) (lookups : List TopLevelLookup)
  | executeCrossChain (source : Address) (data : Bytes)
  | staticLookup (source : Address) (data : Bytes)
  deriving Repr, BEq

structure Parameters where
  keccak : HashFn
  revision : RevisionDescriptor
  localRollup : Word
  manager : Address
  system : Address
  proxyCreationCode : Bytes
  /-- Solidity ABI decoding of manager calldata; `none` models an unmatched selector or
      malformed calldata. Correspondence with the compiled dispatcher is an obligation. -/
  decodeManagerEntry : Bytes → Option ManagerEntryCall

end EvmYul.CrossChainReplay

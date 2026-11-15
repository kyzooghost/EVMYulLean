import EvmYul.CrossChainReplay.Types

namespace EvmYul.CrossChainReplay

/-- Encode a natural number as a 32-byte unsigned big-endian word. -/
def wordBytes (n : Nat) : Bytes :=
  (List.range 32).map fun i => UInt8.ofNat ((n / 256 ^ (31 - i)) % 256)

def addressBytes (a : Address) : Bytes := wordBytes a.val
def address20Bytes (a : Address) : Bytes := (wordBytes a.val).drop 12
def boolByte (b : Bool) : UInt8 := if b then 1 else 0
def hashBytes (h : Hash32) : Bytes := h.toList

def paddedBytes (data : Bytes) : Bytes :=
  data ++ List.replicate ((32 - data.length % 32) % 32) 0

/-- ABI encoding of `(bool,address,uint256,address,uint256,uint256,uint64,bytes)`. -/
def encodeCall (c : CallIdentity) : Bytes :=
  wordBytes (if c.isStatic then 1 else 0) ++
  addressBytes c.sourceAddress ++
  wordBytes c.sourceRollupId.toNat ++
  addressBytes c.targetAddress ++
  wordBytes c.targetRollupId.toNat ++
  wordBytes c.value.toNat ++
  wordBytes 0 ++
  wordBytes 256 ++
  wordBytes c.data.length ++ paddedBytes c.data

def callHash (k : HashFn) (c : CallIdentity) : Hash32 := k (encodeCall c)

structure BoundaryRecord where
  callHash : Hash32
  success : Bool
  returnData : Bytes
  deriving Repr, BEq

/-- Raw packed fold: 32 + 32 + 1 + the unwrapped return bytes. -/
def foldBoundary (k : HashFn) (previous : Hash32) (r : BoundaryRecord) : Hash32 :=
  k (hashBytes previous ++ hashBytes r.callHash ++ [boolByte r.success] ++ r.returnData)

def crossHash (k : HashFn) (records : List BoundaryRecord) : Hash32 :=
  records.foldl (foldBoundary k) zeroHash

inductive StructuralEvent where
  | callBegin (number : Nat)
  | callEnd (number : Nat) (success : Bool) (returnData : Bytes)
  | nestedBegin (number : Nat)
  | nestedEnd (number : Nat)
  deriving Repr, BEq

def structuralBytes : StructuralEvent → Bytes
  | .callBegin n => [1] ++ wordBytes n
  | .callEnd n success data => [2] ++ wordBytes n ++ [boolByte success] ++ data
  | .nestedBegin n => [3] ++ wordBytes n
  | .nestedEnd n => [4] ++ wordBytes n

def foldStructural (k : HashFn) (previous : Hash32) (event : StructuralEvent) : Hash32 :=
  k (hashBytes previous ++ structuralBytes event)

def foldStatic (k : HashFn) (previous : Hash32) (success : Bool) (data : Bytes) : Hash32 :=
  k (hashBytes previous ++ [boolByte success] ++ data)

/-- Exact source guard identities; arguments stay typed at their use sites. -/
inductive ProtocolError where
  | unexpectedContextRevert (data : Bytes)
  | unauthorized
  | invalidRollupId
  | etherTransferFailed
  | emptyEntries
  | emptyIncomingCalls
  | valueMismatch
  | entryHashMismatch
  | nonRootCallWithValue
  | staticCallWithRevertSpan
  | duplicateLookupHash (hash : Hash32)
  | unconsumedIncomingCalls
  | unconsumedOutgoingCalls
  | revertSpanOutOfBounds (processed span frameCount : Word)
  | arrayOutOfBounds
  | unauthorizedProxy
  | notSelf
  | executionNotFound
  | rollingHashMismatch
  | crossChainRollingHashMismatch
  | entrySpansMultiplePeers (expected found : Word)
  | lookupCallProxyNotDeployed (proxy : Address)
  | staticCallWithValue
  | nonStaticSubCall
  | sameNetworkProxy (rollup : Word)
  | invalidOriginalAddress
  | rollupIdOutOfRange (rollup : Word)
  deriving Repr, BEq, DecidableEq

def contextResultSignature : String :=
  "ContextResult(bytes32,uint256,uint256,bool,bytes32)"

def selector (k : HashFn) (signature : String) : Bytes :=
  (hashBytes (k signature.toUTF8.toList)).take 4

def ProtocolError.signature : ProtocolError → String
  | .unexpectedContextRevert _ => "UnexpectedContextRevert(bytes)"
  | .unauthorized => "Unauthorized()"
  | .invalidRollupId => "InvalidRollupId()"
  | .etherTransferFailed => "EtherTransferFailed()"
  | .emptyEntries => "EmptyEntries()"
  | .emptyIncomingCalls => "EmptyIncomingCalls()"
  | .valueMismatch => "ValueMismatch()"
  | .entryHashMismatch => "EntryHashMismatch()"
  | .nonRootCallWithValue => "NonRootCallWithValue()"
  | .staticCallWithRevertSpan => "StaticCallWithRevertSpan()"
  | .duplicateLookupHash _ => "DuplicateLookupHash(bytes32)"
  | .unconsumedIncomingCalls => "UnconsumedIncomingCalls()"
  | .unconsumedOutgoingCalls => "UnconsumedOutgoingCalls()"
  | .revertSpanOutOfBounds _ _ _ => "RevertSpanOutOfBounds(uint256,uint256,uint256)"
  | .arrayOutOfBounds => "Panic(uint256)"
  | .unauthorizedProxy => "UnauthorizedProxy()"
  | .notSelf => "NotSelf()"
  | .executionNotFound => "ExecutionNotFound()"
  | .rollingHashMismatch => "RollingHashMismatch()"
  | .crossChainRollingHashMismatch => "CrossChainRollingHashMismatch()"
  | .entrySpansMultiplePeers _ _ => "EntrySpansMultiplePeers(uint256,uint256)"
  | .lookupCallProxyNotDeployed _ => "LookupCallProxyNotDeployed(address)"
  | .staticCallWithValue => "StaticCallWithValue()"
  | .nonStaticSubCall => "NonStaticSubCall()"
  | .sameNetworkProxy _ => "SameNetworkProxy(uint256)"
  | .invalidOriginalAddress => "InvalidOriginalAddress()"
  | .rollupIdOutOfRange _ => "RollupIdOutOfRange(uint256)"

def ProtocolError.arguments : ProtocolError → Bytes
  | .unexpectedContextRevert data => wordBytes 32 ++ wordBytes data.length ++ paddedBytes data
  | .duplicateLookupHash hash => hashBytes hash
  | .revertSpanOutOfBounds processed span count =>
      wordBytes processed.toNat ++ wordBytes span.toNat ++ wordBytes count.toNat
  | .arrayOutOfBounds => wordBytes 0x32
  | .entrySpansMultiplePeers expected found => wordBytes expected.toNat ++ wordBytes found.toNat
  | .lookupCallProxyNotDeployed proxy => addressBytes proxy
  | .sameNetworkProxy rollup => wordBytes rollup.toNat
  | .rollupIdOutOfRange rollup => wordBytes rollup.toNat
  | _ => []

def ProtocolError.abiBytes (k : HashFn) (e : ProtocolError) : Bytes :=
  selector k e.signature ++ e.arguments

structure ContextResult where
  rollingHash : Hash32
  outgoingCursor : Word
  incomingCursor : Word
  ignoredFlagWord : Word
  crossChainHash : Hash32
  deriving Repr, BEq, DecidableEq

def encodeContextResult (k : HashFn) (result : ContextResult) : Bytes :=
  selector k contextResultSignature ++ hashBytes result.rollingHash ++
  wordBytes result.outgoingCursor.toNat ++ wordBytes result.incomingCursor.toNat ++
  wordBytes result.ignoredFlagWord.toNat ++ hashBytes result.crossChainHash

def encodeExecuteOnBehalf (k : HashFn) (destination : Address) (data : Bytes) : Bytes :=
  selector k "executeOnBehalf(address,bytes)" ++ addressBytes destination ++
    wordBytes 64 ++ wordBytes data.length ++ paddedBytes data

def encodeManagerInvoke (k : HashFn) (staticMode : Bool) (source : Address) (data : Bytes) : Bytes :=
  selector k (if staticMode then "staticCallLookup(address,bytes)" else "executeCrossChainCall(address,bytes)") ++
    addressBytes source ++ wordBytes 64 ++ wordBytes data.length ++ paddedBytes data

def encodeBytesReturn (data : Bytes) : Bytes :=
  wordBytes 32 ++ wordBytes data.length ++ paddedBytes data

def natFromBytes (bytes : Bytes) : Nat :=
  bytes.foldl (fun n b => n * 256 + b.toNat) 0

/-- Exact CREATE2 address formula for the source proxy constructor. -/
def proxySalt (p : Parameters) (original : Address) (rollup : Word) : Hash32 :=
  p.keccak (wordBytes rollup.toNat ++ address20Bytes original)

def proxyInitCode (p : Parameters) (original : Address) (rollup : Word) : Bytes :=
  p.proxyCreationCode ++ addressBytes p.manager ++ addressBytes original ++ wordBytes rollup.toNat

def create2Address (k : HashFn) (creator : Address) (salt : Hash32) (initCode : Bytes) : Address :=
  let digest := k ([0xff] ++ address20Bytes creator ++ hashBytes salt ++ hashBytes (k initCode))
  Fin.ofNat EvmYul.AccountAddress.size (natFromBytes ((hashBytes digest).drop 12))

def proxyAddress (p : Parameters) (original : Address) (rollup : Word) : Address :=
  create2Address p.keccak p.manager (proxySalt p original rollup) (proxyInitCode p original rollup)

def wordAt (bytes : Bytes) (offset : Nat) : Word :=
  EvmYul.UInt256.ofNat (natFromBytes ((bytes.drop offset).take 32))

def hashAt (bytes : Bytes) (offset : Nat) : Hash32 :=
  Vector.ofFn fun i => (bytes[offset + i.val]?).getD 0

/-- Matches `_decodeContextResult`: selector and minimum length only. -/
def decodeContextResult (k : HashFn) (data : Bytes) : Except ProtocolError ContextResult := do
  if data.take 4 != selector k contextResultSignature || data.length < 164 then
    throw (.unexpectedContextRevert data)
  return {
    rollingHash := hashAt data 4
    outgoingCursor := wordAt data 36
    incomingCursor := wordAt data 68
    ignoredFlagWord := wordAt data 100
    crossChainHash := hashAt data 132 }

end EvmYul.CrossChainReplay

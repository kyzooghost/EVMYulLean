import EvmYul.CrossChainReplay.Protocol

open EvmYul.CrossChainReplay

namespace QueuesCheck

#check loadBatch
#check selectProxyEntry
#check selectInboundEntry
#check findNestedLookup

def testHash : Hash32 := Vector.ofFn fun i => UInt8.ofNat (i.val + 1)
def testHashFn (b : Bytes) : Hash32 := Vector.ofFn fun i => UInt8.ofNat (b.length + i.val)
def testParams : Parameters :=
  { keccak := testHashFn
    revision := { name := "fixture", specificationId := "fixture-1", enabledOperations := [], nativeOperations := [] }
    localRollup := EvmYul.UInt256.ofNat 2
    manager := 0
    system := 0
    proxyCreationCode := [], decodeManagerEntry := fun _ => none }

def sampleEntry (hash : Hash32) : Entry :=
  { declaredPeerRollup := EvmYul.UInt256.ofNat 1
    proxyEntryHash := hash
    incomingCalls := []
    expectedOutgoingCalls := []
    expectedLookups := []
    callCount := EvmYul.UInt256.ofNat 0
    returnData := []
    rollingHash := zeroHash
    crossChainRollingHash := zeroHash }

def testContext (height loadIndex : Nat) : LoadContext :=
  { height := height, loadIndex := loadIndex, route := .proxy,
    caller := 0, attachedValue := EvmYul.UInt256.ofNat 0 }

def duplicateFifo : Bool :=
  match loadBatch testParams (testContext 10 0)
    { entries := [sampleEntry testHash, sampleEntry testHash], lookups := [] } {} with
  | .error _ => false
  | .ok loaded =>
      match selectProxyEntry testParams 10 testHash (EvmYul.UInt256.ofNat 1) loaded.state with
      | .error _ => false
      | .ok (first, afterFirst) =>
          match selectProxyEntry testParams 10 testHash (EvmYul.UInt256.ofNat 1) afterFirst with
          | .error _ => false
          | .ok (second, _) => first == .driverLoaded 0 0 && second == .driverLoaded 0 1
#guard duplicateFifo

def stalePrefixRetention : Bool :=
  match loadBatch testParams (testContext 10 0)
    { entries := [sampleEntry testHash, sampleEntry testHash], lookups := [] } {} with
  | .error _ => false
  | .ok loaded =>
      match selectProxyEntry testParams 10 testHash (EvmYul.UInt256.ofNat 1) loaded.state with
      | .error _ => false
      | .ok (_, state) =>
          match loadBatch testParams (testContext 10 1)
            { entries := [sampleEntry testHash], lookups := [] } state with
          | .error _ => false
          | .ok reloaded =>
              match bucketFor testHash reloaded.state with
              | none => false
              | some bucket => bucket.rows.map (·.id) ==
                  [.driverLoaded 0 0, .driverLoaded 0 1, .driverLoaded 1 0] &&
                  nextFreshHead 10 testHash reloaded.state == 1
#guard stalePrefixRetention

def staleBucketReset : Bool :=
  match loadBatch testParams (testContext 10 0)
    { entries := [sampleEntry testHash], lookups := [] } {} with
  | .error _ => false
  | .ok loaded =>
      match loadBatch testParams (testContext 11 1)
        { entries := [sampleEntry testHash], lookups := [] } loaded.state with
      | .error _ => false
      | .ok reloaded => (bucketFor testHash reloaded.state).map (fun b => b.rows.map (·.id)) ==
          some [.driverLoaded 1 0]
#guard staleBucketReset

def rootCall : IncomingCall :=
  { isStatic := false, targetAddress := 0, value := EvmYul.UInt256.ofNat 0,
    data := [3], sourceAddress := 0, sourceRollupId := EvmYul.UInt256.ofNat 1,
    revertSpan := EvmYul.UInt256.ofNat 0 }

def inboundHash : Hash32 := callHash testHashFn
  { isStatic := rootCall.isStatic, sourceAddress := rootCall.sourceAddress,
    sourceRollupId := rootCall.sourceRollupId, targetAddress := rootCall.targetAddress,
    targetRollupId := testParams.localRollup, value := rootCall.value, data := rootCall.data }

def inboundTailSelection : Bool :=
  let entry := { (sampleEntry inboundHash) with incomingCalls := [rootCall] }
  match loadBatch testParams (testContext 10 0)
    { entries := [sampleEntry inboundHash], lookups := [] } {} with
  | .error _ => false
  | .ok older =>
      match loadBatch testParams { (testContext 10 1) with route := .systemInbound }
        { entries := [entry], lookups := [] } older.state with
      | .error _ => false
      | .ok loaded =>
          match selectInboundEntry testParams inboundHash loaded with
          | .error _ => false
          | .ok (id, state) => id == .driverLoaded 1 0 &&
              ((bucketFor inboundHash state).map fun b => b.rows.map (·.consumed)) ==
                some [false, true]
#guard inboundTailSelection

def lookupRow (hash : Hash32) : TopLevelLookup :=
  { declaredPeerRollup := EvmYul.UInt256.ofNat 1, crossChainCallHash := hash,
    returnData := [], failed := false, incomingCalls := [], expectedOutgoingCalls := [],
    expectedLookups := [], callCount := EvmYul.UInt256.ofNat 0,
    rollingHash := zeroHash, crossChainRollingHash := zeroHash }

def duplicateLookupPreflight : Bool :=
  match loadBatch testParams (testContext 10 0)
    { entries := [], lookups := [lookupRow testHash, lookupRow testHash] } {} with
  | .error (.duplicateLookupHash hash) => hash == testHash
  | _ => false
#guard duplicateLookupPreflight

def lookupOverwrite : Bool :=
  match loadBatch testParams (testContext 10 0)
    { entries := [], lookups := [lookupRow testHash] } {} with
  | .error _ => false
  | .ok first =>
      match loadBatch testParams (testContext 10 1)
        { entries := [], lookups := [{ (lookupRow testHash) with returnData := [7] }] } first.state with
      | .error _ => false
      | .ok second => second.state.lookups.length == 1 &&
          second.state.lookups.head?.map (·.row.returnData) == some [7]
#guard lookupOverwrite

def nestedRow (failed : Bool) : NestedLookup :=
  { crossChainCallHash := testHash, returnData := [], failed := failed,
    callNumber := 2, lastOutgoingCallConsumed := 3, executingLookupIndex := 4,
    incomingCalls := [], expectedOutgoingCalls := [], callCount := EvmYul.UInt256.ofNat 0,
    rollingHash := zeroHash, crossChainRollingHash := zeroHash }

def nestedKey : LookupKey :=
  { callHash := testHash, callNumber := 2, outgoingCursor := 3, contextIndex := 4 }

#guard (findNestedLookup false nestedKey [nestedRow false, nestedRow true]).map (·.1) == some 1
#guard (findNestedLookup true nestedKey [nestedRow false, nestedRow true]).map (·.1) == some 0
#guard (findNestedLookup true { nestedKey with contextIndex := 5 } [nestedRow true]).isNone

def cleanupKeepsRemainder : Bool :=
  match loadBatch testParams (testContext 10 0)
    { entries := [sampleEntry testHash, sampleEntry testHash], lookups := [] } {} with
  | .error _ => false
  | .ok loaded =>
      match selectProxyEntry testParams 10 testHash (EvmYul.UInt256.ofNat 1) loaded.state with
      | .error _ => false
      | .ok (_, selected) =>
          let cleaned := clearConsumed 10 testHash 0 selected
          nextFreshHead 10 testHash cleaned == 1 &&
            (bucketFor testHash cleaned).map (fun b => b.rows.length) == some 2
#guard cleanupKeepsRemainder

def hostTableReuse : Bool :=
  let host := [nestedRow true, { (nestedRow true) with executingLookupIndex := 1 }]
  (findNestedLookup false nestedKey host).map (·.1) == some 0 &&
  (findNestedLookup false { nestedKey with contextIndex := 1 } host).map (·.1) == some 1
#guard hostTableReuse

example : lookupKeyRepresentable nestedKey := by
  unfold lookupKeyRepresentable nestedKey
  decide
example : ¬ lookupKeyRepresentable { nestedKey with contextIndex := 2 ^ 64 } := by
  unfold lookupKeyRepresentable nestedKey
  decide
example : nestedContextRepresentable (2 ^ 64 - 2) := by
  unfold nestedContextRepresentable
  decide
example : ¬ nestedContextRepresentable (2 ^ 64 - 1) := by
  unfold nestedContextRepresentable
  decide

/-- `staleRemainderDrains`: after the selected row is cleared, only a stale row remains at or
    after the head, so `_clearConsumedEntryAndDrain` drains the bucket. A live remainder keeps
    the bucket and advances the head to it. -/
def drainBucket (second : LoadedEntry) : ProtocolState :=
  { buckets := [{
      hash := testHash, head := 1, rows :=
      [{ id := .preloaded 0, row := sampleEntry testHash, loadedBlock := 11, consumed := false }, second] }] }
def staleRemainderDrains : Bool :=
  let stale : LoadedEntry := { id := .preloaded 1, row := sampleEntry testHash, loadedBlock := 5, consumed := false }
  let live : LoadedEntry := { id := .preloaded 1, row := sampleEntry testHash, loadedBlock := 11, consumed := false }
  (bucketFor testHash (clearConsumed 10 testHash 0 (drainBucket stale))).map (fun b => (b.rows.length, b.head)) ==
    some (0, 0) &&
  (bucketFor testHash (clearConsumed 10 testHash 0 (drainBucket live))).map (fun b => (b.rows.length, b.head)) ==
    some (2, 1)
#guard staleRemainderDrains

end QueuesCheck

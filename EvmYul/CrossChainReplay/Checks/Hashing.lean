import EvmYul.CrossChainReplay.Hashing

open EvmYul.CrossChainReplay

#check CallIdentity
#check IncomingCall
#check EntryId
#check RevisionDescriptor

def callWithDataLength (n : Nat) : CallIdentity :=
  { isStatic := false
    sourceAddress := 0
    sourceRollupId := EvmYul.UInt256.ofNat 1
    targetAddress := 0
    targetRollupId := EvmYul.UInt256.ofNat 2
    value := EvmYul.UInt256.ofNat 0
    data := List.replicate n 0 }

def abiLengthBoundaries : Bool :=
  ([0, 1, 32, 33].map fun n => (encodeCall (callWithDataLength n)).length)
    == [288, 320, 320, 352]
#guard abiLengthBoundaries

def toyHash (data : Bytes) : Hash32 :=
  Vector.ofFn fun i => UInt8.ofNat ((data.foldl (fun n b => n + b.toNat) 0 + i.val) % 256)

#guard ((encodeCall (callWithDataLength 0)).drop (7 * 32)).take 32 == wordBytes 256
#guard ((encodeCall (callWithDataLength 0)).drop (6 * 32)).take 32 == wordBytes 0
#guard (encodeCall (callWithDataLength 0)).take 32 == wordBytes 0
#guard encodeCall { (callWithDataLength 0) with isStatic := true } !=
  encodeCall (callWithDataLength 0)
#guard crossHash toyHash [] == zeroHash
#guard (foldBoundary toyHash zeroHash { callHash := zeroHash, success := true, returnData := [7] }) ==
  toyHash (hashBytes zeroHash ++ hashBytes zeroHash ++ [1, 7])
#guard (structuralBytes (.callBegin 1)).head? == some 1
#guard (structuralBytes (.callEnd 1 true [9])).head? == some 2
#guard (structuralBytes (.nestedBegin 1)).head? == some 3
#guard (structuralBytes (.nestedEnd 1)).head? == some 4
#guard (foldStatic toyHash zeroHash true [9]) == toyHash (hashBytes zeroHash ++ [1, 9])

def isError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

def transportBytes : Bytes :=
  selector toyHash contextResultSignature ++ List.replicate 160 0

#guard isError (decodeContextResult toyHash (transportBytes.take 163))
#guard !isError (decodeContextResult toyHash transportBytes)
#guard !isError (decodeContextResult toyHash (transportBytes ++ [99]))
#guard isError (decodeContextResult toyHash ([0, 0, 0, 0] ++ List.replicate 160 0))

def sampleContext : ContextResult :=
  { rollingHash := zeroHash
    outgoingCursor := EvmYul.UInt256.ofNat 7
    incomingCursor := EvmYul.UInt256.ofNat 9
    ignoredFlagWord := EvmYul.UInt256.ofNat 2
    crossChainHash := zeroHash }

#guard match decodeContextResult toyHash (encodeContextResult toyHash sampleContext) with
  | .ok decoded => decoded == sampleContext
  | .error _ => false
#guard (ProtocolError.abiBytes toyHash (.duplicateLookupHash zeroHash)).length == 36
#guard (ProtocolError.abiBytes toyHash (.arrayOutOfBounds)).drop 4 == wordBytes 0x32
#guard (ProtocolError.abiBytes toyHash (.unexpectedContextRevert [1])).length == 100

def proxyParams : Parameters :=
  { keccak := toyHash, revision := { name := "toy", specificationId := "toy", enabledOperations := [], nativeOperations := [] }, localRollup := EvmYul.UInt256.ofNat 2, manager := 3, system := 0, proxyCreationCode := [10, 11] }

#guard (address20Bytes (1 : Address)).length == 20
#guard (address20Bytes (1 : Address)).getLast? == some 1
#guard (proxyInitCode proxyParams 1 (EvmYul.UInt256.ofNat 2)).length == 98
#guard proxySalt proxyParams 1 (EvmYul.UInt256.ofNat 2) ==
  toyHash (wordBytes 2 ++ address20Bytes 1)
#guard (proxyAddress proxyParams 1 (EvmYul.UInt256.ofNat 2)).val ==
  natFromBytes ((hashBytes (toyHash ([0xff] ++ address20Bytes proxyParams.manager ++
    hashBytes (proxySalt proxyParams 1 (EvmYul.UInt256.ofNat 2)) ++
    hashBytes (toyHash (proxyInitCode proxyParams 1 (EvmYul.UInt256.ofNat 2)))))).drop 12)

import EvmYul.CrossChainReplay.Footprints

open EvmYul.CrossChainReplay

#check referenceFootprint
#check accountProjection

def location : StorageLocation :=
  { chain := EvmYul.UInt256.ofNat 2, owner := 0, slot := EvmYul.UInt256.ofNat 3 }

def engineEvent (kind : AccessKind) : Observation := .engine
  { frame := 1, instruction := "SLOAD", accesses := [{ location := location, kind := kind }],
    accounts := [0], nativeOperation := none, resources := [], rawLogs := [] }

def attemptedReadFootprint : Bool :=
  let trace : Trace :=
    [.protocol (.access { location := location, kind := .write } []),
     engineEvent .functionalRead,
     .protocol (.failure (some { entry := .driverLoaded 0 0, invocationPath := [1] }) "revert"),
     engineEvent .functionalRead]
  (referenceFootprint trace).storageReads.length == 2 &&
  (referenceFootprint trace).storageReads.contains location
#guard attemptedReadFootprint

#guard !(referenceFootprint [engineEvent .meteringRead]).storageReads.contains location
#guard (referenceFootprint [engineEvent .meteringRead]).meteringReads.contains location

def feeRecipient : Address := 1
def settlementTrace : Trace := [.engine
  { frame := 0, instruction := "settle", accesses := [], accounts := [], nativeOperation := none,
    resources := [.transfer 0 feeRecipient (EvmYul.UInt256.ofNat 1)], rawLogs := [] }]
#guard (referenceFootprint settlementTrace).accounts.contains feeRecipient

def accountWithNonce (nonce : Nat) : AccountView :=
  { present := true, balance := 1, nonce := nonce, storedCode := [],
    resolvedCode := [], delegationTarget := none, empty := false,
    creationEligible := false }

#guard accountProjection (accountWithNonce 3) == accountProjection (accountWithNonce 8)
#guard accountProjection (accountWithNonce 0) != accountProjection (accountWithNonce 8)

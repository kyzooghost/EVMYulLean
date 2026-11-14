import EvmYul.CrossChainReplay.ExecutionState

open EvmYul.CrossChainReplay

#check EvmModel
#check ExecutionState
#check SemanticInterfaceLaws

structure ToyWorld where
  protocol : ProtocolState
  steps : Nat
  factoryNonce : Nat := 1
  deployed : List Address := []

def toyAccount : AccountView :=
  { present := true, balance := 100, nonce := 1, storedCode := [],
    resolvedCode := [], delegationTarget := none, empty := false,
    creationEligible := false }

def toyMachine (frame : Nat) : MachineView :=
  { code := [], pc := frame, stack := [], memory := [], returnData := [], depth := 0,
    address := 0, caller := 0, origin := 0, calldata := [],
    value := EvmYul.UInt256.ofNat 0, staticPermission := false }

def toyResource : ResourceValuation :=
  { balance := fun _ => 100, nonce := fun _ => 1, gasRemaining := 100000,
    stateGasRemaining := 100000, warmedAccounts := [], warmedStorage := [], refund := 0,
    meteringValues := fun _ => EvmYul.UInt256.ofNat 0,
    savedGas := [], savedStateGas := [] }

def toyObservation : EngineObservation :=
  { frame := 0, instruction := "STEP", accesses := [], accounts := [],
    nativeOperation := none, resources := [], rawLogs := [] }

def toyDemand : ResourceDemand :=
  { minimumGas := 1, minimumStateGas := 0, requiredFunds := [],
    nonceHeadroom := [], childGasReserve := 0 }

def toyProtocolLocation : StorageLocation :=
  { chain := EvmYul.UInt256.ofNat 2, owner := 0, slot := EvmYul.UInt256.ofNat 0 }

def toyResourceTransfer (before : ResourceValuation) (action : ResourceAction)
    (after : ResourceValuation) : Prop :=
  match action with
  | .chargeGas amount => amount ≤ before.gasRemaining ∧
      after.gasRemaining = before.gasRemaining - amount
  | _ => after = before

def Toy : EvmModel :=
  { World := ToyWorld
    Frame := Nat
    Environment := Unit
    readProtocol := ToyWorld.protocol
    writeProtocol := fun w ps => { w with protocol := ps }
    storageValue := fun _ _ => EvmYul.UInt256.ofNat 0
    accountView := fun _ _ => toyAccount
    machineView := fun f _ => toyMachine f
    resourceView := fun _ _ => toyResource
    primitiveStep := fun w f _ action w' f' obs =>
      action = .continue ∧ w' = { w with steps := w.steps + 1 } ∧ f' = f ∧ obs = toyObservation
    enterFrame := fun w _ _ w' f' => w' = w ∧ f' = 0
    exitFrame := fun origin _ _ parent _ w' f' => w' = origin ∧ f' = parent
    enterCreation := fun _ _ _ _ _ _ _ _ _ _ _ => False
    rejectCreation := fun _ _ _ _ _ _ _ _ _ _ => False
    exitCreation := fun _ _ _ _ _ _ _ _ _ _ => False
    transactionBegin := fun w _ _ w' f' => w' = w ∧ f' = 0
    transactionSettle := fun w _ _ w' observations => w' = w ∧ observations = []
    transactionValid := fun _ _ => True
    settlementRecipients := fun _ => []
    localDemand := fun _ _ _ => toyDemand
    resourceTransfer := toyResourceTransfer
    protocolLocation := fun _ => toyProtocolLocation
    protocolWord := fun _ _ => EvmYul.UInt256.ofNat 0
    protocolOwned := fun loc => loc = toyProtocolLocation }

def initialToyWorld : ToyWorld := { protocol := {}, steps := 0 }

def toyHash (bytes : Bytes) : Hash32 :=
  Vector.ofFn fun i => UInt8.ofNat (bytes.length + i.val)

def toyParams : Parameters :=
  { keccak := toyHash,
    revision := { name := "toy", specificationId := "toy-1", enabledOperations := [], nativeOperations := [] },
    localRollup := EvmYul.UInt256.ofNat 2, manager := 0,
    system := 0, proxyCreationCode := [] }

def toyContext : ProtocolContext :=
  { activeScope := none, hostEntry := none, route := .proxy,
    height := 10, lookupContext := 0, control := .idle }

def toyState : ExecutionState Toy :=
  { world := initialToyWorld, environment := (), frames := [(0 : Nat)], roles := [.application],
    protocol := toyContext, driverIndex := 0, phase := .inTransaction,
    attempted := [], scopes := [], liveLogs := [], checkpoints := [],
    pendingOutcome := none, probe := none }

example : Toy.primitiveStep initialToyWorld (0 : Nat) () .continue
    { initialToyWorld with steps := 1 } (0 : Nat) toyObservation := by
  unfold Toy initialToyWorld
  simp

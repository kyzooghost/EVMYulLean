import EvmYul.CrossChainReplay.Observations

namespace EvmYul.CrossChainReplay

structure Footprint where
  storageReads : List StorageLocation := []
  meteringReads : List StorageLocation := []
  accounts : List Address := []
  deriving Repr, BEq

def addStorageAccess (f : Footprint) (access : StorageAccess) : Footprint :=
  match access.kind with
  | .functionalRead => { f with storageReads := access.location :: f.storageReads }
  | .meteringRead => { f with meteringReads := access.location :: f.meteringReads }
  | .write => f

def addResourceAccounts (f : Footprint) : List ResourceAction → Footprint
  | [] => f
  | .transfer source target _ :: rest =>
      addResourceAccounts { f with accounts := source :: target :: f.accounts } rest
  | .incrementNonce address :: rest =>
      addResourceAccounts { f with accounts := address :: f.accounts } rest
  | .accessAccount address :: rest =>
      addResourceAccounts { f with accounts := address :: f.accounts } rest
  | _ :: rest => addResourceAccounts f rest

/-- Fold the full attempted history, including observations from reverted frames. -/
def referenceFootprint (trace : Trace) : Footprint :=
  trace.foldl (fun f event =>
    match event with
    | .engine e =>
        let f := e.accesses.foldl addStorageAccess f
        addResourceAccounts { f with accounts := e.accounts ++ f.accounts } e.resources
    | .protocol (.access access accounts) =>
        addStorageAccess { f with accounts := accounts ++ f.accounts } access
    | .protocol _ => f) {}

def extendAccounts (f : Footprint) (addresses : List Address) : Footprint :=
  { f with accounts := addresses ++ f.accounts }

end EvmYul.CrossChainReplay

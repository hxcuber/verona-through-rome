import Gc.Model.Types
import Gc.Model.Helpers
import Mathlib.Data.Finset.Basic

def Region.reachableRefs (region : Region) : List Reference :=
  let bridgeRef := Reference.OId region.bridgeObjectId
  (go region.objMap.keys.length bridgeRef []).2

  where
    go (fuel : Nat) (ref : Reference) (visited : List ObjectId) : (List ObjectId × List Reference) :=
      match fuel with
      | 0 => (visited, [ref])
      | n + 1 =>
        match ref with
        | Reference.RId _ => (visited, [ref])
        | Reference.OId oid =>
          if !visited.contains oid then
            let visited' := oid :: visited
            let obj := region.objMap.lookup oid
            match obj with
            | none => (visited', [ref])
            | some obj =>
              obj.refs.foldl
                (λ (v, acc) r => let (v', acc') := go n r v
                  (v', acc ++ acc'))
                (visited', [ref])
          else
            (visited, [])

def RuntimeConfig.stackReachableRefs (cfg : RuntimeConfig) : List Reference :=
  let rootRefs := cfg.stackWithIndex >>= (fun frame => frame.varMap.entries.map (·.2))
  let (_, out) :=
    rootRefs.foldl
      (λ (v, acc) r => let (v', acc') := go cfg.objectIds.length r v
        (v', acc ++ acc'))
      ([], [])
  out

where
  go (fuel : Nat) (ref : Reference) (visited : List ObjectId) : (List ObjectId × List Reference) :=
    match fuel with
    | 0 => (visited, [ref])
    | n + 1 =>
      match ref with
      | Reference.RId _ => (visited, [ref])
      | Reference.OId oid =>
        if !visited.contains oid then
          let visited' := oid :: visited
          let loc := ref.loc? cfg
          match loc with
          | none => (visited', [ref])
          | some (Location.Stack fid) =>
            match cfg.stackWithIndex[fid]? with
            | none => (visited', [ref])
            | some frame =>
              match frame.objMap.lookup oid with
              | none => (visited', [ref])
              | some obj =>
                obj.refs.foldl
                  (λ (v, acc) r => let (v', acc') := go n r v
                    (v', acc ++ acc'))
                  (visited', [ref])
          | some (Location.Region rid) =>
            match cfg.heap.lookup rid with
            | none => (visited', [ref])
            | some region =>
              match region.objMap.lookup oid with
              | none => (visited', [ref])
              | some obj =>
                obj.refs.foldl
                  (λ (v, acc) r => let (v', acc') := go n r v
                    (v', acc ++ acc'))
                  (visited', [ref])
        else
          (visited, [])

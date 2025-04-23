import Lean4MyLib.DAG
import Std
import Lean4MyLib.MyState
open MyState
open DAG
open Std

namespace BuildSystem
universe u v

abbrev VT (k : Type) [BEq k] [Hashable k]  := HashMap k (UInt64 × (List (k×UInt64)))

structure Store (M)[Monad M](i k v:Type) where
  getInfo:i
  getValue:k->M v

def putInfo [Monad M](info:i) (store:Store M i k v):Store M i k v:={store with getInfo:=info}
def putValue [BEq k] [Monad M](key:k) (value:v) (store:Store M i k v):Store M i k v:=
  let table := fun n_key:k =>if n_key == key then return value else store.getValue n_key
  {store with getValue:=table}

def C := (Type u -> Type v)-> Type (max (u+1) v)

abbrev DirtyInfo k := List k

structure Task (c:C) (k v:Type) where
  run :(c f) -> (k->f v)->DirtyInfo k->f v

structure TaskS (M)[Monad M](i k v:Type)  where
  run : (k->StateT i M (M v))->StateT i M v

def Tasks (c : C) (k v:Type) := k  -> Option (Task c k v)

/-
MonadStateT ir と書いたときに、何が保証されているのか。
1. MonadStateT irはMonadである。 <- m extends Monadしているから。
2. MonadStateT irはirを状態として扱える <- extends MonadState
-/
def Build  (M)[Monad M](c:C) (i k v:Type):= Tasks c k (M v) -> k -> Store M i k v -> M (Store M i k v)
class MonadStateT (σ : Type u) (m : Type u → Type v) extends MonadState σ m, Monad m

instance [Monad M]: MonadStateT i (StateT i M) where

def Rebuilder (M)[Monad M](c:C) (ir k v :Type)[BEq k][Hashable k]:=k->M v->Task c k (M v)->TaskS M ir k v
def Scheduler (M)[Monad M](c:C) (i k v:Type)[BEq k][Hashable k]:= Rebuilder M c i k v-> Build M c i k v

def gets [Monad M](f:S->A) :StateT S M A:=do
  let s<-get
  return f s

structure Const (A B:Type) where
  getConst: A

instance [Append A] [EmptyCollection A]:Applicative (Const A) where
  pure _ := ⟨∅⟩
  seq f x := Const.mk (f.getConst ++ (x ()).getConst)

-- 内部で使用しているbuild関数のterminationが示せないのでunsafe
unsafe def reachableTree {A : Type} [BEq A] [Hashable A]
  (deps : A → List A) (target : A) : DAG A :=

  -- 内部関数: visited により再訪問を避ける
  let rec build (visited : HashSet A) (key : A) : (DAG A × HashSet A) :=
    if visited.contains key then
      (.Node key [], visited) -- 再訪問防止：葉として扱う
    else
      let visited := visited.insert key
      let (children, visited) :=
        deps key |>.foldl
          (fun (acc : List (DAG A) × HashSet A) depKey =>
            let (trees, visited) := acc
            let (childTree, visited') := build visited depKey
            (trees ++ [childTree], visited'))
          ([], visited)
      (.Node key children, visited)

  (build (HashSet.empty) target).fst

def liftStore [Monad M] (x:StateT i M a):StateT (Store M i k v) M a:=do
  let temp <- gets (fun s => x.run s.getInfo)
  let (action, newInfo) <- temp
  modify (putInfo newInfo)
  return action

--直接的に依存しているものを取得する
def dependencies (task:Task Applicative k v):List k:= (task.run (inferInstance : Applicative (Const (List k))) (fun key => Const.mk [key]) []).getConst
def mapM_ [Monad M](f:A->M B) (list:List A):M Unit:=discard <| list.mapM f

-- topological スケジューラの実装
unsafe def topological [Monad M][BEq k] [Hashable k] [ToString k]  : Scheduler M Applicative i k v :=
  fun rebuilder tasks target store =>

    -- 依存関係の辺を取得
    let dep (key : k) : List k := match tasks key with
      | none => []
      | some task =>dependencies task

    -- ノードの実行順序を計算
    let order : List k := DAG.toposort (reachableTree dep target)

    -- 単一のノードをビルド
    let build (key : k) : StateT (Store M i k v) M Unit := do
      let store <- get
      let tk := match tasks key with
        | none => Task.mk $ fun _ _ _ => pure (store.getValue key)
        | some task => task
      let mv := store.getValue key
      let newTask := rebuilder key mv tk
      let newValue <- liftStore (newTask.run (fun _key => return store.getValue _key))
      modify (putValue key newValue)

    execState (mapM_ build order) store


def getHash! [BEq k] [Hashable k] (vt:VT k) (key:k): UInt64 :=
  let res:= vt[key]!
  res.fst

def insertVT [BEq k] [Hashable k]  (key : k) (hash_value:UInt64) (dep_hash:List (k×UInt64)) (vt:VT k) : VT k:=
  vt.insert key (hash_value, dep_hash)

def find_dirty [BEq k] [Hashable k] (vt:VT k) (key:k)(current_hash:UInt64)(current_dep_keys:List k): DirtyInfo k :=
    match vt[key]? with
      | none => [key]
      | some (last_hash, last_dep_key_to_hash) =>
        let dirty_deps:=current_dep_keys.filter (fun current_dep_key =>
          match last_dep_key_to_hash.find? (fun (last_key,_)=>current_dep_key==last_key) with
          | none => true
          | some (_,last_hash) => getHash! vt current_dep_key != last_hash
        )
        if current_hash == last_hash
        then dirty_deps
        else key::dirty_deps

def vtRebuilderA [ToString k][Monad M][BEq k] [Hashable k] [Hashable v] : Rebuilder M Applicative (VT k) k v :=
  fun key mv task => TaskS.mk $ fun fetch => do
    let vt ← get
    let current_dep_keys := dependencies task
    let current_hash <- mv <&> (hash ·)
    let dirty_keys := find_dirty vt key current_hash current_dep_keys

    if dirty_keys.length == 0 then
      let value<- mv
      return value
    else
      let mv <- task.run (inferInstance : Applicative _) fetch dirty_keys
      let newValue <- mv
      let dep_list:=current_dep_keys.map (fun cdk=>(cdk,getHash! vt cdk))
      modify (insertVT key (hash newValue) dep_list)
      return newValue

unsafe def ninja [BEq k] [Hashable k][ToString k] [Hashable v][Monad M]:Build M Applicative (VT k) k v:=topological vtRebuilderA

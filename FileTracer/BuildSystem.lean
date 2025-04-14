import Lean4MyLib.Tree
import Std
open Tree
open Std

namespace BuildSystem
universe u v

structure Store (i k v:Type u) where
  getInfo:i
  getValue:k->v

def putInfo (info:i) (store:Store i k v):Store i k v:={store with getInfo:=info}
def putValue [BEq k] (key:k) (value:v) (store:Store i k v):Store i k v:=
  let table := fun n_key:k =>if n_key == key then value else store.getValue n_key
  {store with getValue:=table}

def C := (Type u -> Type v)-> Type (max (u+1) v)

structure Task (c:C) (k v:Type u)  where
  run :(c f) -> (k->f v)->f v

def Tasks (c : C) (k v:Type u) := k -> Option (Task c k v)

def Build  (c:C) (i k v:Type u):= Tasks c k v -> k -> Store i k v -> Store i k v
class MonadStateM (σ : Type u) (m : Type u → Type v) extends MonadState σ m, Monad m

instance : MonadStateM i (StateM i) where

def Rebuilder (c:C) (ir k v :Type u):=k->v->Task c k v->Task (MonadStateM ir) k v
def Scheduler (c:C) (i ir k v:Type u):= Rebuilder c ir k v-> Build c i k v

def execState (state:StateM S A) (init:S):S:=(state.run init).snd

def gets (f:S->A) :StateM S A:=do
  let s<-get
  return f s

structure Const (A B:Type) where
  getConst: A

instance [Append A] [EmptyCollection A]:Applicative (Const A) where
  pure _ := ⟨∅⟩
  seq f x := Const.mk (f.getConst ++ (x ()).getConst)

-- 内部で使用しているbuild関数のterminationが示せないのでunsafe
unsafe def reachableTree {A : Type} [BEq A] [Hashable A]
  (deps : A → List A) (target : A) : Tree A :=

  -- 内部関数: visited により再訪問を避ける
  let rec build (visited : HashSet A) (key : A) : (Tree A × HashSet A) :=
    if visited.contains key then
      (.Node key [], visited) -- 再訪問防止：葉として扱う
    else
      let visited := visited.insert key
      let (children, visited) :=
        deps key |>.foldl
          (fun (acc : List (Tree A) × HashSet A) depKey =>
            let (trees, visited) := acc
            let (childTree, visited') := build visited depKey
            (trees ++ [childTree], visited'))
          ([], visited)
      (.Node key children, visited)

  (build (HashSet.empty) target).fst

def liftStore (x:StateM i a):StateM (Store i k v) a:=do
  let (a, newInfo) <- gets (fun s => x.run s.getInfo)
  modify (putInfo newInfo)
  return a

--直接的に依存しているものを取得する
def dependencies (task:Task Applicative k v):List k:= (task.run (inferInstance : Applicative (Const (List k))) (fun key => Const.mk [key])).getConst
def mapM_ [Monad M](f:A->M B) (list:List A):M Unit:=discard <| list.mapM f

-- topological スケジューラの実装
unsafe def topological [BEq k] [Hashable k] : Scheduler Applicative i i k v :=
  fun rebuilder tasks target store =>

    -- 依存関係の辺を取得
    let dep (key : k) : List k := match tasks key with
      | none => []
      | some task => dependencies task

    -- ノードの実行順序を計算
    let order : List k := Tree.toposort (reachableTree dep target)

    -- 単一のノードをビルド
    let build (key : k) : StateM (Store i k v) Unit := match tasks key with
      | none => return ()
      | some task => do
        let store ← get
        let value := store.getValue key
        let newTask := rebuilder key value task
        let fetch (key : k) : StateM i v := return (store.getValue key)
        let newValue <- liftStore (newTask.run (inferInstance : MonadStateM i (StateM i)) fetch)
        modify (putValue key newValue)

    execState (mapM_ build order) store

abbrev Time:=Int
def MakeInfo k [BEq k] [Hashable k]:=(Time × HashMap k Time)
def modTimeRebuilder [BEq k] [Hashable k] : Rebuilder Applicative (MakeInfo k) k v :=
  fun key value task => Task.mk $ fun _ fetch => do
    let (now, modTimes) ← get
    let dirty := match modTimes[key]? with
      | none => true
      | some time =>
          let deps := dependencies task
          deps.any (fun d =>
            match modTimes[d]? with
            | none => false
            | some depTime => depTime > time
          )

    if !dirty then
      return value
    else
      let newModTimes := modTimes.insert key (now + 1)
      modify (fun (_, _) => (now + 1, newModTimes))
      task.run (inferInstance : Applicative _) fetch

abbrev VT (k : Type) (_ : Type) [BEq k] [Hashable k]  := HashMap k (UInt64 × (List (k×UInt64)))

def getHash! [BEq k] [Hashable k] (vt:VT k v) (key:k): UInt64 :=
  let res:= vt[key]!
  res.fst

def recordVT [BEq k] [Hashable k] [Hashable v] (key : k) (value:v) (dep_hash:List (k×v)) (vt:VT k v) : VT k v:=
  vt.insert key (hash (value), dep_hash.map (fun (dkey,dvalue)=>(dkey,hash dvalue)))

def insertVT [BEq k] [Hashable k]  (key : k) (hash_value:UInt64) (dep_hash:List (k×UInt64)) (vt:VT k v) : VT k v:=
  vt.insert key (hash_value, dep_hash)

-- False -> should rebuild
-- f: functino to get new hash from key
-- vt: last infomation
def verifyVT [BEq k] [Hashable k] [Hashable v] [Monad M] (key : k) (value: v) (f:k->(M UInt64)) (vt : VT k v) :M Bool :=
  match vt[key]? with
  | none => return false
  | some (oldValueHash,deps_key_to_hash) => if oldValueHash == (hash value)
    then deps_key_to_hash.allM (fun (deps_key,deps_hash) => (fun hs =>hs == deps_hash ) <$> (f deps_key))
    else return false

def anyA [Applicative F] (list:List A) (f:A->F Bool):F Bool:=
  list.foldl (fun a x=>
    let b:=f x
    pure (· || ·) <*> a <*> b
    ) (pure false)

def vtRebuilderA [BEq k] [Hashable k] [Hashable v] : Rebuilder Applicative (VT k v) k v :=
  fun key value task => Task.mk $ fun _ fetch => do
    let vt ← get
    let current_dep_keys := dependencies task
    let dirty := match vt[key]? with
      | none => true
      | some (_, last_dep_key_to_hash) =>
          current_dep_keys.all (fun current_dep_key =>
            match last_dep_key_to_hash.find? (fun (last_key,_)=>current_dep_key==last_key) with
            | none => true
            | some (_,last_hash) => getHash! vt current_dep_key == last_hash
          )

    if !dirty then
      return value
    else
      let newValue<- task.run (inferInstance : Applicative _) fetch
      let dep_list:=current_dep_keys.map (fun cdk=>(cdk,getHash! vt cdk))
      modify (insertVT key (hash newValue) dep_list)
      return newValue

unsafe def make  [BEq k] [Hashable k]:Build Applicative (MakeInfo k) k v:=topological modTimeRebuilder
unsafe def ninja [BEq k] [Hashable k] [Hashable v]:Build Applicative (VT k v) k v:=topological vtRebuilderA

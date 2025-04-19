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

def Build  (M:Type u->Type u)[Monad M] (c:C) (i k v:Type u):= Tasks c k v -> k -> Store i k v -> M (Store i k v)
/-
MonadStateM ir と書いたときに、何が保証されているのか。
1. MonadStateM irはMonadである。 <- m extends Monadしているから。
2. MonadStateM irはirを状態として扱える <- extends MonadState
-/
class MonadStateM (σ : Type u) (m : Type u → Type v) extends MonadState σ m, Monad m

instance [Monad M]: MonadStateM i (StateT i M) where

def Rebuilder (c:C) (ir k v :Type u):=k->v->Task c k v->Task (MonadStateM ir) k v
def Scheduler (M:Type u->Type u) [Monad M] (c:C) (i ir k v:Type u):= Rebuilder c ir k v-> Build M c i k v


def execState [Monad M] (state:StateT S M A) (init:S):M S:= (state.run init) <&> (·.snd)

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

def liftStore [Monad M] (x:StateT i M a):StateT (Store i k v) M a:=do
  let store <- get
  let (action,newInfo) <- x.run store.getInfo
  modify (putInfo newInfo)
  return action

--直接的に依存しているものを取得する
def dependencies (task:Task Applicative k v):List k:= (task.run (inferInstance : Applicative (Const (List k))) (fun key => Const.mk [key])).getConst
def mapM_ [Monad M](f:A->M B) (list:List A):M Unit:=discard <| list.mapM f

-- topological スケジューラの実装
unsafe def topological [BEq k] [Hashable k] [Monad M]: Scheduler M Applicative i i k v :=
  fun rebuilder tasks target store =>

    -- 依存関係の辺を取得
    let dep (key : k) : List k := match tasks key with
      | none => []
      | some task => dependencies task

    -- ノードの実行順序を計算
    let order : List k := Tree.toposort (reachableTree dep target)

    -- 単一のノードをビルド
    let build (key : k) : StateT (Store i k v) M Unit := match tasks key with
      | none => return ()
      | some task => do
        let store ← get
        let value := store.getValue key
        let newTask := rebuilder key value task
        let fetch (key : k) : StateT i M v := return (store.getValue key)
        let newValue <- liftStore (newTask.run (inferInstance : MonadStateM i (StateT i M)) fetch)
        modify (putValue key newValue)

    execState (mapM_ build order) store

abbrev VT (k : Type) [BEq k] [Hashable k]  := HashMap k (UInt64 × (List (k×UInt64)))

def getHash! [BEq k] [Hashable k] (vt:VT k) (key:k): UInt64 :=
  let res:= vt[key]!
  res.fst

def insertVT [BEq k] [Hashable k]  (key : k) (hash_value:UInt64) (dep_hash:List (k×UInt64)) (vt:VT k) : VT k:=
  vt.insert key (hash_value, dep_hash)

def vtRebuilderA [BEq k] [Hashable k] [Hashable v] : Rebuilder Applicative (VT k) k v :=
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

unsafe def ninja [BEq k] [Hashable k] [Hashable v] [Monad M]:Build M Applicative (VT k) k v:=topological vtRebuilderA

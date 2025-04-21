import FileTracer.ninja
import FileTracer.BuildSystem
import Lean4MyLib.DAG
open DAG
open BuildSystem

abbrev BTs := BuildSystem.Tasks

def tasks:BTs Applicative String (IO String) := fun key =>
  match key with
    | "./Test/output.o"=> some (BuildSystem.Task.mk fun _ fetch dirty_keys =>
      let ks: List String := ["./Test/input1.c", "./Test/input2.c"]
      let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
      (human key ks dirty_keys "") <$> fetched)

    | "./Test/exe"=> some (BuildSystem.Task.mk fun _  fetch dirty_keys =>
      let ks: List String :=  ["./Test/output.o"]
      let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
      (human key ks dirty_keys "") <$> fetched)
    | _ => none

class HasFilePathAndComment (A:Type) where
  path:A->String
  comment:A->String

def empty:StateM S Unit := return ()
def root [Inhabited A]:  (DAG A) := DAG.Node default []

def dagToTasks [HasFilePathAndComment A] [Inhabited A] (sd:StateM (DAG A) Unit):BTs Applicative String (IO String) := fun key =>
  let ds := (execState sd root).run
  let condition:A ->Bool := (fun d => (HasFilePathAndComment.path d) == key)
  match find condition ds with
    | none => none
    | some node =>
      match node with
        | DAG.Node _ [] => none
        | DAG.Node a children =>
          some $ BuildSystem.Task.mk fun _ fetch dirty_keys =>
            let ks := (children <&> top) <&> (HasFilePathAndComment.path ·)
            let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
            (human key ks dirty_keys (HasFilePathAndComment.comment a) ) <$> fetched

structure TestA where
  path:String
  comment:String
deriving Inhabited

instance :HasFilePathAndComment TestA where
  path a:=a.path
  comment a:=a.comment

def dag :StateM (DAG TestA) Unit := do
  add {path:="./Test/exe", comment:= ""} do
    add ⟨"./Test/output.o" , "hey" ⟩ do
      add ⟨ "./Test/input1.c", ""⟩  empty
      add ⟨"./Test/input2.c" , ""⟩ empty

unsafe def main : IO Unit := do
  main_process (dagToTasks dag) "./Test/output.o"

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
      (human key ks dirty_keys) <$> fetched)

    | "./Test/exe"=> some (BuildSystem.Task.mk fun _  fetch dirty_keys =>
      let ks: List String :=  ["./Test/output.o"]
      let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
      (human key ks dirty_keys) <$> fetched)
    | _ => none

def empty:StateM S Unit := return ()
def root: (DAG String) := DAG.Node "" []
def dag:StateM (DAG String) Unit := do
  add "./Test/exe" do
    add "./Test/output.o" do
      add "./Test/input1.c" empty
      add "./Test/input2.c" empty


def dagToTasks (sd:StateM (DAG String) Unit):BTs Applicative String (IO String) := fun key =>
  let ds := (execState sd root).run
  match find (fun d => d == key) ds with
    | none => none
    | some node =>
      match node with
        | DAG.Node _ [] => none
        | DAG.Node _ children =>
          some $ BuildSystem.Task.mk fun _ fetch dirty_keys =>
            let ks := children <&> top
            let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
            (human key ks dirty_keys) <$> fetched

unsafe def main : IO Unit := do
  main_process (dagToTasks dag) "./Test/output.o"

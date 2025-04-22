import FileTracer.ninja
import FileTracer.BuildSystem
import Lean4MyLib.DAG
import FileTracer.Utils
open DAG
open BuildSystem

def tasks:Tasks Applicative String (IO ByteArray) := fun key =>
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

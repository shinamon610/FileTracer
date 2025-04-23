import FileTracer.ninja
import FileTracer.BuildSystem
import Lean4MyLib.DAG
import FileTracer.Utils
open DAG
open BuildSystem

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
  main_process (dagToTasks dag fun x:String=> IO.FS.readBinFile x) (fun x:String=> IO.FS.readBinFile x) "./Test/output.o"

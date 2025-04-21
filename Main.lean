import FileTracer.ninja
import FileTracer.BuildSystem

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

unsafe def main : IO Unit := do
  main_process tasks "./Test/output.o"

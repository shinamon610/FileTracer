import FileTracer.ninja
import Lean4MyLib.DAG
import FileTracer.BuildSystem
open DAG
open BuildSystem

class HasFilePathAndComment (A:Type) where
  path:A->String
  comment:A->String

def empty:StateM S Unit := return ()
def root [Inhabited A]:  (DAG A) := DAG.Node default []

def dagToTasks [HasFilePathAndComment A] [Inhabited A] (sd:StateM (DAG A) Unit):Tasks Applicative String (IO ByteArray) := fun key =>
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

import FileTracer.ninja
import Lean4MyLib.Tree
import FileTracer.BuildSystem
import Lean4MyLib.MyState
open MyState
open Tree
open BuildSystem

class HasFilePathAndComment (A:Type) where
  path:A->String
  comment:A->String

def root [Inhabited A]:  (Tree A) := Tree.Node default []

def dagToTasks [HasFilePathAndComment A] [Inhabited A] (sd:StateM (Tree A) Unit) (readBinIO:String ->IO ByteArray):Tasks Applicative String (IO ByteArray) := fun key =>
  let ds := (exec sd root).run
  let condition:A ->Bool := (fun d => (HasFilePathAndComment.path d) == key)
  match find condition ds with
    | none => none
    | some node =>
      match node with
        | Tree.Node _ [] => none
        | Tree.Node a children =>
          some $ BuildSystem.Task.mk fun _ fetch dirty_keys =>
            let ks := (children <&> top) <&> (HasFilePathAndComment.path ·)
            let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
            (human key ks dirty_keys (HasFilePathAndComment.comment a) readBinIO) <$> fetched

def toWinPath (path:System.FilePath):System.FilePath :=
  "C:" ++ (System.FilePath.normalize (path.toString.drop 2)).toString

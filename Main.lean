import FileTracer.BuildSystem
import Lean.Data.Json
import Std
open Std
open BuildSystem
open Lean.Json
open Lean

structure VTEntry (hashValue : UInt64) (deps : List (String × UInt64)) deriving Inhabited

def SVT := VT String

def svtToJson (svt : SVT) : Json :=
  let entries : List (Json) :=
    svt.toList.map (fun (k, (hashVal, deps)) =>
      mkObj [ ("key", toJson k)
            , ("hash", toJson hashVal)
            , ("deps", toJson (deps.map (fun (d, h) => mkObj [("depKey", toJson d), ("depHash", toJson h)])))
            ]
    )
  mkObj [ ("vt", toJson entries) ]

def svtFromJson (json : Json) : Except String SVT := do
  let vtJson ← json.getObjVal? "vt"
  let entriesJson ← vtJson.getArr?

  let mut svt : SVT := Std.HashMap.empty

  for entryJson in entriesJson do
    let keyJson ← entryJson.getObjVal? "key"
    let key ← fromJson? keyJson

    let hashJson ← entryJson.getObjVal? "hash"
    let hashVal ← fromJson? hashJson

    let depsJson ← entryJson.getObjVal? "deps"
    let depsArr ← depsJson.getArr?

    let mut deps : List (String × UInt64) := []

    for depJson in depsArr do
      let depKeyJson ← depJson.getObjVal? "depKey"
      let depKey ← fromJson? depKeyJson

      let depHashJson ← depJson.getObjVal? "depHash"
      let depHash ← fromJson? depHashJson

      deps := deps.append [(depKey, depHash)]

    svt := svt.insert key (hashVal, deps)

  return svt

def loadSVT (path : String) : IO SVT := do
  let content <- IO.FS.readFile path
  match parse content with
  | .error _ => return Std.HashMap.empty
  | .ok json =>  match (svtFromJson json) with
    | .ok val => return val
    | .error _ => return Std.HashMap.empty

def human (targetPath:String) (paths: List String) (fetched: IO (List String)):IO String := do
  println! s!"start"
  let _ <- fetched
  println! s!"target: {targetPath}"
  println! s!"paths: {String.intercalate ", " paths}"
  let stdin <- IO.getStdin
  let _ <- stdin.getLine
  IO.FS.readFile targetPath

def List.sequence {f : Type u → Type v} [Applicative f] {α : Type u} :
  List (f α) → f (List α)
| []      => pure []
| x :: xs => pure (List.cons) <*> x <*> sequence xs

def IO.sequence {α : Type} : List (IO α) → IO (List α)
| []      => pure []
| x :: xs => do
  let a ← x
  let as ← IO.sequence xs
  pure (a :: as)

def tasks:Tasks Applicative String (IO String) := fun key =>
  match key with
    | "./Test/output.o"=> some (Task.mk fun _ fetch =>
      let ks: List String := ["./Test/input1.c", "./Test/input2.c"]
      let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
      (human key ks) <$> fetched)

    | "./Test/exe"=> some (Task.mk fun _  fetch =>
      let ks: List String :=  ["./Test/output.o"]
      let fetched := (List.sequence (ks.map fetch)) <&> IO.sequence
      (human key ks) <$> fetched)
    | _ => none

def saveSVT (path : String) (vt : SVT) : IO Unit := do
  let json := svtToJson vt
  IO.FS.writeFile path json.compress

unsafe def main : IO Unit := do
  let svt_json:="svt.json"
  let svt<-loadSVT svt_json
  let init:Store IO SVT String String := ⟨svt, fun key=> do
    let n<-IO.FS.readFile key
    return n
    ⟩
  let newSvt <- (ninja tasks "./Test/exe" init) <&> fun x => x.getInfo
  saveSVT svt_json newSvt

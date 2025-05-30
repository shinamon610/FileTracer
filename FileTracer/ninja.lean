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
  let sortedEntries := List.mergeSort svt.toList (fun a b => a.fst < b.fst)
  let entries : List (Json) := sortedEntries.map (fun (k, (hashVal, deps)) =>
    let sortedDeps := List.mergeSort deps (fun a b => a.fst < b.fst)
    mkObj [ ("key", toJson k)
          , ("hash", toJson hashVal)
          , ("deps", toJson (sortedDeps.map (fun (d, h) => mkObj [("depKey", toJson d), ("depHash", toJson h)])))
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

def human (targetPath:String) (paths: List String) (dirty_keys: DirtyInfo String) (comment:String) (readBinIO:String ->IO ByteArray) (fetched: IO (List ByteArray))  :IO ByteArray := do
  let _ <- fetched
  println! s!"target: {targetPath}"
  println! s!"paths: {String.intercalate ", " paths}"
  println! s!"dirty!: {dirty_keys}"
  println! s!"comment {comment}"

  let stdin <- IO.getStdin
  let _ <- stdin.getLine
  readBinIO targetPath

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

def saveSVT (path : String) (vt : SVT) : IO Unit := do
  let json := svtToJson vt
  IO.FS.writeFile path json.pretty

unsafe def main_process (tasks:Tasks Applicative String (IO ByteArray)) (readBinIO:String ->IO ByteArray) (target: String) : IO Unit := do
  let svt_json:="ninja.json"
  let svt<-loadSVT svt_json
  let init:Store IO SVT String ByteArray := ⟨svt, fun key=> do
    let n<-readBinIO key
    return n
    ⟩
  let newSvt <- (ninja tasks target init) <&> fun x => x.getInfo
  saveSVT svt_json newSvt

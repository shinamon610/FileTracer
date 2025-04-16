import FileTracer.BuildSystem
import Lean.Data.Json
import Std
open Std
open BuildSystem
open Lean.Json
open Lean

structure VTEntry (hashValue : UInt64) (deps : List (String × UInt64)) deriving Inhabited

def SVT := VT String String

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
  | .error error => panic! error
  | .ok json =>  match (svtFromJson json) with
    | .ok val => return val
    | .error error => panic! error

def tasks:Tasks Applicative String String
| "./Test/output.o"=> some (Task.mk fun _ => fun fetch => ((· ++ ·) <$> fetch "./Test/input1.c" <*> fetch "./Test/input2.c"))
| "./Test/exe"=> some (Task.mk fun _ => fun fetch => ((fun txt=>"exe:"++txt) <$> fetch "./Test/output.o"))
| "./Test/input1.c"=> some (Task.mk fun _ => fun _ => pure "input1.c")
| "./Test/input2.c"=> some (Task.mk fun _ => fun _ => pure "input2.c")
| _ => none

def saveSVT (path : String) (vt : SVT) : IO Unit := do
  let json := svtToJson vt
  IO.FS.writeFile path json.compress

unsafe def main : IO Unit := do
  let svt_json:="svt.json"
  let svt<-loadSVT svt_json
  let init:Store SVT String String:=⟨svt, fun key=>if key=="A1" then "" else ""⟩
  let res:=(ninja tasks "./Test/exe" init).getValue
  dbg_trace res "./Test/exe"
  let new_svt:=(ninja tasks "./Test/exe" init).getInfo
  saveSVT svt_json new_svt

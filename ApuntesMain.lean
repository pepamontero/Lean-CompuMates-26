/-
Textbook Template:
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Notes for CompuMates2026 (c) 2026
Authors: Pepa Montero Jimena, Enrique Díaz Blanco, Jorge Carmona Ruber
-/

import Std.Data.HashMap
import VersoManual
import Apuntes

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open Apuntes


-- Computes the path of this very `main`, to ensure that examples get names relative to it
open Lean Elab Term Command in
#eval show CommandElabM Unit from do
  let here := (← liftTermElabM (readThe Lean.Core.Context)).fileName
  elabCommand (← `(private def $(mkIdent `mainFileName) : System.FilePath := $(quote here)))

/--
A qué archivo se copia el código de un bloque `savedLean`, según dónde esté.
-/
inductive Destino where
  /-- Fuera de los ejercicios (ejemplos, definiciones...): a los dos archivos. -/
  | ambos
  /-- Enunciado de un ejercicio (dentro de `::::ejercicio`, fuera de `:::demostracion`). -/
  | ejercicios
  /-- Demostración de un ejercicio (dentro de `:::demostracion`). -/
  | soluciones
deriving BEq

/-- The saved code of each source file, in its two versions. -/
structure Codigo where
  /-- With the exercise statements, but not their solutions. -/
  ejercicios : HashMap String String := {}
  /-- With the solutions in place of the exercise statements. -/
  soluciones : HashMap String String := {}

/-- The text of an inline as plain text, for the comments of the extracted files. -/
partial def textoPlano : Inline Manual → String
  | .text s | .linebreak s => s
  | .code s => s!"`{s}`"
  | .math _ s => s!"${s}$"
  | .emph xs | .bold xs | .concat xs | .link xs _ | .other _ xs => String.join (xs.map textoPlano).toList
  | .footnote .. | .image .. => ""

/--
A block comment with `texto`, split into lines of at most 100 characters (not counting the closing
marker). Code between backticks is never split.
-/
def comentario (texto : String) : String := Id.run do
  -- Split into words, keeping together the spaces between backticks
  let mut palabras : Array String := #[]
  let mut palabra := ""
  let mut enCodigo := false
  for c in (texto.replace "-/" "- /").toList do
    if c == '`' then enCodigo := !enCodigo
    if c.isWhitespace && !enCodigo then
      unless palabra.isEmpty do palabras := palabras.push palabra
      palabra := ""
    else
      palabra := palabra.push (if c.isWhitespace then ' ' else c)
  unless palabra.isEmpty do palabras := palabras.push palabra
  let mut lineas : Array String := #[]
  let mut linea := "/-"
  for p in palabras do
    if linea.length + 1 + p.length > 100 then
      lineas := lineas.push linea
      linea := p
    else
      linea := linea ++ " " ++ p
  return "\n".intercalate (lineas.push (linea ++ " -/")).toList

/-- While extracting a chapter: the imports and the rest of the code of each file. -/
structure Estado where
  imports : HashMap String String := {}
  codigo : Codigo := {}

/--
Extract the code of a chapter saved with `savedLean`, `savedImport` and `savedComment`, indexed by
the source file it comes from.

To make the files easier to read, each section and each environment (exercise, example...) that
saves some code gets a comment before it: the title of the section, or the label of the environment
followed by its first paragraph.
-/
partial def extraerCodigo (capitulo : Part Manual) : Codigo :=
  let estado := (Id.run ((part 1 capitulo).run {})).2
  let conImports (archivos : HashMap String String) : HashMap String String :=
    archivos.fold (init := {}) fun acc fn code =>
      acc.insert fn <| match estado.imports[fn]? with
        | some imports => imports ++ "\n" ++ code
        | none => code
  { ejercicios := conImports estado.codigo.ejercicios
    soluciones := conImports estado.codigo.soluciones }
where
  part (nivel : Nat) : Part Manual → StateM Estado Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block .ambos b
      for p in subParts do
        conCabecera s!"/-! {"".pushn '#' (nivel + 1)} {p.titleString} -/\n\n" (part (nivel + 1) p)
  /-- Appends `code` to the file `fn` of the exercises and/or the solutions, according to `destino`. -/
  save (destino : Destino) (fn code : String) : StateM Estado Unit :=
    let append (archivos : HashMap String String) :=
      archivos.alter fn fun prior => some (prior.getD "" ++ code)
    modify fun e => { e with codigo := {
      ejercicios := if destino == .soluciones then e.codigo.ejercicios else append e.codigo.ejercicios
      soluciones := if destino == .ejercicios then e.codigo.soluciones else append e.codigo.soluciones } }
  /-- Runs `x`, putting `cabecera` before the code it saves to each file (if it saves any). -/
  conCabecera (cabecera : String) (x : StateM Estado Unit) : StateM Estado Unit := do
    let fuera ← get
    set { fuera with codigo := {} }
    x
    let dentro ← get
    let juntar (fuera dentro : HashMap String String) :=
      dentro.fold (init := fuera) fun acc fn code =>
        acc.alter fn fun prior => some (prior.getD "" ++ cabecera ++ code)
    set { dentro with codigo := {
      ejercicios := juntar fuera.codigo.ejercicios dentro.codigo.ejercicios
      soluciones := juntar fuera.codigo.soluciones dentro.codigo.soluciones } }
  /-- The comment before an environment: its label, its name if it has one, and its first paragraph. -/
  cabeceraEntorno (etiqueta nombre : String) (contents : Array (Block Manual)) : String :=
    let titulo := if nombre.isEmpty then etiqueta else s!"{etiqueta} ({nombre})"
    let texto := contents.findSome? (fun | .para xs => some xs | _ => none) |>.getD #[]
    comentario (titulo ++ ". " ++ String.join (texto.map textoPlano).toList) ++ "\n"
  block (destino : Destino) : Block Manual → StateM Estado Unit
    | .other which contents => do
      if which.name == ``Block.savedLean then
        if let .arr #[.str fn, .str code] := which.data then
          save destino fn (code ++ "\n")

      if which.name == ``Block.savedImport then
        if let .arr #[.str fn, .str code] := which.data then
          modify fun e => { e with imports := e.imports.alter fn (fun prior =>
            some (prior.getD "" ++ code.trimAsciiEnd.copy ++ "\n")) }

      if which.name == ``Block.entorno then
        if let .arr #[.str clase, .str etiqueta, .str nombre] := which.data then
          -- Dentro de un ejercicio, lo que no es demostración es el enunciado.
          let destino := if clase == "ejercicio" then .ejercicios else destino
          conCabecera (cabeceraEntorno etiqueta nombre contents) do
            for b in contents do block destino b
          return

      let destino := if which.name == ``Block.demostracion then .soluciones else destino
      for b in contents do block destino b
    | .concat bs | .blockquote bs =>
      for b in bs do block destino b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block destino b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block destino b
    | .para .. | .code .. => pure ()

/-- The path of a source file relative to the directory of `ApuntesMain.lean`, if it is inside it. -/
def rutaRelativa (fn : String) : Option String := do
  let mainDir ← mainFileName.parent
  let fn' ← fn.dropPrefix? mainDir.toString
  pure (fn'.dropWhile (· ∈ System.FilePath.pathSeparators)).copy

/--
Add an "Archivos Lean" section at the end of each chapter with saved code, with the buttons to
download the skeleton and the solutions or open them in Lean web. Chapters without saved code are
left as they are.
-/
def ponerDescargas : Part Manual → Part Manual
  | .mk title titleString metadata intro capitulos =>
    .mk title titleString metadata intro (capitulos.map capitulo)
where
  capitulo (c : Part Manual) : Part Manual := Id.run do
    let codigo := extraerCodigo c
    let mut esqueletos := #[]
    let mut soluciones := #[]
    for (fn, esqueleto) in codigo.ejercicios do
      let some ruta := rutaRelativa fn
        | continue
      let nombre := (System.FilePath.mk ruta).fileStem.getD "codigo"
      esqueletos := esqueletos.push <| .other
        (Block.descargasLean "esqueleto" s!"codigo/ejercicios/{ruta}" s!"{nombre}.lean" esqueleto) #[]
      soluciones := soluciones.push <| .other
        (Block.descargasLean "soluciones" s!"codigo/soluciones/{ruta}" s!"{nombre}Soluciones.lean"
          (codigo.soluciones.getD fn "")) #[]
    if esqueletos.isEmpty then return c
    let contenido : Array (Block Manual) :=
      #[.para #[.text "El ", .emph #[.text "esqueleto"], .text " tiene todo el código del capítulo: \
          los ejemplos y los enunciados de los ejercicios (sin demostraciones)."]] ++
      esqueletos ++
      #[.para #[.text "Las ", .emph #[.text "soluciones"],
          .text " son el mismo archivo, pero con los ejercicios resueltos."]] ++
      soluciones
    let .mk title titleString metadata intro subParts := c
    return .mk title titleString metadata intro <|
      subParts.push (.mk #[.text "Archivos Lean"] "Archivos Lean" none contenido #[])

/--
Write the extracted code of each chapter to `html-multi/codigo/`, so that the site can link to it:
`ejercicios/...` has the exercise statements and `soluciones/...` has their solutions.
-/
def buildExercises (mode : Mode) (cfg : Config) (_state : TraverseState) (text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode
    | pure ()
  let .mk _ _ _ _ capitulos := text
  let dest := cfg.destination / "html-multi" / "codigo"
  let some mainDir := mainFileName.parent
    | throw <| IO.userError "Can't find directory of `ApuntesMain.lean`"

  -- Start from scratch, so that files from renamed or deleted chapters don't linger
  if (← dest.pathExists) then IO.FS.removeDirAll dest
  for capitulo in capitulos do
    let { ejercicios, soluciones } := extraerCodigo capitulo
    for (sub, code) in [("ejercicios", ejercicios), ("soluciones", soluciones)] do
      for ⟨fn, f⟩ in code do
        if let some fn' := rutaRelativa fn then
          let fn := dest / sub / fn'
          if let some parent := fn.parent then IO.FS.createDirAll parent
          IO.FS.writeFile fn f
        else
          reportError s!"Couldn't save example code. The path '{fn}' is not underneath '{mainDir}'."

/--
Translate the sidebar's "Table of Contents" label, which Verso hardcodes in English.
-/
def translateToc (mode : Mode) (cfg : Config) (_state : TraverseState) (_text : Part Manual) : BuildLogT IO Unit := do
  let dir := cfg.destination / (match mode with | .single => "html-single" | .multi => "html-multi")
  for fn in ← dir.walkDir do
    if fn.extension == some "html" then
      let html ← IO.FS.readFile fn
      let html' := html.replace "Table of Contents" "Índice"
      if html' != html then IO.FS.writeFile fn html'


def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := [Apuntes.estiloCodigo, Apuntes.estiloNotas]
  extraHead := open Verso.Output.Html in #[
    {{<link rel="preconnect" href="https://fonts.googleapis.com"/>}},
    {{<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin="anonymous"/>}},
    {{<link rel="stylesheet"
        href="https://fonts.googleapis.com/css2?family=Nunito:wght@400;600;700&display=swap"/>}}
  ]

def main := manualMain (ponerDescargas (%doc Apuntes)) (extraSteps := [buildExercises, translateToc]) (config := config)

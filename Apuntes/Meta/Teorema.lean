/-
Notes for CompuMates2026 (c) 2026
Authors: Pepa Montero Jimena, Enrique Díaz Blanco, Jorge Carmona Ruber
-/

import VersoManual
import Verso.Doc.ArgParse
import Verso.Doc.Elab

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html
open Verso.Doc.Html (HtmlT)
open Verso.Output (Html)

namespace Apuntes

/-
Entornos al estilo de los de LaTeX: teorema, lema, definición, ejemplo...

`clase` decide el color y `etiqueta` el texto de la cabecera. El nombre opcional del resultado
se pasa como argumento posicional, igual que en `:::teorema "Cantor"`.
-/
block_extension Block.entorno (clase : String) (etiqueta : String) (nombre : String) where
  data := Json.arr #[.str clase, .str etiqueta, .str nombre]

  traverse _ _ _ := pure none

  toTeX := none

  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data content => do
      let .arr #[.str clase, .str etiqueta, .str nombre] := data
        | reportError "Se esperaban tres cadenas JSON en `entorno`" *> pure .empty
      let cabecera : Html :=
        if nombre.isEmpty then Html.text true etiqueta
        else
          .seq #[
            Html.text true etiqueta,
            {{<span class="entorno-nombre">{{" (" ++ nombre ++ ")"}}</span>}}
          ]
      pure {{
        <div class={{"entorno entorno-" ++ clase}}>
          <div class="entorno-cabecera">{{cabecera}}</div>
          {{← content.mapM goB}}
        </div>
      }}

  extraCss := [
r##"
.entorno {
  margin: 1.4rem 0;
  padding: 0.1rem 0 0.1rem 1rem;
  border-left: 3px solid var(--entorno-color);
}
.entorno-cabecera {
  margin: 0.6rem 0 0.4rem 0;
  color: var(--entorno-color);
  font-family: var(--apuntes-etiqueta-font);
  font-weight: 700;
}
.entorno-nombre {
  font-weight: 400;
  font-style: italic;
  font-variant: normal;
}
.entorno > :first-child {
  margin-top: 0;
}
.entorno > :last-child {
  margin-bottom: 0;
}
.entorno-teorema {
  --entorno-color: #3b5bdb;
}
.entorno-definicion {
  --entorno-color: #0b7285;
}
.entorno-ejemplo {
  --entorno-color: #adb5bd;
}
.entorno-ejemplo > .entorno-cabecera {
  color: #868e96;
}
.entorno-observacion {
  --entorno-color: #7048e8;
}
.entorno-ejercicio {
  --entorno-color: #5b8a6c;
}
"##
  ]

structure EntornoConfig where
  /-- Nombre del resultado, opcional: `:::teorema "Cantor"`. -/
  nombre : String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def EntornoConfig.parse : ArgParse m EntornoConfig :=
  EntornoConfig.mk <$> (.positional' `nombre <|> pure "")

instance : FromArgs EntornoConfig m := ⟨EntornoConfig.parse⟩

end

def entornoDirectiva (clase etiqueta : String) : DirectiveExpanderOf EntornoConfig :=
  fun cfg stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other
        (Block.entorno $(quote clase) $(quote etiqueta) $(quote cfg.nombre))
        #[ $[ $args ],* ])

/-- Un teorema, opcionalmente con nombre. -/
@[directive]
def teorema : DirectiveExpanderOf EntornoConfig := entornoDirectiva "teorema" "Teorema"

/-- Una proposición, opcionalmente con nombre. -/
@[directive]
def proposicion : DirectiveExpanderOf EntornoConfig := entornoDirectiva "teorema" "Proposición"

/-- Un lema, opcionalmente con nombre. -/
@[directive]
def lema : DirectiveExpanderOf EntornoConfig := entornoDirectiva "teorema" "Lema"

/-- Un corolario, opcionalmente con nombre. -/
@[directive]
def corolario : DirectiveExpanderOf EntornoConfig := entornoDirectiva "teorema" "Corolario"

/-- Una definición, opcionalmente con nombre. -/
@[directive]
def definicion : DirectiveExpanderOf EntornoConfig := entornoDirectiva "definicion" "Definición"

/-- Un ejemplo, opcionalmente con nombre. -/
@[directive]
def ejemplo : DirectiveExpanderOf EntornoConfig := entornoDirectiva "ejemplo" "Ejemplo"

/-- Una observación, opcionalmente con nombre. -/
@[directive]
def observacion : DirectiveExpanderOf EntornoConfig := entornoDirectiva "observacion" "Observación"

/-- Un ejercicio, opcionalmente con nombre. -/
@[directive]
def ejercicio : DirectiveExpanderOf EntornoConfig := entornoDirectiva "ejercicio" "Ejercicio"

/-
Bloques plegados para los ejercicios: solo se ve su título y hay que pulsarlo para desplegarlos.

* `:::enunciado` guarda el enunciado en Lean, para los ejercicios en los que queremos que el
  alumno lo escriba primero. Su código se copia al archivo de ejemplos como cualquier otro.
* `:::demostracion` guarda la demostración. Su código se comprueba igual que el resto, pero
  `buildExercises` (en `ApuntesMain`) no lo copia al archivo de ejemplos.
-/
def plegableHtml (clase titulo : String) (contenido : Verso.Output.Html) : Verso.Output.Html :=
  open Verso.Output.Html in
  {{
    <details class={{"plegable " ++ clase}}>
      <summary>{{titulo}}</summary>
      {{contenido}}
    </details>
  }}

def plegableCss : String := r##"
.plegable {
  margin: 0.7rem 0 0.2rem 0;
}
.plegable > summary {
  display: inline-block;
  list-style: none;
  cursor: pointer;
  color: #5b8a6c;
  font-family: var(--apuntes-etiqueta-font);
  font-size: 0.92em;
  user-select: none;
}
.plegable > summary::-webkit-details-marker {
  display: none;
}
.plegable > summary::before {
  content: "›";
  display: inline-block;
  width: 0.9em;
  transition: transform 0.15s ease;
}
.plegable[open] > summary::before {
  transform: rotate(90deg);
}
.plegable > summary:hover {
  color: #3f6b50;
}
.plegable[open] > summary {
  margin-bottom: 0.3rem;
}
"##

block_extension Block.enunciado where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun _ goB _ _ content => do
    pure (plegableHtml "enunciado" "enunciado" (← content.mapM goB))
  extraCss := [plegableCss]

block_extension Block.demostracion where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun _ goB _ _ content => do
    pure (plegableHtml "demostracion" "demostración" (← content.mapM goB))
  extraCss := [plegableCss]

/-- El enunciado en Lean de un ejercicio, plegado. -/
@[directive]
def enunciado : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other Block.enunciado #[ $[ $args ],* ])

/-- La demostración de un ejercicio, plegada. No se copia al archivo de ejemplos. -/
@[directive]
def demostracion : DirectiveExpanderOf Unit
  | (), stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other Block.demostracion #[ $[ $args ],* ])

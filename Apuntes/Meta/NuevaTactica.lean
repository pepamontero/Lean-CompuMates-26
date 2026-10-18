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
Un recuadro destacado para presentar una táctica nueva: un rectángulo naranja de esquinas
redondeadas con una etiqueta en forma de píldora que corta el borde superior.
-/
block_extension Block.nuevaTactica (etiqueta : String) (tactica : String) where
  data := Json.arr #[.str etiqueta, .str tactica]

  traverse _ _ _ := pure none

  toTeX := none

  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data content => do
      let .arr #[.str etiqueta, .str tactica] := data
        | reportError "Se esperaban dos cadenas JSON en `nuevaTactica`" *> pure .empty
      let nombre : Html :=
        if tactica.isEmpty then .empty
        else {{<div class="nueva-tactica-nombre"><code>{{tactica}}</code></div>}}
      pure {{
        <div class="nueva-tactica">
          <span class="nueva-tactica-etiqueta">{{etiqueta}}</span>
          {{nombre}}
          {{← content.mapM goB}}
        </div>
      }}

  extraCss := [
r##"
.nueva-tactica {
  position: relative;
  margin: 2.25rem 0 1.75rem 0;
  padding: 1.5rem 1.25rem 1.1rem 1.25rem;
  border: 1px solid #e07b1f;
  border-radius: 14px;
  background: #fff8f0;
}
.nueva-tactica > .nueva-tactica-etiqueta + * {
  margin-top: 0;
}
.nueva-tactica > :last-child {
  margin-bottom: 0;
}
.nueva-tactica-etiqueta {
  position: absolute;
  top: 0;
  left: 1.25rem;
  transform: translateY(-50%);
  padding: 0.12em 0.85em;
  border: 1px solid #e07b1f;
  border-radius: 999px;
  background: #fff;
  color: #c2660c;
  font-size: 0.78rem;
  font-family: var(--apuntes-etiqueta-font);
  font-weight: 600;
  line-height: 1.6;
  white-space: nowrap;
}
.nueva-tactica-nombre {
  margin-bottom: 0.75rem;
  font-size: 1.15rem;
}
.nueva-tactica-nombre code {
  color: #a8500a;
  font-weight: 700;
}
/* Todas las tablas del libro (dentro o fuera del recuadro) llevan el mismo estilo naranja. */
table.tabular {
  margin: 1.25rem auto;
  border-spacing: 0;
  background: #fff;
  border: 1px solid #f2d3ae;
  border-radius: 10px;
  overflow: hidden;
}
.nueva-tactica table.tabular {
  margin: 1.1rem auto 0.25rem auto;
}
table.tabular th,
table.tabular td {
  padding: 0.55rem 1.75rem;
  border-bottom: 1px solid #f2d3ae;
}
table.tabular tr:last-child td {
  border-bottom: none;
}
.tactica-kw code {
  color: #c2660c;
  font-weight: 600;
}
/* Los huecos entre `<code>` contiguos se dibujan con la fuente del párrafo. Sin esto,
   `unfold inyectiva` sale más apretado que el resto del código de la tabla. */
p:has(> .tactica-kw) {
  font-family: var(--verso-code-font-family);
}
table.tabular thead th {
  background: #fdeedd;
  font-family: var(--apuntes-etiqueta-font);
  font-weight: 600;
  white-space: nowrap;
}
"##
  ]

/-
Resalta el nombre de una táctica dentro de una tabla: `{tac}`intro` `hP`` pinta `intro` de
naranja y deja `hP` en su color, que es lo que distingue la táctica de sus argumentos.
-/
inline_extension Inline.tactica where
  traverse _ _ _ := pure none

  toTeX := none

  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ _ content => do
      pure {{ <span class="tactica-kw">{{← content.mapM go}}</span> }}

/-- Resalta el nombre de una táctica, separándolo de sus argumentos. -/
@[role]
def tac : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.tactica #[$[$(← contents.mapM elabInline)],*])

structure NuevaTacticaConfig where
  /-- Texto de la píldora que corta el borde del recuadro. -/
  etiqueta : String
  /-- Nombre de la táctica, destacado dentro del recuadro. Si se omite, no se muestra. -/
  tactica : String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def NuevaTacticaConfig.parse : ArgParse m NuevaTacticaConfig :=
  NuevaTacticaConfig.mk <$>
    .namedD' `etiqueta "nueva táctica" <*>
    .namedD' `tactica ""

instance : FromArgs NuevaTacticaConfig m := ⟨NuevaTacticaConfig.parse⟩

end

/--
Presenta una táctica nueva dentro de un recuadro destacado.

El argumento `tactica` da el nombre que se muestra en grande dentro del recuadro y `etiqueta`
permite cambiar el texto de la píldora (por defecto, «nueva táctica»).
-/
@[directive]
def nuevaTactica : DirectiveExpanderOf NuevaTacticaConfig
  | cfg, stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other
        (Block.nuevaTactica $(quote cfg.etiqueta) $(quote cfg.tactica))
        #[ $[ $args ],* ])

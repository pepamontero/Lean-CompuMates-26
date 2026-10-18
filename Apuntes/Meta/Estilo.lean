/-
Notes for CompuMates2026 (c) 2026
Authors: Pepa Montero Jimena, Enrique Díaz Blanco, Jorge Carmona Ruber
-/

import VersoManual
import Verso.Doc.Elab

open Lean Elab
open Verso Doc Elab Genre.Manual

namespace Apuntes

/--
Estilo extra del libro, que `ApuntesMain` añade a la configuración con `extraCss`.

El género `Manual` no pone fondo a los bloques de código: el recuadro gris que se ve en la web
de Verso viene de `literate.css`, que pertenece a otro género. Aquí lo añadimos nosotros.
-/
def estiloCodigo : CSS := r##"
/* Fuente redondeada para todo lo que no es texto corrido: cabeceras de los entornos, etiquetas,
   plegables y cabeceras de tabla. Se carga desde Google Fonts en `ApuntesMain` (`extraHead`). */
:root {
  --apuntes-etiqueta-font: "Nunito", var(--verso-structure-font-family);
}

code.hl.lean.block {
  display: block;
  margin: 1em 0;
  padding: 0.7em 0.9em;
  background: #f6f8fa;
  border: none;
  border-radius: 8px;
  overflow-x: auto;
}

/* El código en línea del texto, con el mismo gris que los bloques y sin hacer la línea más
   alta. En las tablas no lo ponemos. */
main p code:not(.hl) {
  background: #f6f8fa;
  border-radius: 4px;
  padding: 0.05em 0.3em;
  box-decoration-break: clone;
  -webkit-box-decoration-break: clone;
}
main td code:not(.hl) {
  background: none;
  padding: 0;
}

/* Comandos de Lean escritos en el texto con `{kw}`, en negrita como en los bloques. */
.comando-kw code {
  font-weight: bold;
}
"##

/--
Las notas al margen (`{margin}[...]`) salen por defecto con el mismo tamaño y color que el texto
principal, así que no se leen como notas. Las hacemos más pequeñas y más discretas.
-/
def estiloNotas : CSS := r##"
.marginalia .note {
  font-size: 0.85em;
  line-height: 1.4;
  color: #555;
  border-left: 2px solid #ddd;
  padding: 0.2rem 0 0.2rem 0.7rem;
}

/* Verso pone el número de la nota fuera de la caja, a su izquierda; lo metemos dentro. */
.marginalia .note::before {
  position: static;
  width: auto;
  margin-right: 0.4em;
}
"##

/-
Marca un comando de Lean dentro del texto: `{kw}`#print`` lo pone en negrita, igual que se ven
`example` o `def` en los bloques de código.
-/
inline_extension Inline.comando where
  traverse _ _ _ := pure none

  toTeX := none

  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ _ content => do
      pure {{ <span class="comando-kw">{{← content.mapM go}}</span> }}

/-- Pone en negrita un comando de Lean (`#check`, `#print`...) dentro del texto. -/
@[role]
def kw : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.comando #[$[$(← contents.mapM elabInline)],*])

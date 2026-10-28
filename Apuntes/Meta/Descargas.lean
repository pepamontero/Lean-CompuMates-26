/-
Notes for CompuMates2026 (c) 2026
Authors: Pepa Montero Jimena, Enrique Díaz Blanco, Jorge Carmona Ruber
-/

import VersoManual

open Lean
open Verso Doc Genre.Manual

namespace Apuntes

/-
Botones para descargar el código de un capítulo o abrirlo en Lean web.

No se escriben a mano en los capítulos: `ApuntesMain` añade al final de cada capítulo que tenga
bloques `savedLean` una sección "Archivos Lean" con ellos.
-/

/-- Codifica un texto para meterlo en una URL, escapando todo salvo los caracteres no reservados. -/
def codificarUrl (s : String) : String := Id.run do
  let hex := "0123456789ABCDEF".toList
  let mut out := ""
  for b in s.toUTF8 do
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c ∈ ['-', '_', '.', '~'] then
      out := out.push c
    else
      out := out.push '%' |>.push hex[b.toNat / 16]! |>.push hex[b.toNat % 16]!
  return out

/-- Enlace a Lean web con `codigo` ya cargado en el editor. -/
def urlLeanWeb (codigo : String) : String :=
  "https://live.lean-lang.org/#code=" ++ codificarUrl codigo

/-
`que` es lo que se descarga ("esqueleto" o "soluciones"), `ruta` es la ruta del archivo relativa a
la raíz del sitio, `nombre` el nombre con el que se descarga y `codigo` su contenido.
-/
block_extension Block.descargasLean (que : String) (ruta : String) (nombre : String) (codigo : String) where
  data := .arr #[.str que, .str ruta, .str nombre, .str codigo]

  traverse _ _ _ := pure none

  toTeX := none

  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.str que, .str ruta, .str nombre, .str codigo] := data
        | reportError "Se esperaban cuatro cadenas JSON en `descargasLean`" *> pure .empty
      pure {{
        <div class={{"descargas-lean descargas-" ++ que}}>
          <a class="descarga-lean" href={{ruta}} download={{nombre}}>
            {{"Descargar " ++ que ++ " (.lean)"}}
          </a>
          <a class="descarga-lean" href={{urlLeanWeb codigo}} target="_blank" rel="noopener">
            {{"Abrir " ++ que ++ " en Lean web"}}
          </a>
        </div>
      }}

  extraCss := [
r##"
.descargas-lean {
  display: flex;
  flex-wrap: wrap;
  gap: 0.5rem;
  margin: 0.8rem 0 1.6rem 0;
}
.descarga-lean {
  padding: 0.35rem 0.8rem;
  border: 1px solid #5b8a6c;
  border-radius: 6px;
  color: #5b8a6c;
  font-family: var(--apuntes-etiqueta-font);
  font-size: 0.92em;
  font-weight: 600;
  text-decoration: none;
}
.descarga-lean:hover {
  background: #5b8a6c;
  color: white;
}
"##
  ]

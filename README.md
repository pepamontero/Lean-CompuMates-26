# Lean en CompuMates 2026

Apuntes del curso de Lean de CompuMates 2026 - 2027, escritos con
[Verso](https://github.com/leanprover/verso) (género `Manual`).

## Compilar

```
$ lake exe textbook
```

El HTML se genera en `_out/html-multi`. Hay que servirlo con un servidor
local (por ejemplo `python3 -m http.server` dentro de esa carpeta), no abrirlo
directamente como fichero.

## Código de los ejemplos

Los bloques ```` ```savedLean ```` (definidos en
[Apuntes/Meta/Lean.lean](Apuntes/Meta/Lean.lean)) se extraen a ficheros `.lean`
listos para abrir en el editor. El paso `buildExercises` de
[ApuntesMain.lean](ApuntesMain.lean) los recoge y los escribe en la carpeta
`example-code` de la salida. Las soluciones de los ejercicios no se copian.

## Contenido

* [P01Introduccion.lean](Apuntes/P01Introduccion.lean): qué es Lean, instalación y organización del curso.
* [P02LeanProver.lean](Apuntes/P02LeanProver.lean): teoría de tipos, proposiciones y primeras tácticas (`intro`, `exact`, `apply ... at ...`, `unfold`).

## Licencia

Autores: Pepa Montero Jimena, Enrique Díaz Blanco y Jorge Carmona Ruber.

* El texto de los apuntes se publica bajo
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/deed.es): puedes
  copiarlo y adaptarlo, también en otros cursos, citando a los autores.
* El código (los ficheros `.lean` como código Lean y los ejemplos que se
  extraen de ellos) se publica bajo [Apache 2.0](LICENSE).

El proyecto parte de la plantilla de libro de
[Verso](https://github.com/leanprover/verso), © 2024-2025 Lean FRO LLC, bajo
Apache 2.0. Los ficheros que vienen de ella lo indican en su cabecera.

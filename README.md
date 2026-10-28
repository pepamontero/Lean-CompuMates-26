# Lean en CompuMates 2026

Apuntes del curso de Lean de CompuMates 2026 - 2027, escritos con
[Verso](https://github.com/leanprover/verso) (género `Manual`).

Los apuntes se pueden ver ya compilados [aquí](https://pepamontero.github.io/Lean-CompuMates-26).

## Código de los apuntes

Cada capítulo con código termina con una sección *Archivos Lean*, en la que encontrarás dos versiones
del código visto en los apuntes. Se puede descargar un archivo `.lean` con este código o
abrirlo directamente en [Lean web](https://live.lean-lang.org). Estas dos versiones son:

* El *esqueleto*: los ejemplos, las definiciones y los enunciados de los ejercicios, con `sorry`
  en lugar de las demostraciones.
* Las *soluciones*: el mismo archivo, pero con los ejercicios resueltos.

## Contenido

* [P01Introduccion.lean](Apuntes/P01Introduccion.lean): qué es Lean, instalación y organización del curso.
* [P02LeanProver.lean](Apuntes/P02LeanProver.lean): teoría de tipos, proposiciones y primeras tácticas (`intro`, `exact`, `apply ... at ...`, `unfold`).
* [P03Logica.lean](Apuntes/P03Logica.lean): conectores lógicos (`∧`, `∨`, `¬`, `↔`) y cuantificadores (`∀`, `∃`), con las tácticas `constructor`, `obtain`, `left` / `right`, `rcases`, `rfl`, `by_contra`, `apply`, `specialize` y `use`.

## Compilar en local

Desde la raíz del repositorio:

1. Descargar/actualizar las dependencias (Verso y Mathlib). Solo hace falta la primera vez o cuando cambien las dependencias.

```bash
lake update
```

2. Generar el sitio en `_out/`. Hacer esto siempre que cambie algo de los apuntes.

```bash
lake exe textbook
```

3. Abrir un servidor en local

```bash
python3 -m http.server -d _out/html-multi
```

Abre <http://localhost:8000> en el navegador.

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

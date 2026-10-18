/-
Textbook Template:
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Notes for CompuMates2026 (c) 2026
Authors: Pepa Montero Jimena, Enrique Díaz Blanco, Jorge Carmona Ruber
-/

import VersoManual
import Apuntes.Meta.Lean
import Apuntes.Meta.NuevaTactica
import Apuntes.Meta.Estilo
import Apuntes.Meta.Teorema

-- This is a chapter that's included
import Apuntes.P01Introduccion
import Apuntes.P02LeanProver

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

open Apuntes

set_option pp.rawOnError true

#doc (Manual) "Lean at CompuMates 2026" =>

%%%
authors := ["Pepa Montero, Enrique Díaz & Jorge Carmona"]
%%%

Apuntes para el curso de Lean en CompuMates 2026.

Estos son los apuntes del curso de introducción a Lean que impartimos en CompuMates. Recogen lo
que contamos en clase, con ejemplos que puedes copiar a tu editor y ejercicios para practicar.

Los capítulos siguen el orden de las clases. La primera clase incluye la introducción, en la que contamos qué es Lean, por qué
merece la pena formalizar matemáticas y cómo instalar lo necesario, y también el segundo capítulo "Lean Theorem Prover", en el que
empezamos a escribir código y nuestras primeras demostraciones.

Iremos publicando el resto de
capítulos a medida que avance el curso.

{include 1 Apuntes.P01Introduccion}

{include 1 Apuntes.P02LeanProver}

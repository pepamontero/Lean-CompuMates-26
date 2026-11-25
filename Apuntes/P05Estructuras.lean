import VersoManual
import Apuntes.Meta.Lean
import Apuntes.Meta.NuevaTactica
import Apuntes.Meta.Estilo
import Apuntes.Meta.Teorema
import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Verso.Genre Manual

open Verso.Genre.Manual.InlineLean

open Apuntes

set_option pp.rawOnError true

#doc (Manual) "Estructuras: grupos y espacios topológicos" =>

%%%
%%%

```savedImport
import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
```
```savedComment
# Clase 4: estructuras

Tácticas nuevas: `ext` y `by_cases`.
```
```savedLean -show
namespace Clase4
```

En esta clase vamos a aprender a definir en Lean objetos matemáticos que reúnen varios datos y
varias propiedades a la vez, como los grupos o los espacios topológicos. La herramienta que usa
Lean para esto son las _estructuras_.

Antes de empezar haremos un calentamiento con conjuntos. Nos servirá para repasar las tácticas de
lógica de la segunda clase, y además los conjuntos nos harán falta más adelante para hablar de
subgrupos y de espacios topológicos.

# Conjuntos

En la clase anterior ya apareció la notación `s : Set ℝ` para hablar de un subconjunto de `ℝ`.
Ahora vamos a ver cómo se trabaja con conjuntos en general.

```savedLean -show
section Conjuntos
```

## Qué es un conjunto en Lean

Si `X` es un tipo, `Set X` es el tipo de los subconjuntos de `X`. Es decir, escribir `A : Set X`
quiere decir que `A` es un subconjunto de `X`.

```savedLean (name := checkSet)
#check Set ℝ
```
```leanOutput checkSet
Set ℝ : Type
```

Fíjate en que `Set X` es un tipo distinto para cada `X`: `Set ℕ` y `Set ℝ` son tipos diferentes,
igual que `ℕ` y `ℝ` lo son.

Si `A : Set X` y `x : X`, entonces `x ∈ A` es la proposición que afirma que `x` pertenece a `A`.
El símbolo se escribe con `\in`.

La forma más habitual de definir un conjunto es dar la propiedad que cumplen sus elementos:
`{x : X | P x}` es el conjunto de los `x : X` que cumplen `P x`.

:::definicion "números reales positivos"
```savedLean
def positivos : Set ℝ := {x : ℝ | x > 0}
```
:::

Pertenecer a un conjunto así es, por definición, cumplir la propiedad. El resultado de Mathlib
`Set.mem_setOf_eq` nos permite hacer ese cambio con `rw`: transforma `a ∈ {x | P x}` en `P a`.

:::ejemplo
El `2` es positivo.

```savedLean
example : 2 ∈ positivos := by
  unfold positivos
  rw [Set.mem_setOf_eq]
  norm_num
```
:::

:::observacion
Por dentro, Lean define un conjunto como una propiedad: `Set X` es `X → Prop`, y `x ∈ A` es
simplemente `A x`. No necesitaremos usarlo, pero explica por qué `Set.mem_setOf_eq` se demuestra
con `rfl`: las dos cosas son iguales por definición.
:::

Como pasaba con la negación o con la inyectividad, todas las operaciones con conjuntos están
definidas a partir de la lógica que ya conocemos. Por eso, para trabajar con conjuntos no
necesitamos casi ninguna táctica nueva: basta con saber qué conector lógico hay detrás de cada
operación.

## Subconjuntos

Si `A B : Set X`, entonces `A ⊆ B` (se escribe con `\subseteq`) es la proposición que afirma que
`A` es un subconjunto de `B`, es decir, que todo elemento de `A` está en `B`:

```
A ⊆ B  ↔  ∀ x, x ∈ A → x ∈ B
```

Es un cuantificador universal seguido de una implicación, así que lo manejamos con las tácticas
de siempre.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ A ⊆ B`
  * {tac}`intro` `x hx`
  * `x : X`

    `hx : x ∈ A`

    `⊢ x ∈ B`
*
  * `h : A ⊆ B`

    `hx : x ∈ A`
  * {tac}`apply` `h` {tac}`at` `hx`
  * `hx : x ∈ B`
*
  * `h : A ⊆ B`

    `hx : x ∈ A`

    `⊢ x ∈ B`
  * {tac}`exact` `h hx`
  * No goals
:::

:::observacion
Fíjate en que escribimos `h hx` y no `h x hx`. En la definición de `⊆` el `x` es implícito: Lean
lo deduce mirando `hx`, así que no hace falta dárselo.
:::

:::ejemplo
Todo conjunto es subconjunto de sí mismo.

```savedLean
example (X : Type) (A : Set X) : A ⊆ A := by
  intro x hx
  exact hx
```
:::

::::ejercicio
Si `a ∈ A`, `A ⊆ B` y `B ⊆ C`, entonces `a ∈ C`.

```savedLean
example (X : Type) (A B C : Set X) (a : X) (ha : a ∈ A)
    (hAB : A ⊆ B) (hBC : B ⊆ C) : a ∈ C := by
  sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (X : Type) (A B C : Set X) (a : X) (ha : a ∈ A)
    (hAB : A ⊆ B) (hBC : B ⊆ C) : a ∈ C := by
  apply hAB at ha
  apply hBC at ha
  exact ha
```

Aplicando las inclusiones como funciones:

```savedLean
example (X : Type) (A B C : Set X) (a : X) (ha : a ∈ A)
    (hAB : A ⊆ B) (hBC : B ⊆ C) : a ∈ C := by
  exact hBC (hAB ha)
```
:::
::::

::::ejercicio
La inclusión es transitiva: si `A ⊆ B` y `B ⊆ C`, entonces `A ⊆ C`.

```savedLean
example (X : Type) (A B C : Set X) :
    A ⊆ B → B ⊆ C → A ⊆ C := by
  sorry
```

:::demostracion
```savedLean
example (X : Type) (A B C : Set X) :
    A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC x hx
  apply hAB at hx
  apply hBC at hx
  exact hx
```

Igual que pasaba con `¬¬P`, el mismo `intro` sirve para todo: primero introduce las dos
hipótesis `hAB` y `hBC`, y después, como la tesis `A ⊆ C` es un `∀` seguido de una implicación,
el elemento `x` y la hipótesis `hx : x ∈ A`.
:::
::::

## Intersección

Si `A B : Set X`, su intersección es `A ∩ B` (se escribe con `\cap` o con `\inter`). Que un
elemento esté en la intersección quiere decir que está en los dos conjuntos:

```
x ∈ A ∩ B  ↔  x ∈ A ∧ x ∈ B
```

Es una conjunción, así que usamos las herramientas de la conjunción.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ x ∈ A ∩ B`
  * {tac}`constructor`
  * primera tesis: `⊢ x ∈ A`

    segunda tesis: `⊢ x ∈ B`
*
  * `h : x ∈ A ∩ B`
  * {tac}`obtain` `⟨hA, hB⟩ := h`
  * `hA : x ∈ A`

    `hB : x ∈ B`
*
  * `h : x ∈ A ∩ B`
  * `h.left`, `h.right`
  * `h.left : x ∈ A`

    `h.right : x ∈ B`
:::

:::ejemplo
La intersección está contenida en cada uno de los conjuntos.

```savedLean
example (X : Type) (A B : Set X) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.left
```
:::

::::ejercicio
Si `a` está en `A ∩ (B ∩ C)`, entonces está en `C`.

```savedLean
example (X : Type) (A B C : Set X) (a : X) :
    a ∈ A ∩ (B ∩ C) → a ∈ C := by
  sorry
```

:::demostracion
Con proyecciones:

```savedLean
example (X : Type) (A B C : Set X) (a : X) :
    a ∈ A ∩ (B ∩ C) → a ∈ C := by
  intro h
  exact h.right.right
```

Con `obtain`:

```savedLean
example (X : Type) (A B C : Set X) (a : X) :
    a ∈ A ∩ (B ∩ C) → a ∈ C := by
  intro h
  obtain ⟨hA, hBC⟩ := h
  obtain ⟨hB, hC⟩ := hBC
  exact hC
```
:::
::::

### Igualdad de conjuntos

Dos conjuntos son iguales cuando tienen los mismos elementos. Para demostrar una igualdad de
conjuntos necesitamos una táctica nueva, que nos deja trabajar elemento a elemento.

::::nuevaTactica (tactica := "ext")
Si la tesis es una igualdad de conjuntos `A = B`, la táctica `ext x` la sustituye por
`x ∈ A ↔ x ∈ B`, para un `x` cualquiera.

A partir de ahí seguimos como con cualquier doble implicación: `constructor` nos deja las dos
inclusiones por separado.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ A = B`
  * {tac}`ext` `x`
  * `x : X`

    `⊢ x ∈ A ↔ x ∈ B`
:::
::::

:::ejemplo
La intersección es conmutativa.

```savedLean
example (X : Type) (A B : Set X) : A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro h
    obtain ⟨hA, hB⟩ := h
    constructor
    · exact hB
    · exact hA
  · intro h
    obtain ⟨hB, hA⟩ := h
    constructor
    · exact hA
    · exact hB
```
:::

## Unión

Si `A B : Set X`, su unión es `A ∪ B` (se escribe con `\cup`). Que un elemento esté en la unión
quiere decir que está en alguno de los dos conjuntos:

```
x ∈ A ∪ B  ↔  x ∈ A ∨ x ∈ B
```

Es una disyunción, así que usamos las tácticas de la disyunción.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ x ∈ A ∪ B`
  * {tac}`left`
  * `⊢ x ∈ A`
*
  * `⊢ x ∈ A ∪ B`
  * {tac}`right`
  * `⊢ x ∈ B`
*
  * `h : x ∈ A ∪ B`

    `⊢ P`
  * {tac}`rcases` `h` {tac}`with` `hA | hB`
  * caso 1: `hA : x ∈ A`, con `⊢ P`

    caso 2: `hB : x ∈ B`, con `⊢ P`
:::

:::ejemplo
Todo conjunto está contenido en su unión con otro.

```savedLean
example (X : Type) (A B : Set X) : A ⊆ A ∪ B := by
  intro x hx
  left
  exact hx
```
:::

::::ejercicio
La unión es conmutativa.

```savedLean
example (X : Type) (A B : Set X) : A ∪ B = B ∪ A := by
  sorry
```

:::demostracion
```savedLean
example (X : Type) (A B : Set X) : A ∪ B = B ∪ A := by
  ext x
  constructor
  · intro h
    rcases h with hA | hB
    · right
      exact hA
    · left
      exact hB
  · intro h
    rcases h with hB | hA
    · right
      exact hB
    · left
      exact hA
```
:::
::::

::::ejercicio
La unión es distributiva respecto de la intersección:
`A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`.

```savedLean
example (X : Type) (A B C : Set X) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry
```

:::demostracion
```savedLean
example (X : Type) (A B C : Set X) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · intro h
    rcases h with hA | hBC
    · constructor
      · left
        exact hA
      · left
        exact hA
    · obtain ⟨hB, hC⟩ := hBC
      constructor
      · right
        exact hB
      · right
        exact hC
  · intro h
    obtain ⟨hAB, hAC⟩ := h
    rcases hAB with hA | hB
    · left
      exact hA
    · rcases hAC with hA | hC
      · left
        exact hA
      · right
        constructor
        · exact hB
        · exact hC
```

En la vuelta hay que distinguir casos dos veces. Si `x ∈ A` hemos terminado enseguida; si no,
necesitamos saber también en qué lado de `A ∪ C` está `x`.
:::
::::

## Complementario

Si `A : Set X`, su complementario es `Aᶜ` (se escribe con `\^c`), el conjunto de los elementos de
`X` que no están en `A`:

```
x ∈ Aᶜ  ↔  x ∉ A
```

El símbolo `∉` (se escribe con `\notin`) es solo una abreviatura: `x ∉ A` es `¬(x ∈ A)`. Así que
el complementario es una negación, y recordemos que una negación es una implicación:
`x ∈ Aᶜ` es `x ∈ A → False`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ x ∈ Aᶜ`
  * {tac}`intro` `hx`
  * `hx : x ∈ A`

    `⊢ False`
*
  * `h : x ∈ Aᶜ`

    `hx : x ∈ A`
  * {tac}`apply` `h` {tac}`at` `hx`
  * `hx : False`
*
  * `⊢ x ∈ A`
  * {tac}`by_contra` `h`
  * `h : x ∉ A`

    `⊢ False`
:::

:::ejemplo
Si `A ⊆ B`, entonces `Bᶜ ⊆ Aᶜ`.

```savedLean
example (X : Type) (A B : Set X) (hAB : A ⊆ B) :
    Bᶜ ⊆ Aᶜ := by
  intro x hxB hxA
  apply hAB at hxA
  apply hxB at hxA
  exact hxA
```

Después del `intro` tenemos `hxB : x ∈ Bᶜ`, `hxA : x ∈ A` y la tesis es `False`: el tercer
nombre del `intro` ha servido para introducir la hipótesis de la negación `x ∈ Aᶜ`.
:::

::::ejercicio
Ley de De Morgan: `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`.

```savedLean
example (X : Type) (A B : Set X) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  sorry
```

:::demostracion
```savedLean
example (X : Type) (A B : Set X) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  · intro hx
    by_contra h
    apply hx
    constructor
    · by_contra hA
      apply h
      left
      exact hA
    · by_contra hB
      apply h
      right
      exact hB
  · intro hx hAB
    obtain ⟨hA, hB⟩ := hAB
    rcases hx with hnA | hnB
    · apply hnA at hA
      exact hA
    · apply hnB at hB
      exact hB
```

La ida es la parte difícil, y necesita reducción al absurdo. Sabemos que `x` no está en
`A ∩ B` y queremos ver que no está en `A` o no está en `B`, pero no sabemos en cuál de los dos.
Suponemos que no se cumple ninguna de las dos cosas (`h`) y llegamos a que `x ∈ A ∩ B`, lo que
contradice `hx`.
:::
::::

::::ejercicio
La otra ley de De Morgan: `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`.

```savedLean
example (X : Type) (A B : Set X) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  sorry
```

:::demostracion
```savedLean
example (X : Type) (A B : Set X) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro hx
    constructor
    · intro hA
      apply hx
      left
      exact hA
    · intro hB
      apply hx
      right
      exact hB
  · intro hx hAB
    obtain ⟨hnA, hnB⟩ := hx
    rcases hAB with hA | hB
    · apply hnA at hA
      exact hA
    · apply hnB at hB
      exact hB
```

Esta vez no hace falta reducción al absurdo.
:::
::::

## Resumen

:::table +header
*
  * Conjuntos
  * Lógica
  * Tácticas
*
  * `A ⊆ B`
  * `∀ x, x ∈ A → x ∈ B`
  * {tac}`intro`, {tac}`apply` ... {tac}`at` ..., `h hx`
*
  * `x ∈ A ∩ B`
  * `x ∈ A ∧ x ∈ B`
  * {tac}`constructor`, {tac}`obtain`, `h.left`, `h.right`
*
  * `x ∈ A ∪ B`
  * `x ∈ A ∨ x ∈ B`
  * {tac}`left`, {tac}`right`, {tac}`rcases`
*
  * `x ∈ Aᶜ`
  * `¬(x ∈ A)`
  * {tac}`intro`, {tac}`apply` ... {tac}`at` ..., {tac}`by_contra`
*
  * `A = B`
  * `∀ x, x ∈ A ↔ x ∈ B`
  * {tac}`ext`
:::

```savedLean -show
end Conjuntos
```

# Estructuras

Muchos objetos matemáticos están formados por varios datos y por unas propiedades que esos datos
cumplen. Una _estructura_ junta todo eso en un único tipo: es como un paquete de varias `def` y
varios `theorem` a la vez.

## Repaso: definiciones y teoremas

En la primera clase vimos que en Lean todo tiene un tipo, y que las proposiciones son tipos cuyos
términos son sus demostraciones. Vamos a recordar qué significa esto para `def` y `theorem`.

Una definición y un teorema se escriben exactamente igual:

```
def nombre : Tipo := término
theorem nombre : Proposición := demostración
```

En los dos casos estamos dando un nombre a un término de un tipo. Lo que cambia es el tipo:

```savedLean
def tres : ℕ := 3

theorem dos_mas_dos : 2 + 2 = 4 := by
  norm_num
```

* Como `tres : ℕ`, después de `:=` tenemos que poner un número natural.
* Como `dos_mas_dos : 2 + 2 = 4`, después de `:=` tenemos que poner una demostración de
  `2 + 2 = 4`. Eso es lo que construye `by norm_num`.

Una vez definidos, los dos se usan igual: escribiendo su nombre.

```savedLean (name := checkTres)
#check tres
```
```leanOutput checkTres
Clase4.tres : ℕ
```
```savedLean (name := checkDosMasDos)
#check dos_mas_dos
```
```leanOutput checkDosMasDos
Clase4.dos_mas_dos : 2 + 2 = 4
```

(Lean escribe `Clase4.` delante de los nombres porque todo el código de esta clase está dentro de
`namespace Clase4`.)

Esta idea es la clave de toda la clase: un tipo nos dice qué hay que poner después de `:=`. Si es
un tipo de datos, como `ℕ`, hay que dar un dato; si es una proposición, hay que dar una
demostración.

## Un primer ejemplo: puntos del plano

Empecemos por un ejemplo sencillo: un punto del primer cuadrante del plano, es decir, un punto
con las dos coordenadas positivas. Está formado por dos números reales, `x` e `y`, y por dos propiedades, `x > 0` e `y > 0`.

:::definicion "punto del primer cuadrante"
```savedLean
structure PuntoPrimerCuadrante where
  x : ℝ
  y : ℝ
  hx : x > 0
  hy : y > 0
```
:::

Cada una de las líneas es un _campo_ de la estructura, y cada campo tiene un nombre y un tipo,
igual que una `def` o un `theorem`. Los dos primeros son datos (números reales) y los dos últimos
son propiedades. `PuntoPrimerCuadrante` es un tipo nuevo, y un término de este tipo es un punto concreto
con sus dos demostraciones.

Para construir un término de una estructura usamos `where` y rellenamos cada campo con `:=`. Las
reglas son las de siempre:

* `x : ℝ`, así que después de `x :=` va un número real.
* `hx : x > 0`, así que después de `hx :=` va una demostración. Fíjate en que Lean ya sabe qué
  número hemos puesto en `x`, así que lo que hay que demostrar es `2 > 0`.

```savedLean
def miPunto : PuntoPrimerCuadrante where
  x := 2
  y := 3
  hx := by norm_num
  hy := by norm_num
```

Para acceder a los campos de un término de una estructura usamos un punto: `miPunto.x` es la
primera coordenada de `miPunto`, y `miPunto.hx` es la demostración de que es positiva.

```savedLean (name := checkX)
#check miPunto.x
```
```leanOutput checkX
miPunto.x : ℝ
```
```savedLean (name := checkHx)
#check miPunto.hx
```
```leanOutput checkHx
miPunto.hx : miPunto.x > 0
```

:::ejemplo
Las coordenadas de `miPunto` son las que hemos puesto, por definición.

```savedLean
example : miPunto.x = 2 := by
  rfl
```
:::

Lo interesante es que podemos razonar sobre un punto cualquiera, sin saber cuál es, usando las
propiedades que vienen dentro de él.

:::ejemplo
La suma de las coordenadas de un punto del primer cuadrante es positiva.

```savedLean
example (p : PuntoPrimerCuadrante) : p.x + p.y > 0 := by
  have h1 : p.x > 0 := p.hx
  have h2 : p.y > 0 := p.hy
  linarith
```

Aquí `p.hx` ya es una demostración de `p.x > 0`, así que la ponemos directamente después de `:=`,
sin `by`.
:::

::::ejercicio
Construye el punto `(3, 7)` como un `PuntoPrimerCuadrante`.

```savedLean -keep
def otroPunto : PuntoPrimerCuadrante where
  x := 3
  y := 7
  hx := sorry
  hy := sorry
```

:::demostracion
```savedLean
def otroPunto : PuntoPrimerCuadrante where
  x := 3
  y := 7
  hx := by norm_num
  hy := by norm_num
```
:::
::::

::::ejercicio
El producto de las coordenadas de un punto del primer cuadrante es positivo. Busca con `exact?` el resultado
que necesitas.

```savedLean
example (p : PuntoPrimerCuadrante) : p.x * p.y > 0 := by
  sorry
```

:::demostracion
```savedLean
example (p : PuntoPrimerCuadrante) : p.x * p.y > 0 := by
  have h1 : p.x > 0 := p.hx
  have h2 : p.y > 0 := p.hy
  exact mul_pos h1 h2 -- exact?
```
:::
::::

# Grupos

Nuestro primer ejemplo de verdad son los grupos. Recordemos su definición.

:::definicion "grupo"
Un _grupo_ es un conjunto `G` junto con una operación `⋆` que a cada par `a, b ∈ G` le asigna
`a ⋆ b ∈ G`, un elemento `e ∈ G` y una operación que a cada `a ∈ G` le asigna `a⁻¹ ∈ G`, de
forma que para todos `a, b, c ∈ G`:

1. La operación es asociativa: `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)`.
2. `e` es el elemento neutro: `e ⋆ a = a` y `a ⋆ e = a`.
3. `a⁻¹` es el inverso de `a`: `a⁻¹ ⋆ a = e` y `a ⋆ a⁻¹ = e`.
:::

Un grupo tiene, por tanto, tres datos (la operación, el neutro y el inverso) y varias propiedades.
Esta es nuestra versión en Lean:

:::definicion "grupo, en Lean"
```savedLean
structure Grupo (G : Type) where
  op : G → G → G
  e : G
  inv : G → G
  asoc : ∀ a b c : G, op (op a b) c = op a (op b c)
  neutro_izq : ∀ a : G, op e a = a
  neutro_der : ∀ a : G, op a e = a
  inv_izq : ∀ a : G, op (inv a) a = e
  inv_der : ∀ a : G, op a (inv a) = e
```
:::

Algunas cosas en las que fijarse:

* En lugar de un conjunto usamos un tipo `G`, como `ℤ` o `ℝ`.
* La operación es una función `op : G → G → G`, así que en lugar de `a ⋆ b` escribimos
  `op a b`. Del mismo modo, `a⁻¹` es `inv a`.
* Los tres primeros campos son datos y los cinco últimos son propiedades.
* `Grupo G` es un tipo, y un término `h : Grupo G` es una forma de hacer de `G` un grupo: elegir
  una operación, un neutro y un inverso, y demostrar que cumplen las propiedades. Un mismo tipo
  `G` puede ser un grupo de varias formas distintas.

:::observacion
En Mathlib los grupos no están definidos de una vez como aquí, sino por capas, de lo más sencillo
a lo más complicado. Primero hay una clase para los tipos con una multiplicación (`Mul`), que se
amplía con la propiedad asociativa (`Semigroup`), después con un elemento neutro (`Monoid`) y por
último con los inversos (`Group`). Cada capa _extiende_ a la anterior.

Así, un resultado que solo necesita la asociatividad se demuestra una única vez y sirve para todo
lo que tenga una operación asociativa, sea o no un grupo. Nosotros usaremos nuestra propia
definición, que es más fácil de leer.
:::

## Demostrar que algo es un grupo

Para demostrar que un tipo es un grupo hay que construir un término de `Grupo G`: dar los tres
datos y demostrar las cinco propiedades.

:::ejemplo
Los enteros con la suma son un grupo.

```savedLean
def enterosSuma : Grupo ℤ where
  op a b := a + b
  e := 0
  inv a := -a
  asoc := by
    intro a b c
    ring
  neutro_izq := by
    intro a
    ring
  neutro_der := by
    intro a
    ring
  inv_izq := by
    intro a
    ring
  inv_der := by
    intro a
    ring
```

La línea `op a b := a + b` dice que la operación es la que a `a` y `b` les asigna `a + b`.
Cada propiedad se demuestra como cualquier otro teorema; en este caso todas salen con `ring`.
:::

## Propiedades de los grupos: la notación punto

Si tenemos un grupo `h : Grupo G`, accedemos a sus datos con un punto, igual que hacíamos con
`miPunto.x`: la operación es `h.op`, el neutro es `h.e` y el inverso es `h.inv`. Lo mismo vale
para sus propiedades: `h.asoc a b c` es una demostración de
`h.op (h.op a b) c = h.op a (h.op b c)`, y `h.inv_izq a` es una demostración de
`h.op (h.inv a) a = h.e`.

Con esto podemos hacer dos cosas: construir grupos nuevos a partir de otros, y demostrar
resultados que valen para todos los grupos a la vez. En los dos casos basta con trabajar con un
`h : Grupo G` cualquiera.

::::ejercicio
Dado un grupo `h`, podemos construir otro grupo sobre el mismo tipo cambiando el orden de la
operación: `a ⋆' b = b ⋆ a`. Es el _grupo opuesto_. El neutro y los inversos son los mismos que
los de `h`.

Pista: cada propiedad del grupo opuesto es una propiedad de `h`, pero quizá no la que esperas.

```savedLean -keep
def opuesto {G : Type} (h : Grupo G) : Grupo G where
  op a b := h.op b a
  e := h.e
  inv := h.inv
  asoc := sorry
  neutro_izq := sorry
  neutro_der := sorry
  inv_izq := sorry
  inv_der := sorry
```

:::demostracion
```savedLean
def opuesto {G : Type} (h : Grupo G) : Grupo G where
  op a b := h.op b a
  e := h.e
  inv := h.inv
  asoc := by
    intro a b c
    rw [h.asoc]
  neutro_izq := by
    intro a
    exact h.neutro_der a
  neutro_der := by
    intro a
    exact h.neutro_izq a
  inv_izq := by
    intro a
    exact h.inv_der a
  inv_der := by
    intro a
    exact h.inv_izq a
```

Al dar la vuelta a la operación, la izquierda y la derecha se intercambian: el neutro por la
izquierda del grupo opuesto es el neutro por la derecha de `h`, y lo mismo pasa con los inversos.

En la asociativa, la tesis es `(c ⋆ b) ⋆ a = c ⋆ (b ⋆ a)` escrita al revés:
`c ⋆ (b ⋆ a) = (c ⋆ b) ⋆ a`. Por eso `rw [h.asoc]` cambia el lado derecho por el izquierdo y
cierra la tesis.
:::
::::

:::ejemplo
En un grupo se puede cancelar por la izquierda: si `a ⋆ b = a ⋆ c`, entonces `b = c`.

```savedLean
theorem cancel_izq {G : Type} (h : Grupo G) {a b c : G}
    (hab : h.op a b = h.op a c) : b = c := by
  have h1 : h.op (h.inv a) (h.op a b) =
      h.op (h.inv a) (h.op a c) := by
    rw [hab]
  rw [← h.asoc, ← h.asoc, h.inv_izq, h.neutro_izq,
    h.neutro_izq] at h1
  exact h1
```

Es la demostración de siempre: multiplicamos los dos lados por `a⁻¹` por la izquierda, y luego
operamos. Paso a paso, la hipótesis `h1` va cambiando así:

```
h1 : a⁻¹ ⋆ (a ⋆ b) = a⁻¹ ⋆ (a ⋆ c)
h1 : (a⁻¹ ⋆ a) ⋆ b = (a⁻¹ ⋆ a) ⋆ c    -- con ← h.asoc, dos veces
h1 : e ⋆ b = e ⋆ c                    -- con h.inv_izq
h1 : b = c                            -- con h.neutro_izq, dos veces
```

Hay que usar `← h.asoc` dos veces porque cada `rw` cambia un único patrón: primero
`a⁻¹ ⋆ (a ⋆ b)` y después `a⁻¹ ⋆ (a ⋆ c)`.
:::

Ahora `cancel_izq` es un resultado más, que podemos usar en cualquier grupo: si `h : Grupo G` y
`hab : h.op a b = h.op a c`, entonces `cancel_izq h hab : b = c`.

::::ejercicio
En un grupo también se puede cancelar por la derecha.

```savedLean -keep
theorem cancel_der {G : Type} (h : Grupo G) {a b c : G}
    (hab : h.op b a = h.op c a) : b = c := by
  sorry
```

:::demostracion
```savedLean
theorem cancel_der {G : Type} (h : Grupo G) {a b c : G}
    (hab : h.op b a = h.op c a) : b = c := by
  have h1 : h.op (h.op b a) (h.inv a) =
      h.op (h.op c a) (h.inv a) := by
    rw [hab]
  rw [h.asoc, h.asoc, h.inv_der, h.neutro_der,
    h.neutro_der] at h1
  exact h1
```
:::
::::

::::ejercicio
El inverso del inverso es el propio elemento: `(a⁻¹)⁻¹ = a`.

Pista: usa `cancel_izq`. ¿Por qué elemento hay que cancelar?

```savedLean -keep
theorem inverso_inverso {G : Type} (h : Grupo G) (a : G) :
    h.inv (h.inv a) = a := by
  sorry
```

:::demostracion
```savedLean
theorem inverso_inverso {G : Type} (h : Grupo G) (a : G) :
    h.inv (h.inv a) = a := by
  have h1 : h.op (h.inv a) (h.inv (h.inv a)) =
      h.op (h.inv a) a := by
    rw [h.inv_der, h.inv_izq]
  exact cancel_izq h h1
```

Los dos lados de `h1` son iguales a `e`: el izquierdo porque `inv (inv a)` es el inverso de
`inv a`, y el derecho porque `inv a` es el inverso de `a`. Cancelando `inv a` queda lo que
queríamos.
:::
::::

::::ejercicio
El inverso de un producto es el producto de los inversos, cambiados de orden:
`(a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹`.

```savedLean -keep
theorem inverso_op {G : Type} (h : Grupo G) (a b : G) :
    h.inv (h.op a b) = h.op (h.inv b) (h.inv a) := by
  sorry
```

:::demostracion
```savedLean
theorem inverso_op {G : Type} (h : Grupo G) (a b : G) :
    h.inv (h.op a b) = h.op (h.inv b) (h.inv a) := by
  have h1 : h.op (h.op a b) (h.inv (h.op a b)) =
      h.op (h.op a b) (h.op (h.inv b) (h.inv a)) := by
    rw [h.inv_der, h.asoc, ← h.asoc b, h.inv_der,
      h.neutro_izq, h.inv_der]
  exact cancel_izq h h1
```

La idea es la misma que en el ejercicio anterior: los dos lados de `h1` son `e`, y cancelamos
`a ⋆ b` por la izquierda.
:::
::::

## Ejercicios extra

::::ejercicio
Si en un grupo todo elemento cumple `a ⋆ a = e`, entonces el grupo es _conmutativo_ (o
_abeliano_): `a ⋆ b = b ⋆ a` para todos `a` y `b`.

Pista: primero demuestra con `have` que todo elemento es su propio inverso, y después usa
`inverso_op`.

```savedLean
example {G : Type} (h : Grupo G)
    (hcuad : ∀ a : G, h.op a a = h.e)
    (a b : G) : h.op a b = h.op b a := by
  sorry
```

:::demostracion
```savedLean
example {G : Type} (h : Grupo G)
    (hcuad : ∀ a : G, h.op a a = h.e)
    (a b : G) : h.op a b = h.op b a := by
  have hinv : ∀ x : G, h.inv x = x := by
    intro x
    have h1 : h.op x (h.inv x) = h.op x x := by
      rw [h.inv_der, hcuad]
    exact cancel_izq h h1
  rw [← hinv (h.op a b), inverso_op h, hinv a, hinv b]
```

El último `rw` hace la cuenta `a ⋆ b = (a ⋆ b)⁻¹ = b⁻¹ ⋆ a⁻¹ = b ⋆ a`.
:::
::::

::::ejercicio
Dados dos grupos, uno sobre `G` y otro sobre `H`, los pares `G × H` también forman un grupo
operando cada coordenada por separado: `(a, b) ⋆ (c, d) = (a ⋆ c, b ⋆ d)`. Es el _grupo
producto_.

En Lean, `G × H` es el tipo de los pares (el símbolo `×` se escribe con `\times`) y `(a, b)` es
un par. Si `p : G × H`, sus coordenadas son `p.1 : G` y `p.2 : H`.

Pista: para demostrar que dos pares son iguales también se usa `ext`. En este caso nos deja dos
tesis, una para cada coordenada.

```savedLean -keep
def producto {G H : Type} (g : Grupo G) (h : Grupo H) :
    Grupo (G × H) where
  op p q := (g.op p.1 q.1, h.op p.2 q.2)
  e := (g.e, h.e)
  inv p := (g.inv p.1, h.inv p.2)
  asoc := sorry
  neutro_izq := sorry
  neutro_der := sorry
  inv_izq := sorry
  inv_der := sorry
```

:::demostracion
```savedLean
def producto {G H : Type} (g : Grupo G) (h : Grupo H) :
    Grupo (G × H) where
  op p q := (g.op p.1 q.1, h.op p.2 q.2)
  e := (g.e, h.e)
  inv p := (g.inv p.1, h.inv p.2)
  asoc := by
    intro p q r
    ext
    · exact g.asoc p.1 q.1 r.1
    · exact h.asoc p.2 q.2 r.2
  neutro_izq := by
    intro p
    ext
    · exact g.neutro_izq p.1
    · exact h.neutro_izq p.2
  neutro_der := by
    intro p
    ext
    · exact g.neutro_der p.1
    · exact h.neutro_der p.2
  inv_izq := by
    intro p
    ext
    · exact g.inv_izq p.1
    · exact h.inv_izq p.2
  inv_der := by
    intro p
    ext
    · exact g.inv_der p.1
    · exact h.inv_der p.2
```

Cada propiedad del producto es la misma propiedad de `g` en la primera coordenada y de `h` en la
segunda, así que no hay que hacer ninguna cuenta: basta con usar los campos de los dos grupos.
:::
::::

Para terminar, un grupo formado por conjuntos. Si `A` y `B` son subconjuntos de `X`, su
_diferencia simétrica_ es el conjunto de los elementos que están en exactamente uno de los dos.

:::definicion "diferencia simétrica"
```savedLean
def difSimetrica {X : Type} (A B : Set X) : Set X :=
  (A ∪ B) ∩ (A ∩ B)ᶜ
```
:::

Es decir, `x ∈ difSimetrica A B` cuando `x` está en `A` o en `B`, pero no en los dos a la vez.

::::ejercicio
Según si `x` está o no en `A` y en `B`, hay cuatro casos. Demuestra en cada uno si `x` está en
`difSimetrica A B`.

```savedLean -keep
theorem dif_izq {X : Type} {A B : Set X} {x : X}
    (hA : x ∈ A) (hB : x ∉ B) : x ∈ difSimetrica A B := by
  sorry

theorem dif_der {X : Type} {A B : Set X} {x : X}
    (hA : x ∉ A) (hB : x ∈ B) : x ∈ difSimetrica A B := by
  sorry

theorem dif_ambos {X : Type} {A B : Set X} {x : X}
    (hA : x ∈ A) (hB : x ∈ B) : x ∉ difSimetrica A B := by
  sorry

theorem dif_ninguno {X : Type} {A B : Set X} {x : X}
    (hA : x ∉ A) (hB : x ∉ B) : x ∉ difSimetrica A B := by
  sorry
```

:::demostracion
```savedLean
theorem dif_izq {X : Type} {A B : Set X} {x : X}
    (hA : x ∈ A) (hB : x ∉ B) : x ∈ difSimetrica A B := by
  constructor
  · left
    exact hA
  · intro h
    obtain ⟨hA', hB'⟩ := h
    apply hB at hB'
    exact hB'

theorem dif_der {X : Type} {A B : Set X} {x : X}
    (hA : x ∉ A) (hB : x ∈ B) : x ∈ difSimetrica A B := by
  constructor
  · right
    exact hB
  · intro h
    obtain ⟨hA', hB'⟩ := h
    apply hA at hA'
    exact hA'

theorem dif_ambos {X : Type} {A B : Set X} {x : X}
    (hA : x ∈ A) (hB : x ∈ B) : x ∉ difSimetrica A B := by
  intro h
  obtain ⟨h1, h2⟩ := h
  apply h2
  constructor
  · exact hA
  · exact hB

theorem dif_ninguno {X : Type} {A B : Set X} {x : X}
    (hA : x ∉ A) (hB : x ∉ B) : x ∉ difSimetrica A B := by
  intro h
  obtain ⟨h1, h2⟩ := h
  rcases h1 with h | h
  · apply hA at h
    exact h
  · apply hB at h
    exact h
```
:::
::::

::::ejercicio
Los subconjuntos de `X` forman un grupo con la diferencia simétrica. El neutro es `∅` y cada
conjunto es su propio inverso.

Pista: la asociatividad es la parte larga. Después de `ext x`, distingue con `by_cases` si `x`
está en `A`, en `B` y en `C`. Son ocho casos, y en cada uno los cuatro resultados del ejercicio
anterior te dicen si `x` está en cada lado de la igualdad. Ten paciencia.

```savedLean -keep
def difSim (X : Type) : Grupo (Set X) where
  op := difSimetrica
  e := ∅
  inv A := A
  asoc := sorry
  neutro_izq := sorry
  neutro_der := sorry
  inv_izq := sorry
  inv_der := sorry
```

:::demostracion
```savedLean
def difSim (X : Type) : Grupo (Set X) where
  op := difSimetrica
  e := ∅
  inv A := A
  asoc := by
    intro A B C
    ext x
    by_cases hA : x ∈ A
    · by_cases hB : x ∈ B
      · by_cases hC : x ∈ C
        · constructor
          · intro h
            exact dif_izq hA (dif_ambos hB hC)
          · intro h
            exact dif_der (dif_ambos hA hB) hC
        · constructor
          · intro h
            apply dif_ninguno (dif_ambos hA hB) hC at h
            by_contra hc
            exact h
          · intro h
            apply dif_ambos hA (dif_izq hB hC) at h
            by_contra hc
            exact h
      · by_cases hC : x ∈ C
        · constructor
          · intro h
            apply dif_ambos (dif_izq hA hB) hC at h
            by_contra hc
            exact h
          · intro h
            apply dif_ambos hA (dif_der hB hC) at h
            by_contra hc
            exact h
        · constructor
          · intro h
            exact dif_izq hA (dif_ninguno hB hC)
          · intro h
            exact dif_izq (dif_izq hA hB) hC
    · by_cases hB : x ∈ B
      · by_cases hC : x ∈ C
        · constructor
          · intro h
            apply dif_ambos (dif_der hA hB) hC at h
            by_contra hc
            exact h
          · intro h
            apply dif_ninguno hA (dif_ambos hB hC) at h
            by_contra hc
            exact h
        · constructor
          · intro h
            exact dif_der hA (dif_izq hB hC)
          · intro h
            exact dif_izq (dif_der hA hB) hC
      · by_cases hC : x ∈ C
        · constructor
          · intro h
            exact dif_der hA (dif_der hB hC)
          · intro h
            exact dif_der (dif_ninguno hA hB) hC
        · constructor
          · intro h
            apply dif_ninguno (dif_ninguno hA hB) hC at h
            by_contra hc
            exact h
          · intro h
            apply dif_ninguno hA (dif_ninguno hB hC) at h
            by_contra hc
            exact h
  neutro_izq := by
    intro A
    ext x
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      rcases h1 with h | h
      · by_contra hc
        exact h
      · exact h
    · intro hx
      constructor
      · right
        exact hx
      · intro h
        obtain ⟨h1, h2⟩ := h
        exact h1
  neutro_der := by
    intro A
    ext x
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      rcases h1 with h | h
      · exact h
      · by_contra hc
        exact h
    · intro hx
      constructor
      · left
        exact hx
      · intro h
        obtain ⟨h1, h2⟩ := h
        exact h2
  inv_izq := by
    intro A
    ext x
    constructor
    · intro h
      by_cases hA : x ∈ A
      · apply dif_ambos hA hA at h
        by_contra hc
        exact h
      · apply dif_ninguno hA hA at h
        by_contra hc
        exact h
    · intro h
      by_contra hc
      exact h
  inv_der := by
    intro A
    ext x
    constructor
    · intro h
      by_cases hA : x ∈ A
      · apply dif_ambos hA hA at h
        by_contra hc
        exact h
      · apply dif_ninguno hA hA at h
        by_contra hc
        exact h
    · intro h
      by_contra hc
      exact h
```

En cada caso de la asociatividad, los cuatro resultados nos dicen si `x` está en cada lado. Si
está en los dos, demostramos cada implicación con `exact`. Si no está en ninguno, la hipótesis
`h` del `intro` contradice lo que dicen los resultados, y terminamos como cuando teníamos
`hx : x ∈ ∅`.
:::
::::

Como cada conjunto es su propio inverso, el primer ejercicio extra nos dice además que la
diferencia simétrica es conmutativa, sin necesidad de demostrarlo a mano.

# Subgrupos

:::definicion "subgrupo"
Un _subgrupo_ de un grupo `G` es un subconjunto `H ⊆ G` que contiene al neutro y que es cerrado
para la operación y para el inverso: si `a, b ∈ H`, entonces `a ⋆ b ∈ H` y `a⁻¹ ∈ H`.
:::

En Lean, un subgrupo también es una estructura: un conjunto junto con tres propiedades.

:::definicion "subgrupo, en Lean"
```savedLean
structure Subgrupo {G : Type} (h : Grupo G) where
  conj : Set G
  neutro_mem : h.e ∈ conj
  op_mem : ∀ a b : G, a ∈ conj → b ∈ conj → h.op a b ∈ conj
  inv_mem : ∀ a : G, a ∈ conj → h.inv a ∈ conj
```
:::

Fíjate en que `Subgrupo` no depende solo del tipo `G`, sino del grupo `h`: un mismo conjunto
puede ser un subgrupo para una operación y no serlo para otra.

:::ejemplo
Los enteros pares son un subgrupo de `(ℤ, +)`.

```savedLean
def pares : Subgrupo enterosSuma where
  conj := {n : ℤ | ∃ k, n = 2 * k}
  neutro_mem := by
    rw [Set.mem_setOf_eq]
    unfold enterosSuma
    use 0
    ring
  op_mem := by
    intro a b ha hb
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hl⟩ := hb
    rw [Set.mem_setOf_eq]
    unfold enterosSuma
    use k + l
    rw [hk, hl]
    ring
  inv_mem := by
    intro a ha
    obtain ⟨k, hk⟩ := ha
    rw [Set.mem_setOf_eq]
    unfold enterosSuma
    use -k
    rw [hk]
    ring
```

Después de `rw [Set.mem_setOf_eq]` la tesis habla de `enterosSuma.e` o de `enterosSuma.op a b`, y
`ring` no sabe qué son. Con `unfold enterosSuma` Lean sustituye `enterosSuma` por su definición,
así que ya ve que el neutro es `0` y la operación es la suma, y a partir de ahí `ring` hace el
resto.
:::

::::ejercicio
Los múltiplos de un entero `m` forman un subgrupo de `(ℤ, +)`.

```savedLean -keep
def multiplos (m : ℤ) : Subgrupo enterosSuma where
  conj := {n : ℤ | ∃ k, n = m * k}
  neutro_mem := sorry
  op_mem := sorry
  inv_mem := sorry
```

:::demostracion
```savedLean
def multiplos (m : ℤ) : Subgrupo enterosSuma where
  conj := {n : ℤ | ∃ k, n = m * k}
  neutro_mem := by
    rw [Set.mem_setOf_eq]
    unfold enterosSuma
    use 0
    ring
  op_mem := by
    intro a b ha hb
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hl⟩ := hb
    rw [Set.mem_setOf_eq]
    unfold enterosSuma
    use k + l
    rw [hk, hl]
    ring
  inv_mem := by
    intro a ha
    obtain ⟨k, hk⟩ := ha
    rw [Set.mem_setOf_eq]
    unfold enterosSuma
    use -k
    rw [hk]
    ring
```
:::
::::

::::ejercicio
En cualquier grupo, el conjunto formado solo por el neutro es un subgrupo.

```savedLean -keep
def subgrupoTrivial {G : Type} (h : Grupo G) :
    Subgrupo h where
  conj := {x : G | x = h.e}
  neutro_mem := sorry
  op_mem := sorry
  inv_mem := sorry
```

:::demostracion
```savedLean
def subgrupoTrivial {G : Type} (h : Grupo G) :
    Subgrupo h where
  conj := {x : G | x = h.e}
  neutro_mem := by
    rw [Set.mem_setOf_eq]
  op_mem := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq] at hb
    rw [Set.mem_setOf_eq, ha, hb, h.neutro_izq]
  inv_mem := by
    intro a ha
    rw [Set.mem_setOf_eq] at ha
    rw [Set.mem_setOf_eq, ha]
    rw [← h.neutro_izq (h.inv h.e), h.inv_der]
```

En `neutro_mem` la tesis queda `h.e = h.e` después del `rw`, y `rw` la cierra solo, igual que
haría `rfl`.
:::
::::

## Subtipos

Un subgrupo `H` de un grupo `G` es también un grupo, con la misma operación que `G`. Para
escribir esto en Lean nos encontramos con un problema: `Grupo` necesita un tipo, y `H.conj` es un
conjunto, un término de `Set G`. Necesitamos poder ver un conjunto como un tipo, y para eso Lean
tiene los _subtipos_.

Un subtipo es, de nuevo, una estructura. Simplificando un poco, en Lean está definido así:

```
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val
```

Es decir, si `p` es una propiedad de los elementos de un tipo `α`, un término de `Subtype p` está
formado por dos campos:

* un dato, `val : α`, que es un elemento de `α`,
* y una propiedad, `property : p val`, que es una demostración de que ese elemento cumple `p`.

Igual que pasaba con los puntos del primer cuadrante, que eran dos números reales junto con dos demostraciones de que son positivos, un elemento de `Subtype p` es un elemento de `α` junto con una demostración de que cumple `p`.

El tipo `Subtype p` también se escribe `{x // p x}`. Por ejemplo, `{n : ℕ // n > 0}` es el tipo de
los naturales positivos. Para construir un término, en lugar de usar `where` podemos escribir los
dos campos entre `⟨` y `⟩`, igual que hacíamos con las conjunciones y los existenciales.

:::ejemplo
El `5` como natural positivo.

```savedLean
def cinco : {n : ℕ // n > 0} := ⟨5, by norm_num⟩

example : cinco.val = 5 := by
  rfl
```

El primer campo es el número `5` y el segundo es una demostración de que `5 > 0`. Como en
cualquier estructura, accedemos a los campos con un punto: `cinco.val` es `5`, y `cinco.property`
es la demostración de que es positivo.
:::

Si `S : Set X`, Lean nos deja usar `S` en cualquier sitio donde haga falta un tipo, y entonces lo
entiende como el subtipo `{x // x ∈ S}`. Así, un elemento `a : S` es un par formado por un
elemento `a.val : X` y una demostración `a.property : a.val ∈ S`.

:::observacion
Cuando Lean usa un conjunto como tipo, o un elemento de un subtipo como elemento del tipo grande,
en el InfoView aparece una flecha. Por ejemplo, si `S : Set ℕ` y `a : S`, el InfoView escribe
`a : ↑S`, y escribe `↑a` en lugar de `a.val`.
:::

Dos elementos de un subtipo son iguales cuando sus valores son iguales: la demostración que llevan
dentro no importa. La táctica `ext` hace este cambio.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `a b : S`

    `⊢ a = b`
  * {tac}`ext`
  * `⊢ ↑a = ↑b`
:::

La tesis después de `ext` es `a.val = b.val`, escrita con la notación de la flecha.

Ahora podemos demostrar que todo subgrupo es un grupo con la operación heredada.

:::ejemplo
Si `H` es un subgrupo de `h : Grupo G`, entonces `H.conj` es un grupo.

```savedLean
def grupoDeSubgrupo {G : Type} {h : Grupo G}
    (H : Subgrupo h) :
    Grupo H.conj where
  op a b := ⟨h.op a.val b.val,
    H.op_mem a.val b.val a.property b.property⟩
  e := ⟨h.e, H.neutro_mem⟩
  inv a := ⟨h.inv a.val, H.inv_mem a.val a.property⟩
  asoc := by
    intro a b c
    ext
    exact h.asoc a.val b.val c.val
  neutro_izq := by
    intro a
    ext
    exact h.neutro_izq a.val
  neutro_der := by
    intro a
    ext
    exact h.neutro_der a.val
  inv_izq := by
    intro a
    ext
    exact h.inv_izq a.val
  inv_der := by
    intro a
    ext
    exact h.inv_der a.val
```
:::

## Caracterización de los subgrupos

Una caracterización de los subgrupos que se usa mucho en la práctica: un conjunto que contiene al
neutro es un subgrupo si y solo si, para todos `a, b` del conjunto, `a ⋆ b⁻¹` también está en el
conjunto. Lo demostramos en dos ejercicios, uno para cada implicación.

::::ejercicio
Si `H` es un subgrupo y `a, b ∈ H`, entonces `a ⋆ b⁻¹ ∈ H`.

```savedLean
example {G : Type} {h : Grupo G} (H : Subgrupo h) (a b : G)
    (ha : a ∈ H.conj) (hb : b ∈ H.conj) :
    h.op a (h.inv b) ∈ H.conj := by
  sorry
```

:::demostracion
```savedLean
example {G : Type} {h : Grupo G} (H : Subgrupo h) (a b : G)
    (ha : a ∈ H.conj) (hb : b ∈ H.conj) :
    h.op a (h.inv b) ∈ H.conj := by
  apply H.op_mem
  · exact ha
  · exact H.inv_mem b hb
```
:::
::::

::::ejercicio
Recíprocamente, si `S` contiene al neutro y `a ⋆ b⁻¹ ∈ S` para todos `a, b ∈ S`, entonces `S`
es un subgrupo.

Pista: para `inv_mem`, aplica la hipótesis a `e` y `a`. Para `op_mem`, aplícala a `a` y `b⁻¹`
(y usa `inverso_inverso`).

```savedLean -keep
def subgrupoCriterio {G : Type} (h : Grupo G) (S : Set G)
    (he : h.e ∈ S)
    (hS : ∀ a b : G, a ∈ S → b ∈ S → h.op a (h.inv b) ∈ S) :
    Subgrupo h where
  conj := S
  neutro_mem := sorry
  op_mem := sorry
  inv_mem := sorry
```

:::demostracion
```savedLean
def subgrupoCriterio {G : Type} (h : Grupo G) (S : Set G)
    (he : h.e ∈ S)
    (hS : ∀ a b : G, a ∈ S → b ∈ S → h.op a (h.inv b) ∈ S) :
    Subgrupo h where
  conj := S
  neutro_mem := he
  op_mem := by
    intro a b ha hb
    have hb' : h.inv b ∈ S := by
      have h1 := hS h.e b he hb
      rw [h.neutro_izq] at h1
      exact h1
    have h2 := hS a (h.inv b) ha hb'
    rw [inverso_inverso h] at h2
    exact h2
  inv_mem := by
    intro a ha
    have h1 := hS h.e a he ha
    rw [h.neutro_izq] at h1
    exact h1
```

Fíjate en que en `op_mem` hemos tenido que repetir el argumento de `inv_mem`: dentro de la
construcción, un campo no puede usar lo que hemos demostrado en otro.
:::
::::

# Espacios topológicos

```savedLean -show
section EspaciosTopologicos
```

Nuestro siguiente ejemplo de estructura son los espacios topológicos.

:::definicion "topología"
Una _topología_ en un conjunto `X` es una familia de subconjuntos de `X`, a los que llamamos
_abiertos_, que cumple:

1. El vacío `∅` y el total `X` son abiertos.
2. La unión de cualquier familia de abiertos es un abierto.
3. La intersección de dos abiertos es un abierto.
:::

Para escribir esto en Lean nos faltan algunas cosas sobre conjuntos: el conjunto vacío, el
conjunto total y las uniones de familias de conjuntos.

## Más sobre conjuntos: el vacío, el total y las familias

### El conjunto vacío

El conjunto vacío es `∅ : Set X` (se escribe con `\empty`). Ningún elemento pertenece a él, así
que pertenecer al vacío es, por definición, la proposición falsa:

```
x ∈ ∅  ↔  False
```

Esto quiere decir que una hipótesis `hx : x ∈ ∅` es en realidad una demostración de `False`. Y de
algo falso se puede deducir cualquier cosa: si queremos demostrar una tesis cualquiera, usamos
`by_contra` para que la tesis pase a ser `False`, y la cerramos con `exact hx`.

:::ejemplo
El vacío es subconjunto de cualquier conjunto.

```savedLean
example (X : Type) (A : Set X) : ∅ ⊆ A := by
  intro x hx
  by_contra h
  exact hx
```

Aquí no usamos para nada la hipótesis `h` que nos da `by_contra`: solo queríamos que la tesis
fuera `False`.
:::

### El conjunto total

El conjunto que contiene a todos los elementos de `X` es `Set.univ : Set X`. Todo elemento
pertenece a él, así que pertenecer a `Set.univ` es, por definición, la proposición verdadera:

```
x ∈ Set.univ  ↔  True
```

`True` es una proposición que siempre se puede demostrar, y la táctica que lo hace es `trivial`.

:::ejemplo
Cualquier conjunto está contenido en el total.

```savedLean
example (X : Type) (A : Set X) : A ⊆ Set.univ := by
  intro x hx
  trivial
```
:::

### Familias de conjuntos

En la definición de topología aparecen familias de subconjuntos de `X`. Una familia de
subconjuntos es simplemente un conjunto cuyos elementos son subconjuntos de `X`, es decir, un
término `F : Set (Set X)`. Así, `U ∈ F` quiere decir que el conjunto `U` es uno de los de la
familia.

Para decir que todos los conjuntos de `F` cumplen una propiedad escribimos `∀ U ∈ F, P U`, que es
una abreviatura de `∀ U, U ∈ F → P U`.

La unión de todos los conjuntos de la familia `F` se escribe `⋃₀ F`. Un elemento está en la
unión cuando está en alguno de los conjuntos de la familia:

```
x ∈ ⋃₀ F  ↔  ∃ U ∈ F, x ∈ U
```

Esta vez no es cierto por definición, sino que es un resultado de Mathlib, `Set.mem_sUnion`, y lo
usamos con `rw`.

:::ejemplo
Cada conjunto de una familia está contenido en la unión de la familia.

```savedLean
example (X : Type) (F : Set (Set X)) (A : Set X)
    (hA : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x hx
  rw [Set.mem_sUnion]
  use A
```

Después de `use A` la tesis es `A ∈ F ∧ x ∈ A`, y las dos partes están entre las hipótesis, así
que `use` la cierra solo.
:::

::::ejercicio
Si todos los conjuntos de una familia `F` están contenidos en `A`, entonces su unión también.

```savedLean
example (X : Type) (F : Set (Set X)) (A : Set X)
    (hF : ∀ U ∈ F, U ⊆ A) : ⋃₀ F ⊆ A := by
  sorry
```

:::demostracion
```savedLean
example (X : Type) (F : Set (Set X)) (A : Set X)
    (hF : ∀ U ∈ F, U ⊆ A) : ⋃₀ F ⊆ A := by
  intro x hx
  rw [Set.mem_sUnion] at hx
  obtain ⟨U, hU, hxU⟩ := hx
  specialize hF U hU
  exact hF hxU
```
:::
::::

### Resumen

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `hx : x ∈ ∅`

    `⊢ P`
  * {tac}`by_contra` `h`

    {tac}`exact` `hx`
  * No goals
*
  * `⊢ x ∈ Set.univ`
  * {tac}`trivial`
  * No goals
*
  * `hx : x ∈ ⋃₀ F`
  * {tac}`rw` `[Set.mem_sUnion]` {tac}`at` `hx`
  * `hx : ∃ U ∈ F, x ∈ U`
:::

## La definición en Lean

::::ejercicio
Escribe en Lean la definición de topología. Llámala `MiTopologia` para que no se confunda con la
que daremos después. Te damos el primer campo: `abierto U` es la proposición "`U` es abierto".

```savedLean
structure MiTopologia (X : Type) where
  abierto : Set X → Prop
```
::::

Esta es la definición que usaremos a partir de ahora. Compárala con la tuya.

:::definicion "topología, en Lean"
```savedLean
structure Topologia (X : Type) where
  abierto : Set X → Prop
  vacio : abierto ∅
  total : abierto Set.univ
  union : ∀ F : Set (Set X),
    (∀ U ∈ F, abierto U) → abierto (⋃₀ F)
  inter : ∀ U V : Set X,
    abierto U → abierto V → abierto (U ∩ V)
```
:::

## Ejemplos

Para construir una topología concreta tenemos que decir qué conjuntos son abiertos, y después
demostrar las cuatro propiedades. Como en los grupos, en `abierto U := ...` escribimos la
condición que tiene que cumplir `U` para ser abierto.

::::ejercicio
La _topología discreta_: todos los conjuntos son abiertos.

```savedLean -keep
def topDiscreta (X : Type) : Topologia X where
  abierto U := True
  vacio := sorry
  total := sorry
  union := sorry
  inter := sorry
```

:::demostracion
```savedLean
def topDiscreta (X : Type) : Topologia X where
  abierto U := True
  vacio := by
    trivial
  total := by
    trivial
  union := by
    intro F hF
    trivial
  inter := by
    intro U V hU hV
    trivial
```

Como ser abierto es `True`, no hay nada que comprobar.
:::
::::

Para el siguiente ejemplo nos hace falta una táctica nueva.

::::nuevaTactica (tactica := "by_cases")
La táctica `by_cases h : P` distingue dos casos: uno en el que `P` es cierta y otro en el que es
falsa. En el primero tenemos la hipótesis `h : P` y en el segundo `h : ¬P`; la tesis es la misma
en los dos. Igual que con `rcases`, cada caso se demuestra en su propio bloque con `·`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ Q`
  * {tac}`by_cases` `h : P`
  * caso 1: `h : P`, con `⊢ Q`

    caso 2: `h : ¬P`, con `⊢ Q`
:::
::::

Es lo mismo que haríamos con `rcases` si tuviéramos la hipótesis `P ∨ ¬P` del tercero excluido.

::::ejercicio
La _topología trivial_: los únicos abiertos son `∅` y `X`.

Pista: para la unión, distingue con `by_cases` si `Set.univ` está en `F` o no. Para la
intersección pueden ayudarte `exact?` o los resultados `Set.empty_inter`, `Set.inter_empty` y
`Set.inter_self`.

```savedLean -keep
def topTrivial (X : Type) : Topologia X where
  abierto U := U = ∅ ∨ U = Set.univ
  vacio := sorry
  total := sorry
  union := sorry
  inter := sorry
```

:::demostracion
```savedLean
def topTrivial (X : Type) : Topologia X where
  abierto U := U = ∅ ∨ U = Set.univ
  vacio := by
    left
    rfl
  total := by
    right
    rfl
  union := by
    intro F hF
    by_cases h : Set.univ ∈ F
    · right
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        rw [Set.mem_sUnion]
        use Set.univ
    · left
      ext x
      constructor
      · intro hx
        rw [Set.mem_sUnion] at hx
        obtain ⟨U, hU, hxU⟩ := hx
        specialize hF U hU
        rcases hF with hU' | hU'
        · rw [hU'] at hxU
          exact hxU
        · rw [hU'] at hU
          apply h at hU
          by_contra hc
          exact hU
      · intro hx
        by_contra hc
        exact hx
  inter := by
    intro U V hU hV
    rcases hU with hU | hU
    · left
      rw [hU]
      exact Set.empty_inter V -- exact?
    · rcases hV with hV | hV
      · left
        rw [hV]
        exact Set.inter_empty U -- exact?
      · right
        rw [hU, hV]
        exact Set.inter_self Set.univ -- exact?
```

En la unión, si `Set.univ ∈ F` la unión es todo `X`. Si no, todos los conjuntos de `F` son
vacíos (porque son abiertos y no son `Set.univ`), así que la unión es vacía.
:::
::::

## Ejercicios extra

::::ejercicio
La _topología del punto incluido_: fijado un punto `p : X`, un conjunto es abierto si es vacío o
contiene a `p`.

```savedLean -keep
def topPuntoIncluido (X : Type) (p : X) : Topologia X where
  abierto U := U = ∅ ∨ p ∈ U
  vacio := sorry
  total := sorry
  union := sorry
  inter := sorry
```

:::demostracion
```savedLean
def topPuntoIncluido (X : Type) (p : X) : Topologia X where
  abierto U := U = ∅ ∨ p ∈ U
  vacio := by
    left
    rfl
  total := by
    right
    trivial
  union := by
    intro F hF
    by_cases h : ∃ U ∈ F, p ∈ U
    · right
      rw [Set.mem_sUnion]
      exact h
    · left
      ext x
      constructor
      · intro hx
        rw [Set.mem_sUnion] at hx
        obtain ⟨U, hU, hxU⟩ := hx
        specialize hF U hU
        rcases hF with hU' | hpU
        · rw [hU'] at hxU
          exact hxU
        · have h2 : ∃ U ∈ F, p ∈ U := ⟨U, hU, hpU⟩
          apply h at h2
          by_contra hc
          exact h2
      · intro hx
        by_contra hc
        exact hx
  inter := by
    intro U V hU hV
    rcases hU with hU | hpU
    · left
      rw [hU]
      exact Set.empty_inter V
    · rcases hV with hV | hpV
      · left
        rw [hV]
        exact Set.inter_empty U
      · right
        constructor
        · exact hpU
        · exact hpV
```
:::
::::

::::ejercicio
La _topología usual_ de `ℝ`: un conjunto `U` es abierto si para cada `x ∈ U` hay un intervalo
abierto `(a, b)` que contiene a `x` y está contenido en `U`.

Pista: para la intersección, si `(a, b)` y `(c, d)` son los intervalos de cada abierto, usa el
intervalo `(max a c, min b d)`. Los resultados `max_lt`, `lt_min`, `le_max_left`,
`le_max_right`, `min_le_left` y `min_le_right` te serán útiles.

```savedLean -keep
def topUsual : Topologia ℝ where
  abierto U := ∀ x ∈ U, ∃ a b : ℝ,
    a < x ∧ x < b ∧ {y : ℝ | a < y ∧ y < b} ⊆ U
  vacio := sorry
  total := sorry
  union := sorry
  inter := sorry
```

:::demostracion
```savedLean
def topUsual : Topologia ℝ where
  abierto U := ∀ x ∈ U, ∃ a b : ℝ,
    a < x ∧ x < b ∧ {y : ℝ | a < y ∧ y < b} ⊆ U
  vacio := by
    intro x hx
    by_contra hc
    exact hx
  total := by
    intro x hx
    use x - 1
    use x + 1
    constructor
    · linarith
    · constructor
      · linarith
      · intro y hy
        trivial
  union := by
    intro F hF x hx
    rw [Set.mem_sUnion] at hx
    obtain ⟨U, hU, hxU⟩ := hx
    obtain ⟨a, b, hax, hxb, hab⟩ := hF U hU x hxU
    use a
    use b
    constructor
    · exact hax
    · constructor
      · exact hxb
      · intro y hy
        rw [Set.mem_sUnion]
        exact ⟨U, hU, hab hy⟩
  inter := by
    intro U V hU hV x hx
    obtain ⟨hxU, hxV⟩ := hx
    obtain ⟨a, b, hax, hxb, hab⟩ := hU x hxU
    obtain ⟨c, d, hcx, hxd, hcd⟩ := hV x hxV
    use max a c
    use min b d
    constructor
    · exact max_lt hax hcx
    · constructor
      · exact lt_min hxb hxd
      · intro y hy
        obtain ⟨hy1, hy2⟩ := hy
        have h1 : a ≤ max a c := le_max_left a c
        have h2 : c ≤ max a c := le_max_right a c
        have h3 : min b d ≤ b := min_le_left b d
        have h4 : min b d ≤ d := min_le_right b d
        constructor
        · apply hab
          constructor
          · linarith
          · linarith
        · apply hcd
          constructor
          · linarith
          · linarith
```
:::
::::

::::ejercicio
La _topología de subespacio_. Si `T` es una topología en `X` y `S ⊆ X`, los abiertos de `S` son
las intersecciones de `S` con los abiertos de `X`: un `V ⊆ S` es abierto si existe un abierto
`U` de `X` tal que `V` está formado por los puntos de `S` que están en `U`.

Como vimos en la sección de subgrupos, `S : Set X` también se puede usar como un tipo: un
elemento `x : S` es un elemento `x.val : X` junto con una demostración de que `x.val ∈ S`. Así,
los subconjuntos de `S` son términos de `Set S`.

Pista: en la unión, dada una familia `F` de abiertos de `S`, usa la unión de todos los abiertos
`U` de `X` que corresponden a algún conjunto de `F`.

```savedLean -keep
def topSubespacio {X : Type} (T : Topologia X) (S : Set X) :
    Topologia S where
  abierto V := ∃ U, T.abierto U ∧ V = {x : S | x.val ∈ U}
  vacio := sorry
  total := sorry
  union := sorry
  inter := sorry
```

:::demostracion
```savedLean
def topSubespacio {X : Type} (T : Topologia X) (S : Set X) :
    Topologia S where
  abierto V := ∃ U, T.abierto U ∧ V = {x : S | x.val ∈ U}
  vacio := by
    use ∅
    constructor
    · exact T.vacio
    · ext x
      constructor
      · intro hx
        by_contra hc
        exact hx
      · intro hx
        by_contra hc
        exact hx
  total := by
    use Set.univ
    constructor
    · exact T.total
    · ext x
      constructor
      · intro hx
        trivial
      · intro hx
        trivial
  union := by
    intro F hF
    use ⋃₀ {U : Set X |
      T.abierto U ∧ {x : S | x.val ∈ U} ∈ F}
    constructor
    · apply T.union
      intro U hU
      obtain ⟨hU1, hU2⟩ := hU
      exact hU1
    · ext x
      constructor
      · intro hx
        rw [Set.mem_sUnion] at hx
        obtain ⟨V, hV, hxV⟩ := hx
        obtain ⟨U, hU, hVU⟩ := hF V hV
        rw [Set.mem_setOf_eq, Set.mem_sUnion]
        use U
        constructor
        · constructor
          · exact hU
          · rw [← hVU]
            exact hV
        · rw [hVU] at hxV
          exact hxV
      · intro hx
        rw [Set.mem_setOf_eq, Set.mem_sUnion] at hx
        obtain ⟨U, hU, hxU⟩ := hx
        obtain ⟨hU1, hU2⟩ := hU
        rw [Set.mem_sUnion]
        exact ⟨{x : S | x.val ∈ U}, hU2, hxU⟩
  inter := by
    intro V W hV hW
    obtain ⟨U1, hU1, hV1⟩ := hV
    obtain ⟨U2, hU2, hW2⟩ := hW
    use U1 ∩ U2
    constructor
    · exact T.inter U1 U2 hU1 hU2
    · rw [hV1, hW2]
      ext x
      constructor
      · intro hx
        exact hx
      · intro hx
        exact hx
```
:::
::::

```savedLean -show
end EspaciosTopologicos
```

```savedLean -show
end Clase4
```

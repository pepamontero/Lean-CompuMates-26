import VersoManual
import Apuntes.Meta.Lean
import Apuntes.Meta.NuevaTactica
import Apuntes.Meta.Estilo
import Apuntes.Meta.Teorema
import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

open Verso.Genre Manual

open Verso.Genre.Manual.InlineLean

open Apuntes

set_option pp.rawOnError true

#doc (Manual) "Números reales, sucesiones y continuidad" =>

%%%
%%%

```savedImport
import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
```
```savedComment
# Clase 3: números reales, sucesiones y continuidad

Tácticas nuevas: `norm_num`, `linarith`, `ring`, `rw`, `have` y `exact?`.
```
```savedLean -show
namespace Clase3
```

El objetivo de esta clase es aprender a manipular objetos como las sucesiones y las funciones continuas definidas sobre el cuerpo de los números reales ℝ.

De ahora en adelante daremos por válido el uso de propiedades de los números reales ya demostradas en Mathlib, nuestro objetivo es alcanzar a ser autónomos en el uso de Lean y eso incluye la búsqueda y el uso de resultados ya demostrados.


# Desigualdades e igualdades de números reales

Comenzamos presentando una serie de tácticas nuevas para demostrar resultados sobre los reales.

::::nuevaTactica (tactica := "norm_num")
La táctica `norm_num` demuestra igualdades, desigualdades y `≠` entre números concretos. También es capaz de simplificar una tesis aunque no consiga cerrarla.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ (1 : ℝ) / 2 < 1`
  * {tac}`norm_num`
  * No goals
:::

También puede demostrar algunos resultados algebraicos sencillos.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ Nat.Prime 37`
  * {tac}`norm_num`
  * No goals
:::
::::

:::ejemplo
```savedLean
example : ∃ n, n > 3 := by
  use 5
  norm_num
```
:::

::::nuevaTactica (tactica := "linarith")
Si la tesis es una igualdad o desigualdad lineal que se deduce de hacer combinaciones lineales de las hipótesis, `linarith` la cierra.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h1 : x < y`

    `h2 : y < 5`

    `⊢ x < 5`
  * {tac}`linarith`
  * No goals
:::
::::

:::ejemplo
```savedLean
example (ε : ℝ) (hε : ε > 0) : ε / 2 > 0 := by
  linarith
```
:::

:::ejemplo
```savedLean
example (a b : ℝ) (h1 : a + b = 5) (h2 : a - b = 1) :
    a = 3 := by
  linarith
```
:::

:::ejemplo
No hace falta que las hipótesis sean expresiones lineales para que `linarith` las pueda utilizar:

```savedLean
example (x : ℝ) (hx : x ^ 2 > 0) : x ^ 2 + 1 > 0 := by
  linarith
```
:::

::::nuevaTactica (tactica := "ring")
La táctica `ring` demuestra igualdades que son ciertas en cualquier anillo conmutativo y se demuestran operando, sin necesidad de las hipótesis.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2`
  * {tac}`ring`
  * No goals
:::
::::

:::ejemplo
```savedLean
example (ε : ℝ) : ε / 2 + ε / 2 = ε := by
  ring
```
:::

:::ejemplo
```savedLean
example : ∀ a b : ℝ, ∃ x,
    (a + b) ^ 3 =
      a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  intro a b
  use 3
  ring
```
:::


# Uso de resultados ya demostrados

Las tácticas de la sección anterior tienen un alcance limitado. Por ejemplo, en cuanto aparecen objetos como el valor absoluto, en general, ya no son suficientes.

En esta sección introducimos tres cosas: cómo usar un resultado para transformar la tesis o las hipótesis con `rw`, cómo introducir pasos intermedios en una demostración con `have` y cómo encontrar en Mathlib un resultado que necesitemos.

## Reescribir resultados: `rw`

Una de las tácticas más útiles y más usadas es `rw` del inglés _rewrite_. Esta nos permite reescribir nuestras hipótesis y nuestra tesis utilizando resultados ya demostrados u otras hipótesis.

::::nuevaTactica (tactica := "rw")
Si `h : a = b`, la táctica `rw [h]` cambia todas las apariciones de `a` en la tesis por `b`. Con
`rw [h] at h'` lo hace en la hipótesis `h'`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : a = b`

    `⊢ P a`
  * {tac}`rw` `[h]`
  * `h : a = b`

    `⊢ P b`
:::
::::

:::ejemplo
Generalmente, `linarith` no funciona con valores absolutos.

```lean +error (name := linarithAbs)
example (x y : ℝ) (h : x = y) (hy : |y| < 1) : |x| < 1 := by
  linarith
```
```leanOutput linarithAbs
linarith failed to find a contradiction
x y : ℝ
h : x = y
hy : |y| < 1
a✝ : 1 ≤ |x|
⊢ False
failed
```

En su lugar podemos hacer esto:

```savedLean
example (x y : ℝ) (h : x = y) (hy : |y| < 1) : |x| < 1 := by
  rw [h]
  exact hy
```
:::

:::ejemplo

También podemos utilizarlo, en lugar de con hipótesis, con teoremas ya demostrados.
Por ejemplo, `abs_sub_comm` es un teorema que nos dice que para todos `a` y `b` reales, se tiene `|a - b| = |b - a|`:

```savedLean (name := check_abs_sub_comm)
#check abs_sub_comm
```
```leanOutput check_abs_sub_comm
abs_sub_comm.{u_1} {α : Type u_1} [Lattice α] [AddGroup α] (a b : α) : |a - b| = |b - a|
```

Podemos utilizarlo en este resultado:

```savedLean
example (x y ε : ℝ) (h : |x - y| < ε) : |y - x| < ε := by
  rw [abs_sub_comm]
  exact h
```
:::


## Pasos intermedios en demostraciones: `have`

En ocasiones, como en papel, nos será útil introducir nuevas hipótesis y realizar demostraciones intermedias. Para eso existe la siguiente táctica.

::::nuevaTactica (tactica := "have")
La táctica `have h : P := by ...` nos permite demostrar un resultado intermedio `P`, y una vez demostrado lo añade al contexto con el nombre `h`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ Q`
  * {tac}`have` `h : P := by ...`
  * `h : P`

    `⊢ Q`
:::
::::

Si al utilizar `have` no damos un nombre para la hipótesis, Lean la llamará por defecto `this`. Es decir, `have : P := by ...` añade al contexto `this : P`. Si hacemos esto reiteradamente, Lean seguirá usando el nombre `this` para las nuevas hipótesis y las anteriores dejarán de ser utilizables.

:::ejemplo
```savedLean
example (x y : ℝ) (hx : x = 3) (hy : y = x ^ 2 + 1) :
    y > 8 := by
  have h : x ^ 2 = 9 := by
    rw [hx]
    norm_num
  linarith
```
:::

:::ejemplo
```savedLean
example (x : ℝ) : x ^ 2 + 1 > 0 := by
  have h : x ^ 2 ≥ 0 := by exact sq_nonneg x
  linarith
```
:::

Pero, ¿cómo sabemos nosotros que `x ^ 2 ≥ 0` está demostrado y se llama `sq_nonneg`?

## Buscar resultados en Mathlib

Mathlib contiene miles de resultados ya demostrados, y como hemos dicho, tenéis permitidos usar todo lo relativo a las propiedades de los números reales. Pero, ¿cómo podemos saber los nombres de esos resultados?

La comunidad de Mathlib ha creado buscadores que entienden lenguaje natural que nos permiten encontrarlos, basta escribir lo que buscas, ya sea en inglés o con notación matemática, y te devuelven los resultados de Mathlib que más se parecen. La herramienta más utilizada con este fin es [LeanSearch](https://leansearch.net/).

Esta puede resultar muy útil cuando todavía no sabes cómo enunciar en Lean lo que necesitas.

Cuando ya sabes escribir el enunciado en Lean, puede ser más rápido preguntarle directamente a Lean usando la táctica `exact?`.

::::nuevaTactica (tactica := "exact?")
La táctica `exact?` busca en Mathlib un resultado que, junto con las hipótesis, cierre la tesis. Si lo encuentra, en el InfoView aparece `Try this: exact ...` con lo que ha encontrado.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ x ≤ |x|`
  * {tac}`exact?`
  * `⊢ x ≤ |x|`
    `Try this:`
      `[apply] exact le_abs_self x`
:::
::::

:::ejemplo
```savedLean (name := exactInterrogacion)
example (x : ℝ) : x ≤ |x| := by
  exact?
```
```leanOutput exactInterrogacion
Try this:
  [apply] exact le_abs_self x
```

```savedLean
example (x : ℝ) : x ≤ |x| := by
  exact le_abs_self x
```
:::

Una manera eficiente de usar `exact?` es en combinación con `have`.

:::ejemplo
```savedLean (name := exactCuadrado)

example (x : ℝ) : x ^ 2 + 1 > 0 := by
  have h : x ^ 2 ≥ 0 := by exact?
  linarith
```
```leanOutput exactCuadrado
Try this:
  [apply] exact sq_nonneg x
```
:::

En este ejemplo ya sabemos escribir en Lean qué necesitamos, y da la impresión de que debe ser lo suficientemente sencillo como para estar demostrado ya en Mathlib, es en estos casos donde `exact?` brilla.

:::observacion
¿Cómo saber qué expresiones utilizar dentro de un `have` para poder usar `exact?`?

Piensa que en Mathlib, los resultados se escriben con la mayor generalidad posible, y se intenta reducir el código duplicado lo máximo posible. Así, un resultado muy estándar como `x ^ 2 ≥ 0` es fácil pensar que estará en la librería, mientras que una expresión más concreta como `x ^ 2 + 7 - 2 ≥ 0` es improbable que tenga un nombre propio.

Cuanto más practiques con esto y vayas conociendo más resultados de Mathlib, más sencillo te resultará prever cuál va a ser la forma de un resultado que necesitas. Mientras tanto siempre puedes usar LeanSearch :)
:::


# Valor absoluto

El valor absoluto de `x` se escribe `|x|`. Hay multitud de resultados referentes al valor absoluto en Mathlib, y todos son válidos si queréis usarlos, sin embargo, por ahora nos basta con un único hecho:

:::observacion
`|x| < ε` es equivalente a `-ε < x ∧ x < ε`. En Mathlib este resultado es

`abs_lt : |a| < b ↔ -b < a ∧ a < b`.
:::

:::ejemplo
Si `|x - 3| < 1`, entonces `2 < x < 4`.

```savedLean
example (x : ℝ) (h : |x - 3| < 1) : 2 < x ∧ x < 4 := by
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · linarith
  · linarith
```
:::

El siguiente es un resultado que nos vendrá bien cuando trabajemos con sucesiones.

::::ejercicio
Si `|x| < ε/2` e `|y| < ε/2`, entonces `|x + y| < ε`.

```savedLean -keep
theorem abs_suma_lt {x y ε : ℝ} (hx : |x| < ε / 2)
    (hy : |y| < ε / 2) : |x + y| < ε := by
  sorry
```

:::demostracion
```savedLean
theorem abs_suma_lt {x y ε : ℝ} (hx : |x| < ε / 2)
    (hy : |y| < ε / 2) : |x + y| < ε := by
  rw [abs_lt] at *
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · linarith
  · linarith
```
:::
::::


# Resumen hasta el momento

Antes de pasar a sucesiones y continuidad hagamos un repaso de las tácticas que hemos visto en este capítulo.

:::table +header
*
  * Táctica
  * Qué hace
  * Ejemplo
*
  * {tac}`norm_num`
  * Demuestra igualdades, desigualdades y `≠` entre números concretos.
  * `⊢ (1 : ℝ) / 2 < 1`
*
  * {tac}`linarith`
  * Demuestra igualdades y desigualdades que se deducen de combinaciones lineales de las hipótesis.
  * `h1 : x < y`, `h2 : y < 5`, `⊢ x < 5`
*
  * {tac}`ring`
  * Demuestra igualdades que se obtienen operando con las reglas del álgebra, sin usar hipótesis.
  * `⊢ (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2`
*
  * {tac}`rw` `[h]`
  * Si `h : a = b` (o `h : P ↔ Q`), cambia `a` por `b` en la tesis. Con `at h'`, en la hipótesis `h'`.
  * `rw [abs_lt] at h`
*
  * {tac}`have` `h : P := by ...`
  * Demuestra un resultado intermedio `P` y lo añade al contexto como `h`.
  * `have h : x ^ 2 ≥ 0 := by exact sq_nonneg x`
*
  * {tac}`exact?`
  * Busca en Mathlib un resultado que cierre la tesis y te lo sugiere.
  * `⊢ x ≤ |x|`
:::

Recordamos también el siguiente resultado que hemos demostrado en la sección anterior y que nos será útil al trabajar con sucesiones.

```
abs_suma_lt {x y ε : ℝ} (hx : |x| < ε / 2) (hy : |y| < ε / 2) : |x + y| < ε
```

# Sucesiones de números reales

La primera vez que uno aprende lo que es una sucesión de números (en este caso reales) le enseñan que se trata de una lista ordenada infinita de números que puede o puede no converger a un valor concreto.

Otra manera común de ver una sucesión es como una correspondencia (es decir, una función) entre los números naturales y los números reales. Es así como se trabaja con sucesiones en Lean.

Formalmente, se define una sucesión numérica como una función `a : ℕ → X` de los naturales en cualquier otro conjunto numérico `X` que asigna a cada natural `n` el número de la sucesión cuya posición es la `n`-ésima. Así, dada una sucesión `a` su `n`-ésimo término es `a n : X`.

```savedLean (name := check_a_n)
variable (X : Type) (a : ℕ → X) (n : ℕ)
#check a n
```
```leanOutput check_a_n
a n : X
```

Lo más importante a la hora de trabajar con sucesiones es definir las nociones de convergencia y de límite. Damos nuestras propias definiciones para sucesiones de números reales:

:::definicion "sucesión convergente"
```savedLean
def converge (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
```
:::

De esta forma, si `a : ℕ → ℝ` es una sucesión de números reales y `L : ℝ`, decir `converge a L` significa que `a` tiene límite `L`.

:::observacion
Para escribir una sucesión concreta usamos la notación `fun n ↦ ...` que vimos en la primera clase. Así `b := fun n ↦ a n + c` es una nueva sucesión cuyo `n`-ésimo término es el `n`-ésimo término de `a` más `c`.

Si la expresión no depende de `n`, podemos poner `_` en lugar de un nombre (Lean nos avisará), por ejemplo `fun _ ↦ c` es la sucesión constantemente `c`.
:::

:::ejemplo
Una sucesión constante converge a su valor.

```savedLean
theorem converge_const (c : ℝ) :
    converge (fun _ ↦ c) c := by
  unfold converge
  intro ε hε
  use 0
  intro n hn
  have : (fun x => c) n - c = 0 := by
    ring
  rw [this]
  have : |(0 : ℝ)| = 0 := by
    exact abs_zero -- exact?
  rw [this]
  exact hε
```
:::


::::ejercicio
Si `a` converge a `L`, entonces `a + c` converge a `L + c`.

```savedLean -keep
theorem converge_suma_const {a : ℕ → ℝ} {L : ℝ}
    (c : ℝ) (ha : converge a L) :
    converge (fun n ↦ a n + c) (L + c) := by
  sorry
```

:::demostracion
```savedLean
theorem converge_suma_const {a : ℕ → ℝ} {L : ℝ}
    (c : ℝ) (ha : converge a L) :
    converge (fun n ↦ a n + c) (L + c) := by
  intro ε hε
  specialize ha ε hε
  obtain ⟨N, hN⟩ := ha
  use N
  intro n hn
  specialize hN n hn
  have : (fun n => a n + c) n - (L + c) = a n - L := by
    ring
  rw [this]
  exact hN
```
:::
::::

## Ejercicios extra

::::ejercicio
Si `a` converge a `L`, entonces `-a` converge a `-L`.

```savedLean
example (a : ℕ → ℝ) (L : ℝ) (h : converge a L) :
    converge (fun n ↦ -a n) (-L) := by
  sorry
```

:::demostracion
```savedLean
example (a : ℕ → ℝ) (L : ℝ) (h : converge a L) :
    converge (fun n ↦ -a n) (-L) := by
  intro ε hε
  specialize h ε hε
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  specialize hN n hn
  have : (fun n => -a n) n - -L = - (a n - L) := by
    ring
  rw [this]
  have : |- (a n - L)| = |a n - L| := by
    exact abs_neg (a n - L) -- exact?
  rw [this]
  exact hN
```
:::
::::

::::ejercicio
Si `a` converge a `L` y `b` converge a `M`, entonces `a + b` converge a `L + M`.

```savedLean -keep
theorem converge_suma {a b : ℕ → ℝ} {t u : ℝ}
    (ha : converge a t) (hb : converge b u) :
    converge (fun n ↦ a n + b n) (t + u) := by
  sorry
```

:::demostracion
```savedLean
theorem converge_suma {a b : ℕ → ℝ} {t u : ℝ}
    (ha : converge a t) (hb : converge b u) :
    converge (fun n ↦ a n + b n) (t + u) := by
  unfold converge at *
  intro ε hε
  have hε' : ε/2 > 0 := by
    linarith
  specialize ha (ε/2) hε'
  specialize hb (ε/2) hε'
  obtain ⟨Na, hNa⟩ := ha
  obtain ⟨Nb, hNb⟩ := hb
  use max Na Nb
  intro n hn
  have : (fun n => a n + b n) n - (t + u) =
      (a n - t) + (b n - u) := by
    ring
  rw [this]
  apply abs_suma_lt
  · have : n ≥ Na := by
      exact le_of_max_le_left hn -- exact?
    exact hNa n this
  · have : n ≥ Nb := by
      exact le_of_max_le_right hn -- exact?
    exact hNb n this
```
:::
::::

# Continuidad de funciones sobre los reales

De nuevo damos nuestra propia definición de continuidad en ℝ en lugar de usar la de Mathlib.

:::definicion "función continua en un punto"
```savedLean
def continuaEn (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε
```
:::

:::definicion "función continua"
```savedLean
def continua (f : ℝ → ℝ) : Prop := ∀ a, continuaEn f a
```
:::

:::ejemplo
Las funciones constantes son continuas.

```savedLean
example (c : ℝ) : continua (fun _ ↦ c) := by
  unfold continua
  intro a
  unfold continuaEn
  intro ε hε
  use 1
  constructor
  · norm_num
  · intro x hx
    have : (fun x => c) x - (fun x => c) a = 0 := by
      exact sub_self ((fun x => c) x) -- exact?
    rw [this]
    rw [abs_zero] -- como vimos en `converge_const`
    exact hε
```
:::

::::ejercicio
La identidad es continua.

```savedLean
example : continua (fun x ↦ x) := by
  sorry
```

:::demostracion
```savedLean
example : continua (fun x ↦ x) := by
  intro a ε hε
  use ε
  constructor
  · exact hε
  · intro x hx
    exact hx
```
:::
::::

## Ejercicio extra

::::ejercicio
La función `5x - 2` es continua.

```savedLean
example : continua (fun x ↦ 5 * x - 2) := by
  sorry
```

:::demostracion
```savedLean
example : continua (fun x ↦ 5 * x - 2) := by
  intro a ε hε
  use ε / 5
  constructor
  · linarith
  · intro x hx
    norm_num
    have : 5 * x - 5 * a = 5 * (x - a) := by ring
    rw [this]
    have : |5 * (x - a)| = |5| * |(x - a)| := by
      exact abs_mul 5 (x - a)
    rw [this]
    norm_num -- podrías usar have : |(5 : ℝ)| = 5
    linarith
```
:::
::::


## Operaciones con funciones continuas


::::ejercicio
Si `f` es continua en `a` y `g` es continua en `f a`, entonces `g ∘ f` es continua en `a`.

```savedLean -keep
theorem continuaEn_comp {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuaEn f a) (hg : continuaEn g (f a)) :
    continuaEn (g ∘ f) a := by
  sorry
```

:::demostracion
```savedLean
theorem continuaEn_comp {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuaEn f a) (hg : continuaEn g (f a)) :
    continuaEn (g ∘ f) a := by
  intro ε hε
  specialize hg ε hε
  obtain ⟨η, hη, hg⟩ := hg
  specialize hf η hη
  obtain ⟨δ, hδ, hf⟩ := hf
  use δ
  constructor
  · exact hδ
  · intro x hx
    specialize hf x hx
    specialize hg (f x) hf
    exact hg
```
:::
::::

:::ejemplo
La composición de funciones continuas es continua.

```savedLean
theorem continua_comp (f g : ℝ → ℝ) (hf : continua f)
    (hg : continua g) : continua (g ∘ f) := by
  intro a
  exact continuaEn_comp (hf a) (hg (f a)) -- `exact?`
```
:::


::::ejercicio
Si `f` y `g` son continuas en `a`, entonces `f + g` es continua en `a`.

```savedLean -keep
theorem continuaEn_suma (f g : ℝ → ℝ) (a : ℝ)
    (hf : continuaEn f a) (hg : continuaEn g a) :
    continuaEn (fun x ↦ f x + g x) a := by
  sorry
```

:::demostracion
```savedLean
theorem continuaEn_suma (f g : ℝ → ℝ) (a : ℝ)
    (hf : continuaEn f a) (hg : continuaEn g a) :
    continuaEn (fun x ↦ f x + g x) a := by
  unfold continuaEn
  intro ε hε
  have he2 : ε/2 > 0 := by norm_num; exact hε
  specialize hf (ε/2) he2
  specialize hg (ε/2) he2
  obtain ⟨δ₁, hδ₁, hf⟩ := hf
  obtain ⟨δ₂, hδ₂, hg⟩ := hg
  use min δ₁ δ₂
  constructor
  · exact lt_min hδ₁ hδ₂
  · intro x hx
    have h : |x - a| < δ₁ ∧ |x - a| < δ₂ := by
      exact lt_inf_iff.mp hx -- exact?
    specialize hf x h.left
    specialize hg x h.right
    have : f x + g x - (f a + g a) =
        f x - f a + (g x - g a) := by ring
    rw [this]
    exact abs_suma_lt hf hg -- exact?
```
:::
::::

::::ejercicio
La suma de funciones continuas es continua.

```savedLean -keep
theorem continua_suma (f g : ℝ → ℝ)
    (hf : continua f) (hg : continua g) :
    continua (fun x ↦ f x + g x) := by
  sorry
```

:::demostracion
```savedLean
theorem continua_suma (f g : ℝ → ℝ)
    (hf : continua f) (hg : continua g) :
    continua (fun x ↦ f x + g x) := by
  intro a
  exact continuaEn_suma f g a (hf a) (hg a)
```
:::
::::

::::ejercicio
Si `g` es continua, entonces `-g` también es continua.

```savedLean -keep
theorem continua_neg (g : ℝ → ℝ) (hg : continua g) :
    continua (fun x ↦ -g x) := by
  sorry
```

:::demostracion
```savedLean
theorem continua_neg (g : ℝ → ℝ) (hg : continua g) :
    continua (fun x ↦ -g x) := by
  intro a ε hε
  obtain ⟨δ, hδ, h⟩ := hg a ε hε
  use δ
  constructor
  · exact hδ
  · intro x hx
    have : -g x - -g a = -(g x - g a) := by ring
    rw [this, abs_neg]
    exact h x hx
```
:::
::::

::::ejercicio
Por último, utilizando los dos últimos teoremas, `continua_suma` y `continua_neg`, demuestra que si `f` y `g` son continuas, entonces `f - g` lo es.

```savedLean -keep
theorem continua_resta (f g : ℝ → ℝ)
    (hf : continua f) (hg : continua g) :
    continua (fun x ↦ f x - g x) := by
  sorry
```

:::demostracion
```savedLean
theorem continua_resta (f g : ℝ → ℝ)
    (hf : continua f) (hg : continua g) :
    continua (fun x ↦ f x - g x) := by
  have h : (fun x ↦ f x - g x) = (fun x ↦ f x + -g x) := by
    exact List.map_inj.mp rfl -- exact?
  rw [h]
  apply continua_suma
  · exact hf
  · exact continua_neg g hg
```
:::
::::


## Continuidad en un conjunto

Cuando se trata de continuidad, es común querer trabajar con funciones que son continuas en un conjunto. Para esto no nos sirve la definición de `continua` que hemos dado, pues esta simplemente nos dice que una función es continua en todo ℝ.

Para hablar de subconjuntos necesitamos introducir una nueva notación.

:::observacion
La notación `s : Set ℝ` nos indica que `s` es del tipo de los subconjuntos de ℝ, es decir, un subconjunto de ℝ.

`hx : x ∈ s` es una demostración de que `x` pertenece a `s`.
:::

:::definicion "función continua en un conjunto"
```savedLean
def continuaEnConj (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ a ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s,
    |x - a| < δ → |f x - f a| < ε
```
:::

::::ejercicio
Si `f` es continua, entonces es continua en cualquier conjunto `s : Set ℝ`.

```savedLean
example (f : ℝ → ℝ) (s : Set ℝ) (hf : continua f) :
    continuaEnConj f s := by
  sorry
```

:::demostracion
```savedLean
example (f : ℝ → ℝ) (s : Set ℝ) (hf : continua f) :
    continuaEnConj f s := by
  intro a ha ε hε
  specialize hf a ε hε
  obtain ⟨δ, hδ, hf⟩ := hf
  use δ
  constructor
  · exact hδ
  · intro x hx hxa
    exact hf x hxa
```
:::
::::

## Continuidad y sucesiones

Para terminar, juntamos las dos secciones.

::::ejercicio
Si `f` es continua en `x` y `a` es una sucesión que converge a `x`, entonces `f (a n)` converge a
`f x`.

```savedLean
theorem sucesion_continuaEn (f : ℝ → ℝ) (x : ℝ) (a : ℕ → ℝ)
    (hf : continuaEn f x) (ha : converge a x) :
    converge (fun n ↦ f (a n)) (f x) := by
  sorry
```

:::demostracion
```savedLean
example (f : ℝ → ℝ) (x : ℝ) (a : ℕ → ℝ)
    (hf : continuaEn f x) (ha : converge a x) :
    converge (fun n ↦ f (a n)) (f x) := by
  intro ε hε
  specialize hf ε hε
  obtain ⟨δ, hδ, hf⟩ := hf
  specialize ha δ hδ
  obtain ⟨N, hN⟩ := ha
  use N
  intro n hn
  specialize hN n hn
  specialize hf (a n) hN
  exact hf
```
:::
::::


```savedLean -show
end Clase3
```

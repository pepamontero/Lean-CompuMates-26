
import VersoManual
import Apuntes.Meta.Lean
import Apuntes.Meta.NuevaTactica
import Apuntes.Meta.Estilo
import Apuntes.Meta.Teorema
import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Real.Basic

open Verso.Genre Manual

open Verso.Genre.Manual.InlineLean

open Apuntes

set_option pp.rawOnError true

#doc (Manual) "Lógica: conectores y cuantificadores" =>

%%%
%%%

```savedImport
import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Real.Basic
```
```savedComment
# Clase 2: conectores lógicos

Tácticas nuevas: `constructor`, `obtain`, `left` / `right`, `rcases`, `rfl`, `by_contra`,
`specialize` y `use`.
```
```savedLean -show
namespace Clase2
```

En la clase anterior aprendimos a manejar la implicación. Ahora añadimos los demás
constructores lógicos: la conjunción, la disyunción, la negación y la doble implicación. Al
final volveremos sobre los cuantificadores, que ya aparecieron informalmente en la clase anterior.

# Repaso

Estas son las tácticas que ya conocemos:

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ P → Q`
  * {tac}`intro` `hP`
  * `hP : P`

    `⊢ Q`
*
  * `h : P → Q`

    `hP : P`
  * {tac}`apply` `h` {tac}`at` `hP`
  * `hP : Q`
*
  * `h : P`

    `⊢ P`
  * {tac}`exact` `h`
  * No goals
*
  * `h : P → Q`

    `hP : P`

    `⊢ Q`
  * {tac}`exact` `h hP`
  * No goals
*
  * `hf : inyectiva f`
  * {tac}`unfold` `inyectiva` {tac}`at` `hf`
  * `hf : ∀ x y, f x = f y → x = y`
:::

La cuarta fila es la implicación vista como función: si `h : P → Q` y `hP : P`, entonces
`h hP : Q`. Con ella tenemos dos formas de demostrar, por ejemplo, el modus ponens:

```savedLean
example (P Q : Prop) : (P → Q) → P → Q := by
  intro hPQ hP
  apply hPQ at hP
  exact hP

example (P Q : Prop) : (P → Q) → P → Q := by
  intro hPQ hP
  exact hPQ hP
```

Durante toda la clase trabajaremos con proposiciones y funciones cualesquiera:

```savedLean
variable (P Q R : Prop)
variable (f g : ℝ → ℝ)
```

# Conjunción

Si `P : Prop` y `Q : Prop`, entonces `P ∧ Q : Prop` es la proposición que afirma que `P` y `Q`
son ambas ciertas. El símbolo se escribe con `\and`.

```savedLean (name := checkY)
#check P ∧ Q
```
```leanOutput checkY
P ∧ Q : Prop
```

## La conjunción en la tesis

Para demostrar `P ∧ Q` hay que hacer dos cosas: demostrar `P` y demostrar `Q`. La táctica que
parte el trabajo en esos dos trozos es `constructor`.

::::nuevaTactica (tactica := "constructor")
Cuando la tesis es una conjunción `P ∧ Q`, la táctica `constructor` la sustituye por dos tesis
separadas: primero `P` y después `Q`. Decimos entonces que tenemos dos tesis.

Para no perdernos, cada una de ellas se demuestra en un bloque que empieza por `·` (se escribe
con `\.`). Dentro de un bloque solo se ve una de las dos tesis, así que es mucho más difícil
equivocarse.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ P ∧ Q`
  * {tac}`constructor`
  * primera tesis: `⊢ P`

    segunda tesis: `⊢ Q`
:::
::::

:::ejemplo
Si `P` es cierta y `Q` es cierta, entonces `P ∧ Q` es cierta.

```savedLean
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ
```
:::

::::ejercicio
Si `P` implica `Q` y `P` es cierta, entonces se cumplen a la vez `P` y `Q`.

```savedLean
example (hPQ : P → Q) (hP : P) : P ∧ Q := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (hPQ : P → Q) (hP : P) : P ∧ Q := by
  constructor
  · exact hP
  · apply hPQ at hP
    exact hP
```

Aplicando la implicación como función:

```savedLean
example (hPQ : P → Q) (hP : P) : P ∧ Q := by
  constructor
  · exact hP
  · exact hPQ hP
```
:::
::::

La conjunción aparece constantemente en las definiciones matemáticas, porque muchas propiedades
son en realidad la conjunción de otras dos. El ejemplo clásico es la biyectividad:

:::definicion "función inyectiva"
```savedLean
def inyectiva : Prop := ∀ x y, f x = f y → x = y
```
:::

:::definicion "función sobreyectiva"
```savedLean
def sobreyectiva : Prop := ∀ y, ∃ x, f x = y
```
:::

:::definicion "función biyectiva"
```savedLean
def biyectiva : Prop := inyectiva f ∧ sobreyectiva f
```
:::

::::ejercicio
Una función inyectiva y sobreyectiva es biyectiva.

```savedLean
example (hf1 : inyectiva f) (hf2 : sobreyectiva f) :
    biyectiva f := by sorry
```

:::demostracion
```savedLean
example (hf1 : inyectiva f) (hf2 : sobreyectiva f) :
    biyectiva f := by
  unfold biyectiva
  constructor
  · exact hf1
  · exact hf2
```
:::
::::

## La conjunción en una hipótesis

Ahora la situación es la contraria: tenemos `h : P ∧ Q` y lo que queremos es quedarnos con una
de las dos mitades. Para eso no hace falta ninguna táctica nueva, basta con la notación de
proyecciones: si `h : P ∧ Q`, entonces `h.left : P` y `h.right : Q`.

:::ejemplo
De `P ∧ Q` se deduce `Q`.

```savedLean
example : P ∧ Q → Q := by
  intro hPQ
  exact hPQ.right
```
:::

::::ejercicio
Propiedad conmutativa: si se tiene `P ∧ Q` entonces se tiene `Q ∧ P`.

```savedLean
example : P ∧ Q → Q ∧ P := by sorry
```

:::demostracion
```savedLean
example : P ∧ Q → Q ∧ P := by
  intro hPQ
  constructor
  · exact hPQ.right
  · exact hPQ.left
```
:::
::::

::::ejercicio
Toda función biyectiva es sobreyectiva.

```savedLean
example (hf : biyectiva f) : sobreyectiva f := by sorry
```

:::demostracion
```savedLean
example (hf : biyectiva f) : sobreyectiva f := by
  exact hf.right
```
:::
::::

Las proyecciones se pueden encadenar, lo cual resulta muy cómodo cuando las conjunciones están
anidadas.

::::ejercicio
Propiedad asociativa: si se tiene `P ∧ (Q ∧ R)` entonces se tiene `(P ∧ Q) ∧ R`.

```savedLean
example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by sorry
```

:::demostracion
```savedLean
example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro h
  constructor
  · constructor
    · exact h.left
    · exact h.right.left
  · exact h.right.right
```
:::
::::

::::ejercicio
Si `f` y `g` son biyectivas, entonces `g` es inyectiva y `f` es sobreyectiva.

```savedLean
example (h : biyectiva f ∧ biyectiva g) :
    inyectiva g ∧ sobreyectiva f := by sorry
```

:::demostracion
```savedLean
example (h : biyectiva f ∧ biyectiva g) :
    inyectiva g ∧ sobreyectiva f := by
  constructor
  · exact h.right.left
  · exact h.left.right
```
:::
::::

Cuando las conjunciones están anidadas, contar izquierdas y derechas se vuelve pesado, y a veces
es preferible partir la hipótesis en trozos con nombre y olvidarse de las proyecciones.

Antes de ver la táctica que lo hace, conviene conocer la notación de constructor anónimo: si
`hP : P` y `hQ : Q`, entonces `⟨hP, hQ⟩ : P ∧ Q` (los paréntesis angulares se escriben con
`\<` y `\>` o con `\<>`). Sirve para construir una conjunción sin usar `constructor`.

```savedLean
example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
```

Esa misma notación es la que usamos para descomponer una hipótesis.

::::nuevaTactica (tactica := "obtain")
Si `h : P ∧ Q`, la táctica `obtain ⟨hP, hQ⟩ := h` sustituye `h` por sus dos mitades, con los
nombres que nosotros elijamos. A partir de ahí trabajamos con `hP` y `hQ` como con cualquier
otra hipótesis.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : P ∧ Q`
  * {tac}`obtain` `⟨hP, hQ⟩ := h`
  * `hP : P`

    `hQ : Q`
:::
::::

:::ejemplo
Si `f` y `g` son biyectivas, entonces `g` es inyectiva.

```savedLean
example (h : biyectiva f ∧ biyectiva g) : inyectiva g := by
  obtain ⟨hf, hg⟩ := h
  obtain ⟨hg_iny, hg_sobre⟩ := hg
  exact hg_iny
```
:::

## Ejercicios extra

::::ejercicio
Si `P` implica `Q` y `Q` implica `R`, y además `P` es cierta, entonces `R` es cierta.

```savedLean
example (h : (P → Q) ∧ (Q → R)) (hP : P) : R := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (h : (P → Q) ∧ (Q → R)) (hP : P) : R := by
  apply h.left at hP
  apply h.right at hP
  exact hP
```

Aplicando la implicación como función:

```savedLean
example (h : (P → Q) ∧ (Q → R)) (hP : P) : R := by
  exact h.right (h.left hP)
```
:::
::::

::::ejercicio
En las mismas condiciones, las tres proposiciones `P`, `Q` y `R` son ciertas.

```savedLean
example (h : (P → Q) ∧ (Q → R)) (hP : P) :
    P ∧ Q ∧ R := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (h : (P → Q) ∧ (Q → R)) (hP : P) : P ∧ Q ∧ R := by
  constructor
  · exact hP
  · constructor
    · apply h.left at hP
      exact hP
    · apply h.left at hP
      apply h.right at hP
      exact hP
```

Aplicando la implicación como función:

```savedLean
example (h : (P → Q) ∧ (Q → R)) (hP : P) : P ∧ Q ∧ R := by
  constructor
  · exact hP
  · constructor
    · exact h.left hP
    · exact h.right (h.left hP)
```

Observa que la tesis `P ∧ Q ∧ R` se lee como `P ∧ (Q ∧ R)`: la conjunción asocia por la derecha.
Por eso el primer `constructor` la parte en `P` y `Q ∧ R`, y hace falta un segundo `constructor`
para seguir.
:::
::::

# Disyunción

Si `P : Prop` y `Q : Prop`, entonces `P ∨ Q : Prop` es la proposición que afirma que al menos una
de las dos es cierta. El símbolo se escribe con `\or`.

```savedLean (name := checkO)
#check P ∨ Q
```
```leanOutput checkO
P ∨ Q : Prop
```

## La disyunción en la tesis

Aquí la situación es la opuesta a la de la conjunción: para demostrar `P ∨ Q` no hace falta
demostrarlo todo, basta con elegir un lado y demostrarlo.

::::nuevaTactica (tactica := "left / right")
Cuando la tesis es una disyunción `P ∨ Q`, la táctica `left` se compromete a demostrar el lado
izquierdo y `right` el derecho. En ambos casos nos quedamos con una sola tesis.

Elegir bien el lado es cosa nuestra: si nos equivocamos, la demostración se quedará atascada y
habrá que volver atrás.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ P ∨ Q`
  * {tac}`left`
  * `⊢ P`
*
  * `⊢ P ∨ Q`
  * {tac}`right`
  * `⊢ Q`
:::
::::

:::ejemplo
Si `P` es cierta, entonces `P ∨ Q` es cierta.

```savedLean
example : P → P ∨ Q := by
  intro hP
  left
  exact hP
```
:::

::::ejercicio
Si de `P` se deduce `Q ∧ R`, entonces se cumple `P` o bien `P` implica `R`.

```savedLean
example (hPQR : P → Q ∧ R) : P ∨ (P → R) := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (hPQR : P → Q ∧ R) : P ∨ (P → R) := by
  right
  intro hP
  apply hPQR at hP
  exact hP.right
```

Aplicando la implicación como función:

```savedLean
example (hPQR : P → Q ∧ R) : P ∨ (P → R) := by
  right
  intro hP
  exact (hPQR hP).right
```

No tenemos ninguna demostración de `P`, así que el lado izquierdo es inaccesible; la única
opción razonable es `right`.
:::
::::

Igual que la conjunción, la disyunción aparece en definiciones matemáticas de verdad. Un ejemplo es
la monotonía: una función es monótona si es creciente o decreciente.

:::definicion "función creciente"
```savedLean
def creciente : Prop := ∀ x y, x ≤ y → f x ≤ f y
```
:::

:::definicion "función decreciente"
```savedLean
def decreciente : Prop := ∀ x y, x ≤ y → f y ≤ f x
```
:::

:::definicion "función monótona"
```savedLean
def monotona : Prop := creciente f ∨ decreciente f
```
:::

::::ejercicio
Toda función creciente es monótona.

```savedLean
example (hf : creciente f) : monotona f := by sorry
```

:::demostracion
```savedLean
example (hf : creciente f) : monotona f := by
  unfold monotona
  left
  exact hf
```
:::
::::

::::ejercicio
La función identidad es monótona.

```savedLean
example : monotona (fun x ↦ x) := by sorry
```

:::demostracion
```savedLean
example : monotona (fun x ↦ x) := by
  unfold monotona
  left
  intro x y h
  exact h
```

Fíjate en que para elegir lado hay que saber algo concreto sobre la función: la identidad es
creciente, así que el único lado demostrable es el izquierdo.
:::
::::

## La disyunción en una hipótesis

Si sabemos que `P ∨ Q` pero no sabemos cuál de las dos es cierta, lo único que podemos hacer es
distinguir casos: ver qué ocurre si se cumple `P` y ver qué ocurre si se cumple `Q`.

::::nuevaTactica (tactica := "rcases")
Si `h : P ∨ Q`, la táctica `rcases h with hP | hQ` abre dos ramas de la demostración. En la
primera disponemos de `hP : P` y en la segunda de `hQ : Q`; la tesis es la misma en las dos.

Como en el caso de `constructor`, obtenemos dos tesis y las separamos con `·`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : P ∨ Q`

    `⊢ R`
  * {tac}`rcases` `h` {tac}`with` `hP | hQ`
  * caso 1: `hP : P`, con `⊢ R`

    caso 2: `hQ : Q`, con `⊢ R`
:::
::::

:::ejemplo
Si se cumple `P ∨ Q` y además `Q` implica `P`, entonces `P` es cierta.

```savedLean
example (h : P ∨ Q) (hQP : Q → P) : P := by
  rcases h with hP | hQ
  · exact hP
  · apply hQP at hQ
    exact hQ
```
:::

::::ejercicio
Propiedad conmutativa: si `P ∨ Q` entonces `Q ∨ P`.

```savedLean
example : P ∨ Q → Q ∨ P := by sorry
```

:::demostracion
```savedLean
example : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  · right
    exact hP
  · left
    exact hQ
```
:::
::::

::::ejercicio
Si `P` implica `R` y `Q` implica `R`, entonces `P ∨ Q` implica `R`.

```savedLean
example (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  intro h
  rcases h with hP | hQ
  · apply hPR at hP
    exact hP
  · apply hQR at hQ
    exact hQ
```

Aplicando la implicación como función:

```savedLean
example (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  intro h
  rcases h with hP | hQ
  · exact hPR hP
  · exact hQR hQ
```
:::
::::

Ese es exactamente el razonamiento que hacemos con las funciones monótonas: no sabemos si `f`
es creciente o decreciente, así que demostramos lo que queremos en los dos casos por separado.

::::ejercicio
Si `f` es monótona y `g` es creciente, entonces la composición `g ∘ f` es monótona.

```savedLean
example (hf : monotona f) (hg : creciente g) :
    monotona (g ∘ f) := by sorry
```

:::demostracion
```savedLean
example (hf : monotona f) (hg : creciente g) :
    monotona (g ∘ f) := by
  unfold monotona
  rcases hf with hc | hd
  · left
    intro x y hxy
    apply hc at hxy
    apply hg at hxy
    exact hxy
  · right
    intro x y hxy
    apply hd at hxy
    apply hg at hxy
    exact hxy
```

Aquí se ve lo que tienen de particular las hipótesis disyuntivas: cada caso se demuestra igual,
pero el lado que elegimos en la tesis es distinto. Si `f` es creciente, la composición lo es; si
`f` es decreciente, la composición también lo es.
:::
::::

::::ejercicio
Si `f` y `g` son monótonas, entonces `g ∘ f` es monótona.

```savedLean
example (hf : monotona f) (hg : monotona g) :
    monotona (g ∘ f) := by sorry
```

:::demostracion
```savedLean
example (hf : monotona f) (hg : monotona g) :
    monotona (g ∘ f) := by
  unfold monotona
  rcases hf with hfc | hfd
  · rcases hg with hgc | hgd
    · left
      intro x y hxy
      apply hfc at hxy
      apply hgc at hxy
      exact hxy
    · right
      intro x y hxy
      apply hfc at hxy
      apply hgd at hxy
      exact hxy
  · rcases hg with hgc | hgd
    · right
      intro x y hxy
      apply hfd at hxy
      apply hgc at hxy
      exact hxy
    · left
      intro x y hxy
      apply hfd at hxy
      apply hgd at hxy
      exact hxy
```

Las dos crecientes o las dos decrecientes dan una composición creciente; si hay una de cada, la
composición es decreciente. Por eso elegimos `left` en unos casos y `right` en otros.
:::
::::

# Negación

Si `P : Prop`, entonces `¬P : Prop` es la proposición que afirma que `P` es falsa. El símbolo se
escribe con `\not` o con `\neg`.

```savedLean (name := checkNo)
#check ¬P
```
```leanOutput checkNo
¬P : Prop
```

Lean no trata la negación como un constructor nuevo, sino como una abreviatura. Podemos pedirle
que nos enseñe cómo está definida con {kw}`#print`:{margin}[{kw}`#print` no siempre es tan
legible como aquí: enseña todo lo que ve Lean, incluidas muchas cosas que se generan
automáticamente por debajo y que a nosotros no nos interesan. Lo normal es buscar en la salida
la parte que nos importa e ignorar el resto.]

```savedLean (name := printNot)
#print Not
```
```leanOutput printNot
def Not : Prop → Prop :=
fun a => a → False
```

Es decir, `¬P` es `P → False`, donde `False` es la proposición que nunca se cumple: negar `P` es
decir que de `P` se deduciría algo absurdo.

Igual que casi nunca hace falta escribir `unfold` para que Lean sepa que `inyectiva f` es
`∀ x y, f x = f y → x = y`, tampoco hace falta aquí: para Lean, `¬P` y `P → False` son
literalmente la misma proposición. Cuando dos expresiones son iguales por definición, podemos
demostrar que lo son con `rfl`.

::::nuevaTactica (tactica := "rfl")
Cuando la tesis es una igualdad y Lean puede comprobar que los dos lados son la misma cosa
(quizá después de desplegar definiciones), la táctica `rfl` la cierra.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ x = x`
  * {tac}`rfl`
  * No goals
:::
::::

¿Recuerdas `MiTeorema`, el que en la primera clase era demasiado difícil? Ya podemos demostrarlo:

```savedLean
theorem MiTeorema : 3 = 3 := by rfl
```

:::ejemplo
Las tres igualdades siguientes son ciertas por definición.

```savedLean
example : P = P := by rfl

example :
    (inyectiva f) = (∀ x y, f x = f y → x = y) := by rfl

example : (¬P) = (P → False) := by rfl
```
:::

Lo interesante de que `¬P` sea una implicación es que no necesitamos aprender tácticas nuevas
para manejarla: `intro`, `apply ... at ...` y `exact` funcionan exactamente igual que siempre. Y
si en algún momento queremos ver la implicación escrita del todo, `unfold Not` la despliega,
tanto en la tesis como en una hipótesis.

:::ejemplo
Contrarrecíproco: si `P` implica `Q`, entonces `¬Q` implica `¬P`.

```savedLean
example (hPQ : P → Q) : ¬Q → ¬P := by
  intro hnQ
  unfold Not
  intro hP
  unfold Not at hnQ
  apply hPQ at hP
  apply hnQ at hP
  exact hP
```
:::

::::ejercicio
Toda proposición implica su doble negación.

```savedLean
example : P → ¬¬P := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example : P → ¬¬P := by
  intro hP hnP
  unfold Not at hnP
  apply hnP at hP
  exact hP
```

Aplicando la implicación como función:

```savedLean
example : P → ¬¬P := by
  intro hP hnP
  exact hnP hP
```

Merece la pena seguir el estado paso a paso. Al principio la tesis es `P → ¬¬P`; tras el primer
`intro` pasa a ser `¬¬P`, que por definición es `¬P → False`, de modo que el segundo `intro`
también funciona y nos deja `hnP : ¬P` con tesis `False`. Como `hnP` es la implicación
`P → False`, al aplicarla a `hP` obtenemos justo lo que buscábamos.
:::
::::

## Reducción al absurdo

El recíproco de ese último ejercicio, `¬¬P → P`, no sale con lo que tenemos: por mucho que
despleguemos definiciones, la tesis es `P` a secas y no hay ninguna hipótesis que nos la dé. Lo
que se hace en matemáticas en esta situación es suponer lo contrario y buscar una contradicción.

::::nuevaTactica (tactica := "by_contra")
Si la tesis es `P`, la táctica `by_contra h` la sustituye por `False` y añade la hipótesis
`h : ¬P`. Es decir, nos deja suponer que la tesis es falsa a cambio de tener que llegar a un
absurdo.

Si la tesis ya es una negación `¬Q`, Lean no añade `h : ¬¬Q` sino directamente su versión
simplificada, `h : Q`. En este caso, `by_contra h` hace lo mismo que `intro h`, porque `¬Q` es `Q → False`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ P`
  * {tac}`by_contra` `h`
  * `h : ¬P`

    `⊢ False`
*
  * `⊢ ¬Q`
  * {tac}`by_contra` `h`
  * `h : Q`

    `⊢ False`
:::
::::

:::ejemplo
De la doble negación de `P` se deduce `P`.

```savedLean
example : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  apply hnnP at hnP
  exact hnP
```
:::

Aquí `hnnP : ¬¬P` es la implicación `¬P → False`, y `by_contra` nos ha dado justo un `hnP : ¬P`,
así que al aplicar la una a la otra obtenemos `False`, que es exactamente la tesis.

::::ejercicio
El recíproco del contrarrecíproco: si `¬P` implica `¬Q`, entonces `Q` implica `P`.

```savedLean
example (h : ¬P → ¬Q) : Q → P := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (h : ¬P → ¬Q) : Q → P := by
  intro hQ
  by_contra hnP
  apply h at hnP
  apply hnP at hQ
  exact hQ
```

Aplicando la implicación como función:

```savedLean
example (h : ¬P → ¬Q) : Q → P := by
  intro hQ
  by_contra hnP
  exact h hnP hQ
```

Sin `by_contra` no saldría: la tesis `P` no es una negación, así que no hay nada que introducir,
y `h` solo nos sirve si tenemos un `¬P` al que aplicarla. Suponer `¬P` es justo lo que nos da
ese `¬P`.
:::
::::


## Ejercicio extra: el símbolo ≠

La negación aparece en las matemáticas de todos los días mucho más de lo que parece, aunque casi
siempre disfrazada. El caso más común es `x ≠ y` (se escribe con `\ne`), que no es un concepto
nuevo: es exactamente `¬(x = y)`.

```savedLean
example (x y : ℝ) : (x ≠ y) = ¬(x = y) := by rfl
```

Y como una negación no es más que una implicación, para demostrar `x ≠ y` empezamos con `intro`
igual que siempre: suponemos `x = y` y buscamos el absurdo.

Con `≠` podemos enunciar la inyectividad como la decimos en voz alta: una función es inyectiva
cuando puntos distintos tienen imágenes distintas.

::::ejercicio
Si `f` es inyectiva y `x` e `y` son distintos, entonces `f x` y `f y` son distintos.

```savedLean
example (hf : inyectiva f) (x y : ℝ) (hxy : x ≠ y) :
    f x ≠ f y := by sorry
```

:::demostracion
```savedLean
example (hf : inyectiva f) (x y : ℝ) (hxy : x ≠ y) :
    f x ≠ f y := by
  intro h
  apply hf at h
  apply hxy at h
  exact h
```

Fíjate en que no ha hecho falta ningún `unfold`: la tesis `f x ≠ f y` es una implicación, así que
`intro h` nos deja `h : f x = f y` con tesis `False`. La inyectividad convierte esa `h` en
`x = y`, y `hxy` la convierte en `False`, que es justo lo que queríamos.
:::
::::



# Si y solo si

Si `P : Prop` y `Q : Prop`, entonces `P ↔ Q : Prop` es la proposición que afirma que `P` y `Q`
son equivalentes. El símbolo se escribe con `\iff`.

```savedLean (name := checkSii)
#check P ↔ Q
```
```leanOutput checkSii
P ↔ Q : Prop
```

Decir que `P` y `Q` son equivalentes es decir dos cosas: que `P` implica `Q` y que `Q` implica
`P`. Una demostración de `P ↔ Q` guarda justo esas dos implicaciones: `(P → Q) ∧ (Q → P)`.

Por tanto, no necesitamos ninguna táctica nueva, sino que utilizamos las de la conjunción: en la tesis usaremos `constructor` y en una hipótesis las proyecciones u `obtain`, aunque las proyecciones tienen otros nombres, como veremos a continuación.

## La doble implicación en la tesis

Como `P ↔ Q` es una conjunción de dos implicaciones, `constructor` la parte en esos dos trozos:
primero la ida y después la vuelta.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ P ↔ Q`
  * {tac}`constructor`
  * primera tesis: `⊢ P → Q`

    segunda tesis: `⊢ Q → P`
:::

:::ejemplo
Propiedad reflexiva: toda proposición es equivalente a sí misma.

```savedLean
example : P ↔ P := by
  constructor
  · intro hP
    exact hP
  · intro hP
    exact hP
```
:::

Ese último ejemplo se puede abreviar. Cuando vimos `rfl` lo usamos con la igualdad, pero en
también funciona para `P ↔ P` (y,
en general, para cualquier relación reflexiva, como `x ≤ x`).

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ P ∼ P`, con `∼` una relación de equivalencia
  * {tac}`rfl`
  * No goals
:::

```savedLean
example : P ↔ P := by rfl
```

::::ejercicio
Una función es biyectiva si y solo si es inyectiva y sobreyectiva.

```savedLean
example :
    biyectiva f ↔ inyectiva f ∧ sobreyectiva f := by sorry
```

:::demostracion
Con `constructor`:

```savedLean
example : biyectiva f ↔ inyectiva f ∧ sobreyectiva f := by
  constructor
  · intro h
    exact h
  · intro h
    exact h
```

Con `rfl`: las dos proposiciones son iguales por definición, así que también vale.

```savedLean
example :
    biyectiva f ↔ inyectiva f ∧ sobreyectiva f := by rfl
```
:::
::::

## La doble implicación en una hipótesis

Aquí tampoco hay nada nuevo. Si `h : P ↔ Q`, las dos mitades se recogen con proyecciones, igual
que en una conjunción; lo único que cambia es cómo se llaman: `h.mp : P → Q` (la ida, por
_modus ponens_) y `h.mpr : Q → P` (la vuelta). También podemos partir `h` con `obtain`.

Esos nombres no son arbitrarios: son los que tienen las dos piezas de `Iff` en su definición, y
podemos verlo con {kw}`#print`.

```savedLean (name := printIff)
#print Iff
```
```leanOutput printIff
structure Iff (a b : Prop) : Prop
number of parameters: 2
fields:
  Iff.mp : a → b
  Iff.mpr : b → a
constructor:
  Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b
```

Aquí sí sale bastante más de lo que necesitamos. Lo que nos interesa está bajo `fields`: una
demostración de `P ↔ Q` guarda dentro una pieza `mp : P → Q` y otra `mpr : Q → P`.

:::table +header
*
  * Antes
  * Proyección
  * Después
*
  * `h : P ↔ Q`
  * `h.mp`
  * `h.mp : P → Q`
*
  * `h : P ↔ Q`
  * `h.mpr`
  * `h.mpr : Q → P`
:::

:::ejemplo
Si `P ↔ Q` y `P`, entonces `Q`.

```savedLean
example (h : P ↔ Q) (hP : P) : Q := by
  exact h.mp hP
```
:::

:::ejemplo
Si `P ↔ Q` y `Q`, entonces `P`.

```savedLean
example (h : P ↔ Q) (hQ : Q) : P := by
  apply h.mpr at hQ
  exact hQ
```
:::


::::ejercicio
Si `P ↔ Q` y `P` no es cierta, entonces `Q` tampoco lo es.

```savedLean
example (h : P ↔ Q) (hnP : ¬P) : ¬Q := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (h : P ↔ Q) (hnP : ¬P) : ¬Q := by
  intro hQ
  apply h.mpr at hQ
  apply hnP at hQ
  exact hQ
```

Aplicando la implicación como función:

```savedLean
example (h : P ↔ Q) (hnP : ¬P) : ¬Q := by
  intro hQ
  exact hnP (h.mpr hQ)
```
:::
::::

::::ejercicio
Si `f` es biyectiva si y solo si `g` lo es, y se tiene que `f` es biyectiva, entonces `g` es
sobreyectiva.

```savedLean
example (h : biyectiva f ↔ biyectiva g) (hf : biyectiva f) :
    sobreyectiva g := by sorry
```

:::demostracion
Con `apply ... at ...`:

```savedLean
example (h : biyectiva f ↔ biyectiva g) (hf : biyectiva f) :
    sobreyectiva g := by
  apply h.mp at hf
  exact hf.right
```

Aplicando la implicación como función:

```savedLean
example (h : biyectiva f ↔ biyectiva g) (hf : biyectiva f) :
    sobreyectiva g := by
  exact (h.mp hf).right
```
:::
::::

::::ejercicio
Con la misma hipótesis `h`, si `g` es biyectiva entonces `f` es inyectiva.

```savedLean
example (h : biyectiva f ↔ biyectiva g) (hg : biyectiva g) :
    inyectiva f := by sorry
```

:::demostracion
```savedLean
example (h : biyectiva f ↔ biyectiva g) (hg : biyectiva g) :
    inyectiva f := by
  obtain ⟨h1, h2⟩ := h
  apply h2 at hg
  exact hg.left
```
:::
::::

# Cuantificador universal

Si `X` es un tipo (por ejemplo `ℝ`) y para cada `x : X` tenemos una proposición `P x`, entonces
`∀ x : X, P x : Prop` es la proposición que afirma que todas ellas son ciertas a la vez. El
símbolo se escribe con `\forall`.

```savedLean (name := checkForall)
#check ∀ x : ℝ, x ≤ x
```
```leanOutput checkForall
∀ (x : ℝ), x ≤ x : Prop
```

Lo importante es qué es una demostración de esa proposición: una función. Recibe un `x` y
devuelve una demostración de `P x`, igual que una demostración de `P → Q` recibe una
demostración de `P` y devuelve una de `Q`.

De hecho la implicación es un caso particular del cuantificador universal: el caso en el que la
conclusión no depende del dato que recibimos. Para Lean, `P → Q` es literalmente
`∀ _ : P, Q`, y podemos comprobarlo con `rfl`.

```savedLean
example : (P → Q) = (∀ _ : P, Q) := by rfl
```

Por eso no hay tácticas nuevas que aprender para la tesis: las que ya conocemos para la
implicación funcionan igual.

## El cuantificador en la tesis

Para demostrar que algo se cumple para todo `x`, tomamos un `x` cualquiera y lo demostramos para
él. Eso es exactamente `intro`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `⊢ ∀ x : X, P x`
  * {tac}`intro` `x`
  * `x : X`

    `⊢ P x`
:::

:::ejemplo
Toda función biyectiva es inyectiva.

```savedLean
example : ∀ f : ℝ → ℝ, biyectiva f → inyectiva f := by
  intro f hf
  exact hf.left
```
:::

Fíjate en que el mismo `intro` sirve para las dos cosas: primero introduce la función `f` del
cuantificador y después la hipótesis `hf` de la implicación.

:::ejemplo
Si `f` es inyectiva, entonces dos puntos con la misma imagen son iguales.

```savedLean
example (hf : inyectiva f) :
    ∀ x y : ℝ, f x = f y → x = y := by
  intro x y h
  apply hf at h
  exact h
```
:::

Este último ejemplo no dice nada nuevo: la tesis es, letra por letra, la definición de
`inyectiva f`. Por eso `exact hf` también lo cierra de un golpe.

## El cuantificador en una hipótesis

Si tenemos `h : ∀ x : X, P x` es porque sabemos algo sobre todos los `x`, y normalmente lo que
queremos es usarlo sobre un `x` concreto. Ya hemos visto una forma de hacerlo, `apply h at ...`,
y aquí va la otra.

::::nuevaTactica (tactica := "specialize")
La táctica `specialize h x₀` sustituye la hipótesis general `h` por su caso particular en `x₀`.
Funciona igual con una implicación, porque una implicación es un cuantificador: si `h : P → Q` y
`hP : P`, entonces `specialize h hP` deja `h : Q`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : ∀ x : X, P x`

    `x₀ : X`
  * {tac}`specialize` `h x₀`
  * `h : P x₀`
*
  * `h : P → Q`

    `hP : P`
  * {tac}`specialize` `h hP`
  * `h : Q`
:::
::::

:::ejemplo
Si `f` es inyectiva y `f x = f y`, entonces `x = y`.

```savedLean
example (x y : ℝ) (hf : inyectiva f) (h : f x = f y) :
    x = y := by
  specialize hf x y
  specialize hf h
  exact hf
```
:::

Los dos pasos se pueden dar de una vez, escribiendo todos los argumentos seguidos.

::::ejercicio
Si `f` es creciente y `x ≤ y`, entonces `f x ≤ f y`.

```savedLean
example (x y : ℝ) (hf : creciente f) (h : x ≤ y) :
    f x ≤ f y := by sorry
```

:::demostracion
Con `specialize`:

```savedLean
example (x y : ℝ) (hf : creciente f) (h : x ≤ y) :
    f x ≤ f y := by
  specialize hf x y h
  exact hf
```

Con `apply ... at ...`:

```savedLean
example (x y : ℝ) (hf : creciente f) (h : x ≤ y) :
    f x ≤ f y := by
  apply hf at h
  exact h
```

Aplicando `hf` como función:

```savedLean
example (x y : ℝ) (hf : creciente f) (h : x ≤ y) :
    f x ≤ f y := by
  exact hf x y h
```
:::
::::

Hay que tener una precaución: `specialize` no guarda copia, sustituye la hipótesis general por el
caso particular. Si vamos a necesitar `h` para varios valores, conviene usarla
con `apply ... at ...` en lugar de especializarla.

## Ejercicio extra

::::ejercicio
No todas las proposiciones son ciertas.

```savedLean
example : ¬(∀ A : Prop, A) := by sorry
```

:::demostracion
```savedLean
example : ¬(∀ A : Prop, A) := by
  intro h
  specialize h False
  exact h
```

La tesis es una negación, así que empezamos con `intro`. La hipótesis `h` dice que toda
proposición es cierta; en particular lo es `False`.
:::
::::



# Cuantificador existencial

Si `X` es un tipo y para cada `x : X` tenemos una proposición `P x`, entonces `∃ x : X, P x` es
la proposición que afirma que al menos una de ellas es cierta. El símbolo se escribe con
`\exists`.

```savedLean (name := checkExists)
#check ∃ n : ℕ, n > 0
```
```leanOutput checkExists
∃ n, n > 0 : Prop
```

Si una demostración de `∀ x : X, P x` era una función, una demostración de `∃ x : X, P x` es un
par: un `x₀` concreto, que llamamos el _testigo_, y una demostración de `P x₀`. Como la conjunción, en una hipótesis se descompone con `obtain` (sin embargo, no tiene proyecciones: `h.1` o `h.left` dan error).

## El cuantificador existencial en la tesis

Demostrar que existe algo es, casi siempre, enseñarlo. La táctica que lo hace es `use`.

::::nuevaTactica (tactica := "use")
Cuando la tesis es `∃ x : X, P x`, la táctica `use x₀` se compromete con el testigo `x₀` y deja
como única tesis `P x₀`, que es lo que hay que comprobar de ese candidato concreto.

Además, después de poner el testigo, Lean intenta cerrar lo que queda por su cuenta si es algo
evidente (por ejemplo, si ya lo tenemos entre las hipótesis). Cuando lo consigue, la
demostración termina ahí mismo.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `x₀ : X`

    `⊢ ∃ x : X, P x`
  * {tac}`use` `x₀`
  * `⊢ P x₀`
:::
::::

:::ejemplo
Existe un número natural cuyo doble es `6`.

```savedLean
example : ∃ n : ℕ, 2 * n = 6 := by
  use 3
```
:::

No ha hecho falta añadir nada después de `use`: la tesis que quedaba era `2 * 3 = 6`, y Lean la
ha cerrado solo.

Lo que acabamos de demostrar es que `6` es par. La paridad es un ejemplo de definición con un
existencial: un número es par cuando es el doble de algún otro.

:::definicion "número par"
```savedLean
def esPar (n : ℕ) : Prop := ∃ m, n = 2 * m
```
:::

:::ejemplo
El `2` es par.

```savedLean
example : esPar 2 := by
  unfold esPar
  use 1
```
:::

Igual que antes, Lean cierra solo la tesis que queda, `2 = 2 * 1`. Tampoco hace falta el
`unfold`, que hemos puesto únicamente para ver nosotros la definición.

::::ejercicio
El `4` es par.

```savedLean
example : esPar 4 := by sorry
```

:::demostracion
```savedLean
example : esPar 4 := by
  use 2
```
:::
::::

## El cuantificador existencial en una hipótesis

Si tenemos `h : ∃ x : X, P x` sabemos que hay un testigo, aunque no sepamos cuál. Lo que
hacemos es darle un nombre y seguir trabajando con él, exactamente igual que cuando partíamos
una conjunción: con `obtain`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : ∃ x : X, P x`
  * {tac}`obtain` `⟨x₀, h₀⟩ := h`
  * `x₀ : X`

    `h₀ : P x₀`
:::

:::ejemplo
Si `f` es sobreyectiva, entonces todo `y` tiene una preimagen.

```savedLean
example (y : ℝ) (hf : sobreyectiva f) : ∃ x, f x = y := by
  specialize hf y
  obtain ⟨x, hx⟩ := hf
  use x
```
:::

La demostración anterior da un rodeo a propósito, para ver las dos tácticas juntas: después del
`specialize`, la hipótesis `hf` ya era exactamente la tesis, así que `exact hf` habría bastado.
El rodeo consiste en sacar el testigo `x` de la hipótesis y volver a ofrecerlo como testigo de
la tesis.

::::ejercicio
La identidad es sobreyectiva.

```savedLean
example : sobreyectiva (fun x ↦ x) := by sorry
```

:::demostracion
```savedLean
example : sobreyectiva (fun x ↦ x) := by
  intro y
  use y
```
:::
::::

::::ejercicio
Si la composición `g ∘ f` es sobreyectiva, entonces `g` es sobreyectiva.

```savedLean
example (h : sobreyectiva (g ∘ f)) :
    sobreyectiva g := by sorry
```

:::demostracion
```savedLean
example (h : sobreyectiva (g ∘ f)) :
    sobreyectiva g := by
  intro z
  specialize h z
  obtain ⟨x, hx⟩ := h
  use f x
  exact hx
```
:::
::::

```savedLean -show
end Clase2
```


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

#doc (Manual) "Lean Theorem Prover" =>

%%%
%%%

```savedImport
import Mathlib.Tactic.ApplyAt
import Mathlib.Data.Real.Basic
```
```savedComment
# Clase 1: primeros pasos en Lean

Teoría de tipos, proposiciones y las tácticas `intro`, `exact`, `apply ... at ...` y `unfold`.
```
```savedLean -show
namespace Clase1
```

Vamos a empezar a escribir Lean cuanto antes, para desmitificar el asunto. Abre un
archivo en tu proyecto, o directamente [Lean 4 Web](https://live.lean-lang.org), y ve copiando lo que salga.

# Teoría de tipos

Lean es un sistema basado en *teoría de tipos* en lugar de en teoría de conjuntos. Suena a un
cambio enorme, pero por ahora lo único que hace falta saber es esto:

1. Todos los objetos son *términos*.
2. Todo término tiene asignado un *tipo*.
3. Escribir `t : T` quiere decir que `t` es un término de tipo `T`.

Todo lo que escribamos a partir de ahora van a ser declaraciones de esta forma. Lo único que
Lean sabe hacer de verdad es *typechecking*: comprobar si un término tiene un cierto tipo.

A veces también es capaz de decirte el tipo de un término dado, que es lo más sencillo, así que
empezamos por ahí. Para pedírselo usamos {kw}`#check`:

```savedLean (name := check3)
#check 3
```
```leanOutput check3
3 : ℕ
```

A diferencia de otros lenguajes, Lean no compila el programa entero de golpe: tiene una ventana a
la derecha, el *InfoView*, que te dice el resultado de la línea en la que tienes el cursor ahora
mismo. Ahí es donde aparece la respuesta.

Una nota: `ℕ` es como Mathlib escribe `Nat`, el tipo de los números naturales. Verás las dos
formas.

Podemos preguntar por otras cosas. Una tupla:

```savedLean (name := checkTupla)
#check (3, 5)
```
```leanOutput checkTupla
(3, 5) : ℕ × ℕ
```

O una función. Vamos a declarar una variable que sea una función de los naturales en los
naturales:

```savedLean -show
section
```
```savedLean (name := checkF)
variable (f : Nat → Nat)

#check f
```
```leanOutput checkF
f : ℕ → ℕ
```

La flechita se escribe con `\to` y un espacio. Casi todos los símbolos raros de Lean se escriben
así, con una barra invertida y un nombre.

También podemos concatenar términos para formar otros:

```savedLean (name := checkF3)
#check f 3
```
```leanOutput checkF3
f 3 : ℕ
```

Esto es `f(3)`, y por tanto es un natural. Fíjate en que en teoría de tipos escribimos `f x` y no
`f (x)`.

```savedLean -show
end
```

Y como te hemos dicho que absolutamente todo son términos, y es cierto, también podemos preguntar
por el tipo de un tipo:

```savedLean (name := checkNat)
#check Nat
```
```leanOutput checkNat
Nat : Type
```

`Type` es un tipo especial: el tipo de los tipos.

Hasta aquí la notación `t : T`, y se entiende: `3 : ℕ`, `(3, 5) : ℕ × ℕ`, `f 3 : ℕ`,
`Nat : Type`.

Veamos la siguiente notación, que es

```
example : T := t
```

y que significa "te voy a dar un objeto de tipo `T`; en efecto, aquí tienes `t`". Por ejemplo:

```savedLean
example : Nat := 3
```

Aquí ya no le estamos pidiendo a Lean que nos diga el tipo de `3`, sino que estamos prometiendo
un término de tipo `Nat` y pidiéndole que compruebe que lo es. Si nos equivocamos, protesta:

```lean +error (name := errorTupla)
example : Nat := (3, 5)
```
```leanOutput errorTupla
Type mismatch
  (3, 5)
has type
  ?m.3 × ?m.5
but is expected to have type
  ℕ
```

Es decir, no le hemos dado un término correcto para el tipo que le habíamos prometido. (Los `?m`
son tipos que Lean todavía no ha decidido: sabe que `(3, 5)` es un par, pero no de qué clase de
números.) En este sentido decimos que Lean es un *verificador*: se da cuenta de si cumplimos lo
que prometemos.

Hay una excepción. A veces queremos señalarle a Lean que todavía no sabemos construir el término
que hemos prometido, y para eso está `sorry`:

```
example : Nat := sorry
```

Lean lo permite, aunque claramente no es correcto, y nos avisa con un warning. Es muy útil
mientras estamos construyendo una demostración a trozos.

También podemos darle un término de tipo `Nat → Nat`:

```savedLean
example : Nat → Nat := fun n ↦ n + 1
```

La notación `fun n ↦ n + 1` (la flecha se escribe con `\mapsto`) denota la función que toma un
natural `n` y devuelve `n + 1`.

Esta función es la función "sumar 1", o "sucesor". Estaría bien no tener que escribir
`fun n ↦ n + 1` cada vez y poder llamarla por su nombre; es decir, queremos poder nombrar
nuestros objetos matemáticos. Para eso está `def`, que se usa igual que `example` pero además le
da un nombre al objeto:

```savedLean
def sucesor : Nat → Nat := fun n ↦ n + 1
```

# Proposiciones

Ya tenemos definiciones de objetos matemáticos. Nos falta una cosa: teoremas.

Como venimos diciendo, aquí todo son términos con un tipo. Entonces, ¿un resultado matemático es
un término con un tipo? Obviamente.

Un resultado matemático es una *proposición*, es decir, una afirmación sobre nuestros objetos
matemáticos que tiene un valor de verdad, verdadero o falso. Por ejemplo, `3 = 3` es una
proposición, y `2 = 3` también lo es. En Lean las proposiciones tienen el tipo `Prop`:

```savedLean (name := checkIgual)
#check 3 = 3
```
```leanOutput checkIgual
3 = 3 : Prop
```
```savedLean (name := checkDistinto)
#check 2 = 3
```
```leanOutput checkDistinto
2 = 3 : Prop
```
```savedLean (name := checkProp)
#check Prop
```
```leanOutput checkProp
Prop : Type
```

Y aquí viene la parte graciosa: en Lean un término de tipo `Prop` resulta que es a su vez un
tipo. Es decir, `3 = 3` es un tipo.

¿Y cuáles son los términos de tipo `3 = 3`? Aquí hay que dar un pequeño salto de fe: los términos
de tipo `3 = 3` son las demostraciones de que, en efecto, `3 = 3`. Por tanto, para demostrar
`3 = 3` nos basta con construir un término de tipo `3 = 3`.

Lo que está pasando es que hacemos una correspondencia entre

* teoremas y tipos, y
* demostraciones de un teorema y términos de ese tipo.

Esto se conoce como *correspondencia de Curry-Howard* y queda completamente fuera del contenido
de este curso. Si tienes curiosidad, un buen punto de partida es el artículo
[_Propositions as Types_](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf)
de Philip Wadler; si no, tendrás que creernos.

Escribamos entonces nuestro teorema. Podemos usar las palabras clave `lemma` y `theorem`, y la
diferencia entre ambas es puramente estética. Como este es un resultado importante, le ponemos
`theorem`:

```
theorem MiTeorema : 3 = 3 := sorry
```

Lo que iría en lugar de `sorry` es la demostración. Pero este teorema es muy difícil, así que
vamos a tener que empezar por otros más fáciles.

# Demostraciones

## ¿Qué es una demostración?

Antes de seguir, una pregunta: ¿qué es una demostración?

Todas las respuestas a esta pregunta son válidas, porque la pregunta es inherentemente subjetiva.
Una que nos han dado es "un argumento que valida un resultado a partir de resultados previos", y
otra "una explicación inquebrantable de un hecho". Son buenas respuestas, pero también
increíblemente ambiguas: "validar" e "inquebrantable" son cosas difíciles de medir. En la
práctica la medida que se suele tomar es "esta demostración me convence", o incluso "con esta
demostración mi profesor me aprueba", y entonces lo inquebrantable pasa a ser lo que decida el
profesor.

En Lean esa subjetividad no existe. Cuando demostramos algo en Lean estamos *construyendo* una
demostración, de manera que al final o bien es válida o bien no lo es, de forma determinista y
para todo el mundo igual.

Hay otra forma de mirar una demostración que nos va a resultar muy útil a partir de ahora:

:::observacion
Una demostración de un hecho es una secuencia de pasos que empieza en un conjunto de hipótesis y
termina en el teorema, de forma que cada paso se sustenta en una regla lógica.
:::

Por ejemplo, si mis hipótesis son "3 es un número natural" y "todo número natural es positivo",
entonces puedo concluir "3 es positivo". Esto es *modus ponens*. Si has dado lógica proposicional
tienes aquí una pequeña ventaja.

Esta forma de entender una demostración no se ha inventado para Lean: es como se han razonado
siempre las matemáticas. Cuando escribes una demostración en papel también partes de unas
hipótesis y avanzas paso a paso, y cada paso lo justificas con una regla. Tanto es así que hay
toda una rama de las matemáticas, la lógica matemática, que se dedica a estudiar las
demostraciones entendidas de esta forma, como objetos matemáticos en sí mismos. Lo que cambia con
Lean es el nivel de detalle: en papel muchos de esos pasos se quedan sin decir, porque confiamos
en que el lector sepa completarlos, y aquí hay que escribirlos todos.

## Tácticas

Hemos dicho que para demostrar algo hay que construir un término del tipo del resultado. Eso se
puede hacer directamente, escribiendo el término a mano, pero es la forma menos intuitiva de
trabajar con Lean.

Lean nos da unas herramientas que se llaman *tácticas* y que son, digamos, las reglas lógicas de las
que acabamos de hablar: los pasos que podemos dar dentro de una demostración. Son programas que ha
escrito gente muy lista para facilitarnos la vida, y lo que hacen es acercar el lenguaje de términos
de Lean a nuestra forma de hablar, para que no tengamos que escribirlo todo.

Más adelante aprenderemos a escribir términos directamente. Por ahora nos centramos en demostrar
con tácticas.

Para entrar en *modo táctico* usamos la palabra clave `by`:

```savedLean -show
variable (P : Prop)
```

```lean
example : P → P := by
  sorry
```

y la demostración va indentada debajo. La indentación es importante: es lo que le dice a Lean
dónde empieza y dónde acaba la demostración.

## Primeras demostraciones

Vamos con la primera de verdad. Sea `P` una proposición cualquiera, de la que no sabemos si es
verdadera o falsa:

```lean
variable (P : Prop)
```

```savedLean -show
variable (Q R : Prop)
```

y demostremos que `P` implica `P`.

### El InfoView

Si escribimos el esqueleto de la demostración y ponemos el cursor justo antes del `sorry`,
empieza a aparecer información en el InfoView, la ventana de la derecha. Eso que aparece es el
*estado de la demostración*, y tiene dos partes:

```
P : Prop
⊢ P → P
```

Por encima está el *contexto*, el conjunto de nuestras hipótesis, que de momento solo dice que
`P`, `Q` y `R` son proposiciones. Por debajo de la raya `⊢` está la *tesis*: lo que nos queda
por demostrar. Lean la llama _goal_, y por eso, cuando ya no queda nada por demostrar, el InfoView
dice *No goals*.

Recuerda la lectura de tipos de antes: si `P : Prop` es una proposición, un término `h : P` es
exactamente una demostración de `P`. Por eso todas las hipótesis se escriben igual, con un
nombre, dos puntos y la proposición que demuestran.

La meta del juego es llegar a *No goals*, es decir, a que no quede ninguna tesis por demostrar.
Cada táctica que escribimos cambia las hipótesis, la tesis, o las dos.

### intro y exact

¿Qué hacemos normalmente cuando queremos demostrar que algo implica otra cosa, por ejemplo `A`
implica `B`? Lo primero es decir: supongamos que se tiene `A`. Nos gustaría escribir

```
example : P → P := by
  Supongamos que P
  sorry
```

pero obviamente eso no funciona. Hay una táctica exactamente para esto y se llama `intro`.

::::nuevaTactica (tactica := "intro")
Si la tesis es una implicación `P → Q`, podemos suponer `P` y pasar a demostrar `Q`. La táctica
`intro hP` hace precisamente eso: mete la hipótesis `P` en el contexto con el nombre `hP` y deja
como nueva tesis `Q`.

Se pueden introducir varias hipótesis de golpe escribiendo `intro h1 h2 h3`, que es lo mismo que
aplicar `intro` tres veces seguidas.

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
:::
::::

Al escribir `intro h` pasan dos cosas. La primera es que aparece `h : P` en el contexto; es
decir, `h` es una demostración de que `P` es cierto. La segunda es que la tesis, que antes era
`P → P`, ahora es solo `P`, porque cuando decimos "supongamos `P`" lo que queda por demostrar es
lo que había a la derecha de la flecha.

Así que ahora tenemos: sea `P` una proposición tal que `P` es cierta, por `h`. Demuestra que `P`
es cierta. Es trivial. Nos gustaría escribir "es cierto por `h`", y para eso está `exact`.

::::nuevaTactica (tactica := "exact")
Si entre las hipótesis tenemos `h : P` y la tesis es exactamente `P`, la demostración ya está
terminada: basta con señalar esa hipótesis. Eso es lo que hace `exact h`, que cierra la tesis
actual.

Es importante que `h` demuestre la tesis _exactamente_; si no encaja, Lean nos avisará.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : P`

    `⊢ P`
  * {tac}`exact` `h`
  * No goals
:::
::::

Y con eso ya tenemos nuestra primera demostración.

:::ejemplo
Si `P` es una proposición, entonces `P` implica `P`.

```savedLean
example : P → P := by
  intro h
  exact h
```
:::

A partir de aquí, buena parte del curso es esto: mirar qué tenemos, mirar qué queremos y elegir
la táctica que acerca lo uno a lo otro.

::::ejercicio
Si `P` es cierta, entonces cualquier otra proposición `Q` implica `P`. Dicho de otro modo: de `P`
se deduce que `Q → P`.

```savedLean
example : P → Q → P := by sorry
```

:::demostracion
```savedLean
example : P → Q → P := by
  intro h hQ
  exact h
```

Observa que hemos introducido dos hipótesis y solo hemos usado una. Esto es normal: tener
información de más no estorba.
:::
::::

::::ejercicio
Si disponemos de demostraciones de `P`, de `Q` y de `R`, en particular tenemos una demostración
de `Q`.

```savedLean
example : P → Q → R → Q := by sorry
```

:::demostracion
```savedLean
example : P → Q → R → Q := by
  intro hP hQ hR
  exact hQ
```
:::
::::

::::ejercicio
La proposición `P → Q` se implica a sí misma.

```savedLean
example : (P → Q) → (P → Q) := by sorry
```

:::demostracion
```savedLean
example : (P → Q) → (P → Q) := by
  intro hpq
  exact hpq
```

Aunque `P → Q` sea una implicación, aquí funciona como una proposición cualquiera: `intro` la
mete en el contexto y `exact` la devuelve. Las tácticas miran la forma de la tesis, no su
significado.
:::
::::

### apply at

La regla de inferencia más básica de la lógica dice que si sabemos que `P → Q` y sabemos que `P`,
entonces sabemos que `Q`. Es el modus ponens de antes. En Lean se puede escribir de varias
maneras; nosotros vamos a usar una que resulta muy cómoda porque razona hacia delante, igual que
en una demostración a mano.

::::nuevaTactica (tactica := "apply ... at ...")
Si tenemos `h : P → Q` y también `hP : P`, la táctica `apply h at hP` aplica la implicación a la
hipótesis y _transforma_ `hP` en una demostración de `Q`. La hipótesis cambia de contenido pero
conserva su nombre, lo cual es muy práctico para encadenar varios pasos.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : P → Q`

    `hP : P`
  * {tac}`apply` `h` {tac}`at` `hP`
  * `h : P → Q`

    `hP : Q`
:::
::::

:::ejemplo
Modus ponens: si `P` implica `Q` y `P` es cierta, entonces `Q` es cierta.

```savedLean
example : (P → Q) → P → Q := by
  intro hPQ hP
  apply hPQ at hP
  exact hP
```
:::

::::ejercicio
Transitividad de la implicación: si `P` implica `Q` y `Q` implica `R`, entonces `P` implica `R`.

```savedLean
example : (P → Q) → (Q → R) → P → R := by sorry
```

:::demostracion
```savedLean
example : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP
  apply hPQ at hP
  apply hQR at hP
  exact hP
```

Fíjate en cómo `hP` va viajando: empieza siendo una demostración de `P`, después de `Q` y
finalmente de `R`. Es exactamente la cadena de razonamientos que haríamos en un papel.
:::
::::

::::ejercicio
Si de `P` se deduce que `Q` implica `R`, entonces de `P` y `Q` juntas se deduce `R`.

```savedLean
example : (P → Q → R) → P → Q → R := by sorry
```

:::demostracion
```savedLean
example : (P → Q → R) → P → Q → R := by
  intro h hP hQ
  apply h at hP
  apply hP at hQ
  exact hQ
```

Aquí ocurre algo curioso: al aplicar `h` a `hP` obtenemos `hP : Q → R`, es decir, una hipótesis
que a su vez es una implicación. Nada nos impide volver a usar `apply ... at ...` con ella.
:::
::::

### La implicación como función

Existe otra manera de hacer este tipo de razonamientos. Habrás notado que la implicación
`P → Q` se escribe con el mismo símbolo que las funciones `f : ℕ → ℕ`.

Esto es porque, en Lean, interpretamos una demostración de `P → Q`, es decir, un término
`h : P → Q`, como una función que recibe una demostración de `P` y devuelve una demostración de `Q`.

De la misma forma que si `f : ℕ → ℕ` y `3 : ℕ` entonces `f 3 : ℕ`, si `h : P → Q` y `hP : P`
entonces `h hP : Q`. Es decir, `h` se ve como una función que puede
tomar términos como `hP` que sean de tipo `P`, y `h hP` es esa función aplicada a `hP`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : P → Q`

    `hP : P`

    `⊢ Q`
  * {tac}`exact` `h hP`
  * No goals
:::

Así que, en vez de transformar la hipótesis con `apply ... at ...`, podemos escribir directamente
la demostración que queremos y dársela a `exact`.

:::ejemplo
Modus ponens de nuevo.

```savedLean
example : (P → Q) → P → Q := by
  intro hPQ hP
  exact hPQ hP
```
:::

::::ejercicio
La transitividad de nuevo.

```savedLean
example : (P → Q) → (Q → R) → P → R := by sorry
```

:::demostracion
```savedLean
example : (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP
  exact hQR (hPQ hP)
```

Como `hPQ : P → Q` y `hP : P`, entonces `hPQ hP : Q`. Además, `hQR : Q → R`, luego
`hQR (hPQ hP) : R`.
:::
::::

### Aplicación en un contexto real

Todo lo anterior vale para proposiciones abstractas, pero lo interesante es usarlo con
matemáticas de verdad. Vamos a trabajar con funciones reales y a darle nombre a una propiedad
conocida.

```savedLean
variable (f g : ℝ → ℝ)
```

:::definicion "función inyectiva"
```savedLean
def inyectiva : Prop := ∀ x y, f x = f y → x = y
```
:::

La palabra clave `def` introduce una definición, igual que antes con `sucesor`: a partir de ahora
`inyectiva f` es una proposición, la que afirma que `f` es inyectiva. Lean la considera igual
_por definición_ a `∀ x y, f x = f y → x = y`, es decir, escribir una cosa o la otra es para él
exactamente lo mismo.

Para nosotros no lo es. Cuando en el contexto aparece `hf : inyectiva f` no vemos qué hay dentro,
y al principio eso despista bastante.

::::nuevaTactica (tactica := "unfold")
La táctica `unfold nombre at h` sustituye una definición por aquello que abrevia dentro de la
hipótesis `h`. Sirve para ver qué hay realmente detrás de un nombre.

Para hacerlo en la tesis basta con escribir `unfold nombre`, y para hacerlo en todas partes a la
vez, `unfold nombre at *`.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `hf : inyectiva f`
  * {tac}`unfold` `inyectiva` {tac}`at` `hf`
  * `hf : ∀ x y, f x = f y → x = y`
:::
::::

Vamos a estrenarla comprobando que la definición dice lo que esperamos que diga.

:::ejemplo
Si `f` es inyectiva, entonces para todos `x` e `y` se cumple que `f x = f y` implica `x = y`.

```savedLean
example (hf : inyectiva f) :
    ∀ x y, f x = f y → x = y := by
  -- no hace falta, pero nos ayuda a ver qué pasa
  unfold inyectiva at hf
  exact hf
```
:::

Fíjate en lo que ocurre: después del `unfold`, la hipótesis `hf` y la tesis son literalmente la
misma frase, así que `exact hf` cierra la demostración. Y como Lean ya las consideraba iguales por
definición, la demostración funciona igual si borras la línea del `unfold`. Es una táctica para
nosotros, no para Lean.

Ahora, una vez desplegada, la hipótesis de inyectividad empieza por `∀`, y con eso todavía
no hemos trabajado. Una hipótesis de la forma `∀ x y, f x = f y → x = y` hay que leerla como una
familia entera de implicaciones: una para cada par de valores de `x` e `y`.

La buena noticia es que no hace falta ninguna táctica nueva. `apply ... at ...` funciona
directamente sobre ellas: si `h` empieza por `∀`, Lean mira la hipótesis a la que se lo estamos
aplicando, deduce él solo por qué valores hay que sustituir las variables y aplica la implicación
que corresponde.

:::table +header
*
  * Antes
  * Táctica
  * Después
*
  * `h : ∀ x y, f x = f y → x = y`

    `hxy : f x = f y`
  * {tac}`apply` `h` {tac}`at` `hxy`
  * `hxy : x = y`
:::

:::ejemplo
Si `f` es inyectiva y `f x = f y`, entonces `x = y`.

```savedLean
example (hf : inyectiva f) (x y : ℝ)
    (h : f x = f y) : x = y := by
  unfold inyectiva at hf
  apply hf at h
  exact h
```
:::

Aquí `hf` vale para cualquier par de reales y nosotros la estamos usando con los `x` e `y`
concretos del enunciado. No se lo hemos dicho en ningún sitio: Lean lo ha deducido mirando
`h : f x = f y`.

Con las dos piezas en la mano ya podemos ir a por el resultado de verdad.

:::proposicion
Sean `f` y `g` dos funciones reales inyectivas. Entonces la composición `g ∘ f` es inyectiva.
:::

Antes de escribir nada en Lean, escribamos la demostración como "una secuencia de pasos lógicos",
suponiendo que nuestro profesor es el más estricto del mundo y hay que escribirlos todos. A la
derecha ponemos la táctica que corresponde a cada paso.

:::table +header
*
  * Paso
  * Táctica
*
  * Desplegamos la definición en todas partes: en `hf`, en `hg` y en la tesis.
  * {tac}`unfold` `inyectiva` {tac}`at` `*`
*
  * Sean `x` e `y` cualesquiera tales que `(g ∘ f) x = (g ∘ f) y`.
  * {tac}`intro` `x y h`
*
  * Eso es lo mismo que decir `g (f x) = g (f y)`.
  * {tac}`unfold` `Function.comp` {tac}`at` `h`
*
  * Como `g` es inyectiva, de `g (f x) = g (f y)` obtenemos `f x = f y`.
  * {tac}`apply` `hg` {tac}`at` `h`
*
  * Como `f` es inyectiva, de `f x = f y` obtenemos `x = y`.
  * {tac}`apply` `hf` {tac}`at` `h`
*
  * Queremos `x = y` y tenemos `x = y`.
  * {tac}`exact` `h`
:::

Ahora podemos intentar hacer la demostración en Lean. Fíjate en que en Lean no hay diferencia entre
`(g ∘ f) x` y `g (f x)`, pero, si te lías, puedes utilizar `unfold Function.comp` para cambiar de la
primera a la segunda cuando quieras.

::::ejercicio
La composición de dos funciones inyectivas es inyectiva.

```savedLean
example (hf : inyectiva f) (hg : inyectiva g) :
    inyectiva (g ∘ f) := by sorry
```

:::demostracion
```savedLean
example (hf : inyectiva f) (hg : inyectiva g) :
    inyectiva (g ∘ f) := by
  unfold inyectiva at *
  intro x y h
  unfold Function.comp at h
  apply hg at h
  apply hf at h
  exact h
```
:::
::::

::::ejercicio
La composición de tres funciones inyectivas es inyectiva.

```savedLean
example (h : ℝ → ℝ) (hf : inyectiva f) (hg : inyectiva g)
    (hh : inyectiva h) : inyectiva (h ∘ g ∘ f) := by sorry
```

:::demostracion
```savedLean
example (h : ℝ → ℝ) (hf : inyectiva f) (hg : inyectiva g)
    (hh : inyectiva h) :
    inyectiva (h ∘ g ∘ f) := by
  unfold inyectiva at *
  intro x y hxy
  unfold Function.comp at hxy
  apply hh at hxy
  apply hg at hxy
  apply hf at hxy
  exact hxy
```

El esquema es el mismo: se van quitando funciones de fuera hacia dentro.
:::
::::

Y para comprobar que nada de esto dependía de la inyectividad, repitamos la historia con otra
propiedad.

:::definicion "función creciente"
```savedLean
def creciente : Prop := ∀ x y, x ≤ y → f x ≤ f y
```
:::

::::ejercicio
La composición de dos funciones crecientes es creciente.

Esta vez intenta escribir tú el enunciado en Lean antes de desplegarlo.

:::enunciado
```savedLean
example (hf : creciente f) (hg : creciente g) :
    creciente (g ∘ f) := by sorry
```
:::

:::demostracion
```savedLean
example (hf : creciente f) (hg : creciente g) :
    creciente (g ∘ f) := by
  unfold creciente at *
  intro x y h
  apply hf at h
  apply hg at h
  exact h
```
:::
::::

```savedLean -show
end Clase1
```


import VersoManual
import Apuntes.Meta.Lean
import Apuntes.Meta.NuevaTactica
import Apuntes.Meta.Estilo
import Apuntes.Meta.Teorema

open Verso.Genre Manual

open Verso.Genre.Manual.InlineLean

open Apuntes

set_option pp.rawOnError true

#doc (Manual) "Introducción" =>

%%%
%%%

Bienvenida al curso de Lean de CompuMates. Estos apuntes recogen lo que contamos en clase, con
algo más de calma y algo mejor ordenado. No están pensados para seguirlos en directo, sino para
leerlos después: para repasar lo que se te haya atragantado, copiar código y hacer los ejercicios.

# ¿Qué es Lean?

Lean es un lenguaje de programación funcional, como puede serlo Haskell, y además es un
asistente de demostración.

Conviene hacer una distinción de partida, porque son dos cosas que se confunden mucho. En la
*demostración automática* de teoremas, la máquina busca la demostración por su
cuenta: le das el enunciado y ella intenta encontrar una prueba. En la *demostración asistida* (o
interactiva), la demostración la construyes tú, paso a paso, y la máquina te ayuda un poco por el
camino y comprueba que cada paso es correcto.

Lean es sobre todo un asistente de este segundo tipo: nos da un lenguaje en el que podemos
escribir matemáticas en el ordenador, nos ofrece herramientas que automatizan los pasos más
rutinarios y nos garantiza la corrección de aquello que demostremos. Pero la idea de la
demostración, qué pasos dar y en qué orden, sigue siendo nuestra. Más adelante hablaremos de qué
significa exactamente esa garantía.

# Instalación

Lo más cómodo es trabajar en local, con VS Code.

Para seguir el curso, puedes usar tu propio ordenador o uno del aula. Si utilizas el del aula,
reinícialo en Linux: con Windows no funciona.

Si tu ordenador es Windows puede que te dé algún problema; inténtalo, y si ves que no te funciona
dínoslo.

Para empezar a trabajar con Lean sigue los siguientes pasos:

1. Instala VS Code.
2. Instala la extensión *Lean 4*. La extensión se encarga del resto: descarga por su cuenta la
   versión de Lean que haga falta, así que no tienes que instalar el compilador a mano.
3. Crea un proyecto que use Mathlib. Desde el menú `∀` que aparece arriba a la derecha en VS Code
   puedes crear un proyecto nuevo ya configurado con la librería. Tarda un rato la primera vez,
   porque se descarga Mathlib entera.
4. Crea dentro un archivo, por ejemplo `Prueba.lean`, y ábrelo.

Si no quieres instalar nada, o si la instalación se te complica, puedes usar [*Lean 4 Web*](https://live.lean-lang.org): es un
Lean completo con Mathlib que corre en el navegador. Para los primeros ejemplos sirve
perfectamente.

# Motivación

Antes de entrar en materia, dos preguntas: por qué querríamos un asistente de demostración, y por
qué Lean en particular y no otro.

## ¿Por qué formalizar matemáticas?

Hay tres motivos que nos parecen los más interesantes.

*El cuello de botella de la revisión.* Conforme avanza la investigación, los resultados son cada
vez más especializados. Puede que publiques un artículo sobre tu área y que en esa área haya
cuatro personas capaces de revisarlo con criterio. Si publicas el artículo junto con una
formalización, esa formalización es una garantía de corrección. No una garantía absoluta, porque
siempre se puede haber formalizado un enunciado que no es el que creías, pero sí un indicador para
un revisor de que merece la pena dedicarle tiempo.

*El nivel de detalle.* Los asistentes de demostración son muy exigentes. El grado de detalle que
hay que alcanzar en una formalización no lo has tenido que alcanzar nunca en papel: Lean no te
deja escribir "esto es trivial" ni "la demostración es análoga a la anterior". Si has tenido algún
profesor muy exigente en la carrera, probablemente te hayas dado cuenta de que es con quien mejor
has aprendido a demostrar. Formalizar un resultado te obliga a entenderlo mucho más a fondo.

*La inteligencia artificial.* Un lenguaje en el que se pueden formalizar matemáticas es
tremendamente útil para la IA porque no tiene ambigüedad. Las matemáticas aspiran a ser cada vez más
formales, pero el lenguaje natural con el que las escribimos normalmente sigue siendo ciertamente
ambiguo, lo que permite muchas más trampas. A los modelos se les ha dado siempre mejor programar que
hacer matemáticas, y en buena medida es porque al programar hay algo que comprueba lo que escriben.
Formalizar convierte las matemáticas en algo comprobable de la misma forma.

Un ejemplo reciente: en septiembre de 2026, OpenAI
[anunció](https://openai.com/index/navier-stokes-solution/) que uno de sus modelos había
construido un contraejemplo para las ecuaciones de Navier-Stokes, uno de los problemas del milenio, y lo acompañó de una formalización en Lean. El
resultado todavía está en revisión y ha generado bastante debate, en parte precisamente sobre qué
garantiza y qué no esa formalización.

## ¿Por qué Lean?

Sobre todo, por su comunidad.

La de Lean es la comunidad más grande de entre los asistentes de demostración. Otros que te
pueden sonar son Rocq (antes llamado Coq), Agda o Isabelle. Cada vez hay más matemáticos importantes
dedicándole tiempo y recursos, como por ejemplo el medallista fields Terence Tao.

Eso también significa que hay proyectos de formalización muy grandes, y con bastante dinero
detrás. Uno de ellos es [*FLT*](https://github.com/ImperialCollegeLondon/FLT), la formalización del último teorema de Fermat que inició Kevin
Buzzard. Anthropic publicó en septiembre
[una formalización del teorema](https://www.anthropic.com/research/formalizing-fermats-last-theorem)
en Lean; el proyecto continúa de todas formas, porque además de formalizar se quiere formalizar con unos
ciertos estándares de calidad.

El proyecto más importante, sin embargo, es [*Mathlib*](https://github.com/leanprover-community/mathlib4): la librería de matemáticas de Lean. Es un
repositorio público en el que colaboran miles de personas para construir un cuerpo de matemáticas
formalizadas con estándares muy estrictos, tanto de calidad del código como de la formalización.
Durante el curso nos vamos a apoyar en Mathlib constantemente, para poder echar mano de objetos y
resultados que ya están ahí y no tener que definir las matemáticas desde cero.

La comunidad se reúne en el [*Zulip de Lean*](https://leanprover.zulipchat.com), un chat público
donde puedes preguntar cualquier duda. El canal `#new members` está pensado para usuarios que acaban de empezar.

# Este curso

Algunas cuestiones prácticas antes de meter las manos en la masa.

## Metodología

El curso son cinco clases de unas dos horas. Las clases son bastante prácticas: contamos unas
pocas cosas y después hacemos muchos ejemplos.

También mandamos ejercicios para casa. Intentamos que el volumen de ejercicios obligatorios sea
reducido, pero hay algunos, y son bastante necesarios para poder seguir la clase siguiente. Además
mandamos otros opcionales, más difíciles o simplemente más curiosos, para coger soltura y para
divertirse.

### Cómo usar estos apuntes

Los apuntes siguen el orden de las clases. Un par de convenios que te vas a encontrar:

* El código aparece en recuadros grises y se puede copiar tal cual a tu editor. Este código está
  comprobado con la versión de Lean de los apuntes. Si algo no te funciona, quizás estés trabajando
  en una versión distinta.
* Cada vez que aparece una táctica nueva la presentamos en un recuadro naranja como el que verás
  en la clase siguiente, con una explicación y una tabla de antes y después. Esas tablas son lo
  más útil para consultar mientras haces los ejercicios.
* Al final de cada capítulo hay una sección *Archivos Lean* con todo su código en un archivo
  `.lean`, que puedes descargar o abrir directamente en [Lean web](https://live.lean-lang.org). Hay dos versiones: el *esqueleto*, con los ejemplos y los enunciados de los
  ejercicios por resolver, y las *soluciones*, con los
  ejercicios ya resueltos. La idea es trabajar sobre el esqueleto y mirar las soluciones solo
  cuando te atasques.

## Estructura del curso

Los contenidos de las cinco clases son, más o menos:

1. Qué es Lean, teoría de tipos y primeras demostraciones.
2. Lógica proposicional.
3. Propiedades de los números reales, sucesiones y continuidad de funciones.
4. Trabajando con estructuras: grupos.
5. Temas a elegir según el interés del grupo (modo término, axioma de elección, ...). Preguntas, cómo seguir aprendiendo y cómo contribuir a la comunidad.

## Objetivos

Esperamos que al final del curso puedas:

* Leer matemáticas escritas en Lean, y en Mathlib, y entender qué es lo que estás leyendo.
* Tener suficiente autonomía como para hacer un proyecto de formalización de matemáticas del nivel
  de la carrera.

### Trabajo de fin de curso

A raíz de esto último: hacia el final del curso propondremos varios proyectos en los que puedes
trabajar cuando terminen las clases.

No es obligatorio y no forma parte del curso; es un material didáctico más. Nos parece que la
forma más interesante de aprender es verse teniendo que sacarse las castañas del fuego en un
contexto más o menos real, y un proyecto de formalización es justo eso. Te ayudaríamos durante el
proyecto como si fuera un trabajo de fin de grado, así que tómatelo como una buena oportunidad para profundizar.

Si en algún momento se te ocurre un tema concreto que te apetezca formalizar, dínoslo y lo
miramos.

Dependiendo del número de interesados en realizar este trabajo, podrá ser individual o en grupo. Daremos más información en las últimas clases.

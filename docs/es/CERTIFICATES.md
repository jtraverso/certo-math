# Certificados

Con un LLM en el bucle el riesgo dominante no es la escasez de ideas, es la
**plausibilidad sin verificación**. De ahí sale una sola regla de diseño:

> El LLM propone, el motor certifica, y el certificado sobrevive sin el LLM.

Un veredicto que no puedes re-comprobar es un rumor. Cada comando aquí produce
un artefacto en su lugar, y la mayoría se re-comprueban con nada más que
aritmética.

## Qué compra "sin solver"

Un certificado marcado *sin solver* se comprueba con aritmética, evaluación,
conteo o propagación unitaria. No necesitas fiarte ni de Z3 ni de CBC —ni
tampoco quien lea tu paper, que es el punto de verdad. Un `unsat` de Z3 es una
aseveración; una prueba DRAT verificada es algo que un árbitro comprueba en su
propia máquina sin ejecutar tu código.

También es una red de seguridad. Si el solver tuviera un fallo, el certificado
no verificaría y obtendrías `ERROR`, no `DEMOSTRADO`.

**Manda la cabecera del propio `verify`.** Dice cómo se comprobó ese
certificado en concreto: *"verificado sin solver"*, *"comprobado contando, sin
solver"*, *"reejecutando el spec, no confiando en sus respuestas"*. La tabla de
abajo es el mapa; la cabecera es el territorio.

## Los cincuenta y dos tipos

| Tipo | Qué atestigua | ¿Sin solver? |
|---|---|---|
| `model` | un contraejemplo de `prove`, o un régimen no vacío | **sí**, sustituir y simplificar |
| `cnf_model` | una asignación satisface el CNF | **sí**, evaluación |
| `unsat_core` | las hipótesis se contradicen | **sí** cuando el núcleo es lineal (viajan los multiplicadores de Farkas); si no, vuelve a resolver solo el núcleo |
| `mus` | insatisfacibilidad **y** minimalidad | **sí** |
| `core_matrix` | un núcleo por objetivo, y que la tabla dice lo que dicen los núcleos | como `unsat_core`, por objetivo |
| `farkas` | una combinación de las hipótesis que cierra el sistema | **sí**, sumar fracciones |
| `farkas_ray` | infactibilidad de un LP | **sí**, sumar fracciones |
| `lp_dual` | optimalidad exacta de un LP | **sí**, aritmética racional |
| `branch_bound` | un óptimo entero, cada hoja cerrada por su propio certificado | **sí**, aritmética exacta |
| `mixed_design` | una construcción existe y alcanza un valor; **no** que sea óptima | **sí**, aritmética exacta |
| `gap` | una cota superior y una inferior, y la distancia entre ellas | no: el lado entero vuelve a resolver |
| `drat` | insatisfacibilidad de un CNF | **sí**, RUP/RAT |
| `graph_set` | una familia no isomorfa que pasa los filtros | **sí** |
| `sweep` | familia + certificados del predicado | depende del predicado |
| `domain_sweep` | dominio, vector de veredictos, y el predicado repetido | reejecuta el spec |
| `sweep_range` | un subcertificado por tamaño, y el orden | como sus hijos |
| `orbit_witnesses` | cada miembro es el representante reetiquetado | **sí**, reaplicar la permutación |
| `shrink_graph` | el contraejemplo es 1-minimal | sí, necesita el módulo del spec |
| `shrink_domain` | el descenso, repetido por índice | sí, necesita el módulo del spec |
| `bisect` | el par que acota el umbral | depende de sus hijos |
| `ideal` | `f = Σ hᵢgᵢ`, o `1 ∈ I` | **sí**, expandir un producto |
| `resultant` | `Res = A·f + B·g` | **sí**, expandir dos productos |
| `sos` | `p = Σ dᵢqᵢ²` en racionales exactos | **sí**, expandir un producto |
| `number` | primalidad, o una factorización | **sí**, exponenciación modular |
| `asymptotic` | el exponente de un parámetro en un término | **sí**, aritmética exacta |
| `ball` | una cantidad real está en un intervalo, y eso zanja la afirmación | **sí** para la afirmación; el intervalo necesita el spec |
| `parametric_bound` | `opt(p) ≤ b(p)·y` para todo p, o `≥` para un recubrimiento | **sí**, expandir y leer signos |
| `parametric_symmetry` | el cociente simbólico de una familia, y sus regímenes | **sí** simbólicamente; la ventana necesita instancias |
| `integer_peak` | ningún entero supera a `x*`, y `x*` alcanza el valor | **sí**, expandir y leer signos |
| `ratio_bound` | una desigualdad de fracciones por encima de un suelo | **sí**, multiplicar en cruz y leer signos |
| `first_entry` | dónde una sucesión cruza por primera vez una línea | **sí**, reencontrarlo en racionales exactos |
| `first_moment` | `E[X] < 1`, así que existe un objeto bueno | **sí**, volver a sumar y comparar |
| `exact_cover` | cada elemento en exactamente una parte | **sí**, contar |
| `symmetry_reduction` | las tres hipótesis del argumento de promediado | **sí**, el cociente se reconstruye |
| `equitable_quotient` | la partición, ambas regularidades, y los dos mapas | **sí**, conteo exacto |
| `integer_matrix` | rango, determinante, Hermite, Smith, con las transformaciones | **sí**, multiplicación de matrices |
| `clique_lp` | un óptimo LP sobre todas las cliques de un grafo, sin listarlas | **sí**, aritmética racional y la búsqueda de precios repetida |
| `symmetric_inertia` | la inercia de una matriz simétrica racional, PSD, y un vector que refuta PSD | **sí**, dos productos racionales: `S A Sᵀ = D`, `S S⁻¹ = I` |
| `affine_semigroup` | puntiagudo, pertenencia al cono, al grupo y al semigrupo, refutación de normalidad, base de Hilbert propuesta | **sí**, las negativas rehaciendo la búsqueda acotada |
| `capacity_profile` | una función afín a trozos de una capacidad: cota, alcance y cobertura en un intervalo | **sí**, una comprobación LP exacta por tramo |
| `branch_frontier` | lo que sabía una ramificación detenida: incumbente, cota, brecha, nodos abiertos | **sí**; un informe de estado, no una prueba |
| `linear_system` | `A x = b`, o una obstrucción `y·A = 0`, `y·b ≠ 0` | **sí**, un producto |
| `toric_cone` | primitividad, multiplicidad, altura, discrepancias | **sí**, determinante y resolución exactos |
| `family_extremum` | el mayor de una familia, y un dual para el resto | reconstruye el programa de cada ítem |
| `hypothesis_audit` | un veredicto por hipótesis, con la asignación que la rompe | no — sustituir un testigo deja una fórmula cerrada, y decidirla sigue siendo una llamada al solver |
| `variable_range` | el intervalo que puede tomar una variable: una combinación de Farkas en un extremo acotado, un rayo factible en uno no acotado | **sí**, sumar fracciones y caminar el rayo |
| `dependency_cycle` | un ciclo en las dependencias de un parámetro, y la comparación que lo cierra | **sí**, aritmética de clases |
| `lean_binding` | lo que un certificado supuso, contra lo que provee una declaración | no, vuelve a preguntar la implicación |
| `cegis` | el objeto no tiene contraejemplos en el dominio acotado | no, vuelve a resolver |
| `synth_proved` | el descubrimiento acotado **y** el enunciado universal | no, vuelve a resolver |
| `proof` | los lemas, **y** que cada uno se usa como su certificado permite | no, vuelve a resolver |
| `induction` | los casos base, el paso, **y** que encadenan sin hueco | no, vuelve a resolver |

## Delatan la manipulación

Edita a mano el objetivo de un dual y `verify` lo atrapa. Toca un paso de una
prueba DRAT y deja de ser RUP. Cambia una multiplicidad en un certificado de
cono y deja de coincidir con lo que dan los generadores.

Esto no es accidental: es por lo que las cantidades se **recalculan** durante la
verificación en vez de leerse. Un nodo de ramificación y acotación deriva su
propio programa lineal del sistema raíz y sus propias fijaciones; un cociente de
simetría se reconstruye desde los generadores; cada número de un cono se rehace
desde los rayos. Una carga útil que nadie recalcula es una carga útil que
cualquiera puede editar.

Un caso real de eso saliendo mal, antes de arreglarse: un dual para la
relajación de un nodo es un dual válido para **algún** programa lineal, y nada
en él dice de qué nodo vino. Un árbol que guardaba uno por nodo y comprobaba
cada uno por su cuenta aceptó dos de ellos **intercambiados**, y un subárbol
caro cerrado por el certificado de uno barato se leía exactamente como una
demostración completa.

## Hacia dónde es arriba: el marco de un `lp_dual`

`A`, `b`, `c`, `primal`, `dual` y `objective` se guardan en el sistema interno
**maximizado**, porque es el único marco donde cierra `c.x == b.y`. Un spec
escrito con `sense="min"` se resuelve como `max -c.x`, así que esos números son
la negación de los que pediste.

El payload no lo decía. Una minimización cuya respuesta era `3/2` quedaba
archivada como `"sense": "min", "objective": "-3/2"` y **verificaba**, siendo
consistente consigo misma en un marco que no nombraba. La pantalla decía `3/2`
y el fichero decía `-3/2`, y nada decía cuál era cuál.

Así que el artefacto lleva los dos:

```json
"sense": "min",
"objective": "-3/2",              // el sistema interno, donde c.x == b.y
"declared": {"objective": "3/2"}  // el sentido que pediste
```

`declared` es **opcional**, como `loads`: un certificado escrito antes de que
existiera verifica exactamente igual, y el esquema sigue en 4. Se deriva al
construir el certificado y `verify` lo **recalcula** — edítalo y el certificado
se rechaza, como cualquier otro número de aquí.

## Un puntero no es una comprobación

`verify` toma **un certificado y ningún sistema de ficheros**. Es deliberado
—un artefacto que hay que comprobar teniendo el directorio delante es un
artefacto que nadie comprueba— y tiene una consecuencia que conviene decir
claramente: **una ruta o un digest guardados son un campo que nada puede
recalcular jamás.**

`lean_binding` tenía uno. Dice *esto es lo que asumió AQUEL certificado, y esta
declaración de Lean lo provee*, y lo que ataba los dos era la cadena
`"certificate": "out/counting_bound.json"`:

```
honesto : VALID | certificate = out/counting_bound.json
forjado : VALID | certificate = out/un_fichero_que_no_existe.json
```

Mismo veredicto, un fichero que no está, un tipo que nunca fue. La implicación
se re-preguntaba correctamente desde las fórmulas del payload; era el *eslabón*
lo que nadie comprobaba.

Ahora el certificado viaja dentro del binding. `verify` re-comprueba el eslabón
sin disco: la fuente incrustada tiene que verificar por sí misma, ser del tipo
que se afirma, y llevar la procedencia del spec cuyo hash el binding registró.
La garantía es **exactamente la del verificador interno, ni más**: manipular el
`core_smt2` de un `unsat_core` se atrapa, manipular un campo que `unsat_core`
no mira, no.

Ese mismo razonamiento es por qué las relaciones del manifiesto se **calculan
del contenido** en vez de declararse. Un digest guardado en el padre habría
sido este defecto añadido a propósito.

## El Lean que certo emite se comprueba antes de salir

*¿Se puede certificar que el Lean generado es sintácticamente válido, sin
construirlo?* No como se pregunta, y la razón vale la pena: **la gramática de
Lean 4 es extensible, así que lo que parsea depende de lo que importes.**
`!![1, 2; 3, 4]` sin `Mathlib.LinearAlgebra.Matrix.Notation` falla con
`unexpected token ';'` —un error de *parseo* causado por un import ausente—. No
existe una noción de «Lean sintácticamente válido» independiente de los
imports, y `lean` no tiene modo solo-parseo: parsea y elabora juntos.

Lo que sí es decidible sin toolchain es más estrecho y útil: los invariantes
que la propia emisión de certo debe cumplir. `check_emission` los comprueba en
milisegundos —namespaces balanceados, toda declaración alcanzando su `:=`, un
`/--` adosado a una declaración, `sorry` presente exactamente cuando el
encabezado lo dice, imports coincidiendo con lo que el exportador declara—.

Medido contra el único exportador que tuvo bugs: añadir el de Smith costó
cuatro vueltas contra un Mathlib real y produjo cinco fallos de emisión. Estas
reglas atrapan tres. Los otros dos eran una ruta de módulo que se había mudado
y un import ausente, y eso no lo sabe nadie sin Mathlib en disco.

Esa proporción es el argumento. `tests/run_lean.py` no puede ser puerta de
release —minutos por fichero, dependencia de toolchain, y fallos que no dicen
nada sobre si la matemática de certo es correcta— así que nada comprobaba una
emisión entre una de esas corridas y una publicación. Esto sí, para cada
exportador registrado, en cada corrida de la suite.

## Una búsqueda que agotó su presupuesto

`branch_bound` afirma un óptimo y lo paga: cada hoja cerrada, cada rama
cubierta. Branch and bound es exponencial, así que una corrida real a menudo no
termina — y hasta la 0.12.1 una detenida devolvía `resource_exhausted` **sin
certificado alguno**. Su propio informe lo decía: *«Not a certificate — a
status report»*. Y además tiraba la pila de nodos sin abrir. Horas de búsqueda
que no dejaban nada verificable, archivable ni combinable.

`branch_frontier` es esa corrida como artefacto. Afirma un INTERVALO:

```
el óptimo está en [incumbente, cota]
este diseño alcanza el extremo inferior
estos subproblemas ABIERTOS son todo lo que queda
```

La tercera cláusula es la que lo hace certificado y no bitácora, y se comprueba
igual que la completitud de un árbol cerrado: cada nodo de ramificación tiene
todos sus hijos, y cada hijo está cerrado, ramifica, o está declarado abierto.
Una frontera que perdió un subárbol falla exactamente igual que un árbol que lo
perdió.

**Un nodo abierto lleva el dual de su padre, y las fijaciones del padre con
él.** El conjunto factible de un hijo es subconjunto del de su padre, así que
el dual del padre también lo acota — y se comprueban las dos mitades: el dual
contra el programa derivado del padre, y que el hijo de verdad extiende al
padre. Heredar solo el número habría sido gratis y habría heredado algo que
nadie comprueba: la cota de un nodo de ramificación no se verifica en ningún
sitio en un árbol cerrado, porque allí no descansa ninguna afirmación sobre
ella. Aquí sí.

**Lo que no afirma: que el incumbente sea óptimo.** Ese es el punto. `verify`
lo dice como aviso en todos ellos.


## Los avisos son parte del artefacto

Un certificado lleva lo que *no* establece, y `verify` lo repite cada vez —meses
después, cuando solo queda el artefacto y la ejecución está olvidada hace
tiempo.

```
AVISO: VACUA: las hipótesis se contradicen, así que esta demostración vale para
cualquier objetivo. El choque minimal es: dens_high, kappa_small
```

Una demostración vacua sigue diciendo que es vacua. Un barrido sigue diciendo
qué no certificó. Una multiplicidad sigue nombrando el retículo del que habla.
Un puente sigue siendo nombrado.

Esta es la mitad que envejece. El veredicto es fácil de recordar mal; el aviso
es lo que impide que una síntesis acotada se cite como teorema dos años después.

## Procedencia

Cada certificado lleva la versión de `certo` que lo emitió y, cuando vino del
CLI, la ruta y el `sha256` del spec. Si el archivo cambia después, `verify`
avisa: el certificado sigue siendo válido por su cuenta, pero ya no corresponde
al archivo que hay ahora. `certo status` llama a eso **obsoleto** y lo lista.

## La vacuidad se comprueba, no se supone

`prove` tiene éxito cuando `hipótesis ∧ ¬objetivo` es insatisfacible. Si las
hipótesis ya son insatisfacibles *por sí solas*, eso pasa para **cualquier**
objetivo. La demostración es válida —de una contradicción se sigue todo— y no
dice nada.

Es la forma más vergonzosa de estar equivocado y la más fácil de pasar por
alto, porque la salida se ve exactamente como un éxito. Así que se comprueba en
cada `prove`, `core`, `farkas` y `compose` exitoso.

```
$ certo prove vacuous.py
DEMOSTRADO -- simbólico y universal bajo las hipótesis  [unsat]
  VACUA: las hipótesis se contradicen, así que este objetivo --y cualquier
  otro-- se sigue. La demostración es válida y no dice nada.
  El choque es: dens_high, kappa_small
```

El veredicto no cambia, porque el veredicto no está mal. Lo que cambia es que
te lo dicen, **y te dicen qué hipótesis chocan**, minimalmente, así que la
siguiente pregunta ya está respondida.

### Por qué esta es la comprobación que un asistente de demostración no puede hacer por ti

Lean demostrará ese teorema, reportará cero `sorry`, y saldrá limpio en
`#print axioms`. Nada de eso te dice que las hipótesis fueran satisfacibles.

Un usuario lo dijo exactamente: `#print axioms` certifica *"no hice trampa"*. No
dice nada sobre *"esto no está hueco"*. Tenía dos módulos Lean —sin `sorry`,
axiomas `[propext, Classical.choice, Quot.sound]`, todo lo que una
formalización debe parecer— y **ambos tenían el régimen vacío**. Los teoremas
eran ciertos, válidos, y sobre nada. Otra línea produjo cuatro.

### Dos detalles

* **Cuesta una llamada extra al solver, solo en el camino exitoso**, y esa
  llamada es sobre un problema estrictamente más fácil que el que se acaba de
  resolver: las hipótesis sin el objetivo.
* **En `farkas` no se lee de los multiplicadores.** Un multiplicador cero sobre
  el objetivo negado sugeriría vacuidad, pero el LP es libre de darle a esa fila
  un peso no nulo aunque no haga falta, y suele hacerlo. Así que la pregunta se
  hace directamente: quita la fila del objetivo (y, en modo `--nonlinear`, cada
  fila derivada de ella) y busca de nuevo.

En `compose` la comprobación cae donde más importa. Dos lemas *derivados* nunca
pueden contradecirse —ambos son ciertos. Solo los **puentes** pueden, porque un
puente se afirma en vez de derivarse, y dos puentes que chocan hacen vacuo todo
el teorema.

## El alcance aparece en pantalla

Un `DEMOSTRADO` pelado invita a leer una síntesis acotada como un teorema. Cada
comando dice de qué alcance está hablando:

```
CANDIDATO SINTETIZADO -- búsqueda ACOTADA
CASO FINITO VERIFICADO -- no el teorema
BARRIDO FINITO REPRODUCIBLE -- el predicado NO está certificado
DEMOSTRADO -- simbólico y universal bajo las hipótesis
```

## Conservarlos: `status` y `ledger`

[`certo status`](COMMANDS.md#certo-status) lee un directorio y lo ordena en
RESULTADOS, AÚN DEBIDO, HUECO y OBSOLETO. No emite certificado,
deliberadamente: un informe que se certificara a sí mismo sería el único
artefacto aquí que nadie ha comprobado.

[`certo ledger`](COMMANDS.md#certo-ledger) es el registro de solo-añadir. Guarda
rutas y digests, nunca copias, así que un certificado manipulado o ausente
aparece como fallo en vez de duplicarse silenciosamente en el registro.

[`certo repro`](COMMANDS.md#certo-repro) empaqueta spec, certificados, versiones
y hashes para un árbitro.

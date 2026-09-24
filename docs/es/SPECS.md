# Specs: el DSL

Python es el lenguaje anfitrión. Un spec es un archivo `.py` con una función
`spec()` que devuelve uno de los tipos de abajo. No hay lenguaje propio, porque
un LLM escribe Python mucho mejor de lo que escribe SMT-LIB.

> **Los specs se ejecutan al cargarse.** Eso es inherente al DSL. Es el mismo
> nivel de confianza que ya tiene un agente con acceso a archivos, pero
> significa: no corras specs de terceros que no hayas leído.

```python
import z3
from certo import Spec

def spec():
    a, b, c = z3.Reals("a b c")
    s = Spec()
    s.assume("a_pos", a > 0)      # hipótesis NOMBRADAS: core informa sobre ellas
    s.assume("b_pos", b > 0)
    s.assume("c_pos", c > 0)
    s.claim((a+b)*(b+c)*(a+c) >= 8*a*b*c)
    return s
```

Nombra cada hipótesis. El nombre es lo que `core`, `audit` y `farkas` te
devuelven, y una hipótesis sin nombre es una sobre la que no te pueden avisar.

## Qué tipo para qué comando

| Tipo | Comandos |
|---|---|
| `Spec` | `prove`, `check`, `core`, `farkas`, `audit` |
| `MultiSpec` | `core` sobre varios objetivos |
| `SynthSpec` | `synth` |
| `LPSpec` | `opt`, `mixed` |
| `PackingSpec` | `opt` |
| `CNFSpec` | `cases`, `shrink` |
| `SweepSpec` | `sweep`, `shrink`, `enum` |
| `DomainSpec` | `sweep`, `cases`, `shrink` sobre cualquier dominio finito |
| `ProofSpec` | `compose` |
| `InductSpec` | `induct` |
| `IdealSpec` | `ideal` |
| `EliminateSpec` | `eliminate` |
| `ParametricSpec` | `parametric` |
| `PeakSpec` | `peak` |
| `SymmetrySpec` | `reduce` |
| `EquitableQuotientSpec` | `quotient` |
| `MatrixSpec` | `matrix` |
| `LinearSystemSpec` | `solve` |
| `ConeSpec` | `cone` |
| `CycleSpec` | `cycle` |
| `BindSpec` | `bind` |
| `FamilySpec` | `family` |
| `CoverSpec` | `cover`, `exists` |
| `RatioSpec` | `ratio` |
| `MomentSpec` | `moment` |
| `EntrySpec` | `entry` |
| `SOSSpec` | `sos` |
| `NumberSpec` | `number` |
| `BoundSpec` | `bounds` |
| `OrderSpec` | `order` |
| `BisectSpec` | `bisect` |

`certo ask spec.py` lee el tipo y corre el comando al que pertenece, así que
nunca tienes que recordar esta tabla. `certo lint spec.py` también lo lee, y
nombra los comandos para los que sirve el spec.

## Números

Los coeficientes aceptan `int`, `Fraction`, la cadena `"7/12"` o `float`:

```python
lp.objective({"x": Fraction(7, 12), "y": "1/3"})
lp.constraint({"x": 1, "y": 1}, "<=", Fraction(1, 2), name="cap")
```

Prefiere `Fraction` o la forma de cadena. Un flotante que llega como dato es un
flotante en el certificado, y `verify` te dirá que no es citable. En un
`BoundSpec` un flotante de Python **lanza** en vez de aceptarse, porque un
encierro construido desde `0.1` sería perfectamente riguroso sobre
`3602879701896397/2^55`.

## Dominios finitos

`DomainSpec` corre el patrón exhaustivo —los mismos seis estados, los mismos
certificados de predicado, la misma calibración— sobre cualquier cosa que
puedas enumerar.

```python
from certo import DomainSpec, Outcome

def spec():
    return DomainSpec(
        items=[(s, r) for s in range(2, 8) for r in range(2, 8)],
        predicate=lambda p: bound_holds(*p),
        collect=lambda p: ratio(*p),
        key=lambda p: "s={},r={}".format(*p),
    )
```

`key` convierte un ítem en un id estable: es lo que acaba en el certificado, así
que debe identificar el ítem sin ambigüedad. `verify` comprueba que los ids son
únicos. Lo que no puede comprobar es que el dominio sea **completo** —eso lo
define el spec.

`items` puede ser un invocable que devuelva un iterador, y `lint` inspecciona el
conteo sin materializarlo, así que `lambda: iter(range(10**7))` pasa el `lint`
en lo que tarda en leerse el archivo.

### Certificar el predicado

Un `bool` pelado te da un barrido **reproducible**. Devolver un `Outcome` te da
uno **certificado**:

```python
from certo import Outcome

def predicate(item):
    res = lp.opt(build(item))
    return Outcome(ok=res.verdict is Verdict.PROVED, cert=res.certificate,
                   detail="W* = " + res.meta["objective"])
```

```bash
certo sweep spec.py --cert-all
```

Hacen falta ambas mitades. Un predicado que certifica cada respuesta pero corre
con `--cert-all` apagado por defecto guarda solo los certificados de los
contraejemplos, y el certificado lleva entonces uno de veintiuno —y lo dice.
**Un certificado solo puede atestiguar lo que realmente contiene.**

`ok=None` significa "no concluyó". Un predicado que revienta o no concluye ya no
tumba el barrido entero, pero sí bloquea la afirmación de que la propiedad se
cumple en toda la familia. Un contraejemplo, en cambio, refuta aunque otros
ítems hayan fallado.

### Medir en vez de refutar

`collect` devuelve un valor por ítem y las estadísticas se mantienen **exactas**
si devuelves un `Fraction`: `2/5`, no `0.4`. `predicate` es opcional, así que
puedes medir sin refutar nada, y puedes devolver `Outcome(..., value=...)` para
que nada se calcule dos veces.

```python
SweepSpec(n=5, filters=["connected"], collect=lambda g: ratio(g), worst="min")
```

```
CALIBRACIÓN sobre 21 grafos: min=2/5 (D?{)  max=1 (D~{)  media=13/21
  3 más bajos: D?{ 2/5 | DCw 2/5 | DEg 2/5
```

El certificado guarda los valores y `verify` recalcula mínimo, máximo y media
para comprobar que concuerdan. Una conjetura que falla es un hecho; *cuán mal
falla y sobre qué objeto* es lo que te dice si debilitarla o abandonarla.

### Filtros

Los nombrados: `connected`, `chordal`, `triangle_free`, `k4_free`, `regular`,
`has_triangle`, `min_degree=K`, `max_degree=K`, y el número de aristas como
`edges=K`, un rango `edges=A:B` (cualquier extremo puede quedar abierto),
`min_edges=K` o `max_edges=K`.

**Con `geng` instalado, los que puede hacer de forma exacta los hace `geng`**:
`connected`, los grados y el rango de aristas siempre, y `triangle_free`,
`k4_free` y `chordal` cuando la propia ayuda del `geng` instalado los lista.
Cada filtro se vuelve a aplicar después, así que bajarlo solo puede ahorrar
tiempo: el barrido cordal de un usuario en n=9 enumeraba 274 668 grafos para
quedarse con 125, toda la diferencia filtrada en Python. `enumerated` cuenta
entonces lo que produjo `geng`, tras su parte del filtrado. certo encuentra `geng` con ese nombre o como `nauty-geng`
de Debian.

`filters` acepta invocables junto a los nombrados, así que una familia que el
catálogo no conoce igual se cuenta bien:

```python
SweepSpec(n=6, filters=["connected", is_split], predicate=...)
```

Los conteos se mantienen separados —`enumerated` antes de filtrar, `in_family`
después— y `verify` dice claramente que un filtro programable no puede
re-comprobarse solo desde el certificado, porque vive en el spec.

## Simetría: `canonicalize` frente a `labelling`

Ambos declaran cuándo dos ítems son el mismo objeto reetiquetado. Difieren en
qué puede hacer un certificado al respecto.

```python
canonicalize=lambda t: tuple(sorted(t))          # pide que le crean
labelling=lambda item: {punto_origen: etiqueta}  # pide que le comprueben
```

`canonicalize` es Python arbitrario, así que *"estos cuarenta comparten forma
canónica"* lo **afirma el spec**. Lo que `verify` comprueba es que la
descomposición se sostiene —los conteos cuadran, los representantes son
distintos, cada uno pertenece a la órbita que encabeza. Eso vale la pena tenerlo
(una descomposición cuyas partes no cuadran está mal fuera cual fuera el grupo)
y no es la pregunta.

`labelling` entrega la **permutación** en vez de la forma. certo la aplica, el
resultado *es* la forma canónica, y la permutación viaja en el certificado:

```
[ok] cada miembro ES el representante reetiquetado, reaplicando la permutación
     guardada  (40 reaplicadas, 0 llevadas pero no decodificables, fallan: -)
```

Declarar ambas se rechaza: una pide que le crean y la otra pide que le
comprueben.

La forma canónica propia de certo es exacta y **se niega** en vez de adivinar.
Sobre un objeto vértice-transitivo se niega de inmediato —una 1-factorización de
K6 tiene quince puntos que se ven todos iguales, y saber que `|Aut| = 120` aún
deja 10 897 286 400 clases laterales. Calcular bien un etiquetado canónico es
una búsqueda dura que una herramienta hecha para eso hace mucho mejor, así que
nauty encuentra el etiquetado, certo lo comprueba, y el artefacto lleva ambos.
**Esa vía no tiene tope, porque no se busca nada.**

## Tipos combinatorios nativos

Familias de conjuntos, hipergrafos, diseños y sistemas de máscaras se
recodificaban a mano en cada spec: una tupla de frozensets aquí, bitmasks allá,
un `key` para hacer un id, un `canonicalize` para cocientar, un `reduce` para
encoger. Cuatro piezas de andamiaje por problema, cada una un sitio donde
equivocarse sutilmente.

```python
from certo import DomainSpec, SetFamily

def spec():
    return DomainSpec(
        items=lambda: list(SetFamily.all_families(5, 2, 3)),
        predicate=lambda f: f.intersecting(),
        canonicalize="auto", reduce="auto",      # y ningún key= en absoluto
    )
```

| | |
|---|---|
| `is_design(t, λ)` | cada t-subconjunto en exactamente λ bloques |
| `is_uniform(k)`, `is_regular(r)` | las dos de siempre |
| `intersecting()` | todos los pares de bloques se cortan — la forma de Erdős–Ko–Rado |
| `covers()` | cada punto usado |
| `SetFamily.all_families(n, k, size)` | el dominio que barrer |
| `family_from_masks(n, masks)` | un sistema de máscaras, con id y forma canónica |

El valor de un tipo nativo aquí no es que guarde datos —una tupla hace eso. Es
que aporta las tres cosas que el resto de la herramienta pide: `key()`,
`canonical()` y `reductions()`. Así `key`, `canonicalize` y `reduce` pueden
quedarse todos en `"auto"`, y la clase de cualquiera se suma teniendo esos tres
métodos.

Dos familias reciben la misma forma canónica **exactamente cuando** un
reetiquetado del conjunto base lleva una a la otra. Los puntos se refinan en
clases que ningún reetiquetado puede mezclar —grado, luego los tamaños de bloque
por cada punto, luego lo mismo otra vez sobre las clases refinadas— y la forma
se minimiza sobre las permutaciones que respetan ese refinamiento. Sobre una
familia muy regular eso degenera hacia `n!`, así que hay un tope; alcanzarlo
**lanza** en vez de caer a un invariante más barato, porque un invariante que
fusionara dos familias no isomorfas fusionaría dos órbitas y nada aguas abajo se
enteraría.

## Un spec que no ejecuta nada

`load_spec` compila y ejecuta el `.py` que recibe. Para una persona editando
su propio archivo eso es la confianza que ya tiene un editor. Para un
**agente** es la parte más fina de la superficie: un modelo que escribe un spec
escribe un programa, y el cargador no distingue un programa lineal de
cualquier otra cosa que Python pueda hacer.

La mayor parte del corpus no lo necesita. Escribe el spec como **datos**:

```json
{
  "type": "LPSpec",
  "sense": "max",
  "var_names": ["x", "y"],
  "bounds": {"x": [0, 10], "y": [0, 10]},
  "obj": {"x": 2, "y": 3},
  "cons": [["cap_a", {"x": 1, "y": 1}, "<=", 1]]
}
```

```bash
certo opt spec.json          # un spec .json nunca ejecuta nada
certo opt spec.py --safe     # rechaza: este archivo se ejecutaría
CERTO_NO_EXEC=1 certo-mcp    # el servidor entero, en una línea de .mcp.json
```

Construibles desde datos: `LPSpec`, `PackingSpec`, `MatrixSpec`,
`LinearSystemSpec`, `ConeSpec`, `CycleSpec`, `CoverSpec`, `CNFSpec`,
`NumberSpec`, `EquitableQuotientSpec`. Lo que lleva una fórmula z3 o un
invocable está ausente a propósito: no hay forma de escribirlo en JSON, e
inventar un lenguaje de expresiones es justo lo que este proyecto decidió no
hacer.

**Lo que garantiza, exactamente: ningún código del archivo se ejecuta.** Nada
más. Un `LPSpec` en JSON todavía puede codificar el programa equivocado, y
`lint`, los avisos de alcance y la re-derivación de `verify` son lo que
trabaja sobre eso. Un modo que hiciera a la gente dejar de leer su propio spec
cambiaría un riesgo pequeño por uno mayor.

**Los números son exactos o se rechazan.** `"7/12"` es un `Fraction`; `0.583`
lanza, porque un flotante aquí es un flotante en el certificado y `verify` lo
llamaría no citable.

**Una clave desconocida se rechaza, no se ignora.** Un nombre de campo
descartado en silencio es como desaparece una restricción — este proyecto ya lo
pagó una vez. Una clave que empieza por `_` es un comentario, ya que JSON no
tiene y ningún campo de spec empieza así.

## Una tabla detrás de cada recuento

```bash
certo commands --table              # comando, spec, motor, certificado
certo commands --table --markdown   # como la llevan los documentos
certo commands --table --json
```

Derivada del parser, la tabla de rutas y el registro de verificadores, y los
tests comparan cada documento contra ella en vez de unos contra otros. La tabla
del README llegó a decir veintiocho listando veintinueve con treinta y nueve en
el CLI; la página del proyecto decía cuarenta y tres el día después de publicar
el comando cuarenta y seis. Nada de eso es difícil. Cada uno es un número que
nadie recalculó.

## Opciones y códigos de salida

Las opciones comunes van **después** del subcomando:

| Opción | Hace |
|---|---|
| `--json` | resultado legible por máquina en stdout |
| `--cert FILE` | escribe aquí el certificado |
| `--lang` | `en` o `es`; o pon `CERTO_LANG` |
| `--timeout-ms` | reloj de pared, un tope y no el presupuesto |
| `--rlimit` | el presupuesto de trabajo de Z3 — este es el reproducible |
| `--max-memory-mb` | techo duro |
| `--seed` | para los motores que toman uno |
| `--enumerate-timeout-s` | reloj de una enumeración externa (`geng`), separado del de un solver; por defecto 120 |
| `--max-output-mb` | cuánto puede imprimir una enumeración externa antes de detenerla; por defecto 64 |

**Hasta dónde llega el presupuesto.** `--timeout-ms` se le pasa a z3, a HiGHS
y CBC, a Clarabel dentro de `sos`, a los binarios SAT, y a `drat-trim` cuando
contrasta una prueba. Una enumeración externa tiene su propio reloj, porque
enumerar todos los grafos de `n` vértices y decidir una fórmula son trabajos
distintos. `export --check` compila Lean con `--check-timeout-s` (por defecto
900), porque una compilación contra Mathlib son minutos. Dos cosas **no**
quedan acotadas por él, a propósito o sin remedio: las sondas de `doctor` y la
llamada a `git` de la procedencia mantienen cotas fijas cortas propias, y el
cálculo de facetas de cddlib corre dentro del proceso, donde nada puede
interrumpir una llamada en C salvo el propio proceso.

Códigos de salida: `0` concluyente, `2` no concluyente, `1` certificado
inválido, `3` error. `lint` difiere: `0` limpio o solo notas, `1` errores, `2`
avisos.

## El esquema está congelado

El esquema de certificados está **congelado desde 0.4**: las cargas útiles
existentes no se mueven, así que un certificado producido para un paper sigue
verificando contra un certo posterior. Los tipos nuevos de certificado siguen
siendo aditivos y siempre lo serán. Los campos nuevos sobre un tipo existente
son opcionales, que es como `unsat_core` ganó sus multiplicadores de Farkas sin
que un lector de 0.5 se enterara.

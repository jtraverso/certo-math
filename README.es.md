# certo

**Entre tener una idea matemática y tener una demostración de ella hay mucho
trabajo que no es demostrar.** certo hace ese trabajo —encontrar el objeto,
romper las afirmaciones falsas, medir lo que sobrevive, reducirlo a lo que
realmente es, y ensamblar el resto— y cada paso vuelve con un **certificado
que cualquiera puede re-comprobar sin fiarse de certo.**

CLI y MCP. Cincuenta y cuatro comandos. Corre en milisegundos donde una
formalización cuesta horas.

*English: [README.md](README.md) · cualquier comando acepta `--lang en`.*

| | |
|---|---|
| **[Página del proyecto →](https://jtraverso.github.io/certo-math/)** | la introducción didáctica: para qué sirve, en una página, en ambos idiomas |
| **[Comandos](docs/es/COMMANDS.md)** | los cincuenta y cuatro, una entrada cada uno: la pregunta, el spec, el certificado, y qué **no** establece |
| **[Specs](docs/es/SPECS.md)** | el DSL: cada tipo con un ejemplo mínimo que funciona, opciones comunes, códigos de salida |
| **[Certificados](docs/es/CERTIFICATES.md)** | por qué son el centro, los cincuenta y tres tipos, cuáles se re-comprueban sin solver |
| **[Casos trabajados](docs/es/CASES.md)** | problemas reales de punta a punta: simetría, barridos, cotas paramétricas, empaquetamientos, datos tóricos |
| **[Qué significa un resultado](docs/es/VERDICTS.md)** | estado frente a veredicto, las cuatro afirmaciones de optimización que se parecen, `false` frente a `null`, códigos de salida |
| **[Límites](docs/es/LIMITS.md)** | qué no hace, y las preguntas frecuentes |
| **[Recorrido](examples/WALKTHROUGH.md)** | un problema, siete comandos, quince segundos |

---

## Qué es

El instrumento de laboratorio: encontrar una contradicción rápido, saber qué
hipótesis sobran, validar exhaustivamente un caso finito, acotar una constante
con certificado, sintetizar un candidato sobre un dominio acotado.

**No** es un asistente de demostración —eso es Lean, Rocq o Isabelle— ni un
catálogo de álgebra computacional. [Qué no hace](docs/es/LIMITS.md) importa
tanto como la lista de comandos.

La división del trabajo, en palabras de un usuario tras una sesión real: certo
encuentra y certifica los intercambios pequeños; la demostración humana explica
por qué se ensamblan globalmente sin doble conteo.

| Fase | Qué preguntas | Qué vuelve |
|---|---|---|
| **Encontrar** | ¿Existe un objeto así? ¿Cuál es el mejor? | el objeto —y con `mixed --prove-optimal`, una demostración de que *es* el mejor |
| **Romper** | ¿Es cierta esta afirmación? | un contraejemplo **con valores concretos**, en milisegundos |
| **Medir** | No *si* falla: cuánto, y ¿dónde es peor? | mínimo, máximo y media exactos, y las instancias extremas por nombre |
| **Reducir** | Noventa contraejemplos. ¿Cuántos objetos son en realidad? | órbitas bajo tu simetría, y un testigo minimal por órbita |
| **Establecer** | ¿Vale para todos los casos, para todo `n`, exactamente? | pruebas DRAT, inducción con la cadena comprobada, multiplicadores de Farkas, cofactores de Gröbner, sumas de cuadrados, encierros rigurosos |
| **Ensamblar** | ¿Sobre qué descansa todo mi proyecto, y qué sigo debiendo? | la demostración con cada **puente nombrado**, y un informe de lo que sigue supuesto |

Un veredicto que no puedes re-comprobar es un rumor. Todo aquí produce un
artefacto, y la mayoría se comprueba sin solver alguno.

## Instalación

Requiere Python 3.11+.

```bash
pip install "certo-math[mcp,numerics]"
```

El paquete importable y los comandos son `certo`, no `certo-math`:
`from certo import Spec`, `certo prove spec.py`. Solo la distribución
lleva el nombre largo, porque `certo` a secas es una palabra disputada.

Desde un clon, en cambio:

```bash
git clone https://github.com/jtraverso/certo-math
cd certo-math
pip install -e ".[mcp,numerics]"
```

Dependencias: `z3-solver` y `pulp`, que traen sus binarios. Los extras son
`mcp` para el servidor MCP y `numerics` para `bounds` y `sos` (`python-flint`,
`mpmath`, `numpy`, `clarabel` y `highspy`); sin ellos tienes el CLI, menos
numérica rigurosa y sumas de cuadrados, y los LP se resuelven lanzando CBC en
vez de con HiGHS dentro del proceso. `polyhedra` (`pycddlib`) hace que `semigroup`
decida con las facetas del cono en vez de buscar; solo trae *wheels* para
Windows, y en el resto se compila contra cddlib y GMP.

Comprueba que funciona:

```bash
certo doctor
```

Herramientas opcionales, ninguna se instala sola y ninguna hace falta para
empezar:

| Herramienta | Para qué | Sin ella |
|---|---|---|
| [`nauty`](https://pallini.di.uniroma1.it/) (`geng` en el `PATH`) | enumerar grafos | motor Python, cómodo hasta n=8 |
| `cadical` o `kissat` | `cases` en instancias grandes | nuestro CDCL, correcto pero lento |
| `drat-trim` | segunda opinión sobre pruebas DRAT | el verificador Python incorporado basta |
| `python-flint` (Arb) | `bounds` con funciones especiales | `mpmath.iv`, para las elementales |
| `numpy` | la búsqueda de Gram detrás de `sos` | **nada** — `sos` no puede correr sin ella |

`certo doctor` dice cuáles tienes y **qué cuesta cada hueco**, que es la parte
que una lista de cruces rojas se deja fuera.

## Dos minutos

```bash
certo core examples/amgm.py --lang es
```

```
DEMOSTRADO -- simbólico y universal bajo las hipótesis  [unsat]
  hipótesis necesarias: a_pos, b_pos, c_pos | redundantes: noise
```

Cada archivo de [`examples/`](examples/) lleva en su docstring qué hace y qué
esperar. ¿Perdido? `certo commands` imprime la tabla de rutas en tu terminal,
en tu idioma.

## Las tres reglas transversales

1. **Cada comando devuelve un certificado, o dice explícitamente por qué no.**
   Nunca un "sí" pelado.
2. **Seis estados de resultado:** `unsat`, `sat`, `unknown_solver`, `timeout`,
   `resource_exhausted`, `out_of_theory`. Solo los dos primeros son
   concluyentes. Los otros cuatro significan "sin respuesta", pero por razones
   distintas, y colapsarlos sale caro: un LLM que lee "unknown" escribe "no
   existe solución".
3. **Determinismo por presupuesto de trabajo, no por reloj:** `rlimit` en Z3 y
   `conflict_budget` en SAT. *Esto cubre nuestros motores, no tu predicado:* si
   tu predicado de `sweep` llama a scipy o a CBC, esa parte queda fuera de la
   garantía.

## Si eres un LLM al que le piden usar esto

1. Lee [`docs/es/SPECS.md`](docs/es/SPECS.md), o llama a la herramienta MCP
   `dsl_guide`, antes de escribir un spec.
2. Busca el comando por la **pregunta**, no por el nombre:
   [`docs/es/COMMANDS.md`](docs/es/COMMANDS.md), o `certo commands`.
3. Corre [`certo lint`](docs/es/COMMANDS.md#certo-lint) en cada spec antes de
   ejecutarlo. Es lo más barato de la herramienta y atrapa el régimen
   contradictorio, la familia vacía y el dominio de 10⁹.
4. Lee el veredicto, no el código de salida. `unknown_solver` **no** es "no
   existe".
5. Los certificados se escriben a disco y no viajan en la respuesta MCP. Llama
   a `verify` con la ruta que te dan.
6. ¿Más de un puñado de preguntas? Usa la [API en proceso](#api-en-proceso), no
   un bucle sobre la CLI: manda el arranque, y un apaño escrito para evitarlo
   es un apaño en punto flotante.

## Los cincuenta y cuatro comandos

Agrupados como los agrupa [`certo commands`](docs/es/COMMANDS.md). Las entradas
completas, con lo que cada uno **no** establece, en
[`docs/es/COMMANDS.md`](docs/es/COMMANDS.md).

| Comando | Qué hace | Motor | Certificado |
|---|---|---|---|
| `prove` | Niega la afirmación y busca `unsat` | Z3 | núcleo insatisfacible, o contraejemplo |
| `check` | Satisfacibilidad; `--hypotheses-only` pregunta si el régimen es no vacío | Z3 | modelo, o núcleo |
| `core` | MUS: qué hipótesis hacen falta | Z3 | núcleo minimal |
| `audit` | ¿Cada hipótesis se gana su lugar, o el teorema está sobreenunciado? | Z3 | **veredicto por hipótesis, cada uno con la asignación que la rompe** |
| `farkas` | `linarith` / `nlinarith`, con los multiplicadores | LP exacto | **certificado de Farkas**, sin solver |
| `compose` | Ensambla lemas en una demostración, comprobando la unión | Z3 | **demostración**: cada lema, su certificado y el enlace |
| `induct` | Casos base + paso, y la comprobación de que la cadena une | Z3 | **inducción**: ambas mitades, y los dos números que importan |
| `synth` | CEGIS: ∃obj ∀entrada ∃aux | CEGIS/Z3 | objeto + los contraejemplos que lo forzaron |
| `opt` | LP/ILP, o un empaquetamiento | CBC | **dual en racionales exactos** = el certificado de carga |
| `mixed` | Un esqueleto discreto buscado, la parte continua certificada | CBC + LP exacto | **diseño mixto**: asignación, dual exacto y una cota |
| `order` | El exponente de `n` al sustituir magnitudes: ¿decae, o es Θ(1)? | Laurent exacto | **el exponente**, sin solver |
| `bounds` | Una desigualdad numérica, rigurosamente (`e`, `log`, `π`, `ζ`) | Arb o mpmath | **encierro en racionales exactos** |
| `ideal` | Sistemas polinomiales: refutarlos, o certificar qué se sigue | Gröbner, nuestro | **cofactores**, comprobados expandiendo |
| `eliminate` | Quita una variable de dos polinomios; conserva la condición sobre el resto | Sylvester + Bareiss | **Res = A·f + B·g**, sin solver |
| `parametric` | Una cota para TODO valor de un parámetro, desde un dual que ya tienes | dualidad débil, simbólica | **y y los residuos desplazados**, sin solver |
| `peak` | La mejor elección ENTERA para una familia de cuadráticas cóncavas | exacto, sin búsqueda | **el maximizador y dos desigualdades de paso**, sin solver |
| `reduce` | "Por simetría": las tres hipótesis del argumento de promediado, comprobadas | exacto, sin búsqueda | **generadores, órbitas y el cociente**, sin solver |
| `matrix` | Álgebra lineal entera exacta: rango, determinante, Hermite y Smith | transformaciones unimodulares | **U, V y sus inversas**, comprobadas multiplicando, sin solver |
| `solve` | `A x = b` exactamente, sobre ℚ o ℤ | eliminación exacta, Smith | **la solución y el sistema**, un producto que comprobar; una obstrucción cuando no hay |
| `quotient` | Una partición de un programa, y la equivalencia que induce | conteo exacto | **los datos de clase y ambas regularidades**, sin solver |
| `cone` | Datos tóricos locales: primitividad, multiplicidad, funcional de altura, discrepancias | det y solve exactos | **los números que consumen dos teoremas geométricos**, sin solver |
| `columns` | Un LP sobre todas las cliques de un grafo, sin listarlas: generación de columnas con una búsqueda de precios que el verificador repite | aritmética racional exacta | sin solver |
| `atlas` | Un dominio de parámetros cubierto por cajas, cada una certificada por `parametric`, y UN enunciado para el todo | cada pieza re-verificada, el cubrimiento recalculado celda por celda | **nombra la franja sin cubrir**, sin solver |
| `semigroup` | Semigrupos afines como comprobador: puntiagudez, minimalidad y pertenencia al cono, al grupo y al semigrupo | aritmética entera y racional exacta | **refuta la normalidad con un testigo, nunca la afirma**, sin solver |
| `profile` | Cómo responde un óptimo a UNA capacidad en todo un intervalo: una función afín a trozos, no un valor | aritmética racional exacta | **decide `f` en su dominio** — cota, alcanzabilidad y cobertura — sin solver |
| `family` | El mayor de diez mil programas lineales, y por qué nada lo supera | LP exacto | **el ganador y un dual para el resto**, sin solver |
| `ratio` | Una desigualdad de fracciones para TODO n | polinomios exactos | **el numerador despejado y el signo del denominador**, sin solver |
| `moment` | ¿El número esperado de eventos malos es menor que uno, así que existe un objeto bueno? | racionales exactos | **el momento y la masa que deja**, sin solver |
| `entry` | Dónde una sucesión cruza por primera vez una línea, y por cuán poco | racionales exactos | **el prefijo y los dos términos que lo acotan**, sin solver |
| `exists` | ¿Existe alguno, y la refutación cuando no? | CDCL propio | modelo, o prueba DRAT |
| `cover` | ¿Es esto un recubrimiento exacto? Una partición en cliques es un caso | conteo | **el universo y las partes**, sin solver |
| `sos` | Un polinomio es no negativo, como suma de cuadrados | numérico + redondeo exacto | **cuadrados racionales**, sin solver |
| `number` | Primalidad, o una factorización | Pratt | **árbol de exponenciación modular** |
| `cases` | SAT con prueba DRAT verificada | CDCL propio o binario externo | prueba DRAT |
| `enum` | Grafos no isomorfos con filtros | nauty o Python | lista canónica + hash |
| `sweep` | Predicado y/o valor sobre una familia o CUALQUIER dominio finito | nauty o Python | familia **+ certificados del predicado** |
| `shrink` | Minimiza un contraejemplo (grafo o MUS) | CDCL / reducción | testigo de minimalidad |
| `bisect` | El umbral de una constante | prove o cases | el par que lo acota |
| `range` | El intervalo admisible de una variable sobre el régimen, no un punto suyo | dual LP exacto | **una combinación de Farkas en cada extremo**, sin solver |
| `cycle` | Un parámetro que depende de sí mismo: compone las clases de crecimiento y cierra el ciclo | escalera de crecimiento | **la cadena, sus clases y la única comparación**, sin solver |
| `bind` | Ata un certificado a la declaración Lean que debe justificarlo, y comprueba que lo hace | implicación Z3 | **la hipótesis, el enunciado, y si uno cubre al otro** |
| `lint` | Comprueba un spec antes de gastar el cómputo en él | — | — |
| `status` | Dónde está una demostración: demostrado, debido, hueco, obsoleto | — | — |
| `doctor` | Qué puede hacer esta instalación, y qué cuesta cada hueco | — | — |
| `report` | ¿De quién es el bug -- de certo, del spec o de la máquina? -- y una carpeta local para reportarlo. No envía nada | — | — |
| `ask` | Un único punto de entrada: carga un spec y corre lo que pida (`what` es el mismo comando) | — | lo que produzca el comando |
| `commands` | Qué comando responde qué pregunta | — | — |
| `repro` | Empaqueta spec, certificados, versiones y hashes para un árbitro | — | el paquete |
| `promote` | Corre de nuevo un `--explore`, certificado, y dice si coinciden | se corre certificado | el certificado de la corrida certificada |
| `pack` | Miles de certificados en un solo zip con manifiesto, cada miembro legible por separado | — | el archivo; `verify` comprueba cada miembro |
| `mcp` | Qué servidores MCP de certo siguen con código viejo tras reinstalar; `restart --yes` los detiene | — | — |
| `verify` | Re-verifica un certificado guardado | — | — |
| `export` | Spec a SMT-LIB2/DIMACS, o un certificado de Farkas lineal a Lean | — | — |
| `ledger` | Registro de auditoría de lo que se corrió | — | — |

Opciones comunes, **después** del subcomando: `--json`, `--cert FILE`,
`--lang`, `--timeout-ms`, `--rlimit`, `--max-memory-mb`, `--seed`.

Códigos de salida: `0` concluyente, `2` no concluyente, `1` certificado
inválido, `3` error. Qué significa cada estado y cada veredicto está en
[Qué significa un resultado](docs/es/VERDICTS.md).

## Qué no hace

El límite duro son los **enunciados asintóticos con cuantificadores sobre `n`**.
"Existe `N` tal que para todo `n ≥ N`, todo grafo…, la pérdida es `≤ εn²`" no lo
decide esta herramienta.

| Pregunta | ¿`certo`? |
|---|---|
| ¿R(3,3) ≤ 6? | **Sí.** `cases`, una prueba DRAT de 23 líneas, verificada |
| ¿R(3,3) = 6? | **Sí.** `bisect`, umbral certificado por ambos lados |
| ¿R(5,5) ≤ 48? | **En la práctica no.** Finito, pero el espacio es 2^903 |
| ¿Converge R(k,k)^(1/k)? | **No, en principio.** Asintótico: no expresable |

La lista completa, y las preguntas frecuentes, en
[`docs/es/LIMITS.md`](docs/es/LIMITS.md).

## API en proceso

Una CLI cuesta un arranque de Python por pregunta. En un portátil con Windows
son **1,2 s antes de importar certo** —`python -c pass` a secas— frente a unos
70 ms propios de certo. Un barrido de 853 programas lineales son dos minutos de
trabajo detrás de veinte minutos de arrancar Python.

```python
from certo import LPSpec, api

spec = LPSpec(sense="max", title="w")
...
res = api.run("opt", spec)
res.meta["objective"]     # '32/3' -- una cadena exacta, no un float
res.certificate           # el artefacto que habría escrito `--cert`
```

| | |
|---|---|
| `api.run(comando, spec, limits=None, **opciones)` | devuelve un `Result` |
| `api.runnable()` | cada comando que toma un spec |
| `api.options(comando)` | lo que ese comando acepta, leído del motor |

`run` **verifica lo que produjo** y levanta `api.SelfCheckFailed` antes que
devolver un certificado que no pasa su propio verificador. Cuesta menos del 1%
de un `opt`. Pon `self_check=False` solo después de medirlo.

Los módulos de `certo.engines` siguen siendo privados; la promesa son `run`,
`runnable` y `options`. Los comandos que leen un directorio o el entorno
(`verify`, `status`, `doctor`, `enum`, …) no están aquí —para los dos primeros
ya están exportados `certo.verify` y `certo.load_spec`—.

## Servidor MCP

Cada comando expuesto al LLM, sin copiar y pegar. El proyecto trae un
[`.mcp.json`](.mcp.json) listo; para registrarlo a mano en Claude Code:

```bash
claude mcp add certo --env CERTO_WORKSPACE=. -- certo-mcp
```

`CERTO_WORKSPACE` (el directorio actual por defecto) contiene `specs/` y
`certs/`. **Toda ruta queda confinada ahí.**

Tres decisiones de diseño:

1. **Los certificados no vuelven en la respuesta.** Un MUS ocupa 18× más en
   disco que la respuesta entera, y el modelo no puede verificarlo leyéndolo.
   Se escriben a disco y vuelven la ruta, el tipo y el digest.
2. **Los errores vuelven como datos, no como excepciones.** El SDK convierte
   cualquier excepción en `Error executing tool X` y se traga la razón; un
   modelo que lee eso no puede arreglar su spec. Aquí recibe qué pasó y qué
   corregir.
3. **`dsl_guide` primero.** Es herramienta y recurso (`certo://dsl`).

> **Los specs son código Python y se ejecutan al cargarse.** Eso es inherente
> al DSL y es el mismo nivel de confianza que ya tiene un agente con acceso a
> archivos. El servidor confina rutas, pero **no es un sandbox**: no lo
> apuntes a specs de terceros.

`certo doctor --register-mcp` añade certo al `.mcp.json` del directorio actual,
**fusionando** con lo que ya esté registrado en vez de reemplazarlo, negándose
a tocar un archivo que no sea JSON válido, y comprobando que el servidor
arranca de verdad —una pregunta distinta de si está registrado, y la que la
gente quiere decir.

## Idiomas

El inglés es el idioma por defecto y la fuente de verdad. El español va como
capa encima:

```bash
certo core examples/amgm.py --lang es      # o CERTO_LANG=es
```

Las traducciones viven en [`src/certo/locales/`](src/certo/locales/) como JSON.
Una clave ausente cae a inglés, así que una traducción parcial se degrada en
lugar de romperse. Para añadir un idioma, copia `en.json`, traduce los valores
y conserva los `{placeholders}` — hay un test que impone ambas invariantes.

Dos cosas se quedan en inglés diga lo que diga `--lang`, porque son superficie
de API y no prosa: **los nombres de comandos y flags**, y **los nombres y
descripciones de las herramientas MCP**. Los certificados guardan **claves** de
nota, no texto renderizado, así que uno emitido en español se lee correctamente
para un lector en inglés.

## Tests

Más de quinientos, sin necesidad de framework de tests. La cifra no se da
exacta a propósito: el README antiguo decía 253 cuando había el doble,
porque un número que nadie recalcula es un número equivocado.

```bash
for t in smoke mcp i18n extras adversarial determinism; do python tests/test_$t.py; done
```

`python tests/run_examples.py` corre los 65 specs de ejemplo y verifica cada
certificado que producen.

Notas de versión en [CHANGELOG.md](CHANGELOG.md); lo planeado, lo bloqueado y
lo rechazado deliberadamente en [BACKLOG.md](BACKLOG.md).

## Licencia

MIT. El motor de síntesis es una reimplementación del algoritmo CEGIS de
[marcelwa/CEGIS](https://github.com/marcelwa/CEGIS) (MIT), no de su código.

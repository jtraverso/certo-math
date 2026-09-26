# Qué significa un resultado

Cada comando de certo responde con **dos palabras y, casi siempre, un
certificado**: un *estado* y un *veredicto*. Son preguntas distintas, y leer
una como la otra es la manera más común de malinterpretar un resultado. Esta
página es el único lugar que dice qué significa cada uno, comando por comando
donde difieren.

## Estado y veredicto no son lo mismo

El **estado** es lo que el solver dijo sobre la consulta que certo *le
planteó*. El **veredicto** es lo que eso significa para *la pregunta que tú
hiciste*.

Se separan porque certo suele plantear la negación de tu pregunta. Para
probar `x > 0` pregunta si `x <= 0` es posible; el solver dice `unsat`, y tu
veredicto es `proved`. Para probar que un óptimo entero es 9, la ramificación
pregunta si algo supera 9; la respuesta es `unsat`, y el veredicto es
`proved`. **Un estado `unsat` sobre un óptimo probado no es un fallo.** Lee el
veredicto.

## Los siete estados

| Estado | Significa | Concluyente |
|---|---|---|
| `unsat` | la consulta que planteó certo no tiene solución | **sí** |
| `sat` | la consulta tiene solución, y certo la tiene | **sí** |
| `unknown_solver` | el solver paró sin concluir, por sus propias razones | no |
| `timeout` | se agotó el reloj | no |
| `resource_exhausted` | se agotó un presupuesto de nodos, memoria o rlimit | no |
| `out_of_theory` | la pregunta está fuera de lo que este comando decide | no |
| `explored` | `--explore` respondió barato, en punto flotante o sobre una muestra, y no certificó nada | no |

**Ninguno de los cuatro últimos significa «no existe».** Cada uno es una razón
distinta para no tener respuesta, y se mantienen separados porque quien lee
`unknown` tiende a escribir «no hay solución». `resource_exhausted` en una
búsqueda suele venir con lo que la búsqueda sabía al parar: ver
`branch_frontier` más abajo.

## Los siete veredictos

| Veredicto | Significa para tu pregunta |
|---|---|
| `proved` | lo que afirmaste se cumple, y el certificado es la prueba |
| `refuted` | lo que afirmaste falla, y el certificado lleva el contraejemplo |
| `satisfiable` | lo que pediste existe, y aquí está: un punto, un óptimo, un diseño |
| `unsatisfiable` | lo que pediste no existe: tus restricciones se contradicen |
| `inconclusive` | sin respuesta. El estado dice por qué |
| `error` | el comando no pudo correr: un spec que no carga, una opción que no aplica |
| `likely` | `--explore` lo encontró donde miró, sin certificar. Nunca `proved`; `certo promote` es cómo llega a serlo |

## Códigos de salida

`0` concluyente, `2` no concluyente, `1` un certificado que falla su propia
comprobación, `3` error. `lint` es distinto: `0` limpio o solo notas, `1`
errores, `2` avisos. Los scripts deben decidir por estos, no por el texto.

`--deadline` detiene una corrida con `2`, tras imprimir la pila de cada hilo.
Cualquier OTRO código no es de certo: `-1073741819` (`0xC0000005`) o
`-1073740022` (`0xC000070A`) en Windows, o un número de señal negativo en
Linux, es el proceso muriendo en código nativo; un código grande o negativo
sin nada en stderr suele ser una muerte desde fuera — el propio límite de
tiempo de un driver. Una corrida que termina sin salida y funciona al
relanzarla: corre `certo doctor`, cuya fila `startup` nombra los hooks de
arranque que se sabe matan el intérprete antes de que corra certo. Con
`PYTHONFAULTHANDLER=1` incluso esos imprimen una pila.

### Llamar a certo desde un programa

- **Usa `python -m certo ...`, no `certo`.** En Windows `certo.exe` es un
  lanzador que arranca el intérprete como *hijo*. Un timeout que mata
  `certo.exe` deja vivo ese intérprete con las tuberías abiertas, y quien
  llama se queda esperándolas para siempre. Bajo carga el lanzador mismo
  puede además no encontrarse (`WinError 2`). `python -m certo` es un solo
  proceso, sin lanzador. Si no hay más remedio que usar el lanzador, mata el
  árbol entero (`taskkill /T /F /PID ...`).
- **`--json` siempre escribe JSON.** Una corrida que falla, sea por una
  excepción (salida `3`) o por un rechazo (salida `1`), y que habría dejado
  stdout vacío, ahora escribe una línea:
  `{"status": "error", "exit": ..., "message": ...}`, donde el mensaje es lo
  que dijo stderr. Lo único que no puede cubrir es un proceso que muere en
  código nativo antes de que corra Python. `doctor` nombra los hooks de
  arranque que se sabe que hacen eso.
- **Costo de arranque.** Cada corrida vuelve a importar certo y z3. Donde un
  hook `.pth` hace lento o mata el arranque del intérprete, `python -S` con
  el directorio site-packages en `PYTHONPATH` se salta todos los `.pth`. Un
  usuario midió que `import certo` bajó de 10–21 s a 1,7–4,8 s así, sin tocar
  su instalación de Python.

## Optimización: cuatro afirmaciones distintas

Aquí es donde más importan las palabras, porque cuatro resultados se parecen
en pantalla y establecen cosas muy distintas.

| Lo que ves | Comando | Lo que queda establecido |
|---|---|---|
| `EXACT optimum certified: v` | `opt` sobre un LP | **el óptimo**, en racionales exactos, con un dual que prueba que nada lo mejora |
| `integer optimum v, CERTIFIED` | `opt` sobre un ILP, ajustado | **el óptimo entero**: un punto entero alcanza la cota exacta de la relajación |
| `best integral point found: v ... bounds the optimum by b` | `opt` sobre un ILP, con brecha | solo que el óptimo está **entre** `v` y `b`. El punto entero es del solver, no está probado óptimo |
| `OPTIMUM v, PROVED` | `mixed --prove-optimal`, `cover --prove-optimal` | **el óptimo entero**, por ramificación y acotación: cada hoja certificada, y el árbol comprobado para cubrir todo el dominio entero |

Cuando `opt` reporta una brecha, **`certo mixed SPEC --prove-optimal` la
cierra** sobre el mismo spec. Existe desde 0.4.0; ahora el mensaje lo dice.

### `mixed`: tres niveles, con nombre en el certificado

| Nivel | Significa |
|---|---|
| `feasible` | este diseño existe y alcanza su valor. **Ninguna optimalidad** |
| `conditional_optimum` | lo mejor que puede hacer la parte continua **dado este esqueleto discreto**. Otro esqueleto puede ser mejor. **No es una prueba del óptimo global**, y es el nivel que más a menudo se lee como si lo fuera |
| `global_optimum` | el valor alcanzado iguala la cota de relajación sobre todos los esqueletos, así que nada lo mejora |

Para pasar de `conditional_optimum` a una prueba, usa `--prove-optimal`.

### Una búsqueda que se detuvo

Un `--prove-optimal` que se queda sin nodos o sin reloj devuelve
`resource_exhausted` con un certificado **`branch_frontier`**: el incumbente,
la mejor cota, la brecha y cada nodo aún abierto. Es un informe de estado, no
una prueba, pero es exacto, y el incumbente es una cota inferior genuina.
Nunca se asciende a «óptimo» porque se acabó el presupuesto.

## Una negativa, y la ausencia de respuesta

Varios comandos distinguen «no» de «no se pudo saber», y la diferencia vive en
el certificado como `false` frente a `null`.

| Campo | `false` significa | `null` significa |
|---|---|---|
| `semigroup` `in_semigroup` | no está en el semigrupo, y la búsqueda graduada que lo prueba está acotada | la búsqueda no era finita o se agotó |
| `semigroup` `pointed` | no es puntiagudo, **con una combinación nula de los generadores que lo muestra** | no se encontró ni graduación ni esa combinación |
| `semigroup` `normal` | -- | siempre `null`: un testigo refuta la normalidad, nada aquí la afirma |
| `hilbert` `is_minimal_generating_set` | decidido: no es el sistema minimal, y por qué | no se pudo decidir |

## Alcance: sobre qué es concluyente una respuesta

Un veredicto concluyente lo es **sobre lo que se preguntó**, que no siempre es
el enunciado que tienes en mente.

* `sweep` y `cases` resuelven **los casos finitos** que recibieron, no el
  enunciado general.
* `synth` **descubre** sobre un dominio acotado. No prueba un teorema.
* `family` y `sweep` toman la **completitud de su lista** como afirmación del
  spec, igual que una prueba toma sus hipótesis.
* Cada certificado dice qué **no** establece; la referencia de comandos tiene
  una línea «No establece» por comando.

## Verificar: válido, inválido, y un aviso

`certo verify ARCHIVO` rehace cada comprobación desde el certificado solo.

* **VÁLIDO**: pasaron todas las comprobaciones.
* **INVÁLIDO**: falló una comprobación. No hay que fiarse del certificado, lo
  haya producido quien lo haya producido.
* **Un aviso sobre un certificado válido** es un hecho distinto de la
  invalidez: un `--target` no alcanzado, un certificado de una versión
  anterior que dice menos de lo que diría uno nuevo, o un certificado en punto
  flotante marcado **no citable**. El certificado es correcto; el aviso dice
  lo que no te da.

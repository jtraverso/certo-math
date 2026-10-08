# Qué no hace

Esta página importa tanto como la lista de comandos.

## El límite duro

**Enunciados asintóticos con cuantificadores sobre `n`.** "Existe `N` tal que
para todo `n ≥ N`, todo grafo…, la pérdida es `≤ εn²`" no lo decide esta
herramienta. `prove` y `synth` trabajan sobre fórmulas decidibles o dominios
acotados; `sweep` y `cases` sobre familias finitas.

La escalera, con números de Ramsey como ejemplo:

| Pregunta | ¿`certo`? |
|---|---|
| ¿R(3,3) ≤ 6? | **Sí.** `cases`, una prueba DRAT de 23 líneas, verificada |
| ¿R(3,3) = 6? | **Sí.** `bisect`, umbral certificado por ambos lados |
| ¿R(5,5) ≤ 48? | **En la práctica no.** Finito, pero el espacio es 2^903 |
| ¿Converge R(k,k)^(1/k)? | **No, en principio.** Asintótico: no expresable |

## Los límites específicos, cada uno enunciado en la propia salida

- `sweep` y `cases` resuelven el **caso finito**, no el teorema.
- Un `sweep` sobre un predicado `bool` pelado es **reproducible**, no
  certificado: nada establece que las respuestas del predicado sean correctas.
- El certificado `graph_set` verifica la no isomorfía y los filtros, **no la
  completitud** de la familia.
- Para un ILP el dual certifica la **cota de la relajación**, no la optimalidad
  entera.
- `mixed` certifica que una construcción existe y alcanza un valor —no que el
  esqueleto discreto fuera óptimo, salvo que `achieved` iguale a `bound`.
- `shrink` da un contraejemplo **1-minimal, no mínimo**.
- `audit` quita hipótesis de una en una, así que no establece que el conjunto
  sea **conjuntamente** minimal.
- `bisect` **supone monotonía** en el parámetro; comprueba los extremos y avisa
  si se portan mal, pero la monotonía misma no se demuestra.
- `parametric` y `peak` usan un test de desplazamiento **suficiente y no
  necesario**, así que un fallo significa *no establecido por esta vía*, nunca
  *falso*.
- `ideal` trabaja sobre **ℂ**. Un ideal propio significa que existe una raíz
  compleja y no dice nada sobre una real.
- `eliminate` da una resultante que es **necesaria** para una raíz común sobre
  cualquier cuerpo y **suficiente** solo sobre uno algebraicamente cerrado.
- `sos` es incompleto: desde grado 4 en 3 variables hay polinomios no negativos
  que no son sumas de cuadrados.
- `order` certifica el **exponente, no la constante**.
- `cone` calcula los números que consumen dos teoremas geométricos; **no**
  afirma una carta lisa, una modificación crepante, ni una fibra SNC o reducida.
- `bounds` nunca demostrará que una cantidad es no nula cuando de hecho es cero;
  reporta `resource_exhausted`.
- La eliminación de cuantificadores sobre los reales es doblemente exponencial y
  se cuelga en ejemplos de libro de texto. Por eso `qe` no está entre los
  comandos.

- Una `card` -- rol, eslabón, pendientes -- es **declarada**, nunca
  comprobada: dice para qué pensó el autor el resultado, y un PASS que descansa
  sobre algo pendiente es condicional.
- Un LP exacto resuelto desde la base del solver en flotante sigue siendo
  **comprobado**, no creído: `check_lp` decide, sea cual sea la ruta que lo
  encontró.

**El nicho es claro:** descubrir objetos, destruir formulaciones falsas y
minimizar hipótesis antes de pagar el coste de formalizarlas.

## Cosas que certo no adivina

Una decisión de diseño recurrente, en un solo sitio porque explica muchos
rechazos:

| Rechaza | Porque |
|---|---|
| un flotante en la expresión de un `BoundSpec` | un encierro construido desde `0.1` es riguroso sobre `3602879701896397/2^55` |
| una entrada no entera en un `MatrixSpec` | una matriz redondeada en silencio es otra matriz |
| `reduce="auto"` sobre un tipo no reconocido | un testigo minimal para la relación equivocada se ve igual que uno minimal para la correcta |
| `canonicalize` y `labelling` a la vez | una pide que le crean, la otra pide que le comprueben |
| un generador de simetría que falla cualquiera de las tres hipótesis | un grupo equivocado da una reducción equivocada, no una más débil |
| un maximizador de `peak` con coeficientes no enteros | un argumento sobre un punto que no existe no demuestra nada |
| `cover --prove-optimal` sin `candidates=` | un recubrimiento solo es minimal relativo a lo que estabas dispuesto a usar |
| una forma canónica más allá de su tope | un invariante que fusionara dos familias no isomorfas fusionaría dos órbitas, y nada aguas abajo se enteraría |

---

# Preguntas frecuentes

**¿Es esto un demostrador de teoremas?**
No. Decide fórmulas en teorías decidibles y verifica casos finitos. Para el
teorema, Lean o Rocq. certo es la capa anterior.

**Si ya confío en Z3, ¿para qué sirve el certificado?**
Para que quien lea tu paper no tenga que hacerlo. Un `unsat` de Z3 es una
aseveración; una prueba DRAT verificada es algo que un árbitro comprueba en su
propia máquina sin ejecutar tu código. También es una red de seguridad: si el
solver tuviera un fallo, el certificado no verificaría y obtendrías `ERROR`, no
`DEMOSTRADO`.

**¿Qué significa `unknown_solver`? ¿Es "no existe"?**
No. Significa que el solver terminó sin concluir. `timeout` es que se acabó el
reloj, `resource_exhausted` el presupuesto, `out_of_theory` que la fórmula cae
fuera del fragmento decidible. Los cuatro difieren de `unsat`, que sí significa
"no existe".

**¿Por qué mi `opt` salió en punto flotante?**
Porque nada exacto verificó. certo prueba tres rutas en orden: reconstruir la
respuesta de CBC como racionales; derivar el dual del primal por holgura
complementaria; y resolver el dual directamente con un símplex exacto. Que
fallen las dos primeras suele deberse a datos de entrada que ya eran flotantes
—pásalos como `Fraction` o como la cadena `"7/12"`—. La tercera ruta tiene un
presupuesto de pivotes, así que un programa bastante grande puede agotarlo.

**Mi `opt` dio un número pero no escribió certificado.**
Es deliberado. Un certificado en punto flotante puede ser
holgado; lo que no puede ser es uno que el propio certo rechace. Cuando el único
certificado disponible no pasa `certo verify` —que es lo que hace un dual de
ceros, porque `b.0 = 0` no acota nada—, el número vuelve etiquetado como sin
certificar y no se escribe fichero. Un artefacto que no pasa el verificador no
es un certificado más débil; no es un certificado.

**¿Por qué `prove` es rápido con un polinomio y no puede con otro?**
El grado. Sobre `t^k <= t` en `[0, 1]` —trivialmente cierto y decidible— el
grado 10 se demuestra en 12 ms y el grado 11 no se demuestra en 20 segundos. Es
un acantilado, no una pendiente, y está mucho más abajo de lo que se espera: un
objetivo de grado 63 no es "un poco más difícil". `certo lint` avisa en 11. El
remedio es una sustitución que baje el grado; el schedule de grado 63 de un
usuario se volvió `t = s^3` más un argumento de dominación, y certo lo cerró en
4,3 ms.

**Necesito correr miles de instancias.**
No hagas un bucle sobre la CLI. Cada llamada paga un arranque de Python —1,2 s
en Windows antes de importar certo— así que un barrido de dos minutos tarda
veinte. La [API en proceso](../README.es.md#api-en-proceso) es
`api.run(comando, spec)`, y conserva los racionales exactos que un apaño en
flotante regala.

**¿Por qué es lento el solver SAT incorporado?**
Porque es un CDCL en Python. Existe porque el registro de pruebas de pysat no
funciona en Windows —devuelve 0 líneas con cada uno de sus solvers— y sin prueba
no hay certificado. Para instancias grandes:
`certo cases spec.py --solver-binary /ruta/a/cadical`.

**¿Puedo fiarme de ese CDCL?**
No hace falta. Si emitiera una prueba malformada, el verificador DRUP la rechaza
y obtienes `ERROR`. También hay un test diferencial contra Z3 sobre CNF
aleatorios. **El verificador audita al solver.**

**¿Los resultados son reproducibles?**
Los de nuestros motores sí: el presupuesto es trabajo, no tiempo. Tu predicado
de `sweep` queda fuera de esa garantía.

**¿Y si cambio el spec después de generar un certificado?**
`verify` lo sigue aceptando —verifica por su cuenta— pero avisa de que ya no
corresponde al archivo actual. `certo status` llama a eso **obsoleto**.

**¿`synth` demuestra algo?**
Encuentra un candidato en el dominio acotado que declaraste. Eso es un
descubrimiento, no un teorema, y el banner lo dice. Para el enunciado general,
usa `--prove-candidate`.

**¿Cómo conecto esto con Lean?**
`certo export --lean` emite **una** cosa: un certificado de Farkas lineal como
ejemplo `linarith` ejecutable. Todo lo demás es a mano, y es deliberado —certo
solía emitir andamiaje para varios tipos de certificado y nada de eso compilaba,
lo que cuesta una compilación de Lean descubrir. Donde un certificado es el
entregable, lo que una formalización necesita de él son los números y el
enunciado, y ambos están en la carga útil.

**¿Por qué no un certificado SOS de verdad vía un SDP, en `farkas --nonlinear`?**
Porque un SDP se resuelve en punto flotante, así que lo que vuelve no es exacto,
y un certificado inexacto no es citable —la misma razón por la que `opt`
reconstruye racionales en vez de imprimir los flotantes del solver. Una
heurística de grado 2 cuya salida es exacta gana a una de grado *d* cuya salida
necesita una salvedad. `certo sos` es la vía exacta: búsqueda numérica,
reconstrucción racional, LDLᵀ exacto.

**¿Puedo usarlo sin conexión y sin nada más instalado?**
Sí. `z3-solver` y `pulp` traen sus binarios; el resto es Python puro.

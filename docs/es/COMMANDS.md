# Los cuarenta y seis comandos

Agrupados por la pregunta que responden, en el mismo orden y con las mismas
palabras que `certo commands` imprime en tu terminal. Si alguna vez discrepan,
manda la terminal: se genera desde la tabla de rutas.

Cada entrada tiene los mismos cinco campos, siempre en este orden:

| Campo | Significa |
|---|---|
| **Pregunta** | qué estás preguntando realmente. Lee esto, no el nombre |
| **Spec** | el tipo que tu función `spec()` debe devolver — ver [SPECS.md](SPECS.md) |
| **Responde** | qué vuelve por el camino concluyente |
| **Certificado** | el tipo que se escribe a disco, y si re-comprobarlo necesita solver |
| **No establece** | qué **no** debe concluir un lector. La herramienta lo repite en `verify`; no son descargos de responsabilidad, son el borde de lo afirmado |

Saltar: [¿Es cierto?](#es-cierto) · [¿Mi planteamiento es sano?](#mi-planteamiento-es-sano) ·
[¿Cuán grande, cuán pequeño, cuántos?](#cuán-grande-cuán-pequeño-cuántos) ·
[¿Para todos los casos?](#vale-para-todos-los-casos) ·
[Álgebra y números](#álgebra-números-y-estructuras) ·
[Construir y ensamblar](#construir-ensamblar-conservar) ·
[Puntos de entrada](#puntos-de-entrada-y-contabilidad)

---

## ¿Es cierto?

### `certo prove`

**Pregunta** — ¿Es cierta esta afirmación bajo estas hipótesis?
**Spec** — `Spec`
**Responde** — una demostración, o un **contraejemplo con valores concretos**
**Certificado** — `unsat_core`, sin solver siempre que el núcleo sea aritmética
lineal; o `model`, siempre sin solver
**No establece** — que las hipótesis sean satisfacibles. Una demostración desde
hipótesis contradictorias es válida y no dice nada, así que la vacuidad se
comprueba en cada éxito y se reporta por nombre.

Una refutación es la mitad útil más a menudo de lo que se espera, porque viene
con valores. Se afirmaba que la restricción de densidad de un usuario forzaba
`G` casi completo; `prove` la refutó en 15 ms con `dens = 27/32` factible —ni
cerca de "casi completo", y ese número dice hacia dónde arreglar el enunciado.

```
$ certo prove examples/refute_density.py
REFUTADO  [sat]
  el contraejemplo:
    dens = 7/8
    kappa = 4
  certificado: model (no necesita solver, id 1a76b821f2cafa42)
```

### `certo core`

**Pregunta** — ¿Qué hipótesis necesita realmente?
**Spec** — `Spec`, o `MultiSpec` para varios objetivos a la vez
**Responde** — el subconjunto insatisfacible minimal, y qué hipótesis sobraban
**Certificado** — `mus` / `unsat_core`, sin solver cuando el núcleo es lineal
**No establece** — que el conjunto de hipótesis sea minimal *conjuntamente*. Un
par puede sobrar junto sin que sobre ninguna por separado.

```
$ certo core examples/amgm.py
DEMOSTRADO -- simbólico y universal bajo las hipótesis  [unsat]
  hipótesis necesarias: a_pos, b_pos, c_pos | redundantes: noise
```

Sobre un `MultiSpec` la respuesta es una tabla, y la tabla es el punto: una
hipótesis irrelevante para un objetivo y necesaria para otro es invisible
cuando los objetivos se miran de uno en uno.

```
$ certo core examples/core_matrix.py
  hipótesis   identity  positivi  ordering
  r_ge_3            no        sí        no
  d_ge_1            no        no        no
  d_le_r            no        no        sí
  nunca usada por ningún objetivo: d_ge_1
```

`verify` también comprueba que **la tabla dice exactamente lo que dicen los
núcleos**.

### `certo farkas`

**Pregunta** — ¿Es cierta esta desigualdad, con los multiplicadores a la vista?
**Spec** — `Spec`
**Responde** — los multiplicadores racionales no negativos que combinan las
hipótesis con el objetivo negado hasta que todo se cancela, más la llamada a
`linarith` / `nlinarith` lista para pegar
**Certificado** — `farkas`, **sin solver**: comprobarlo es sumar fracciones
**No establece** — nada, cuando no encuentra nada. `farkas` es incompleto a
propósito en ambos modos, así que "sin certificado" significa *esta búsqueda no
lo cerró*, nunca *falso*.

```
$ certo farkas examples/farkas_linear.py
DEMOSTRADO  [unsat]
  multiplicadores:
    x_ge_1                 1
    y_ge_1                 1
    __goal__               1
  Lean: linarith [x_ge_1, y_ge_1]
```

Una hipótesis con multiplicador 0 no aparece en la lista, así que el
certificado dice qué hipótesis usa realmente la demostración —`core` gratis, y
exactamente lo que mantiene pequeña una interfaz a Lean.

`--nonlinear` es `nlinarith`, fielmente: multiplica pares de hipótesis, añade
algunos cuadrados, trata cada monomio como variable fresca y corre la búsqueda
lineal sobre eso. Las filas derivadas quedan marcadas en el certificado, porque
un lector debe saber cuáles no eran hipótesis.

> **`prove` para saber. `farkas` para certificar.** El `nlsat` de Z3 es
> completo para aritmética real; esto no lo es, y a cambio te da la razón.

### `certo induct`

**Pregunta** — ¿Vale para todo `n ≥ n₀`?
**Spec** — `InductSpec`
**Responde** — los casos base, el paso, **y la comprobación de que la cadena
une**
**Certificado** — `induction`; vuelve a resolver, así que no es sin solver
**No establece** — nada por parte de un solver: no hay esquema de inducción en
un solver SMT. El principio se aplica *aquí*, y `verify` lo dice siempre.

La unión es la razón de que esto sea un comando. Una base que cubre 3..8 con un
paso válido solo desde `k ≥ 10` no demuestra **nada** sobre `n = 9`, y la frase
"y de ahí por inducción" se lee exactamente igual en ambos casos.

```
$ certo induct examples/induct_sum.py
DEMOSTRADO  [unsat]
  6 casos base k=3..8, paso desde k=3, encadenados por inducción
```

Pon `step_from=10` y se niega al construir —no se escribe certificado—. Falsifica
uno después y la verificación vuelve a atraparlo:

```
[XX] el paso empieza no más tarde de donde acaba la base  (paso desde k=10, la base llega a 8)
```

El paso se demuestra con el índice **libre**, que es lo que lo hace
universalmente válido: una demostración con una variable libre es una
demostración para todo valor de ella.

---

## ¿Mi planteamiento es sano?

### `certo check`

**Pregunta** — ¿Mi régimen es no vacío — tienen estas hipótesis algún modelo?
**Spec** — `Spec`
**Responde** — con `--hypotheses-only`, un **modelo** si el régimen está
habitado, el **choque minimal** si no
**Certificado** — `model`, **sin solver**: la no vacuidad se re-comprueba solo
evaluando
**No establece** — nada sobre las hipótesis, si preguntas sin
`--hypotheses-only` y tu afirmación es el literal `False`.

Esa última línea es la trampa, y está señalizada. `check` decide
`hipótesis AND afirmación`, así que una afirmación `False` reporta
INSATISFACIBLE sean cuales sean las hipótesis. Un usuario preguntó exactamente
eso sobre un sistema que sí tiene modelos y se le dijo "no existe modelo".

```
$ certo check regime.py
INSATISFACIBLE  [unsat]
  no existe modelo -- pero la afirmación es el literal False, así que esto no
  dice nada sobre las hipótesis. Pregunta con `--hypotheses-only`.
```

```
$ certo check regime.py --hypotheses-only
SATISFACIBLE  [sat]
  el régimen es NO VACÍO: las 3 hipótesis se cumplen juntas, y aquí hay un
  punto donde lo hacen
```

### `certo lint`

**Pregunta** — ¿Está bien planteado este spec, antes de gastar el cómputo?
**Spec** — cualquiera
**Responde** — hipótesis contradictorias, una familia vacía, un dominio de 10⁹,
un predicado que devuelve `bool`, un paso inductivo que empieza después de que
acabe la base
**Certificado** — ninguno, y ninguno afirmado
**No establece** — que el spec sea *correcto*. Comprueba la forma de la
pregunta, no la matemática.

Lo más barato de la herramienta. Córrelo en cada spec antes de correr el spec.

```
$ certo lint examples/lint_vacuous_regime.py
Spec -- para `certo prove / check / core`
  [XX] las hipótesis se contradicen, así que cualquier demostración será VACUA
       --válida y sobre nada. El choque es: kappa_large, density_high, sparse
  1 errores, 0 avisos, 0 notas
```

Cuatro hallazgos que se pagan solos:

| Hallazgo | Por qué importa |
|---|---|
| la afirmación es un polinomio univariado de grado ≥ 11 | `prove` cierra grado 10 en 12 ms y no cierra grado 11 en 20 s, medido sobre un enunciado trivialmente cierto. Un usuario pasó 71 minutos con un polinomio de schedule de grado 63 y obtuvo `INCONCLUSIVE [timeout]`; sustituir `t = s³` a mano dejó que certo lo cerrara en 4,3 ms |
| el paso inductivo empieza después de que acaben los casos base | `induct` también se niega —después de descargar cada caso base, que es donde se van las horas. Aquí es comparar dos enteros |
| el predicado devuelve `bool` | entonces el barrido será `reproducible`, no `certificado`. Gente que escribió el predicado ella misma ha leído mal esa diferencia |
| `integer=True` hace enteras **todas** las variables | un usuario lo leyó como "aquí dentro hay enteros" y obtuvo un diseño que no vale nada, con cada peso redondeado a cero |

Cuenta un dominio sin construirlo —`items=lambda: iter(range(10**7))` se
inspecciona, nunca se materializa— y lee el tamaño de una familia de grafos de
una tabla, así que pasar `lint` a un barrido de 11 vértices cuesta lo que
cuesta leer el archivo.

Cargar un spec lo **ejecuta**; así funcionan los specs aquí. Más allá de eso,
lint llama al predicado una vez como mucho y nunca corre el solver sobre el
objetivo.

Códigos de salida: `0` limpio o solo notas, `1` errores, `2` avisos.

### `certo audit`

**Pregunta** — ¿Cada hipótesis se gana su lugar, o mi teorema está
sobreenunciado?
**Spec** — cualquier spec con hipótesis nombradas
**Responde** — uno de cuatro veredictos por hipótesis —`needed`, `redundant`,
`domain`, `unknown`— y, para `needed`, **la asignación que rompe la afirmación
sin ella**
**Certificado** — `hypothesis_audit`; re-comprobarlo sustituye cada testigo y
vuelve a decidir el resultado, así que necesita solver — pero no la búsqueda que
lo encontró
**No establece** — que el conjunto de hipótesis sea minimal. Se quitan de una
en una.

`core` atrapa un teorema enunciado con holgura. Esto atrapa el error contrario
y más caro: un teorema enunciado **con demasiada fuerza**, formalizado, y solo
entonces descubierto como un enunciado sobre una clase más pequeña que la que
el paper afirma.

```
$ certo audit examples/hypothesis_audit.py
SATISFACIBLE  [sat]
  2 hipótesis son REDUNDANTES (n_large, connected): la afirmación sigue
  siguiéndose sin ellas, así que el teorema es más débil de lo que parece
  [REDUNDANTE] n_large
  [necesaria]  m_bounded   sin ella: connected=True, m=6, n=5
```

`connected` se plantó como señuelo obvio. `n_large` no —`n ≥ 5` se lee como si
tuviera que importar, y no importa, porque `m ≤ n − 2` ya da `m ≤ n`. La
hipótesis que no hace nada rara vez es la que alguien sospechaba.

**El testigo es el contenido, no el veredicto.** Saber que `m_bounded` hace
falta vale poco; saber que `n = 5, m = 6` la rompe es lo que te dice si
escribiste la hipótesis que querías.

**`domain` existe porque la división es total en SMT.** `n/0` no es un error en
Z3; es algún valor fijo que el solver se inventa. Quitar una hipótesis que
protege un denominador daba un "contraejemplo" instantáneo en `d = 0`, y la
hipótesis quedaba como `needed` por una razón sobre el solver y no sobre el
teorema. Ahora todo divisor que pueda anularse se recoge de antemano y cada
búsqueda queda protegida por él:

```
$ certo audit guarded.py
  1 hipótesis son obligaciones de DOMINIO (d_nonzero): quitar una no hace falsa
  la afirmación, la hace sin sentido
  [DOMINIO]    d_nonzero   sostiene: d != 0
```

Ni `needed`, porque la afirmación no se vuelve falsa sin ella; ni desde luego
`redundant`, porque quitarla da un enunciado sobre un valor que nadie definió.
Una hipótesis `domain` **no** debe quitarse —descárgala como condición lateral
en el asistente de demostración. Y la distinción se pregunta en vez de leerse
de la forma de la fórmula: pon `d >= 1` junto a `d != 0` y ese mismo `d != 0`
pasa a ser genuinamente `redundant`.

### `certo status`

**Pregunta** — ¿Dónde está todo mi proyecto?
**Spec** — ninguno; lee un directorio de certificados
**Responde** — cuatro secciones: RESULTADOS, AÚN DEBIDO, HUECO, OBSOLETO
**Certificado** — **ninguno, deliberadamente.** Un informe que se certificara a
sí mismo sería el único artefacto aquí que nadie ha comprobado
**No establece** — que los certificados verifiquen. `status` lee las
afirmaciones que otros comandos hicieron; `certo status --verify` las
re-comprueba todas.

```
$ certo status out/
19 certificados bajo out
  sweep 6   unsat_core 4   proof 3   farkas 2   gap 1   induction 1   sos 1

  RESULTADOS -- 9 certificados sobre los que nada más aquí se apoya
  AÚN DEBIDO -- 3 supuestos sobre los que descansan estos resultados
  HUECO -- 1 afirmaciones válidas que dicen menos de lo que parecen
  OBSOLETO -- 2 certificados cuyo spec se movió
```

**RESULTADOS** son los certificados sobre los que nada más en el directorio se
apoya. El certificado de un lema no es un resultado; la demostración que se
sostiene sobre él sí.

**AÚN DEBIDO** es cada puente y cada optimalidad no afirmada, incluidos los que
están tres niveles abajo. Los puentes son legítimos y a menudo inevitables;
perderles la cuenta no lo es, y es fácil perderla precisamente porque todo lo
que los rodea verifica.

**HUECO** es lo válido que dice menos de lo que parece: una demostración vacua
con su choque nombrado, un barrido cuyo predicado nadie certificó, un óptimo
que es un valor alcanzado y no un máximo demostrado. También escanea archivos
`.lean` en busca de enunciados de la forma `theorem foo : True := by`, saltando
`.lake` y `lake-packages`.

**OBSOLETO** es un certificado cuyo spec cambió desde que se emitió. No está
mal —verifica por su cuenta— pero ya no describe el archivo que tiene al lado,
y seis meses después nadie recuerda cuál.

`certo status <dir> --manifest` responde otra pregunta: *¿certifiqué todos,
exactamente una vez?* Un conteo no es esa garantía —dos corridas sobre 71
celdas con un duplicado también cuentan 72—.

El manifiesto da el conjunto en orden canónico —**por digest, no por nombre de
fichero**, así que dos personas que lo produjeron en distinto orden obtienen el
mismo número— con una huella agregada sobre la misma receta Horner que
`matrix`, y los dos tipos de duplicado reportados en vez de colapsados: el
mismo artefacto en dos rutas, y dos certificados distintos sobre el mismo
sujeto.

La omisión necesita un conjunto declarado para ser detectable siquiera, y ese
es el límite honesto. `--expect FICHERO` toma los titulares que se pretendía
producir y nombra lo que falta; sin él, el manifiesto solo dice lo que hay, y
no dice nada que no pueda saber.

También reporta las relaciones que puede **derivar**, y las deriva en vez de
leerlas: un cono declara un retículo, un certificado Smith trata de una matriz,
y la arista es una coincidencia de huellas. Ninguno menciona al otro, así que
no hay nada que falsificar. Una arista dice *estos dos tratan de la misma
matriz*, no que uno dependa del otro. La regularidad de un cono la establece su
propio `multiplicity == 1`; un Smith sobre ese retículo la corrobora y no la
carga.


### `certo doctor`

**Pregunta** — ¿Puede esta instalación hacer lo que necesito?
**Spec** — ninguno
**Responde** — cada capacidad, presente o ausente, y **qué cuesta cada hueco**
**Certificado** — ninguno
**No establece** — nada; no hace ninguna afirmación matemática.

```
$ certo doctor
  capacidad    presente  para qué
  z3           [ok]      prove, check, core, synth, compose
  nauty        [--]      enumeración rápida de grafos para enum y sweep

  piezas opcionales ausentes, cada una con su alternativa:
    nauty        el motor Python incorporado, cómodo hasta n=8
```

Cada fila dice tres cosas, y la tercera es la que importa. Una herramienta
opcional ausente casi nunca es fatal aquí, y una lista de cruces rojas que no
lo diga se lee como una instalación rota.

También reporta **hooks de arranque** del intérprete (un `.pth` que corre en
cada arranque cuesta tiempo real en cada invocación), una **instalación
parcial** que quedó cuando un archivo no pudo reemplazarse, y un desajuste
entre `certo --version` y la versión que `pip` tiene registrada.

`certo doctor --register-mcp` registra el servidor MCP en `.mcp.json`,
fusionando en vez de reemplazar, y comprueba que arranca.

---

## ¿Cuán grande, cuán pequeño, cuántos?

`certo doctor --repair` lista lo que dejó atrás una instalación interrumpida, y
`--repair --apply` lo borra. **La vista previa es lo que hace por defecto** y
aplicar es una segunda decisión, porque lo que se borra está dentro de
site-packages: equivocarse ahí rompe un entorno, no un fichero.

pip deja dos marcadores y reconoce los dos. `~`-algo es un renombrado que no
terminó —en Windows un `certo-mcp.exe` retenido lo corta entre el renombrado y
la limpieza, y el paquete queda presente dos veces con dos nombres, uno de
ellos no importable—. `algo.deleteme` es un lanzador que no pudo reemplazar,
junto a un `.exe` huérfano. No toca nada que no lleve `~` o `.deleteme`, y al
`.exe` huérfano lo deja en paz: no es marcador de pip.

**No** reinstala. Correr pip desde dentro de la herramienta ocultaría cuál de
los dos falló, y el motivo de que la instalación se rompiera suele seguir
corriendo: `--repair` nombra qué está reteniendo los ejecutables de certo antes
de listar nada.


### `certo opt`

**Pregunta** — ¿Cuál es el óptimo, exactamente?
**Spec** — `LPSpec`, o `PackingSpec`
**Responde** — el óptimo en racionales exactos, y el **dual**, que en un
empaquetamiento se lee como la carga sobre cada recurso
**Certificado** — `lp_dual`, **sin solver**: aritmética racional
**No establece** — optimalidad entera. Para un ILP el dual certifica la **cota
de la relajación**. Con `integer={"K3"}` —entero en un tipo, fraccionario en
otro— `opt` reporta solo la cota de la relajación y lo dice.

CBC trabaja en punto flotante y devuelve `10.66666656003499` donde la respuesta
es `32/3`. certo resuelve en flotante, **reconstruye racionales y verifica en
`Fraction`**, aceptando solo si la comprobación exacta pasa, así que una mala
reconstrucción se rechaza sola.

```
$ certo verify out/lp.json
VÁLIDO  certificado lp_dual (verificado sin solver)
  [ok] dualidad fuerte exacta (c.x == b.y)  (c.x=25/2 | b.y=25/2)
  aritmética racional EXACTA, sin tolerancias
```

`--no-exact` salta la reconstrucción; el certificado queda en punto flotante y
`verify` lo marca como **no citable**.

`--target` responde la pregunta que una demostración de existencia tiene de
verdad —*¿se alcanza esta cota?*— y el objetivo viaja en el certificado, así
que `verify` repite la comparación. Quedarse corto es un **aviso sobre un
certificado válido**, no invalidez: el certificado es correcto y la cota es
insuficiente, y son afirmaciones distintas.

`loads=[...]` declara regiones nombradas que el diseño debe respetar, y el dual
las tarifica: ver [Cargas locales](CASES.md#cargas-locales).

`--gap` sobre un `PackingSpec` reporta `mu*` (la relajación), `nu` (el valor
entero alcanzado) y la distancia entre ambos, como **un** artefacto en vez de
dos corridas que restar: dos ficheros en una carpeta no pueden afirmar que
hablan del mismo empaquetamiento.

Las dos mitades las construye `--gap` mismo, diga lo que diga la bandera
`integer` del spec, porque eso es lo que un gap ES. A un spec que se declara
entero se le construye igualmente su mitad fraccionaria, y `relaxed_for_gap` en
el resultado lo dice en vez de hacerlo callando. (Hasta la 0.11.6 la mitad
fraccionaria se heredaba del spec, así que `integer=True` comparaba el óptimo
entero consigo mismo y reportaba **gap 0** —la conclusión más fuerte que existe
en este dominio— por una combinación de banderas.)

Con `--target`, el número se compara contra `nu` y el resultado lleva `reached`
y `deficit`. Un objetivo no alcanzado **refuta** solo cuando el óptimo entero es
global; por debajo de eso `nu` es un punto que alguien encontró, y «no llegamos»
no es «no se puede llegar». El veredicto distingue los dos casos.

`meta.objective` lleva el óptimo bajo el mismo nombre que usa `opt` para el
mismo número, así que un script lee las dos rutas igual.


### `certo mixed`

**Pregunta** — …y ¿es realmente óptimo sobre los enteros?
**Spec** — `LPSpec` con variables que llevan `kind="binary"` o `kind="integer"`
**Responde** — un esqueleto discreto de una búsqueda, un LP residual sobre la
parte continua certificado exactamente, y tres números que se mantienen
separados
**Certificado** — `mixed_design`, **sin solver**: aritmética exacta
**No establece** — que la elección discreta fuera óptima, salvo que `achieved`
alcance `bound`. Cuando no lo hace, el banner dice **LA OPTIMALIDAD GLOBAL NO
SE AFIRMA**.

| | Qué es |
|---|---|
| **achieved** | lo que esta construcción alcanza. Exacto, y una cota **inferior** genuina del óptimo verdadero, porque la cosa existe |
| **conditional** | lo mejor que la parte continua puede hacer **con este esqueleto**, del dual exacto del LP residual |
| **bound** | la relajación sobre **todos** los esqueletos: una cota **superior** |

Cuando `achieved` alcanza `bound`, la optimalidad global del MILP queda
certificada gratis.

Tres niveles viajan con el certificado, nombrados: `feasible`,
`conditional_optimum`, `global_optimum`.

`--freeze mi_solucion.json` acepta un esqueleto de HiGHS, Gurobi, algo a medida
o una persona. Se redondea y comprueba exactamente igual que cualquier otro,
así que de dónde vino no cambia nada de lo certificado —y que vino de fuera
queda registrado. Exigir que el CBC de certo reprodujera una construcción que
ya existe pondría los límites de certo por delante de ella.

Tratamiento completo en [Casos trabajados](CASES.md#diseños-mixtos).

### `certo bisect`

**Pregunta** — ¿Dónde está el umbral de esta constante?
**Spec** — `BisectSpec`
**Responde** — el par que acota el umbral, cada lado certificado
**Certificado** — `bisect`; la libertad de solver depende de sus hijos
**No establece** — monotonía en el parámetro. Se **supone**; se comprueban los
extremos y se avisa si se portan mal, pero la monotonía misma no se demuestra.

`build(t)` puede devolver un **`CNFSpec`**, no solo un `Spec`, y así es como
`bisect` responde *«¿cuál es el conjunto más pequeño que arregla esto?»* — los
mínimos vértices que borrar, cláusulas que quitar, aristas que eliminar. Para un
`CNFSpec`, «se cumple» significa **UNSAT**: no existe objeto de ese tamaño. Ver
[**El conjunto más pequeño que arregla esto**](CASES.md#el-conjunto-más-pequeño-que-arregla-esto).

Úsalo en vez de un bucle sobre `cases`. Un `for k in ...` que pare en el primer
SAT lee `unknown_solver` como `unsat` y reporta un umbral que no lo es; dos
personas escribieron exactamente eso con un día de diferencia y las dos
obtuvieron un número falso. `bisect` lleva tres estados y se detiene ante el
sondeo inconcluso en vez de elegir un lado.

### `certo bounds`

**Pregunta** — ¿Es cierta esta desigualdad numérica? (`e`, `log`, `π`, `ζ`)
**Spec** — `BoundSpec`
**Responde** — un encierro riguroso en racionales exactos, y si resuelve la
afirmación
**Certificado** — `ball`, **sin solver para la afirmación**; el intervalo mismo
necesita el spec y el mismo backend
**No establece** — que una cantidad sea no nula cuando de hecho es cero. Ningún
encierro lo demostrará nunca, y quedarse sin precisión se reporta como
`resource_exhausted`, no como refutación.

`prove` y `farkas` son exactos pero algebraicos. En cuanto una demostración
dice "esta constante está por debajo de 0.4" y la constante lleva `e` o `ζ`,
ninguno la ve, y "lo calculé y salió 0.397" no es una afirmación sobre nada. Un
encierro sí.

```
$ certo bounds examples/bounds_constant.py
DEMOSTRADO  [unsat]
  el valor es < 0.866 -- establecido rigurosamente a 64 bits
  encierro: [0.8652559794322651, 0.8652559794322651]  ancho 3.062e-19
```

**La precisión es el presupuesto de trabajo**, exactamente como `rlimit` lo es
para Z3: la búsqueda empieza en `prec` bits y duplica hasta que el encierro
resuelve la afirmación. La aritmética de bolas pierde exactitud en las
cancelaciones, así que cuánta precisión necesita una expresión es una propiedad
de la expresión, no de la respuesta.

**Los flotantes se rechazan.** `0.1` no es un décimo, es
`3602879701896397/2^55`, y un encierro construido a partir de él sería
perfectamente riguroso sobre el número equivocado. Así que
`value=lambda m: m.pi * 0.5` lanza y `m.pi * m("1/2")` está bien. Es la única
forma en que la garantía podría perderse en silencio, así que es lo único que
detiene la ejecución.

| Backend | Cubre |
|---|---|
| `python-flint` (Arb) | todo lo de abajo, más `gamma`, `lgamma`, `digamma`, `zeta`, `erf`, `erfc`, las inversas e hiperbólicas |
| `mpmath.iv` | `exp`, `log`, `sqrt`, `sin`, `cos`, `tan`, `gamma` |

El backend queda registrado, porque una cota vale lo que vale lo que la
produjo. Pedirle `zeta` a `mpmath.iv` lo dice en vez de caer a una evaluación
no rigurosa.

Omite `claim` para **medir** en vez de decidir.

### `certo order`

**Pregunta** — ¿DECAE este término en `n`, o es Θ(1)?
**Spec** — `OrderSpec`
**Responde** — el exponente principal, y los términos agrupados por exponente
**Certificado** — `asymptotic`, **sin solver**: aritmética exacta
**No establece** — la constante. `≍` esconde un factor, así que un término
Θ(1) con coeficiente 1e-9 puede estar perfectamente bien en la práctica.

Hay errores que no son infactibilidades. Un usuario tenía
`5|k| W C² / (u³ d² p¹⁰)` con `d ≍ n²`, `C ≍ n`, `|W| ≍ n²`, y preguntaba si
decae. No decae —es **Θ(1)**— y ese error era invisible para Lean *y* para
`certo prove`, por la misma razón: es una factibilidad que no mejora con `n`,
así que un solver al que preguntas "¿es satisfacible?" dice que sí para
siempre, correctamente, mientras la cota en la que vive nunca mejora.

```
$ certo order examples/order_decay.py --expect decays
REFUTADO  [sat]
  REFUTADO: afirmaste que decae, y es Theta(1) -- el exponente principal en n
  es 0
```

Lo que lo hace certificado y no cálculo es que **la sustitución queda
escrita** en vez de hecha en la cabeza de alguien, y que la agrupación es
exacta: dos términos que comparten el exponente superior y cuyos coeficientes
se cancelan realmente se cancelan.

No puedes dividir por una suma —`1/(x + y)` tiene un orden que depende de cuál
domine— y un símbolo sin entrada en `orders` es un **error**, no un supuesto.

**`relations=` deriva los exponentes en vez de pedirlos.** Seis números
sacados mentalmente de `|E| <= Lmass`, `C >= n`, `d' >= C(n,2)` son seis
ocasiones de equivocarse, y una entrada mal da una respuesta limpia y falsa:

```python
OrderSpec(expression=..., orders={},
          relations=["E ~ n**2", "tC ~ 1", "Lmass ~ E * tC",
                     "C ~ n", "dp ~ C**2"])
```

Cada relación es **lineal en los exponentes** —`E ~ n**2` es `exp(E) = 2`,
`Lmass ~ E * tC` es `exp(Lmass) = exp(E) + exp(tC)`— así que el sistema es un
programa lineal, resuelto exactamente. La variable de crecimiento queda fijada
en uno: es la escala, no una incógnita.

**Refusa en vez de adivinar.** El núcleo de Laurent necesita un número por
símbolo y un intervalo no lo es, así que unas relaciones que dejan un símbolo
acotado por un solo lado se refusan nombrando el intervalo: `Lmass en
[1, +inf)` dice qué cota falta, y *no se puede inferir* no lo dice.

Alias: `certo asymptotics`, `certo decays`.

### `certo reduce`

**Pregunta** — Esto es simétrico. ¿Puedo resolver una variable por órbita?
**Spec** — `SymmetrySpec`
**Responde** — las tres hipótesis del argumento de promediado, comprobadas, más
el programa cociente
**Certificado** — `symmetry_reduction`, **sin solver**
**No establece** — de dónde salió el grupo. nauty lo calcula, un paper lo
enuncia, tú lo escribes.

Cinco ejemplos de este repositorio empiezan con un programa simetrizado, y el
paso que los lleva ahí siempre es alguna versión de *"promediando sobre el
grupo de automorfismos, puede suponerse una solución óptima constante en cada
órbita"*. Todo lo que viene después está certificado; esa frase no lo estaba, y
carga peso: **si el grupo está mal, el programa reducido es otro programa** y
cada número posterior es sobre otra cosa.

El argumento tiene exactamente tres hipótesis, y dado un conjunto generador las
tres son comprobaciones finitas:

| Hipótesis | La comprobación | Por qué hace falta |
|---|---|---|
| la acción permuta las variables | cada generador es una biyección | si no, no hay grupo |
| el conjunto de restricciones es invariante | σ(fila) es una fila, mismo sentido, mismo lado derecho, mismas cotas | para que toda imagen de un punto factible sea factible |
| el objetivo es invariante | `c[σ(v)] = c[v]` | para que el promedio tenga el mismo valor |

Un generador que falle cualquiera se **rechaza por nombre**. Un grupo
equivocado no da una reducción más débil, da una equivocada. Un grupo *menor*
siempre es correcto y solo menos útil.

`--parametric` hace la misma pregunta sobre una **familia**: órbitas cuyas
multiplicidades son polinomios, filas que existen solo bajo condiciones
declaradas, y regímenes derivados en vez de listados. Ver
[Simetría paramétrica](CASES.md#simetría-paramétrica).

### `certo quotient`

**Pregunta** — Tengo una partición de este programa. ¿El cociente tiene los
mismos valores alcanzables?
**Spec** — `EquitableQuotientSpec`
**Responde** — los datos de clase, ambas regularidades, y los dos mapas
**Certificado** — `equitable_quotient`, **sin solver**: conteo exacto
**No establece** — que la partición sea la que usa tu argumento. Eso lo afirma
el spec.

Donde `reduce` comprueba un argumento de promediado, esto comprueba una
*equivalencia constructiva*: `Proj` lleva un punto del programa físico al
cociente y `Lift` vuelve, y el certificado lleva ambas regularidades
—`N_i · H_ij = M_j · B_ij`— en vez de una, porque son números distintos y
confundirlos da una respuesta equivocada con confianza.

### `certo matrix`

**Pregunta** — ¿Cuál es el rango, el determinante o la forma de Smith de esta
matriz entera — exactamente?
**Spec** — `MatrixSpec`
**Responde** — rango, determinante, forma normal de Hermite o de Smith, con las
transformaciones unimodulares **y sus inversas**
**Certificado** — `integer_matrix`, **sin solver**: multiplicación de matrices
enteras
**No establece** — que la matriz que escribiste sea la matriz de la que habla
tu paper. La matriz de incidencia correcta, la base correcta, la orientación
correcta: eso lo afirma el spec, y es exactamente donde un cálculo deja de ser
sobre la matemática.

```
U · A = H          U unimodular, H en forma normal de Hermite
U · A · V = S      U, V unimodulares, S la forma normal de Smith
```

Cada afirmación se vuelve una multiplicación:

| De | Se sigue |
|---|---|
| `U · U_inv = I` | det(U) es +1 o −1, y nada más |
| `U · A = H` | A y H generan el mismo retículo de filas |
| H escalonada con r pivotes | rango(A) = r, porque U es invertible sobre ℤ |
| la diagonal de H | \|det A\|, y con el signo de det(U), det A |
| S diagonal, sᵢ \| sᵢ₊₁ | los factores invariantes, o sea la torsión de ℤⁿ / A ℤᵐ |

**El signo es la parte interesante.** `U · U_inv = I` fija la magnitud de
det(U) y no dice nada sobre cuál signo —y ese signo *es* el signo de det(A).
Recalcularlo sobre ℤ costaría lo que cuesta la eliminación. No hace falta:
det(U) ya se sabía ±1, y esos dos son distintos módulo cualquier primo impar,
así que un determinante de U módulo un primo de tamaño de palabra lo zanja. No
probablemente — **exactamente**, porque solo había dos candidatos.

`rows` y `cols` seleccionan una submatriz primero, así que un **menor** es la
misma pregunta sin maquinaria aparte. Las entradas deben ser enteras: `2.5` se
rechaza en vez de redondearse. El rango se decide contando pivotes, no
comparando un valor singular contra un épsilon —sobre ℤ no hay épsilon que
elegir ni que defender.

`certo lint` avisa antes de que Smith corra: 10 000 entradas es una nota,
40 000 un aviso. Un Smith de 64×64 tarda unos 2 segundos; uno de 80×80, unos 6.

### `certo cone`

**Pregunta** — ¿Es este cono regular, de altura uno, y subdividirlo es
crepante?
**Spec** — `ConeSpec`
**Responde** — primitividad por generador, la multiplicidad, el funcional de
altura `u` con `⟨u,v⟩ = 1`, y la discrepancia `⟨u,w⟩ − 1` de cualquier rayo que
nombres
**Certificado** — `toric_cone`, **sin solver**: determinante y resolución
exactos
**No establece** — la geometría. Que multiplicidad uno dé una carta lisa, que
discrepancia cero dé una modificación crepante, que una fibra sea SNC o
reducida: eso son teoremas sobre variedades, y un certificado que los afirmara
en silencio sería la sustitución que este proyecto existe para rechazar.

**El retículo se declara, nunca se adivina, y cambia la respuesta.** Una celda
real con generadores `(4,0,0,0)`, `(2,2,0,0)`, `(2,0,2,0)`, `(1,1,1,1)` tiene
multiplicidad **16** leída en `ℤ⁴` y **1** leída en el retículo en el que sus
generadores son primitivos. Ninguna es un error. Una multiplicidad leída sin su
retículo es media frase, y `verify` lo dice siempre.

**`crepant` es una pregunta sobre lo que una subdivisión añade.** La
discrepancia de un generador es cero *por construcción* dondequiera que exista
un funcional de altura —eso es lo que dice `⟨u,v⟩ = 1`. Sin subdivisión
nombrada la respuesta es `None` y no un `True` vacuo.

Un cono no simplicial igual recibe respuesta: la multiplicidad ausente se
registra con su razón, en vez de rechazar el certificado y perder las otras
tres cantidades.

### `certo range`

**Pregunta** — ¿Hasta dónde llega esta variable — el intervalo entero, no un
punto?
**Spec** — `Spec`, con `--var` nombrando la variable
**Responde** — el `min` y el `max` racionales exactos sobre el régimen, cada
uno con la combinación no negativa de hipótesis que lo da
**Certificado** — `variable_range`, **sin solver**: sumar fracciones
**No establece** — nada sobre la **afirmación** del spec, que nunca se lee.
Esto acota la variable sobre las hipótesis: el régimen, no el teorema.

`check --hypotheses-only` exhibe un *punto*. Eso responde si el régimen está
habitado y nada más, y un usuario que necesitaba `a <= 1/3` obtuvo `a = 0` y
dedujo el resto a mano.

```
$ certo range examples/variable_range.py --var a
SATISFACIBLE  [sat]
  a recorre [0, 1/3], y ese es el intervalo entero -- no un punto suyo
  a <= 1/3
    cheb x 1/3
```

Los multiplicadores **son** la prueba: `1/3` por la fila `3a - 1 <= 0` da
`a <= 1/3`, y la dualidad LP dice que ninguna combinación da una más ajustada.

**Las variables son libres.** Un régimen no es un empaquetamiento —`a` puede
ser negativa— y un dual derivado bajo `x >= 0` certificaría una cota que no
vale. La restricción dual es una igualdad justo por eso.

**Un extremo no acotado lleva un rayo, o no queda establecido.** `max x` sobre
un poliedro es no acotado exactamente cuando el poliedro es no vacío *y* alguna
dirección `d` cumple `A d <= 0` con `d[x] > 0`: desde cualquier punto factible
puedes caminar por `d` para siempre. Ese `d` viaja en el certificado y `verify`
lo camina contra cada fila.

Sin él, `unbounded` es una palabra y no una afirmación — y eso fue hasta 0.11.2.
Un payload editado para decir `unbounded` verificaba tan contento, y `[0, 1]`
volvía como `[0, +inf)`: el único extremo sin evidencia adjunta era el único que
nadie miraba. Un certificado emitido antes de 0.11.2 con un extremo no acotado
no verifica, porque afirma algo de lo que nunca llevó la evidencia.

**Un régimen vacío es su propia respuesta, no un intervalo infinito.** Sobre un
régimen vacío toda dirección es no acotada, y leer eso como *la variable recorre
todo* es el error de aspecto permisivo, así que la habitación se pregunta
primero — y un rayo sobre un poliedro vacío no establece nada, que es por lo que
se comprueban ambas mitades.

**Una fila estricta que ata deja el extremo abierto**: `a < 1/3` y `a <= 1/3`
tienen el mismo supremo y solo uno lo contiene.

Solo hipótesis lineales. Una no lineal se refusa por nombre en vez de
descartarse, porque descartarla *ensancharía* el rango — equivocado en la
dirección que parece segura.

### `certo cycle`

**Pregunta** — ¿Depende este parámetro de sí mismo — y puede cerrar el ciclo
siquiera?
**Spec** — `CycleSpec`
**Responde** — la cadena, la clase de crecimiento de cada paso, y la única
comparación que la cierra
**Certificado** — `dependency_cycle`, **sin solver**: aritmética de clases
**No establece** — que tus clases de crecimiento sean las reales. Que `k`
crezca como una torre lo dice tu lema; esto comprueba lo que se sigue de ello.
Y un ciclo que esta vía no refuta vuelve como *no establecido*, nunca *no hay
ciclo*.

Tres líneas inocentes, ninguna de las cuales menciona un ciclo:

```
k     >= tower(1/delta)        la cota del lema de regularidad
rho   <= K / (3 k**2)          lo que deja el conteo grueso
delta <= rho                   Chebyshev
```

Lo hay —`delta -> k -> rho -> delta`— y componer las cotas da
`delta <= K/(3 tower(1/delta)**2)`, cuyo lado derecho se anula más rápido que
cualquier potencia de delta.

```
$ certo cycle examples/dependency_cycle.py
DEMOSTRADO  [unsat]
  el ciclo delta -> k -> rho -> delta no puede cerrar: ningún delta positivo
  lo sobrevive
```

**La clase es el argumento, no un sustituto suyo.** Encontrarlo a mano obliga a
inventar un suplente que un solver pueda ver —`k >= 1/delta` fue el que se
usó— que demuestra algo estrictamente más débil y deja la torre sostenida en
prosa.

**La monotonía se rastrea.** `rho <= K/(3k**2)` acota rho por arriba solo
porque el mapa *decrece* en `k`, y lo disponible es una cota inferior de `k`.
Una arista cuyo lado disponible no sostiene la dirección necesaria se **refusa
por nombre**: componerla igualmente podría declarar vacío un régimen vivo, que
es el único error que esto no debe cometer.

La escalera es `const < poly(d) < exp < tower`, y `exp` de un argumento que *se
anula* es una constante y no crecimiento — reclamar un nivel ahí cerraría un
ciclo que no cierra.

### `certo solve`

**Pregunta** — ¿Qué resuelve exactamente este sistema lineal — y si nada lo
hace, por qué?
**Spec** — `LinearSystemSpec`
**Responde** — la solución sobre ℚ o ℤ, una base del núcleo cuando está
indeterminado, o una obstrucción cuando no hay ninguna
**Certificado** — `linear_system`, **sin solver**: un producto matriz-vector
**No establece** — que la solución sea **no negativa**, ni sobre ℚ que sea
**entera**. Una solución racional de las ecuaciones de un empaquetamiento no es
un empaquetamiento.

El certificado es casi vergonzoso: es la solución, y comprobarlo es un
producto. Ese es el punto. Un número de una biblioteca numérica es un número
del que *fiarse*; `x` con `A` y `b` al lado es un número que se **multiplica**
—y contra el sistema que se *enunció*, no contra el que alguien recuerda haber
enunciado.

**Lo irresoluble también se certifica:** `y` con `y·A = 0` y `y·b ≠ 0`, que es
una operación de fila que la eliminación ya hizo, guardada en vez de tirada.

**Lo indeterminado no se redondea a "una solución".** Una solución particular
más una base del núcleo dice cuál es el *conjunto* solución. Reportar un punto
de un subespacio afín como si fuera la respuesta es como desaparece un
parámetro libre de un texto.

**Sobre ℤ decide la forma normal de Smith**, y "no hay solución entera" es una
respuesta distinta de "no hay solución". La matriz de incidencia
arista-triángulo de `K₄` con `y` todo unos da `(½,½,½,½)` sobre ℚ y *nada*
sobre ℤ, bloqueada por el último factor invariante.

### `certo parametric`

**Pregunta** — Lo comprobé para `p = 5..12`. ¿Vale para TODO `p`?
**Spec** — `ParametricSpec`
**Responde** — una cota demostrada para toda la familia, desde un solo dual
**Certificado** — `parametric_bound`, **sin solver**: expandir y leer signos
**No establece** — nada por debajo del suelo, nada sobre un óptimo entero, y
nada en absoluto si falla. El test de desplazamiento es **suficiente y no
necesario**, así que un fallo significa *no establecido por esta vía*, nunca
*falso* —y **no se emite certificado**, porque una vía que no funcionó no es
una cota.

Para un programa lineal cuyos datos son polinomios en un parámetro, la dualidad
débil está disponible simbólicamente: cualquier `y ≥ 0` con `A(p)ᵀy ≥ c(p)` da
`opt(p) ≤ b(p)·y` para todo `p` a la vez.

```
$ certo parametric examples/parametric_bound.py
DEMOSTRADO  [unsat]
  para todo p >= 10, el óptimo es como mucho 1/6*p^2 + 1/6*p - 2/3
  y eso es todo valor con p >= 10 -- no una muestra de ellos
```

Y no es floja: en `p` = 10, 11, 15, 30 la cota iguala al óptimo. **Un dual,
leído de una sola instancia resuelta en `p = 10`, da el óptimo exacto para todo
`p` por encima.**

certo no busca `y`. `certo opt` sobre una instancia te da uno; lo que esto
comprueba es que el `y` que ya tienes sirve para toda la familia, y esa
comprobación es aritmética: sustituye `p = p₀ + u`, expande, lee los signos.

`sense="min"` con filas `≥` es la forma **recubrimiento**, que acota por abajo
desde un empaquetamiento factible. Dos cosas cambian y ambas son forzadas: el
dual de un recubrimiento es él mismo un empaquetamiento, así que una entrada
del dual puede ser un polinomio; y un umbral en la función de valor *es* la
factibilidad del dual agotándose. Ver
[De dónde salió parametric](CASES.md#de-dónde-salió-parametric).

### `certo peak`

**Pregunta** — Lo resolví para `n = 1..40`. ¿Qué entero es el mejor para TODO
`n`?
**Spec** — `PeakSpec`
**Responde** — el maximizador entero y el valor ahí, para toda la familia
**Certificado** — `integer_peak`, **sin solver**: expandir y leer signos
**No establece** — nada para un maximizador con coeficientes no enteros, que se
**rechaza** en vez de suponerse entero. Un argumento sobre un punto que no
existe no demuestra nada.

Un texto llega a la respuesta así: completa el cuadrado, observa que el
objetivo es entero en argumento entero, concluye que el máximo es el **suelo**
del pico continuo. Cada paso es correcto y ninguno es comprobable, porque el
suelo de una expresión paramétrica no es un polinomio: no hay nada que
expandir.

Mueve en cambio el origen al maximizador afirmado `x*`. Para cualquier paso
entero `t`, `q(x* + t) − q(x*) = A t² + q'(x*) t`, que para `A < 0` es `≤ 0`
para todo entero `t` no nulo **exactamente cuando** `A ≤ q'(x*) ≤ −A`. Dos
desigualdades polinomiales, comprobadas con el mismo desplazamiento que usa
`parametric`. Ningún suelo en ninguna parte.

`x*` es entero, así que el valor **se alcanza**: el certificado dice que ningún
entero lo supera *y* que este entero llega ahí.

### `certo entry`

**Pregunta** — ¿Dónde cruza esto la línea por primera vez — y por cuán poco?
**Spec** — `EntrySpec`
**Responde** — el índice del primer cruce, el valor ahí, y los dos términos que
lo acotan
**Certificado** — `first_entry`, **sin solver**: racionales exactos
**No establece** — que la sucesión sea la que querías. El prefijo lleva los
valores hasta el cruce y nada más allá, porque nada más allá es parte de la
afirmación.

```
$ certo entry examples/first_entry.py
DEMOSTRADO  [unsat]
  cruza 1/2 por primera vez en el índice 9, donde el valor es 3/5 -- y por
  como mucho la cota de paso, así que dentro de [1/2, 7/10)
```

### `certo moment`

**Pregunta** — ¿El número esperado de eventos malos es menor que uno — así que
existe un objeto bueno?
**Spec** — `MomentSpec`
**Responde** — la esperanza, y la masa que deja
**Certificado** — `first_moment`, **sin solver**: volver a sumar racionales
exactos y comparar
**No establece** — que las probabilidades describan el experimento que querías.
Lo que se comprueba es que *son* probabilidades, que la suma es la suma, y que
la comparación se cumple.

```
$ certo moment examples/first_moment.py
DEMOSTRADO  [unsat]
  E[X] = 15/32 < 1, así que ALGÚN RESULTADO NO TIENE NINGUNO: existe un objeto
  que evita los 15 eventos
```

### `certo ratio`

**Pregunta** — ¿Es cierta esta desigualdad de fracciones para TODO `n`, sin
solver?
**Spec** — `RatioSpec`
**Responde** — el numerador despejado y el signo del denominador
**Certificado** — `ratio_bound`, **sin solver**: multiplicar en cruz, expandir,
leer signos
**No establece** — nada por debajo del suelo. Vale para todo valor del
parámetro en el suelo o por encima y no dice nada por debajo.

```
$ certo ratio examples/ratio_window.py
DEMOSTRADO  [unsat]
  para todo n >= 2: (n - 2) / (n^2) <= (1) / (n)
  diferencia: 2*n
```

### `certo family`

**Pregunta** — ¿Cuál es el mayor de estos diez mil LP — y puede algo superarlo?
**Spec** — `FamilySpec`
**Responde** — el ganador, su valor, y un dual que certifica que nada más lo
alcanza
**Certificado** — `family_extremum`; la verificación reconstruye el programa de
cada ítem desde el spec
**No establece** — que la familia sea la que querías. La completitud de `items`
la afirma el spec, igual que el dominio de un barrido.

### `certo exists`

**Pregunta** — ¿Existe alguno — y si no, puedes demostrarlo?
**Spec** — `CoverSpec`
**Responde** — un modelo, o una refutación DRAT
**Certificado** — `cnf_model` o `drat`, ambos **sin solver**
**No establece** — nada fuera del conjunto de candidatos que diste.

```
$ certo exists examples/no_decomposition.py
DEMOSTRADO  [unsat]
  NO existe recubrimiento exacto sobre estas 9 partes candidatas, para un
  universo de 15. La refutación DRAT lo dice; no necesita solver para
  re-comprobarse
```

---

## ¿Vale para todos los casos?

### `certo sweep`

**Pregunta** — ¿Vale para todo grafo de `n` vértices?
**Spec** — `SweepSpec` para grafos, `DomainSpec` para cualquier dominio finito
**Responde** — el veredicto sobre la familia, **y cuál de tres niveles se
estableció sobre el predicado**
**Certificado** — `sweep` / `domain_sweep`; la libertad de solver depende del
predicado
**No establece** — el teorema. Se comprobó un dominio finito, no todo `n`. Y,
por separado: nada dice que el predicado respondiera bien, salvo que devolviera
certificados.

Esas dos salvedades son independientes, y el banner nombra qué nivel obtuviste:

| Nivel | Qué se sostiene | Cuándo |
|---|---|---|
| **certificado** | cada evaluación lleva su propio certificado; no se confía nada en el predicado | el predicado devuelve `Outcome(ok, cert=...)` **y** `--cert-all` los guarda |
| **reproducible** | el dominio, su hash, y un vector de veredictos: repetir el predicado da las mismas respuestas | un predicado `bool` pelado — el caso común |
| **registrado** | solo el dominio y su hash | el spec no está, se movió, o nunca se selló |

Un banner verde sobre once mil booleanos sin comprobar es donde la formulación
antigua hacía más daño: no hay contraejemplo al que ir a mirar.

`--witnesses` descompone los contraejemplos en órbitas bajo una simetría que
declares. `--collect` mide en vez de refutar, en racionales exactos.
`--n-range 3..8 --stop-on-first` da un subcertificado por tamaño más la
afirmación de que nada falló por debajo del primer fallo. Tratamiento completo
en [Qué establece un barrido](CASES.md#qué-establece-un-barrido).

### `certo cases`

**Pregunta** — ¿Para cada ítem de un dominio finito / es este CNF insatisfacible?
**Spec** — `CNFSpec`, o `DomainSpec`
**Responde** — satisfacibilidad, con una **prueba DRAT** cuando es
insatisfacible
**Certificado** — `drat`, **sin solver**: comprobación RUP/RAT
**No establece** — el teorema. Resuelve el **caso finito**.

El CDCL incorporado es Python y es lento. Existe porque el registro de pruebas
de pysat no funciona en Windows, y sin prueba no hay certificado. Para
instancias grandes: `certo cases spec.py --solver-binary /ruta/a/cadical`.

No hace falta que confíes en ese CDCL. Una prueba malformada la rechaza el
verificador DRUP y obtienes `ERROR`, no `DEMOSTRADO`. **El verificador audita
al solver.**

### `certo shrink`

**Pregunta** — Mi contraejemplo es enorme. ¿Cuál es el de verdad?
**Spec** — `SweepSpec` o `DomainSpec`, con un `reduce`
**Responde** — un testigo minimal, con el descenso registrado
**Certificado** — `shrink_graph` / `mus`; necesita el módulo del spec
**No establece** — que sea mínimo. Da un contraejemplo **1-minimal**, no
mínimo.

Tiene que saber qué significa "un paso más pequeño". Las formas que se repiten
tienen nombre:

| `reduce=` | Hace |
|---|---|
| `"auto"` | elige según el tipo del ítem, o **se niega** |
| `"sets"` | quita un elemento |
| `"sequences"` | quita un elemento de una lista o tupla |
| `"decrement"` | baja una coordenada entera en uno |
| `"graphs"` | borra un vértice |
| `"masks"` | apaga un bit |
| un invocable | lo que escribieras — intacto |

`auto` trata una tupla de enteros como **punto de parámetros**, no como
colección: `(3, 1)` se reduce a `(2, 1)` y `(3, 0)`, no a `(1,)` y `(3,)`. Y se
niega ante un tipo que no reconoce en vez de inventar algo —un testigo minimal
para la relación equivocada se ve exactamente igual que uno minimal para la
correcta.

La traza registra el **índice** tomado en `reduce()` en cada paso, no solo el id
resultante, que es lo que permite a la verificación repetir el descenso exacto
en vez de rehacer la búsqueda.

### `certo sweep --witnesses`

**Pregunta** — Mil fallos. ¿Cuántos objetos son?
**Spec** — `SweepSpec` o `DomainSpec` con `canonicalize=` o `labelling=`
**Responde** — las órbitas de los contraejemplos, y un testigo minimal por
órbita
**Certificado** — `sweep` llevando la descomposición en órbitas
**No establece** — que dos ítems con la misma forma canónica estén realmente en
la misma órbita, cuando pasas `canonicalize`. Eso lo afirma el spec. Pasar
`labelling` lo mueve al lado comprobado.

Un barrido que reporta 1400 contraejemplos donde hay cuatro estructurales no te
ha dicho cuatro cosas y las ha enterrado: te ha dicho una cosa 1400 veces y ha
dejado la lectura a tu cargo.

```
$ certo sweep examples/sweep_orbits.py
REFUTADO  [sat]
  REFUTADO: 10 contraejemplos de 64 examinados -- 10 etiquetados, 3 salvo simetría
  órbitas (de los contraejemplos):
    (1,2,3)   x6   (1,2,3), (1,3,2), (2,1,3)
    (1,1,4)   x3   (1,1,4), (1,4,1), (4,1,1)
    (2,2,2)   x1   (2,2,2)
```

Nada aquí sabe cuál es el grupo, y no le hace falta: le hace falta saber cuándo
dos ítems son iguales. El representante es el de id más pequeño: una regla
arbitraria, pero **determinista**, así que dos ejecuciones nunca producen
certificados que parezcan contradecirse diciendo lo mismo.

La línea de honestidad, y la alternativa que la mueve, en
[Órbitas que puedes comprobar](CASES.md#órbitas-que-puedes-comprobar).

### `certo enum`

**Pregunta** — ¿Qué grafos de `n` vértices hay, salvo isomorfismo?
**Spec** — `SweepSpec`, o flags
**Responde** — la lista canónica y su hash
**Certificado** — `graph_set`, **sin solver**
**No establece** — la **completitud**. El certificado verifica la no isomorfía
y los filtros, no que la familia sean todos.

`filters` acepta invocables junto a los nombrados. Los conteos se mantienen
separados (`enumerated` antes de filtrar, `in_family` después), y `verify` dice
claramente que un filtro programable no puede re-comprobarse solo desde el
certificado, porque vive en el spec.

---

## Álgebra, números y estructuras

### `certo ideal`

**Pregunta** — ¿Tienen solución estas ecuaciones polinomiales?
**Spec** — `IdealSpec`
**Responde** — los cofactores de Gröbner que muestran `1 ∈ I`, o que certifican
`f = Σ hᵢgᵢ`
**Certificado** — `ideal`, **sin solver**: expandir un producto y comparar
coeficientes
**No establece** — nada sobre raíces **reales**. El cuerpo es ℂ. `1 ∈ I` refuta
soluciones sobre ℂ, y por tanto sobre ℝ, ℚ y ℤ; el recíproco no vale.

```
$ certo ideal examples/ideal_inconsistent.py
DEMOSTRADO  [unsat]
  el sistema NO tiene solución común: 1 está en el ideal, y los cofactores lo
  demuestran
  cofactores:
    g0 * (2/7)
    g1 * (2/7*y - 3/7)
    g2 * (-2/7*x - 3/7)
```

Multiplica eso y sale `1`. Esa es toda la demostración. Encontrar los
cofactores es un cálculo de base de Gröbner; una biblioteca que solo dice "sí,
está en el ideal" te deja con su palabra y nada más.

**Decide.** La pertenencia a una base de Gröbner es decidible, así que una
respuesta negativa es `REFUTADO`, no `unknown_solver`. Eso es raro en esta
herramienta y vale la pena usarlo: `prove` sobre un sistema de igualdades
polinomiales puede atascarse donde esto responde.

### `certo eliminate`

**Pregunta** — Quita `t` y dime la condición sobre `s`
**Spec** — `EliminateSpec`
**Responde** — la resultante, con la identidad de Bézout `Res = A·f + B·g`
adjunta
**Certificado** — `resultant`, **sin solver**: expandir dos productos y restar
**No establece** — suficiencia sobre ℝ. `Res = 0` es **necesario** para una
raíz común sobre cualquier cuerpo, **suficiente** sobre uno algebraicamente
cerrado, y solo donde los coeficientes principales no se anulan ambos. `verify`
nombra ese lugar específicamente.

```
$ certo eliminate examples/eliminate_parameter.py
SATISFACIBLE  [sat]
  eliminada t. Solo existe raíz común donde esto se anula: -4*s^3 + 1
```

Ese ejemplo está elegido para que lo compruebes a mano: sustituye `t² = s` en
`t³ + st + 1` para obtener `2st + 1`, de donde `t = −1/(2s)`, y de vuelta en
`t² = s` sale `4s³ = 1`.

Calcular una resultante es un determinante sobre un anillo de polinomios;
comprobar una es expandir dos productos. El determinante es Bareiss —libre de
fracciones, donde cada división es una división polinomial cuyo resto se
**afirma cero** en vez de suponerse.

Una resultante constante no nula es una refutación, concluyente en la dirección
fuerte y al coste de un determinante.

**Dos definiciones de la misma cantidad son esta pregunta.** Un primer momento
que fija `A m = P6 t^4` y un segundo que fija `A^2 m = P11 t^6` son dos
ecuaciones para una `A`, y si concuerdan es la resultante del par en `A`:

```
$ certo eliminate examples/overdetermined.py
  eliminada A. Solo existe raíz común donde esto se anula:
  m*P6^2*t^8 - m^2*P11*t^6
```

que factoriza como `m t^6 (P6^2 t^2 - m P11)`, así que fuera de los casos
degenerados la condición de compatibilidad es `P6^2 / P11 = m / t^2` --la
identidad que produce un argumento de doblado, recuperada en vez de supuesta.
Una incompatibilidad hallada así se halla ahora, no cuando la formalización se
niega a cerrar.

**Exactamente dos polinomios**, porque eso es una resultante. Iterarla por
pares sobre un sistema mayor introduce factores extraños que nada aquí podría
certificar como espurios; tres definiciones de una cantidad es una pregunta de
pertenencia a un ideal, y `ideal` es el comando para eso.

### `certo sos`

**Pregunta** — ¿Es este polinomio no negativo en todas partes?
**Spec** — `SOSSpec`
**Responde** — cuadrados racionales exactos
**Certificado** — `sos`, **sin solver**: expandir un producto
**No establece** — negatividad, nunca. Desde grado 4 en 3 variables hay
polinomios no negativos que no son sumas de cuadrados —el de Motzkin es el
estándar— y `certo sos` vuelve con `unknown_solver` sobre él, nunca con "el
polinomio se va a negativo".

El proceso: escribe `p = zᵀGz` (una condición lineal sobre `G`), encuentra una
`G` numérica por proyecciones alternadas sobre ese subespacio y el cono PSD,
redondéala, **proyecta de vuelta al subespacio exactamente en `Fraction`**, y
haz un LDLᵀ exacto. Si cada pivote es no negativo, la descomposición *es* la
suma de cuadrados. Los flotantes fueron la búsqueda; nunca llegan al
certificado.

Para grado 2, `farkas --nonlinear` es más barato y llega antes.

### `certo number`

**Pregunta** — ¿Es primo este entero?
**Spec** — `NumberSpec`, o `--n`
**Responde** — un certificado de Pratt, o una factorización con
`--question factor`
**Certificado** — `number`, **sin solver**: exponenciación modular
**No establece** — nada más allá de la primalidad de lo que preguntaste.

`n.is_prime()` es cierto, rápido y no citable. Un certificado de Pratt es el
mismo hecho con la evidencia adjunta: `n` es primo exactamente cuando algún `a`
genera `(ℤ/n)*`, y esos factores primos de `n−1` también necesitan
certificados, así que la cosa es un **árbol** que recurre hasta 2.

Tres detalles que separan un certificado de un test:

* **La lista de factores debe estar completa.** Omitir un factor primo de `n−1`
  dejaría pasar un compuesto, así que `verify` comprueba que los factores
  multiplican de vuelta a `n−1` antes de mirar el testigo.
* **Números de Carmichael.** 561 pasa la condición de Fermat para la mayoría de
  bases; la condición de orden lo atrapa, y `certo number --n 561` vuelve
  `REFUTADO` sin certificado.
* **El testigo es reproducible.** Las bases pequeñas se prueban en orden y no
  al azar, así que el mismo `n` da el mismo certificado —y el mismo digest— en
  cualquier máquina.

### `certo cover`

**Pregunta** — ¿Es esto realmente una partición en cliques, y de qué tamaño?
**Spec** — `CoverSpec`
**Responde** — cada parte comprobada como clique, cada elemento contado
exactamente una vez, y con `--optimize --prove-optimal`, a qué distancia queda
del mínimo
**Certificado** — `exact_cover`, **sin solver**: conteo
**No establece** — minimalidad, salvo que la pidas. Un certificado de
recubrimiento es una cota **superior**.

Esa última línea le costó trabajo real a alguien: un usuario leyó uno como si
fuera un óptimo, reportó una construcción de 780 partes donde la obvia usa unas
41, y llamó a la diferencia una propiedad del grafo en vez de un hecho sobre su
construcción. Nada en el certificado estaba mal; la mitad que faltaba era la
cota inferior.

```
$ certo cover examples/cover_optimize.py --optimize --prove-optimal
  y a qué distancia queda del mínimo:
    tu recubrimiento 21 partes  (una cota SUPERIOR, certificada arriba)
    relajación       7   (una cota INFERIOR, dual racional exacto --
                          fraccionaria, así que no es un recubrimiento construible)
    óptimo entero    7   (DEMOSTRADO por ramificación y acotación)
```

Tres números, tres estados, y las etiquetas viajan con ellos.
`CoverSpec(candidates=...)` es **obligatorio** para esto y se rechaza en vez de
adivinarse: un recubrimiento solo es minimal relativo a lo que estabas
dispuesto a usar.

Tres formas de salir mal, reportadas como tres cosas distintas:

| Qué está mal | Qué vuelve |
|---|---|
| una parte no es clique | **no concluyente**, con los pares ofensores nombrados —eso es un enunciado sobre el grafo, no sobre el recubrimiento, y no se escribe certificado |
| una arista está cubierta dos veces | **REFUTADO**, nombrando las aristas, y señalando que `exact=False` haría de los mismos datos un recubrimiento válido |
| una arista está cubierta cero veces | **REFUTADO**, nombrando las aristas |

Encontrar una partición mínima en cliques es NP-duro y deliberadamente no es lo
que esto hace. Trae la tuya, de lo que sea que la encontró.

---

## Construir, ensamblar, conservar

### `certo synth`

**Pregunta** — ¿Existe un objeto con estas propiedades?
**Spec** — `SynthSpec`
**Responde** — el objeto, más los contraejemplos que lo forzaron
**Certificado** — `cegis`; vuelve a resolver
**No establece** — un teorema. `synth` busca sobre un dominio **acotado**, el
banner dice `CANDIDATO SINTETIZADO -- búsqueda ACOTADA`, y eso es un
descubrimiento.

`--prove-candidate` encadena el enunciado general:

```
$ certo synth examples/synth_prove_identity.py --prove-candidate
CANDIDATO SINTETIZADO -- búsqueda ACOTADA  [sat]
    A = 2
    B = -2
DEMOSTRACIÓN SIMBÓLICA UNIVERSAL: PASA  [unsat]
```

El certificado combinado lleva ambas mitades y `verify` comprueba cada una por
separado, porque dicen cosas distintas. El spec tiene que **declarar** cuál es
el enunciado general, porque no es derivable: suele cambiar el dominio *y el
tipo*. La búsqueda corre sobre enteros acotados y la demostración sobre los
reales, que es donde la aritmética polinomial es decidible.

### `certo compose`

**Pregunta** — ¿Cómo ensamblo mis lemas en una demostración?
**Spec** — `ProofSpec`
**Responde** — el teorema, con cada lema o bien **enlazado** o bien nombrado
como **puente**
**Certificado** — `proof`; vuelve a resolver
**No establece** — ningún puente. Un puente se afirma, no se deriva, y se
reporta por nombre **cada vez que la demostración se verifica**.

Un lema dado por `proves=` se descarga y **enlaza**: lo que su certificado
cierra realmente *implica* el enunciado que se pasa al paso final. Un lema
demostrado para `x ≥ 1` y declarado como `x ≥ 2` se rechaza por nombre, en el
punto de ensamblaje, y no se emite nada.

Un lema dado por `certificate=` es un **puente**. Una prueba DRAT habla de
variables proposicionales llamadas `e0_1`; no habla de un número de Ramsey. El
paso de "esta codificación es insatisfacible" a "R(3,3) ≤ 6" es el *significado*
de la codificación, y ningún verificador puede confirmarlo. Así que los puentes
no se rechazan: se hacen visibles.

```
$ certo verify out/proof.json
  [ok] el paso final usa solo los lemas y las hipótesis del propio teorema
  [ok] nada entró en la demostración sin declararse
  AVISO: PUENTE: upper se afirma, no se deriva -- la prueba DRAT cierra...
  AVISO: lemas que el teorema no necesita: spare
```

El puente está en la cabeza del autor de todas formas. La diferencia es si el
lector puede verlo y sopesarlo.

El "NO necesarios" sale del propio núcleo insatisfacible del paso final, no de
una suposición. Espera que atrape más de lo que crees: sobre aritmética real
lineal Z3 rederiva la mayoría de lemas auxiliares por su cuenta, y los que
sobreviven como *necesarios* son precisamente los que llevan algo que la teoría
no alcanza.

Dos lemas *derivados* nunca pueden contradecirse —ambos son ciertos. Solo los
**puentes** pueden, y dos puentes que chocan hacen vacuo todo el teorema, lo
que se reporta por nombre.

### `certo verify`

**Pregunta** — ¿Sigue siendo bueno este certificado guardado?
**Spec** — ninguno; toma una ruta de certificado
**Responde** — cada comprobación, pasada o fallida, más **los avisos repetidos**
**Certificado** — ninguno
**No establece** — que el spec siga coincidiendo. Si el archivo cambió desde
que se emitió el certificado, `verify` lo acepta y avisa: sigue siendo válido
por su cuenta, pero ya no corresponde a lo que hay ahora.

Los avisos son la parte que envejece bien. Una demostración vacua sigue
diciendo que es vacua; un barrido sigue diciendo qué no certificó; una
multiplicidad sigue nombrando su retículo. Meses después, solo con el artefacto.

### `certo bind`

**Pregunta** — ¿Da realmente el lema de Lean lo que supuso mi certificado?
**Spec** — `BindSpec`
**Responde** — si lo que dices que **provee** la declaración implica la
hipótesis sobre la que descansa el certificado
**Certificado** — `lean_binding`; vuelve a preguntar la implicación, así que no
es sin solver
**No establece** — que tu versión de la declaración sea fiel. Nada aquí lee
Mathlib. Es un **puente**, y `verify` lo dice siempre.

El fallo para el que existe: una cota certificada *suponiendo* la estimación
fina de conteo, y un `patCount_K4_le` empaquetado que usa densidad `<= 1` y da
algo inútil — descubierto tres módulos después, yendo a leer el enunciado.

```
$ certo bind examples/lean_binding.py
REFUTADO  [sat]
  PaperIV.MomentErrors.N1_from_counting NO provee lo que fine_count supuso
```

certo lee la procedencia del certificado, carga el spec del que salió, busca la
hipótesis nombrada en `discharges` y pregunta la implicación. Lo que cambia es
**cuándo** muerde —al vincular, mientras miras el enunciado— y que `status`
pueda contarlo.

**Un spec que se movió se reporta obsoleto** en vez de leerse como si no. El
certificado lleva el hash del archivo del que salió, y una vinculación
comprobada contra un enunciado que ha cambiado sería peor que ninguna.

### `certo export`

**Pregunta** — Llévame esto a Lean
**Spec** — ninguno; toma un certificado o un spec
**Responde** — un spec como SMT-LIB2 o DIMACS; un **certificado de Farkas
lineal** como ejemplo `linarith` ejecutable
**Certificado** — ninguno
**No establece** — nada más. `--lean` emite **una** cosa, a propósito.

```lean
theorem from_core (x y : ℝ)
    (x_ge_1 : 1 - x ≤ 0)
    (y_ge_1 : 1 - y ≤ 0)
    : -2 + x + y ≥ 0 := by
  linarith [x_ge_1, y_ge_1]
```

Todo lo demás que certo solía emitir era andamiaje que no compilaba, y un
archivo Lean que no compila es peor que ninguno: cuesta una compilación
descubrirlo. Donde los multiplicadores ya están verificados y `linarith` decide
el fragmento en que vive el objetivo, la exportación es fiable; en todo lo
demás el certificado es el entregable, y lo que una formalización necesita de
él son los números y el enunciado, que están ambos ahí.

`certo status` escanea un directorio en busca de enunciados Lean de la forma
`theorem foo : True := by`, así que un archivo hueco dejado por un flujo
anterior se encuentra en vez de darse por desaparecido.

### `certo ledger`

**Pregunta** — ¿Qué corrí el mes pasado?
**Spec** — ninguno
**Responde** — un registro de solo-añadir, re-verificable
**Certificado** — ninguno
**No establece** — nada; guarda rutas y digests, nunca copias.

```bash
certo opt spec.py --cert c.json --log --note "cota K6" --tag paper
certo ledger verify
```

```
  [ok] 2026-09-16T00:45:23  core     núcleo de 4 fórmulas
  [!!] 2026-09-16T00:45:25  opt      digest 3653579e... != registrado 681631ea...
  2 entradas: 1 verificada, 0 FALLIDAS, 1 cambiada desde que se registró
```

**Solo-añadir**: una ejecución posterior que contradice a una anterior es una
línea nueva, no una edición. **Sin copias**: solo la ruta y el digest de cada
certificado, así que un certificado manipulado o ausente aparece como fallo en
vez de duplicarse silenciosamente en el registro.

---

## Puntos de entrada y contabilidad

### `certo ask`

**Pregunta** — Corre lo que este spec pida, sin más
**Spec** — cualquiera
**Responde** — lo que produzca el comando enrutado
**Certificado** — lo que produzca el comando enrutado
**No establece** — nada extra; el enrutado cambia quién responde, no qué
significa la respuesta.

Un punto de entrada que carga un spec, lee su tipo y corre el comando al que
ese tipo pertenece. `certo what` es el mismo comando.

### `certo commands`

**Pregunta** — ¿Qué comando responde qué pregunta?
**Spec** — ninguno
**Responde** — esta página, en tu terminal, en tu idioma
**Certificado** — ninguno
**No establece** — que un comando listado pueda responder *tu* instancia.
Enruta por la forma de la pregunta, no por si el problema está al alcance.

```
$ certo commands
  ¿CUÁN GRANDE, CUÁN PEQUEÑO, CUÁNTOS?
    certo opt                          ¿Cuál es el óptimo, exactamente?
    certo order                        ¿DECAE este término en n, o es Theta(1)?
```

Esto existe por un fallo que vale la pena registrar. `certo order` salió en
0.5.0 con su propia sección, ejemplo y dos filas de tabla. Un usuario pasó una
sesión escribiéndolo a mano en Python tres veces, y luego lo pidió como *la
única función que querría en 0.7*. Había buscado "asintótico" y "decae"; el
comando se llama `order`.

Así que `certo asymptotics` y `certo decays` ahora lo ejecutan, la línea de
ayuda encabeza con *"¿DECAE este término en n?"* en vez de con el exponente, y
`lint` nombra el comando cuando una afirmación divide por un producto de
símbolos —la forma de una pregunta de magnitud, que `prove` no puede responder.
Ese disparador es deliberadamente estrecho: **dos o más** símbolos distintos con
exponente negativo, porque uno es demasiado común para significar algo. Sobre
los ejemplos publicados dispara cero veces.

`certo what <comando>` hace la misma pregunta sobre un solo comando: su spec,
su motor, el tipo de certificado y el nivel.


### `certo repro`

**Pregunta** — ¿Qué necesita un árbitro para rehacer esto?
**Spec** — ninguno
**Responde** — un paquete: spec, certificados, versiones y hashes
**Certificado** — el paquete mismo
**No establece** — que la máquina del árbitro coincida. Coincidirá, para
nuestros motores; un predicado de `sweep` que llama a scipy queda fuera de esa
garantía.

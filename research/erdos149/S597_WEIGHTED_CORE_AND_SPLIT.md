# Erdős #149 — S597: núcleo ponderado, Hall de raíces, absorción en dos escalas y C13

**Estado: el arco de tres aristas universal sigue OPEN.** Este archivo enuncia
resultados analíticos exactos con sus hipótesis. Los algoritmos finitos sirven
para reproducir casos, NO para sustituir la cuantificación sobre todo grafo.

## Notación

H es un grafo físico simple y finito, masas positivas m_v con
`d_H(v)=sum_{z∼v}m_z≤1` y al añadir el arco `s-u-v-t` con masas `a,b`
se mantienen las filas factibles. Las raíces s,t no son adyacentes ni tienen
vecinos comunes. `x=m_s,y=m_t`, `r_s=x*d_H(s)`, `r_t=y*d_H(t)`.
Sea `K=5/4`, `D=r_s+r_t+ab-K>0`, `1/2<x,y<3/4`, `x+y>K`.
Suponemos el resultado inductivo `Q_H≤K`. El crux universal es obtener
una paleta exacta K de H cuya medida J de colores con ambas estrellas sea
`J≥D`.

Todas las incompatibilidades se miden en el grafo físico H ORIGINAL,
incluso después de eliminar demandas.

## Teorema 1. Hall completo de las estrellas si se consideran solas

Las dos estrellas pueden cubrirse exactamente a ancho
`max(r_s,r_t)` con solapamiento `min(r_s,r_t)`.

Prueba: supongamos `r_s≤r_t` y usemos transporte de demandas
`x m_w` de `sw` hacia `y m_z` de `tz`, permitido si `wz∉E(H)`.
Para `U⊆N(s)` sea `C_U={z∈N(t): wz∈E(H) ∀w∈U}`.
Si C_U vacío, todos los destinos están disponibles: `r_t≥r_s≥xm(U)`.
Si U y C_U no vacíos, la fila de un z∈C_U da `m(U)≤1−y` y
la de un w∈U da `m(C_U)≤1−x`. La demanda del corte es
`xm(U)≤x(1−y)`, y su capacidad es al menos
`r_t−y(1−x)>K−x−y(1−x)≥x(1−y)`.
La última desigualdad vale porque `2x+y−2xy≤K`
para `x,y∈[1/2,3/4]`: como `1−2x≤0`, el máximo en y
ocurre en y=1/2, donde vale `x+1/2≤K`.
Todos los cortes Hall pasan. El caso reflejado es simétrico.

**Importante:** este Hall no dice que las aristas INTERIORES se puedan
reinsertar sin más; ése es precisamente el crux pendiente.

## Teorema 2. Eliminación exacta por carga de conflicto

Sea T cualquier conjunto de demandas antiguas que contiene las dos
estrellas. Para e∈T fuera de ellas defina

`L_T(e)=sum_{f∈T, f=e or f conflictúa fuertemente con e} w_f`.

Si `L_T(e)≤K`, se puede borrar e, resolver todas las restantes
demandas en una paleta exacta K con solapamiento J arbitrario, y
reinsertar e en ancho `w_e` compatible, sin modificar J.

Prueba: en una paleta exacta de T\{e}, el ancho de colores
que contienen alguna arista incompatible con e es a lo sumo
`L_T(e)−w_e` por unión y exactitud. Por tanto los colores
compatibles tienen ancho al menos
`K−L_T(e)+w_e≥w_e`. Subdivida y coloque e. Puesto que e no
toca raíces, las medidas de clases con s,t no cambian.

Iterando hasta que ningún e restante cumpla la regla se obtiene un
**núcleo relativo estable**. Es independiente del orden de eliminación:
el operador de borrar todas las aristas no raíces con carga ≤K
es monótono bajo reducción del soporte; su punto fijo obtenido por
iteración simultánea es el mismo que el obtenido secuencialmente.
Se conserva siempre el grafo físico original al calcular conflictos.

## Teorema 3. C13: criterio de presupuesto del núcleo ANCLADO

En el núcleo relativo sean R todas las demandas de las raíces, y
descomponga el grafo de conflictos restringido a las demandas
SUPERVIVIENTES en componentes. Llame A al conjunto de aristas
interiores de componentes que también contienen alguna arista de R.
Sea `W_A=sum_{e∈A}w_e`.

Si

`max(r_s,r_t)+W_A≤K`,

se puede construir una paleta exacta K con
`J=min(r_s,r_t)≥D`; el arco de tres aristas se reinserta.

Prueba: primero coloree sólo R mediante el Hall del teorema 1, con
ancho `max(r_s,r_t)` y solapamiento `min(r_s,r_t)`.
Pague cada arista de A en banda separada de ancho w_e, total W_A.
Para todas las componentes del núcleo que no contienen R,
restrinja una paleta exacta antigua de H de ancho K que existe
por hipótesis `Q_H≤K`: cada componente obtiene un ancho ≤K.
Son mutuamente compatibles y no chocan con las componentes ancladas
(la separación es en el grafo de CONFLICTOS físicos), por lo que
se pueden superponer sin gasto adicional. Complete con vacío a K.
Finalmente reinserte las aristas eliminadas por el teorema 2.
El solapamiento J permanece exacto.

Si A vacío, **todos los núcleos interiores persistentes desconectados
por conflicto de las raíces son inofensivos**, aunque sean grandes o no
bipartitos. Si A no vacío, C13 cierra siempre que su masa total pague
con el margen `K−max(r_s,r_t)`.

### Testigos exactos C13

- Árbol de 10 vértices, 9 aristas: raíces s,t con masas 7/10,
  cuatro vecinos cada una de masa 19/80 y una arista cruzada entre
  los vecinos s0,t0. Las raíces tienen `r_s=r_t=133/200`,
  `D=33/400`. La cruzada es pesada, persiste en el núcleo relativo
  y está ANCLADA a las dos estrellas, pero
  `W_A=(19/80)^2=361/6400`, y
  `133/200+361/6400=4617/6400<K`. C13 cierra.
- Grafo conectado de 34 vértices y 39 aristas, con un bloque
  de Petersen y un conector de masa 1/2000: tras el peeling persisten
  exactamente sus 15 aristas interiores, pero están en una
  componente de conflictos libre de raíces. Luego W_A=0, C13 cierra.
  `Q_H≤K` puede verse también por la paleta bipartita del árbol
  de ancho ≤1, una 5-coloración fuerte de Petersen de ancho
  `5((1−1/1000)/3)^2<1` superpuesta físicamente, y dos
  aristas del conector en banda separada de demanda <1/1000.
- El grafo 3-conexo de 70 vértices posee 111 aristas interiores
  ANCLADAS y su masa supera el margen: C13 es inconcluso allí.

## Teorema 4. C12: absorción de una clique fuerte protegida

Seleccione una clique fuerte R de aristas antiguas; L sean las demás
aristas antiguas compatibles físicamente con TODAS las aristas de R;
C las demás. Se exige:
(i) el subgrafo H[V(L)] contiene exactamente las aristas L
(sin conectores físicos ocultos entre extremos de L);
(ii) L es bipartito;
(iii) las tres aristas nuevas s-u,u-v,v-t son compatibles con R;
(iv) todas las masas y filas son factibles.

Por el teorema ponderado bipartito S591, L cuesta ≤1.
Coloréelo y reserve porciones separadas para el arco, cuya demanda
total es `w_arc=xa+ab+by`, en ancho `1+w_arc`.
La clique R cuesta exactamente `w(R)` en singletons y puede
SUPERPONERSE completamente con L+arco por compatibilidad física.
Pague cada arista del resto C en una banda adicional de ancho `w(C)`.
Por tanto

`Q_F≤max(1+w_arc,w(R))+w(C)`.             (C12)

Esto es un criterio **suficiente** (no universal) y depende sólo del
teorema bipartito y de comprobaciones explícitas de compatibilidad.

### Familia 3-conexa de PG(2,4)

El generador reproducible `s597_pg4_3conn_hard.py` produce, para todo
racional `0<eps≤1/1000`, un grafo de 70 vértices y 157 aristas, 3-conexo,
grado mínimo 3, no bipartito y con filas factibles. Es una ampliación
del grafo de incidencia del plano proyectivo de orden 4, con dos
estrellas pesadas y un C5 casi saturado.

Aquí x=y=7/10, a=b=1/20, `w_arc=29/400`. En C12:
`|L|=137, |R|=5, |C|=15`,
`c=(1−eps)/2`, `delta=eps/2`,
`w(R)=5c²`, `w(C)=5delta(c+19/50)`.

Para todo `0<eps≤1/1000` se verifica
`5c²≥1+29/400`, y por tanto

`Q_F ≤ 5c²+5delta(c+19/50) = 5/4−3eps/10 <K.`

Además `Q_H≥5c²>K−ab`; las ramas sencillas por
`Q_H≤K−ab`, C10, C11 y C13 no cierran esta familia.
Sin embargo, C12 sí lo hace.

`examples/erdos149_s597_twoscale_budget.py` verifica
la desigualdad paramétrica REAL con Certo (Z3).
`s597_clique_absorb.py` verifica la separación física exacta
y el presupuesto en instancias racionales.
`s597_proof_router.py` combina peeling, C13 y detección C12.

## Frontera universal abierta: un solo gate local

Para cerrar el arco de tres aristas sin más hipótesis resta
demostrar que todo H con Q_H≤K y masas del residuo S591
admite una paleta exacta con `J≥D`, o producir una reducción
a orden menor que conserve exceso estricto. Ni los
criterios de corte C10/C11, ni el núcleo C13, ni la absorción C12
fuerzan universalmente la condición suficiente que emplean.

Un enfoque próximo es derivar un INVARIANTE GLOBAL del LP dual

`Jmax = max{sum_M h(M)c_M: A c=w, 1^T c=K,c≥0}`.

Su dual tiene variables libres `lambda_e,tau` y es

`min K*tau+sum_e lambda_e*w_e`
`    sujeto a tau+sum_{e∈M}lambda_e ≥ h(M)`
para cada matching inducido M físico; `h(M)=1` si M
contiene ambas raíces, cero de otro modo.
El crux equivale a descartar un dual factible de valor <D
cuando `Q_H≤K`.

Esta formulación evita sobrecontar bloqueadores por clases;
también es el objetivo correcto para Certo (exact LP + dual)
y Jacobian (segundo verificador), aunque sin una reducción
universal a tamaño finito los experimentos permanecen finitos.

**Estados globales:** arco de tres aristas OPEN;
arco de dos aristas OPEN; separadores ponderados ramificados
OPEN; núcleo 3-conexo universal OPEN; conversión entera OPEN;
Erdős–Nešetřil #149 OPEN.

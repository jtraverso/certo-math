# Erdős #149 — S595: traslado exacto, saturación pesada y flujo cruzado

**Estado:** demuestra un nuevo criterio SUFICIENTE para el arco de tres aristas
en el régimen S591. **NO cierra el arco universal ni la conjetura.**

Sea F=H+(s-u-v-t) con masas x,a,b,y positivas y filas factibles.
K=5/4, Q_H<=K; la paleta de H es exacta y se completa con vacío hasta K.
Sea r_s=x d_H(s), r_t=y d_H(t),
D=r_s+r_t+ab-K>0; las raíces no son adyacentes y no tienen vecinos comunes.
Para esta rama exigimos x,y en (1/2,3/4), x+y>K (régimen S591).

Elegimos una paleta P que maximiza J, el ancho de colores que contienen
simultáneamente aristas antiguas incidentes a s y t. Si J<D,
escribimos S=r_s-J, T=r_t-J. Como r_s+ab<=x y r_t+ab<=y,
S>K-y y T>K-x. Así S,T>0.

## Lema de traslado **sin hipótesis externa**

Definamos la carga física `ell_H(e)=sum_{f: f=e or f strong-conflicts e} w_f`.
Para una paleta exacta, el ancho ocupado por colores que contienen e o
alguna arista incompatible con e es <=ell_H(e). Por tanto
el ancho de colores compatibles con e es >=K-ell_H(e).

Si ell_H(e)<K, y protegemos dos porciones de tamaño eta, elegimos
`0<3*eta<K-ell_H(e)`. Fuera de las dos porciones siguen existiendo
al menos `K-ell_H(e)-2*eta >eta` colores compatibles. Se retira e
de una porción protegida y se inserta con igual medida en destinos
compatibles, sin cambiar demanda ni presupuesto. Para una lista FINITA
de aristas ligeras escogemos eta menor que todos los márgenes y repetimos;
cada iteración mantiene la paleta exacta y, con ello, la misma cota
`K-ell_H(e)`. Los perfiles de raíz no cambian si las aristas recolocadas
no inciden a s ni t.

## Refuerzo de la sesión 593: cada color exclusivo debe portar un bloqueador cruzado

Sea Z el conjunto de aristas interiores antiguas e (sin s ni t) con
`ell_H(e)>=K`. Para un color exclusivo de s cuyo único borde de raíz
sea r=sw, consideremos las clases exclusivas de t con borde tz.

El ancho de esas clases cuyo tz choca con sw es <=y*c_w, donde
`c_w=sum_{z in N_H(t), wz in E(H)} m_z <=1-x`, pues la fila de w
incluye x. Por `T>K-x>y*(1-x)` (identidad
`K-x-y(1-x)=1/4+(1-x)(1-y)>0`) existe una clase exclusiva de t
cuya arista tz es compatible con sw.

Si la clase de s NO contiene una arista pesada e incompatible con tz,
todos sus conflictos interiores con tz son ligeros. Con el lema previo,
limpiamos una porción eta de esa clase, manteniendo su sw, y trasladamos
tz de una porción eta de su clase t-exclusiva a la s-exclusiva.
Esta sigue siendo un matching inducido; la cobertura de tz es exacta.
La clase receptora obtiene las dos raíces y aumenta J en eta,
contradicción.

Así, TODO color exclusivo de s lleva al menos una arista interior
e∈Z que (i) es compatible con su arista s de raíz y (ii) choca
con alguna arista de la raíz t. Simétricamente para los colores
exclusivos de t.

Esta prueba no necesita que la clase donante sea ligera, no usa
intercambios alternantes y no asume saturación de soportes o minimalidad
global. Sólo usa una paleta exacta óptima, positividad de los márgenes
y la factibilidad de las filas.

## Flujo cruzado exacto (C10)

Definimos una red bipartita capacitada:
- izquierda: todas las aristas de las estrellas antiguas s y t, capacidad w_r;
- derecha: e∈Z, capacidad w_e;
- r=sw se conecta a e sólo cuando e es compatible con sw y es incompatible
  con alguna arista tz de la otra estrella antigua;
- r=tz se conecta a e sólo cuando e es compatible con tz y es incompatible
  con alguna arista sw de la otra estrella antigua.

Sea nu_cross el flujo máximo racional. Por cada color exclusivo de una
raíz elegimos UNA arista pesada cruzada e, y enviamos el ancho de ese
color de r a e. Exactitud de cobertura acota ambos lados. Así

    nu_cross >= S+T > 2K-x-y.                             (S595-C10)

En consecuencia:

    nu_cross <= 5/2-x-y  ==>  J>=D.

Como x+y<3/2, `5/2-x-y>1`; el criterio `nu_cross<=1`
es suficiente uniformemente en el residuo. Este criterio domina C9
para dicho residuo: nu_cross<=nu_Z y
`5/2-x-y > K-max(x,y)`.

Más aún, cada familia individual suministra
`nu_cross,s >= S > K-y` y `nu_cross,t>=T>K-x`.
Por tanto un corte en UNO de los flujos por lado también basta.

El teorema C10 es analítico bajo las hipótesis de S591. Certo `prove`
verifica por separado la desigualdad algebraica de corte de los márgenes,
NO reemplaza la demostración combinatoria que acabamos de escribir.

## La desigualdad dirigida 593.6, ahora sin su anterior condicional

Fijada cualquier arista exclusiva sw, las clases exclusivas de t
incompatibles por sus propias aristas tz ocupan <=y*c_w.
Si tz es compatible con sw pero la clase t-exclusiva no contiene un
interior pesado incompatible con sw, limpiamos sus interiores ligeros y
trasladamos sw a ella, aumentando J. Por tanto cada restante
clase t-exclusiva asigna su ancho a una arista pesada e incompatible
con sw, compatible con tz. La asignación es un flujo de ancho
`nu_t(sw)`, de donde

    T<=y*c_w+nu_t(sw).

El peso de TODAS las aristas interiores incompatibles con sw
(no sólo las pesadas) queda acotado por
`p*(1-x)+(d_H(w)-x)*(1-m_w) <= (1-x)*(p+1-m_w)`.
Para probarlo, separa las que tocan A=N_H(s), usando en cada
z∈A la fila `d_H(z)-x<=1-x`, y las demás que tocan
N_H(w)\\{s}, usando `d_H(z)-m_w<=1-m_w`.

Además, toda estrella de aristas cruzadas `wz`, z∈N_H(t),
ocupa colores sin raíz y exige masa `m_w*c_w`.
Como la reserva sin raíces es `K-r_s-r_t+J<ab`,
`m_w*c_w<ab`. Por `T>K-x`, obtenemos

    1/4 < (1-x)*(p-m_w)+y*ab/m_w.                        (593.6')

La implicación 593.6' queda demostrada sin asumir el lema de traslado
como axioma: arriba consta una demostración directa.

## Consecuencias locales verificadas (siguen siendo casos parciales)

Combinando 593.6' con las demostraciones algebraicas previamente auditadas:
- grado antiguo <=3 en la raíz de mayor masa: reinserción;
- grado antiguo <=4 y x>=7/10: reinserción;
- grado antiguo <=5 y x>=73/100: reinserción.

Estos son cierres **dentro de la rama residual de S591**;
las reducciones iniciales de S591 y el núcleo global no se recertifican aquí.

## Inventario OPEN (sin añadir gates)

1. Arco de tres aristas universal cuando no pasan C10/593.degree.
2. Arco de dos aristas en una misma paleta de tres cortes.
3. Separadores ponderados ramificados de orden dos.
4. Núcleo 3-conexo.
5. Paso exacto de fractional a entero en la ruta ponderada.

Erdős #149 sigue OPEN. Ningún ejemplo finito prueba su cierre universal.


## Auditoría adversarial S595: 2-conectividad + coste casi K no fuerzan C10

El generador `research/erdos149_s595_neartight.py` construye, para
`eps=1/1000000`, un grafo físico H de 617 vértices y 1049 aristas con
x=y=13/20, a=b=1/200 y D=1741/40000>0. No hay articulaciones
(verificado por DFS en `tests/test_erdos149_s595.py`). El flujo cruzado
resulta, con fracciones y mincorte repetido,

    nu_cross = 2587/2000 = r_s+r_t,
    threshold_exact = 2K-r_s-r_t-2ab = 24129/20000 = 1.20645.

Por tanto C10 es INCONCLUSO aunque H sea 2-conexo. También refuta
la hipótesis auxiliar `nu_cross<=1` para grafos 2-conexos.

### Paleta legal y acotación exacta Q_H (incluyendo conectores físicos)

El núcleo consta de un bosque bipartito T y un anillo cíclico de 432
hojas W, agrupadas en 72 bloques consecutivos de seis hojas con el
mismo padre D. Los extremos vecinos del anillo de bloques distintos
introducen nuevos conflictos entre ciertas aristas del bosque;
**no es correcto** aplicar sin más la cota bipartita a T dentro de H.

Eliminamos de T la arista D-W de la **última hoja de cada bloque**.
Las 72 aristas eliminadas forman un solo matching inducido físico,
con máxima demanda `(3/4)*(1/8)=3/32`. En el bosque restante T',
todas las nuevas incompatibilidades debidas al anillo desaparecen:
cada arista del anillo que conecta bloques distintos toca una hoja
cuya arista D-W fue retirada. Por lo tanto, la paleta bipartita de T'
de ancho <=1 sigue siendo físicamente válida en el grafo completo H.

Las aristas del anillo, que tiene longitud 432 divisible por 3, se
dividen por índice módulo tres en tres matchings inducidos físicos,
cada uno con demanda `1/64`. Sumando bandas disjuntas:

    Q_core <= 1 + 3/32 + 3/64 = 73/64 < 5/4.

Un C5 adicional de masas `c=(1-eps)/2` se conecta al anillo mediante
dos caminos disjuntos W--omega--c0 y W'--omega'--c2, con masas
`m_omega=m_omega'=eps`. Para mantener todas las filas <=1, se
reducen las masas de los respectivos padres D,D' en eps. No hay
aristas DIRECTAS entre vértices del núcleo y vértices del C5:
sólo se conectan mediante los omega.

Por ello la paleta del núcleo y la del C5 se pueden **superponer**
(familias físicamente compatibles), dando coste
`max(73/64, 5c^2)=5c^2` para todas las aristas anteriores a los
conectores. Las cuatro aristas de los dos conectores se pagan
en porciones disjuntas adicionales de medida total

    E_connectors = 2eps(c+1/8).

El C5 aporta una clique fuerte de cinco aristas, así que

    5c² <= Q_H <= 5c² + 2eps(c+1/8) < 5/4.

A eps=1/1000000 los valores exactos son

    Q_H >= 999998000001/800000000000,
    Q_H <= 4999995000001/4000000000000,
    5/4-ab = 49999/40000.

Esto da `5/4-ab < Q_H < 5/4`: no se aplica el cierre fácil
`Q_H<=K-ab`.

Se puede incluso reinsertar el arco completo en el ejemplo:
en una banda separada de la paleta del núcleo pagamos las tres
aristas nuevas, por un total
`xa+ab+by=261/40000`. Como

    73/64 + 261/40000 < 5c²,

podemos superponer también el arco con la paleta del C5 (no existen
aristas directas entre esos conjuntos de extremos). Los conectores
siguen pagando exactamente E_connectors. Así

    Q_F <= 5c² + E_connectors < 5/4.

**Importante:** este grafo no es un contraejemplo a Erdős #149 ni un
mínimo ponderado: contiene muchos vértices de grado dos y separadores
de orden dos. Falsifica únicamente la suficiencia de C10 bajo las
hipótesis 2-conectividad y `Q_H>K-ab`. Para cerrar universalmente el
arco hay que imponer compatibilidad simultánea de los bloqueadores
dentro de las paletas, o aprovechar reducciones adicionales.

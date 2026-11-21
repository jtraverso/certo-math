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

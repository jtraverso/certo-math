# Erdős #149 — S598: compresión exacta y localización del dual

**Estado:** dos teoremas universales de REDUCCIÓN, no una demostración de la
reinserción universal del arco de tres aristas. Erdős–Nešetřil #149 OPEN.

## 1. Grafo de conflictos tipado

Dado un grafo físico H, defina C=L(H)^2: los vértices de C son las
aristas de H; dos vértices de C son adyacentes cuando esas aristas son
incompatibles en un matching inducido **del H físico**.
Para cada e=uv de H, su demanda es w_e=m_u m_v.

Cada conjunto independiente I de C corresponde exactamente a un
matching inducido físico de H. Colorear con paleta racional es cubrir
cada tipo e con ancho w_e y ancho total K=5/4. Marcamos el tipo
\`b(e)=(1_{s∈e},1_{t∈e})\`. La función de reserva es

    h(I)=1 si I contiene algún tipo de cada marca de raíz; 0 si no.

**La estructura física sigue siendo necesaria para determinar C.**
No se puede inventar un grafo de conflictos abstracto y asumir que
satisface las filas de masas del modelo físico.

## 2. Teorema S598.A: contracción de gemelas verdaderas de conflictos

Sean e,f dos tipos del soporte con:
(i) e y f son adyacentes en C;
(ii) N_C[e]=N_C[f] dentro del soporte de demandas;
(iii) b(e)=b(f).

Reemplazar e,f por un tipo z con demanda w_z=w_e+w_f, el mismo
conjunto de incompatibilidades y la misma marca, **conserva
exactamente Q y Jmax para TODO K**.

**Prueba, ida.** Un conjunto independiente jamás contiene ambos
tipos e,f. Proyecte cada clase reemplazando cualquiera de ellos por z;
la condición de gemelos asegura que todos los demás tipos permitidos
siguen siendo compatibles. Las coberturas se suman a w_e+w_f,
todos los otros tipos siguen exactos, el ancho y h(I) se conservan.

**Prueba, vuelta.** Para una clase con z de ancho c, divídala en dos
porciones de anchos c*w_e/(w_e+w_f) y c*w_f/(w_e+w_f), reemplazando
z por e o f respectivamente. Si la clase no contiene z, déjela igual.
Las incompatibilidades son idénticas con cada sustituto; se cubren
exactamente ambas demandas y no cambian ancho ni h.
Itere o aplique una distribución producto cuando la clase contiene
varios tipos comprimidos. QED.

La regla sirve también en el núcleo relativo A* de S597, **calculando
los conflictos desde el grafo físico H original y restringiendo sólo
el soporte de demandas**. No borre conectores físicos de precio cero.

Certificado finito reproducible: el núcleo 3-conexo de 18 vértices
y 39 aristas tiene 6 pares de gemelas de conflicto, por lo que su LP
se reduce de 39 a 33 demandas. La paleta exacta de 34 colores se proyecta
al cociente; la reconstrucción produce 62 colores físicos con
Q=5/4 y J=133/200, todas las ecuaciones racionales verificadas.

Script: \`research/erdos149/s598_conflict_twins.py\`.
Prueba: \`research/erdos149/test_s598_conflict_twins.py\`.

## 3. Teorema S598.B: gemelos falsos de vértices físicos

Sean u,v vértices no adyacentes con idéntico vecindario abierto:
N_H(u)=N_H(v). Fusiónelos en z, con m_z=m_u+m_v y
N_{H'}(z)=N_H(u).

**Afirmación:** Q_{H'}=Q_H y la factibilidad de todas las filas
se conserva. Si u,v NO son las raíces distinguidas s,t, también
Jmax_{H'}(K)=Jmax_H(K).

**Filas:** para cualquier vecino a común, su carga antigua contenía
m_u+m_v y su carga nueva contiene m_z; las demás filas siguen
iguales. La fila de z es la misma que las filas iguales de u,v.

**Paletas:** toda clase inducida original puede contener como máximo
una arista incidente a u o v: si contuviera ua y vb (a≠b),
las aristas físicas ub y va producirían conflicto cruzado.
Al fusionar, la clase proyecta a una clase legal de H'.
Recíprocamente, una porción de ancho c con za puede repartirse
en ua y va proporcionalmente a m_u y m_v, sin cambiar los demás
elementos de la clase: u,v poseen idénticas compatibilidades.
El coste y las demandas quedan exactamente preservados. Como las
raíces s,t no se fusionan, la marca h también queda intacta.

**Corolario de minimalidad:** un contraejemplo ponderado Q_F>K
de ORDEN MÍNIMO, con masas positivas, no puede contener dos gemelos
falsos. Si los contuviera, su fusión produciría un contraejemplo de
menor orden con el mismo exceso. No hace falta que m_z<3/4 para
aplicar este corolario; basta la factibilidad, preservada por la fusión.
Es una reducción universal de la selección del contraejemplo, aunque
el grafo 3-conexo PG(2,4) usado en S597 ya carece de tales gemelos.

Script: \`research/erdos149/s598_false_twins.py\`.
Test de ida-vuelta: \`research/erdos149/test_s598_false_twins.py\`.

## 4. Teorema S598.C: localización del dual y masa negativa >1/2

Mantengamos las hipótesis residuales S591/S597:
K=5/4, x,y en (1/2,3/4),
r_s+ab≤x y r_t+ab≤y, D=r_s+r_t+ab-K>0,
Q_H≤K. Sea A* el soporte del núcleo anclado,
obtenido por peeling y componentes de conflictos S597.

Para maximizar la reserva J, el dual del LP con coberturas EXACTAS es

    min K*tau + sum_e lambda_e*w_e
    s.a. tau+sum_{e∈M}lambda_e ≥ h(M)
         para todos los matchings inducidos M,
         tau y lambda_e libres, pero tau≥0 (clase vacía).

Como S597 demuestra que Jmax(H)=Jmax(A*), el dual óptimo
de A* se prolonga al sistema completo poniendo lambda_e=0
fuera de A*: para todo matching M de H, M∩A* es un matching
inducido de A* con la MISMA marca h. La restricción de
compatibilidad es por el H físico original, y las desigualdades
duales se conservan. Por ello **existe un dual óptimo cuyo soporte
de precios no nulos está contenido en A***.

El Hall S597 proporciona una paleta exacta de las DOS estrellas de
ancho max(r_s,r_t) y solapamiento min(r_s,r_t). Complétela con
vacío a K. Integrando las desigualdades de CUALQUIER dual factible
sobre esta paleta de estrellas:

    alpha := K*tau + sum_{e∈R}lambda_e*w_e ≥ min(r_s,r_t).

Si supusiéramos Jmax<D, existe por dualidad un óptimo con

    alpha + P_plus - P_minus < D,

donde

    P_plus=sum_{e∈A*\\R,lambda_e>0}lambda_e*w_e ≥0,
    P_minus=sum_{e∈A*\\R,lambda_e<0}(-lambda_e)*w_e ≥0.

Entonces

    P_minus > min(r_s,r_t) - D
             = K - max(r_s,r_t) - ab
             ≥ K-max(x,y) > 1/2.              (S598.C)

Es una NECESARIA condición global para una obstrucción. No se
ha demostrado una cota superior universal para P_minus; por tanto
NO cierra el arco. En la rebanada x=y=7/10, r_s=r_t=133/200,
a=b=1/20, el umbral preciso es

    K - 133/200 - 1/400 = 233/400 > 1/2.

Certo verifica la parte algebraica con cuantificadores reales:
\`examples/erdos149_s598_dual_negative.py\`. La hipótesis Hall
y la regla de prolongación dual están demostradas arriba y en S597,
pero **no están codificadas en la especificación Z3**.

## 5. Consecuencias y gate que realmente resta

El crux universal queda concentrado en un núcleo A*:

- sin demandas interiores de carga baja;
- conectado por conflictos con las dos estrellas;
- después de fusionar tipos con igual vecindario cerrado y marca;
- sin gemelos falsos físicos si se trata del contraejemplo mínimo;
- cualquier dual obstructivo necesita precios NEGATIVOS interiores
  con contribución absoluta >1/2.

**Pendiente único del arco3:** demostrar que ningún núcleo A*
fisicamente realizable, con las filas residuales y Q_H≤K,
admite un dual de valor <D; equivalentemente, construir una paleta
K de reserva J≥D. Después todavía quedan arco2, separadores
ponderados ramificados, núcleo 3-conexo y conversión entera.

No hay afirmación de demostración de Erdős–Nešetřil #149.

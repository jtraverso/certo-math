# Erdős #149, sesión S597 — Sincronización completa de las estrellas

**Teorema analítico PASS para las dos estrellas por separado**. No resuelve
la paleta completa de H ni la reinserción universal del arco de tres aristas.

Sea H un grafo simple con raíces s,t no adyacentes ni con vecinos comunes.
Denotamos x=m_s, y=m_t, A=N_H(s), B=N_H(t), p=m(A), q=m(B),
r_s=x p y r_t=y q. Suponemos
1/2 ≤x,y≤3/4, K=5/4 y un arco futuro de masas a,b>0 con
`r_s+ab ≤x`, `r_t+ab≤y` y D=r_s+r_t+ab−K>0.

**Proposición (Hall completo de raíces).** Se pueden cubrir exactamente
todas las demandas de las aristas incidentes a s y t mediante una paleta
de ancho `max(r_s,r_t)` cuyos colores que contienen una arista de la
estrella menor también contienen una arista de la estrella mayor.
Es decir, el máximo solapamiento de las estrellas *solas* es
`min(r_s,r_t)`.

**Prueba.** Por simetría supongamos `r_s≤r_t`. Cada arista `sw` de
la primera estrella demanda `x m_w`, cada arista `tz` de la segunda
demanda `y m_z`, y el par es compatible exactamente cuando `wz`
no es arista de H. Hall capacitado pide para todo `U⊆A`:

    x*m(U) ≤ y*m({z∈B: existe w∈U con wz∉E(H)}).

Si el conjunto `C_U={z∈B: wz∈E(H) para TODO w∈U}` es vacío,
el destino total es `r_t≥r_s≥x*m(U)`.

Si `C_U` no es vacío y `U` no es vacío, elige un `z∈C_U`.
Su fila de grado da `y+m(U)≤1`, luego `m(U)≤1−y`.
Para cualquier `w∈U`, su fila da `x+m(C_U)≤1`, luego
`m(C_U)≤1−x`. Por tanto la demanda del corte es ≤`x(1−y)`
y la capacidad receptora es ≥

    y*(q−m(C_U)) ≥ r_t−y(1−x).

De D>0 y `r_s+ab≤x` se deduce `r_t>K−x`. Además, para
`1/2≤x,y≤3/4`,

    x(1−y)+y(1−x) ≤ K−x.

En efecto, el miembro izquierdo más x es
`2x+y−2xy`; como x≥1/2 su coeficiente de y,
`1−2x`, es no positivo. El máximo en y≥1/2 es `x+1/2≤5/4`.
Por consiguiente `r_t−y(1−x)>x(1−y)`. Todos los cortes Hall pasan,
con margen estricto cuando C_U no es vacío. El emparejamiento racional
del flujo proporciona una paleta de medida `r_t`; las porciones t
no emparejadas quedan como clases t-solas. QED.

El caso `r_t≤r_s` resulta intercambiando s,t. Certo
`examples/erdos149_s597_root_hall_scalar.py` certifica por Z3 la
parte polinómica universal `r_s,r_t>x(1−y)+y(1−x)`.
El texto arriba prueba además Hall en todos los subconjuntos U,
es decir, la conclusión combinatoria que Certo no codifica.

**Interpretación:** todo supuesto bloqueo de J≥D proviene de las
demandas de las aristas INTERIORES de H. Las estrellas, por sí
solas, no pueden crear la obstrucción. Esto refuerza la prioridad
del LP global de paletas, y es compatible con las observaciones
de Hall de S591.

## Búsqueda adversarial de LP global

Usamos un programa lineal por todos los matchings inducidos físicos
de H con cobertura exacta y ancho 5/4; optimizamos J.
Familia 1: 200 grafos aleatorios factibles sobre diez vértices y
masas x=y=7/10, cuatro vecinos por raíz de masa 19/80, a=b=1/20.
Familia 2: otros 520 grafos factibles con 4, 6, 8 o 10 vértices
auxiliares y aristas aleatorias sujetas a todas las filas.

**Resultado exploratorio:** 720 de 720 instancias LP factibles,
todas tuvieron `Jmax=min(r_s,r_t)=133/200` dentro de tolerancia
numérica de HiGHS. Esto no es una verificación exhaustiva de
todos los grafos, ni un certificado racional por instancia.
La salida exacta de Certo para casos fijos se encarga de
verificar modelos representativos.

## Nuevo gate (sin multiplicar obligaciones)

No se añade un gate global. El único crux local sigue siendo:

    para todo H con Q_H≤5/4 y masas residuales S591,
    existe paleta exacta de H con J≥D.

Ahora el test útil es una desigualdad primal-dual **GLOBAL** que acople
colores completos de H, no solamente una saturación de estrellas o un
packing individual de bloqueadores. Una falla de `Jmax=min` podría
ser todavía compatible con `Jmax≥D`; ambos umbrales deben informarse.

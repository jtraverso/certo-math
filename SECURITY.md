# Security

*Español más abajo.*

## The bug this project most wants to hear about

Not a crash. **A certificate that verifies and should not.**

certo's whole claim is that an artefact can be re-checked without trusting the
tool that produced it. A payload that passes `certo verify` while asserting
something false breaks that claim completely, and it is worse than a crash in
the way that matters: a crash stops you, and this does not.

It has happened. A branch-and-bound tree once accepted two node duals
**exchanged** — each was a valid dual for *some* linear program, nothing in it
said which node it came from, and an expensive subtree closed by a cheap one's
certificate read exactly like a complete proof. A coefficient on an undeclared
variable was silently dropped, turning a certified `1/3` into a certified `10`
with `lint` reporting nothing. Both were found by someone looking, not by the
tool.

**`certo report --wrong --certificate FILE`** checks that the certificate
really does verify, writes a local folder with everything needed to reproduce
it, and points you to the private form below. It sends nothing.

So: if you can produce a certificate that verifies and is wrong, that is the
report worth making, and it is treated as the highest severity here regardless
of whether it fits anyone's definition of a vulnerability.

**Report it privately** through GitHub's
[Report a vulnerability](https://github.com/jtraverso/certo-math/security/advisories/new)
on this repository. Please include the spec, the certificate, and what the
certificate claims that is not true. If you would rather not use GitHub, open
an issue saying only that you have something to send and we will find a
channel.

Expect a first response within a week. There is one maintainer; this is not a
company.

## Specs are code, and certo executes them

`certo prove spec.py` **compiles and runs** `spec.py`. That is inherent to the
DSL — Python is the host language, and a spec can import, open files and make
network calls like any other script. It is the same trust an editor already
has over a file you wrote yourself, and it is *not* a safe way to run a spec
somebody sent you.

**If you did not write the spec, do not run it as Python.** Two ways not to:

```bash
certo opt spec.json          # a .json spec is DATA; nothing in it executes
certo opt spec.py --safe     # refuses a .py outright
CERTO_NO_EXEC=1 certo-mcp    # process-wide, one line in .mcp.json
```

Ten spec types build from JSON: `LPSpec`, `PackingSpec`, `MatrixSpec`,
`LinearSystemSpec`, `ConeSpec`, `CycleSpec`, `CoverSpec`, `CNFSpec`,
`NumberSpec`, `EquitableQuotientSpec`. Anything carrying a formula or a
callable is deliberately absent, because there is no way to write one in JSON.

**What `--safe` guarantees is exactly one thing: no code from the file runs.**
It does not guarantee the spec means what you think. A JSON `LPSpec` can still
encode the wrong program, and `lint`, the scope warnings and `verify`'s
re-derivation are what work on that. Do not read the flag as "this spec is
correct".

## The MCP server confines paths, and is not a sandbox

`certo-mcp` resolves every path inside `CERTO_WORKSPACE` and refuses to leave
it -- including the spec a certificate names for replay, which since 0.20.1 is
refused when it lies outside the workspace. That stops a path traversal. It does **not** stop a spec that executes, so
an agent pointed at third-party specs is running third-party code with your
privileges. Set `CERTO_NO_EXEC=1` in `.mcp.json` if the specs are not yours:

```json
{"mcpServers": {"certo": {"command": "certo-mcp",
  "env": {"CERTO_WORKSPACE": ".", "CERTO_NO_EXEC": "1"}}}}
```

## Supported versions

The latest release on PyPI. The certificate schema is frozen at 5 (since
0.20; 4 before) and payloads do not move, so a certificate issued by an older
certo still verifies — but fixes land on the newest version only.

## Out of scope

- A solver returning `unknown`, `timeout` or `resource_exhausted`. Those are
  answers, they are distinguished on purpose, and none of them means "does not
  exist".
- A spec you wrote doing what you wrote it to do.
- A command refusing input it says it refuses — a float where an exact number
  is required, a non-simplicial cone, a growth edge whose bound points the
  wrong way. Those refusals are the feature.
- Denial of service by handing certo an enormous problem. It is a laboratory
  instrument, not a service; `lint` warns before the compute is spent.

---

# Seguridad

## El fallo que este proyecto más quiere conocer

No un crash. **Un certificado que verifica y no debería.**

Toda la afirmación de certo es que un artefacto puede re-comprobarse sin
fiarse de la herramienta que lo produjo. Una carga útil que pasa
`certo verify` afirmando algo falso rompe esa afirmación por completo, y es
peor que un crash justo en lo que importa: un crash te detiene, y esto no.

Ha pasado. Un árbol de ramificación y acotación aceptó dos duales de nodo
**intercambiados** —cada uno era un dual válido para *algún* programa lineal,
nada en él decía de qué nodo venía, y un subárbol caro cerrado por el
certificado de uno barato se leía como una demostración completa. Un
coeficiente sobre una variable no declarada se descartó en silencio,
convirtiendo un `1/3` certificado en un `10` certificado sin que `lint` dijera
nada. Los dos los encontró alguien mirando, no la herramienta.

Así que: si puedes producir un certificado que verifica y está mal, ese es el
reporte que vale, y aquí se trata como la severidad más alta al margen de si
encaja en la definición de vulnerabilidad de nadie.

**Repórtalo en privado** por
[Report a vulnerability](https://github.com/jtraverso/certo-math/security/advisories/new)
en este repositorio. Incluye el spec, el certificado, y qué afirma el
certificado que no es cierto. Si prefieres no usar GitHub, abre un issue
diciendo solo que tienes algo que enviar y buscamos un canal.

Espera una primera respuesta en una semana. Hay un mantenedor; esto no es una
empresa.

## Los specs son código, y certo los ejecuta

`certo prove spec.py` **compila y ejecuta** `spec.py`. Es inherente al DSL
—Python es el lenguaje anfitrión— y un spec puede importar, abrir archivos y
hacer llamadas de red como cualquier script. Es la misma confianza que ya tiene
un editor sobre un archivo que escribiste tú, y **no** es una forma segura de
correr un spec que te mandaron.

**Si no escribiste el spec, no lo corras como Python.** Dos maneras de no
hacerlo:

```bash
certo opt spec.json          # un spec .json son DATOS; nada en él se ejecuta
certo opt spec.py --safe     # rechaza un .py de plano
CERTO_NO_EXEC=1 certo-mcp    # para todo el proceso, una línea en .mcp.json
```

Diez tipos se construyen desde JSON: `LPSpec`, `PackingSpec`, `MatrixSpec`,
`LinearSystemSpec`, `ConeSpec`, `CycleSpec`, `CoverSpec`, `CNFSpec`,
`NumberSpec`, `EquitableQuotientSpec`. Lo que lleva una fórmula o un invocable
está ausente a propósito, porque no hay forma de escribirlo en JSON.

**Lo que `--safe` garantiza es exactamente una cosa: ningún código del archivo
corre.** No garantiza que el spec signifique lo que crees. Un `LPSpec` en JSON
todavía puede codificar el programa equivocado, y `lint`, los avisos de alcance
y la re-derivación de `verify` son lo que trabaja sobre eso. No leas el flag
como «este spec es correcto».

## El servidor MCP confina rutas, y no es un sandbox

`certo-mcp` resuelve toda ruta dentro de `CERTO_WORKSPACE` y se niega a salir
-- también el spec que un certificado nombra para reproducirlo, que desde la
0.20.1 se rechaza si está fuera del workspace. Eso detiene un path traversal. **No** detiene un spec que se ejecuta, así que
un agente apuntado a specs de terceros está corriendo código de terceros con
tus privilegios. Pon `CERTO_NO_EXEC=1` en `.mcp.json` si los specs no son
tuyos.

## Versiones soportadas

La última publicada en PyPI. El esquema de certificados está congelado en 5
(desde la 0.20; antes en 4) y las cargas útiles no se mueven, así que un certificado emitido por un certo
anterior sigue verificando — pero los arreglos aterrizan solo en la versión
más nueva.

## Fuera de alcance

- Un solver devolviendo `unknown`, `timeout` o `resource_exhausted`. Son
  respuestas, se distinguen a propósito, y ninguna significa «no existe».
- Un spec que escribiste tú haciendo lo que escribiste que hiciera.
- Un comando rechazando entrada que dice que rechaza — un flotante donde se
  exige un número exacto, un cono no simplicial, una arista de crecimiento
  cuya cota apunta al lado equivocado. Esos rechazos son la funcionalidad.
- Denegación de servicio entregándole a certo un problema enorme. Es un
  instrumento de laboratorio, no un servicio; `lint` avisa antes de gastar el
  cómputo.

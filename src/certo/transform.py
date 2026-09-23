"""What a transformation promises, and whether it kept the promise.

THE DEFECT THIS CLOSES. `PackingSpec.restricted()` built the new spec without
passing `loads`, so a packing carrying `t0 <= 0`, restricted to t0's own kind,
came back admitting `t0 = 1`. A user found it. The reason it is worse than an
ordinary bug is in their own words:

    a correct solver cannot repair that omission

Every optimum it reported was a true optimum -- of the model it was handed.
Nothing downstream can notice, because nothing downstream ever sees the model
that was meant.

Auditing for the same shape found `LPSpec.relaxed()` dropping `target` and
`load_names`. Then the reflection below found a transformation nobody had
looked at -- `LPSpec.frozen()` -- losing the same two. THREE OF THE SIX
transformations in the tree, and not one of them said anywhere what it was
supposed to preserve.

`frozen` is also the case where copying the field across would have been the
WRONG fix: its target is about an objective missing a constant, so the target
had to be SHIFTED. Finding the omissions is mechanical; deciding what each one
should have been is not, which is why the reasons are written down one by one
rather than generated.

THE RULE, which is the one this project already applies everywhere else:
DERIVE THE EXPECTATION. Not "remember to pass loads" -- compare the two specs
field by field and require every difference to be DECLARED, with a reason. A
field that changes silently is the bug; a field that changes on purpose is a
sentence somebody wrote.

THE THREE RELATIONS, and what each one licenses:

  EQUIVALENT    same feasible set, same optimum. A renaming, a reordering.
  RESTRICTION   the feasible set shrinks. A maximum cannot rise and a
                minimum cannot fall. `restricted` is one: keeping some kinds
                is forcing the others to zero.
  RELAXATION    the feasible set grows. A maximum cannot fall and a minimum
                cannot rise. `relaxed` is one: integrality is dropped.

The relation is not decoration. It says which direction a comparison between
the two optima is allowed to go, which is the thing a reader actually wants
when they see two numbers.

AND A NEW TRANSFORMATION CANNOT BE FORGOTTEN. `transformations()` finds them
by looking for methods that CONSTRUCT a spec, so adding one without a contract
is caught by a test rather than by the next user.

WHAT THIS DOES NOT DO. It does not verify the relation semantically -- that a
restriction really did shrink the feasible set is a statement about all
points, not about two dataclasses. What it checks is that nothing changed
without being declared, which is the failure that actually happened.
"""
from __future__ import annotations

import dataclasses
import inspect
import re

EQUIVALENT = "equivalent"
RESTRICTION = "restriction"
RELAXATION = "relaxation"

#: What each relation licenses about the two optima, for a reader holding
#: both numbers.
MEANS = {
    EQUIVALENT: "same feasible set: the optima are equal",
    RESTRICTION: "the feasible set shrinks: a maximum cannot rise, "
                 "a minimum cannot fall",
    RELAXATION: "the feasible set grows: a maximum cannot fall, "
                "a minimum cannot rise",
}


@dataclasses.dataclass(frozen=True)
class Contract:
    """What a transformation promises about the spec it returns."""

    relation: str
    #: field -> why it legitimately differs. Every other difference is a bug.
    changes: dict = dataclasses.field(default_factory=dict)
    note: str = ""

    def means(self) -> str:
        return MEANS.get(self.relation, "")


#: The registry. A transformation not in here is one nobody has thought about,
#: which `transformations()` plus a test turns into a failure rather than a
#: surprise.
CONTRACTS = {
    ("PackingSpec", "restricted"): Contract(
        RESTRICTION,
        {"items": "only the kinds asked for survive",
         "loads": "each load keeps its surviving terms; forcing an item to "
                  "zero removes its TERM, not the constraint",
         "title": "records which kinds were kept",
         "_kinds": "derived from `items`"},
        "keeping some kinds is exactly forcing every other item to zero"),
    ("LPSpec", "relaxed"): Contract(
        RELAXATION,
        {"integer": "dropped: this IS the relaxation",
         "kinds": "every variable becomes continuous, which is the same fact"},
        "integrality is the only thing a relaxation drops"),
    ("LPSpec", "frozen"): Contract(
        RESTRICTION,
        {"var_names": "only the continuous variables remain",
         "bounds": "the frozen variables have no bounds left to state",
         "kinds": "same, one entry per surviving variable",
         "obj": "the frozen variables' contribution leaves as `const`",
         "cons": "each right-hand side absorbs the frozen variables' share",
         "integer": "nothing discrete is left to mark",
         "target": "SHIFTED by `const`, not copied: the residual meets the "
                   "original target T exactly when z + const >= T",
         "title": "records the assignment"},
        "fixing the discrete variables is a slice of the feasible set"),

    # TRANSLATIONS, not transformations of the same kind of object. There is
    # no field-by-field comparison to make -- the two sides are different
    # classes -- so the contract carries the relation and the note alone. That
    # these say EQUIVALENT is exactly the claim "certify the map" would have
    # to establish, and nothing here establishes it yet.
    ("PackingSpec", "to_lp"): Contract(
        EQUIVALENT, {},
        "the same packing written as a linear program. NOT CHECKED: that the "
        "rows are the resources they are named after is the translation "
        "obligation, and it is open"),
    ("CoverSpec", "to_lp"): Contract(
        EQUIVALENT, {},
        "the same cover written as a linear program. Same open obligation"),
    ("MultiSpec", "single"): Contract(
        RESTRICTION, {},
        "one goal of the many, under all the same assumptions"),
}


def fields_of(obj) -> list:
    if dataclasses.is_dataclass(obj):
        return [f.name for f in dataclasses.fields(obj)]
    return sorted(k for k in vars(obj) if not k.startswith("__"))


def differences(before, after) -> list:
    """Fields whose value is not the same in both. Derived, never listed."""
    names = fields_of(before)
    if fields_of(after) != names:
        # Different shapes entirely: a translation, not a transformation of
        # the same kind of object. Those get a relation and no field diff.
        return None
    out = []
    for name in names:
        a, b = getattr(before, name, None), getattr(after, name, None)
        try:
            same = (a == b)
        except Exception:  # noqa: BLE001
            same = a is b
        if not same:
            out.append(name)
    return out


def check(before, after, contract: Contract) -> dict:
    """Did the transformation change anything it did not declare?"""
    diff = differences(before, after)
    if diff is None:
        return {"relation": contract.relation, "means": contract.means(),
                "comparable": False, "undeclared": [], "stale": []}
    declared = set(contract.changes)
    return {
        "relation": contract.relation,
        "means": contract.means(),
        "comparable": True,
        "changed": diff,
        # THE BUG CLASS: something moved and nobody said it would.
        "undeclared": sorted(set(diff) - declared),
        # Declared but unchanged IN THIS CALL. Not a defect: a contract says
        # what a transformation MAY change, and `restricted` leaves the loads
        # alone whenever every item they mention survives. It is worth
        # reporting because a declaration that is stale across EVERY instance
        # is a sentence describing code that changed under it -- but one call
        # cannot tell you that, so nothing here treats it as a failure.
        "unchanged_but_declared": sorted(declared - set(diff)),
    }


#: A method BUILDS a spec when its source constructs one. Catches `relaxed`,
#: whose return annotation says nothing, which is exactly the one that had the
#: defect.
_BUILDS = re.compile(r"\b(\w*Spec)\s*\(")


def transformations() -> dict:
    """Every method on a spec class that constructs a spec. Found, not listed.

    The point of finding them rather than naming them: a transformation added
    next year without a contract fails a test here, instead of losing a
    constraint in somebody's model two releases later.
    """
    from . import packing, spec

    found = {}
    for module in (spec, packing):
        for cname, cls in vars(module).items():
            if not (inspect.isclass(cls) and cname.endswith("Spec")):
                continue
            if not dataclasses.is_dataclass(cls):
                continue
            for mname, meth in vars(cls).items():
                if mname.startswith("_") or not callable(meth):
                    continue
                try:
                    src = inspect.getsource(meth)
                except (OSError, TypeError):
                    continue
                if _BUILDS.search(src):
                    found[(cname, mname)] = meth
    return found


def contract_of(cls_name: str, method: str):
    return CONTRACTS.get((cls_name, method))


def report(before, after, cls_name: str, method: str) -> dict:
    """The whole answer for one call of one transformation."""
    c = contract_of(cls_name, method)
    if c is None:
        return {"transformation": "{}.{}".format(cls_name, method),
                "contract": None,
                "undeclared": sorted(differences(before, after) or []),
                "means": ""}
    out = check(before, after, c)
    out["transformation"] = "{}.{}".format(cls_name, method)
    out["contract"] = c.relation
    out["note"] = c.note
    return out

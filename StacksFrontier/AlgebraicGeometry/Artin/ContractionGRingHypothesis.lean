module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituation
public import StacksFrontier.RingTheory.GRing.Defs

/-!
# The G-ring hypothesis on the situation of Artin's contraction theorem (Stacks 0GH9)

**Stacks 0GH9** is a remark on Situation 0GH8: the desired result cannot be proved for every
such situation, because the local rings of `S` will have to be assumed to be G-rings, and the
reader who can prove the general case or produce a counterexample is invited to write in.

The only mathematics the remark names is the standing assumption it announces, and that
assumption is what the sequel uses: the main theorem of the section, Stacks 0GIB, carries it
as a hypothesis. It is recorded here as a predicate on the situation of Stacks 0GH8.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.LocalRingsAreGRings`: **Stacks 0GH9**, the
  announced hypothesis, namely that every local ring of the base scheme `S` is a G-ring in the
  sense of Stacks 07GH.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isNoetherianRing_of_localRingsAreGRings`: a
  situation satisfying the hypothesis has Noetherian local rings, which is the first clause of
  being a G-ring.

## What is and is not proved

What is recorded is a definition, not a theorem: the remark asserts nothing. Its two further
sentences — that the general case is not proved in the source, and the invitation to readers —
are editorial, so the attribute on the definition is keyed to say that only the announced
hypothesis is delivered.

Nothing is assumed.

## Implementation notes

The local rings of `S` are the stalks `S.presheaf.stalk s` of its structure sheaf, and
`IsGRing` is the predicate of Stacks 07GH: Noetherian, with a regular map from each local ring
to that local ring's completion. The condition mentions only the base scheme of the situation,
which is why the remark can announce it before any of the other data of Situation 0GH8 is
used; it is nevertheless phrased as a predicate on the situation, since that is the object the
remark is about and the object the sequel attaches it to. The situation argument is therefore
named `_c`: it fixes the base scheme the condition is about and is not otherwise used.

Stacks 0GIB in fact only needs the local rings at the finite type points of `S` to be G-rings,
which is weaker. The remark states the hypothesis in the unqualified form recorded here, and
that is what this file follows.

## References

* [Stacks Project, Tag 07GH](https://stacks.math.columbia.edu/tag/07GH)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GH9](https://stacks.math.columbia.edu/tag/0GH9)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Artin

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GH9.** The hypothesis the remark announces for the situation of Stacks 0GH8:
every local ring of the base scheme `S` is a G-ring in the sense of Stacks 07GH. -/
@[stacks 0GH9 "the standing hypothesis the remark announces, that the local rings of S are \
G-rings, as a predicate on Situation 0GH8. The remark's two other sentences — that the source \
therefore does not prove its theorem for every Situation 0GH8, and the invitation to a reader \
who can prove the general case or supply a counterexample — assert no mathematics and are not \
formalized"]
def LocalRingsAreGRings (_c : ContractionSituation B S hS) : Prop :=
  ∀ s : S, IsGRing (S.presheaf.stalk s)

/-- Under the hypothesis of Stacks 0GH9 the local rings of `S` are Noetherian, that being the
first clause of the definition of a G-ring. -/
theorem isNoetherianRing_of_localRingsAreGRings {c : ContractionSituation B S hS}
    (hc : c.LocalRingsAreGRings) (s : S) : IsNoetherianRing (S.presheaf.stalk s) :=
  (hc s).1

end ContractionSituation

end AlgebraicGeometry.Artin

end

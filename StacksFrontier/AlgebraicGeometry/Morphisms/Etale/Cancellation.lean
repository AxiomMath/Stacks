module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute

/-!
# The cancellation law for étale morphisms

A morphism between two schemes that are étale over a common base is itself étale. Equivalently,
if a composite `f ≫ q` and the second factor `q` are étale, then so is the first factor `f`.

## Main results

* `AlgebraicGeometry.Etale.of_comp_right` is the cancellation law in composite form.
* `AlgebraicGeometry.etale_of_etale_over` is the same statement for two schemes étale over a
  common base and a morphism between them over that base.

## Implementation notes

Étaleness of schemes is Mathlib's morphism property `AlgebraicGeometry.Etale`, which has the
cancellation property `MorphismProperty.HasOfPostcompProperty` against itself because an étale
morphism is unramified and an unramified morphism cancels on the right.

## References

* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The cancellation law for étale morphisms.** If a composite `f ≫ q` is étale and the
second factor `q` is étale, then the first factor `f` is étale. -/
theorem Etale.of_comp_right {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) [Etale q]
    [Etale (f ≫ q)] : Etale f :=
  MorphismProperty.of_postcomp @Etale (W' := @Etale) f q ‹_› ‹_›

/-- **Stacks Project, Tag 02GW.** A morphism between two schemes that are étale over a common
base, and which commutes with the structure morphisms, is étale. -/
@[stacks 02GW, sga "4 VII 1.2"]
theorem etale_of_etale_over {X Y S : Scheme.{u}} (f : X ⟶ Y) {p : X ⟶ S} {q : Y ⟶ S}
    (h : f ≫ q = p) [Etale p] [Etale q] : Etale f :=
  have : Etale (f ≫ q) := h ▸ ‹Etale p›
  Etale.of_comp_right f q

end AlgebraicGeometry

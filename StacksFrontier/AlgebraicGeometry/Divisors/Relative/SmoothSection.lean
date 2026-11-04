module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# A section of a smooth morphism is a regular immersion

Let `f : X ⟶ S` be a smooth morphism of schemes and let `σ : S ⟶ X` be a section of `f`, that is
`σ ≫ f = 𝟙 S`.  Then `σ` is an immersion, and it is a *regular* immersion.

## Main results

* `Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id`: a morphism admitting a retraction is an
  immersion.
* `Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section`: **Stacks tag 067R**.

## Implementation notes

The source replaces `X` by an open neighbourhood of `σ(S)` and checks the fibres by hand.  Here
the statement follows from Stacks tag 067U — an immersion between two schemes smooth over a base
is regular — applied to `σ : S ⟶ X` over `S`, because `σ ≫ f = 𝟙 S` makes the structure morphism
of the source the identity, which is smooth.

The immersion instance is not an argument of the statement: it is produced from `hσ` by
`isImmersion_of_comp_eq_id`, so the conclusion is stated under a `letI` supplying exactly that
instance.

## References

* [Stacks Project, Lemma 31.22.5 (Tag 067R)](https://stacks.math.columbia.edu/tag/067R)
* [Stacks Project, Lemma 31.22.7 (Tag 067U)](https://stacks.math.columbia.edu/tag/067U)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- A morphism of schemes which admits a retraction is an immersion: its composite with the
retraction is the identity, which is an immersion, and an immersion factors through any
morphism whose composite with it is an immersion. -/
theorem isImmersion_of_comp_eq_id (σ : S ⟶ X) (f : X ⟶ S) (hσ : σ ≫ f = 𝟙 S) :
    IsImmersion σ := by
  have : IsImmersion (σ ≫ f) := by rw [hσ]; infer_instance
  exact IsImmersion.of_comp σ f

/-- **Stacks Project, Tag 067R.**  A section `σ` of a smooth morphism `f : X ⟶ S` of schemes is a
regular immersion. -/
@[stacks 067R,
  sga "6 VII 1.10" "section case",
  ega "IV 17.12.3" "necessity",
  sga "6 VII 4.2" "more general",
  sga "6 VIII 1.3" "more general",
  sga "6 VIII 2.4" "special case"]
theorem isRegularImmersion_of_smooth_section (f : X ⟶ S) [Smooth f] (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) :
    letI : IsImmersion σ := isImmersion_of_comp_eq_id σ f hσ
    IsRegularImmersion σ := by
  have : IsImmersion σ := isImmersion_of_comp_eq_id σ f hσ
  have : Smooth (σ ≫ f) := by rw [hσ]; infer_instance
  exact isRegularImmersion_of_smooth_of_smooth σ f

end Stacks.AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine

/-!
# Affine intersections in the standard cover of a thickening of an affine scheme

Let `i : X ⟶ X'` be a thickening. For `V` an affine open of `X'` and `W` an open of `X'` whose
preimage is a basic open of `X`, the intersection `V ⊓ W` is a basic open of `V`, hence affine.
If moreover the preimages of `V` and `W` are the basic opens of `a` and `b`, the preimage of
`V ⊓ W` is the basic open of `a * b`. The open `W` itself is not assumed affine.

## Main results

* `Stacks.Thickenings.IsThickening.exists_app_basicOpen_eq_inf`: the intersection of an affine
  open of `X'` with an open whose preimage is a basic open of `X` is a basic open of the affine
  one.
* `Stacks.Thickenings.IsThickening.isAffineOpen_inf`: that intersection is affine.
* `Stacks.Thickenings.IsThickening.preimage_inf_eq_basicOpen`: the preimage of the intersection
  of two opens with basic-open preimages is the basic open of the product of the two sections.
* `Stacks.Thickenings.IsThickening.isAffineOpen_inf_of_isAffineOpen`: both statements together.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}}

/-- For a thickening `i : X ⟶ X'`, an affine open `V` of `X'` and an open `W` of `X'` whose
preimage is a basic open of `X`, the intersection `V ⊓ W` is the basic open of a section of `X'`
over `V`. -/
theorem IsThickening.exists_app_basicOpen_eq_inf {i : X ⟶ X'} (hi : IsThickening i)
    {V W : X'.Opens} (hV : IsAffineOpen V) {b : Γ(X, (⊤ : X.Opens))}
    (hW : i ⁻¹ᵁ W = X.basicOpen b) :
    ∃ c : Γ(X', V), X'.basicOpen c = V ⊓ W := by
  have := hi.1
  obtain ⟨c, hc⟩ :=
    i.app_surjective V hV (X.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ V ≤ ⊤)).op b)
  refine ⟨c, ?_⟩
  have hpre : i ⁻¹ᵁ X'.basicOpen c = i ⁻¹ᵁ (V ⊓ W) := by
    rw [Scheme.preimage_basicOpen, hc, Scheme.basicOpen_res, ← hW, Scheme.Hom.preimage_inf]
  exact le_antisymm (hi.le_of_preimage_le hpre.le) (hi.le_of_preimage_le hpre.ge)

/-- For a thickening `i : X ⟶ X'`, an affine open `V` of `X'` and an open `W` of `X'` whose
preimage is a basic open of `X`, the intersection `V ⊓ W` is affine. -/
theorem IsThickening.isAffineOpen_inf {i : X ⟶ X'} (hi : IsThickening i) {V W : X'.Opens}
    (hV : IsAffineOpen V) {b : Γ(X, (⊤ : X.Opens))} (hW : i ⁻¹ᵁ W = X.basicOpen b) :
    IsAffineOpen (V ⊓ W) := by
  obtain ⟨c, hc⟩ := hi.exists_app_basicOpen_eq_inf hV hW
  exact hc ▸ hV.basicOpen c

/-- If the preimages of opens `V` and `W` of `X'` under `i : X ⟶ X'` are the basic opens of `a`
and `b`, then the preimage of `V ⊓ W` is the basic open of `a * b`. -/
theorem IsThickening.preimage_inf_eq_basicOpen {i : X ⟶ X'} {V W : X'.Opens}
    {a b : Γ(X, (⊤ : X.Opens))} (hV : i ⁻¹ᵁ V = X.basicOpen a) (hW : i ⁻¹ᵁ W = X.basicOpen b) :
    i ⁻¹ᵁ (V ⊓ W) = X.basicOpen (a * b) := by
  rw [Scheme.Hom.preimage_inf, hV, hW, Scheme.basicOpen_mul]

/-- For a thickening `i : X ⟶ X'`, an affine open `V` of `X'` and an open `W` of `X'` whose
preimages are the basic opens of `a` and `b`, the intersection `V ⊓ W` is affine and its preimage
is the basic open of `a * b`. -/
theorem IsThickening.isAffineOpen_inf_of_isAffineOpen {i : X ⟶ X'} (hi : IsThickening i)
    {V W : X'.Opens} (hV : IsAffineOpen V) {a b : Γ(X, (⊤ : X.Opens))}
    (hV' : i ⁻¹ᵁ V = X.basicOpen a) (hW : i ⁻¹ᵁ W = X.basicOpen b) :
    IsAffineOpen (V ⊓ W) ∧ i ⁻¹ᵁ (V ⊓ W) = X.basicOpen (a * b) :=
  ⟨hi.isAffineOpen_inf hV hW, IsThickening.preimage_inf_eq_basicOpen hV' hW⟩

end Stacks.Thickenings

end

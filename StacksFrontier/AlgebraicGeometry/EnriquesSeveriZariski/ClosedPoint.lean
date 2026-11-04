module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal

/-!
# A point of a proper scheme whose closure is affine is closed

Let `X` be a scheme proper over a field `k` and let `y` be a point of `X` whose closure is
contained in an affine open `U ⊆ X`. Then `y` is a closed point.

## Main definitions

* `Stacks.EnriquesSeveriZariski.closureSubscheme`: the reduced closed subscheme of `X` supported
  on `closure {y}`.
* `Stacks.EnriquesSeveriZariski.closureSubschemeι`: its closed immersion into `X`.

## Main results

* `Stacks.EnriquesSeveriZariski.range_closureSubschemeι`: the closed immersion has range
  `closure {y}`.
* `Stacks.EnriquesSeveriZariski.closureSubschemeι_genericPoint`: the generic point of the reduced
  closure of `y` is carried to `y`.
* `Stacks.EnriquesSeveriZariski.isAffine_closureSubscheme`: the reduced closure of `y` is affine
  as soon as `closure {y}` lies in an affine open.
* `Stacks.EnriquesSeveriZariski.isClosed_singleton_of_closure_subset_of_isAffineOpen`: on a
  scheme proper over a field, a point whose closure is contained in an affine open is closed.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.EnriquesSeveriZariski

variable {X : Scheme.{u}}

/-- The reduced closed subscheme of `X` supported on the closure of a point `y`. -/
abbrev closureSubscheme (y : X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subscheme

/-- The canonical closed immersion of the reduced closure of a point into the ambient scheme. -/
abbrev closureSubschemeι (y : X) : closureSubscheme y ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subschemeι

/-- The reduced closure of a point is integral. -/
instance isIntegral_closureSubscheme (y : X) : IsIntegral (closureSubscheme y) :=
  Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y

/-- The closed immersion of the reduced closure of `y` has range `closure {y}`. -/
theorem range_closureSubschemeι (y : X) :
    Set.range (closureSubschemeι y) = closure ({y} : Set X) :=
  (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _).trans (Closeds.coe_closure _)

/-- The generic point of the reduced closure of `y` is carried to `y`. -/
theorem closureSubschemeι_genericPoint (y : X) :
    closureSubschemeι y (genericPoint (closureSubscheme y)) = y :=
  Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure y

/-- The reduced closure of a point whose closure is contained in an affine open is affine. -/
theorem isAffine_closureSubscheme {U : X.Opens} (hU : IsAffineOpen U) {y : X}
    (hy : closure ({y} : Set X) ⊆ (U : Set X)) : IsAffine (closureSubscheme y) := by
  have hpre : closureSubschemeι y ⁻¹ᵁ U = ⊤ := by
    refine Opens.ext ?_
    rwa [Opens.coe_top, Scheme.Hom.coe_preimage, Set.preimage_eq_univ_iff,
      range_closureSubschemeι]
  have h1 : IsAffineOpen (closureSubschemeι y ⁻¹ᵁ U) := hU.preimage _
  rw [hpre] at h1
  have h2 : IsAffine (⊤ : (closureSubscheme y).Opens).toScheme := h1
  exact IsAffine.of_isIso (Scheme.topIso (closureSubscheme y)).inv

/-- On a scheme proper over a field, a point whose closure is contained in an affine open is
closed. -/
theorem isClosed_singleton_of_closure_subset_of_isAffineOpen
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    {U : X.Opens} (hU : IsAffineOpen U) {y : X}
    (hy : closure ({y} : Set X) ⊆ (U : Set X)) :
    IsClosed ({y} : Set X) := by
  have : IsAffine (closureSubscheme y) := isAffine_closureSubscheme hU hy
  have hfield : IsField Γ(closureSubscheme y, ⊤) := by
    open Stacks.AlgebraicGeometry.ProperSectionsGeom in
    exact isField_globalSections_of_connectedSpace_of_isReduced k (closureSubschemeι y ≫ f)
  have : _root_.IsReduced ↥Γ(closureSubscheme y, ⊤) :=
    AlgebraicGeometry.IsReduced.component_reduced ⊤
  have : Subsingleton ↥(Spec Γ(closureSubscheme y, ⊤)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hfield
  have : Subsingleton ↥(closureSubscheme y) :=
    (Scheme.homeoOfIso (closureSubscheme y).isoSpec).injective.subsingleton
  have hcl : closure ({y} : Set X) = {y} := by
    refine Set.Subset.antisymm ?_ subset_closure
    rw [← range_closureSubschemeι y]
    rintro _ ⟨z, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim z (genericPoint (closureSubscheme y))]
    exact closureSubschemeι_genericPoint y
  exact hcl ▸ isClosed_closure

end Stacks.EnriquesSeveriZariski

end

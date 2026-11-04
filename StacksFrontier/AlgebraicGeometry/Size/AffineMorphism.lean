module

public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The size of a scheme affine over a base

A scheme `X` affine over a base scheme `S` is covered by the preimages `f⁻¹(U)` of the affine
opens `U` of `S`, each of them affine with ring of sections `Γ(X, f⁻¹(U))`. So `size X` is
bounded by the size of `S` together with the cardinalities of those rings.

## Main results

* `AlgebraicGeometry.Scheme.size_le_of_isAffineHom`: for an affine morphism `f : X ⟶ S`,
  `size X ≤ max (size S) (⨆ U, #Γ(X, f⁻¹(U)))`, the supremum over the affine opens of `S`.
* `AlgebraicGeometry.BigFppfSite.contains_of_isAffineHom`: a scheme affine over a scheme
  contained in a big fppf site is itself contained in that site as soon as the sections over
  the preimages of the affine opens of the base are uniformly bounded by a cardinal below the
  cutoff.

## Implementation notes

The bound on the rings of sections cannot be dropped: `Spec R ⟶ Spec (ULift ℤ)` is affine, and
`AlgebraicGeometry.Scheme.size_Spec` gives `size (Spec R) = max ℵ₀ #R`, which exceeds any fixed
cutoff for `R` large enough.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open Cardinal CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For an affine morphism `f : X ⟶ S`, the size of `X` is at most the maximum of the size of `S`
and the cardinalities of the rings of sections of `X` over the preimages of the affine opens of
`S`. -/
theorem Scheme.size_le_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    X.size ≤ max S.size (⨆ U : S.affineOpens, #Γ(X, f ⁻¹ᵁ U.1)) := by
  have : Nonempty S.affineOpens := ⟨⟨⊥, isAffineOpen_bot S⟩⟩
  have hcov : ⨆ U : S.affineOpens, f ⁻¹ᵁ U.1 = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  refine (Scheme.size_le_of_iSup_eq_top (fun U : S.affineOpens => f ⁻¹ᵁ U.1) hcov).trans
    (max_le ((Scheme.mk_affineOpens_le_size S).trans (le_max_left _ _))
      (ciSup_le' fun U => ?_))
  have : IsAffine ((f ⁻¹ᵁ U.1 : X.Opens) : Scheme.{u}) :=
    IsAffineHom.isAffine_preimage (f := f) U.1 U.2
  rw [Scheme.size_of_isAffine, Scheme.mk_sections_coe_opens]
  exact max_le (le_max_of_le_left (Scheme.aleph0_le_size S))
    (le_max_of_le_right (le_ciSup bddAbove_of_small U))

/-- A scheme affine over an object of a big fppf site lies in that site, provided its rings of
sections over the preimages of the affine opens of the base are bounded by a cardinal below the
cutoff. -/
theorem BigFppfSite.contains_of_isAffineHom (B : BigFppfSite.{u}) {X S : Scheme.{u}}
    (f : X ⟶ S) [IsAffineHom f] (hS : B.Contains S) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hsec : ∀ U : S.affineOpens, #Γ(X, f ⁻¹ᵁ U.1) ≤ μ) :
    B.Contains X :=
  (Scheme.size_le_of_isAffineHom f).trans_lt (max_lt hS ((ciSup_le' hsec).trans_lt hμ))

end AlgebraicGeometry

end

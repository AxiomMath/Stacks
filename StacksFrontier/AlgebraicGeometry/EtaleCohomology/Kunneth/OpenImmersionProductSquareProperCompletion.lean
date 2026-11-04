module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareRestriction
public import StacksFrontier.AlgebraicGeometry.Variety.AffineProjectiveCompletionDimension

/-!
# Replacing an affine `Y` by a projective completion of the same dimension

The proof of [Stacks, Tag 0F1H], after reducing to affine `X` and `Y`, says: *"However, then we
can choose an open dense immersion `Y ⟶ Y'` with `Y'` projective. [...] Then `dim(Y') = dim(Y)`
and hence we get a "minimal" counter example with `Y` projective over `K`."* This file proves
that step for the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` of the product square of `j`
and `Y`: it is invertible as soon as the base change map of the product square of `j` and every
proper `Y'` over `K` containing `Y` as an open subscheme, with `dim(Y') = dim(Y)`, is.

## Main results

* `OpenImmersionProductSquare.isIso_higherBaseChangeMapAb_of_isProper_completion`

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenImmersionProductSquare

variable {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) (hj : j ≫ sX = sU)

/-- **Replacing an affine `Y` by a projective completion** ([Stacks, Tag 0F1H]). Let `Y` be affine
and locally of finite type over `K`. Suppose that for every scheme `Y'` with a projective (hence
proper) morphism `sY' : Y' ⟶ Spec K` and an open immersion `ι : Y ⟶ Y'` over `K` with
`dim(Y') = dim(Y)`, the base change map of the product square of `j` and `Y'` is invertible at
`𝓕`. Then `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible: such a `Y'` exists, and the base change
map restricts along the open immersion `Y ×_K X ⟶ Y' ×_K X`. -/
theorem isIso_higherBaseChangeMapAb_of_isProper_completion [IsAffine Y] [LocallyOfFiniteType sY]
    (i : ℕ) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (H : ∀ (Y' : Scheme.{u}) (sY' : Y' ⟶ Spec (.of K)) (ι : Y ⟶ Y'), IsProjectiveMorphism sY' →
      IsProper sY' → IsOpenImmersion ι → ι ≫ sY' = sY →
        topologicalKrullDim Y' = topologicalKrullDim Y →
        IsIso ((higherBaseChangeMapAb (q sX sY') j (h sX sU sY' j hj) (p sU sY')
          (h_comp_q sX sU sY' j hj) i).app 𝓕)) :
    IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕) := by
  obtain ⟨Y', ι, sY', hι, hcomp, hproj, hprop, -, hdim⟩ :=
    exists_isOpenImmersion_isProper_topologicalKrullDim_eq_of_isAffine K sY
  have := H Y' sY' ι hproj hprop hι hcomp hdim
  subst hcomp
  exact isIso_higherBaseChangeMapAb_of_etale_left sX sU sY' j hj ι i 𝓕 this

end Stacks.EtaleCohomology.OpenImmersionProductSquare

end

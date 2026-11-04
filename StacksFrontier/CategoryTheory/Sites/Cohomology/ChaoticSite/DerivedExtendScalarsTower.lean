module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitCoefficientTensor

/-!
# Functorial base change along a tower of presheaves of rings

Let `C` be a small category with the chaotic topology, so that a sheaf of `O`-modules on `C` is a
presheaf of `O`-modules, and let

`O ⟶ O' ⟶ O''`

be a tower of presheaves of rings on `C`. This file proves the **functorial base change for the
tower**: the derived tensor product with the last coefficient ring is the composite of the two
intermediate ones,

`K ⊗^L_O O'' ≅ (K ⊗^L_O O') ⊗^L_{O'} O''`,

as an isomorphism of functors `D(Mod(O)) ⥤ D(Mod(O''))`. Being an isomorphism of functors it is
automatically natural in the coefficient complex `K`, so it is compatible with every map
`K₁ ⟶ K₂` — in the intended application, with the inclusions `𝒦ⁿ⁺¹ ⊆ 𝒦ⁿ` of the powers of the
augmentation ideal on the polynomial site, uniformly in `n`.

The three functors are `Stacks.ChaoticSite.derivedExtendScalars` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedColimitCoefficientTensor.lean`,
each of which exists unconditionally; the point is that they compose.

## The proof

Each `- ⊗^L_O O'` is the total left derived functor of extension of scalars, and is left adjoint
to the degreewise derived functor of restriction of scalars
(`Stacks.ChaoticSite.derivedExtendScalarsAdjunction`). Restriction of scalars along a composite
*is* the composite of the restrictions — definitionally, since on sections over an object of the
site both are the same module with the same action — so the two candidate functors are both left
adjoint to the same functor up to the isomorphism
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, and a left adjoint is unique.

Nothing is assumed of the tower: no flatness, no surjectivity, no vanishing.

## Main results

* `Stacks.ChaoticSite.restrictScalars_comp`: restriction of scalars along a composite is the
  composite of the restrictions.
* `Stacks.ChaoticSite.derivedExtendScalarsComp`: the functorial base change for the tower.

## What this is and is not

This is the base change that **holds** for a tower. It is *not* the Künneth-type decomposition
`𝒦ⁿ ⊗^L_𝒪 B̲ ≅ Λ_• ⊗^L_B (𝒦ⁿ ⊗^L_Ō B̲)` with `Λ_• = B̲ ⊗^L_𝒪 Ō`, which is a different
assertion, and which is false: see
`StacksFrontier/Cotangent/SurjectionSiteAugmentationBaseChange.lean` for the counterexample and for
the analysis of the two `Ō`-module structures on `Λ_•` that is behind the failure. In particular
the pro-nilpotence hypothesis
`CommAlgCat.SmallPolynomialAugmentationProNilpotent` does **not** follow from what is proved
here: the transitivity above presents `𝒦ⁿ ⊗^L_𝒪 B̲` as `(𝒦ⁿ ⊗^L_𝒪 Ō) ⊗^L_Ō B̲`, whose varying
factor is `𝒦ⁿ ⊗^L_𝒪 Ō` and not `𝒦ⁿ`, while [Stacks, Tag 08RE] kills the transition maps on
`Tor^Ō(B, 𝒦ⁿ)`, that is after applying `- ⊗^L_Ō B̲` to `𝒦ⁿ` itself.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] {O O' O'' : Cᵒᵖ ⥤ RingCat.{u}}

/-- Restriction of scalars along a composite of maps of presheaves of rings is the composite of
the restrictions: over an object of the site both are the same module of sections with the same
action, so the two functors are equal. -/
theorem restrictScalars_comp (a : O ⟶ O') (b : O' ⟶ O'') :
    PresheafOfModules.restrictScalars.{u} (a ≫ b) =
      PresheafOfModules.restrictScalars.{u} b ⋙ PresheafOfModules.restrictScalars.{u} a :=
  rfl

/-- **Functorial base change along the tower `O ⟶ O' ⟶ O''`**: the derived tensor product with
`O''` is the composite of the derived tensor products with `O'` and with `O''`,

`K ⊗^L_O O'' ≅ (K ⊗^L_O O') ⊗^L_{O'} O''`,

naturally in `K`. Each of the three functors is the total left derived functor of extension of
scalars and so is left adjoint to the degreewise derived functor of restriction of scalars; the
restrictions compose by `Stacks.ChaoticSite.restrictScalars_comp`, hence so do their degreewise
derived functors by `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, and a left
adjoint of a
given functor is unique up to a unique isomorphism.

Nothing is assumed of the tower. Naturality in `K` is automatic, this being an isomorphism of
functors, so the identification is compatible with every map of coefficient complexes. -/
def derivedExtendScalarsComp (a : O ⟶ O') (b : O' ⟶ O'') :
    derivedExtendScalars (a ≫ b) ≅ derivedExtendScalars a ⋙ derivedExtendScalars b :=
  Adjunction.leftAdjointUniq
    ((derivedExtendScalarsAdjunction (a ≫ b)).ofNatIsoRight
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (PresheafOfModules.restrictScalars.{u} b)
        (PresheafOfModules.restrictScalars.{u} a)))
    ((derivedExtendScalarsAdjunction a).comp (derivedExtendScalarsAdjunction b))

end Stacks.ChaoticSite

end

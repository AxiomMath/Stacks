module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurveDevissage

/-!
# Dévissage for the restriction map on étale cohomology

Let `f : X ⟶ Y` be a morphism of schemes. This file proves closure properties of the class of
abelian sheaves on the small étale site of `Y` whose restriction map
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` along `f` is bijective. These are the
closure steps of the dévissage proving part (7) of [Stacks, Tag 03SC], where `f` is the base change
of a proper scheme along an extension of algebraically closed fields; here `f` is arbitrary.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_shortExact`: the class of
  abelian étale sheaves whose restriction map is bijective in every degree is closed under
  extensions.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_biprod`: closure under binary
  biproducts.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_retract`: if the restriction
  map of a sheaf is bijective in degree `q`, so is that of any retract of it.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 03SD](https://stacks.math.columbia.edu/tag/03SD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

universe u v w

section RestrictionDevissage

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Dévissage for the restriction map: closure under extensions.** Let `f : X ⟶ Y` be a morphism
of schemes and let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves on the small
étale site of `Y`. If restriction along `f` is bijective on étale cohomology for `F₁` and for `F₃`
in every degree, then it is bijective for `F₂` in every degree. -/
theorem etaleCohomologyRestrictionMap_bijective_of_shortExact
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact)
    (h₁ : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₁ q))
    (h₃ : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₃ q))
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f S.X₂ q) := by
  simp only [etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w}] at h₁ h₃ ⊢
  exact isBijectiveOnExt_of_shortExact (etaleAbelianInverseImage.{u, v} f) _ hS h₁ h₃ q

/-- **Dévissage for the restriction map: closure under binary biproducts.** If restriction along
`f` is bijective on étale cohomology for two abelian étale sheaves in every degree, then it is
bijective for their biproduct in every degree. -/
theorem etaleCohomologyRestrictionMap_bijective_biprod
    (F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q))
    (hG : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f G q))
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f (F ⊞ G) q) :=
  etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w} f
    (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact hF hG q

/-- **Dévissage for the restriction map: closure under retracts.** If `i : F' ⟶ F` and `p : F ⟶ F'`
satisfy `i ≫ p = 𝟙 F'` and restriction along `f` is bijective on étale cohomology for `F` in degree
`q`, then it is bijective for `F'` in degree `q`. -/
theorem etaleCohomologyRestrictionMap_bijective_of_retract
    {F F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (i : F' ⟶ F) (p : F ⟶ F') (hip : i ≫ p = 𝟙 F') {q : ℕ}
    (h : Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F' q) := by
  simp only [etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w}] at h ⊢
  exact isBijectiveOnExt_of_retract (etaleAbelianInverseImage.{u, v} f) _ i p hip h

end RestrictionDevissage

end Stacks.EtaleCohomology

end

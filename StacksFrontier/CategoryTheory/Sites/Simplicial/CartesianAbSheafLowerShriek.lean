module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms

/-!
# Cartesian abelian sheaves and the comparison with lower shriek

Let `S` be a simplicial-site situation and `F` an abelian sheaf on its total site. The canonical
map `g_{n!}(F_n) ⟶ bar_n(F)` of `componentLowerShriekMap'` compares the lower shriek image of the
degree-`n` restriction of `F` with the degree-`n` term of the simplex-coefficient resolution.
Restricted to the component of simplicial degree `m` that map is the direct sum, over the simplex
maps `φ : ⦋n⦌ ⟶ ⦋m⦌`, of the inverse-image transitions at `φ`
(`restrictAb_map_componentLowerShriekMap_eq`), so it is invertible in every degree exactly when
every transition is — which is cartesianness.

One direction is `isIso_componentLowerShriekMap'`. This file proves the converse and packages the
two as an equivalence: a map of finite coproducts taken summandwise is invertible exactly when all
of its components are, and the restrictions to the simplicial degrees are jointly conservative.

The equivalence is the sheaf-level form of the projection formula of Stacks 0D9E (1): the
degree-`n` term of the simplex-coefficient resolution is the tensor product `g_{n!}ℤ ⊗_ℤ F`.

## Main results

* `CategoryTheory.Limits.isIso_sigma_map_iff`: a map of coproducts of a family of objects, taken
  summandwise, is invertible exactly when all of its components are.
* `CategoryTheory.SimplicialSiteSituation.isCartesianAbSheaf_of_isIso_componentLowerShriekMap`:
  if the canonical comparison map is invertible in every simplicial degree then `F` is cartesian.
* `CategoryTheory.SimplicialSiteSituation.isCartesianAbSheaf_iff_isIso_componentLowerShriekMap`:
  **an abelian sheaf on the total site is cartesian exactly when the canonical comparison map
  `g_{n!}(F_n) ⟶ bar_n(F)` is invertible for every simplicial degree `n`.**

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.Limits

/-- **A map of coproducts of a family of objects, taken summandwise, is invertible exactly when
all of its components are.** The summand inclusions of a coproduct in a category with zero
morphisms admit retractions that kill the other summands, and conjugating by them turns the
summandwise map into each of its components. -/
theorem isIso_sigma_map_iff {ι : Type*} {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : ι → C} [HasCoproduct X] [HasCoproduct Y] (f : ∀ i, X i ⟶ Y i) :
    IsIso (Sigma.map f) ↔ ∀ i, IsIso (f i) := by
  classical
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · let pX : ∀ k, ∐ X ⟶ X k := fun k =>
      Sigma.desc fun j => if hj : j = k then eqToHom (congrArg X hj) else 0
    let pY : ∀ k, ∐ Y ⟶ Y k := fun k =>
      Sigma.desc fun j => if hj : j = k then eqToHom (congrArg Y hj) else 0
    have hiX : Sigma.ι X i ≫ pX i = 𝟙 (X i) := by simp [pX]
    have hiY : Sigma.ι Y i ≫ pY i = 𝟙 (Y i) := by simp [pY]
    have hsq : pX i ≫ f i = Sigma.map f ≫ pY i := by
      refine Sigma.hom_ext _ _ fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp [pX, pY]
      · simp [pX, pY, hj]
    refine ⟨Sigma.ι Y i ≫ inv (Sigma.map f) ≫ pX i, ?_, ?_⟩
    · rw [← Sigma.ι_map_assoc, IsIso.hom_inv_id_assoc, hiX]
    · rw [Category.assoc, Category.assoc, hsq, IsIso.inv_hom_id_assoc, hiY]
  · have : ∀ i, IsIso (f i) := h
    refine ⟨Sigma.map fun i => inv (f i), ?_, ?_⟩
    all_goals exact Sigma.hom_ext _ _ fun j => by simp

end CategoryTheory.Limits

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] componentFunctorHasCoproductsOfShape
attribute [local instance] hasColimitsOfShapeDiscreteSheafComponent

variable (S : SimplicialSiteSituation.{u}) (F : Sheaf S.totalTopology Ab.{u})

/-- **The converse of `isIso_componentLowerShriekMap'`.** If the canonical comparison map from the
lower shriek image of the degree-`n` restriction of `F` to the degree-`n` term of the
simplex-coefficient resolution is invertible for every `n`, then `F` is cartesian: restricted to
the component of degree `m` that map is the direct sum of the inverse-image transitions at the
simplex maps `⦋n⦌ ⟶ ⦋m⦌`, a coproduct map is invertible only if each of its components is, and
the transition of Stacks 07TF is the component at `φ` after forgetting the group structure. -/
theorem isCartesianAbSheaf_of_isIso_componentLowerShriekMap
    (h : ∀ n : SimplexCategory, IsIso ((componentLowerShriekMap' S n).app F)) :
    IsCartesianAbSheaf S F := by
  intro m n φ
  have := h m
  have key : (Limits.Sigma.map fun ψ : m ⟶ n => (S.fiberTransitionAb' ψ).app F) =
      (((S.componentLowerShriekRestrictionIsoCoproduct m n).app ((S.restrictAb m).obj F)) ≪≫
          Limits.sigmaObjIso (fun ψ : m ⟶ n => S.transitionInverseImageAb ψ)
            ((S.restrictAb m).obj F)).inv ≫
        (S.restrictAb n).map ((componentLowerShriekMap' S m).app F) ≫
          (abelianComponentBarIsoCoproduct' S F m n).hom := by
    rw [restrictAb_map_componentLowerShriekMap_eq S F m n]
    simp
  have h₃ : IsIso (Limits.Sigma.map fun ψ : m ⟶ n => (S.fiberTransitionAb' ψ).app F) := by
    rw [key]; infer_instance
  have hfib : IsIso ((S.fiberTransitionAb' φ).app F) :=
    (Limits.isIso_sigma_map_iff _).1 h₃ φ
  have : IsIso ((abelianTransitionOfFiber' S φ).app F) := by
    have h2 : (abelianTransitionOfFiber' S φ).app F =
        inv ((S.transitionInverseImageAbIso φ).hom.app ((S.restrictAb m).obj F)) ≫
          (S.fiberTransitionAb' φ).app F := by
      rw [congr_app (S.fiberTransitionAb_eq' φ) F, NatTrans.comp_app, Functor.whiskerLeft_app,
        IsIso.inv_hom_id_assoc]
    rw [h2]
    infer_instance
  have hforget : IsIso ((sheafCompose (S.componentTopology n) (forget Ab.{u})).map
      ((abelianTransitionOfFiber' S φ).app F)) := inferInstance
  rwa [abelianTransitionOfFiber_forget' S φ F] at hforget

/-- **The sheaf-level form of Stacks 0D9E (1).** An abelian sheaf on the total site is cartesian
exactly when the canonical map from the lower shriek image of its degree-`n` restriction to the
degree-`n` term of the simplex-coefficient resolution is invertible for every simplicial degree
`n`. Restricted to the component of degree `m` that map is the direct sum, over the simplex maps
`φ : ⦋n⦌ ⟶ ⦋m⦌`, of the inverse-image transitions at `φ`, and the restrictions to the simplicial
degrees are jointly conservative. -/
theorem isCartesianAbSheaf_iff_isIso_componentLowerShriekMap :
    IsCartesianAbSheaf S F ↔
      ∀ n : SimplexCategory, IsIso ((componentLowerShriekMap' S n).app F) :=
  ⟨fun hF n => isIso_componentLowerShriekMap' S F hF n,
    isCartesianAbSheaf_of_isIso_componentLowerShriekMap S F⟩

end CategoryTheory.SimplicialSiteSituation

end

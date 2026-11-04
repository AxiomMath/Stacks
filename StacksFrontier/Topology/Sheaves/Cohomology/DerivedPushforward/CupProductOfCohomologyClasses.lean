module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct

/-!
# The cup product of two cohomology classes is the tensor product of their adjuncts

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K, M ∈ D(𝒪_X)`.  For
`Y` the point `(pt, A)` with `A = Γ(X, 𝒪_X)`, so that `Rf_*(-) = RΓ(X, -)`, a cohomology class
`ξ ∈ H^i(X, K)` is a morphism `ξ : A[-i] ⟶ Rf_*K` in `D(A)` and, by the adjunction
`Lf^* ⊣ Rf_*`, the same thing as a morphism `ξ̃ : 𝒪_X[-i] ⟶ K` in `D(𝒪_X)`.  Two such classes
can be multiplied in two ways:

* tensor them on `Y` and apply the relative cup product `μ` of Stacks 0B68, obtaining
  `ξ ∪ η : A[-i-j] = A[-i] ⊗^L_A A[-j] ⟶ Rf_*K ⊗^L_A Rf_*M ⟶ Rf_*(K ⊗^L_{𝒪_X} M)`, or
* tensor their adjuncts on `X`, obtaining
  `ξ̃ ⊗ η̃ : 𝒪_X[-i-j] = 𝒪_X[-i] ⊗^L_{𝒪_X} 𝒪_X[-j] ⟶ K ⊗^L_{𝒪_X} M`.

The two agree: the adjunct of `ξ ∪ η` is `ξ̃ ⊗ η̃`.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.homEquiv_symm_adjunctionBitensorMap`: the
  abstract form, for an adjunction `L ⊣ R` with binary functors `A` on the source and `B` on
  the target and a morphism of bifunctors `α : A ⋙ L ⟶ (L × L) ⋙ B`.  The adjoint transpose of
  `A(ξ, η)` followed by the abstract relative cup product is `α` followed by `B` of the pair of
  adjoint transposes of `ξ` and `η`.
* `Stacks.Cohomology.DerivedRelativeCupProduct.homEquiv_symm_comp_adjunctionBitensorMap`: the
  same with a morphism `χ : W ⟶ A(U, V)` precomposed.
* `Stacks.Cohomology.DerivedRelativeCupProduct.homEquiv_symm_relativeCupProduct`: for classes
  `ξ : U ⟶ Rf_*K` and `η : V ⟶ Rf_*M` on the target, the adjunct of `(ξ ⊗ η) ≫ μ` is the
  derived pullback-tensor comparison of Stacks 079U followed by the tensor product `ξ̃ ⊗ η̃` of
  their adjuncts.
* `Stacks.Cohomology.DerivedRelativeCupProduct.homEquiv_symm_comp_relativeCupProduct`: the same
  with a morphism `χ : W ⟶ U ⊗^L_{𝒪_Y} V` precomposed.

## References

* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FNH](https://stacks.math.columbia.edu/tag/0FNH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedAdjunction derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedProjectionFormula (pullbackTensorComparison)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedRelativeCupProduct

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The adjoint transpose of `A(ξ, η)` followed by the abstract relative cup product is `α`
followed by `B` of the pair of adjoint transposes of `ξ` and `η`. -/
theorem homEquiv_symm_adjunctionBitensorMap {U V : C} {G G' : D}
    (ξ : U ⟶ R.obj G) (η : V ⟶ R.obj G') :
    (adj.homEquiv _ _).symm (A.map (ξ ×ₘ η) ≫ adjunctionBitensorMap adj A B α G G') =
      α.app (U, V) ≫ B.map ((adj.homEquiv U G).symm ξ ×ₘ (adj.homEquiv V G').symm η) := by
  unfold adjunctionBitensorMap
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit]
  have ha := α.naturality (ξ ×ₘ η : ((U, V) : C × C) ⟶ ((R.obj G, R.obj G') : C × C))
  change L.map (A.map (ξ ×ₘ η)) ≫ α.app (R.obj G, R.obj G') =
    α.app (U, V) ≫ B.map (L.map ξ ×ₘ L.map η) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp, prod_comp]

/-- The adjoint transpose of a morphism `χ : W ⟶ A(U, V)` followed by `A(ξ, η)` and the abstract
relative cup product is `L χ` followed by `α` and by `B` of the pair of adjoint transposes of
`ξ` and `η`. -/
theorem homEquiv_symm_comp_adjunctionBitensorMap {W U V : C} {G G' : D}
    (χ : W ⟶ A.obj (U, V)) (ξ : U ⟶ R.obj G) (η : V ⟶ R.obj G') :
    (adj.homEquiv _ _).symm (χ ≫ A.map (ξ ×ₘ η) ≫ adjunctionBitensorMap adj A B α G G') =
      L.map χ ≫ α.app (U, V) ≫
        B.map ((adj.homEquiv U G).symm ξ ×ₘ (adj.homEquiv V G').symm η) := by
  rw [Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_adjunctionBitensorMap]

end Abstract

section Uncurry

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]

/-- The uncurried bifunctor on a product of two morphisms. -/
private lemma uncurry_map_mkHom (T : C₁ ⥤ C₂ ⥤ C₃) {Z Z' : C₁} {W W' : C₂}
    (u : Z ⟶ Z') (v : W ⟶ W') :
    (Functor.uncurry.obj T).map (u ×ₘ v) = (T.map u).app W ≫ (T.obj Z').map v :=
  rfl

end Uncurry

section AbstractCurried

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (α : Functor.uncurry.obj TC ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TD)

/-- The agreement of the two products of a pair of morphisms, with both bifunctors written in
curried form. -/
theorem homEquiv_symm_adjunctionBitensorMap_curried {U V : C} {G G' : D}
    (ξ : U ⟶ R.obj G) (η : V ⟶ R.obj G') :
    (adj.homEquiv _ _).symm
        ((TC.map ξ).app V ≫ (TC.obj (R.obj G)).map η ≫
          adjunctionBitensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α G G') =
      α.app (U, V) ≫ (TD.map ((adj.homEquiv U G).symm ξ)).app (L.obj V) ≫
        (TD.obj G).map ((adj.homEquiv V G').symm η) := by
  have h := homEquiv_symm_adjunctionBitensorMap adj (Functor.uncurry.obj TC)
    (Functor.uncurry.obj TD) α ξ η
  rwa [uncurry_map_mkHom TC, uncurry_map_mkHom TD, Category.assoc] at h

/-- The agreement of the two products of a pair of morphisms, with a morphism
`χ : W ⟶ TC U V` precomposed and both bifunctors written in curried form. -/
theorem homEquiv_symm_comp_adjunctionBitensorMap_curried {W U V : C} {G G' : D}
    (χ : W ⟶ (TC.obj U).obj V) (ξ : U ⟶ R.obj G) (η : V ⟶ R.obj G') :
    (adj.homEquiv _ _).symm
        (χ ≫ (TC.map ξ).app V ≫ (TC.obj (R.obj G)).map η ≫
          adjunctionBitensorMap adj (Functor.uncurry.obj TC) (Functor.uncurry.obj TD) α G G') =
      L.map χ ≫ α.app (U, V) ≫ (TD.map ((adj.homEquiv U G).symm ξ)).app (L.obj V) ≫
        (TD.obj G).map ((adj.homEquiv V G').symm η) := by
  rw [Adjunction.homEquiv_naturality_left_symm,
    homEquiv_symm_adjunctionBitensorMap_curried]

end AbstractCurried

universe u

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The two constructions of the cup product agree: the adjunct of the tensor product `ξ ⊗ η` of
two cohomology classes followed by the relative cup product of Stacks 0B68 is the derived
pullback-tensor comparison of Stacks 079U followed by the tensor product `ξ̃ ⊗ η̃` of their
adjuncts. -/
@[stacks 0FP2 "the identification-free core, at arbitrary objects of `D(𝒪_Y)` in place of the \
  source's shifted structure sheaves, and for an arbitrary morphism of ringed spaces"]
theorem homEquiv_symm_relativeCupProduct
    {U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    {K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (ξ : U ⟶ (derivedPushforward f).obj K) (η : V ⟶ (derivedPushforward f).obj M) :
    ((derivedAdjunction f).homEquiv _ _).symm
        (((derivedTensorProductFunctor Y.sheaf).map ξ).app V ≫
          ((derivedTensorProductFunctor Y.sheaf).obj
              ((derivedPushforward f).obj K)).map η ≫
            relativeCupProduct f K M) =
      (pullbackTensorComparison f).app (U, V) ≫
        ((derivedTensorProductFunctor X.sheaf).map
              (((derivedAdjunction f).homEquiv U K).symm ξ)).app
            ((derivedPullback f).obj V) ≫
          ((derivedTensorProductFunctor X.sheaf).obj K).map
            (((derivedAdjunction f).homEquiv V M).symm η) :=
  homEquiv_symm_adjunctionBitensorMap_curried (derivedAdjunction f)
    (derivedTensorProductFunctor Y.sheaf) (derivedTensorProductFunctor X.sheaf)
    (pullbackTensorComparison f) ξ η

/-- Let `χ : W ⟶ U ⊗^L_{𝒪_Y} V`. The adjunct of `χ` followed by `ξ ⊗ η` and the relative cup
product of Stacks 0B68 is `Lf^*χ` followed by the derived pullback-tensor comparison of
Stacks 079U and by the tensor product `ξ̃ ⊗ η̃` of the adjuncts. -/
@[stacks 0FP2 "stated for an arbitrary morphism of ringed spaces, with the source's \
  identification `𝒪_Y[-i-j] = 𝒪_Y[-i] ⊗ᴸ 𝒪_Y[-j]` carried as an arbitrary morphism `χ`"]
theorem homEquiv_symm_comp_relativeCupProduct
    {W U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    {K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (χ : W ⟶ ((derivedTensorProductFunctor Y.sheaf).obj U).obj V)
    (ξ : U ⟶ (derivedPushforward f).obj K) (η : V ⟶ (derivedPushforward f).obj M) :
    ((derivedAdjunction f).homEquiv _ _).symm
        (χ ≫ ((derivedTensorProductFunctor Y.sheaf).map ξ).app V ≫
          ((derivedTensorProductFunctor Y.sheaf).obj
              ((derivedPushforward f).obj K)).map η ≫
            relativeCupProduct f K M) =
      (derivedPullback f).map χ ≫ (pullbackTensorComparison f).app (U, V) ≫
        ((derivedTensorProductFunctor X.sheaf).map
              (((derivedAdjunction f).homEquiv U K).symm ξ)).app
            ((derivedPullback f).obj V) ≫
          ((derivedTensorProductFunctor X.sheaf).obj K).map
            (((derivedAdjunction f).homEquiv V M).symm η) :=
  homEquiv_symm_comp_adjunctionBitensorMap_curried (derivedAdjunction f)
    (derivedTensorProductFunctor Y.sheaf) (derivedTensorProductFunctor X.sheaf)
    (pullbackTensorComparison f) χ ξ η

end Stacks.Cohomology.DerivedRelativeCupProduct

end

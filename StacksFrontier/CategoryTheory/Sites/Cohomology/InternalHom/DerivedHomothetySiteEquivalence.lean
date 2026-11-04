module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSliceTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomothetyRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceModels

/-!
# The homothety map along an equivalence of ringed sites

Let `e : Y ≌ X` be an equivalence of the underlying sites of two ringed sites with an invertible
structure map `φ : 𝒪_Y ⟶ e_* 𝒪_X`, and `φ_*` the induced equivalence of derived categories.
For `K` in `D(𝒪_X)`, `φ_*` of the homothety map `𝒪_X ⟶ R𝓗om(K, K)` is invertible exactly when
the homothety map of `φ_* K` is. The same holds for restriction to a slice followed by such an
equivalence.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_map_derivedHomothety_pushforward_iff`: the statement for
  an equivalence of ringed sites.
* `AlgebraicGeometry.RingedSite.isIso_map_derivedHomothety_sliceEquivTransport_iff`: the
  statement for a slice followed by an equivalence of ringed sites.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section SiteEquivalence

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [hφ : IsIso φ]

/-- The pushforward along an invertible structure map carries the unit module to the unit
module. -/
def pushforwardUnitIsoOfIso :
    (SheafOfModules.pushforward.{u} φ).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  haveI : IsIso (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ⟶
      eqv.functor.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj from φ.hom) :=
    ((sheafToPresheaf _ _).mapIso (@asIso _ _ _ _ φ hφ)).isIso_hom
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.pushforwardUnitIso
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ⟶
        eqv.functor.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj from φ.hom))

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor Y.O).Additive] [∀ M, ((sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor Y.O) (ComplexShape.up ℤ)]
  [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- The derived pushforward along an equivalence of ringed sites is fully faithful. -/
def mapDerivedCategoryPushforwardFullyFaithful :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.FullyFaithful :=
  haveI := pushforward_additive eqv φ
  haveI : (SheafOfModules.pushforward.{u} φ).IsEquivalence :=
    (modulesEquiv eqv φ (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
      (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
      (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ)).isEquivalence_functor
  haveI := Stacks.Injectives.mapDerivedCategory_isEquivalence (SheafOfModules.pushforward.{u} φ)
  Functor.FullyFaithful.ofFullyFaithful _

/-- The derived pushforward along an equivalence of ringed sites carries `𝒪_X` to `𝒪_Y`. -/
def mapDerivedCategoryPushforwardUnitIso :
    haveI := pushforward_additive eqv φ
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  haveI := pushforward_additive eqv φ
  ((SheafOfModules.pushforward.{u} φ).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).mapIso
      (pushforwardUnitIsoOfIso eqv φ)

/-- **The homothety map along an equivalence of ringed sites.** The transport of the homothety
map of `K` is invertible exactly when the homothety map of the transport of `K` is. -/
theorem isIso_map_derivedHomothety_pushforward_iff
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    haveI := pushforward_additive eqv φ
    IsIso ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map (derivedHomothety X K)) ↔
      IsIso (derivedHomothety Y ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K)) :=
  have := pushforward_additive eqv φ
  isIso_map_derivedHomothety_iff X Y _ (mapDerivedCategoryPushforwardFullyFaithful eqv φ) K
    (mapDerivedCategoryPushforwardUnitIso eqv φ)
    (fun L => siteEquivDerivedSheafHomIsoOfIso eqv φ K L)
    (fun a => siteEquivDerivedSheafHomIsoOfIso_natural_right eqv φ a)

end SiteEquivalence

section SliceTransport

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

attribute [local instance] sliceSheafTensorAdditive
  sliceSheafTensorObjAdditive

variable {X Y : RingedSite.{u, u, u}} (U : X.C) (eqv : Y.C ≌ (X.over U).C)
  [eqv.functor.IsContinuous Y.J (X.over U).J] [eqv.inverse.IsContinuous (X.over U).J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J (X.over U).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))
  [hφ : IsIso φ]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.over U).J AddCommGrpCat.{u}]
  [(X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.O.over U))) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  [hl : PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [hc : PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor Y.O).Additive] [∀ M, ((sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor Y.O) (ComplexShape.up ℤ)]

/-- **The homothety map along a slice followed by an equivalence of ringed sites.** For `K` in
`D(𝒪_X)`, restricting the homothety map of `K` to the slice at `U` and transporting it along an
equivalence of ringed sites `Y ≌ X/U` gives an isomorphism exactly when the homothety map of the
transported restriction of `K` is one. -/
theorem isIso_map_derivedHomothety_sliceEquivTransport_iff
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    haveI := sliceEquivTransport_preservesFiniteLimits U eqv φ
    haveI := sliceEquivTransport_preservesFiniteColimits U eqv φ
    IsIso ((sliceEquivTransport U eqv φ).mapDerivedCategory.map (derivedHomothety X K)) ↔
      IsIso (derivedHomothety Y ((sliceEquivTransport U eqv φ).mapDerivedCategory.obj K)) := by
  have := sliceEquivTransport_preservesFiniteLimits U eqv φ
  have := sliceEquivTransport_preservesFiniteColimits U eqv φ
  have := pushforward_preservesFiniteLimitsOfIso (X := X.over U) (Y := Y) eqv φ
  have := pushforward_preservesFiniteColimitsOfIso (X := X.over U) (Y := Y) eqv φ
  have : (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive :=
    SheafOfModules.overFunctor_additive _ _
  have : (sliceEquivPushforward U eqv φ).Additive :=
    pushforward_additive (X := X.over U) (Y := Y) eqv φ
  let c := Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (sliceEquivPushforward U eqv φ)
  have : (sliceEquivPushforward U eqv φ).mapDerivedCategory.ReflectsIsomorphisms :=
    (mapDerivedCategoryPushforwardFullyFaithful (X := X.over U) (Y := Y) eqv φ).reflectsIsomorphisms
  refine (NatIso.isIso_map_iff c (derivedHomothety X K)).trans ?_
  refine (isIso_iff_of_reflects_iso _ (sliceEquivPushforward U eqv φ).mapDerivedCategory).trans ?_
  refine (isIso_map_derivedHomothety_overFunctor_iff X U K).trans ?_
  refine (isIso_iff_of_reflects_iso _ (sliceEquivPushforward U eqv φ).mapDerivedCategory).symm.trans
    ?_
  refine (isIso_map_derivedHomothety_pushforward_iff (X := X.over U) (Y := Y) eqv φ _).trans ?_
  exact isIso_derivedHomothety_iff_of_iso Y (c.app K).symm

end SliceTransport

end AlgebraicGeometry.RingedSite

end

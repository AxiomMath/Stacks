module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Cohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FiniteDirectImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeBoundedBelow
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeTransformation
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModulesFunctor

/-!
# Derived direct image and the comparison of the big and small étale sites

Let `B` be a big étale site and `f : T ⟶ S` a morphism of it. Write `π_S⁻¹` for the inverse
image of abelian sheaves from the small étale site of `S` to the big étale site over `S`, which is
exact (Stacks 0DDI), `Rf_{small,*}` and `Rf_{big,*}` for right derived functors of the direct
images of abelian sheaves along `f` on the unbounded derived categories. This file constructs the
canonical base change map

`π_S⁻¹ ∘ Rf_{small,*} ⟶ Rf_{big,*} ∘ π_T⁻¹`

of Cohomology on Sites, Remark 07A7 — the derived map that the underived base change map
`AlgebraicGeometry.bigSmallEtaleBaseChange` of Stacks 0DDJ (1) induces — and proves part (4) of
Stacks 0DDJ: for `f` finite it is an isomorphism on the whole unbounded derived category.

## Main definitions

* `AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` — the base change map
  `π_S⁻¹ ∘ Rf_{small,*} ⟶ Rf_{big,*} ∘ π_T⁻¹`.

## Main results

* `AlgebraicGeometry.isIso_of_forall_isIso_bigEtaleRestriction_mapDerivedCategory_map` — the
  restrictions to the small étale sites of the objects of the big étale site jointly detect
  isomorphisms of the derived category.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_of_isFinite` — **Stacks 0DDJ (4)**.
* `AlgebraicGeometry.etaleAbelianDerivedBaseChange_eq_derivedBaseChangeMap` — the base change map
  (0A2A) of Mathlib's small étale sites is the generic derived base change map.
* `AlgebraicGeometry.isIso_derivedBaseChangeMap_bounded_app_of_isIso_etaleAbelianDerivedBaseChange`
  — from Mathlib's small étale sites to the bounded ones.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_app_of_forall_isIso` — the reduction of
  the big/small comparison to the fibre squares.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_app_of_cohomologyCommutesWithBaseChange`
  — **Stacks 0DDJ (2)**, granted Stacks 095T for `f`.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_app_toSheaf_of_zmod` — **Stacks 0DDJ
  (3)**, granted Stacks 0F0C for `f`.

## References

* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Opposite
open Stacks.Cohomology.ZModSheaf (zmodRingSheaf)

universe u v w₁ w₂ w₃ w₄

namespace AlgebraicGeometry

-- The site-modules `Abelian` instance is stated in a `max` universe; on the `ℤ/nℤ`-module sheaves
-- of the small étale site it leaves a universe metavariable unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigEtaleSite.{u})

/-! ### Restriction to the small étale sites -/

section Restriction

variable (S : B.Scheme)

/-- Restriction of abelian sheaves to the small étale site of an object `U` of the big étale site
over `S` is a right adjoint, of the sheaf pullback along `i_U`. -/
public instance bigEtaleRestriction_isRightAdjoint (U : BigEtaleOver B S.obj S.property) :
    (bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).IsRightAdjoint :=
  ((smallEtaleToBigEtaleFunctor B U.left S U.hom).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B U.left.obj U.left.property)
    (BigEtaleOver.topology B S.obj S.property)).isRightAdjoint

/-- Restriction of abelian sheaves to the small étale site of an object of the big étale site is
additive. -/
public instance bigEtaleRestriction_additive (U : BigEtaleOver B S.obj S.property) :
    (bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).Additive where
  map_add := by intros; rfl

/-- **The restrictions to the small étale sites detect isomorphisms of the derived category.** A
morphism of the derived category of abelian sheaves on the big étale site over `S` which becomes
invertible after restriction to the small étale site of every object `U` is invertible. -/
public theorem isIso_of_forall_isIso_bigEtaleRestriction_mapDerivedCategory_map
    [HasDerivedCategory.{w₁}
      (Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1})]
    [∀ U : BigEtaleOver B S.obj S.property, HasDerivedCategory.{w₂}
      (Sheaf (SmallEtale.topology B U.left.obj U.left.property) AddCommGrpCat.{u + 1})]
    {K L : DerivedCategory
      (Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1})} (ψ : K ⟶ L)
    (h : ∀ U : BigEtaleOver B S.obj S.property,
      IsIso ((bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).mapDerivedCategory.map ψ)) :
    IsIso ψ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_forall_isIso_bigEtaleRestriction_map B AddCommGrpCat.{u + 1} _ fun U ↦ ?_
  exact ((bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).isIso_mapDerivedCategory_map_iff
    ψ).1 (h U) n

end Restriction

/-! ### The derived base change map -/

section Map

variable {T S : B.Scheme} (f : T ⟶ S)
  [HasDerivedCategory.{w₁} (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₂} (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₃}
    (Sheaf (BigEtaleOver.topology B T.obj T.property) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄}
    (Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1})]
  (RfSmall : DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1})
    ⥤ DerivedCategory (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}))
  (RfBig :
    DerivedCategory (Sheaf (BigEtaleOver.topology B T.obj T.property) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1}))
  (αSmall : (B.smallPushforward f AddCommGrpCat.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfSmall)
  (αBig : ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfBig)
  [RfSmall.IsRightDerivedFunctor αSmall (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [RfBig.IsRightDerivedFunctor αBig (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]

/-- **The base change map `π_S⁻¹ ∘ Rf_{small,*} ⟶ Rf_{big,*} ∘ π_T⁻¹`** of the square of topoi
`π_S ∘ f_big = f_small ∘ π_T` (Cohomology on Sites, Remark 07A7), on unbounded derived
categories of abelian sheaves: the derived map
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap` of the abelian base change map
`π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹` of `AlgebraicGeometry.bigSmallEtaleBaseChange`, the
exact functors `π_S⁻¹` and `π_T⁻¹` acting degreewise. -/
public def bigSmallEtaleDerivedBaseChange :
    RfSmall ⋙ ((SmallEtale.inclusion B S.obj S.property).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property)).mapDerivedCategory ⟶
      ((SmallEtale.inclusion B T.obj T.property).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property)).mapDerivedCategory ⋙ RfBig :=
  haveI := smallEtaleSheaf_isGrothendieckAbelian B T
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
    ((SmallEtale.inclusion B T.obj T.property).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B T.obj T.property) (BigEtaleOver.topology B T.obj T.property))
    ((SmallEtale.inclusion B S.obj S.property).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property))
    (B.smallPushforward f AddCommGrpCat.{u + 1})
    ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property))
    RfSmall RfBig αSmall αBig
    (bigSmallEtaleBaseChange B AddCommGrpCat.{u + 1} f
      (bigEtaleAbelianProjectionAdjunction B T) (bigEtaleAbelianProjectionAdjunction B S))

/-- A morphism of functors out of the unbounded derived category of a Grothendieck abelian category
is invertible at `K` as soon as it is invertible at every K-injective complex isomorphic to `K`. -/
private theorem isIso_app_of_forall_isKInjective_iso {A : Type (u + 2)} [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasDerivedCategory.{w₁} A] {D : Type*}
    [Category D] {F G : DerivedCategory A ⥤ D} (α : F ⟶ G) (K : DerivedCategory A)
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≅ K) →
      IsIso (α.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    IsIso (α.app K) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  exact h I hI e

/-- **Stacks 0DDJ (4).** Let `f : T ⟶ S` be a finite morphism of a big étale site. Then
`π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for all `K` in the unbounded derived category
`D(T_étale)` of abelian sheaves on the small étale site of `T`: the canonical base change map
`AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` is an isomorphism of functors.

Here `Rf_{small,*}` and `Rf_{big,*}` are any right derived functors, on the unbounded derived
categories, of the direct images of abelian sheaves along `f` on the small and the big étale
sites. -/
public theorem isIso_bigSmallEtaleDerivedBaseChange_of_isFinite [IsFinite (B.inclusion.map f)] :
    IsIso (bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig) := by
  have := smallEtaleSheaf_isGrothendieckAbelian B T
  have := bigEtaleSheaf_isGrothendieckAbelian B T
  have := bigEtaleAbelianPushforward_preservesFiniteColimits_of_isFinite B f
  have := isIso_bigSmallEtaleBaseChange_abelian_of_isFinite B f
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine isIso_app_of_forall_isKInjective_iso _ K fun I hI _ ↦ ?_
  obtain ⟨J, t, hJ, ht⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    ((((SmallEtale.inclusion B T.obj T.property).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  refine (Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_quasiIso
    _ _ _ _ RfSmall RfBig αSmall αBig _ I hI t hJ).2 ?_
  have : IsIso ((NatTrans.mapHomologicalComplex (bigSmallEtaleBaseChange B AddCommGrpCat.{u + 1} f
      (bigEtaleAbelianProjectionAdjunction B T) (bigEtaleAbelianProjectionAdjunction B S))
      (ComplexShape.up ℤ)).app I) := by
    refine ⟨⟨(NatTrans.mapHomologicalComplex (inv (bigSmallEtaleBaseChange B AddCommGrpCat.{u + 1}
      f (bigEtaleAbelianProjectionAdjunction B T) (bigEtaleAbelianProjectionAdjunction B S)))
      (ComplexShape.up ℤ)).app I, ?_, ?_⟩⟩ <;> ext n <;> simp
  have : ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  infer_instance

end Map


/-! ### The base change map (0A2A) of Mathlib's small étale sites -/

section SmallEtale

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology

/-- The comparison `derivedBaseChangeMapUnit` for the base change data of a square of schemes and
a transformation `θ`, written out. -/
private theorem derivedBaseChangeMapUnit_app_etaleAbelian {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (θ : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)) :
    (Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapUnit
        (etaleAbelianInverseImage.{u, v} g') (etaleAbelianInverseImage.{u, v} g)
        (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDirectImage.{u, v} f')
        (etaleAbelianDerivedDirectImage.{u, v} f')
        (etaleAbelianDerivedDirectImageUnit.{u, v} f') θ).app K =
      (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.hom.app
          (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map (((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
          (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory θ (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
          (ComplexShape.up ℤ)).inv).app K) ≫
        (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
          (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (etaleAbelianDerivedDirectImage.{u, v} f').map
          ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K) :=
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapUnit_app _ _ _ _ _ _ θ K

/-- **The base change map (0A2A) is the derived base change map of the underived one.** The map
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of a commutative
square of schemes is `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap` of the underived
comparison `Stacks.EtaleCohomology.etaleAbelianBaseChange`. -/
public theorem etaleAbelianDerivedBaseChange_eq_derivedBaseChangeMap {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g) :
    etaleAbelianDerivedBaseChange.{u, v} f g g' f' h =
      Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
        (etaleAbelianInverseImage.{u, v} g') (etaleAbelianInverseImage.{u, v} g)
        (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDirectImage.{u, v} f')
        (etaleAbelianDerivedDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f')
        (etaleAbelianDerivedDirectImageUnit.{u, v} f)
        (etaleAbelianDerivedDirectImageUnit.{u, v} f')
        (etaleAbelianBaseChange.{u, v} f g g' f' h) := by
  have := Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp
    ((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh (etaleAbelianDerivedDirectImage.{u, v} f)
    (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    (etaleAbelianInverseImage.{u, v} g).mapDerivedCategory
  refine Functor.rightDerived_ext _ (Functor.whiskerRight
    (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    (etaleAbelianInverseImage.{u, v} g).mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, Category.assoc]
  rw [Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap_fac_app]
  have hfac := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h K
  rw [← cancel_epi ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
    (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))]
  have e : etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h =
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory (etaleAbelianBaseChange.{u, v} f g g' f' h)
      (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
      (ComplexShape.up ℤ)).inv := by
    rw [etaleAbelianHomotopyBaseChange]
  rw [hfac, derivedBaseChangeMapUnit_app_etaleAbelian, Iso.inv_hom_id_app_assoc, e]

end SmallEtale

/-! ### Exactness of the inverse images of the bounded small étale sites -/

section SmallInverseImage

variable {X Y : B.Scheme} (k : X ⟶ Y)

/-- Inverse image of abelian sheaves along a morphism of a big étale site, on the bounded small
étale sites, preserves finite limits. -/
public instance smallInverseImage_preservesFiniteLimits_addCommGrp :
    PreservesFiniteLimits (B.smallInverseImage k AddCommGrpCat.{u + 1}) :=
  preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp.{0, u} B k

/-- Inverse image of abelian sheaves on the bounded small étale sites preserves finite
colimits. -/
public instance smallInverseImage_preservesFiniteColimits_addCommGrp :
    PreservesFiniteColimits (B.smallInverseImage k AddCommGrpCat.{u + 1}) :=
  preservesFiniteColimits_smallEtaleSheafPullback_addCommGrp.{0, u} B k

/-- Inverse image of abelian sheaves on the bounded small étale sites is additive. -/
public instance smallInverseImage_additive_addCommGrp :
    (B.smallInverseImage k AddCommGrpCat.{u + 1}).Additive :=
  additive_smallEtaleSheafPullback_addCommGrp.{0, u} B k

end SmallInverseImage

/-! ### From Mathlib's small étale site to the bounded one -/

section Bounded

attribute [local instance] HasDerivedCategory.standard smallEtaleSheaf_isGrothendieckAbelian

open Stacks.EtaleCohomology

/-- Restriction of abelian sheaves from Mathlib's small étale site of a scheme of `B` to the
bounded small étale site preserves finite limits. -/
private instance toEtaleSiteRestriction_preservesFiniteLimits (X : B.Scheme) :
    PreservesFiniteLimits ((SmallEtale.toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property) X.obj.smallEtaleTopology) :=
  haveI := (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).isEquivalence_inverse
  inferInstance

/-- Restriction of abelian sheaves from Mathlib's small étale site to the bounded one preserves
finite colimits. -/
private instance toEtaleSiteRestriction_preservesFiniteColimits (X : B.Scheme) :
    PreservesFiniteColimits ((SmallEtale.toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property) X.obj.smallEtaleTopology) :=
  haveI := (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).isEquivalence_inverse
  inferInstance

/-- Restriction of abelian sheaves from Mathlib's small étale site to the bounded one is
additive. -/
private instance toEtaleSiteRestriction_additive (X : B.Scheme) :
    ((SmallEtale.toEtaleSite B X.obj X.property).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      X.obj.smallEtaleTopology).Additive where
  map_add := by intros; rfl

/-- The comparison of the bounded small étale site with Mathlib's, on abelian sheaves, is
additive. -/
private instance sheafEquiv_functor_additive (X : B.Scheme) :
    (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)
  (RF : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}))
  (RF' : DerivedCategory (Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})
    ⥤ DerivedCategory (Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1}))
  (αF : (B.smallPushforward f AddCommGrpCat.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  (αF' : (B.smallPushforward f' AddCommGrpCat.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]

/-- **The derived base change map of the bounded small étale sites is invertible where the base
change map (0A2A) of Mathlib's small étale sites is.** For a commutative square
`g' ≫ f = f' ≫ g` of a big étale site and a K-injective complex `I` of abelian sheaves on the
bounded small étale site of `X`, the derived base change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of the
bounded small étale sites is invertible at `I` if the map (0A2A) of Mathlib's small étale sites
is invertible at the image of `I` under the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
public theorem isIso_derivedBaseChangeMap_bounded_app_of_isIso_etaleAbelianDerivedBaseChange
    (I : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) ℤ)
    (hI : I.IsKInjective)
    (hM : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} (B.inclusion.map f) (B.inclusion.map g)
      (B.inclusion.map g') (B.inclusion.map f')
      (by rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, h])).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((SmallEtale.sheafEquiv B X.obj X.property
            AddCommGrpCat.{u + 1}).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))))) :
    IsIso ((Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
      (B.smallInverseImage g' AddCommGrpCat.{u + 1}) (B.smallInverseImage g AddCommGrpCat.{u + 1})
      (B.smallPushforward f AddCommGrpCat.{u + 1}) (B.smallPushforward f' AddCommGrpCat.{u + 1})
      RF RF' αF αF'
      ((mateEquiv (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
        (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})).symm
        (SmallEtale.boundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl
          h.symm)).natTrans).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  let e := SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}
  let IM := (e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hIM : CochainComplex.IsKInjective IM :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact e.functor e.inverse
      e.symm.toAdjunction I
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (B.inclusion.obj X).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse _
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (B.inclusion.obj X').smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse _
  have hKinj : ∀ (Z : B.Scheme) (J : CochainComplex (Sheaf Z.obj.smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ), J.IsKInjective → CochainComplex.IsKInjective
        ((((SmallEtale.toEtaleSite B Z.obj Z.property).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology B Z.obj Z.property)
          Z.obj.smallEtaleTopology).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    fun Z J _ ↦ CochainComplex.isKInjective_mapHomologicalComplex_of_exact _
      (SmallEtale.sheafEquiv B Z.obj Z.property AddCommGrpCat.{u + 1}).functor
      (SmallEtale.toEtaleSiteRestrictionAdjunction B AddCommGrpCat.{u + 1} Z) J
  let adjUg := etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map g)
  let adjUg' := etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map g')
  have hcube := Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app adjUg' adjUg
    (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
    (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})
    (SmallEtale.restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g' adjUg' _)
    (SmallEtale.restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g adjUg _)
    (SmallEtale.toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1}).hom
    (SmallEtale.toEtaleSitePushforwardBaseChangeIso B f' AddCommGrpCat.{u + 1}).inv
    (SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl h.symm)
    (SmallEtale.boundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl h.symm)
    (SmallEtale.baseChangeMate_cube_eq B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl h.symm
      adjUg _ adjUg' _)
  have := SmallEtale.isIso_restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g' adjUg'
    (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
  have := SmallEtale.isIso_restrictionPullbackBaseChange B AddCommGrpCat.{u + 1} g adjUg
    (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})
  have key := Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_of_cube
    (etaleAbelianInverseImage.{u, 0} (B.inclusion.map g'))
    (etaleAbelianInverseImage.{u, 0} (B.inclusion.map g))
    (etaleAbelianDirectImage.{u, 0} (B.inclusion.map f))
    (etaleAbelianDirectImage.{u, 0} (B.inclusion.map f'))
    (etaleAbelianDerivedDirectImage.{u, 0} (B.inclusion.map f))
    (etaleAbelianDerivedDirectImage.{u, 0} (B.inclusion.map f'))
    (etaleAbelianDerivedDirectImageUnit.{u, 0} (B.inclusion.map f))
    (etaleAbelianDerivedDirectImageUnit.{u, 0} (B.inclusion.map f'))
    ((mateEquiv adjUg' adjUg).symm (SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1}
      f g g' f' (g' ≫ f) rfl h.symm)).natTrans
    (B.smallInverseImage g' AddCommGrpCat.{u + 1}) (B.smallInverseImage g AddCommGrpCat.{u + 1})
    (B.smallPushforward f AddCommGrpCat.{u + 1}) (B.smallPushforward f' AddCommGrpCat.{u + 1})
    RF RF' αF αF'
    ((mateEquiv (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
      (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})).symm
      (SmallEtale.boundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl
        h.symm)).natTrans
    _ _ _ _ _ _ _ _ hcube (hKinj X') IM hIM (hKinj X _ hIM)
  have hθ : etaleAbelianBaseChange.{u, 0} (B.inclusion.map f) (B.inclusion.map g)
      (B.inclusion.map g') (B.inclusion.map f')
      (by rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, h]) =
      ((mateEquiv adjUg' adjUg).symm (SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1}
        f g g' f' (g' ≫ f) rfl h.symm)).natTrans := by
    rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0}
      (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') _
      (B.inclusion.map (g' ≫ f)) (B.inclusion.map_comp g' f)
      ((congrArg B.inclusion.map h).trans (B.inclusion.map_comp f' g))]
    rfl
  rw [etaleAbelianDerivedBaseChange_eq_derivedBaseChangeMap, hθ] at hM
  exact (NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Qh.mapIso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((e.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.app I)))).2
    (key.2 (Functor.map_isIso _ _))

end Bounded

/-! ### Sheaves of `ℤ/nℤ`-modules -/

section ZMod

/-- The sections of the image under `AlgebraicGeometry.SmallEtale.sheafEquiv` of the underlying
abelian sheaf of a sheaf of `ℤ/nℤ`-modules are annihilated by `n`. -/
public theorem nsmul_sheafEquiv_functor_toSheaf_eq_zero (X : B.Scheme) (n : ℕ)
    (M : SheafOfModules.{u + 1}
      (zmodRingSheaf.{u + 1} (SmallEtale.topology B X.obj X.property) n))
    (V : X.obj.Etaleᵒᵖ)
    (x : ToType (((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor.obj
      ((SheafOfModules.toSheaf _).obj M)).obj.obj V)) :
    n • x = 0 := by
  have h₀ : ((n : ℤ) • 𝟙 ((SheafOfModules.toSheaf _).obj M)) = 0 :=
    (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ _).2 fun W y ↦ by
      rw [natCast_zsmul]
      exact Stacks.Cohomology.ZModSheaf.nsmul_toSheaf_eq_zero _ _ M W y
  have h₁ : ((n : ℤ) • 𝟙 ((SmallEtale.sheafEquiv B X.obj X.property
      AddCommGrpCat.{u + 1}).functor.obj ((SheafOfModules.toSheaf _).obj M))) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, h₀, Functor.map_zero]
  have := (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ _).1 h₁ V x
  rwa [natCast_zsmul] at this

/-- The comparison `AlgebraicGeometry.SmallEtale.sheafEquiv` of the bounded small étale site of
`X` with Mathlib's, on sheaves of `ℤ/nℤ`-modules: the comparison of the underlying abelian sheaves,
whose values are again annihilated by `n`, read as sheaves of modules over the constant sheaf of
rings `ℤ/nℤ` (`Stacks.Cohomology.ZModSheaf.torsionSheafToModulesFunctor`). -/
public def zmodSheafEquivFunctor (X : B.Scheme) (n : ℕ) :
    SheafOfModules.{u + 1}
        (zmodRingSheaf.{u + 1} (SmallEtale.topology B X.obj X.property) n)
      ⥤ SheafOfModules.{u + 1}
        (zmodRingSheaf.{u + 1} X.obj.smallEtaleTopology n) :=
  Stacks.Cohomology.ZModSheaf.torsionSheafToModulesFunctor.{u + 1, u + 1} X.obj.smallEtaleTopology n
    (SheafOfModules.toSheaf.{u + 1}
      (zmodRingSheaf.{u + 1} (SmallEtale.topology B X.obj X.property) n) ⋙
      (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor)
    (nsmul_sheafEquiv_functor_toSheaf_eq_zero B X n)

/-- The comparison `AlgebraicGeometry.zmodSheafEquivFunctor` is additive. -/
public instance zmodSheafEquivFunctor_additive (X : B.Scheme) (n : ℕ) :
    (zmodSheafEquivFunctor B X n).Additive :=
  Stacks.Cohomology.ZModSheaf.torsionSheafToModulesFunctor_additive.{u + 1, u + 1}
    X.obj.smallEtaleTopology n _ (nsmul_sheafEquiv_functor_toSheaf_eq_zero B X n)

/-- The underlying abelian sheaf of the image of a sheaf of `ℤ/nℤ`-modules under
`AlgebraicGeometry.zmodSheafEquivFunctor` is the image of its underlying abelian sheaf. -/
public def zmodSheafEquivFunctorCompToSheaf (X : B.Scheme) (n : ℕ) :
    zmodSheafEquivFunctor B X n ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf.{u + 1}
        (zmodRingSheaf.{u + 1} (SmallEtale.topology B X.obj X.property) n)
        ⋙ (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor :=
  Stacks.Cohomology.ZModSheaf.torsionSheafToModulesFunctorCompToSheaf.{u + 1, u + 1}
    X.obj.smallEtaleTopology n _ (nsmul_sheafEquiv_functor_toSheaf_eq_zero B X n)

end ZMod

/-! ### Reduction of the big/small comparison to the small étale sites -/

section Reduction

open Stacks.EtaleCohomology
  (isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange)

attribute [local instance] HasDerivedCategory.standard smallEtaleSheaf_isGrothendieckAbelian
  bigEtaleSheaf_isGrothendieckAbelian

variable {T S : B.Scheme} (f : T ⟶ S)
  (RfSmall : DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1})
    ⥤ DerivedCategory (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}))
  (RfBig :
    DerivedCategory (Sheaf (BigEtaleOver.topology B T.obj T.property) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1}))
  (αSmall : (B.smallPushforward f AddCommGrpCat.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfSmall)
  (αBig : ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfBig)
  [RfSmall.IsRightDerivedFunctor αSmall (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [RfBig.IsRightDerivedFunctor αBig (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]

/-- **The big/small base change map is invertible where the small-site base change maps of the
fibre squares are.** Let `I` be a K-injective complex of abelian sheaves on the small étale site
of `T`. If, for every object `g : U ⟶ S` of the big étale site over `S`, the derived base change
map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of the bounded small étale sites for the fibre square
`U ×_S T` is invertible at `I`, then so is
`AlgebraicGeometry.bigSmallEtaleDerivedBaseChange`. The derived direct image along
`U ×_S T ⟶ U` is the total right derived functor
`Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditive`. -/
public theorem isIso_bigSmallEtaleDerivedBaseChange_app_of_forall_isIso
    (I : CochainComplex (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1}) ℤ)
    (hI : I.IsKInjective)
    (h : ∀ U : BigEtaleOver B S.obj S.property,
      IsIso ((Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
        (B.smallInverseImage ((Over.pullback f).obj U).hom AddCommGrpCat.{u + 1})
        (B.smallInverseImage U.hom AddCommGrpCat.{u + 1})
        (B.smallPushforward f AddCommGrpCat.{u + 1})
        (B.smallPushforward (bigEtaleFibreFst B f U) AddCommGrpCat.{u + 1})
        RfSmall (Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditive
          (B.smallPushforward (bigEtaleFibreFst B f U) AddCommGrpCat.{u + 1}))
        αSmall (Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditiveUnit
          (B.smallPushforward (bigEtaleFibreFst B f U) AddCommGrpCat.{u + 1}))
        ((mateEquiv (B.smallPullbackAdjunction ((Over.pullback f).obj U).hom AddCommGrpCat.{u + 1})
          (B.smallPullbackAdjunction U.hom AddCommGrpCat.{u + 1})).symm
          (SmallEtale.boundedBaseChangeMate B AddCommGrpCat.{u + 1} f U.hom
            ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U)
            (((Over.pullback f).obj U).hom ≫ f) rfl pullback.condition)).natTrans).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) :
    IsIso ((bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  refine isIso_of_forall_isIso_bigEtaleRestriction_mapDerivedCategory_map B S _ fun U ↦ ?_
  have hc := Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app
    (bigEtaleAbelianProjectionAdjunction B T) (bigEtaleAbelianProjectionAdjunction B S)
    (B.smallPullbackAdjunction ((Over.pullback f).obj U).hom AddCommGrpCat.{u + 1})
    (B.smallPullbackAdjunction U.hom AddCommGrpCat.{u + 1})
    (bigEtaleRestrictionPullbackSquare B AddCommGrpCat.{u + 1} T ((Over.pullback f).obj U)
      (bigEtaleAbelianProjectionAdjunction B T))
    (bigEtaleRestrictionPullbackSquare B AddCommGrpCat.{u + 1} S U
      (bigEtaleAbelianProjectionAdjunction B S))
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)
    (bigEtaleRestrictionDirectImageSquare B AddCommGrpCat.{u + 1} f U)
    (bigSmallEtaleDirectImageSquare B AddCommGrpCat.{u + 1} f)
    (SmallEtale.boundedBaseChangeMate B AddCommGrpCat.{u + 1} f U.hom ((Over.pullback f).obj U).hom
      (bigEtaleFibreFst B f U) (((Over.pullback f).obj U).hom ≫ f) rfl pullback.condition)
    (bigSmallEtale_cube_eq B AddCommGrpCat.{u + 1} f U _ _)
  have hKinj : ∀ J : CochainComplex
      (Sheaf (BigEtaleOver.topology B T.obj T.property) AddCommGrpCat.{u + 1}) ℤ,
      J.IsKInjective → CochainComplex.IsKInjective
        (((bigEtaleRestriction B AddCommGrpCat.{u + 1} T
          ((Over.pullback f).obj U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    fun J _ ↦ isKInjective_smallEtaleRestrictionAlong B _ T _ J
  exact (Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_of_cube
    _ _ _ _ RfSmall RfBig αSmall αBig
    (bigSmallEtaleBaseChange B AddCommGrpCat.{u + 1} f
      (bigEtaleAbelianProjectionAdjunction B T) (bigEtaleAbelianProjectionAdjunction B S))
    _ _ _ _ _ _ _ _ _ (𝟭 _)
    (bigEtaleRestriction B AddCommGrpCat.{u + 1} T ((Over.pullback f).obj U))
    (𝟭 _) (bigEtaleRestriction B AddCommGrpCat.{u + 1} S U) _ _ _ _ hc hKinj I hI hI).1 (h U)

/-- **The derived base change map of the bounded small étale sites on bounded below complexes
with torsion cohomology sheaves**, granted that cohomology commutes with base change for `f`. For
a commutative square `g' ≫ f = f' ≫ g` of a big étale site whose image in the category of schemes
is cartesian, the derived base change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of the bounded small étale
sites is invertible at every bounded below `K` with torsion cohomology sheaves. -/
public theorem isIso_derivedBaseChangeMap_bounded_app_of_cohomologyCommutesWithBaseChange
    {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (h : g' ≫ f = f' ≫ g)
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    (RF : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}))
    (RF' : DerivedCategory (Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1})
      ⥤ DerivedCategory (Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1}))
    (αF : (B.smallPushforward f AddCommGrpCat.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (αF' : (B.smallPushforward f' AddCommGrpCat.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (h095T : Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} (B.inclusion.map f))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}))
    (n : ℤ) (hK : K.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1}
      (SmallEtale.topology B X.obj X.property) K) :
    IsIso ((Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
      (B.smallInverseImage g' AddCommGrpCat.{u + 1}) (B.smallInverseImage g AddCommGrpCat.{u + 1})
      (B.smallPushforward f AddCommGrpCat.{u + 1}) (B.smallPushforward f' AddCommGrpCat.{u + 1})
      RF RF' αF αF'
      ((mateEquiv (B.smallPullbackAdjunction g' AddCommGrpCat.{u + 1})
        (B.smallPullbackAdjunction g AddCommGrpCat.{u + 1})).symm
        (SmallEtale.boundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f' (g' ≫ f) rfl
          h.symm)).natTrans).app K) := by
  refine isIso_app_of_forall_isKInjective_iso _ K fun I hI e ↦ ?_
  refine isIso_derivedBaseChangeMap_bounded_app_of_isIso_etaleAbelianDerivedBaseChange B f g g' f'
    h _ _ _ _ I hI ?_
  let Ψ := (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor
  let eE : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≅ Ψ.mapDerivedCategory.obj K :=
    (Ψ.mapDerivedCategoryFactorsh.app _).symm ≪≫ Ψ.mapDerivedCategory.mapIso e
  have hE : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))).IsGE n := by
    have := Functor.isGE_obj_mapDerivedCategory Ψ K n hK
    rw [DerivedCategory.isGE_iff] at this ⊢
    exact fun i hi ↦ (this i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eE)
  have hTE : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.obj.smallEtaleTopology
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := fun i ↦
    (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      (((Ψ.mapDerivedCategoryHomologyIso i).app K).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso eE.symm)
      (SmallEtale.torsionSheafProperty_sheafEquiv_functor_obj B X _ (hT i))
  exact isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange h095T sq _ n hE hTE

/-- **Stacks 0DDJ (2), granted the proper base change theorem (Stacks 095T) for `f`.** Suppose
that cohomology commutes with base change for `f`, in the sense of
`Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange` — for `f` proper this is Stacks 095T.
Then `π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for every `K` in `D^+(T_étale)` whose cohomology
sheaves are torsion: the canonical base change map
`AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` is invertible at `K`. -/
public theorem isIso_bigSmallEtaleDerivedBaseChange_app_of_cohomologyCommutesWithBaseChange
    (h095T : Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} (B.inclusion.map f))
    (K : DerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1}))
    (n : ℤ) (hK : K.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1}
      (SmallEtale.topology B T.obj T.property) K) :
    IsIso ((bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app K) := by
  refine isIso_app_of_forall_isKInjective_iso _ K fun I hI e ↦ ?_
  refine isIso_bigSmallEtaleDerivedBaseChange_app_of_forall_isIso B f RfSmall RfBig αSmall αBig
    I hI fun U ↦ ?_
  refine isIso_derivedBaseChangeMap_bounded_app_of_cohomologyCommutesWithBaseChange B f U.hom
    ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U) pullback.condition.symm
    ((bigEtaleFibreSquare_isPullback B f U).map B.inclusion) _ _ _ _ h095T _ n ?_ ?_
  · exact DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  · exact fun i ↦ (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e.symm) (hT i)

/-- **Stacks 0DDJ (3), granted Stacks 0F0C for `f`.** Let `n ≥ 1`, and suppose that for every
cartesian square of schemes with right side `f` the base change map (0A2A) is invertible at the
underlying abelian complex of every object of `D(T_étale, ℤ/nℤ)` — for `f` proper this is
Stacks 0F0C, which in `Stacks.EtaleCohomology` is
`isIso_etaleAbelianDerivedBaseChange_zmod_of_cohomologyCommutesWithBaseChange`.
Then `π_S⁻¹ Rf_{small,*} K = Rf_{big,*} π_T⁻¹ K` for every `K` in `D(T_étale, ℤ/nℤ)`: the
canonical base change map `AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` is invertible at the
underlying abelian complex of `K`.

`D(T_étale, ℤ/nℤ)` is the unbounded derived category of sheaves of modules over the constant
sheaf of rings `ℤ/nℤ`; as in Stacks 0F0C, the base change maps are maps of abelian complexes,
applied to the underlying abelian complex. -/
public theorem isIso_bigSmallEtaleDerivedBaseChange_app_toSheaf_of_zmod {n : ℕ}
    (h0F0C : ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ S.obj) (g' : X' ⟶ T.obj) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' (B.inclusion.map f) g)
      (E : DerivedCategory (SheafOfModules.{u + 1}
        (zmodRingSheaf.{u + 1} T.obj.smallEtaleTopology n))),
      IsIso ((Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange.{u, 0} (B.inclusion.map f) g g'
        f' sq.w).app
        ((SheafOfModules.toSheaf _).mapDerivedCategory.obj E)))
    (E : DerivedCategory (SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1}
      (SmallEtale.topology B T.obj T.property) n))) :
    IsIso ((bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app
      ((SheafOfModules.toSheaf _).mapDerivedCategory.obj E)) := by
  refine isIso_app_of_forall_isKInjective_iso _ _ fun I hI e ↦ ?_
  refine isIso_bigSmallEtaleDerivedBaseChange_app_of_forall_isIso B f RfSmall RfBig αSmall αBig
    I hI fun U ↦ ?_
  refine isIso_derivedBaseChangeMap_bounded_app_of_isIso_etaleAbelianDerivedBaseChange B f U.hom
    ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U) pullback.condition.symm _ _ _ _ I hI ?_
  let Ψ := (SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}).functor
  have := Localization.essSurj (DerivedCategory.Q (C := SheafOfModules.{u + 1}
    (zmodRingSheaf.{u + 1} (SmallEtale.topology B T.obj T.property) n)))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  let M := DerivedCategory.Q.objPreimage E
  let eM : DerivedCategory.Q.obj M ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let eΦ := zmodSheafEquivFunctorCompToSheaf B T n
  let EM := DerivedCategory.Q.obj (((zmodSheafEquivFunctor B T n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj M)
  let iso : (SheafOfModules.toSheaf _).mapDerivedCategory.obj EM ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    ((SheafOfModules.toSheaf _).mapDerivedCategoryFactors.app _) ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex eΦ (ComplexShape.up ℤ)).app M) ≪≫
      (Ψ.mapDerivedCategoryFactors.app (((SheafOfModules.toSheaf _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)).symm ≪≫
      Ψ.mapDerivedCategory.mapIso
        (((SheafOfModules.toSheaf _).mapDerivedCategoryFactors.app M).symm ≪≫
        (SheafOfModules.toSheaf _).mapDerivedCategory.mapIso eM ≪≫ e.symm) ≪≫
      Ψ.mapDerivedCategoryFactorsh.app _
  exact (NatTrans.isIso_app_iff_of_iso _ iso).1
    (h0F0C _ _ _ ((bigEtaleFibreSquare_isPullback B f U).map B.inclusion) EM)

end Reduction

end AlgebraicGeometry

end

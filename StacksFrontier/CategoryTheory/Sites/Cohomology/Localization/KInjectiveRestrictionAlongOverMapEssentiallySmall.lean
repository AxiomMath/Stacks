module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMap
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall

/-!
# Restriction of modules along `Over.map` preserves K-injectives, over a site with large objects

Let `(C, J)` be a site whose objects live in an arbitrary universe while its morphisms live in
`u`, let `f : V ⟶ U` be an arrow of `C`, and let `R` be a sheaf of rings on the slice site
`C/U`. Restriction of sheaves of `R`-modules along `Over.map f : C/V ⥤ C/U` carries K-injective
complexes to K-injective complexes, as soon as `C/U` is essentially small.

This is `Stacks.Cohomology.Localization.isKInjective_overMap` (Stacks 08FI for `Over.map`) with
the object universe of the site freed and with an arbitrary sheaf of rings on the slice. The
proof is the same: `Over.map f` is the forgetful functor of the slice of `C/U` at `Over.mk f`
read through the iterated slice equivalence, restriction to that slice preserves K-injectivity
(`Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`), and transport along an
equivalence does too.

The topologies of the two slice sites are taken as arbitrary topologies equal to the
localizations of `J`, so that the result applies to sites whose slice topologies are defined
independently and only proved equal to the localized topology.

## Main results

* `Stacks.Cohomology.Localization.isKInjective_restriction_overMap_of_essentiallySmall`.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ), the adjoint criterion
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Localization

universe u c

variable {C : Type c} [Category.{u} C] (J : GrothendieckTopology C) {V U : C} (f : V ⟶ U)

/-- A right adjoint whose left adjoint is an equivalence carries K-injective complexes to
K-injective complexes: the left adjoint is exact. -/
theorem isKInjective_mapHomologicalComplex_of_isEquivalence {A B : Type*} [Category A]
    [Abelian A] [Category B] [Abelian B] (G : B ⥤ A) (L : A ⥤ B) [L.IsEquivalence] (adj : L ⊣ G)
    [G.Additive] (I : CochainComplex B ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have : L.Additive := adj.left_adjoint_additive
  have : PreservesFiniteLimits L :=
    ((L.asEquivalence.symm.toAdjunction).rightAdjoint_preservesLimits.{0, 0}).preservesFiniteLimits
  have : PreservesFiniteColimits L :=
    (adj.leftAdjoint_preservesColimits.{0, 0}).preservesFiniteColimits
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact G L adj I

/-- The comparison `(Over.map f).obj (iteratedSliceForward α) ⟶ α` in `C/U`, for `α` an object of
the slice of `C/U` at `Over.mk f`; its underlying morphism of `C` is the identity. -/
def iteratedSliceForwardMapToForget :
    (Over.mk f).iteratedSliceForward ⋙ Over.map f ⟶ Over.forget (Over.mk f) where
  app α := Over.homMk (𝟙 α.left.left) ((Category.id_comp _).trans (Over.w α.hom).symm)
  naturality _ _ _ := Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The structure map comparing the restriction of a sheaf of rings `R` on `C/U` to the iterated
slice with its restriction to `C/V` read on the iterated slice. -/
def iteratedSliceRingMap {JU : GrothendieckTopology (Over U)} {JV : GrothendieckTopology (Over V)}
    [(Over.map f).IsContinuous JV JU]
    [(Over.mk f).iteratedSliceForward.IsContinuous (JU.over (Over.mk f)) JV]
    (R : Sheaf JU RingCat.{u}) :
    R.over (Over.mk f) ⟶ ((Over.mk f).iteratedSliceForward.sheafPushforwardContinuous RingCat.{u}
      (JU.over (Over.mk f)) JV).obj (((Over.map f).sheafPushforwardContinuous RingCat.{u}
        JV JU).obj R) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op (iteratedSliceForwardMapToForget f)) R.obj)

/-- **Restriction along `Over.map` preserves K-injective complexes of modules**, over a site
whose slice at the target is essentially small, for an arbitrary sheaf of rings on that slice and
for slice topologies given up to equality with the localized topology. -/
theorem isKInjective_restriction_overMap_of_essentiallySmall
    (JU : GrothendieckTopology (Over U)) (JV : GrothendieckTopology (Over V))
    (hU : JU = J.over U) (hV : JV = J.over V) (hf : (Over.map f).IsContinuous JV JU)
    (R : Sheaf JU RingCat.{u}) (hs : EssentiallySmall.{u} (Over U))
    (hU₁ : HasWeakSheafify JU AddCommGrpCat.{u})
    (hU₂ : JU.WEqualsLocallyBijective AddCommGrpCat.{u})
    (hV₁ : HasWeakSheafify JV AddCommGrpCat.{u})
    (hV₂ : JV.WEqualsLocallyBijective AddCommGrpCat.{u})
    (hf₁ : HasWeakSheafify (JU.over (Over.mk f)) AddCommGrpCat.{u})
    (hf₂ : (JU.over (Over.mk f)).WEqualsLocallyBijective AddCommGrpCat.{u})
    (I : CochainComplex (SheafOfModules.{u} R) ℤ) (hI : I.IsKInjective) :
    letI := hf; letI := hU₁; letI := hU₂; letI := hV₁; letI := hV₂
    CochainComplex.IsKInjective
      (((SheafOfModules.pushforward.{u}
        (𝟙 (((Over.map f).sheafPushforwardContinuous RingCat.{u} JV JU).obj
          R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  subst hU hV
  have := hI; have := hf; have := hs; have := hU₁; have := hU₂; have := hV₁
  have := hV₂; have := hf₁; have := hf₂
  have h₁ : CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{u} R (Over.mk f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    isKInjective_over_of_essentiallySmall (J.over U) R (Over.mk f) I
  let e := Over.iteratedSliceEquiv (Over.mk f)
  have : (Over.mk f).iteratedSliceForward.IsContinuous ((J.over U).over (Over.mk f)) (J.over V) :=
    inferInstanceAs ((Over.mk f).iteratedSliceForward.IsContinuous
      ((J.over U).over (Over.mk f)) (J.over (Over.mk f).left))
  have : (Over.mk f).iteratedSliceBackward.IsContinuous (J.over V) ((J.over U).over (Over.mk f)) :=
    inferInstanceAs ((Over.mk f).iteratedSliceBackward.IsContinuous
      (J.over (Over.mk f).left) ((J.over U).over (Over.mk f)))
  have : e.functor.IsContinuous ((J.over U).over (Over.mk f)) (J.over V) := by assumption
  have : e.inverse.IsContinuous (J.over V) ((J.over U).over (Over.mk f)) := by assumption
  let E : SheafOfModules.{u} (((Over.map f).sheafPushforwardContinuous RingCat.{u}
        (J.over V) (J.over U)).obj R) ≌ SheafOfModules.{u} (R.over (Over.mk f)) :=
    SheafOfModules.pushforwardPushforwardEquivalence.{u} e (iteratedSliceRingMap f R) (𝟙 _)
      (by
        ext X : 2
        dsimp [iteratedSliceRingMap]
        refine Eq.trans ?_ (Category.id_comp _).symm
        exact congrArg R.obj.map (Quiver.Hom.unop_inj (by
          ext
          simp [e, iteratedSliceForwardMapToForget]
          rfl)))
      (by
        ext X : 2
        dsimp [iteratedSliceRingMap]
        refine (R.obj.map_comp _ _).symm.trans (Eq.trans ?_ (R.obj.map_id _))
        exact congrArg R.obj.map (Quiver.Hom.unop_inj (by
          ext
          simp only [e, iteratedSliceForwardMapToForget]
          exact Category.comp_id _)))
  let P : SheafOfModules.{u} (R.over (Over.mk f)) ⥤ SheafOfModules.{u}
      (((Over.map f).sheafPushforwardContinuous RingCat.{u} (J.over V) (J.over U)).obj R) :=
    SheafOfModules.pushforward.{u} (F := (Over.mk f).iteratedSliceBackward) (𝟙 _)
  have : P.Additive := ⟨rfl⟩
  have hP : E.inverse = P := rfl
  have h₂ := isKInjective_mapHomologicalComplex_of_isEquivalence P E.functor
    (E.toAdjunction.ofNatIsoRight (eqToIso hP))
    (((SheafOfModules.overFunctor.{u} R (Over.mk f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)
  have h₂' : CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{u} R (Over.mk f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := h₂
  have h₃ : CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{u} R (Over.mk f) ⋙ P).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_of_iso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app I)
  let eF : SheafOfModules.overFunctor.{u} R (Over.mk f) ⋙ P ≅ SheafOfModules.pushforward.{u}
      (𝟙 (((Over.map f).sheafPushforwardContinuous RingCat.{u} (J.over V) (J.over U)).obj R)) :=
    have : ((Over.mk f).iteratedSliceBackward ⋙ Over.forget (Over.mk f)).IsContinuous
        (J.over V) (J.over U) :=
      Functor.isContinuous_comp _ _ (J.over V) ((J.over U).over (Over.mk f)) (J.over U)
    SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr (by
      ext X x
      rfl)
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex eF (ComplexShape.up ℤ)).app I)

end Stacks.Cohomology.Localization

end

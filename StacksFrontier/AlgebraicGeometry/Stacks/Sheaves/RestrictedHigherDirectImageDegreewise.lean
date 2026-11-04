module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictedHigherDirectImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites

/-!
# Stacks 075N in each degree

Let `f : 𝒰 ⥤ 𝒱` be a 1-morphism between categories fibred in groupoids over `(Sch/S)_fppf`
which are represented by algebraic spaces `F` and `G`, and let `f : F ⟶ G` also denote the
induced morphism of algebraic spaces. Stacks 075N (2) is the identity
`(Rf_*ℱ)|_{G_étale} = Rf_{small,*}(ℱ|_{F_étale})` in `D(𝒪_G)`, which the library has as
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso`. Here we take cohomology and get the
same identity for the classical higher direct images, naturally in the sheaf of modules `ℱ`:

```text
(Rⁱf_*ℱ)|_{G_étale} ≅ Rⁱf_{small,*}(ℱ|_{F_étale}).
```

## Main results

* `AlgebraicGeometry.Space.restrictedHigherDirectImageIso`: the identity above, for every `i`,
  with the total derived functors it passes through as data.
* `AlgebraicGeometry.Space.restrictedHigherDirectImageIsoOfGrothendieck`: the same, with those
  derived functors constructed.

## Implementation notes

`Rⁱ` is Mathlib's `CategoryTheory.Functor.rightDerived`, computed from injective resolutions. It is
compared with `Hⁱ` of the total right derived functor applied to a complex in degree zero by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`. The two restrictions
`π_{F,*}`, `π_{G,*}` are exact. `π_{G,*}` is moved past `Hⁱ` by
`AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExactCompHomologyFunctorIso`, and
`π_{F,*}` past the inclusion in degree zero by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

## References

* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w v' w' dU dV dF dG

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- The direct image of sheaves of modules along the morphism of small étale ringed topoi of a
morphism of algebraic spaces is additive. It is stated for algebraic spaces written as
`⟨F, hF⟩`, the form in which they occur below; instance search does not find the same statement
for a general `X : AlgebraicSpaces` at `⟨F, hF⟩`. -/
instance additive_pushforwardModules_smallEtaleToposHom (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {hG : IsAlgebraicSpace B S hS G}
    (f : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
    [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})] :
    (RingedToposHom.pushforwardModules (smallEtaleRingedToposHom B S hS f)).Additive :=
  RingedToposHom.pushforwardModules_additive _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (fChart : 𝒰 ⥤ 𝒱) (hfChart : p.IsFibredOneMorphism q fChart)
  [∀ P : 𝒰ᵒᵖ ⥤ Type u, fChart.op.HasPointwiseRightKanExtension P]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [IsGrothendieckAbelian.{u} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]

section DerivedData

variable [HasDerivedCategory.{dU} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [HasDerivedCategory.{dV} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [HasDerivedCategory.{dF} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  [HasDerivedCategory.{dG} (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules]
  (Rf : DerivedCategory (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules ⥤
    DerivedCategory (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules)
  (RfSpace : DerivedCategory (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules ⥤
    DerivedCategory (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules)
  (αf : RingedToposHom.pushforwardToDerivedCategory
      (FibredSite.ringedToposMorphism B S hS p q hp hq fChart hfChart .etale) ⟶
    DerivedCategory.Qh ⋙ Rf)
  (αfSpace : RingedToposHom.pushforwardToDerivedCategory
      (smallEtaleRingedToposHom B S hS
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fChart hfChart)) ⟶
    DerivedCategory.Qh ⋙ RfSpace)
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
    (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules (ComplexShape.up ℤ))]
  [RfSpace.IsRightDerivedFunctor αfSpace (HomotopyCategory.quasiIso
    (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules (ComplexShape.up ℤ))]

/-- **Stacks 075N (2) in degree `i`**: for a 1-morphism `f : 𝒰 ⥤ 𝒱` between categories fibred in
groupoids represented by algebraic spaces `F` and `G`, and every `i`,
`(Rⁱf_*ℱ)|_{G_étale} ≅ Rⁱf_{small,*}(ℱ|_{F_étale})` naturally in the sheaf of `𝒪_𝒰`-modules `ℱ`.
Here `Rⁱ` is the classical right derived functor, and the restrictions are the exact
`π_{G,*}`, `π_{F,*}` of Stacks 073M.

The total derived functors `Rf`, `RfSpace` and their units are parameters only because the
comparison passes through them; any choice gives the same isomorphism of functors. -/
noncomputable def restrictedHigherDirectImageIso (i : ℕ) :
    (RingedToposHom.pushforwardModules
        (FibredSite.ringedToposMorphism B S hS p q hp hq fChart hfChart .etale)).rightDerived i ⋙
        RingedToposHom.pushforwardModules (projectionRingedToposHom B S hS G q hq hG eG) ≅
      RingedToposHom.pushforwardModules (projectionRingedToposHom B S hS F p hp hF eF) ⋙
        (RingedToposHom.pushforwardModules (smallEtaleRingedToposHom B S hS
          (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fChart hfChart))).rightDerived i :=
  have := RingedToposHom.pushforwardModules_preservesFiniteLimits
    (projectionRingedToposHom B S hS F p hp hF eF)
  have : (RingedToposHom.pushforwardModules
      (projectionRingedToposHom B S hS F p hp hF eF)).Additive :=
    RingedToposHom.pushforwardModules_additive _
  have e1 := Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (RingedToposHom.pushforwardModules
      (FibredSite.ringedToposMorphism B S hS p q hp hq fChart hfChart .etale)) Rf αf
    Stacks.Cohomology.Localization.enoughKInjectives i
  have e2 := Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (RingedToposHom.pushforwardModules (smallEtaleRingedToposHom B S hS
      (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fChart hfChart))) RfSpace αfSpace
    Stacks.Cohomology.Localization.enoughKInjectives i
  have hπG := RingedToposHom.derivedPushforwardOfExactCompHomologyFunctorIso
    (projectionRingedToposHom B S hS G q hq hG eG) (i : ℤ)
  have hN := restrictedDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fChart hfChart
    Rf RfSpace αf αfSpace
  have hs : DerivedCategory.singleFunctor _ 0 ⋙ RingedToposHom.derivedPushforwardOfExact
        (projectionRingedToposHom B S hS F p hp hF eF) ≅
      RingedToposHom.pushforwardModules (projectionRingedToposHom B S hS F p hp hF eF) ⋙
        DerivedCategory.singleFunctor _ 0 :=
    eqToIso (by rw [RingedToposHom.derivedPushforwardOfExact_eq]) ≪≫
      Functor.mapDerivedCategorySingleFunctor _ 0
  Functor.isoWhiskerRight e1.symm _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙ Rf) hπG.symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight hN (DerivedCategory.homologyFunctor _ (i : ℤ))) ≪≫
    Functor.isoWhiskerRight hs (RfSpace ⋙ DerivedCategory.homologyFunctor _ (i : ℤ)) ≪≫
    Functor.isoWhiskerLeft _ e2

end DerivedData

/-- **Stacks 075N (2) in degree `i`**, with no derived functors as data:
`(Rⁱf_*ℱ)|_{G_étale} ≅ Rⁱf_{small,*}(ℱ|_{F_étale})` naturally in `ℱ`. This is
`AlgebraicGeometry.Space.restrictedHigherDirectImageIso` at the total right derived functors
`Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditive`, which exist because the two
source categories of modules are Grothendieck abelian. -/
noncomputable def restrictedHigherDirectImageIsoOfGrothendieck (i : ℕ) :
    (RingedToposHom.pushforwardModules
        (FibredSite.ringedToposMorphism B S hS p q hp hq fChart hfChart .etale)).rightDerived i ⋙
        RingedToposHom.pushforwardModules (projectionRingedToposHom B S hS G q hq hG eG) ≅
      RingedToposHom.pushforwardModules (projectionRingedToposHom B S hS F p hp hF eF) ⋙
        (RingedToposHom.pushforwardModules (smallEtaleRingedToposHom B S hS
          (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fChart hfChart))).rightDerived i :=
  letI := HasDerivedCategory.standard (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules
  letI := HasDerivedCategory.standard (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules
  letI := HasDerivedCategory.standard (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules
  letI := HasDerivedCategory.standard (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules
  restrictedHigherDirectImageIso B S hS F G p q hp hq hF hG eF eG fChart hfChart
    (Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditive _)
    (Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditive _)
    (Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditiveUnit _)
    (Stacks.Cohomology.UnboundedComplexes.totalRightDerivedOfAdditiveUnit _) i

end AlgebraicGeometry.Space

module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleComparisonAcyclicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedToposTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.WeakSerreAcrossTopologies
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.VanishingFromSectionsFormula
public import StacksFrontier.Homology.CompositeCollapse

/-!
# fppf and étale cohomology of modules cartesian along flat morphisms of affines (Stacks 075R)

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` and let
`ε : 𝒳_fppf ⟶ 𝒳_étale` be the comparison morphism, the identity functor of `𝒳` read for the two
topologies; its direct image `ε_*` is `AlgebraicGeometry.Stack.etaleComparisonPushforward`, which
changes neither the underlying presheaf of modules nor the scalars.  **Stacks 075R** says that
for a module `ℱ` in `LQCoh^fbc(𝒪_𝒳)`

1. `Rε_*ℱ = ε_*ℱ`, that is `R^iε_*ℱ = 0` for `i > 0`;
2. `H^p_fppf(x, ℱ) = H^p_ét(x, ℱ)` for every object `x`, and `H^p_fppf(𝒳, ℱ) = H^p_ét(𝒳, ℱ)`.

This file proves both, for every sheaf of modules on the fppf site of an algebraic stack which is
*cartesian along flat morphisms of affines*
(`AlgebraicGeometry.FibredSite.IsCartesianAlongFlatAffines`: for `z ⟶ x` over a flat morphism
of affine schemes `Z ⟶ X`, the comparison `Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} ℱ(x) ⟶ ℱ(z)` is bijective).

## The source's argument, and where each step is

* `ε` is a morphism of sites given by the identity functor, so by **Stacks 072W** the sheaf
  `R^pε_*ℱ` is the étale sheafification of `x ↦ H^p_fppf(x, ℱ)`; it vanishes as soon as that
  presheaf vanishes on the objects lying over affine schemes, since those cover `𝒳_étale`
  (**Stacks 0H0B**): `isZero_rightDerived_etaleComparisonPushforward_of_isZero_affine`.  This is
  the reduction of
  `AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_of_lqcFbc`,
  stated for one module and with the covering class proved rather than carried.
* The vanishing over an affine object is the source's "075F + 0756 + 01XB".  Here it is
  `AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine` (Čech cohomology on
  the cofinal finite fppf coverings by affine objects, **Stacks 03F9** and **Stacks 03FJ**),
  which needs exactly the cartesianness above:
  `isZero_rightDerived_etaleComparisonPushforward_of_isCartesianAlongFlatAffines`.
* Part (2) "follows formally from (1) and the Leray spectral sequence".  Here the spectral
  sequence is not needed: `ε_*` is left exact and preserves injectives (its left adjoint, fppf
  sheafification, is exact), so it carries an injective resolution of an `ε_*`-acyclic `ℱ` to an
  injective resolution of `ε_*ℱ` (`Stacks.RightDerivedComp.objIso`), and the sections functors
  over `x` and the global sections functor `Hom(𝒪, -)` of the fppf site factor through `ε_*`.

## The input that is not proved here

Cartesianness along flat morphisms of affines for a module of `LQCoh^fbc(𝒪_𝒳)`, with the flat base
change property of **Stacks 0762** read on sheaves
(`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`), is the affine flat base change of the
proof of **Stacks 0779**, which is not proved here.  It is not taken as a
hypothesis of any statement presented as 075R: the statements below are about the explicit
property `IsCartesianAlongFlatAffines`, and
`isCartesianAlongFlatAffines_of_isIso_restrictionBaseChange` converts the affine flat base change,
in the form `IsIso (Stacks.PresheafOfModules.restrictionBaseChange F φ.op)` in which it is being
proved, into that property.

## Main results

* `AlgebraicGeometry.Stack.preservesInjectiveObjects_etaleComparisonPushforward`,
  `AlgebraicGeometry.Stack.preservesFiniteLimits_etaleComparisonPushforward`: `ε_*` is left exact
  and preserves injective objects.
* `AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_of_isZero_affine`: the
  reduction of 075R (1) to objects lying over affine schemes.
* `AlgebraicGeometry.Stack.rightDerivedEvaluationIsoOfIsZero`,
  `AlgebraicGeometry.Stack.rightDerivedCoyonedaUnitIsoOfIsZero`: 075R (2) for an `ε_*`-acyclic
  module, over an object and globally.
* `AlgebraicGeometry.Stack.isCartesianAlongFlatAffines_of_isIso_restrictionBaseChange`: the
  affine flat base change gives cartesianness along flat morphisms of affines.
* `isZero_rightDerived_etaleComparisonPushforward_of_isCartesianAlongFlatAffines`,
  `shortExact_map_etaleComparisonPushforward_of_isCartesianAlongFlatAffines`,
  `rightDerivedEvaluationIsoOfIsCartesianAlongFlatAffines`,
  `rightDerivedCoyonedaUnitIsoOfIsCartesianAlongFlatAffines` (all in
  `AlgebraicGeometry.Stack`): 075R (1) and (2) on an algebraic stack, at module universe `u`.

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`ε^* ⊣ ε_*`** for the comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale`: fppf sheafification is
left adjoint to reading an fppf module as an étale one
(`Stacks.Cohomology.CompareTopologies.adjunction` at the two associated topologies). -/
def etaleComparisonAdjunction :
    Stacks.Cohomology.CompareTopologies.pullback.{v, w, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp) ⊣
      etaleComparisonPushforward B S hS p hp :=
  Stacks.Cohomology.CompareTopologies.adjunction _ _

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`ε_*` preserves injective objects**: its left adjoint, fppf sheafification, is left exact
and therefore preserves monomorphisms. -/
theorem preservesInjectiveObjects_etaleComparisonPushforward :
    (etaleComparisonPushforward B S hS p hp).PreservesInjectiveObjects :=
  have : PreservesFiniteLimits (Stacks.Cohomology.CompareTopologies.pullback.{v, w, u, u}
      (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp)) :=
    inferInstance
  have : (Stacks.Cohomology.CompareTopologies.pullback.{v, w, u, u}
      (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)
      (fppfSiteRingSheaf B S hS p hp)).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  @Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms _ _ _ _ _ _
    (etaleComparisonAdjunction B S hS p hp) this

/-- `ε_*` is left exact, being a right adjoint. -/
theorem preservesFiniteLimits_etaleComparisonPushforward :
    PreservesFiniteLimits (etaleComparisonPushforward B S hS p hp) :=
  have : PreservesLimitsOfSize.{0, 0} (etaleComparisonPushforward B S hS p hp) :=
    (etaleComparisonAdjunction B S hS p hp).rightAdjoint_preservesLimits
  inferInstance

variable [EnoughInjectives (fppfSiteModules B S hS p hp)]

/-- **The reduction of Stacks 075R (1) to objects lying over affine schemes.**  If the higher
fppf cohomology `H^i(x, ℱ)` of a sheaf of modules vanishes over every object `x` lying over an
affine scheme, then `R^iε_*ℱ = 0` for `i > 0`.

By **Stacks 072W** `R^iε_*ℱ` is the étale sheafification of the presheaf `x ↦ H^i(x, ℱ)`, and
that presheaf dies on the covering sieve of each object generated by the objects lying over
affine schemes, which is an étale covering by **Stacks 0H0B**
(`AlgebraicGeometry.Stack.isDenseSubsite_affineInclusion_etale`). -/
theorem isZero_rightDerived_etaleComparisonPushforward_of_isZero_affine
    (ℱ : fppfSiteModules B S hS p hp)
    (hℱ : ∀ x : 𝒳, IsAffineObject B S hS p x → ∀ i : ℕ, 0 < i →
      IsZero (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp) (op x)).rightDerived
        i).obj ℱ))
    (i : ℕ) (hi : 0 < i) :
    IsZero (((etaleComparisonPushforward B S hS p hp).rightDerived i).obj ℱ) := by
  classical
  set R := fppfSiteRingSheaf B S hS p hp with hR
  set Re := etaleSiteRingSheaf B S hS p hp with hRe
  set φ := etaleComparisonRingMap B S hS p hp with hφ
  set P := cohPresheafModule (Functor.id 𝒳) R Re φ i ℱ with hP
  obtain ⟨e⟩ := higherDirectImage_iso_sheafify_cohomologyPresheaf (Functor.id 𝒳) R Re φ i ℱ
  refine IsZero.of_iso ?_ e
  have hPzero : ∀ V : 𝒳, IsAffineObject B S hS p V → IsZero (P.obj (op V)) := by
    intro V hV
    obtain ⟨eV⟩ := cohPresheafModule_evaluation_iso (Functor.id 𝒳) R Re φ i ℱ V
    refine IsZero.of_iso ?_ eV
    exact Functor.map_isZero _ (hℱ V hV i hi)
  refine Stacks.Cohomology.ModuleLocalVanishing.isZero_sheafification_of_locallyZero _ P ?_
  intro U x
  have hcov := (isDenseSubsite_affineInclusion_etale B S hS p hp).isCoverDense'.is_cover U
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  rintro V g ⟨⟨Y, a, b, hfac⟩⟩
  have hsub : Subsingleton (ToType (P.obj (op Y.obj))) :=
    ModuleCat.isZero_iff_subsingleton.1 (hPzero Y.obj Y.property)
  show P.presheaf.map g.op x = P.presheaf.map g.op 0
  rw [← hfac]
  have hfac' : (a ≫ b).op = b.op ≫ a.op := rfl
  rw [hfac', P.presheaf.map_comp]
  have hmid : P.presheaf.map b.op x = P.presheaf.map b.op 0 := hsub.elim _ _
  simp only [ConcreteCategory.comp_apply, hmid]

section Comparison

variable [EnoughInjectives (SheafOfModules.{u} (etaleSiteRingSheaf B S hS p hp))]

/-- `ε_*` carries a short exact sequence to a short exact sequence as soon as `R¹ε_*` vanishes
on its first term. -/
theorem shortExact_map_etaleComparisonPushforward_of_isZero
    {T : ShortComplex (fppfSiteModules B S hS p hp)} (hT : T.ShortExact)
    (h₁ : IsZero (((etaleComparisonPushforward B S hS p hp).rightDerived 1).obj T.X₁)) :
    (T.map (etaleComparisonPushforward B S hS p hp)).ShortExact :=
  let := preservesFiniteLimits_etaleComparisonPushforward B S hS p hp
  Stacks.Cohomology.RightDerivedDelta.shortExact_map_of_isZero_rightDerived_one _ hT h₁

/-- **Stacks 075R (2) over an object, for an `ε_*`-acyclic module**: if `R^iε_*ℱ = 0` for
`i > 0`, then `H^n_fppf(x, ℱ) ≅ H^n_ét(x, ε_*ℱ)` for every object `x` and every `n`.

Sections over `x` of the fppf site are `ε_*` followed by sections over `x` of the étale site, and
`ε_*` carries an injective resolution of `ℱ` to an injective resolution of `ε_*ℱ`
(`Stacks.RightDerivedComp.objIso`). -/
def rightDerivedEvaluationIsoOfIsZero (ℱ : fppfSiteModules B S hS p hp)
    (hℱ : ∀ i : ℕ, 0 < i →
      IsZero (((etaleComparisonPushforward B S hS p hp).rightDerived i).obj ℱ))
    (x : 𝒳) (n : ℕ) :
    ((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp) (op x)).rightDerived n).obj ℱ ≅
      ((SheafOfModules.evaluation (etaleSiteRingSheaf B S hS p hp) (op x)).rightDerived n).obj
        ((etaleComparisonPushforward B S hS p hp).obj ℱ) :=
  letI := preservesFiniteLimits_etaleComparisonPushforward B S hS p hp
  letI := preservesInjectiveObjects_etaleComparisonPushforward B S hS p hp
  letI := Stacks.Cohomology.AcyclicCover.evaluation_additive (etaleSiteRingSheaf B S hS p hp) x
  Stacks.RightDerivedComp.objIso (etaleComparisonPushforward B S hS p hp)
    (injectiveResolution ℱ) hℱ (SheafOfModules.evaluation (etaleSiteRingSheaf B S hS p hp) (op x)) n

/-- `ε_*` carries the structure sheaf of the fppf site to that of the étale site. -/
def etaleComparisonUnitIso :
    (etaleComparisonPushforward B S hS p hp).obj
        (SheafOfModules.unit (fppfSiteRingSheaf B S hS p hp)) ≅
      SheafOfModules.unit (etaleSiteRingSheaf B S hS p hp) :=
  Iso.refl _

/-- Global sections `Hom(𝒪, -)` of the fppf site are `ε_*` followed by global sections of the
étale site, `ε_*` being fully faithful. -/
def etaleComparisonPushforwardCompCoyonedaIso :
    etaleComparisonPushforward B S hS p hp ⋙
        preadditiveCoyoneda.obj (op (SheafOfModules.unit (etaleSiteRingSheaf B S hS p hp))) ≅
      preadditiveCoyoneda.obj (op (SheafOfModules.unit (fppfSiteRingSheaf B S hS p hp))) :=
  Functor.isoWhiskerLeft _ (preadditiveCoyoneda.mapIso (etaleComparisonUnitIso B S hS p hp).op) ≪≫
    NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso
      { toEquiv := ((Stacks.SheafOfModules.comparisonPushforwardFullyFaithful
            (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)
            (fppfSiteRingSheaf B S hS p hp)).homEquiv (X := SheafOfModules.unit _) (Y := M)).symm
        map_add' := fun _ _ => rfl })
      (fun _ => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => SheafOfModules.hom_ext rfl))

/-- **Stacks 075R (2) globally, for an `ε_*`-acyclic module**: if `R^iε_*ℱ = 0` for `i > 0`,
then `H^n_fppf(𝒳, ℱ) ≅ H^n_ét(𝒳, ε_*ℱ)` for every `n`, where `H^n(𝒳, -)` is the `n`-th right
derived functor of the global sections `Hom(𝒪_𝒳, -)`. -/
def rightDerivedCoyonedaUnitIsoOfIsZero (ℱ : fppfSiteModules B S hS p hp)
    (hℱ : ∀ i : ℕ, 0 < i →
      IsZero (((etaleComparisonPushforward B S hS p hp).rightDerived i).obj ℱ))
    (n : ℕ) :
    ((preadditiveCoyoneda.obj
        (op (SheafOfModules.unit (fppfSiteRingSheaf B S hS p hp)))).rightDerived n).obj ℱ ≅
      ((preadditiveCoyoneda.obj
          (op (SheafOfModules.unit (etaleSiteRingSheaf B S hS p hp)))).rightDerived n).obj
        ((etaleComparisonPushforward B S hS p hp).obj ℱ) :=
  letI := preservesFiniteLimits_etaleComparisonPushforward B S hS p hp
  letI := preservesInjectiveObjects_etaleComparisonPushforward B S hS p hp
  ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (etaleComparisonPushforwardCompCoyonedaIso B S hS p hp) n).app ℱ).symm ≪≫
    Stacks.RightDerivedComp.objIso (etaleComparisonPushforward B S hS p hp)
      (injectiveResolution ℱ) hℱ _ n

end Comparison

end

section Bridge

variable {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **Affine flat base change gives cartesianness along flat morphisms of affines**: a sheaf of
modules on the fppf site whose restriction maps along arrows over flat morphisms of affine
schemes induce isomorphisms `Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} ℱ(x) ≅ ℱ(z)` satisfies
`AlgebraicGeometry.FibredSite.IsCartesianAlongFlatAffines`.  Pointwise this is
`AlgebraicGeometry.FibredSite.isIso_tensorToSectionsApp_of_isIso_restrictionBaseChange`; on an
algebraic stack the hypothesis is `AlgebraicGeometry.Stack.IsCartesianAlongFlatAffine`. -/
theorem isCartesianAlongFlatAffines_of_isIso_restrictionBaseChange
    (F : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (h : ∀ {z x : 𝒳} (φ : z ⟶ x), Flat (B.inclusion.map (p.map φ).left) →
      IsAffine (FibredSite.schemeOf B S hS p z) → IsAffine (FibredSite.schemeOf B S hS p x) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        F.val φ.op)) :
    FibredSite.IsCartesianAlongFlatAffines B S hS p hp F :=
  fun x hx Z hZ hflat =>
    FibredSite.isIso_tensorToSectionsApp_of_isIso_restrictionBaseChange B S hS p hp .fppf x F Z
      (h Z.hom hflat hZ hx)

end Bridge

section AlgebraicStack

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] enoughInjectives_fppfModules

-- Lean v4.35.0: the `HasProducts` searches behind `hasExt_of_enoughInjectives` exceed the default.
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 075R (1)**, `Rε_*ℱ = ε_*ℱ`, on an algebraic stack at module universe `u`, for a
sheaf of modules on the fppf site cartesian along flat morphisms of affines: `R^iε_*ℱ = 0` for
`i > 0`.

The higher cohomology over objects lying over affine schemes vanishes by
`AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine` (the source's
075F + 0756 + 01XB), and `isZero_rightDerived_etaleComparisonPushforward_of_isZero_affine`
concludes. -/
theorem isZero_rightDerived_etaleComparisonPushforward_of_isCartesianAlongFlatAffines
    (F : fppfModules B S hS 𝒳)
    (hF : FibredSite.IsCartesianAlongFlatAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((etaleComparisonPushforward B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids).rightDerived i).obj F) := by
  refine isZero_rightDerived_etaleComparisonPushforward_of_isZero_affine B S hS _ _ F
    (fun x hx j hj => ?_) i hi
  let : IsGrothendieckAbelian.{u}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  let : HasExt.{u + 1}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{u + 1} (fppfModules B S hS 𝒳) := hasExt_of_enoughInjectives _
  exact FibredSite.isZero_rightDerived_evaluation_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F hF hx j hj

/-- Modules on the étale site of an algebraic stack, at module universe `u`, have enough
injectives. -/
theorem enoughInjectives_etaleSiteModules :
    EnoughInjectives (SheafOfModules.{u}
      (etaleSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)) :=
  enoughInjectives_moduleRingSheaf B S hS 𝒳 .etale

attribute [local instance] enoughInjectives_etaleSiteModules

/-- **`ε_*` is exact on short exact sequences whose first term is cartesian along flat morphisms of
affines**, on an algebraic stack: the case `i = 1` of 075R (1) and the long exact sequence. -/
theorem shortExact_map_etaleComparisonPushforward_of_isCartesianAlongFlatAffines
    {T : ShortComplex (fppfModules B S hS 𝒳)} (hT : T.ShortExact)
    (h₁ : FibredSite.IsCartesianAlongFlatAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      T.X₁) :
    (T.map (etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)).ShortExact :=
  shortExact_map_etaleComparisonPushforward_of_isZero B S hS _ _ hT
    (isZero_rightDerived_etaleComparisonPushforward_of_isCartesianAlongFlatAffines B S hS 𝒳 T.X₁
      h₁ 1 one_pos)

/-- **Stacks 075R (2) over an object**, on an algebraic stack at module universe `u`:
`H^n_fppf(x, ℱ) ≅ H^n_ét(x, ε_*ℱ)` for a sheaf of modules on the fppf site cartesian along flat
morphisms of affines, every object `x` and every `n`. -/
def rightDerivedEvaluationIsoOfIsCartesianAlongFlatAffines (F : fppfModules B S hS 𝒳)
    (hF : FibredSite.IsCartesianAlongFlatAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F)
    (x : 𝒳.val.val.obj) (n : ℕ) :
    ((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)
        (op x)).rightDerived n).obj F ≅
      ((SheafOfModules.evaluation (etaleSiteRingSheaf B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids) (op x)).rightDerived n).obj
        ((etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).obj F) :=
  rightDerivedEvaluationIsoOfIsZero B S hS _ _ F
    (isZero_rightDerived_etaleComparisonPushforward_of_isCartesianAlongFlatAffines B S hS 𝒳 F hF)
    x n

/-- **Stacks 075R (2) globally**, on an algebraic stack at module universe `u`:
`H^n_fppf(𝒳, ℱ) ≅ H^n_ét(𝒳, ε_*ℱ)`, as right derived functors of `Hom(𝒪_𝒳, -)`, for a sheaf of
modules on the fppf site cartesian along flat morphisms of affines. -/
def rightDerivedCoyonedaUnitIsoOfIsCartesianAlongFlatAffines (F : fppfModules B S hS 𝒳)
    (hF : FibredSite.IsCartesianAlongFlatAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F)
    (n : ℕ) :
    ((preadditiveCoyoneda.obj (op (SheafOfModules.unit (fppfSiteRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)))).rightDerived n).obj F ≅
      ((preadditiveCoyoneda.obj (op (SheafOfModules.unit (etaleSiteRingSheaf B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids)))).rightDerived n).obj
        ((etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids).obj F) :=
  rightDerivedCoyonedaUnitIsoOfIsZero B S hS _ _ F
    (isZero_rightDerived_etaleComparisonPushforward_of_isCartesianAlongFlatAffines B S hS 𝒳 F hF)
    n

end AlgebraicStack

end AlgebraicGeometry.Stack

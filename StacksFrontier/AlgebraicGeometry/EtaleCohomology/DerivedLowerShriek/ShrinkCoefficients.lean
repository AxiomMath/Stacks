module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CohomologicalBound
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact

/-!
# Changing the coefficient ring along `Shrink`

For a ring `Λ : Type` the sheaves of `Λ`-modules on the small étale site of `X : Scheme.{u}`,
`EtaleModules.{u, 0} Λ X`, and the sheaves of `Shrink.{u + 1} Λ`-modules,
`EtaleModules.{u, u + 1} (Shrink.{u + 1} Λ) X`, have the same coefficient universe `u + 1`;
restriction of scalars along `Shrink.ringEquiv` identifies them. This file records the
equivalence and the compatibilities used to read results proved for coefficient rings in
`Type (u + 1)` at a ring in `Type`: it preserves and reflects torsion and constructibility, and it
commutes with the derived lower shriek.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleShrinkEquivalence`.

## Main results

* `Stacks.EtaleCohomology.isTorsionEtaleModule_shrink_iff`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_shrink_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

variable (Λ : Type) [CommRing Λ]

/-- `AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCat` at the coefficient universe
`u + 1` of `EtaleModules.{u, 0} Λ`, where instance search cannot solve `max (u + 1) ?w = u + 1`. -/
private instance isRightAdjointPushforward_moduleCat_succ (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (f : T ⟶ S) :
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1, 0} B Λ f

/-- `AlgebraicGeometry.SmallEtale.hasWeakSheafifyOver_moduleCat` at the coefficient universe
`u + 1`. -/
private instance hasWeakSheafifyOver_moduleCat_succ (B : BigEtaleSite.{u}) (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ) :=
  SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1, 0} B Λ T V

/-- **Sheaves of `Λ`-modules are sheaves of `Shrink Λ`-modules**: restriction of scalars along
`Shrink.ringEquiv`, sheaf by sheaf, is an equivalence `EtaleModules.{u, 0} Λ X ≌
EtaleModules.{u, u + 1} (Shrink.{u + 1} Λ) X`; both have coefficients in `ModuleCat.{u + 1}`. -/
abbrev etaleModuleShrinkEquivalence (X : Scheme.{u}) :
    EtaleModules.{u, 0} Λ X ≌ EtaleModules.{u, u + 1} (Shrink.{u + 1} Λ) X :=
  Sheaf.coefficientEquivalence X.smallEtaleTopology
    (ModuleCat.restrictScalarsShrinkEquivalence.{0, u + 1, u + 1} Λ)

/-- The change of coefficients along `Shrink` is additive, being an equivalence. -/
instance etaleModuleShrinkEquivalence_functor_additive (X : Scheme.{u}) :
    (etaleModuleShrinkEquivalence Λ X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction of scalars along `Shrink.ringEquiv` does not change the underlying abelian groups
of sections, so a sheaf is torsion exactly when the associated sheaf of `Shrink Λ`-modules is. -/
theorem isTorsionEtaleModule_shrink_iff (X : Scheme.{u}) (F : EtaleModules.{u, 0} Λ X) :
    IsTorsionEtaleModule (Shrink.{u + 1} Λ) X ((etaleModuleShrinkEquivalence Λ X).functor.obj F) ↔
      IsTorsionEtaleModule Λ X F :=
  Iff.rfl

/-- **Constructibility is unchanged by restriction of scalars along `Shrink.ringEquiv`**: the
transport to the small étale site of Tag 021B commutes with the change of coefficients, and there
`AlgebraicGeometry.isConstructibleModuleSheaf_shrink` and
`AlgebraicGeometry.isConstructibleModuleSheaf_of_shrink` apply. -/
theorem isConstructibleEtaleModule_shrink_iff [IsNoetherianRing Λ] (X : Scheme.{u})
    (F : EtaleModules.{u, 0} Λ X) :
    IsConstructibleEtaleModule (Shrink.{u + 1} Λ)
        ((etaleModuleShrinkEquivalence Λ X).functor.obj F) ↔
      IsConstructibleEtaleModule Λ F :=
  ⟨fun h ↦ isConstructibleModuleSheaf_of_shrink _ Λ _ _ h,
    fun h ↦ isConstructibleModuleSheaf_shrink _ Λ _ _ h⟩

/-! ### The derived lower shriek -/

section LowerShriek

attribute [local instance] HasDerivedCategory.standard

/-- **Extension by zero commutes with the change of coefficients along `Shrink`**: both composites
are left adjoint to the same functor, restriction followed by the inverse change of coefficients,
which commute on the nose. -/
def etaleModuleExtensionByZeroShrinkIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleExtensionByZero.{u, 0} Λ j ⋙ (etaleModuleShrinkEquivalence Λ X).functor ≅
      (etaleModuleShrinkEquivalence Λ U).functor ⋙
        etaleModuleExtensionByZero.{u, u + 1} (Shrink.{u + 1} Λ) j :=
  ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).comp
      (etaleModuleShrinkEquivalence Λ X).toAdjunction).leftAdjointUniq
    (((etaleModuleShrinkEquivalence Λ U).toAdjunction.comp
      (etaleModuleExtensionByZeroAdj.{u, u + 1} (Shrink.{u + 1} Λ) j)).ofNatIsoRight (Iso.refl _))

/-- **The derived direct image commutes with the change of coefficients along `Shrink`**, at every
object: on a K-injective model both are the degreewise direct image, and the change of
coefficients is an exact equivalence, which preserves K-injective complexes and commutes with the
direct image on the nose. -/
theorem nonempty_iso_etaleModuleDerivedDirectImageUnbounded_shrink {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    Nonempty ((etaleModuleShrinkEquivalence Λ Y).functor.mapDerivedCategory.obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj M) ≅
      (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} (Shrink.{u + 1} Λ) f).obj
        ((etaleModuleShrinkEquivalence Λ X).functor.mapDerivedCategory.obj M)) := by
  let ΦX := (etaleModuleShrinkEquivalence Λ X).functor
  let ΦY := (etaleModuleShrinkEquivalence Λ Y).functor
  obtain ⟨I, g, hI, hg⟩ := Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
    (EtaleModules.{u, 0} Λ X) (DerivedCategory.Q.objPreimage M)
  let eM : M ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map g)
  have hΦI : CochainComplex.IsKInjective ((ΦX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence ΦX I
  have u₁ := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ f I hI
  have u₂ := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, u + 1} (Shrink.{u + 1} Λ) f
    ((ΦX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) hΦI
  exact ⟨ΦY.mapDerivedCategory.mapIso
      ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).mapIso eM) ≪≫
    ΦY.mapDerivedCategory.mapIso
      (@asIso _ _ _ _ ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f).app I) u₁).symm ≪≫
    ΦY.mapDerivedCategoryFactors.app
      (((etaleModuleDirectImage.{u, 0} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
    @asIso _ _ _ _ ((etaleModuleDerivedDirectImageUnboundedUnit.{u, u + 1} (Shrink.{u + 1} Λ) f).app
      ((ΦX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) u₂ ≪≫
    (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} (Shrink.{u + 1} Λ) f).mapIso
      ((ΦX.mapDerivedCategoryFactors.app I).symm ≪≫ ΦX.mapDerivedCategory.mapIso eM.symm)⟩

/-- **The derived lower shriek commutes with the change of coefficients along `Shrink`**, at every
object: `Rf_! = Rf̄_* ∘ j_!` with `j_!` exact, and both factors commute with it. -/
theorem nonempty_iso_derivedLowerShriekUnbounded_shrink {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    Nonempty ((etaleModuleShrinkEquivalence Λ Y).functor.mapDerivedCategory.obj
        ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj K) ≅
      (derivedLowerShriekUnbounded.{u, u + 1} f j (Shrink.{u + 1} Λ)).obj
        ((etaleModuleShrinkEquivalence Λ X).functor.mapDerivedCategory.obj K)) := by
  let ΦX := (etaleModuleShrinkEquivalence Λ X).functor
  let ΦXb := (etaleModuleShrinkEquivalence Λ j.obj.right.left).functor
  let ΦY := (etaleModuleShrinkEquivalence Λ Y).functor
  obtain ⟨e⟩ := nonempty_iso_etaleModuleDerivedDirectImageUnbounded_shrink Λ j.toBase
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapDerivedCategory.obj K)
  exact ⟨ΦY.mapDerivedCategory.mapIso
      ((derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, 0} Λ j).app K) ≪≫ e ≪≫
    (etaleModuleDerivedDirectImageUnbounded.{u, u + 1} (Shrink.{u + 1} Λ) j.toBase).mapIso
      ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) ΦXb).symm.app K ≪≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
          (etaleModuleExtensionByZeroShrinkIso Λ j.immersion)).app K ≪≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso ΦX
          (etaleModuleExtensionByZero.{u, u + 1} (Shrink.{u + 1} Λ) j.immersion)).app K) ≪≫
    ((derivedLowerShriekUnboundedIsoMapDerivedCategory.{u, u + 1} (Shrink.{u + 1} Λ) j).app
      (ΦX.mapDerivedCategory.obj K)).symm⟩

/-- **Constructibility of `Rf_!(F[0])` descends along `Shrink`**: if `Rf_!` of the associated sheaf
of `Shrink Λ`-modules placed in degree zero has constructible cohomology sheaves, then so does
`Rf_!(F[0])`. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_single_of_shrink
    [IsNoetherianRing Λ] {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, 0} Λ X)
    (h : IsConstructibleEtaleComplex (Shrink.{u + 1} Λ)
      ((derivedLowerShriekUnbounded.{u, u + 1} f j (Shrink.{u + 1} Λ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((etaleModuleShrinkEquivalence Λ X).functor.obj F)))) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, 0} f j Λ).obj
      ((DerivedCategory.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj F)) := by
  let ΦX := (etaleModuleShrinkEquivalence Λ X).functor
  let ΦY := (etaleModuleShrinkEquivalence Λ Y).functor
  obtain ⟨e⟩ := nonempty_iso_derivedLowerShriekUnbounded_shrink Λ j
    ((DerivedCategory.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj F)
  intro i
  refine (isConstructibleEtaleModule_shrink_iff Λ Y _).1 ?_
  refine (IsConstructibleEtaleModule (Shrink.{u + 1} Λ)).prop_of_iso ?_ (h i)
  exact (DerivedCategory.homologyFunctor _ i).mapIso
      (((derivedLowerShriekUnbounded.{u, u + 1} f j (Shrink.{u + 1} Λ)).mapIso
        ((ΦX.mapDerivedCategorySingleFunctor 0).app F).symm) ≪≫ e.symm) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso ΦY i).app _

end LowerShriek

end Stacks.EtaleCohomology

end

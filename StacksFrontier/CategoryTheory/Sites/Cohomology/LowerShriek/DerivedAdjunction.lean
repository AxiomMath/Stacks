module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived adjunction for lower shriek on a site

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `O_D` be a sheaf of rings
on `D` and let `O_C = g^{-1} O_D` be its restriction along `u`. The lower-shriek functor
`g_! : Mod(O_C) ⥤ Mod(O_D)` is Mathlib's `SheafOfModules.pullback` for the identity map of
`O_C`, the left adjoint of restriction of modules `g^* : Mod(O_D) ⥤ Mod(O_C)`. Restriction is
exact. When the unbounded left derived functor `Lg_!` exists and stays a left derived functor
after composition with derived restriction, it is left adjoint to derived restriction, compatibly
with the ordinary adjunction and the two canonical comparison transformations.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekOnHomotopy` and
  `Stacks.Cohomology.DerivedLowerShriek.restrictionOnHomotopy`: lower shriek and restriction
  applied degreewise to unbounded homotopy categories.
* `Stacks.Cohomology.DerivedLowerShriek.homotopyAdjunction`: the ordinary
  lower-shriek--restriction adjunction, read on the homotopy categories. Its unit and counit are
  the degreewise ones.
* `Stacks.Cohomology.DerivedLowerShriek.derivedRestriction` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedRestrictionComparison`: restriction on the
  unbounded derived categories, and the comparison identifying it with the degreewise functor.
* `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekComparison`: the total left derived
  functor of degreewise lower shriek, and its counit.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.restriction_exact`: restriction of sheaves of modules
  along a continuous and cocontinuous functor of sites is exact.
* `Stacks.Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic`:
  under an acyclicity hypothesis on lower shriek, `Lg_!` stays a left derived functor after
  composition with any functor out of `D(O_D)`.
* `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekAdjunction`,
  `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekAdjunction_unit_fac` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekAdjunction_counit_fac`: the derived
  adjunction and the factorizations of its unit and counit through the comparison
  transformations.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]

/-- Restriction of modules `g^* : Mod(O_D) ⥤ Mod(O_C)` along the functor of sites, for
`O_C = g^{-1} O_D`. -/
abbrev restrictionModules :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w} (inverseImageRing J K f O) :=
  SheafOfModules.pushforward.{w} (idRingMap J K f O)

/-- Lower shriek `g_! : Mod(O_C) ⥤ Mod(O_D)`, the left adjoint of restriction of modules. -/
abbrev lowerShriekModules :
    SheafOfModules.{w} (inverseImageRing J K f O) ⥤ SheafOfModules.{w} O :=
  SheafOfModules.pullback.{w} (idRingMap J K f O)

/-- Restriction of sheaves of modules along a continuous and cocontinuous functor of sites
preserves finite colimits. -/
instance preservesFiniteColimits_restriction :
    PreservesFiniteColimits (restrictionModules J K f O) := by
  have h : PreservesColimitsOfSize.{w, w} (restrictionModules J K f O) :=
    Stacks.SheafOfModules.pushforward_preservesColimits f _
  have : PreservesColimitsOfSize.{0, 0} (restrictionModules J K f O) :=
    preservesColimitsOfSize_shrink _
  infer_instance

omit [(SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint] in
/-- Restriction of sheaves of modules along a continuous and cocontinuous functor of sites is
exact. -/
theorem restriction_exact :
    exactFunctor (SheafOfModules.{w} O) (SheafOfModules.{w} (inverseImageRing J K f O))
      (restrictionModules J K f O) :=
  ⟨inferInstanceAs (PreservesFiniteLimits (restrictionModules J K f O)),
    preservesFiniteColimits_restriction J K f O⟩

/-- Restriction of sheaves of modules is additive. -/
instance additive_restriction : (restrictionModules J K f O).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (restriction_exact J K f O)

/-- The ordinary adjunction between lower shriek and restriction of sheaves of modules. -/
abbrev adjunctionModules : lowerShriekModules J K f O ⊣ restrictionModules J K f O :=
  SheafOfModules.pullbackPushforwardAdjunction.{w} (idRingMap J K f O)

/-- Lower shriek applied degreewise to unbounded homotopy categories. -/
abbrev lowerShriekOnHomotopy :
    HomotopyCategory (SheafOfModules.{w} (inverseImageRing J K f O)) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{w} O) (ComplexShape.up ℤ) :=
  (lowerShriekModules J K f O).mapHomotopyCategory (ComplexShape.up ℤ)

/-- Restriction applied degreewise to unbounded homotopy categories. -/
abbrev restrictionOnHomotopy :
    HomotopyCategory (SheafOfModules.{w} O) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{w} (inverseImageRing J K f O)) (ComplexShape.up ℤ) :=
  (restrictionModules J K f O).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The ordinary lower-shriek--restriction adjunction, read on the unbounded homotopy
categories. Its unit and counit are the degreewise unit and counit of `adjunctionModules`. -/
abbrev homotopyAdjunction :
    lowerShriekOnHomotopy J K f O ⊣ restrictionOnHomotopy J K f O :=
  (adjunctionModules J K f O).mapHomotopyCategory (ComplexShape.up ℤ)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of sheaves of modules, induced on the unbounded derived categories by
exactness. -/
abbrev derivedRestriction :
    DerivedCategory (SheafOfModules.{w} O) ⥤
      DerivedCategory (SheafOfModules.{w} (inverseImageRing J K f O)) :=
  (restrictionModules J K f O).mapDerivedCategory

/-- The comparison from degreewise restriction to restriction on the derived categories, an
isomorphism. -/
abbrev derivedRestrictionComparison :
    restrictionOnHomotopy J K f O ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedRestriction J K f O :=
  (restrictionModules J K f O).mapDerivedCategoryFactorsh.inv

/-- Restriction on the derived categories, with `derivedRestrictionComparison`, is the right
derived functor of degreewise restriction. -/
instance isRightDerivedFunctor_derivedRestriction :
    (derivedRestriction J K f O).IsRightDerivedFunctor (derivedRestrictionComparison J K f O)
      (HomotopyCategory.quasiIso (SheafOfModules.{w} O) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    ((restrictionModules J K f O).mapDerivedCategoryFactorsh)

/-- The quasi-isomorphisms of the unbounded homotopy category of `Mod(O_C)`. -/
abbrev sourceQuasiIso :
    MorphismProperty
      (HomotopyCategory (SheafOfModules.{w} (inverseImageRing J K f O)) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{w} (inverseImageRing J K f O)) (ComplexShape.up ℤ)

variable [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (sourceQuasiIso J K f O)]

/-- The canonical unbounded left derived lower-shriek functor `Lg_!`. -/
abbrev derivedLowerShriek :
    DerivedCategory (SheafOfModules.{w} (inverseImageRing J K f O)) ⥤
      DerivedCategory (SheafOfModules.{w} O) :=
  (lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
    (sourceQuasiIso J K f O)

/-- The comparison from derived lower shriek to degreewise lower shriek on the homotopy
category, i.e. the counit exhibiting `Lg_!` as a left derived functor. -/
abbrev derivedLowerShriekComparison :
    DerivedCategory.Qh ⋙ derivedLowerShriek J K f O ⟶
      lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh :=
  (lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
    (sourceQuasiIso J K f O)

omit [f.IsCocontinuous J K] in
/-- Suppose lower shriek carries every acyclic bounded-above complex whose terms satisfy
`IsSumOfExtensionByZeroUnits` to an acyclic complex. Then the left derived functor `Lg_!` stays a
left derived functor after composition with any functor `G` out of `D(O_D)`. -/
theorem isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}] [Small.{w} C]
    [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
      (𝟙 ((inverseImageRing J K f O).over U) :
        (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]
    (hFP : ∀ (a : ℤ)
      (Lc : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      Lc.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (Lc.X n)) → Lc.Acyclic →
      (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj Lc).Acyclic)
    {E : Type*} [Category E] (G : DerivedCategory (SheafOfModules.{w} O) ⥤ E) :
    (derivedLowerShriek J K f O ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedLowerShriek J K f O) G).inv ≫
        Functor.whiskerRight (derivedLowerShriekComparison J K f O) G)
      (sourceQuasiIso J K f O) := by
  have : HasExactColimitsOfShape ℕ
    (SheafOfModules.{w} (inverseImageRing J K f O)) := hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{w} O) := hasExactColimitsOfShape_nat _
  exact Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    (lowerShriekModules J K f O) (IsSumOfExtensionByZeroUnits (inverseImageRing J K f O))
    (fun _ _ ↦ isSumOfExtensionByZeroUnits_biprod _)
    (exists_epi_isSumOfExtensionByZeroUnits _) hFP DerivedCategory.Qh
    (derivedLowerShriek J K f O) (derivedLowerShriekComparison J K f O) G

variable [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)]
  [(derivedLowerShriek J K f O ⋙ derivedRestriction J K f O).IsLeftDerivedFunctor
  ((Functor.associator DerivedCategory.Qh (derivedLowerShriek J K f O)
      (derivedRestriction J K f O)).inv ≫
    Functor.whiskerRight (derivedLowerShriekComparison J K f O) (derivedRestriction J K f O))
  (sourceQuasiIso J K f O)]

/-- The unbounded left derived lower-shriek functor is left adjoint to derived restriction of
sheaves of modules. -/
def derivedLowerShriekAdjunction :
    derivedLowerShriek J K f O ⊣ derivedRestriction J K f O :=
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction (homotopyAdjunction J K f O)
    (sourceQuasiIso J K f O) (derivedLowerShriekComparison J K f O)
    (derivedRestrictionComparison J K f O)

/-- The unit of the derived adjunction is the one induced by the unit of the ordinary
lower-shriek--restriction adjunction, through the two canonical comparison transformations. -/
theorem derivedLowerShriekAdjunction_unit_fac
    (M : HomotopyCategory (SheafOfModules.{w} (inverseImageRing J K f O))
      (ComplexShape.up ℤ)) :
    (derivedLowerShriekAdjunction J K f O).unit.app (DerivedCategory.Qh.obj M) ≫
        (derivedRestriction J K f O).map
          ((derivedLowerShriekComparison J K f O).app M) =
      DerivedCategory.Qh.map ((homotopyAdjunction J K f O).unit.app M) ≫
        (derivedRestrictionComparison J K f O).app
          ((lowerShriekOnHomotopy J K f O).obj M) :=
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction_unit_app (homotopyAdjunction J K f O)
    (sourceQuasiIso J K f O) (derivedLowerShriekComparison J K f O)
    (derivedRestrictionComparison J K f O) M

/-- The counit of the derived adjunction is the one induced by the counit of the ordinary
lower-shriek--restriction adjunction, through the two canonical comparison transformations. -/
theorem derivedLowerShriekAdjunction_counit_fac
    (N : HomotopyCategory (SheafOfModules.{w} O) (ComplexShape.up ℤ)) :
    (derivedLowerShriek J K f O).map ((derivedRestrictionComparison J K f O).app N) ≫
        (derivedLowerShriekAdjunction J K f O).counit.app (DerivedCategory.Qh.obj N) =
      (derivedLowerShriekComparison J K f O).app ((restrictionOnHomotopy J K f O).obj N) ≫
        DerivedCategory.Qh.map ((homotopyAdjunction J K f O).counit.app N) :=
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction_counit_app (homotopyAdjunction J K f O)
    (sourceQuasiIso J K f O) (derivedLowerShriekComparison J K f O)
    (derivedRestrictionComparison J K f O) N

end Derived

end Stacks.Cohomology.DerivedLowerShriek

end

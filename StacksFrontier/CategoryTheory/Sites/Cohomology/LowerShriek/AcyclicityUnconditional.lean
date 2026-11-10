module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AcyclicityFromExtVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExtensionByZeroExtComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.TotalAcyclicityOfTheInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AC for sheaves of modules, unconditionally

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites satisfying the
covering-pullback clause of Stacks continuity, let `O_D` be a sheaf of rings on `D` and let
`O_C = g^{-1}O_D`. This file discharges the one open input of Stacks 07AC for
sheaves of modules — the acyclicity statement of Stacks 0794 at the class of direct sums of the
extensions by zero `j_{U!}O_U` — and so makes the unbounded left derived functor
`Lg_! : D(O_C) ⥤ D(O_D)` and its adjunction unconditional.

That is Stacks 08PC part (3) for sheaves of modules, and it is the functor `Lπ_!` of Stacks 09CY.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.subsingleton_ext_extensionByZeroUnit_restriction`:
  **Stacks 0D6X** in the `Ext` form the reduction consumes.
* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_preservesCoveringPullbacks`: the
  acyclicity statement of Stacks 07AC for modules holds.
* `Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek`: consequently
  degreewise lower shriek has a pointwise left derived functor — **Stacks 07AC for modules,
  existence, with no open hypothesis** — so that
  `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek` is available.
* `Stacks.Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_derivedLowerShriek_comp`: and it is
  absolute, which is the other hypothesis of the derived adjunction.
* `Stacks.Cohomology.DerivedLowerShriek.derivedModuleLowerShriekAdjunction`: **Stacks 08PC part
  (3) for sheaves of modules**, the adjunction `Lg_! ⊣ g^*` on the unbounded derived categories.
* `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek_commShift` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek_isTriangulated`: `Lg_!` commutes with
  the shift and is exact as a functor of triangulated categories. These two are exactly the
  instances that `Stacks.SimplicialModules.augmentedLowerShriek` asks of its `proj` parameter,
  so `Lg_!` here is the functor `Lπ_!` of Stacks 09CY that 09D3 was carrying as a parameter.

## How the three inputs meet

The statement about complexes was reduced to an object-level `Ext` vanishing in
`AcyclicityFromExtVanishing.lean`: by
`Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_ext_vanishing` it suffices that
`Ext^n(j_{U!}O_U, g^*I) = 0` for `n ≥ 1` and every injective `O_D`-module `I`. Three
facts then close it.

* `Stacks.Cohomology.DerivedLowerShriek.ext_eq_zero_of_isZero_sheafCohomology` converts that
  `Ext`-group into the sheaf cohomology of the underlying abelian sheaf over `U`: `j_{U!}O_U`
  corepresents sections over `U` in `Mod(O_C)` (Stacks 0G1V) and the free abelian sheaf on the
  representable corepresents them on abelian sheaves, and the two corepresentations agree
  because the forgetful functor is exact and carries injectives to `Ext`-acyclic objects.
* The underlying abelian sheaf of `g^*I` *is* `g^{-1}` of the underlying abelian sheaf of `I`:
  restriction of a sheaf of modules is precomposition with `uᵒᵖ` on underlying presheaves, so
  the two agree on the nose. This is the same identification as
  `Stacks.Cohomology.DerivedLowerShriek.restrictionModules_comp_moduleSections`.
* `Stacks.Cohomology.DerivedLowerShriek.vanishesOnObjects_inverseImage_sheafOfRings` is
  **Stacks 0D6X**: that cohomology vanishes in positive degrees, by the Čech computation of the
  source over the cofinal system of coverings furnished by the covering-pullback clause.

## What is and is not assumed

The covering-pullback clause `Stacks.Sites.PreservesCoveringPullbacks` is clause (2) of the
Stacks definition of a continuous functor of sites (Sites, Definition 00WV), so it is part of
the standing hypothesis of the source and not an addition; it is carried as an instance because
Mathlib's `CategoryTheory.Functor.IsContinuous` does not include it. Cocontinuity is a
hypothesis of Stacks 07AC and is used, as there, to make restriction exact.

There is **no hypothesis here beyond the source's**. The structure sheaf is an arbitrary
`Sheaf K RingCat`, as in Stacks 07AC, and not a sheaf of commutative rings as in
`AlgebraicGeometry.RingedSite`; this is possible because the Čech half of Stacks 0D6X,
`Stacks.CechSite.injective_moduleCechCohomology_isZero`, is stated for arbitrary rings. The
commutativity a Čech argument naively uses is *not* a packaging artefact: the Čech argument fed the
commutative
structure presheaf to a tensor construction whose objectwise exactness went through Mathlib's
`ModuleCat.extendScalars`, which is stated for commutative rings. Removing it needed a genuine
replacement, `Stacks.CechSite.extendScalarsGrp`, sound because `ℤ` is central in every ring and
the exactness proof needs only additivity.

Every site is small and every universe is the universe `w` of the module sections, as in
`TotalAcyclicityOfTheInverseImage.lean` and `ExtensionByZeroExtComparison.lean`, whose
statements this file joins.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace Stacks.Cohomology.DerivedLowerShriek

attribute [local instance] HasDerivedCategory.standard

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {D : Type w} [SmallCategory D] (K : GrothendieckTopology D) (O : Sheaf K RingCat.{w})
  (u : C ⥤ D)
  [u.IsContinuous J K] [u.IsCocontinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J u]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := u) (idRingMap J K u O)).IsRightAdjoint]
  [∀ V : C, (SheafOfModules.pushforward.{w} (F := Over.forget V)
    (𝟙 ((inverseImageRing J K u O).over V) :
      (inverseImageRing J K u O).over V ⟶
        (inverseImageRing J K u O).over V)).IsRightAdjoint]
  [EnoughInjectives (SheafOfModules.{w} (inverseImageRing J K u O))]
  [EnoughInjectives (SheafOfModules.{w} O)]

omit [u.IsCocontinuous J K] [HasSheafify K AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := u) (idRingMap J K u O)).IsRightAdjoint]
  [EnoughInjectives (SheafOfModules.{w} (inverseImageRing J K u O))]
  [EnoughInjectives (SheafOfModules.{w} O)] in
/-- **Stacks 0D6X in the form the reduction consumes.** For an injective `O_D`-module `I`, every
`Ext`-class of positive degree from `j_{V!}O_V` to `g^*I` in sheaves of `O_C`-modules vanishes.

`Ext` out of `j_{V!}O_V` is the sheaf cohomology of the underlying abelian sheaf over `V`, by
`ext_eq_zero_of_isZero_sheafCohomology`; the underlying abelian sheaf of `g^*I` is `g^{-1}` of
the underlying abelian sheaf of `I`, restriction being precomposition with `uᵒᵖ`; and that
cohomology vanishes by `vanishesOnObjects_inverseImage_sheafOfRings`. -/
theorem subsingleton_ext_extensionByZeroUnit_restriction (V : C)
    (I : SheafOfModules.{w} O) (hI : Injective I) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Abelian.Ext.{w}
      (extensionByZeroUnit (inverseImageRing J K u O) V)
      ((restrictionModules J K u O).obj I) n) := by
  have := hI
  have hvan := vanishesOnObjects_inverseImage_sheafOfRings.{w} J K O u I V (yoneda.obj V)
    (Functor.representableByEquiv.symm (Iso.refl _)) n hn
  refine subsingleton_of_forall_eq 0 fun e => ?_
  refine ext_eq_zero_of_isZero_sheafCohomology J (inverseImageRing J K u O) V
    ((restrictionModules J K u O).obj I) n ?_ e
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr hvan

omit [u.IsCocontinuous J K] in
/-- **The acyclicity statement of Stacks 07AC for sheaves of modules holds.** Lower shriek
carries every bounded above acyclic complex whose terms are direct sums of the extensions by
zero `j_{V!}O_V` to an acyclic complex.

This is `lowerShriekAcyclic_of_ext_vanishing` fed with
`subsingleton_ext_extensionByZeroUnit_restriction`, that is with Stacks 0D6X. -/
theorem lowerShriekAcyclic_of_preservesCoveringPullbacks :
    LowerShriekAcyclic J K u O :=
  lowerShriekAcyclic_of_ext_vanishing.{w, w} J K u O
    fun V I hI n hn => subsingleton_ext_extensionByZeroUnit_restriction J K O u V I hI n hn

/-- **Stacks 07AC for sheaves of modules, existence, with no open hypothesis.** Degreewise lower
shriek followed by the localization has a pointwise left derived functor, so the unbounded left
derived functor `Lg_! : D(O_C) ⥤ D(O_D)` of
`Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek` exists. -/
instance hasPointwiseLeftDerivedLowerShriek :
    (lowerShriekOnHomotopy J K u O ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso J K u O) :=
  hasPointwiseLeftDerivedLowerShriek_of_acyclic.{w} J K u O
    (lowerShriekAcyclic_of_preservesCoveringPullbacks J K O u)

/-- **The derived lower-shriek functor is absolute**, which is the second hypothesis of the
derived adjunction. It follows from the same acyclicity statement, the left derived functor of
Stacks 0794 being constructed by resolutions. -/
instance isLeftDerivedFunctor_derivedLowerShriek_comp :
    (derivedLowerShriek J K u O ⋙
        derivedRestriction J K u O).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedLowerShriek J K u O)
          (derivedRestriction J K u O)).inv ≫
        Functor.whiskerRight (derivedLowerShriekComparison J K u O)
          (derivedRestriction J K u O))
      (sourceQuasiIso J K u O) :=
  isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic J K u O
    (lowerShriekAcyclic_of_preservesCoveringPullbacks J K O u) _

variable [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)]

/-- **Stacks 08PC part (3), and the functor `Lπ_!` of Stacks 09CY, for sheaves of modules.** The
unbounded left derived lower-shriek functor `Lg_! : D(O_C) ⥤ D(O_D)` together with its
adjunction to derived restriction, now with no open hypothesis. -/
def derivedModuleLowerShriekAdjunction :
    derivedLowerShriek J K u O ⊣ derivedRestriction J K u O :=
  derivedLowerShriekAdjunction J K u O

/-- **`Lg_!` commutes with the shift**, being a left adjoint of a functor that does. This is one
of the two instances that `Stacks.SimplicialModules.augmentedLowerShriek` asks of its `proj`
parameter. -/
instance derivedLowerShriek_commShift :
    (derivedLowerShriek J K u O).CommShift ℤ :=
  (derivedModuleLowerShriekAdjunction J K O u).leftAdjointCommShift ℤ

/-- **`Lg_!` is an exact functor of triangulated categories.** This is the other instance that
`Stacks.SimplicialModules.augmentedLowerShriek` asks of its `proj` parameter. -/
instance derivedLowerShriek_isTriangulated :
    (derivedLowerShriek J K u O).IsTriangulated :=
  have : (derivedModuleLowerShriekAdjunction J K O u).CommShift ℤ :=
    (derivedModuleLowerShriekAdjunction J K O u).commShift_of_rightAdjoint ℤ
  (derivedModuleLowerShriekAdjunction J K O u).isTriangulated_leftAdjoint

end Stacks.Cohomology.DerivedLowerShriek

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Discharging the adjoint-existence hypotheses of Stacks 07AC

`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic` reduces
the existence half of Stacks 07AC to the one statement that is its mathematical content — that
the lower-shriek functor carries a bounded above acyclic complex with terms in the generating
class to an acyclic complex — but it carries **three** further hypotheses that are not content:
`Small.{w} C` and the existence of the left adjoints of restriction of sheaves of modules along
the functor of sites and along `Over.forget U` for each slice. Those were hypotheses because
Mathlib supplies the corresponding instances only for small sites whose objects, morphisms,
rings and module sections lie in one universe.

They are no longer hypotheses: `SheafOfModules.pushforward_isRightAdjoint_of_univLE` and
`Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint_of_univLE` supply them with the
two sites, their morphisms, the sheaves of rings and the module sections in mutually
independent universes, subject only to `UnivLE` into the universe of the sections. This file
records that, so that a consumer of Stacks 07AC supplies the acyclicity statement and nothing
else.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic_univLE`:
  Stacks 07AC, existence, with the acyclicity statement as its only non-instance hypothesis.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC, existence, with no adjointness hypotheses.** If the lower-shriek functor
carries every bounded above acyclic complex whose terms are direct sums of extensions by zero
of the structure sheaves of the slices to an acyclic complex, then it has an unbounded left
derived functor. This is
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic` with its
`Small.{w} C` hypothesis and its two `IsRightAdjoint` hypotheses discharged: the universes of
the two sites and of their morphisms are independent of the universe `w` of the sheaves of
rings and of the module sections, and are related to it only by `UnivLE`. -/
theorem hasPointwiseLeftDerivedLowerShriek_of_acyclic_univLE
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (O : Sheaf K RingCat.{w})
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}]
    [UnivLE.{u₁, w}] [UnivLE.{v₁, w}] [UnivLE.{v₂, w}]
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((SheafOfModules.pullback.{w} (idRingMap J K f O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic) :
    let S := (f.sheafPushforwardContinuous RingCat.{w} J K).obj O
    let φ : S ⟶ S := 𝟙 S
    let F := SheafOfModules.pullback.{w} φ
    let : F.Additive := by
      let _ := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
      exact Functor.additive_of_preservesBinaryBiproducts F
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} S) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedLowerShriek_of_acyclic.{w} J K f O hFP

end Stacks.Cohomology.DerivedLowerShriek

end

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lower shriek for modules is left exact when the slices of the functor of sites are equivalences

Let `u : C ⥤ D` be a continuous functor of sites and let `O` be a sheaf of rings on `D`.  Writing
`g : Sh(C) ⟶ Sh(D)` for the associated morphism of topoi and `O_C = g^{-1}O`, restriction of
modules `g^* : Mod(O) ⥤ Mod(O_C)` is `SheafOfModules.pushforward` at the identity of `O_C`, and
its left adjoint is `g_!`, lower shriek for modules.

This file proves that `g_!` is **left exact**, and hence that `g^*` carries injective modules to
injective modules, under the hypothesis that **every slice functor `Over.post u` is an
equivalence**.  That hypothesis is what makes the two lower shrieks — the one on abelian sheaves
and the one on modules — agree: the comparison transformation of Stacks 0798 is in general *not*
invertible (`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`), but it is invertible under
exactly this hypothesis, by
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence`.  Granted that,
left exactness of `g_!` on modules is left exactness of `g_!` on abelian sheaves, which is the
left-exact half of Stacks 04BH, `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`.

The localization functor `Over.forget U : C/U ⥤ C` satisfies the hypothesis, so this generalizes
the exactness of extension by zero of Stacks 03DJ
(`Stacks.Sites.ExtensionByZero.extensionByZero_exact`) and, with it, part (1) of Stacks 03F3
(`Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor_of_essentiallySmall`), away
from a slice projection to any functor of sites whose slices are equivalences.  The gain is that
the direct-sum formula for the sections of extension by zero, which is what the localization proofs
rest on and which has no analogue for a general functor of sites, is not used.

## Main results

* `Stacks.SheafOfModules.hasPointwiseLeftKanExtension_op_of_essentiallySmall`: an essentially
  small source site has pointwise left Kan extensions of abelian presheaves along `u.op`.
* `Stacks.SheafOfModules.preservesFiniteLimits_pullback_of_sliceEquivalence`: **lower shriek for
  sheaves of modules is left exact**, the generalization of Stacks 03DJ.
* `Stacks.SheafOfModules.preservesInjectiveObjects_pullback_of_sliceEquivalence`: **restriction of
  modules carries injective modules to injective modules**, the generalization of Stacks 03F3,
  part (1).

## Implementation notes

The source site is asked to be essentially small in the universe of the module sections, which is
where the left adjoint comes from — `SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall`
— and which also discharges the pointwise-Kan-extension hypothesis of Stacks 04BH, through
`CategoryTheory.Limits.hasColimitsOfShape_of_essentiallySmall` applied to the comma categories
`CostructuredArrow u.op V`.  The universe of the sheaves of rings is taken equal to the universe of
the module sections, because
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence` needs the
presheaf-level left adjoint at the spelling `PresheafOfModules.pushforward (𝟙 (u.op ⋙ O.obj))`,
which `PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall` supplies at that seating.

Cocontinuity of `u` is *not* a hypothesis: the left adjoint is produced from essential smallness
rather than from the adjunction of a morphism of topoi, and Stacks 04BH asks only continuity
together with fibre products and equalizers of the source which `u` preserves.

## References

* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
  [F.IsContinuous J K] (O : Sheaf K RingCat.{w})
  [EssentiallySmall.{w} C] [LocallySmall.{w} D]
  [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingParallelPair F]
  [∀ x : C, (Over.post (X := x) F).IsEquivalence]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasPullbacks C] [HasEqualizers C] [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingParallelPair F] [∀ x : C, (Over.post (X := x) F).IsEquivalence] in
/-- Left Kan extensions of abelian presheaves along the opposite of a functor of sites exist
pointwise as soon as the source site is essentially small in the universe of the sections.

The comma category `CostructuredArrow F.op V` computing the extension at `V` is then essentially
small, so colimits of its shape exist in abelian groups.  This is the hypothesis under which the
left-exact half of Stacks 04BH is stated. -/
theorem hasPointwiseLeftKanExtension_op_of_essentiallySmall :
    ∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{w}, F.op.HasPointwiseLeftKanExtension G := by
  intro G V
  have := hasColimitsOfShape_of_essentiallySmall.{w} (CostructuredArrow F.op V)
    AddCommGrpCat.{w}
  infer_instance

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Lower shriek for sheaves of modules is left exact** when every slice functor of the functor
of sites is an equivalence: the generalization of Stacks 03DJ away from a localization.

Forgetting the module structure commutes with lower shriek under that hypothesis, by part of
Stacks 0798 — `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence` — so
the composite of `g_!` with the forgetful functor to abelian sheaves is lower shriek on abelian
sheaves, which is left exact by the left-exact half of Stacks 04BH.  The forgetful functor
reflects limits, so `g_!` itself is left exact. -/
theorem preservesFiniteLimits_pullback_of_sliceEquivalence :
    PreservesFiniteLimits (_root_.SheafOfModules.pullback.{w} (structureMap J K F O)) := by
  have hpk := hasPointwiseLeftKanExtension_op_of_essentiallySmall.{w} F
  have hg : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      F AddCommGrpCat.{w} J K) :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits F J K
  have hg' : PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{w} J K) :=
    preservesFiniteLimits_of_natIso
      (Functor.sheafPullbackConstruction.sheafPullbackIso F AddCommGrpCat.{w} J K).symm
  have hiso : IsIso (lowerShriekForgetComparison.{w, w} F (structureMap J K F O)) :=
    isIso_lowerShriekForgetComparison_of_sliceEquivalence.{w, w} J K F O
  have h1 : PreservesFiniteLimits (_root_.SheafOfModules.toSheaf.{w}
        (inverseImageRing J K F O) ⋙ F.sheafPullback AddCommGrpCat.{w} J K) :=
    comp_preservesFiniteLimits _ _
  have h2 : PreservesFiniteLimits (_root_.SheafOfModules.pullback.{w} (structureMap J K F O) ⋙
      _root_.SheafOfModules.toSheaf.{w} O) :=
    preservesFiniteLimits_of_natIso (asIso (lowerShriekForgetComparison.{w, w} F _))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (_root_.SheafOfModules.toSheaf.{w} O)

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Restriction of modules along a functor of sites all of whose slice functors are
equivalences carries injective modules to injective modules**: the generalization of part (1) of
Stacks 03F3 away from a localization.

Restriction is right adjoint to lower shriek, which is left exact by
`Stacks.SheafOfModules.preservesFiniteLimits_pullback_of_sliceEquivalence` and so preserves
monomorphisms; a right adjoint of a monomorphism-preserving functor preserves injective
objects. -/
@[sga "4 V 4.11" "1), special case"]
theorem preservesInjectiveObjects_pullback_of_sliceEquivalence :
    (_root_.SheafOfModules.pushforward.{w} (structureMap J K F O)).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_pullback_of_sliceEquivalence.{w} J K F O
  have := preservesMonomorphisms_of_preservesLimitsOfShape
    (_root_.SheafOfModules.pullback.{w} (structureMap J K F O))
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} (structureMap J K F O))

end Stacks.SheafOfModules

end

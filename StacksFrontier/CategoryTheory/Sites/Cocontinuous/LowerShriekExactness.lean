module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekTypeExactness
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Presheaf.Functoriality.StructuredArrowCompletion
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of lower shriek on abelian sheaves

Let `u : C ⥤ D` be a continuous functor between sites. If `C` has fibre products and equalizers
and `u` preserves them, then lower shriek from abelian sheaves on `C` to abelian sheaves on `D`
preserves finite limits. Independently of those hypotheses, lower shriek preserves finite
colimits. Together these say that lower shriek is exact.

## Main results

* `Stacks.Sites.LowerShriek.hasExactColimitsOfShape_of_span_and_coequalizer`: colimits of a
  shape in which spans are completed to commutative squares and parallel pairs are coequalized
  are exact in an abelian category satisfying `AB5`.
* `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`: lower shriek preserves finite
  limits.
* `Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits`: lower shriek preserves finite
  colimits.

## References

* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w vA uA vC vD uC uD

namespace Stacks.Sites.LowerShriek

/-- A shape in which every span is completed by a commutative square and every parallel pair is
coequalized has exact colimits in an abelian category satisfying `AB5`. -/
theorem hasExactColimitsOfShape_of_span_and_coequalizer
    {J : Type uC} [Category.{vC} J] {A : Type uA} [Category.{vA} A]
    [UnivLE.{uC, vA}] [UnivLE.{vC, vA}]
    [HasColimitsOfShape J A]
    [Abelian A] [Limits.HasColimitsOfSize.{vA, vA} A] [AB5OfSize.{vA, vA} A]
    (hspan : ∀ (x y z : J) (f : x ⟶ y) (g : x ⟶ z),
      ∃ (W : J) (a : y ⟶ W) (b : z ⟶ W), f ≫ a = g ≫ b)
    (hpar : ∀ (x y : J) (f g : x ⟶ y),
      ∃ (W : J) (a : y ⟶ W), f ≫ a = g ≫ a) : HasExactColimitsOfShape J A := by
  have : LocallySmall.{vA} J := locallySmall_of_univLE J
  let e := (ShrinkHoms.equivalence J).trans
    (Shrink.equivalence.{vA, vA} (ShrinkHoms.{uC} J))
  have : HasExactColimitsOfShape (Shrink.{vA} (ShrinkHoms.{uC} J)) A :=
    hasExactColimitsOfShape_of_isPseudofiltered (hasSpanCocone_of_equivalence e hspan)
      (hasCoequalizingHom_of_equivalence e hpar)
  exact HasExactColimitsOfShape.of_domain_equivalence A e.symm

@[sga "4 I 2.10" "special case"]
private theorem preservesFiniteLimits_lan_ab
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [∀ F : Cᵒᵖ ⥤ Ab.{w}, u.op.HasPointwiseLeftKanExtension F] :
    PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Ab.{w}) ⥤ (Dᵒᵖ ⥤ Ab.{w})) := by
  let U := AddCommGrpCat.uliftFunctor.{max (max uC vD) vC, w}
  let R₁ := (Functor.whiskeringRight Cᵒᵖ Ab.{w} Ab.{max w (max (max uC vD) vC)}).obj U
  let R₂ := (Functor.whiskeringRight Dᵒᵖ Ab.{w} Ab.{max w (max (max uC vD) vC)}).obj U
  have : U.PreservesPointwiseLeftKanExtensions u.op := fun F ↦ by infer_instance
  have : ∀ F : Cᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)},
      u.op.HasPointwiseLeftKanExtension F := by infer_instance
  have hLarge : PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)}) ⥤
        (Dᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)})) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max w (max (max uC vD) vC)}
    intro I _ _
    apply preservesLimitsOfShape_of_evaluation _ I
    intro Y
    let E := Ab.{max w (max (max uC vD) vC)}
    have := Limits.hasColimitsOfSizeShrink.{vC, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    have := Limits.hasColimitsOfSizeShrink.{max uC vD, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    have := Limits.hasColimitsOfSizeShrink.{max vC (max uC vD), max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    have := AB5OfSize_shrink.{vC, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    have := AB5OfSize_shrink.{max uC vD, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    have : HasExactColimitsOfShape (StructuredArrow (Y.unop) u)ᵒᵖ E :=
      hasExactColimitsOfShape_of_span_and_coequalizer (A := E)
        (structuredArrow_op_span_and_parallelPair_completion u Y.unop).1
          (structuredArrow_op_span_and_parallelPair_completion u Y.unop).2
    have : HasExactColimitsOfShape (CostructuredArrow u.op Y) E :=
      HasExactColimitsOfShape.of_domain_equivalence _
        (structuredArrowOpEquivalence u Y.unop)
    exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm
  have : PreservesFiniteLimits (R₁ ⋙
      (u.op.lan : (Cᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)}) ⥤
        (Dᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)}))) := comp_preservesFiniteLimits R₁ _
  have hComp : PreservesFiniteLimits
      ((u.op.lan : (Cᵒᵖ ⥤ Ab.{w}) ⥤ (Dᵒᵖ ⥤ Ab.{w})) ⋙ R₂) :=
    preservesFiniteLimits_of_natIso (Functor.lanCompIsoOfPreserves U u.op).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ R₂

/-- If a continuous functor between sites has a source with fibre products and equalizers which
it preserves, then lower shriek on abelian sheaves preserves finite limits. -/
@[stacks 04BH "preservation of finite limits", instance, sga "4 III 1.3" "5), Ab-valued"]
public theorem gShriek_preservesFiniteLimits
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [∀ F : Cᵒᵖ ⥤ Ab.{w}, u.op.HasPointwiseLeftKanExtension F]
    [HasSheafify K Ab.{w}] :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback u Ab.{w} J K) := by
  have := preservesFiniteLimits_lan_ab u
  show PreservesFiniteLimits
    (sheafToPresheaf J Ab.{w} ⋙ u.op.lan ⋙ presheafToSheaf K Ab.{w})
  infer_instance

/-- Lower shriek along a continuous functor `u` preserves finite colimits, for sheaves valued in
any category `A` for which the left Kan extensions along `u.op` and weak sheafification on the
target site exist. -/
@[stacks 04BH "preservation of finite colimits", instance, sga "4 III 1.3" "4), finite colimits"]
public theorem gShriek_preservesFiniteColimits
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (A : Type uA) [Category.{vA} A]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]
    [HasWeakSheafify K A] :
    PreservesFiniteColimits
      (Functor.sheafPullbackConstruction.sheafPullback u A J K) := by
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).isLeftAdjoint
  infer_instance

end Stacks.Sites.LowerShriek

end

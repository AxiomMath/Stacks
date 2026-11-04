module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Presheaf.Functoriality.StructuredArrowCompletion
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of lower shriek on sheaves of modules

Let `u : C ⥤ D` be a continuous functor between sites and `R` a ring. If `C` has fibre products
and equalizers and `u` preserves them, then lower shriek from sheaves of `R`-modules on `C` to
sheaves of `R`-modules on `D` preserves finite limits. This is the module-coefficient companion of
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`, and the argument is the same one: lower
shriek is the sheafification of the left Kan extension along `u.op`, sheafification is exact, and
the Kan extension is computed pointwise as a colimit over a costructured-arrow category which the
two hypotheses make pseudofiltered (Stacks 00X4). A pseudofiltered colimit of modules is exact
because it is one of abelian groups.

## Main results

* `Stacks.Sites.LowerShriek.preservesFiniteLimits_lan_module` — the left Kan extension along
  `u.op` on presheaves of `R`-modules preserves finite limits.
* `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits_module` — **lower shriek on sheaves of
  `R`-modules preserves finite limits**.

## Implementation notes

The three universe inequalities say that the coefficient universe `w` receives the
costructured-arrow categories: those have objects in `Type (max uC vD)` and morphisms in
`Type vC`, and the shape of a colimit over them has to be small enough both for the colimit to
exist in `ModuleCat.{w} R` and for the exactness criterion
`Stacks.Sites.LowerShriek.hasExactColimitsOfShape_of_span_and_coequalizer` to apply. The ring
universe is free: nothing here mentions a functor tying the ring to the modules.

`AB5` for `ModuleCat.{w} R` is assembled by hand rather than taken from Mathlib, whose instance
holds only when the ring and the modules share a universe: it is the image of the axiom for
abelian groups along the forgetful functor, which preserves the colimits in question.

## References

* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 00X4](https://stacks.math.columbia.edu/tag/00X4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w r vC vD uC uD vJ uJ vE uE

namespace Stacks.Sites.LowerShriek

/-- A category whose objects and morphisms are no larger than the universe of the morphisms of
the coefficients has colimits of its shape as soon as the coefficients have colimits of that
size. -/
private theorem hasColimitsOfShape_of_univLE
    (J : Type uJ) [Category.{vJ} J] (A : Type uE) [Category.{vE} A]
    [UnivLE.{uJ, w}] [UnivLE.{vJ, w}]
    [HasColimitsOfSize.{w, w, vE, uE} A] : HasColimitsOfShape J A :=
  let : HasColimitsOfSize.{vJ, uJ, vE, uE} A := hasColimitsOfSizeOfUnivLE.{w, w, vJ, uJ} A
  inferInstance

/-- **Stacks 04BH for module coefficients, at the level of presheaves.** If `C` has fibre
products and equalizers which `u` preserves, then the left Kan extension along `u.op` of
presheaves of `R`-modules preserves finite limits.

The Kan extension is computed pointwise as a colimit over `CostructuredArrow u.op Y`, which is
equivalent to the opposite of a comma category `StructuredArrow Y u`; the two hypotheses make
that opposite satisfy the span and coequalizer conditions of Stacks 002X, so colimits over it are
exact in any abelian category satisfying `AB5` at the relevant size, and `ModuleCat.{w} R` is
one. -/
@[sga "4 I 5.8.3" "special case"]
public theorem preservesFiniteLimits_lan_module
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (u : C ⥤ D) (R : Type r) [Ring R]
    [UnivLE.{max uC uD, w}] [UnivLE.{max vC vD, w}] [UnivLE.{max uC vD, w}]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [∀ F : Cᵒᵖ ⥤ ModuleCat.{w} R, u.op.HasPointwiseLeftKanExtension F] :
    PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{w} R)) := by
  let E := ModuleCat.{w} R
  let : HasColimitsOfSize.{w, w} E := ModuleCat.hasColimitsOfSize.{w, r, w, w} R
  let : PreservesColimits (forget₂ E AddCommGrpCat.{w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{w, r, w, w} R
  let : AB5 E :=
    { ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor J
        (forget₂ E AddCommGrpCat.{w}) }
  let : UnivLE.{vC, w} :=
    @UnivLE.trans.{vC, max vC vD, w} univLE_max inferInstance
  let : ∀ Y : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow u.op Y) E :=
    fun Y => hasColimitsOfShape_of_univLE (CostructuredArrow u.op Y) E
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{w}
  intro I _ _
  apply preservesLimitsOfShape_of_evaluation _ I
  intro Y
  let : HasColimitsOfShape (StructuredArrow Y.unop u)ᵒᵖ E :=
    hasColimitsOfShape_of_univLE (StructuredArrow Y.unop u)ᵒᵖ E
  let : HasExactColimitsOfShape (StructuredArrow Y.unop u)ᵒᵖ E :=
    hasExactColimitsOfShape_of_span_and_coequalizer
      (J := (StructuredArrow Y.unop u)ᵒᵖ) (A := E)
      (CategoryTheory.structuredArrow_op_span_and_parallelPair_completion u Y.unop).1
      (CategoryTheory.structuredArrow_op_span_and_parallelPair_completion u Y.unop).2
  let : HasExactColimitsOfShape (CostructuredArrow u.op Y) E :=
    HasExactColimitsOfShape.of_domain_equivalence _
      (structuredArrowOpEquivalence u Y.unop)
  exact preservesLimitsOfShape_of_natIso
    (CategoryTheory.lanEvaluationIsoColimit E u.op Y).symm

/-- **Stacks 04BH for module coefficients.** If a continuous functor between sites has a source
with fibre products and equalizers which it preserves, then lower shriek on sheaves of
`R`-modules preserves finite limits. Being a left adjoint it preserves finite colimits, so it is
exact. -/
@[stacks 04BH "preservation of finite limits, module coefficients"]
public theorem gShriek_preservesFiniteLimits_module
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (u : C ⥤ D) (R : Type r) [Ring R]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [UnivLE.{max uC uD, w}] [UnivLE.{max vC vD, w}] [UnivLE.{max uC vD, w}]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [∀ F : Cᵒᵖ ⥤ ModuleCat.{w} R, u.op.HasPointwiseLeftKanExtension F]
    [HasSheafify K (ModuleCat.{w} R)] :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback u (ModuleCat.{w} R) J K) := by
  let : PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{w} R)) :=
    preservesFiniteLimits_lan_module u R
  show PreservesFiniteLimits
    (sheafToPresheaf J (ModuleCat.{w} R) ⋙ u.op.lan ⋙ presheafToSheaf K (ModuleCat.{w} R))
  apply comp_preservesFiniteLimits

end Stacks.Sites.LowerShriek

end

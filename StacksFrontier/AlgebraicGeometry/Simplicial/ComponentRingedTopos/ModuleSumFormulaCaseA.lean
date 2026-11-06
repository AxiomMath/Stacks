module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanSumFormula
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentCommaDecomposition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ContinuousAugmentationSiteFunctors

/-!
# The componentwise direct sum for module lower shriek, case (A)

Let `C` be a simplicial site — case (A) of the simplicial-site situation of Stacks 09WE — and let
`O` be a sheaf of rings on its total site. Stacks 0D72 says that the restriction to simplicial
degree `m` of module lower shriek from degree `n` is the direct sum, over the simplex maps
`φ : [n] ⟶ [m]`, of the module pullbacks along the transitions `f_φ`. This file proves that, for
sheaves of modules, in case (A).

## Main definitions

* `CategoryTheory.SimplicialSite.transitionFunctorA`: the transition functor `u_φ : C_n ⥤ C_m` of
  case (A).
* `CategoryTheory.SimplicialSite.transitionNatTransA`: the cross-fibre arrows `(φ, 𝟙)`.
* `CategoryTheory.SimplicialSite.ringTransitionA`: the ring map `O(φ) : O_n ⟶ (u_φ)_* O_m`.
* `CategoryTheory.SimplicialSite.transitionModulePullbackA`: the summand `f_φ^*`, the pullback of
  sheaves of modules along `O(φ)`.

## Main results

* `CategoryTheory.SimplicialSite.componentModuleSumFormulaA`: **Stacks 0D72, the componentwise
  direct-sum formula for sheaves of modules in case (A).**

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor Stacks.SheafOfModules.RestrictRan

universe u

namespace CategoryTheory.SimplicialSite

variable (C : SimplicialSite.{u}) {n m : SimplexCategory}

/-- The transition functor `u_φ : C_n ⥤ C_m` of case (A). -/
def transitionFunctorA (φ : n ⟶ m) :
    (situation C).component n ⥤ (situation C).component m :=
  (C.underlying.map φ).toFunctor

/-- The transition functor of case (A) is continuous for the component topologies. -/
instance isContinuous_transitionFunctorA (φ : n ⟶ m) :
    (transitionFunctorA C φ).IsContinuous
      ((situation C).componentTopology n) ((situation C).componentTopology m) :=
  (C.isMorphismOfSites φ).isContinuous

/-- The cross-fibre arrows `(φ, 𝟙)` of case (A), as a natural transformation from `u_φ` followed
by the degree-`m` component inclusion to the degree-`n` component inclusion. -/
def transitionNatTransA (φ : n ⟶ m) :
    transitionFunctorA C φ ⋙ SimplicialSiteSituation.componentFunctor (situation C) m ⟶
      SimplicialSiteSituation.componentFunctor (situation C) n :=
  SimplicialSiteSituation.continuousInclusionTransition C φ

variable (O : Sheaf (situation C).totalTopology RingCat.{u})

/-- The ring map `O(φ) : O_n ⟶ (u_φ)_* O_m` of Stacks 0D72 in case (A): restriction of the total
sheaf of rings along the cross-fibre arrows `(φ, 𝟙)`. -/
def ringTransitionA (φ : n ⟶ m) :
    (situation C).componentRingSheaf O n ⟶
      ((transitionFunctorA C φ).sheafPushforwardContinuous RingCat.{u}
        ((situation C).componentTopology n) ((situation C).componentTopology m)).obj
        ((situation C).componentRingSheaf O m) :=
  ringComparisonSheaf (SimplicialSiteSituation.componentFunctor (situation C) n)
    (SimplicialSiteSituation.componentFunctor (situation C) m)
    ((situation C).componentTopology n) ((situation C).componentTopology m)
    (situation C).totalTopology O (transitionFunctorA C φ) (transitionNatTransA C φ)

/-- Pointwise right Kan extensions along the opposite of the degree-`m` component inclusion exist
at abelian coefficients. -/
instance hasPointwiseRan_componentA (m : SimplexCategory)
    (G : (C.underlying.obj m)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (CoGrothendieck.ι C.totalPseudofunctor (op m)).op.HasPointwiseRightKanExtension G :=
  inferInstance

/-- Right Kan extensions along the opposite of the degree-`m` component inclusion exist at
abelian coefficients. -/
instance hasRan_componentA (m : SimplexCategory)
    (G : (C.underlying.obj m)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (CoGrothendieck.ι C.totalPseudofunctor (op m)).op.HasRightKanExtension G :=
  (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension _ G).hasRightKanExtension

/-- The direct image of sheaves of modules along `O(φ)` has a left adjoint. -/
instance isRightAdjoint_pushforward_ringTransitionA (φ : n ⟶ m) :
    (_root_.SheafOfModules.pushforward.{u}
      (ringComparisonSheaf (SimplicialSiteSituation.componentFunctor (situation C) n)
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        ((situation C).componentTopology n) ((situation C).componentTopology m)
        (situation C).totalTopology O (transitionFunctorA C φ)
        (transitionNatTransA C φ))).IsRightAdjoint :=
  inferInstance

/-- The summand `f_φ^*` of Stacks 0D72 in case (A): the pullback of sheaves of modules along the
ring map `O(φ)`, for the morphism of sites given by the transition functor `u_φ`. -/
def transitionModulePullbackA (φ : n ⟶ m) :
    _root_.SheafOfModules.{u} ((situation C).componentRingSheaf O n) ⥤
      _root_.SheafOfModules.{u} ((situation C).componentRingSheaf O m) :=
  _root_.SheafOfModules.pullback.{u} (ringTransitionA C O φ)

/-- The direct sum of the case-(A) summands exists. -/
instance (priority := high) hasCoproduct_transitionModulePullbackA (n m : SimplexCategory) :
    HasCoproduct (fun i : n ⟶ m => _root_.SheafOfModules.pullback.{u}
      (ringComparisonSheaf (SimplicialSiteSituation.componentFunctor (situation C) n)
        (SimplicialSiteSituation.componentFunctor (situation C) m)
        ((situation C).componentTopology n) ((situation C).componentTopology m)
        (situation C).totalTopology O (transitionFunctorA C i) (transitionNatTransA C i))) :=
  letI : HasColimitsOfShape (Discrete (n ⟶ m))
      (_root_.SheafOfModules.{u} ((situation C).componentRingSheaf O n) ⥤
        _root_.SheafOfModules.{u} ((situation C).componentRingSheaf O m)) :=
    functorCategoryHasColimitsOfShape
  HasColimitsOfShape.has_colimit _

/-- The direct sum of the case-(A) summands `f_φ^*` exists, stated with
`transitionModulePullbackA` itself (instance search does not unfold it). -/
instance (priority := high) hasCoproduct_transitionModulePullbackA' (n m : SimplexCategory) :
    HasCoproduct (fun φ : n ⟶ m => transitionModulePullbackA C O φ) :=
  hasCoproduct_transitionModulePullbackA C O n m

/-- **Stacks 0D72, the componentwise direct-sum formula for sheaves of modules in case (A).**
The restriction to simplicial degree `m` of lower shriek `g_{n!}` of sheaves of `O`-modules from
degree `n` is the direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the pullbacks `f_φ^*` of
sheaves of modules along the transitions, each taken along the ring map `O(φ)`. -/
@[stacks 0D72 "direct-sum formula in case (A), on sheaves of modules"]
def componentModuleSumFormulaA (n m : SimplexCategory) :
    (∐ fun φ : n ⟶ m => transitionModulePullbackA C O φ) ≅
      (situation C).componentModuleLowerShriek O n ⋙
        (situation C).componentModuleRestriction O m := by
  haveI : (_root_.SheafOfModules.pushforward.{u}
      (F := SimplicialSiteSituation.componentFunctor (situation C) n)
      (𝟙 ((situation C).componentRingSheaf O n))).IsRightAdjoint :=
    SimplicialSiteSituation.componentModuleRestriction_isRightAdjoint _ O n
  exact pullbackCompRestrictIsoCoproductOfRan
    (SimplicialSiteSituation.componentFunctor (situation C) n)
    (SimplicialSiteSituation.componentFunctor (situation C) m)
    ((situation C).componentTopology n) ((situation C).componentTopology m)
    (situation C).totalTopology O (fun φ : n ⟶ m => transitionFunctorA C φ)
    (fun φ : n ⟶ m => transitionNatTransA C φ)
    (fun P U => isLimitFanRanComponent C U P)

end CategoryTheory.SimplicialSite

end

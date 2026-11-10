module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleProjection
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormulaSummandLeg
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionTargetSummand

/-!
# The summandwise comparison of Stacks 0D9E (2), reduced to one square at a simplex map

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site all of whose structure-sheaf transitions are flat. The one hypothesis
`CategoryTheory.SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection` still
carries is `proj_restrict`: that the restriction to a degree `m` of the canonical map
`g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` of Stacks 0D9E (2) is, under the direct-sum identifications of its
source and its target, the direct sum of the derived transitions `K(φ)` of Stacks 07TF (4).

Both sides of `proj_restrict` are maps *out of* `g_m^*g_{n!}K_n`, which the componentwise
direct-sum formula of Stacks 0D72 (6) identifies with `⨁_φ Lf_φ^*K_n`. The summand inclusions of
both identifications are now theorems — of the source by
`CategoryTheory.SimplicialSiteSituation.DerivedModuleSumFormulaSummand`, of the target by
`CategoryTheory.SimplicialSiteSituation.biproduct_ι_moduleProjectionTargetIso_inv` — so the square
can be checked one summand at a time. This file performs that reduction, and reduces it once more
by the transposition that defines the canonical map. What is left is a single square at each
simplex map `φ : [n] ⟶ [m]`, stated in
`CategoryTheory.SimplicialSiteSituation.moduleProjection_restrict_of_adjunctSquare` and containing
neither a biproduct nor either direct-sum formula.

## Main results

* `…unit_comp_derivedComponentModuleRestriction_map_moduleProjection`: the canonical map of
  Stacks 0D9E (2) transposes back to the adjunct it was built from.
* `…derivedTransitionPullback_map_unit_comp_derivedComponentModuleTransition_comp_map`:
  the canonical leg of Stacks 0D72 (6) at `K_n`, followed by the restriction to degree `m` of the
  canonical map, is the derived adjunct of Stacks 0D9E (2) carried along `Lf_φ^*` and then the
  derived transition of Stacks 0D9P.
* `…moduleProjection_restrict_of_componentSquare`:
  **`proj_restrict` holds as soon as it holds on each summand**, granted the summand description
  of the source formula.
* `…moduleProjection_restrict_of_adjunctSquare`:
  **`proj_restrict` reduced to one square at each simplex map**, with the canonical map and the
  source direct-sum formula both eliminated.

## Implementation notes

*Why the componentwise route works.* `proj_restrict` compares two maps `g_m^*g_{n!}K_n ⟶ ⨁_φ K_m`,
one of which is already presented as `(sum formula) ≫ (direct sum of the transitions)`. Composing
with the inverse of the sum formula turns it into an equation between maps out of the biproduct
`⨁_φ Lf_φ^*K_n`, where `CategoryTheory.Limits.biproduct.hom_ext'` applies: the summand inclusions
of a biproduct are jointly epic. Precomposing with the `φ`th inclusion replaces the left-hand side
by the `φ`th summand inclusion of the sum formula — which is the canonical leg, by
`…DerivedModuleSumFormulaSummand` — and the right-hand side by the `φ`th derived transition
followed by the `φ`th inclusion of the target, by `CategoryTheory.Limits.biproduct.ι_map`. So the
reduction consumes the summand description of the *source* formula only; the summand description of
the target is not needed to perform it, and is what the residual square would be attacked with.

*Why the reduction is split across four declarations.* Performing the summand reduction and the
transposition in one declaration exceeds the heartbeat budget: the rewrite by the summand
description and the rewrite by naturality of the derived transition each unfold a localization.
Each step is cheap on its own.

*Why the transposition step is in term mode.* After naturality of the derived transition of
Stacks 0D9P has been applied, the goal contains `(Lg_n^* ⋙ Lf_φ^*).map` of the canonical map, which
has to be read as `Lf_φ^*` of `Lg_n^*` of it. The two agree by a delta step that the elaborator
takes at default transparency but `rw` does not take when building its motive, so
`CategoryTheory.Functor.comp_map` fails there with a motive that is not type correct — the
hazard the implementation notes of `ModuleProjectionTargetSummand.lean` (in the same directory,
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/`) record for the same reason.
`CategoryTheory.Functor.map_comp` under a `congrArg` goes through.

*What the residual square is, and what it is blocked on.* The hypothesis `hadj` of
`…moduleProjection_restrict_of_adjunctSquare` says that the derived adjunct
`K_m ⟶ (g_{n!}O_n ⊗^L_O K)_m` of Stacks 0D9E (2) in degree `n`, carried along `Lf_φ^*` and followed
by the derived transition of Stacks 0D9P, is the `φ`th summand inclusion of the target
identification preceded by the derived transition at `K`. The summand inclusion on the right is
known explicitly — `…biproduct_ι_moduleProjectionTargetIso_inv_leg` expands it, granted the
sheaf-level leg equation `…ModuleSumFormulaLegEq`, into the component's left unitor, the canonical
leg of Stacks 0D72 (6) at the structure sheaf tensored into the restriction, and Stacks 03EL. Both
sides of the residual square are then derived functors of sheaf-level transformations, so the
square is the derived image of a square of sheaves of modules; and that sheaf-level square is the
module analogue of `…transitionInverseImageAb_map_componentSheafInclusion_comp_fiberTransitionAb'`,
which is what closes Stacks 0D9E (1) for abelian coefficients.

The sheaf-level square compares, on one side, `f_φ^*` of [the component's left unitor, the
adjunction unit `O_n ⟶ g_n^*g_{n!}O_n` tensored into `M_n`, and Stacks 03EL] followed by the
transition of Stacks 0D9P on the tensor product; and on the other side the transition on `M` alone
followed by the same chain built from the canonical leg instead of the unit. The leg *is* the unit
carried along `f_φ^*` and then the transition —
`…moduleSumFormulaLeg_app` is a definitional unfolding — so the two sides differ only by
whether the transition is applied to a tensor product or to its two factors separately.
Closing the square therefore needs the compatibility of the transition morphisms with the
comparison of Stacks 03EL: a monoidality statement for
`CategoryTheory.SimplicialSiteSituation.componentModuleTransition` against
`…componentRestrictionTensorIso`. No such statement exists in this development, and it is not among
the summand descriptions that this file consumes.

*The derived transport is not the obstruction.* Once the sheaf-level square is available, carrying
it to the derived level needs nothing new: `CategoryTheory.derivedNatTrans` is additive and
functorial for vertical composition (`CategoryTheory.derivedNatTrans_id`,
`CategoryTheory.derivedNatTrans_comp`), its interaction with whiskering is
`CategoryTheory.derivedCompIso_refl_hom_whiskerLeft` and
`CategoryTheory.derivedCompIso_refl_hom_whiskerRight`, and the derived transitions of Stacks 0D9P —
which are lifts along the localization of the homotopy category, hence `Classical.choice` — are
turned into `…derivedNatTrans`s by `CategoryTheory.liftedTransition_eq_derivedNatTrans`. So the
whole of the residual square is a sheaf-level statement in disguise, and the only missing
ingredient is the monoidality above.

The nearest statement the development does have is for ringed *spaces*, not ringed topoi:
`Stacks.PullbackTensorComposition.comparison_comp` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorAlongAComposite.lean`, the
compatibility of the comparison of Stacks 01CD with the composition law for pullback. The
module-of-a-ringed-topos comparison `Stacks.SheafOfModules.pullbackTensorIso` of Stacks 03EL
carries naturality in both module variables and no composition law at all.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The canonical map of Stacks 0D9E (2) transposes back to the adjunct it was built from.** The
unit of the derived adjunction `Lg_{n!} ⊣ Lg_n^*` at `K_n`, followed by the restriction to degree
`n` of `CategoryTheory.SimplicialSiteSituation.moduleProjection`, is
`CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunctDerived`.

The canonical map is the transpose of that adjunct along the derived adjunction, so this is the
transposition read back, `CategoryTheory.Adjunction.homEquiv_unit` followed by the inverse law of
the equivalence. -/
theorem unit_comp_derivedComponentModuleRestriction_map_moduleProjection
    (n : SimplexCategory)
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    (S.componentModuleLowerShriekDerivedAdjunction O n hflat).unit.app
          ((S.derivedComponentModuleRestriction O n).obj K) ≫
        (S.derivedComponentModuleRestriction O n).map (S.moduleProjection O n hflat K) =
      S.componentModuleProjectionAdjunctDerived O n K :=
  ((S.componentModuleLowerShriekDerivedAdjunction O n hflat).homEquiv_unit _ _
        (S.moduleProjection O n hflat K)).symm.trans
    (((S.componentModuleLowerShriekDerivedAdjunction O n hflat).homEquiv _ _).apply_symm_apply _)

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The canonical leg of Stacks 0D72 (6) at `K_n`, followed by the restriction to degree `m` of
the canonical map of Stacks 0D9E (2).** It is the derived adjunct
`CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunctDerived` carried along
`Lf_φ^*`, followed by the derived transition of Stacks 0D9P at the target `g_{n!}O_n ⊗^L_O K`.

The leg is the unit of `Lg_{n!} ⊣ Lg_n^*` carried along `Lf_φ^*` and then the derived transition,
so this is the naturality of the derived transition at the canonical map followed by
`…unit_comp_derivedComponentModuleRestriction_map_moduleProjection`.
It is the step that eliminates the canonical map from the summandwise comparison of
Stacks 0D9E (2), leaving only the adjunct. -/
theorem derivedTransitionPullback_map_unit_comp_derivedComponentModuleTransition_comp_map
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.derivedTransitionPullback O φ).map
          ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app
            ((S.derivedComponentModuleRestriction O n).obj K)) ≫
        (S.derivedComponentModuleTransition O φ).app
            ((S.componentModuleLowerShriekDerived O n (hflat n)).obj
              ((S.derivedComponentModuleRestriction O n).obj K)) ≫
          (S.derivedComponentModuleRestriction O m).map (S.moduleProjection O n (hflat n) K) =
      (S.derivedTransitionPullback O φ).map (S.componentModuleProjectionAdjunctDerived O n K) ≫
        (S.derivedComponentModuleTransition O φ).app _ := by
  refine Eq.trans (congrArg (fun k => (S.derivedTransitionPullback O φ).map
      ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app
        ((S.derivedComponentModuleRestriction O n).obj K)) ≫ k)
    ((S.derivedComponentModuleTransition O φ).naturality
      (S.moduleProjection O n (hflat n) K)).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun k => k ≫ (S.derivedComponentModuleTransition O φ).app _)
    ((((S.derivedTransitionPullback O φ).map_comp _ _).symm).trans
      (congrArg (S.derivedTransitionPullback O φ).map
        (S.unit_comp_derivedComponentModuleRestriction_map_moduleProjection O n (hflat n) K)))

/-- **The summandwise comparison `proj_restrict` of Stacks 0D9E (2) holds as soon as it holds on
each summand.** Granted the summand description
`CategoryTheory.SimplicialSiteSituation.DerivedModuleSumFormulaSummand` of the source direct-sum
formula, and granted that for every simplex map `φ : [n] ⟶ [m]` the canonical leg of Stacks 0D72
(6) followed by the restriction of the canonical map and the target identification is the `φ`th
derived transition followed by the `φ`th summand inclusion, the restriction to degree `m` of the
canonical map of Stacks 0D9E (2) is the direct sum of the derived transitions.

This is the reduction by components: both sides are maps out of `g_m^*g_{n!}K_n`, which the
direct-sum formula identifies with a biproduct, and the summand inclusions of a biproduct are
jointly epic. -/
theorem moduleProjection_restrict_of_componentSquare
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (hsq : ∀ (n m : SimplexCategory) (φ : n ⟶ m),
      (S.derivedTransitionPullback O φ).map
            ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app
              ((S.derivedComponentModuleRestriction O n).obj K)) ≫
          (S.derivedComponentModuleTransition O φ).app
              ((S.componentModuleLowerShriekDerived O n (hflat n)).obj
                ((S.derivedComponentModuleRestriction O n).obj K)) ≫
            (S.derivedComponentModuleRestriction O m).map (S.moduleProjection O n (hflat n) K) ≫
              (S.moduleProjectionTargetIso O n m K).hom =
        (S.derivedComponentModuleTransition O φ).app K ≫
          Limits.biproduct.ι
            (fun _ : n ⟶ m => (S.derivedComponentModuleRestriction O m).obj K) φ)
    (n m : SimplexCategory) :
    (S.derivedComponentModuleRestriction O m).map (S.moduleProjection O n (hflat n) K) ≫
        (S.moduleProjectionTargetIso O n m K).hom =
      (S.derivedModuleSumFormula O n m (hflat n)
          ((S.derivedComponentModuleRestriction O n).obj K)).hom ≫
        Limits.biproduct.map fun φ : n ⟶ m =>
          (S.derivedComponentModuleTransition O φ).app K := by
  refine (Iso.inv_comp_eq _).1 ?_
  refine Limits.biproduct.hom_ext' _ _ fun φ => ?_
  rw [Limits.biproduct.ι_map, ← Category.assoc, hsummand φ]
  exact Eq.trans (Category.assoc _ _ _) (hsq n m φ)

/-- **The residual square of Stacks 0D9E (2)**, as a property of a situation, a sheaf of rings and
an object `K` of `D(O)`: for every simplex map `φ : [n] ⟶ [m]`, the derived adjunct
`CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunctDerived` of the canonical
map, carried along `Lf_φ^*` and followed by the derived transition of Stacks 0D9P and by the
identification of the target with `⨁_φ K_m`, is the derived transition at `K` followed by the `φ`th
summand inclusion.

It carries no flatness hypothesis: the adjunct, the target identification and the derived
transitions are all available over an arbitrary sheaf of rings, and flatness enters Stacks 0D9E (2)
only through the derived adjunction that transposes the adjunct into the canonical map. Granted the
summand description of the source direct-sum formula, this is exactly what is left of the
summandwise comparison `proj_restrict`; the module docstring records what it is blocked on. -/
def ModuleProjectionAdjunctSquare (K : DerivedCategory (S.totalRingedTopos O).Modules) : Prop :=
  ∀ (n m : SimplexCategory) (φ : n ⟶ m),
    (S.derivedTransitionPullback O φ).map (S.componentModuleProjectionAdjunctDerived O n K) ≫
        (S.derivedComponentModuleTransition O φ).app _ ≫
          (S.moduleProjectionTargetIso O n m K).hom =
      (S.derivedComponentModuleTransition O φ).app K ≫
        Limits.biproduct.ι
          (fun _ : n ⟶ m => (S.derivedComponentModuleRestriction O m).obj K) φ

/-- **The summandwise comparison `proj_restrict` of Stacks 0D9E (2), reduced to one square at each
simplex map.** Granted the summand description of the source direct-sum formula, `proj_restrict`
follows from `CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare`.

Neither the canonical map `CategoryTheory.SimplicialSiteSituation.moduleProjection` nor the
direct-sum formula `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` occurs in that
hypothesis: the first has been transposed away and the second consumed by the reduction. What
remains is the module-coefficient analogue of the square that closes Stacks 0D9E (1) for abelian
coefficients. -/
theorem moduleProjection_restrict_of_adjunctSquare
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (hadj : S.ModuleProjectionAdjunctSquare O K)
    (n m : SimplexCategory) :
    (S.derivedComponentModuleRestriction O m).map (S.moduleProjection O n (hflat n) K) ≫
        (S.moduleProjectionTargetIso O n m K).hom =
      (S.derivedModuleSumFormula O n m (hflat n)
          ((S.derivedComponentModuleRestriction O n).obj K)).hom ≫
        Limits.biproduct.map fun φ : n ⟶ m =>
          (S.derivedComponentModuleTransition O φ).app K := by
  refine S.moduleProjection_restrict_of_componentSquare O hflat hsummand K
    (fun n m φ => ?_) n m
  refine Eq.trans (congrArg (fun k => (S.derivedTransitionPullback O φ).map
      ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app
        ((S.derivedComponentModuleRestriction O n).obj K)) ≫ k)
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ (S.moduleProjectionTargetIso O n m K).hom)
    (S.derivedTransitionPullback_map_unit_comp_derivedComponentModuleTransition_comp_map
      O hflat K φ)) ?_
  exact Eq.trans (Category.assoc _ _ _) (hadj n m φ)

/-- **Stacks 0D9E (2) with the summandwise comparison replaced by the residual square.** Under the
source's flatness hypothesis, granted the summand description of the componentwise direct-sum
formula of Stacks 0D72 (6) on derived categories and granted
`CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare`, an object `K` of `D(O)` is
cartesian exactly when the canonical map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism in every
simplicial degree.

This is `…isCartesianDerivedModule_iff_isIso_moduleProjection` with its hypothesis `proj_restrict`
supplied from the reduced square. The conclusion and the flatness hypothesis are unchanged; what
changes is which statement a consumer has to produce. -/
theorem isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (hadj : S.ModuleProjectionAdjunctSquare O K) :
    S.IsCartesianDerivedModule O K ↔
      ∀ n : SimplexCategory, IsIso (S.moduleProjection O n (hflat n) K) :=
  S.isCartesianDerivedModule_iff_isIso_moduleProjection O hflat K
    (S.moduleProjection_restrict_of_adjunctSquare O hflat hsummand K hadj)

/-- **The invertibility of the canonical projection map of Stacks 0D9E (2) in the spelling
Stacks 0D9R asks for.** The hypothesis `hproj` of
`CategoryTheory.SimplicialSiteSituation.eq_zero_of_derivedComponentModule_zero` is the
invertibility of `CategoryTheory.SimplicialSiteSituation.moduleProjection` in every degree `⦋i⦌`,
with the flatness of the structure-sheaf transitions spelled `fun _ φ => hflat φ` out of a
strict-implicit `hflat`; Stacks 0D9E (2) spells the same hypothesis `hflat n` out of a fully
explicit one. This delivers the former from cartesianness.

The two spellings are distinct terms and give syntactically distinct canonical maps, which is why
this crossing is a declaration rather than a step inside one: flatness is a proposition, so the
spellings are definitionally equal by proof irrelevance and the conversion is accepted by `exact`,
but instance synthesis unfolds only reducibly and will not find an `IsIso` instance for one
spelling from a hypothesis about the other. -/
theorem isIso_moduleProjection_of_isCartesianDerivedModule
    (hflat : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (hsummand : DerivedModuleSumFormulaSummand S O fun _ _ φ => hflat φ)
    (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (hadj : S.ModuleProjectionAdjunctSquare O K)
    (hK : S.IsCartesianDerivedModule O K) (i : ℕ) :
    IsIso (S.moduleProjection O ⦋i⦌ (fun _ φ => hflat φ) K) :=
  (S.isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare O
    (fun _ _ φ => hflat φ) hsummand K hadj).1 hK ⦋i⦌

end CategoryTheory.SimplicialSiteSituation

end

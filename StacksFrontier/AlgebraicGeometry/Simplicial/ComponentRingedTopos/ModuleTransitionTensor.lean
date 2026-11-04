module

public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionTargetSummand
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposTransition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# The transition of component modules against the comparison of Stacks 03EL

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. A simplex map `φ : [n] ⟶ [m]` carries the pullback transition
`CategoryTheory.SimplicialSiteSituation.componentModuleTransition` of Stacks 09WF,
`θ_φ : f_φ^*(ℱ_n) ⟶ ℱ_m`, comparing the restrictions of a sheaf of `O`-modules to the components
of degrees `n` and `m`; and each of the three morphisms of ringed topoi involved carries the
comparison of **Stacks 03EL**, `g_n^*(A ⊗_O B) ≅ A_n ⊗_{O_n} B_n` and its analogues at `g_m` and
at `f_φ`.

This file names the two halves of the compatibility of `θ_φ` with those three comparisons — the
*tensorator* half and the *unitor* half — and proves the one square they were isolated for: the
sheaf-level residual square of Stacks 0D9E (2). That square is what is left of the summandwise
comparison `proj_restrict` of
`CategoryTheory.SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection`
after the reduction of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleProjectionRestrict.lean`,
read at the level of sheaves of modules rather than of derived categories.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.TransitionTensorCoherence`: **the tensorator half** —
  the pullback transition of Stacks 09WF is compatible with the comparison of Stacks 03EL at the
  three morphisms of ringed topoi involved.
* `CategoryTheory.SimplicialSiteSituation.TransitionUnitorCoherence`: **the unitor half** — the
  comparison of Stacks 03EL at a transition morphism carries the inverse left unitor of the
  degree-`n` component to the inverse left unitor of the degree-`m` component, twisted by the
  identification `O_m ≅ f_φ^*O_n` of Stacks 03D6.

## Main results

* `…componentModuleUnitTensorUnit_app`: the map `- ⟶ (g_n^*g_{n!}O_n) ⊗_{O_n} -` of Stacks
  0D9E (2) at a sheaf of modules, as the inverse left unitor followed by the adjunction unit
  tensored in.
* `…transitionPullbackModules_map_componentRestrictionTensorIso_inv_comp`: the tensorator half
  with the comparison at `g_n` inverted, which is the direction the adjunct of Stacks 0D9E (2) is
  built in.
* `…transitionPullbackModules_map_componentModuleUnitTensorUnit_comp`: **the sheaf-level residual
  square of Stacks 0D9E (2)**, from the two halves, with both sides split into their factors.
* `…transitionPullbackModules_map_componentModuleProjectionAdjunct_comp`: the same square with
  its two sides spelled as the adjunct of Stacks 0D9E (2) and as the `φ`th summand inclusion of
  the target identification, which is the shape
  `CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare` asks for.

## Implementation notes

*What the square needs, and what it does not.* Both sides are built from an inverse left unitor, a
map into the degree-`m` restriction of `g_{n!}O_n` tensored into the restriction, and the inverse
comparison of Stacks 03EL; they differ only in whether the transition is applied to the tensor
product or to its two factors separately. Separating the two applications is exactly the
tensorator half, and the left unitors are then crossed by the unitor half. Everything between
them is available: naturality of the comparison of Stacks 03EL in its first variable is
`Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_fst`, the canonical leg of
Stacks 0D72 (6) is the adjunction unit carried along `f_φ^*` and then the transition by
definition (`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg_app`), and the two
remaining crossings are the naturality of the left unitor and of the tensor product in the module
variable. So the square is proved here from the two halves and nothing else.

*Why the two halves were isolated as hypotheses.* BOTH ARE NOW PROVED — the tensorator half as
`CategoryTheory.SimplicialSiteSituation.transitionTensorCoherence` of
`…/ModuleTransitionTensorCoherence.lean`, the unitor half as
`CategoryTheory.SimplicialSiteSituation.transitionUnitorCoherence` of
`…/ModuleTransitionUnitor.lean` — but they are kept as named propositions because the square
below is the only consumer of either, and because the route to the tensorator half is long enough
to be worth recording. When they were isolated neither was available, and the obstruction was
structural rather than a matter of further assembly. The tensorator half is the simplicial
instance of
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence`, and all six steps of
`Stacks.SheafOfModules.pullbackTensorHomEquiv` now do carry a composition law in the morphism of
ringed topoi — `Stacks.SheafOfModules.pullbackTensorStep1_comp'` through `…Step5_comp` and
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_eq_comp` — resting on the
identification `MorphismOfTopoi.inverseImageCompIso` of the inverse image of a composite with the
composite of the inverse images. What they do not reach is this statement, and the obstruction is
structural rather than a matter of further assembly. Every one of the six is a law at a *literal
composite* `ψ ∘ φ` of morphisms of ringed topoi and at the canonical comparisons attached to it,
so what they characterise is the comparison of Stacks 03EL at `g_n ∘ f_φ`; the comparison this
statement is about is the one at `g_m`, and `g_m` is not `g_n ∘ f_φ`. The two are compared by the
2-morphism `CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism` of Stacks 04IC,
which is not invertible — the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/AugmentationRingedTwoIso.lean`
record that it becomes invertible only after a ringed augmentation is appended, by Stacks
0D7H (1), and the transition of Stacks 09WF in its pullback presentation
(`CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`) is by definition the compositor
of pullbacks followed by that 2-morphism's
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap`. So what the six laws leave
owed here is a compatibility of `pullbackModulesMap` with the comparison of Stacks 03EL at two
*parallel* morphisms of ringed topoi, which is not an instance of
`PullbackTensorTransitionCoherence`.

THAT COMPATIBILITY IS NOW PROVED, unconditionally, as
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackTensorIso_hom_app_comp_pullbackModulesMap`
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorTwoMorphismMonoidal.lean`, the
2-morphism assumed neither invertible nor cartesian; the four-field form it comes from is
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_mate` of
`…/PullbackTensorMateMonoidal.lean`. It is carried into the shape this statement needs by
`Stacks.SheafOfModules.pullbackTensorTransitionCoherence_comp_pullbackModulesMap` of
`…/PullbackTensorTransitionTwoMorphism.lean`, which says the coherence is stable under twisting a
morphism by a 2-morphism. So the tensorator half reduces to the single case of the *literal*
composite `g_m ∘ f_φ`, with the compositor of Stacks 03D8 as the transition.

THAT CASE IS NOW PROVED TOO. The compositor of Stacks 03D8 is monoidal,
`Stacks.SheafOfModules.pullbackTensorTransitionCoherence_pullbackModulesCompAdjIso_inv` of
`…/PullbackTensorCompMonoidal.lean`, and the two compositors of Stacks 03D8 — the two-field
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`, which `moduleFiberTransition` uses,
and the four-field `Stacks.SheafOfModules.pullbackModulesCompAdjIso`, which the step laws use —
agree, by `Stacks.SheafOfModules.pullbackModulesCompAdjIso_eq` of
`…/PullbackModulesCompIsoAgreement.lean`. So the tensorator half **is** available in the pullback
presentation of restriction to a component:
`CategoryTheory.SimplicialSiteSituation.pullbackTensorTransitionCoherence_moduleFiberTransition`
of `…/ModuleTransitionTensorPullback.lean` is
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence` at `f_φ`, `g_n`, `g_m` and
`moduleFiberTransition`, unconditionally and for an arbitrary `O`.

AND SO IS THE CHANGE OF PRESENTATION, which is all that stood between the two.
`CategoryTheory.SimplicialSiteSituation.transitionTensorCoherence` of
`…/ModuleTransitionTensorCoherence.lean` INHABITS `TransitionTensorCoherence`, unconditionally and
for an arbitrary situation. For the transition the change of presentation is
`CategoryTheory.SimplicialSiteSituation.componentModuleTransition_app_eq_moduleFiberTransition`;
for the comparison of Stacks 03EL it is
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso_hom_app`, which takes
`componentRestrictionTensorIso` apart at a pair of modules; and the seam between the four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` the coherence is written at and
the two-field `AlgebraicGeometry.RingedToposHom.pullbackModules` the simplicial development is
written at is crossed one factor at a time there. The implementation notes of that file record the
measurements.

The second link that used to be
owed alongside it is not owed any more: `componentModuleTransition` is the transition in the
*literal restriction* presentation, and its identification with `moduleFiberTransition` is
`CategoryTheory.SimplicialSiteSituation.moduleFiberTransition_comp_restrictionIso`, which is now
unconditional. The unitor half is the mirror of
`Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`; that proposition itself is now
proved, by `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/PullbackToposRightUnitorCoherence.lean`, but the mirror here is not an
instance of it: it is the *left* unitor, and the comparison of Stacks 03EL is accompanied by no
compatibility with the braiding that would turn one into the other. See
`TransitionUnitorCoherence` below for what that leaves owed.

*Why the comparison at the transition is used unwrapped.* Stacks 03EL at `f_φ` is
`Stacks.SheafOfModules.pullbackTensorIso` at
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom`, used here directly rather than
transported into the uncurried-bifunctor spelling of
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso`. Unlike restriction to a
component, the transition pullback *is* the pullback of modules along a morphism of ringed topoi,
so no analogue of
`CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso` is needed; and
`Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_fst` is already stated at the curried
tensor product of Tag 06YM, which is the spelling the rest of the square is written at.

*Why the square is proved twice.* The proof needs both sides split into their factors, so that
each step rewrites the application of a single morphism; the consumer needs them folded back into
the adjunct of Stacks 0D9E (2) and the whiskered chain of
`…biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv_leg`. The folding is
`CategoryTheory.Functor.map_comp` and associativity, and is kept in its own declaration so that
no bookkeeping step sits between two mathematical ones.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent GrothendieckTopology.hasSheafify_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The tensorator half of the compatibility of the pullback transition of Stacks 09WF with the
comparison of Stacks 03EL**, as a property of a simplicial-site situation and a sheaf of rings on
its total site: for every simplex map `φ : [n] ⟶ [m]` and all sheaves of `O`-modules `A` and `B`,
the transition at `A ⊗_O B` followed by the comparison at `g_m` is the pullback along `f_φ` of the
comparison at `g_n`, followed by the comparison at `f_φ`, followed by the transition in each
tensor factor.

This is the simplicial instance of
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence`, at the three morphisms of ringed topoi
`f_φ`, `g_n` and `g_m` and at the transition of Stacks 09WF, written at the spellings of the
simplicial development — the tensor product in the curried form of Tag 06YM, and restriction to a
component in place of the pullback it is identified with by Stacks 0D72. It is inhabited,
unconditionally and for an arbitrary situation, by
`CategoryTheory.SimplicialSiteSituation.transitionTensorCoherence` of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/
ModuleTransitionTensorCoherence.lean`. -/
def TransitionTensorCoherence : Prop :=
  ∀ {n m : SimplexCategory} (φ : n ⟶ m) (A B : (S.totalRingedTopos O).Modules),
    (S.componentModuleTransition O φ).app
          ((Functor.uncurry.obj (sheafTensor (S.totalRingedTopos O).O)).obj (A, B)) ≫
        (S.componentRestrictionTensorIso O m).hom.app (A, B) =
      (S.transitionPullbackModules' O φ).map
          ((S.componentRestrictionTensorIso O n).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
              (S.transitionRingedToposHom O φ).toModulesHom).hom.app
            ((S.componentModulesRestriction O n).obj A,
              (S.componentModulesRestriction O n).obj B) ≫
          ((sheafTensor (S.componentRingedTopos O m).O).map
                ((S.componentModuleTransition O φ).app A)).app
              ((S.transitionPullbackModules' O φ).obj
                ((S.componentModulesRestriction O n).obj B)) ≫
            ((sheafTensor (S.componentRingedTopos O m).O).obj
                ((S.componentModulesRestriction O m).obj A)).map
              ((S.componentModuleTransition O φ).app B)

/-- **The unitor half of the compatibility of the pullback transition of Stacks 09WF with the
comparison of Stacks 03EL**, as a property of a simplicial-site situation and a sheaf of rings on
its total site: for every simplex map `φ : [n] ⟶ [m]` and every sheaf of `O_n`-modules `X`, the
pullback along `f_φ` of the inverse left unitor of the degree-`n` component, followed by the
comparison of Stacks 03EL at `f_φ`, is the inverse left unitor of the degree-`m` component
followed by the identification `O_m ≅ f_φ^*O_n` of Stacks 03D6 in the left tensor factor.

This is the unit half of the assertion that the comparison of Stacks 03EL at `f_φ` is monoidal.
It is the mirror of `Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`, and that
one is now proved —
`Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/PullbackToposRightUnitorCoherence.lean` — but this one is not an instance of
it; it is proved separately, as
`CategoryTheory.SimplicialSiteSituation.transitionUnitorCoherence` of
`…/ModuleTransitionUnitor.lean`. Two things stand between the two statements.  First, the *side*:
what is available is the
**right**-unitor coherence of Stacks 03EL, as
`Stacks.Sheaves.RingedToposModules.pullbackTensorIso_hom_app_comp_rightUnitor_unitComparison` for
an arbitrary morphism of ringed topoi, and the comparison of Stacks 03EL carries no compatibility
with the braiding, so the left unitor is a separate computation.  Second, the *unit comparison*:
the available coherence is stated at
`Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison`, the adjunct of `f♯` across
Stacks 03CZ, whose identification with the comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` of Stacks 03LU used here is proved
only when the morphism of topoi is presented by a morphism of sites
(`Stacks.Sheaves.DerivedPullback.pullbackModulesUnitComparison_eq`), because the value on the unit
section of the transpose of `pullbackModulesObjUnitIso.inv` is the direct image of a global
section and a bare `CategoryTheory.Sheaf.MorphismOfTopoi` describes no direct image on sections.
The transition morphism `CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom` is not
given by a `AlgebraicGeometry.RingedToposSiteHom`. -/
def TransitionUnitorCoherence : Prop :=
  ∀ {n m : SimplexCategory} (φ : n ⟶ m)
    (X : SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)),
    (S.transitionPullbackModules' O φ).map
          ((S.componentModuleUnitTensorLeftUnitor O n).inv.app X) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
            (S.transitionRingedToposHom O φ).toModulesHom).hom.app
          (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n), X) =
      (S.componentModuleUnitTensorLeftUnitor O m).inv.app
          ((S.transitionPullbackModules' O φ).obj X) ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map
              (pullbackModulesObjUnitIso
                (S.transitionRingedToposHom O φ).toModulesHom).hom).app
          ((S.transitionPullbackModules' O φ).obj X)

/-- **The map `- ⟶ (g_n^*g_{n!}O_n) ⊗_{O_n} -` of Stacks 0D9E (2) at a sheaf of modules.** It is
the inverse left unitor of the component followed by the unit of `g_{n!} ⊣ g_n^*` at the
structure sheaf of the component, tensored into the module. This holds by definition; the split
form is the one every step of the residual square acts on. -/
theorem componentModuleUnitTensorUnit_app (n : SimplexCategory)
    (X : (S.componentRingedTopos O n).Modules) :
    (S.componentModuleUnitTensorUnit O n).app X =
      (S.componentModuleUnitTensorLeftUnitor O n).inv.app X ≫
        ((sheafTensor (S.componentRingedTopos O n).O).map
            ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
              (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app X :=
  rfl

/-- **The tensorator half with the comparison at `g_n` inverted.** The pullback along `f_φ` of the
inverse comparison of Stacks 03EL at `g_n`, followed by the transition at `A ⊗_O B`, is the
comparison at `f_φ`, followed by the transition in each tensor factor, followed by the inverse
comparison at `g_m`.

This is the direction the adjunct of Stacks 0D9E (2) is built in: that adjunct ends with the
inverse comparison, so it is this form of the coherence that meets it. -/
theorem transitionPullbackModules_map_componentRestrictionTensorIso_inv_comp
    (htensor : S.TransitionTensorCoherence O) {n m : SimplexCategory} (φ : n ⟶ m)
    (A B : (S.totalRingedTopos O).Modules) :
    (S.transitionPullbackModules' O φ).map
          ((S.componentRestrictionTensorIso O n).inv.app (A, B)) ≫
        (S.componentModuleTransition O φ).app
          ((Functor.uncurry.obj (sheafTensor (S.totalRingedTopos O).O)).obj (A, B)) =
      (Stacks.SheafOfModules.pullbackTensorIso
            (S.transitionRingedToposHom O φ).toModulesHom).hom.app
          ((S.componentModulesRestriction O n).obj A,
            (S.componentModulesRestriction O n).obj B) ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map
              ((S.componentModuleTransition O φ).app A)).app
            ((S.transitionPullbackModules' O φ).obj
              ((S.componentModulesRestriction O n).obj B)) ≫
          ((sheafTensor (S.componentRingedTopos O m).O).obj
                ((S.componentModulesRestriction O m).obj A)).map
              ((S.componentModuleTransition O φ).app B) ≫
            (S.componentRestrictionTensorIso O m).inv.app (A, B) := by
  have e : (S.componentModuleTransition O φ).app
        ((Functor.uncurry.obj (sheafTensor (S.totalRingedTopos O).O)).obj (A, B)) =
      ((S.transitionPullbackModules' O φ).map
          ((S.componentRestrictionTensorIso O n).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
              (S.transitionRingedToposHom O φ).toModulesHom).hom.app
            ((S.componentModulesRestriction O n).obj A,
              (S.componentModulesRestriction O n).obj B) ≫
          ((sheafTensor (S.componentRingedTopos O m).O).map
                ((S.componentModuleTransition O φ).app A)).app
              ((S.transitionPullbackModules' O φ).obj
                ((S.componentModulesRestriction O n).obj B)) ≫
            ((sheafTensor (S.componentRingedTopos O m).O).obj
                ((S.componentModulesRestriction O m).obj A)).map
              ((S.componentModuleTransition O φ).app B)) ≫
        (S.componentRestrictionTensorIso O m).inv.app (A, B) :=
    Eq.trans (Eq.trans (Category.comp_id _).symm
        (congrArg (fun k => (S.componentModuleTransition O φ).app
            ((Functor.uncurry.obj (sheafTensor (S.totalRingedTopos O).O)).obj (A, B)) ≫ k)
          ((S.componentRestrictionTensorIso O m).hom_inv_id_app (A, B)).symm))
      (Eq.trans (Category.assoc _ _ _).symm
        (congrArg (fun k => k ≫ (S.componentRestrictionTensorIso O m).inv.app (A, B))
          (htensor φ A B)))
  refine Eq.trans (congrArg (fun k => (S.transitionPullbackModules' O φ).map
      ((S.componentRestrictionTensorIso O n).inv.app (A, B)) ≫ k) e) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫
    (S.componentRestrictionTensorIso O m).inv.app (A, B)) (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun k => (k ≫ _) ≫
      (S.componentRestrictionTensorIso O m).inv.app (A, B))
    (Eq.trans ((S.transitionPullbackModules' O φ).map_comp
        ((S.componentRestrictionTensorIso O n).inv.app (A, B))
        ((S.componentRestrictionTensorIso O n).hom.app (A, B))).symm
      (Eq.trans (congrArg (S.transitionPullbackModules' O φ).map
          ((S.componentRestrictionTensorIso O n).inv_hom_id_app (A, B)))
        ((S.transitionPullbackModules' O φ).map_id _)))) ?_
  refine Eq.trans (congrArg (fun k => k ≫
    (S.componentRestrictionTensorIso O m).inv.app (A, B)) (Category.id_comp _)) ?_
  exact Eq.trans (Category.assoc _ _ _)
    (congrArg (fun k => (Stacks.SheafOfModules.pullbackTensorIso
        (S.transitionRingedToposHom O φ).toModulesHom).hom.app
        ((S.componentModulesRestriction O n).obj A,
          (S.componentModulesRestriction O n).obj B) ≫ k) (Category.assoc _ _ _))

/-- **The rearrangement that finishes the sheaf-level residual square of Stacks 0D9E (2).** The
inverse left unitor at `f_φ^*M_n`, followed by the three morphisms tensored into it — the
identification `O_m ≅ f_φ^*O_n`, the adjunction unit carried along `f_φ^*`, and the transition at
`g_{n!}O_n` — then the transition at `M` in the right tensor factor and the inverse comparison of
Stacks 03EL at `g_m`, is the transition at `M` followed by the inverse left unitor at `M_m`, the
canonical leg of Stacks 0D72 (6) tensored into it, and the same inverse comparison.

The three morphisms are merged into the canonical leg by functoriality of the tensor product in
its left variable, and the transition at `M` is then crossed to the front by the naturality of the
tensor product and of the left unitor. This is a separate declaration because performing it inside
the square exceeds the heartbeat budget for one declaration: the degree-`m` module category has
three spellings here — through the component ringed topos, through the component ring sheaf, and
through the ring sheaf of the tensor product — and a rewriting step whose motive abstracts a
morphism between two of them has to unify their category instances, which `whnf` does not finish.
Written as its own statement, each spelling is crossed once. -/
theorem componentModuleUnitTensorLeftUnitor_inv_app_comp_rearrange
    {n m : SimplexCategory} (φ : n ⟶ m) (M : (S.totalRingedTopos O).Modules) :
        (S.componentModuleUnitTensorLeftUnitor O m).inv.app ((S.transitionPullbackModules' O φ).obj
        ((S.componentModulesRestriction O n).obj M)) ≫ (((sheafTensor (S.componentRingedTopos O
        m).O).map (pullbackModulesObjUnitIso (S.transitionRingedToposHom O
        φ).toModulesHom).hom).app ((S.transitionPullbackModules' O φ).obj
        ((S.componentModulesRestriction O n).obj M))) ≫ (((sheafTensor (S.componentRingedTopos O
        m).O).map ((S.transitionPullbackModules' O φ).map ((S.componentModuleLowerShriekAdjunction
        (S.totalRingSheaf O) n).unit.app (SheafOfModules.unit (S.componentRingSheaf
        (S.totalRingSheaf O) n))))).app ((S.transitionPullbackModules' O φ).obj
        ((S.componentModulesRestriction O n).obj M))) ≫ (((sheafTensor (S.componentRingedTopos O
        m).O).map ((S.componentModuleTransition O φ).app (S.componentModuleLowerShriekUnit O
        n))).app ((S.transitionPullbackModules' O φ).obj ((S.componentModulesRestriction O n).obj
        M))) ≫ (((sheafTensor (S.componentRingedTopos O m).O).obj ((S.componentModulesRestriction
        O m).obj (S.componentModuleLowerShriekUnit O n))).map ((S.componentModuleTransition O
        φ).app M)) ≫ ((S.componentRestrictionTensorIso O m).inv.app
        (S.componentModuleLowerShriekUnit O n, M)) =
            ((S.componentModuleTransition O φ).app M) ≫ (S.componentModuleUnitTensorLeftUnitor O
          m).inv.app ((S.componentModulesRestriction O m).obj M) ≫ (((sheafTensor
          (S.componentRingedTopos O m).O).map ((pullbackModulesObjUnitIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom ≫ ((S.transitionPullbackModules' O
          φ).map ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
          (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))) ≫
          ((S.componentModuleTransition O φ).app (S.componentModuleLowerShriekUnit O n)))).app
          ((S.componentModulesRestriction O m).obj M)) ≫ ((S.componentRestrictionTensorIso O
          m).inv.app (S.componentModuleLowerShriekUnit O n, M)) := by
  have hc : ∀ {X Y Z : (S.componentRingedTopos O m).Modules} (f : X ⟶ Y) (g : Y ⟶ Z) (W),
      ((sheafTensor (S.componentRingedTopos O m).O).map (f ≫ g)).app W =
        ((sheafTensor (S.componentRingedTopos O m).O).map f).app W ≫
          ((sheafTensor (S.componentRingedTopos O m).O).map g).app W :=
    fun f g W => by rw [Functor.map_comp]; rfl
  have key : ∀ {X0 Y1 Y2 Y3 P Q Z : (S.componentRingedTopos O m).Modules}
      (u : 𝟭 _ ⟶ (sheafTensor (S.componentRingedTopos O m).O).obj X0) (w1 : X0 ⟶ Y1)
      (w2 : Y1 ⟶ Y2) (w3 : Y2 ⟶ Y3) (g : P ⟶ Q)
      (z : ((sheafTensor (S.componentRingedTopos O m).O).obj Y3).obj Q ⟶ Z),
      u.app P ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map w1).app P ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map w2).app P ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map w3).app P ≫
        ((sheafTensor (S.componentRingedTopos O m).O).obj Y3).map g ≫ z =
      g ≫ u.app Q ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map (w1 ≫ w2 ≫ w3)).app Q ≫ z := by
    intro X0 Y1 Y2 Y3 P Q Z u w1 w2 w3 g z
    have h1 : ((sheafTensor (S.componentRingedTopos O m).O).obj X0).map g ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map (w1 ≫ w2 ≫ w3)).app Q =
        ((sheafTensor (S.componentRingedTopos O m).O).map (w1 ≫ w2 ≫ w3)).app P ≫
          ((sheafTensor (S.componentRingedTopos O m).O).obj Y3).map g :=
      ((sheafTensor (S.componentRingedTopos O m).O).map (w1 ≫ w2 ≫ w3)).naturality g
    have h2 : g ≫ u.app Q = u.app P ≫ ((sheafTensor (S.componentRingedTopos O m).O).obj X0).map g :=
      u.naturality g
    rw [reassoc_of% h2, reassoc_of% h1, hc, hc]
    simp only [Category.assoc]
  exact key _ _ _ _ _ _

/-- **The sheaf-level residual square of Stacks 0D9E (2)**, with both sides split into their
factors and the canonical leg of Stacks 0D72 (6) unfolded. For a simplex map `φ : [n] ⟶ [m]` and
a sheaf of `O`-modules `M`, the pullback along `f_φ` of the inverse left unitor, of the
adjunction unit tensored in, and of the inverse comparison of Stacks 03EL at `g_n`, followed by
the transition of Stacks 09WF at `g_{n!}O_n ⊗_O M`, is the transition at `M` followed by the
inverse left unitor of the degree-`m` component, the identification `O_m ≅ f_φ^*O_n` and the
canonical leg tensored into the restriction, and the inverse comparison of Stacks 03EL at `g_m`.

The proof separates the two applications of the transition by the tensorator half, crosses the
left unitors by the unitor half, and uses nothing else. The canonical leg is spelled out as the
adjunction unit carried along `f_φ^*` and then the transition — which is what it is, by
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg_app`. -/
theorem transitionPullbackModules_map_componentModuleUnitTensorUnit_comp
    (htensor : S.TransitionTensorCoherence O) (hunit : S.TransitionUnitorCoherence O)
    {n m : SimplexCategory} (φ : n ⟶ m) (M : (S.totalRingedTopos O).Modules) :
    (S.transitionPullbackModules' O φ).map
          ((S.componentModuleUnitTensorLeftUnitor O n).inv.app
            ((S.componentModulesRestriction O n).obj M)) ≫
        (S.transitionPullbackModules' O φ).map
                        (((sheafTensor (S.componentRingedTopos O n).O).map
                ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
                (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
                ((S.componentModulesRestriction O n).obj M)) ≫
          (S.transitionPullbackModules' O φ).map
              ((S.componentRestrictionTensorIso O n).inv.app
                (S.componentModuleLowerShriekUnit O n, M)) ≫
            (S.componentModuleTransition O φ).app
              ((S.componentModuleLowerShriekUnitTensor O n).obj M) =
            ((S.componentModuleTransition O φ).app M) ≫ (S.componentModuleUnitTensorLeftUnitor O
          m).inv.app ((S.componentModulesRestriction O m).obj M) ≫ ((sheafTensor
          (S.componentRingedTopos O m).O).map ((pullbackModulesObjUnitIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom ≫ ((S.transitionPullbackModules' O
          φ).map ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
          (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))) ≫
          ((S.componentModuleTransition O φ).app (S.componentModuleLowerShriekUnit O n)))).app
          ((S.componentModulesRestriction O m).obj M) ≫ ((S.componentRestrictionTensorIso O
          m).inv.app (S.componentModuleLowerShriekUnit O n, M)) := by
  -- Replace the last two factors by the tensorator half, inverted.
  refine Eq.trans (congrArg (fun k =>
      (S.transitionPullbackModules' O φ).map
          ((S.componentModuleUnitTensorLeftUnitor O n).inv.app
            ((S.componentModulesRestriction O n).obj M)) ≫
        (S.transitionPullbackModules' O φ).map
                        (((sheafTensor (S.componentRingedTopos O n).O).map
                ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
                (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
                ((S.componentModulesRestriction O n).obj M)) ≫ k)
    (S.transitionPullbackModules_map_componentRestrictionTensorIso_inv_comp O htensor φ
      (S.componentModuleLowerShriekUnit O n) M)) ?_
  -- Pull the comparison at `f_φ` next to the adjunction unit and apply its naturality.
  refine Eq.trans (congrArg (fun k =>
      (S.transitionPullbackModules' O φ).map
          ((S.componentModuleUnitTensorLeftUnitor O n).inv.app
            ((S.componentModulesRestriction O n).obj M)) ≫ k)
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun k =>
      (S.transitionPullbackModules' O φ).map
          ((S.componentModuleUnitTensorLeftUnitor O n).inv.app
            ((S.componentModulesRestriction O n).obj M)) ≫ k ≫ _)
    (Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_fst
            (S.transitionRingedToposHom O φ).toModulesHom ((S.componentModuleLowerShriekAdjunction
          (S.totalRingSheaf O) n).unit.app (SheafOfModules.unit (S.componentRingSheaf
          (S.totalRingSheaf O) n)))
      ((S.componentModulesRestriction O n).obj M))) ?_
  -- Pull the comparison next to the inverse left unitor and apply the unitor half.
  refine Eq.trans (congrArg (fun k =>
      (S.transitionPullbackModules' O φ).map
          ((S.componentModuleUnitTensorLeftUnitor O n).inv.app
            ((S.componentModulesRestriction O n).obj M)) ≫ k)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ _)
    (hunit φ ((S.componentModulesRestriction O n).obj M))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact S.componentModuleUnitTensorLeftUnitor_inv_app_comp_rearrange O φ M

/-- **The sheaf-level residual square of Stacks 0D9E (2).** The pullback along `f_φ` of the
adjunct `CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunct` of Stacks
0D9E (2) in degree `n`, followed by the transition of Stacks 09WF at `g_{n!}O_n ⊗_O M`, is the
transition at `M` followed by the `φ`th summand inclusion of the sheaf-level target
identification, in the form
`…biproduct_ι_componentModuleLowerShriekUnitTensorRestrictionSum_inv_leg` delivers it.

This is `…transitionPullbackModules_map_componentModuleUnitTensorUnit_comp` with both sides
folded back into the spellings a consumer uses; the folding is
`CategoryTheory.Functor.map_comp`, associativity, and the identification of the whiskered chain
with its components, each of which holds by definition. -/
theorem transitionPullbackModules_map_componentModuleProjectionAdjunct_comp
    (htensor : S.TransitionTensorCoherence O) (hunit : S.TransitionUnitorCoherence O)
    {n m : SimplexCategory} (φ : n ⟶ m) (M : (S.totalRingedTopos O).Modules) :
    (S.transitionPullbackModules' O φ).map
          ((S.componentModuleProjectionAdjunct O n).app M) ≫
        (S.componentModuleTransition O φ).app
          ((S.componentModuleLowerShriekUnitTensor O n).obj M) =
      (S.componentModuleTransition O φ).app M ≫
        (S.restrictionTensorWhiskeredUnitIso O m).inv.app M ≫
          ((S.restrictionTensorWhiskered O m).map
              ((pullbackModulesObjUnitIso
                    (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
                (S.moduleSumFormulaLeg O φ).app
                  (SheafOfModules.unit
                    (S.componentRingSheaf (S.totalRingSheaf O) n)))).app M ≫
            (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom.app M := by
  have h0 : (S.componentModuleProjectionAdjunct O n).app M =
      (((S.componentModuleUnitTensorLeftUnitor O n).inv.app ((S.componentModulesRestriction O
      n).obj M)) ≫ (((sheafTensor (S.componentRingedTopos O n).O).map
      ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
      (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
      ((S.componentModulesRestriction O n).obj M))) ≫ ((S.componentRestrictionTensorIso O
      n).inv.app (S.componentModuleLowerShriekUnit O n, M)) := rfl
  have hadj : (S.transitionPullbackModules' O φ).map ((S.componentModuleProjectionAdjunct O
      n).app M) =
            (S.transitionPullbackModules' O φ).map ((S.componentModuleUnitTensorLeftUnitor O
          n).inv.app ((S.componentModulesRestriction O n).obj M)) ≫ (S.transitionPullbackModules' O
          φ).map (((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
          (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
          ((S.componentModulesRestriction O n).obj M)) ≫ (S.transitionPullbackModules' O φ).map
          ((S.componentRestrictionTensorIso O n).inv.app (S.componentModuleLowerShriekUnit O n,
          M)) :=
    Eq.trans (congrArg (S.transitionPullbackModules' O φ).map h0)
            (Eq.trans ((S.transitionPullbackModules' O φ).map_comp
          (((S.componentModuleUnitTensorLeftUnitor O n).inv.app ((S.componentModulesRestriction O
          n).obj M)) ≫ (((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
          (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
          ((S.componentModulesRestriction O n).obj M))) ((S.componentRestrictionTensorIso O
          n).inv.app (S.componentModuleLowerShriekUnit O n, M)))
                (Eq.trans (congrArg (fun k => k ≫ (S.transitionPullbackModules' O φ).map
            ((S.componentRestrictionTensorIso O n).inv.app (S.componentModuleLowerShriekUnit O n,
            M))) ((S.transitionPullbackModules' O φ).map_comp
            ((S.componentModuleUnitTensorLeftUnitor O n).inv.app ((S.componentModulesRestriction O
            n).obj M)) (((sheafTensor (S.componentRingedTopos O n).O).map
            ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
            (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
            ((S.componentModulesRestriction O n).obj M))))
          (Category.assoc _ _ _)))
  exact Eq.trans (congrArg (fun k => k ≫ ((S.componentModuleTransition O φ).app
      ((S.componentModuleLowerShriekUnitTensor O n).obj M))) hadj)
    (Eq.trans (Category.assoc _ _ _)
            (Eq.trans (congrArg (fun k => (S.transitionPullbackModules' O φ).map
          ((S.componentModuleUnitTensorLeftUnitor O n).inv.app ((S.componentModulesRestriction O
          n).obj M)) ≫ k) (Category.assoc _ _ _))
        (S.transitionPullbackModules_map_componentModuleUnitTensorUnit_comp O
          htensor hunit φ M)))

end CategoryTheory.SimplicialSiteSituation

end

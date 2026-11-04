module

public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensorPullback

/-!
# The transition of Stacks 09WF is monoidal, in the literal-restriction presentation

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. This file proves
`CategoryTheory.SimplicialSiteSituation.TransitionTensorCoherence` — the tensorator half of the
compatibility of the transition of Stacks 09WF with the comparison of Stacks 03EL — which was the
last open input of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleTransitionTensor.lean`.

Nothing is assumed: `O` is arbitrary, the transition is not assumed invertible, no sheaf of
modules is assumed cartesian, and the statement is proved for an arbitrary
`CategoryTheory.SimplicialSiteSituation`, so it covers both cases (A) and (B) of Situation 09WE at
once.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition_comp_componentPullbackTensorIso`:
  the coherence of
  `CategoryTheory.SimplicialSiteSituation.pullbackTensorTransitionCoherence_moduleFiberTransition`,
  restated pointwise and entirely in the spellings of the simplicial development.
* `CategoryTheory.SimplicialSiteSituation.transitionTensorCoherence`: **the tensorator half**,
  i.e. `CategoryTheory.SimplicialSiteSituation.TransitionTensorCoherence`.

## Implementation notes

*What the mathematics is.* Both sides of `TransitionTensorCoherence` are rewritten by the two
changes of presentation that
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleTransitionTensorPullback.lean`
and `…/ComponentRestrictionTensor.lean` provide — the transition of Stacks 09WF in its pullback
presentation, and the comparison of Stacks 03EL at a component split into the identification of
Stacks 0D72 and Stacks 03EL at the component morphism of ringed topoi — and then meet at one
expression. Between them sit: the cancellation of the identification of Stacks 0D72 against itself
on the left; the coherence in the pullback presentation; the naturality of Stacks 03EL at the
transition morphism in both variables; the functoriality of the uncurried tensor bifunctor; and
the identification of the uncurried bifunctor with the curried one of Tag 06YM
(`Stacks.SheafOfModules.tensorSheafBifunctor_map_eq`). Nothing else.

*The one real obstacle, and what it actually was.* The coherence that is available,
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence`, is written throughout at the
four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` of a `ModulesHom`,
whereas the simplicial development is written at the two-field
`AlgebraicGeometry.RingedToposHom.pullbackModules`. The two pullback functors are the same term,
the second being the first at `toModulesHom`. Crossing that seam turned out to be cheap once two
things were fixed, and *neither* of them is the seam itself:

* Every occurrence of `pullbackModules` in a hand-written statement has to be given its two ringed
  topoi explicitly, as `pullbackModules (X := …) (Y := …) f`, and every `Functor.map` of the
  uncurried tensor bifunctor on a pair has to be given its source and target explicitly, as
  `.map (X := …) (Y := …) (a, b)`. Without them the elaborator leaves metavariables where the
  composite's objects should be and the unifier descends into the sheafification of the pullback;
  with them the four-field coherence applies to a written-out pointwise statement directly.
* The transition itself must be retyped at the four-field spelling before the coherence is
  restated at it. `…moduleFiberTransitionPullbackModules` below is that retyping — the same term,
  `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`, with both endpoints written out
  four-field — and it is the analogue, in the opposite direction, of
  `CategoryTheory.SimplicialSiteSituation.componentPullbackTensorIso`.

With those, the only genuinely expensive unification left is the one between
`componentPullbackTensorIso` and the `pullbackTensorIso` it is defined to be, *inside a composite
of four morphisms*. That one is crossed a single factor at a time, by `congrArg` against the
one-factor identity `…componentPullbackTensorIso_hom_app`, which is cheap. A `rw` cannot do it:
`rw` checks its motive at `instances` transparency and the identification of the two spellings
needs `default`.

*The other expensive unification, and how it is avoided.* The comparison of Stacks 03EL at a
component is stated against the *uncurried* tensor bifunctor of Tag 06YM
(`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O)`), while Stacks 03EL for a
morphism of ringed topoi is stated against
`AlgebraicGeometry.SheafOfModules.tensorSheafBifunctor`. The two agree on objects, but only at
`default` transparency and only after both sheafifications are unfolded, so identifying
`(A ⊗ B)` in the two spellings *on the total site* is the single most expensive defeq in this
file. It appears once, inside
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso_hom_app`, and the rule
followed here is that it must never be re-formed inside a `congrArg` motive. Concretely:
`…componentRestrictionTensorIso_hom_app_assoc` below rebrackets that comparison *before* anything
is applied to it, so that the subsequent `CategoryTheory.Functor.map_comp` splits a composite
whose bracketing already comes from a statement in which the identification was performed once.
Doing the rebracketing after `congrArg …pullbackModules.map` instead — which is the obvious order
— asks the unifier to identify two independently elaborated copies of the same junction and
exceeds the recursion limit.

## References

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

/-- **The transition of Stacks 09WF in the pullback presentation, retyped at the four-field
pullback functor.** This is `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`,
nothing more: the two-field `AlgebraicGeometry.RingedToposHom.pullbackModules` is *defined* as the
four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` at `toModulesHom`,
so the retyping is the identity on terms. It exists so that
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence` can be restated at a transition whose
type is spelled the way that proposition is. The module docstring records the measurements. -/
def moduleFiberTransitionPullbackModules {n m : SimplexCategory} (φ : n ⟶ m) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
          (componentRingedToposHom S O n).toModulesHom ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := S.componentRingedTopos O m) (Y := S.componentRingedTopos O n)
          (S.transitionRingedToposHom O φ).toModulesHom ⟶
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := S.componentRingedTopos O m) (Y := S.totalRingedTopos O)
        (componentRingedToposHom S O m).toModulesHom :=
  S.moduleFiberTransition O φ

/-- **The transition of Stacks 09WF is compatible with the comparison of Stacks 03EL**, at the
retyped transition. This is
`CategoryTheory.SimplicialSiteSituation.pullbackTensorTransitionCoherence_moduleFiberTransition`
with its transition written at the four-field pullback functor. -/
theorem pullbackTensorTransitionCoherence_moduleFiberTransitionPullbackModules
    {n m : SimplexCategory} (φ : n ⟶ m) :
    Stacks.SheafOfModules.PullbackTensorTransitionCoherence.{u, u, u, u, u, u, u, u, u}
      (S.transitionRingedToposHom O φ).toModulesHom
      (componentRingedToposHom S O n).toModulesHom
      (componentRingedToposHom S O m).toModulesHom
      (S.moduleFiberTransitionPullbackModules O φ) :=
  S.pullbackTensorTransitionCoherence_moduleFiberTransition O φ

/-- **The coherence of Stacks 03EL with the transition of Stacks 09WF, pointwise**, at the
four-field pullback functor: for sheaves of `O`-modules `A` and `B`, the transition at `A ⊗_O B`
followed by the comparison of Stacks 03EL at `g_m` is the pullback along `f_φ` of the comparison
at `g_n`, followed by the comparison at `f_φ`, followed by the transition in each tensor
factor. -/
theorem moduleFiberTransitionPullbackModules_comp_pullbackTensorIso_hom_app
    {n m : SimplexCategory} (φ : n ⟶ m)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) :
    (S.moduleFiberTransitionPullbackModules O φ).app
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O))).obj (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (componentRingedToposHom S O m).toModulesHom).hom.app (A, B) =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := S.componentRingedTopos O m) (Y := S.componentRingedTopos O n)
            (S.transitionRingedToposHom O φ).toModulesHom).map
          ((Stacks.SheafOfModules.pullbackTensorIso
            (componentRingedToposHom S O n).toModulesHom).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
              (S.transitionRingedToposHom O φ).toModulesHom).hom.app
            ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
                (componentRingedToposHom S O n).toModulesHom).obj A,
              (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
                (componentRingedToposHom S O n).toModulesHom).obj B) ≫
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
            (X := ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  (X := S.componentRingedTopos O m)
                  (Y := S.componentRingedTopos O n)
                  (S.transitionRingedToposHom O φ).toModulesHom).obj
                ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  (X := S.componentRingedTopos O n)
                  (Y := S.totalRingedTopos O)
                  (componentRingedToposHom S O n).toModulesHom).obj A),
              (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  (X := S.componentRingedTopos O m)
                  (Y := S.componentRingedTopos O n)
                  (S.transitionRingedToposHom O φ).toModulesHom).obj
                ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  (X := S.componentRingedTopos O n)
                  (Y := S.totalRingedTopos O)
                  (componentRingedToposHom S O n).toModulesHom).obj B)))
            (Y := ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  (X := S.componentRingedTopos O m)
                  (Y := S.totalRingedTopos O)
                  (componentRingedToposHom S O m).toModulesHom).obj A,
              (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
                  (X := S.componentRingedTopos O m)
                  (Y := S.totalRingedTopos O)
                  (componentRingedToposHom S O m).toModulesHom).obj B))
            ((S.moduleFiberTransitionPullbackModules O φ).app A,
              (S.moduleFiberTransitionPullbackModules O φ).app B) :=
  S.pullbackTensorTransitionCoherence_moduleFiberTransitionPullbackModules O φ A B

/-- **The same coherence with the pullback along the transition written two-field**, which is the
spelling the simplicial development uses. The comparison of Stacks 03EL is still the four-field
`Stacks.SheafOfModules.pullbackTensorIso`. -/
theorem moduleFiberTransition_comp_pullbackTensorIso_hom_app {n m : SimplexCategory} (φ : n ⟶ m)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) :
    (S.moduleFiberTransition O φ).app
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O))).obj (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (componentRingedToposHom S O m).toModulesHom).hom.app (A, B) =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((Stacks.SheafOfModules.pullbackTensorIso
            (componentRingedToposHom S O n).toModulesHom).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom.app
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
              (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B) ≫
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
            (X := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
              ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
              (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
                ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B)))
            (Y := ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
              (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B))
            ((S.moduleFiberTransition O φ).app A, (S.moduleFiberTransition O φ).app B) :=
  S.moduleFiberTransitionPullbackModules_comp_pullbackTensorIso_hom_app O φ A B

/-- **The pinned comparison of Stacks 03EL at a component is the comparison of Stacks 03EL**, at a
pair of sheaves of modules. `CategoryTheory.SimplicialSiteSituation.componentPullbackTensorIso` is
`Stacks.SheafOfModules.pullbackTensorIso` by definition; this records the identification at one
factor, which is where it is affordable. -/
theorem componentPullbackTensorIso_hom_app (n : SimplexCategory)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) :
    (componentPullbackTensorIso S O n).hom.app (A, B) =
      (Stacks.SheafOfModules.pullbackTensorIso
        (componentRingedToposHom S O n).toModulesHom).hom.app (A, B) := rfl

/-- **The coherence of Stacks 03EL with the transition of Stacks 09WF, pointwise and entirely in
the spellings of the simplicial development.** For sheaves of `O`-modules `A` and `B`, the
transition of Stacks 09WF in its pullback presentation at `A ⊗_O B`, followed by Stacks 03EL at
`g_m`, is the pullback along `f_φ` of Stacks 03EL at `g_n`, followed by Stacks 03EL at `f_φ`,
followed by the transition in each tensor factor.

This is
`CategoryTheory.SimplicialSiteSituation.pullbackTensorTransitionCoherence_moduleFiberTransition`,
crossed to this side of the four-field/two-field seam one factor at a time. -/
theorem moduleFiberTransition_comp_componentPullbackTensorIso {n m : SimplexCategory} (φ : n ⟶ m)
    (A B : (S.totalRingedTopos O).Modules) :
    (S.moduleFiberTransition O φ).app
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O))).obj (A, B)) ≫
        (componentPullbackTensorIso S O m).hom.app (A, B) =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
        ((componentPullbackTensorIso S O n).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom.app
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
              (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B) ≫
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B))) (Y :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B))
      ((S.moduleFiberTransition O φ).app A, (S.moduleFiberTransition O φ).app B) := by
  rw [S.componentPullbackTensorIso_hom_app O m A B, S.componentPullbackTensorIso_hom_app O n A B]
  exact S.moduleFiberTransition_comp_pullbackTensorIso_hom_app O φ A B

/-- **The transition of Stacks 09WF crosses the identification of Stacks 0D72.** The pullback
along `f_φ` of the identification at `M`, followed by the transition in the literal-restriction
presentation, is the transition in the pullback presentation followed by the identification. -/
theorem componentModuleTransition_app_comp_restrictionIso {n m : SimplexCategory} (φ : n ⟶ m)
    (M : (S.totalRingedTopos O).Modules) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
      ((componentPullbackModulesRestrictionIso S O n).hom.app M) ≫
        (S.componentModuleTransition O φ).app M =
      (S.moduleFiberTransition O φ).app M ≫
        (componentPullbackModulesRestrictionIso S O m).hom.app M :=
  (congrArg (fun k => (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
    ((componentPullbackModulesRestrictionIso S O n).hom.app M) ≫ k)
      (S.componentModuleTransition_app_eq_moduleFiberTransition O φ M)).trans
    (Iso.hom_inv_id_assoc ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapIso
      ((componentPullbackModulesRestrictionIso S O n).app M)) _)

/-- **Stacks 03EL at a transition morphism is natural in both tensor factors**, read off the
uncurried tensor bifunctor. -/
theorem pullbackTensorIso_hom_app_naturality {n m : SimplexCategory} (φ : n ⟶ m)
    {X₁ Y₁ X₂ Y₂ : (S.componentRingedTopos O n).Modules} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O))).map
              (X := (X₁, X₂)) (Y := (Y₁, Y₂)) (a, b)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom.app (Y₁, Y₂) =
      (Stacks.SheafOfModules.pullbackTensorIso
        (S.transitionRingedToposHom O φ).toModulesHom).hom.app (X₁, X₂) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
          (X := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj X₁,
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj X₂))
          (Y := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj Y₁,
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj Y₂))
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map a,
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map b) :=
  (Stacks.SheafOfModules.pullbackTensorIso
    (S.transitionRingedToposHom O φ).toModulesHom).hom.naturality (((a, b)) : (((X₁,
    X₂)) : _ × _) ⟶ (Y₁, Y₂))

/-- **Stacks 03EL at a transition morphism is natural in both tensor factors**, in the form that
meets a morphism appended on the right. This is
`…pullbackTensorIso_hom_app_naturality` reassociated; it is stated at a general appended morphism
`h` so that applying it needs no `congrArg` motive. -/
theorem pullbackTensorIso_hom_app_naturality_assoc {n m : SimplexCategory} (φ : n ⟶ m)
    {X₁ Y₁ X₂ Y₂ : (S.componentRingedTopos O n).Modules} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    {W : (S.componentRingedTopos O m).Modules}
    (h : ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).obj
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj Y₁,
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj Y₂) ⟶ W) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O))).map
              (X := (X₁, X₂)) (Y := (Y₁, Y₂)) (a, b)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom.app (Y₁, Y₂) ≫ h =
      (Stacks.SheafOfModules.pullbackTensorIso
        (S.transitionRingedToposHom O φ).toModulesHom).hom.app (X₁, X₂) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
            (X := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj X₁,
              (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj X₂))
            (Y := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj Y₁,
              (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj Y₂))
            ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map a,
              (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map b) ≫ h :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ h)
      (S.pullbackTensorIso_hom_app_naturality O φ a b)).trans (Category.assoc _ _ _))

/-- The uncurried tensor bifunctor on a component, on a composite pair of morphisms. -/
theorem tensorSheafBifunctor_map_comp_pair (m : SimplexCategory)
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : (S.componentRingedTopos O m).Modules}
    (x : X₁ ⟶ Y₁) (x' : Y₁ ⟶ Z₁) (y : X₂ ⟶ Y₂) (y' : Y₂ ⟶ Z₂) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
        (X := (X₁, X₂)) (Y := (Y₁, Y₂)) (x, y) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
            (X := (Y₁, Y₂)) (Y := (Z₁, Z₂)) (x', y') =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
          (X := (X₁, X₂)) (Y := (Z₁, Z₂)) (x ≫ x',
          y ≫ y') :=
  (((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map_comp _ _).symm

/-- The uncurried tensor bifunctor on a component, on a pair of morphisms, in the curried
spelling of Tag 06YM. This is `Stacks.SheafOfModules.tensorSheafBifunctor_map_eq`. -/
theorem tensorSheafBifunctor_map_pair_eq (m : SimplexCategory)
    {X₁ Y₁ X₂ Y₂ : (S.componentRingedTopos O m).Modules} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
        (X := (X₁, X₂)) (Y := (Y₁, Y₂)) (a, b) =
      ((sheafTensor (S.componentRingedTopos O m).O).map a).app X₂ ≫
        ((sheafTensor (S.componentRingedTopos O m).O).obj Y₁).map b :=
  Stacks.SheafOfModules.tensorSheafBifunctor_map_eq (S.componentRingedTopos O m).O a b

/-- **The transition in each tensor factor, in the curried spelling of Tag 06YM.** This is
`…tensorSheafBifunctor_map_pair_eq` at the transition of Stacks 09WF, with the source and target
of the uncurried bifunctor's action written out; the written-out form is what the proof of the
tensorator half substitutes, so that every later step speaks one spelling. -/
theorem componentModuleTransition_tensorSheafBifunctor_map_eq {n m : SimplexCategory} (φ : n ⟶ m)
    (A B : (S.totalRingedTopos O).Modules) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((S.componentModulesRestriction O n).obj A),
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((S.componentModulesRestriction O n).obj B))) (Y :=
          ((S.componentModulesRestriction O m).obj A, (S.componentModulesRestriction O m).obj B))
          ((S.componentModuleTransition O φ).app A, (S.componentModuleTransition O φ).app B) =
      ((sheafTensor (S.componentRingedTopos O m).O).map
            ((S.componentModuleTransition O φ).app A)).app
              ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
              ((S.componentModulesRestriction O n).obj B)) ≫
        ((sheafTensor (S.componentRingedTopos O m).O).obj
          ((S.componentModulesRestriction O m).obj A)).map
          ((S.componentModuleTransition O φ).app B) :=
  S.tensorSheafBifunctor_map_pair_eq O m ((S.componentModuleTransition O φ).app A)
    ((S.componentModuleTransition O φ).app B)

/-- **The comparison of Stacks 03EL at a component, with its first two factors bracketed.** This
is `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso_hom_app` rebracketed, and
it is rebracketed here rather than later because the junction between its first two factors
identifies the two spellings of `A ⊗_O B` on the total site; re-forming that junction inside a
`congrArg` motive exceeds the recursion limit. -/
theorem componentRestrictionTensorIso_hom_app_assoc (n : SimplexCategory)
    (A B : (S.totalRingedTopos O).Modules) :
    (S.componentRestrictionTensorIso O n).hom.app (A, B) =
      ((componentPullbackModulesRestrictionIso S O n).inv.app ((Functor.uncurry.obj (sheafTensor
        (S.totalRingedTopos O).O)).obj (A, B)) ≫ (componentPullbackTensorIso S O n).hom.app (A,
        B)) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O))).map (X :=
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B)) (Y :=
          ((S.componentModulesRestriction O n).obj A, (S.componentModulesRestriction O n).obj B))
          ((componentPullbackModulesRestrictionIso S O n).hom.app A,
            (componentPullbackModulesRestrictionIso S O n).hom.app B) :=
  (componentRestrictionTensorIso_hom_app S O n A B).trans (Category.assoc _ _ _).symm

/-- **The left-hand side of the tensorator half, with the transition and the comparison split.**
The transition at `A ⊗_O B` followed by the comparison of Stacks 03EL at `g_m` is the pullback
along `f_φ` of the identification of Stacks 0D72, the transition in the pullback presentation,
Stacks 03EL at `g_n` pinned, and the identification of Stacks 0D72 in each tensor factor; the two
copies of the identification at `A ⊗_O B` cancel. -/
theorem componentModuleTransition_comp_componentRestrictionTensorIso {n m : SimplexCategory}
    (φ : n ⟶ m) (A B : (S.totalRingedTopos O).Modules) :
    (S.componentModuleTransition O φ).app ((Functor.uncurry.obj (sheafTensor
      (S.totalRingedTopos O).O)).obj (A, B)) ≫
        (S.componentRestrictionTensorIso O m).hom.app (A, B) =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
        ((componentPullbackModulesRestrictionIso S O n).inv.app ((Functor.uncurry.obj (sheafTensor
        (S.totalRingedTopos O).O)).obj (A, B))) ≫
        (S.moduleFiberTransition O φ).app ((Functor.uncurry.obj (sheafTensor
          (S.totalRingedTopos O).O)).obj (A, B)) ≫
          (componentPullbackTensorIso S O m).hom.app (A, B) ≫
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B)) (Y :=
          ((S.componentModulesRestriction O m).obj A, (S.componentModulesRestriction O m).obj B))
      ((componentPullbackModulesRestrictionIso S O m).hom.app A,
        (componentPullbackModulesRestrictionIso S O m).hom.app B) := by
  rw [S.componentModuleTransition_app_eq_moduleFiberTransition,
    componentRestrictionTensorIso_hom_app]
  erw [Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

/-- **The left-hand side of the tensorator half reaches the common expression.** -/
theorem componentModuleTransition_comp_componentRestrictionTensorIso_eq {n m : SimplexCategory}
    (φ : n ⟶ m) (A B : (S.totalRingedTopos O).Modules) :
    (S.componentModuleTransition O φ).app ((Functor.uncurry.obj (sheafTensor
      (S.totalRingedTopos O).O)).obj (A, B)) ≫
        (S.componentRestrictionTensorIso O m).hom.app (A, B) =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
        ((componentPullbackModulesRestrictionIso S O n).inv.app ((Functor.uncurry.obj (sheafTensor
        (S.totalRingedTopos O).O)).obj (A, B)) ≫ (componentPullbackTensorIso S O n).hom.app (A,
        B)) ≫
      (Stacks.SheafOfModules.pullbackTensorIso
        (S.transitionRingedToposHom O φ).toModulesHom).hom.app
        ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
        (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B) ≫
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B))) (Y :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B))
      ((S.moduleFiberTransition O φ).app A, (S.moduleFiberTransition O φ).app B) ≫
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B)) (Y :=
          ((S.componentModulesRestriction O m).obj A, (S.componentModulesRestriction O m).obj B))
      ((componentPullbackModulesRestrictionIso S O m).hom.app A,
        (componentPullbackModulesRestrictionIso S O m).hom.app B) := by
  refine Eq.trans (S.componentModuleTransition_comp_componentRestrictionTensorIso O φ A B) ?_
  refine Eq.trans (congrArg
    (fun k => (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
    ((componentPullbackModulesRestrictionIso S O n).inv.app ((Functor.uncurry.obj (sheafTensor
    (S.totalRingedTopos O).O)).obj (A, B))) ≫ k)
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun k => k ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B)) (Y :=
          ((S.componentModulesRestriction O m).obj A, (S.componentModulesRestriction O m).obj B))
      ((componentPullbackModulesRestrictionIso S O m).hom.app A,
        (componentPullbackModulesRestrictionIso S O m).hom.app B))
          (S.moduleFiberTransition_comp_componentPullbackTensorIso O φ A B))
        (Eq.trans (Category.assoc _ _ _)
          (congrArg (fun k => (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
            ((componentPullbackTensorIso S O n).hom.app (A, B)) ≫ k)
            (Category.assoc _ _ _)))))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun k => k ≫
    _) ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map_comp _ _).symm

/-- **The two tensored transitions agree.** The identification of Stacks 0D72 in each tensor
factor, pulled back along `f_φ` and followed by the transition in the literal-restriction
presentation in each factor, is the transition in the pullback presentation in each factor
followed by the identification in each factor. -/
theorem componentModuleTransition_tensor_eq {n m : SimplexCategory} (φ : n ⟶ m)
    (A B : (S.totalRingedTopos O).Modules) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
          (X := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B)))
          (Y := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((S.componentModulesRestriction O n).obj A),
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((S.componentModulesRestriction O n).obj B)))
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
            ((componentPullbackModulesRestrictionIso S O n).hom.app A),
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
            ((componentPullbackModulesRestrictionIso S O n).hom.app B)) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((S.componentModulesRestriction O n).obj A),
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((S.componentModulesRestriction O n).obj B))) (Y :=
          ((S.componentModulesRestriction O m).obj A, (S.componentModulesRestriction O m).obj B))
      ((S.componentModuleTransition O φ).app A, (S.componentModuleTransition O φ).app B) =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B))) (Y :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B))
      ((S.moduleFiberTransition O φ).app A, (S.moduleFiberTransition O φ).app B) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B)) (Y :=
          ((S.componentModulesRestriction O m).obj A, (S.componentModulesRestriction O m).obj B))
      ((componentPullbackModulesRestrictionIso S O m).hom.app A,
        (componentPullbackModulesRestrictionIso S O m).hom.app B) := by
  refine Eq.trans (S.tensorSheafBifunctor_map_comp_pair O m _ _ _ _) ?_
  refine Eq.trans ?_ (S.tensorSheafBifunctor_map_comp_pair O m _ _ _ _).symm
  refine Eq.trans (congrArg (fun k =>
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
          (X := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B)))
          (Y := ((S.componentModulesRestriction O m).obj A,
            (S.componentModulesRestriction O m).obj B))
          (k,
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
              ((componentPullbackModulesRestrictionIso S O n).hom.app B) ≫
              (S.componentModuleTransition O φ).app B))
    (S.componentModuleTransition_app_comp_restrictionIso O φ A)) ?_
  exact congrArg (fun k =>
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map
          (X := ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
            ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B)))
          (Y := ((S.componentModulesRestriction O m).obj A,
            (S.componentModulesRestriction O m).obj B))
          ((S.moduleFiberTransition O φ).app A ≫
            (componentPullbackModulesRestrictionIso S O m).hom.app A, k))
    (S.componentModuleTransition_app_comp_restrictionIso O φ B)

/-- **The right-hand side of the tensorator half reaches the common expression**, with the
pullback along the transition written through the transition morphism of ringed topoi. -/
theorem transitionPullbackModules_map_componentRestrictionTensorIso_hom_eq
    {n m : SimplexCategory} (φ : n ⟶ m) (A B : (S.totalRingedTopos O).Modules) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
      ((S.componentRestrictionTensorIso O n).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom.app
          ((S.componentModulesRestriction O n).obj A, (S.componentModulesRestriction O n).obj B) ≫
          ((sheafTensor (S.componentRingedTopos O m).O).map
                ((S.componentModuleTransition O φ).app A)).app
                  ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
                  ((S.componentModulesRestriction O n).obj B)) ≫
            ((sheafTensor (S.componentRingedTopos O m).O).obj
              ((S.componentModulesRestriction O m).obj A)).map
              ((S.componentModuleTransition O φ).app B) =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
        ((componentPullbackModulesRestrictionIso S O n).inv.app ((Functor.uncurry.obj (sheafTensor
        (S.totalRingedTopos O).O)).obj (A, B)) ≫ (componentPullbackTensorIso S O n).hom.app (A,
        B)) ≫
      (Stacks.SheafOfModules.pullbackTensorIso
        (S.transitionRingedToposHom O φ).toModulesHom).hom.app
        ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
        (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B) ≫
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A),
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B))) (Y :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B))
      ((S.moduleFiberTransition O φ).app A, (S.moduleFiberTransition O φ).app B) ≫
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O))).map (X :=
          ((componentRingedToposHom S O m).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O m).toModulesHom.pullbackModules.obj B)) (Y :=
          ((S.componentModulesRestriction O m).obj A, (S.componentModulesRestriction O m).obj B))
      ((componentPullbackModulesRestrictionIso S O m).hom.app A,
        (componentPullbackModulesRestrictionIso S O m).hom.app B) := by
  have hsplit : (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
    ((S.componentRestrictionTensorIso O n).hom.app (A, B)) =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
        ((componentPullbackModulesRestrictionIso S O n).inv.app ((Functor.uncurry.obj (sheafTensor
        (S.totalRingedTopos O).O)).obj (A, B)) ≫ (componentPullbackTensorIso S O n).hom.app (A,
        B)) ≫
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
        (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O))).map (X :=
          ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
          (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B)) (Y :=
          ((S.componentModulesRestriction O n).obj A, (S.componentModulesRestriction O n).obj B))
      ((componentPullbackModulesRestrictionIso S O n).hom.app A,
        (componentPullbackModulesRestrictionIso S O n).hom.app B)) :=
    (congrArg (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
      (S.componentRestrictionTensorIso_hom_app_assoc O n A B)).trans
      ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map_comp _ _)
  refine Eq.trans (congrArg (fun k => _ ≫ _ ≫ k)
    (S.componentModuleTransition_tensorSheafBifunctor_map_eq O φ A B).symm) ?_
  refine Eq.trans (congrArg (fun k => k ≫ _) hsplit) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun k => _ ≫ k) ?_
  refine Eq.trans (S.pullbackTensorIso_hom_app_naturality_assoc O φ
    (X₁ := (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A)
    (Y₁ := (S.componentModulesRestriction O n).obj A)
    (X₂ := (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B)
    (Y₂ := (S.componentModulesRestriction O n).obj B)
    ((componentPullbackModulesRestrictionIso S O n).hom.app A)
    ((componentPullbackModulesRestrictionIso S O n).hom.app B) _) ?_
  exact congrArg (fun k => _ ≫ k) (S.componentModuleTransition_tensor_eq O φ A B)

/-- The right-hand side of the tensorator half, read through
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules` and through the pullback along
the transition morphism of ringed topoi, which are the same functor. -/
theorem transitionTensorCoherence_rhs_eq {n m : SimplexCategory} (φ : n ⟶ m)
    (A B : (S.totalRingedTopos O).Modules) :
    (S.transitionPullbackModules' O φ).map
          ((S.componentRestrictionTensorIso O n).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom.app
          ((S.componentModulesRestriction O n).obj A, (S.componentModulesRestriction O n).obj B) ≫
          ((sheafTensor (S.componentRingedTopos O m).O).map
                ((S.componentModuleTransition O φ).app A)).app
              ((S.transitionPullbackModules' O φ).obj ((S.componentModulesRestriction O n).obj B)) ≫
            ((sheafTensor (S.componentRingedTopos O m).O).obj
              ((S.componentModulesRestriction O m).obj A)).map
              ((S.componentModuleTransition O φ).app B) =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
        ((S.componentRestrictionTensorIso O n).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom.app
          ((S.componentModulesRestriction O n).obj A, (S.componentModulesRestriction O n).obj B) ≫
          ((sheafTensor (S.componentRingedTopos O m).O).map
                ((S.componentModuleTransition O φ).app A)).app
                  ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.obj
                  ((S.componentModulesRestriction O n).obj B)) ≫
            ((sheafTensor (S.componentRingedTopos O m).O).obj
              ((S.componentModulesRestriction O m).obj A)).map
              ((S.componentModuleTransition O φ).app B) := rfl

/-- **The tensorator half of the compatibility of the transition of Stacks 09WF with the
comparison of Stacks 03EL**, i.e.
`CategoryTheory.SimplicialSiteSituation.TransitionTensorCoherence`.

Nothing is assumed: `O` is an arbitrary sheaf of commutative rings on the total site, the
transition is not assumed invertible, no sheaf of modules is assumed cartesian, and `S` is an
arbitrary simplicial-site situation, so both cases (A) and (B) of Situation 09WE are covered. -/
theorem transitionTensorCoherence : S.TransitionTensorCoherence O := by
  intro n m φ A B
  exact (S.componentModuleTransition_comp_componentRestrictionTensorIso_eq O φ A B).trans
    (((S.transitionTensorCoherence_rhs_eq O φ A B).trans
      (S.transitionPullbackModules_map_componentRestrictionTensorIso_hom_eq O φ A B)).symm)

end CategoryTheory.SimplicialSiteSituation

end

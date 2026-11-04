module

public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTransitionComparison
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesCompIsoAgreement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCompMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorTransitionTwoMorphism

/-!
# The transition of Stacks 09WF is monoidal, in the pullback presentation

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site and `φ : [n] ⟶ [m]` a simplex map. The transition of Stacks 09WF comparing the
restrictions of a sheaf of `O`-modules to the components of degrees `n` and `m` has two
presentations, and in the **pullback** one it is
`CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`, a transformation
`g_n^* ⋙ f_φ^* ⟶ g_m^*` of pullbacks of sheaves of modules along morphisms of ringed topoi.

This file proves that this transformation is compatible with the comparison of **Stacks 03EL** at
the three morphisms of ringed topoi involved — that is, that it satisfies
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence`. Nothing is assumed: the sheaf of rings
`O` is arbitrary, the transition is not assumed invertible, and no cartesianness is used.

## Main results

* `CategoryTheory.SimplicialSiteSituation.pullbackTensorTransitionCoherence_moduleFiberTransition`:
  **the transition of Stacks 09WF is compatible with the comparison of Stacks 03EL**, in the
  pullback presentation of restriction to a component.
* `CategoryTheory.SimplicialSiteSituation.componentModuleTransition_app_eq_moduleFiberTransition`:
  the transition in the literal-restriction presentation is the pullback transition conjugated by
  the identification of Stacks 0D72, read at a sheaf of modules.

## Implementation notes

*How the coherence is obtained.* Two unconditional inputs meet here. The compositor of
Stacks 03D8 is monoidal,
`Stacks.SheafOfModules.pullbackTensorTransitionCoherence_pullbackModulesCompAdjIso_inv`, which is
the coherence at the **literal composite** `g_n ∘ f_φ` with the inverse compositor as transition;
and the coherence is stable under twisting a morphism of ringed topoi by a 2-morphism of
Stacks 04IC, `Stacks.SheafOfModules.pullbackTensorTransitionCoherence_comp_pullbackModulesMap`.
The 2-morphism to twist by is
`CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism`, `g_m ⟶ g_n ∘ f_φ`, and
`moduleFiberTransition` is by definition the inverse compositor followed by its
`pullbackModulesMap`. The one link between the two inputs is that the compositor the monoidality
is stated at — the four-field `Stacks.SheafOfModules.pullbackModulesCompAdjIso` — and the one
`moduleFiberTransition` is built from — the two-field
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` — agree, which is
`Stacks.SheafOfModules.pullbackModulesCompAdjIso_inv`.

*Why the substitution of that link is a `congrArg` on the proposition and not a rewrite.* The two
compositors have the same type, but their common type is a `Hom` in a category of natural
transformations whose two spellings of the category of sheaves of modules on the total ringed
topos — through `Stacks.ringSheaf` and through
`Stacks.Sheaves.RingedToposModules.structureRingSheaf` — are equal only definitionally. A `rw` by
`pullbackModulesCompAdjIso_inv` inside
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence` fails to find its own pattern for that
reason. Substituting instead into the proposition, by `congrArg` at the explicit motive
`PullbackTensorTransitionCoherence f_φ g_n g_m`, never forms a motive over the `Hom` type and
goes through.

*What this does not give directly, and how that gap was closed.* The last open input of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleTransitionTensor.lean` is
`CategoryTheory.SimplicialSiteSituation.TransitionTensorCoherence`, which is this coherence
written in the **literal-restriction** presentation: the transition is
`componentModuleTransition` and the comparison of Stacks 03EL at `g_n` and at `g_m` is
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso`. For the transition the
change of presentation is `componentModuleTransition_app_eq_moduleFiberTransition` below; for the
comparison it is
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso_hom_app`, which takes
`componentRestrictionTensorIso` apart at a pair of sheaves of modules into the identification of
Stacks 0D72 at `A ⊗_O B`, Stacks 03EL at `g_n`, and the identification of Stacks 0D72 in each
tensor factor. That decomposition used to be unavailable, and is now available: it needed the
third factor of the chain pinned to one spelling of the pullback functor, which is what
`CategoryTheory.SimplicialSiteSituation.componentPullbackTensorIso` is for; the implementation
notes of `…/ComponentRestrictionTensor.lean` record the measurements.

*The seam that stood in the way, and what it actually was.* Both halves of the change of
presentation are in hand, and so are the pieces they meet: the identification of Stacks 0D72
cancels against the transition on either side, the naturality of Stacks 03EL at `f_φ` in both
variables is `(pullbackTensorIso _).hom.naturality` at a pair, and the curried pair of tensorings
on the right-hand side of `TransitionTensorCoherence` is
`Stacks.SheafOfModules.tensorSheafBifunctor_map_eq`. What stood in the way was that the coherence
proved here is `Stacks.SheafOfModules.PullbackTensorTransitionCoherence`, written throughout at
the *four-field* `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` of a
`ModulesHom`, whereas the simplicial development — `moduleFiberTransition`,
`componentPullbackModulesRestrictionIso`, `transitionPullbackModules'` — is written at the
two-field `AlgebraicGeometry.RingedToposHom.pullbackModules`. It is crossed in
`…/ModuleTransitionTensorCoherence.lean`, and the four-field-versus-two-field difference turned
out *not* to be the expensive part of it: what is expensive is identifying the two spellings of
`A ⊗_O B` on the total site — `Functor.uncurry.obj (…sheafTensor O)` against
`AlgebraicGeometry.SheafOfModules.tensorSheafBifunctor` — which agree only after both
sheafifications are unfolded. The measurements are recorded in the implementation notes of that
file; what this file supplies is the input, and
`CategoryTheory.SimplicialSiteSituation.transitionTensorCoherence` is the result.

## References

* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
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

/-- **The transition of Stacks 09WF is compatible with the comparison of Stacks 03EL**, in the
pullback presentation of restriction to a simplicial component.

For a simplex map `φ : [n] ⟶ [m]` and sheaves of `O`-modules `A` and `B`, the transition
`g_n^*(A ⊗_O B) ⟶ g_m^*(A ⊗_O B)` of Stacks 09WF followed by the comparison of Stacks 03EL at
`g_m` is the pullback along `f_φ` of the comparison at `g_n`, followed by the comparison at
`f_φ`, followed by the transition in each tensor factor. This is
`Stacks.SheafOfModules.PullbackTensorTransitionCoherence` at the three morphisms of ringed topoi
`f_φ`, `g_n`, `g_m` and at `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`.

Nothing is assumed: `O` is an arbitrary sheaf of commutative rings on the total site, the
transition is not assumed invertible, and no sheaf of modules is assumed cartesian. The proof
composes the monoidality of the compositor of Stacks 03D8 at the literal composite `g_n ∘ f_φ`
with the stability of the coherence under twisting by the 2-morphism `g_m ⟶ g_n ∘ f_φ` of
Stacks 04IC, the two compositors of Stacks 03D8 being identified by
`Stacks.SheafOfModules.pullbackModulesCompAdjIso_inv`. -/
theorem pullbackTensorTransitionCoherence_moduleFiberTransition
    {n m : SimplexCategory} (φ : n ⟶ m) :
    Stacks.SheafOfModules.PullbackTensorTransitionCoherence.{u, u, u, u, u, u, u, u, u}
      (S.transitionRingedToposHom O φ).toModulesHom
      (componentRingedToposHom S O n).toModulesHom
      (componentRingedToposHom S O m).toModulesHom
      (S.moduleFiberTransition O φ) := by
  have hfun : S.moduleFiberTransition O φ =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
          (S.transitionRingedToposHom O φ) (componentRingedToposHom S O n)).inv ≫
        (S.componentRingedTwoMorphism O φ).pullbackModulesMap := rfl
  have h : (Stacks.SheafOfModules.pullbackModulesCompAdjIso
          (S.transitionRingedToposHom O φ) (componentRingedToposHom S O n)).inv ≫
        (S.componentRingedTwoMorphism O φ).pullbackModulesMap =
      S.moduleFiberTransition O φ :=
    (congrArg (fun α => α ≫ (S.componentRingedTwoMorphism O φ).pullbackModulesMap)
      (Stacks.SheafOfModules.pullbackModulesCompAdjIso_inv
        (S.transitionRingedToposHom O φ) (componentRingedToposHom S O n))).trans hfun.symm
  exact (congrArg (Stacks.SheafOfModules.PullbackTensorTransitionCoherence
      (S.transitionRingedToposHom O φ).toModulesHom
      (componentRingedToposHom S O n).toModulesHom
      (componentRingedToposHom S O m).toModulesHom) h).mp
    (Stacks.SheafOfModules.pullbackTensorTransitionCoherence_comp_pullbackModulesMap
      (S.transitionRingedToposHom O φ).toModulesHom
      (componentRingedToposHom S O n).toModulesHom
      (S.componentRingedTwoMorphism O φ) _
      (Stacks.SheafOfModules.pullbackTensorTransitionCoherence_pullbackModulesCompAdjIso_inv
        (S.transitionRingedToposHom O φ) (componentRingedToposHom S O n)))

/-- **The transition of Stacks 09WF in the literal-restriction presentation is the pullback
transition conjugated by the identification of Stacks 0D72**, read at a sheaf of modules: for a
simplex map `φ : [n] ⟶ [m]` and a sheaf of `O`-modules `M`, the map `f_φ^*(M_n) ⟶ M_m` between
the literal restrictions is the identification of `M_n` with `g_n^*M` pulled back along `f_φ`,
then `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`, then the identification of
`g_m^*M` with `M_m`.

This is the change of presentation that
`CategoryTheory.SimplicialSiteSituation.TransitionTensorCoherence` needs for the transition. It
is `CategoryTheory.SimplicialSiteSituation.componentModuleTransition_app` followed by
`CategoryTheory.SimplicialSiteSituation.moduleFiberTransition_comp_restrictionIso`, both of which
are unconditional. -/
theorem componentModuleTransition_app_eq_moduleFiberTransition {n m : SimplexCategory}
    (φ : n ⟶ m) (M : (S.totalRingedTopos O).Modules) :
    (S.componentModuleTransition O φ).app M =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((componentPullbackModulesRestrictionIso S O n).inv.app M) ≫
        (S.moduleFiberTransition O φ).app M ≫
          (componentPullbackModulesRestrictionIso S O m).hom.app M :=
  (S.componentModuleTransition_app O φ M).trans
    (S.moduleFiberTransition_comp_restrictionIso O φ M).symm

end CategoryTheory.SimplicialSiteSituation

end

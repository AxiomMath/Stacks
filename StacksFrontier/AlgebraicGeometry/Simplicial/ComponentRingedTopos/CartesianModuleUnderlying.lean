module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModule
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposTwoMorphismUnderlying
import StacksCore.Tactic.StacksAttribute

/-!
# The underlying sheaf of sets of a cartesian sheaf of modules

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site
which is itself cartesian, i.e. whose underlying sheaf of sets satisfies Stacks 07TF (1). This
file shows that a sheaf of `O`-modules whose module transitions `f_φ^*F_m ⟶ F_n` are invertible
has a cartesian underlying sheaf of sets.

Cartesianness of `O` is not a technical convenience: without it the statement is false. The
module transition of `F = O` is an isomorphism for every `O`, since it extends scalars along
itself, while the transition of the underlying sheaf of sets of `O` is the structure-sheaf
transition, invertible exactly when `O` is cartesian.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isIso_transitionRingedToposHom_fSharpInverseImage`:
  for a cartesian `O`, the structure map of the transition morphism of ringed topoi attached to a
  simplex map is invertible.
* `CategoryTheory.SimplicialSiteSituation`
  `.isIso_fiberTransition_of_isIso_componentInverseImageTransition`: invertibility passes from the
  inverse-image transition read through the component morphisms of topoi to the transition of
  Stacks 09WF itself.
* `CategoryTheory.SimplicialSiteSituation.isIso_componentInverseImageTransition_moduleSheaf`: the
  inverse-image transition of sheaves of sets, evaluated at the underlying sheaf of a sheaf of
  modules with invertible module transitions, is invertible.
* `CategoryTheory.SimplicialSiteSituation.isCartesianSheaf_moduleSheaf`: **the statement.** The
  underlying sheaf of sets of such a sheaf of modules is cartesian in the sense of
  Stacks 07TF (1).

## The argument

The module transition `moduleFiberTransition` is, up to the compositor of Stacks 03D8, the mate
of the 2-morphism `g_n ⟶ g_m ∘ f_φ` of ringed topoi on pullbacks of sheaves of modules; the
transition `componentInverseImageTransition` of sheaves of sets is the mate of the same
2-morphism on inverse images of sheaves of sets. That the first has the second underneath is
`AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pullbackModulesMap_app`,
which asks the structure maps of the two morphisms of ringed topoi to be invertible: for `g_n`
that is `CategoryTheory.SimplicialSiteSituation.isIso_componentRingedToposHom_fSharpInverseImage`
and for the composite `g_m ∘ f_φ` it is where cartesianness of `O` enters.

Passing from `componentInverseImageTransition` to the transition `fiberTransition` of
Stacks 09WF that the cartesian condition for sheaves of sets is stated with is
`CategoryTheory.SimplicialSiteSituation.componentInverseImageTransition_comp_hom`: the two differ
by the comparisons of Stacks 09WG, which are isomorphisms.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The structure map of the transition morphism of ringed topoi of a cartesian `O` is
invertible.** It is the structure-sheaf transition of
`CategoryTheory.SimplicialSiteSituation.fiberTransitionCommRing`, whose underlying morphism of
sheaves of sets is the transition of Stacks 09WF at the underlying sheaf of sets of `O`; that is
invertible by hypothesis, and forgetting the ring operations reflects isomorphisms. -/
theorem isIso_transitionRingedToposHom_fSharpInverseImage
    (hO : S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (S.transitionRingedToposHom O φ).fSharpInverseImage := by
  have h : IsIso ((sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
      (S.fiberTransitionCommRing O φ)) := by
    rw [S.fiberTransitionCommRing_forget O φ]
    exact hO φ
  rw [S.transitionRingedToposHom_fSharpInverseImage O φ]
  exact isIso_of_reflects_iso (S.fiberTransitionCommRing O φ)
    (sheafCompose (S.componentTopology n) (forget CommRingCat.{u}))

/-- **Invertibility passes from the inverse-image transition to the transition of Stacks 09WF.**
The two differ by the comparisons of Stacks 09WG between inverse image along a component morphism
of topoi and restriction along the component inclusion, which are isomorphisms:
`CategoryTheory.SimplicialSiteSituation.componentInverseImageTransition_comp_hom`. -/
theorem isIso_fiberTransition_of_isIso_componentInverseImageTransition
    {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf S.totalTopology (Type u))
    (h : IsIso ((S.componentInverseImageTransition φ).app G)) :
    IsIso ((S.fiberTransition φ).app G) := by
  have e : (S.fiberTransition φ).app G =
      (((S.transitionMorphism φ).inverseImage.mapIso
            ((S.componentRingedTopos_setRestrictionIso m).app G)).symm ≪≫
        (@asIso _ _ _ _ _ h ≪≫ (S.componentRingedTopos_setRestrictionIso n).app G)).hom :=
    ((congrArg (((S.transitionMorphism φ).inverseImage.mapIso
              ((S.componentRingedTopos_setRestrictionIso m).app G)).inv ≫ ·)
          (S.componentInverseImageTransition_comp_hom φ G)).trans
        (Iso.inv_hom_id_assoc ((S.transitionMorphism φ).inverseImage.mapIso
          ((S.componentRingedTopos_setRestrictionIso m).app G))
          ((S.fiberTransition φ).app G))).symm
  rw [e]
  exact Iso.isIso_hom _

section Modules

attribute [local instance]
  hasWeakSheafifyComponent hasSheafifyTotal wEqualsLocallyBijectiveComponent
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- **The inverse-image transition of sheaves of sets is invertible at the underlying sheaf of a
sheaf of modules with invertible module transitions**, over a cartesian `O`.

The module transition is the compositor of Stacks 03D8 followed by the mate of the 2-morphism
`g_n ⟶ g_m ∘ f_φ` on pullbacks of sheaves of modules, so the mate is invertible; the mate on
inverse images of sheaves of sets is its underlying morphism by
`AlgebraicGeometry.RingedToposHom.TwoMorphism.isIso_conjugateEquiv_symm_app`, and it is
`componentInverseImageTransition` because
`CategoryTheory.SimplicialSiteSituation.componentPushforwardTransition` is its conjugate. -/
theorem isIso_componentInverseImageTransition_moduleSheaf
    (hO : S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))}
    (hF : S.IsModuleFiberTransitionIso O F) {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso ((S.componentInverseImageTransition φ).app
      ((Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))).obj F)) := by
  have := S.isIso_transitionRingedToposHom_fSharpInverseImage O hO φ
  have hmate : IsIso ((S.componentRingedTwoMorphism O φ).pullbackModulesMap.app F) := by
    have h0 : IsIso ((S.moduleFiberTransition O φ).app F) := hF φ
    have hfun : S.moduleFiberTransition O φ =
        (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
            (componentRingedToposHom S O m)).inv ≫
          (S.componentRingedTwoMorphism O φ).pullbackModulesMap := rfl
    have happ : (S.moduleFiberTransition O φ).app F =
        (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
            (componentRingedToposHom S O m)).inv.app F ≫
          (S.componentRingedTwoMorphism O φ).pullbackModulesMap.app F :=
      (congrArg (fun α ↦ NatTrans.app α F) hfun).trans (NatTrans.comp_app _ _ F)
    rw [happ] at h0
    have : IsIso ((RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
        (componentRingedToposHom S O m)).inv.app F) :=
      ((RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
        (componentRingedToposHom S O m)).app F).isIso_inv
    exact IsIso.of_isIso_comp_left ((RingedToposHom.pullbackModulesCompIso
      (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)).inv.app F) _
  have hconj : ((conjugateEquiv (componentRingedToposHom S O n).toToposHom.adj
          (RingedToposHom.comp (X := S.componentRingedTopos O n)
            (Y := S.componentRingedTopos O m) (Z := S.totalRingedTopos O)
            (componentRingedToposHom S O m)
            (S.transitionRingedToposHom O φ)).toToposHom.adj).symm
        (S.componentRingedTwoMorphism O φ).t) =
      S.componentInverseImageTransition φ :=
    (conjugateEquiv (componentMorphism S n).adj
      ((componentMorphism S m).comp (S.transitionMorphism φ)).adj).symm_apply_apply _
  have h := (S.componentRingedTwoMorphism O φ).isIso_conjugateEquiv_symm_app F
  rw [hconj] at h
  exact h

/-- **The underlying sheaf of sets of a sheaf of modules with invertible module transitions is
cartesian**, over a cartesian sheaf of rings `O`. This is Stacks 07TF (1) for that sheaf of sets,
deduced from Stacks 07TF (2) for the sheaf of modules.

The inverse-image transition of sheaves of sets is invertible there by
`isIso_componentInverseImageTransition_moduleSheaf`, and that carries over to the transition of
Stacks 09WF by `isIso_fiberTransition_of_isIso_componentInverseImageTransition`. -/
theorem isCartesianSheaf_moduleSheaf
    (hO : S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))}
    (hF : S.IsModuleFiberTransitionIso O F) :
    S.IsCartesianSheaf
      ((Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))).obj F) := by
  intro m n φ
  exact S.isIso_fiberTransition_of_isIso_componentInverseImageTransition φ _
    (S.isIso_componentInverseImageTransition_moduleSheaf O hO hF φ)

end Modules

end CategoryTheory.SimplicialSiteSituation

end

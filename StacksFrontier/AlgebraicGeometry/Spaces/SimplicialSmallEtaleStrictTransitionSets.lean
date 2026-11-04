module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTransitionCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTransitionPasteIdentity
public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensorPullback
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The transition identity of the strict system on sheaves of sets

Let `X` be a simplicial algebraic space with an augmentation `a : X → Z`. The sheaf-level
transition identity `StrictTransitionSheafIdentity a φ` for the strict system of `b^*F` is an
identity of pullbacks of sheaves of modules built from the 2-cells of the strict model. This file
reduces it to the corresponding identity of direct images of sheaves of sets,
`StrictTransitionSetsIdentity a φ`, in which only the underlying 2-cells of morphisms of topoi
occur.

## Main results

* `SimplicialSpacesEtaleSite.StrictTransitionSetsIdentity`: the identity of direct images of
  sheaves of sets.
* `SimplicialSpacesEtaleSite.strictTransitionSheafIdentity_of_setsIdentity`: it implies the
  sheaf-level identity.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- The transition of component modules, in the pullback presentation of restriction, as the
transformation of pullbacks of the 2-morphism `g_n ⟶ g_m ∘ f_φ`. -/
theorem componentModulesTransition_app_eq_pullbackModulesMap (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) {m n : SimplexCategory} (φ : m ⟶ n)
    (M : (S.totalRingedTopos O).Modules) :
    (S.componentModulesTransition O φ).app M =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((S.componentPullbackModulesRestrictionIso O m).inv.app M) ≫
        ((pullbackModulesCompIso (S.transitionRingedToposHom O φ)
            (S.componentRingedToposHom O m)).inv ≫
          (S.componentRingedTwoMorphism O φ).pullbackModulesMap).app M ≫
        (S.componentPullbackModulesRestrictionIso O n).hom.app M := by
  have h1 := S.componentModuleTransition_app_eq_moduleFiberTransition O φ M
  have h2 : S.moduleFiberTransition O φ =
      (pullbackModulesCompIso (S.transitionRingedToposHom O φ)
        (S.componentRingedToposHom O m)).inv ≫
          (S.componentRingedTwoMorphism O φ).pullbackModulesMap :=
    rfl
  rw [h2] at h1
  exact h1

end CategoryTheory.SimplicialSiteSituation

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)} {Z : AlgebraicSpaces B S hS}
  (a : X ⟶ (Functor.const _).obj Z)

/-- **The transition identity of the strict model on direct images of sheaves of sets**: for a
sheaf of sets `G` on `(X_n)_{spaces,étale}`, the two comparisons
`a_{n*}G ⟶ b_* g_{m*} f_{φ*} sc_{n*} G` built from the 2-cells of the strict model agree. -/
structure StrictTransitionSetsIdentity {m n : SimplexCategory} (φ : m ⟶ n) : Prop where
  eq : ∀ G : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1)),
    (augmentationDegreeTwoIso a n).e.inv.app G ≫
        (strictAugmentationTwoIso a).e.inv.app
          ((degreeRingedToposHom X n).toToposHom.pushforward.obj G) ≫
        (strictAugmentationRingedToposHom a).toToposHom.pushforward.map
          ((strictDegreeTwoIso X n).e.hom.app G) ≫
        (strictAugmentationRingedToposHom a).toToposHom.pushforward.map
          (((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ).t.app
            ((strictComponentRingedToposHom X n).toToposHom.pushforward.obj G)) =
      (augmentationTransitionTwoIso a φ).e.inv.app G ≫
        (augmentationDegreeTwoIso a m).e.inv.app
          ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G) ≫
        (strictAugmentationTwoIso a).e.inv.app
          ((degreeRingedToposHom X m).toToposHom.pushforward.obj
            ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G)) ≫
        (strictAugmentationRingedToposHom a).toToposHom.pushforward.map
          ((strictDegreeTwoIso X m).e.hom.app
            ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G)) ≫
        (strictAugmentationRingedToposHom a).toToposHom.pushforward.map
          (((strictSituation X).componentRingedToposHom (strictStructureSheaf X)
              m).toToposHom.pushforward.map
            ((strictComponentTransitionTwoIso X φ).e.inv.app G))

/-- The sheaf-level transition identity follows from its form on direct images of sheaves of
sets. -/
theorem strictTransitionSheafIdentity_of_setsIdentity {m n : SimplexCategory} (φ : m ⟶ n)
    (hsets : StrictTransitionSetsIdentity a φ) : StrictTransitionSheafIdentity a φ := by
  refine ⟨fun F ↦ ?_⟩
  have key := pullbackModules_transitionPaste_eq (strictComponentRingedToposHom X n)
    (strictComponentRingedToposHom X m)
    ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
    ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
    (spacesEtaleRingedToposHom (X.map φ.op)) (degreeRingedToposHom X n) (degreeRingedToposHom X m)
    (strictRingedToposHom X) (strictAugmentationRingedToposHom a) (augmentationRingedToposHom a)
    (spacesEtaleRingedToposHom (a.app (op n))) (spacesEtaleRingedToposHom (a.app (op m)))
    ((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ)
    (strictDegreeTwoIso X n) (strictDegreeTwoIso X m) (strictAugmentationTwoIso a)
    (augmentationDegreeTwoIso a n) (augmentationDegreeTwoIso a m)
    (strictComponentTransitionTwoIso X φ) (augmentationTransitionTwoIso a φ) hsets.eq
    ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X) m)
    ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X) n)
    ((strictSituation X).componentModulesTransition (strictStructureSheaf X) φ)
    (fun M ↦ eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      ((strictSituation X).componentModulesTransition_app_eq_pullbackModulesMap
        (strictStructureSheaf X) φ M)) (by heq_congr)))) F
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

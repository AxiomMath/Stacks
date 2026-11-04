module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.BoundedBelowCompositionToDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# The map `Rf_! ⟶ Rf_*` and base change, on `D⁺_tors`

The map `Rf_! ⟶ Rf_*` of [Stacks, Tag 0H6X]
(`Stacks.EtaleCohomology.derivedLowerShriekToDirectImage`) is compatible with the base change
isomorphism `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` of [Stacks, Tag 0F7L] and the base change map
`g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ (g')⁻¹` of Cohomology on Sites, Remark 07A7: this is compatibility (2) of
the remark, whose proof the source omits.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_comp_toDirectImage`: the base change
  map of a cube of compactifications followed by `Rf'_! ⟶ Rf'_*` is `g⁻¹` of `Rf_! ⟶ Rf_*`
  followed by the base change map of direct images, on all of `D⁺`.
* `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeIso_hom_comp_toDirectImage`:
  **[Stacks, Tag 0H6X], compatibility (2)**, on `D⁺_tors`.

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

section Cube

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- **The map `Rf_! ⟶ Rf_*` commutes with the base change map of a cube of compactifications**,
on all of `D⁺(X_étale, Λ)`: for compactifications `j` of `f` and `j'` of `f'` and
`φ : X̄' ⟶ X̄` with `j' ≫ φ = g' ≫ j` cartesian and `f̄' ≫ g = φ ≫ f̄`, the base change map
`g⁻¹ Rf_! K ⟶ Rf'_! (g')⁻¹ K` followed by `Rf'_! ⟶ Rf'_*` is `g⁻¹` of `Rf_! K ⟶ Rf_* K` followed
by the base change map `g⁻¹ Rf_* K ⟶ Rf'_* (g')⁻¹ K`. -/
theorem derivedLowerShriekBaseChangeCube_comp_toDirectImage (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (φ : j'.space ⟶ j.space)
    (hc : IsPullback g' j'.immersion j.immersion φ) (w : j'.toBase ≫ g = φ ≫ j.toBase)
    (wf : f' ≫ g = g' ≫ f) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekBaseChangeCube Λ j j' φ hc w).app K ≫
        (derivedLowerShriekToDirectImage.{u, 0} Λ f' j').app
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K) =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
          ((derivedLowerShriekToDirectImage.{u, 0} Λ f j).app K) ≫
        (etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' wf).app K := by
  have hP := NatTrans.congr_app (etaleModuleDerivedBaseChange_comp Λ j.immersion j.toBase f
    (CompactificationOf.immersion_toBase j).symm j'.immersion j'.toBase f'
    (CompactificationOf.immersion_toBase j').symm g' φ g hc.w.symm w wf) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hP
  have hε := NatTrans.congr_app
    (etaleModuleDerivedExtensionByZeroToDirectImagePlus_baseChange Λ hc) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hε
  have nB := (etaleModuleDerivedBaseChange.{u, 0} Λ j.toBase j'.toBase g φ w).naturality
    ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, 0} Λ j.immersion).app K)
  simp only [Functor.comp_map] at nB
  have hP' : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
        ((etaleModuleDerivedDirectImageComp.{u, 0} Λ j.immersion j.toBase f
          (CompactificationOf.immersion_toBase j).symm).inv.app K) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' wf).app K =
      (etaleModuleDerivedBaseChange.{u, 0} Λ j.toBase j'.toBase g φ w).app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ j.immersion).obj K) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ j'.toBase).map
          ((etaleModuleDerivedBaseChange.{u, 0} Λ j.immersion j'.immersion φ g' hc.w.symm).app K) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ j'.immersion j'.toBase f'
          (CompactificationOf.immersion_toBase j').symm).inv.app
            ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K) := by
    refine (cancel_mono ((etaleModuleDerivedDirectImageComp.{u, 0} Λ j'.immersion j'.toBase f'
      (CompactificationOf.immersion_toBase j').symm).hom.app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K))).1 ?_
    refine ((Category.assoc _ _ _).trans ((whisker_eq _ hP).trans
      ((Functor.map_comp_assoc _ _ _ _).symm.trans ((eq_whisker ((congrArg _
        (Iso.inv_hom_id_app (etaleModuleDerivedDirectImageComp.{u, 0} Λ j.immersion j.toBase f
          (CompactificationOf.immersion_toBase j).symm) K)).trans
            (CategoryTheory.Functor.map_id _ _)) _).trans (Category.id_comp _))))).trans ?_
    exact ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
      ((whisker_eq _ (Iso.inv_hom_id_app (etaleModuleDerivedDirectImageComp.{u, 0} Λ j'.immersion
        j'.toBase f' (CompactificationOf.immersion_toBase j').symm) _)).trans
          (Category.comp_id _))))).symm
  simp only [derivedLowerShriekBaseChangeCube, derivedLowerShriekToDirectImage, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc, Functor.map_comp]
  rw [hP', reassoc_of% nB]
  exact whisker_eq _ ((Functor.map_comp_assoc _ _ _ _).symm.trans ((eq_whisker
    (congrArg (etaleModuleDerivedDirectImage.{u, 0} Λ j'.toBase).map hε.symm) _).trans
      (Functor.map_comp_assoc _ _ _ _)))

end Cube

section Iso

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}

/-- **[Stacks, Tag 0H6X], compatibility (2), on `D⁺_tors(X_étale, Λ)`**: the map `Rf_! ⟶ Rf_*`
is compatible with the isomorphism `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` of [Stacks, Tag 0F7L]
(`Stacks.EtaleCohomology.derivedLowerShriekBaseChangeIso`) and the base change map
`g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ (g')⁻¹` of Cohomology on Sites, Remark 07A7
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange`): for a cartesian square
`g' ≫ f = f' ≫ g`, a compactification `j` of `f` and `K` in `D⁺_tors(X_étale, Λ)`,
`g⁻¹ Rf_! K ≅ Rf'_! (g')⁻¹ K ⟶ Rf'_* (g')⁻¹ K` is `g⁻¹ Rf_! K ⟶ g⁻¹ Rf_* K ⟶ Rf'_* (g')⁻¹ K`,
`Rf'_!` being computed with the base change of `j`. -/
@[stacks 0H6X "(2), on D⁺_tors"]
theorem derivedLowerShriekBaseChangeIso_hom_comp_toDirectImage (sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f)) (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekBaseChangeIso Λ sq j).hom.app K ≫
        (derivedLowerShriekToDirectImage.{u, 0} Λ f' (j.baseChange sq)).app
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K.obj) =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
          ((derivedLowerShriekToDirectImage.{u, 0} Λ f j).app K.obj) ≫
        (etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' sq.w.symm).app K.obj := by
  rw [derivedLowerShriekBaseChangeIso_hom_app, derivedLowerShriekBaseChange_eq_cube]
  exact derivedLowerShriekBaseChangeCube_comp_toDirectImage Λ j (j.baseChange sq) _
    (j.isPullback_baseChange sq) _ sq.w.symm K.obj

end Iso

end Stacks.EtaleCohomology

end

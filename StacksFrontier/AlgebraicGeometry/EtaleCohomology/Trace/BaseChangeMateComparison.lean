module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap

/-!
# The two base change maps for sheaves of modules agree

For a commutative square `h' ≫ g = g' ≫ h` of schemes there are two descriptions of the base
change map `g^{-1} h_* ⟶ h'_* g'^{-1}` of étale sheaves of `Λ`-modules:
`Stacks.EtaleCohomology.etaleModuleBaseChange`, the mate along the adjunctions of `h` and `h'` of
the comparison of the composite inverse images, and
`Stacks.EtaleCohomology.etaleModuleBaseChangeGeneral`, the inverse mate along the adjunctions of
`g'` and `g` of the comparison of the composite direct images. They are equal: the iterated mate of
the first is the conjugate of the inverse image comparison, which is the direct image comparison.

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChange_eq_etaleModuleMateBaseChange`: the two base
  change maps `etaleModuleBaseChange` and `etaleModuleBaseChangeGeneral` are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {Z Y Z' Y' : Scheme.{u}} (h : Z ⟶ Y) (h' : Z' ⟶ Y') (g : Y' ⟶ Y)
  (g' : Z' ⟶ Z) (w : h' ≫ g = g' ≫ h)

/-- **The two base change maps agree.** -/
theorem etaleModuleBaseChange_eq_etaleModuleMateBaseChange :
    etaleModuleBaseChange Λ h h' g g' w =
      etaleModuleBaseChangeGeneral.{u, r} Λ h g g' h' w.symm := by
  unfold etaleModuleBaseChangeGeneral
  rw [← (mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ g')
    (etaleModuleInverseImageAdj.{u, r} Λ g)).symm_apply_apply (etaleModuleBaseChange Λ h h' g g' w)]
  congr 1
  have hit := iterated_mateEquiv_conjugateEquiv (etaleModuleInverseImageAdj.{u, r} Λ h)
    (etaleModuleInverseImageAdj.{u, r} Λ h') (etaleModuleInverseImageAdj.{u, r} Λ g)
    (etaleModuleInverseImageAdj.{u, r} Λ g')
    (Stacks.CategoryTheory.BaseChange.pullbackComparison
      (etaleModuleInverseImageCompIso.{u, r} Λ h' g).symm
      ((etaleModuleInverseImageCompIso.{u, r} Λ g' h).symm ≪≫
        eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w.symm)))
  refine hit.trans ?_
  let adjA := (etaleModuleInverseImageAdj.{u, r} Λ h).comp (etaleModuleInverseImageAdj.{u, r} Λ g')
  let adjB := (etaleModuleInverseImageAdj.{u, r} Λ g).comp (etaleModuleInverseImageAdj.{u, r} Λ h')
  let adjC := etaleModuleInverseImageAdj.{u, r} Λ (h' ≫ g)
  let ef := (etaleModuleInverseImageCompIso.{u, r} Λ g' h).symm ≪≫
    eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w.symm)
  have hB : conjugateEquiv adjC adjB (etaleModuleInverseImageCompIso.{u, r} Λ h' g).inv =
      (etaleModuleDirectImageComp.{u, r} Λ h' g (h' ≫ g) rfl).inv :=
    conjugateEquiv_etaleModuleInverseImageCompIso_inv Λ h' g
  have hA' : conjugateEquiv adjC adjA ef.hom =
      (etaleModuleDirectImageComp.{u, r} Λ g' h (h' ≫ g) w).inv :=
    conjugateEquiv_etaleModuleInverseImageCompIso_inv' Λ g' h (h' ≫ g) w
  have hA : conjugateEquiv adjA adjC ef.inv =
      (etaleModuleDirectImageComp.{u, r} Λ g' h (h' ≫ g) w).hom := by
    have h1 := conjugateEquiv_comp adjA adjC adjA ef.inv ef.hom
    rw [Iso.hom_inv_id, conjugateEquiv_id adjA, hA'] at h1
    exact (Iso.comp_inv_eq_id _).1 h1
  change conjugateEquiv adjA adjB ((etaleModuleInverseImageCompIso.{u, r} Λ h' g).inv ≫ ef.inv) = _
  rw [← conjugateEquiv_comp adjA adjC adjB, hA, hB]
  have key : ∀ (c : Z' ⟶ Y) (e₁ : c = g' ≫ h) (e₂ : c = h' ≫ g),
      (etaleModuleDirectImageComp.{u, r} Λ g' h c e₁).hom ≫
        (etaleModuleDirectImageComp.{u, r} Λ h' g c e₂).inv =
      (etaleModuleDirectImageComp.{u, r} Λ g' h (g' ≫ h) rfl).hom ≫
        (etaleModuleDirectImageComp.{u, r} Λ h' g (g' ≫ h) w.symm).inv := by
    rintro c rfl e₂
    rfl
  rw [key _ w rfl]
  rfl

end Stacks.EtaleCohomology

end

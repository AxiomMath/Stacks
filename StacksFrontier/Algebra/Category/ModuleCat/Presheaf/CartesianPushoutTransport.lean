module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction

/-!
# Transporting the cartesian condition across a pushout of rings

Let `M` be a presheaf of modules over a presheaf of commutative rings `R_C` on `C`, and `N` one
over `R_D` on `D`. Suppose an arrow `f : X ⟶ Y` of `Cᵒᵖ` and an arrow `f' : X' ⟶ Y'` of `Dᵒᵖ`
are related by ring maps `α_X : R_C X ⟶ R_D X'`, `α_Y : R_C Y ⟶ R_D Y'` forming a pushout square
with the restriction maps, and by additive bijections `M X ≃ N X'`, `M Y ≃ N Y'`, semilinear over
`α_X`, `α_Y` and compatible with the restriction maps. Then `M` is cartesian over `f` as soon as
`N` is cartesian over `f'`: the base-change comparison `R_C Y ⊗_{R_C X} M X ⟶ M Y` is bijective
when `R_D Y' ⊗_{R_D X'} N X' ⟶ N Y'` is.

This is the algebra behind `Stacks.PresheafOfModules.bijective_restrictionBaseChange_pushforward`,
freed from the requirement that `M` be a pushforward of `N`: here the sections of `M` are only
identified with those of `N`, one arrow at a time. That is the situation of a direct image of
modules computed by its sections over terminal objects of the comma categories, as for a
1-morphism of algebraic stacks representable by affine schemes (Stacks 0765).

The module statement is `Algebra.IsPushout.cancelBaseChange`,
`R_D Y' ⊗_{R_D X'} N X' ≅ R_C Y ⊗_{R_C X} N X'`, and the comparison maps agree on pure tensors.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_isPushout`: the transport.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v₁ v₂ u₁ u₂ r m

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {RC : Cᵒᵖ ⥤ CommRingCat.{r}} {RD : Dᵒᵖ ⥤ CommRingCat.{r}}

/-- **The cartesian condition transports across a pushout square of rings.** If the sections of
`M` over `X` and `Y` are identified, semilinearly over a pushout square of rings and compatibly with
the restriction maps, with the sections of `N` over `X'` and `Y'`, then `M` is cartesian over
`f : X ⟶ Y` as soon as `N` is cartesian over `f' : X' ⟶ Y'`. -/
theorem bijective_restrictionBaseChange_of_isPushout
    (M : PresheafOfModules.{max m r} (RC ⋙ forget₂ CommRingCat RingCat.{r}))
    (N : PresheafOfModules.{max m r} (RD ⋙ forget₂ CommRingCat RingCat.{r}))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) {X' Y' : Dᵒᵖ} (f' : X' ⟶ Y')
    (αX : RC.obj X ⟶ RD.obj X') (αY : RC.obj Y ⟶ RD.obj Y')
    (hpo : IsPushout αX (RC.map f) (RD.map f') αY)
    (eX : M.obj X ≃+ N.obj X') (eY : M.obj Y ≃+ N.obj Y')
    (heX : ∀ (a : RC.obj X) (x : M.obj X), eX (a • x) = αX.hom a • eX x)
    (heY : ∀ (a : RC.obj Y) (x : M.obj Y), eY (a • x) = αY.hom a • eY x)
    (hnat : ∀ x : M.obj X, eY ((M.map f).hom x) = (N.map f').hom (eX x))
    (hN : Function.Bijective (restrictionBaseChange (R := RD) N f')) :
    Function.Bijective (restrictionBaseChange (R := RC) M f) := by
  let : Algebra (RC.obj X) (RC.obj Y) := (RC.map f).hom.toAlgebra
  let : Algebra (RC.obj X) (RD.obj X') := αX.hom.toAlgebra
  let : Algebra (RD.obj X') (RD.obj Y') := (RD.map f').hom.toAlgebra
  let : Algebra (RC.obj Y) (RD.obj Y') := αY.hom.toAlgebra
  let : Algebra (RC.obj X) (RD.obj Y') := (αX ≫ RD.map f').hom.toAlgebra
  have : IsScalarTower (RC.obj X) (RD.obj X') (RD.obj Y') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (RC.obj X) (RC.obj Y) (RD.obj Y') :=
    IsScalarTower.of_algebraMap_eq fun x =>
      congrArg (fun g : RC.obj X ⟶ RD.obj Y' => g.hom x) hpo.w
  have : Algebra.IsPushout (RC.obj X) (RC.obj Y) (RD.obj X') (RD.obj Y') :=
    (CommRingCat.isPushout_iff_isPushout.1 hpo).symm
  let : Module (RC.obj X) (N.obj X') := Module.compHom (N.obj X') αX.hom
  let : Module (RD.obj X') (N.obj Y') := inferInstanceAs
    (Module (RD.obj X') ((ModuleCat.restrictScalars (RD.map f').hom).obj (N.obj Y')))
  have : IsScalarTower (RC.obj X) (RD.obj X') (N.obj X') :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (RD.obj X') (RD.obj Y') (N.obj Y') :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : N.obj X' →ₗ[RD.obj X'] N.obj Y' :=
    { toFun := fun x => (N.map f').hom x
      map_add' := fun x y => map_add (N.map f').hom x y
      map_smul' := fun c x => (N.map f').hom.map_smul c x }
  have hbc : IsBaseChange (RD.obj Y') g :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective (restrictionBaseChange (R := RD) N f').hom hN)
      fun x => restrictionBaseChange_one_tmul N f' x
  let eXl : M.obj X ≃ₗ[RC.obj X] N.obj X' := { eX with map_smul' := heX }
  let c := Algebra.IsPushout.cancelBaseChange (RC.obj X) (RC.obj Y) (RD.obj X') (RD.obj Y')
    (N.obj X')
  let Φ : (RC.obj Y) ⊗[RC.obj X] (M.obj X) ≃+ M.obj Y :=
    (((LinearEquiv.baseChange (RC.obj X) (RC.obj Y) _ _ eXl).toAddEquiv.trans
      c.symm.toAddEquiv).trans hbc.equiv.toAddEquiv).trans eY.symm
  have key : ∀ x, (restrictionBaseChange (R := RC) M f) x = Φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero Φ).symm
    | tmul s mm =>
      refine (restrictionBaseChange_tmul (R := RC) M f s mm).trans (eY.injective ?_)
      refine (heY (show RC.obj Y from s) _).trans ?_
      rw [hnat]
      refine Eq.symm ((eY.apply_symm_apply _).trans ?_)
      refine (congrArg (fun z => hbc.equiv (c.symm z))
        (rfl : LinearEquiv.baseChange (RC.obj X) (RC.obj Y) _ _ eXl (s ⊗ₜ mm) =
          (show RC.obj Y from s) ⊗ₜ eX mm)).trans ?_
      refine (congrArg hbc.equiv (Algebra.IsPushout.cancelBaseChange_symm_tmul (RC.obj X)
        (RC.obj Y) (RD.obj X') (RD.obj Y') (N.obj X') (show RC.obj Y from s) (eX mm))).trans ?_
      exact hbc.equiv_tmul _ _
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add Φ x y).symm)
  rw [show ⇑(restrictionBaseChange (R := RC) M f) = Φ from funext key]
  exact Φ.bijective

end Stacks.PresheafOfModules

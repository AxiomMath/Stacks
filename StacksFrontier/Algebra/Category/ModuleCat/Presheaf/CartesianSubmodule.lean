module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# A sub-presheaf of a cartesian presheaf of modules, along a flat map

Let `M` be a presheaf of modules over a presheaf of commutative rings `R`, `N ⊆ M` a sub-presheaf
of modules and `f : X ⟶ Y` an arrow along which `R` is flat and `M` is cartesian (the comparison
`R(Y) ⊗_{R(X)} M(X) ⟶ M(Y)` is an isomorphism).  Then `N` is cartesian along `f` as soon as
`N(Y)` is spanned by the restriction of `N(X)`: injectivity of the comparison of `N` is flatness,
surjectivity is the spanning condition.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_submodule`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped ChangeOfRings

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **A sub-presheaf spanned along a flat cartesian arrow is cartesian there.** -/
theorem isIso_restrictionBaseChange_submodule
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)) (N : M.Submodule)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (hflat : (R.map f).hom.Flat)
    (hM : IsIso (restrictionBaseChange M f))
    (hspan : N.obj Y ≤ Submodule.span (R.obj Y) (M.restrictₛₗ f '' N.obj X)) :
    IsIso (restrictionBaseChange N.toPresheafOfModules f) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  have : Module.Flat (R.obj X) (R.obj Y) := hflat
  let θN : TensorProduct (R.obj X) (R.obj Y) (N.obj X) →ₗ[R.obj Y] N.obj Y :=
    (restrictionBaseChange N.toPresheafOfModules f).hom
  let θM : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y :=
    (restrictionBaseChange M f).hom
  let ιX : N.obj X →ₗ[R.obj X] M.obj X := (N.obj X).subtype
  have hθM : Function.Bijective θM := (ConcreteCategory.isIso_iff_bijective _).mp hM
  have nat : ∀ t, (θN t : M.obj Y) = θM (ιX.lTensor (R.obj Y) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a n =>
      rw [LinearMap.lTensor_tmul]
      exact (congrArg Subtype.val (restrictionBaseChange_tmul N.toPresheafOfModules f a n)).trans
        (restrictionBaseChange_tmul M f a (n : M.obj X)).symm
    | add x y hx hy => rw [map_add, map_add, map_add, Submodule.coe_add, hx, hy]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective θN
  refine ⟨fun t t' h => ?_, fun y => ?_⟩
  · exact Module.Flat.lTensor_preserves_injective_linearMap ιX Subtype.val_injective
      (hθM.1 (by rw [← nat, ← nat, h]))
  · have hle : Submodule.span (R.obj Y) (M.restrictₛₗ f '' N.obj X) ≤
        (LinearMap.range θN).map (N.obj Y).subtype := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨θN ((1 : R.obj Y) ⊗ₜ ⟨n, hn⟩), ⟨_, rfl⟩, ?_⟩
      rw [Submodule.subtype_apply, nat, LinearMap.lTensor_tmul]
      exact restrictionBaseChange_one_tmul M f n
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hle (hspan y.2)
    exact ⟨t, Subtype.ext ht⟩

end Stacks.PresheafOfModules

end

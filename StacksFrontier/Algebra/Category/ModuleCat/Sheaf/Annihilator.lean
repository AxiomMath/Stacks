module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The annihilator of a sheaf of modules

Let `(C, J)` be a site, `R` a sheaf of rings on it and `M` a sheaf of `R`-modules. A section `a`
of `R` over `U` *annihilates* `M` when, for every arrow `V ⟶ U`, the restriction of `a` to `V`
kills every section of `M` over `V`. These sections form a sheaf of ideals of `R`, the
annihilator `Ann(M)`: membership is visibly stable under restriction, and it is local because a
sheaf of modules is separated.

The annihilator is the device for transporting "every section of a sheaf of ideals `𝓘` kills
`M`" from generators of `𝓘` to all of `𝓘`: it suffices that the generators lie in `Ann(M)`,
since `Ann(M)` is itself a sheaf of ideals.

## Main definitions

* `SheafOfModules.annihilatorObj`: the ideal of sections of `R` over `U` annihilating `M`.
* `SheafOfModules.annihilator`: the annihilator `Ann(M)`, a submodule of the free rank-one
  sheaf of `R`-modules.

## Main results

* `SheafOfModules.mem_annihilator_iff`: membership in the annihilator, unfolded.
* `SheafOfModules.smul_eq_zero_of_mem_annihilator`: a section of the annihilator kills every
  section of `M` over the same object.

## Implementation notes

The annihilator is stated with the restriction to every object *over* `U` rather than with the
action on sections over `U` alone: only the former is stable under restriction, which a
submodule of a presheaf of modules has to be. For a sheaf of commutative rings the two agree.
-/

@[expose] public section

open CategoryTheory Opposite

universe v v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The ideal of sections `a` of `R` over `U` which annihilate `M`: for every arrow `V ⟶ U`, the
restriction of `a` to `V` kills every section of `M` over `V`. -/
def annihilatorObj (M : SheafOfModules.{v} R) (U : Cᵒᵖ) :
    _root_.Submodule (R.obj.obj U) (R.obj.obj U) where
  carrier := {a | ∀ ⦃W : Cᵒᵖ⦄ (g : U ⟶ W) (y : M.val.obj W), R.obj.map g a • y = 0}
  add_mem' := fun {a b} ha hb W g y => by
    change R.obj.map g (a + b) • y = 0
    rw [map_add, add_smul, ha g y, hb g y, add_zero]
  zero_mem' := fun W g y => by
    change R.obj.map g 0 • y = 0
    rw [map_zero, zero_smul]
  smul_mem' := fun c a ha W g y => by
    change R.obj.map g (c * a) • y = 0
    rw [map_mul, mul_smul, ha g y, smul_zero]

/-- A section `a` of `R` over `U` lies in `annihilatorObj M U` if and only if, for every arrow
`U ⟶ W` in `Cᵒᵖ`, the restriction of `a` to `W` kills every section of `M` over `W`. -/
theorem mem_annihilatorObj_iff (M : SheafOfModules.{v} R) {U : Cᵒᵖ} (a : R.obj.obj U) :
    a ∈ annihilatorObj M U ↔
      ∀ ⦃W : Cᵒᵖ⦄ (g : U ⟶ W) (y : M.val.obj W), R.obj.map g a • y = 0 :=
  Iff.rfl

/-- The restriction of a section annihilating `M` annihilates `M`. -/
theorem map_mem_annihilatorObj (M : SheafOfModules.{v} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    {a : R.obj.obj U} (ha : a ∈ annihilatorObj M U) :
    R.obj.map f a ∈ annihilatorObj M V := fun W g y => by
  rw [← RingCat.comp_apply, ← Functor.map_comp]
  exact ha (f ≫ g) y

/-- A section annihilating `M` kills every section of `M` over the same object. -/
private theorem smul_eq_zero_of_mem_annihilatorObj (M : SheafOfModules.{v} R) {U : Cᵒᵖ}
    {a : R.obj.obj U} (ha : a ∈ annihilatorObj M U) (y : M.val.obj U) : a • y = 0 := by
  simpa using ha (𝟙 U) y

/-- **Annihilating `M` is a local condition.** A section whose restrictions along the arrows of a
covering sieve annihilate `M` annihilates `M`, because a sheaf of modules is separated. -/
theorem mem_annihilatorObj_of_locally (M : SheafOfModules.{v} R) {U : Cᵒᵖ}
    (a : R.obj.obj U) {S : Sieve U.unop} (hS : S ∈ J U.unop)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ U.unop), S f → R.obj.map f.op a ∈ annihilatorObj M (op Y)) :
    a ∈ annihilatorObj M U := fun W g y => by
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (R := R) _
    (J.pullback_stable g.unop hS) fun Y k hk => ?_
  rw [PresheafOfModules.map_smul]
  have := smul_eq_zero_of_mem_annihilatorObj M (h (k ≫ g.unop) hk) (M.val.map k.op y)
  rwa [op_comp, R.obj.map_comp, RingCat.comp_apply] at this

/-- **The annihilator of a sheaf of modules**, the sheaf of ideals of `R` whose sections over `U`
are the sections of `R` over `U` annihilating `M`. -/
@[ega "0 5.3.7"]
noncomputable def annihilator (M : SheafOfModules.{v} R) : (unit R).Submodule where
  obj U := annihilatorObj M U
  map f a ha := map_mem_annihilatorObj M f (a := a) ha
  isSheaf {_U} a ha := mem_annihilatorObj_of_locally M a ha fun _ _ hf => hf

/-- A section `a` of `R` over `U` lies in the annihilator of `M` if and only if, for every arrow
`U ⟶ W` in `Cᵒᵖ`, the restriction of `a` to `W` kills every section of `M` over `W`. -/
theorem mem_annihilator_iff (M : SheafOfModules.{v} R) {U : Cᵒᵖ} (a : R.obj.obj U) :
    a ∈ (annihilator M).obj U ↔
      ∀ ⦃W : Cᵒᵖ⦄ (g : U ⟶ W) (y : M.val.obj W), R.obj.map g a • y = 0 :=
  Iff.rfl

/-- A section of the annihilator kills every section of `M` over the same object. -/
theorem smul_eq_zero_of_mem_annihilator (M : SheafOfModules.{v} R) {U : Cᵒᵖ} {a : R.obj.obj U}
    (ha : a ∈ (annihilator M).obj U) (y : M.val.obj U) : a • y = 0 :=
  smul_eq_zero_of_mem_annihilatorObj M ha y

end SheafOfModules

end

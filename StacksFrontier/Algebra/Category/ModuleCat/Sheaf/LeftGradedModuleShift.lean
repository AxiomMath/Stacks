module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedGrothendieck
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleBimodule

/-!
# The shift of a left graded module over a sheaf of graded algebras

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of `ℤ`-graded `R`-algebras and let `N`
be a left graded `A`-module. For `k : ℤ` the shift `N(k)` is the left graded `A`-module whose
degree-`n` piece is the degree-`n + k` piece of `N`, with the same action: a homogeneous algebra
section of degree `i` sends the degree-`n` piece of `N(k)` to its degree-`i + n` piece because it
sends `N`'s degree-`n + k` piece to its degree-`i + (n + k)` piece, and `i + (n + k)` and
`i + n + k` are the same degree.

This is the construction the twisted sheaves `ℳ(n)` on a relative `Proj` are built from, so it
is what makes property (7) of Tag 01O7 stateable; the right-handed shift it mirrors is
`SheafOfModules.GradedModule.shift`.

## Main definitions

* `SheafOfModules.LeftGradedModule.shift`: **the shift `N(k)` of a left graded module.**

## Main results

* `SheafOfModules.LeftGradedModule.shift_piece` and
  `SheafOfModules.LeftGradedModule.shift_smul`: the pieces and the action of the shift.
* `SheafOfModules.LeftGradedModule.shiftZeroIso`: **shifting by `0` changes nothing.**
* `SheafOfModules.LeftGradedModule.shiftShiftIso`: **shifting twice is shifting by the sum.**

## Implementation notes

Every degree equality is discharged by `omega` and every transport of a local section is a
`SheafOfModules.castHom`, exactly as in the right-handed `SheafOfModules.GradedModule.shift`.
That keeps the action of the shift a *homogeneous* equation — `shift_smul` is `rfl` — so only the
two structure fields that are heterogeneous equalities for every graded module, associativity and
unitality, need `HEq` reasoning. Each transport is then moved out of the way by `subst`-ing the
degree equality away, after which the transport is the identity and the field is the matching
field of `N`; `SheafOfModules.LeftGradedModule.smul_congr` packages the one place where both the
degree and the section have to move at once.

`shift` is marked `@[implicit_reducible]`, as is the right-handed shift: without it
`(N.shift k).piece n` does not reduce to `N.piece (n + k)` at the transparency `rw` uses to check
type correctness, and the comparison morphisms below fail to elaborate.

The two comparison morphisms are degreewise `SheafOfModules.degCastHom`s, so they are
isomorphisms for the cheapest possible reason, and their inverses are the transports along the
reversed degree equalities.

No Koszul sign appears here. The shift of a left graded module over a *differential* graded
algebra is defined in Tag 0FQ1 with the factor `(-1)^(i * k)`, as in
`ExternallyGradedLeftModule.shift`; this construction is the unsigned reindexing that the
commutative graded rings of Tag 01O7 call for, and it is not the shift of Tag 0FQ1. The two are
isomorphic as left graded modules — degreewise multiplication by `(-1)^(n * k)` is an
`A`-linear bijection between them — but they are not the same action, so a consumer that needs
the sign convention of Tag 0FQ1 must not use this.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

namespace LeftGradedModule

variable (N : LeftGradedModule.{t, a, m} A)

/-- Transporting the module argument of the action along an equality of degrees. -/
theorem smul_castHom_right {i n n' : ℤ} (h : n = n') (U : Cᵒᵖ) (a : (A.piece i).val.obj U)
    (x : (N.piece n).val.obj U) :
    N.smul i n' U a (castHom N.piece h U x)
      = castHom N.piece (by rw [h]) U (N.smul i n U a x) := by
  subst h
  rfl

/-- Transporting the algebra argument of the action along an equality of degrees. -/
theorem smul_castHom_left {i i' n : ℤ} (h : i = i') (U : Cᵒᵖ) (a : (A.piece i).val.obj U)
    (x : (N.piece n).val.obj U) :
    N.smul i' n U (castHom A.piece h U a) x
      = castHom N.piece (by rw [h]) U (N.smul i n U a x) := by
  subst h
  rfl

/-- **The shift `N(k)` of a left graded module**: the degree-`n` piece of `N.shift k` is the
degree-`n + k` piece of `N`, with the same action. -/
@[implicit_reducible]
def shift (k : ℤ) : LeftGradedModule.{t, a, m} A where
  piece n := N.piece (n + k)
  smul i n U :=
    AddMonoidHom.mk'
      (fun a ↦ (castHom N.piece (by omega : i + (n + k) = i + n + k) U).comp
        (N.smul i (n + k) U a))
      (fun a b ↦ AddMonoidHom.ext fun x ↦ by
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add])
  smul_smul_left i n U r a x := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply, N.smul_smul_left, castHom_smul]
  smul_smul_right i n U r a x := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply, N.smul_smul_right, castHom_smul]
  smul_naturality i n {U V} f a x := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply, castHom_naturality,
      N.smul_naturality]
    rfl
  mul_smul i j n U a b x := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply]
    refine ((heq_castHom _ _ _ _).trans ?_).trans (heq_castHom _ _ _ _).symm
    refine (N.mul_smul i j (n + k) U a b x).trans ?_
    exact N.smul_congr rfl (by omega) U HEq.rfl (heq_castHom N.piece _ U _).symm
  one_smul n U x := by
    simp only [AddMonoidHom.mk'_apply, AddMonoidHom.comp_apply]
    exact (heq_castHom _ _ _ _).trans (N.one_smul (n + k) U x)

/-- The degree-`n` piece of `N.shift k` is the degree-`n + k` piece of `N`. -/
@[simp] theorem shift_piece (k n : ℤ) : (N.shift k).piece n = N.piece (n + k) := rfl

/-- The action of a degree-`i` section on the degree-`n` piece of `N.shift k` is the action on the
degree-`n + k` piece of `N`, transported along `i + (n + k) = i + n + k`. -/
theorem shift_smul (k i n : ℤ) (U : Cᵒᵖ) (a : (A.piece i).val.obj U)
    (x : (N.piece (n + k)).val.obj U) :
    (N.shift k).smul i n U a x
      = castHom N.piece (by omega : i + (n + k) = i + n + k) U (N.smul i (n + k) U a x) := rfl

/-- Transporting a section of `N.shift k` along `i = j` is transporting it in `N` along
`i + k = j + k`. -/
theorem castHom_shift_piece (k : ℤ) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (N.piece (i + k)).val.obj U) :
    castHom (N.shift k).piece h U x = castHom N.piece (by rw [h] : i + k = j + k) U x := by
  subst h
  rfl

/-- **Shifting a left graded module by `0` changes nothing.** -/
def shiftZeroIso : N.shift 0 ≅ N where
  hom :=
    { app n := degCastHom N.piece (by omega : n + 0 = n)
      map_smul i n U a x := by
        simp only [degCastHom_val_app, shift_smul, Cofree.castHom_castHom, smul_castHom_right] }
  inv :=
    { app n := degCastHom N.piece (by omega : n = n + 0)
      map_smul i n U a x := by
        simp only [degCastHom_val_app, shift_smul, Cofree.castHom_castHom, smul_castHom_right] }
  hom_inv_id := Hom.ext fun _ ↦
    (degCastHom_comp_degCastHom N.piece _ _).trans (degCastHom_eq_id N.piece _)
  inv_hom_id := Hom.ext fun _ ↦
    (degCastHom_comp_degCastHom N.piece _ _).trans (degCastHom_eq_id N.piece _)

/-- **Shifting a left graded module twice is shifting it by the sum.** -/
def shiftShiftIso (k l : ℤ) : (N.shift k).shift l ≅ N.shift (k + l) where
  hom :=
    { app n := degCastHom N.piece (by omega : n + l + k = n + (k + l))
      map_smul i n U a x := by
        simp only [degCastHom_val_app, shift_smul, castHom_shift_piece, Cofree.castHom_castHom,
          smul_castHom_right] }
  inv :=
    { app n := degCastHom N.piece (by omega : n + (k + l) = n + l + k)
      map_smul i n U a x := by
        simp only [degCastHom_val_app, shift_smul, castHom_shift_piece, Cofree.castHom_castHom,
          smul_castHom_right] }
  hom_inv_id := Hom.ext fun _ ↦
    (degCastHom_comp_degCastHom N.piece _ _).trans (degCastHom_eq_id N.piece _)
  inv_hom_id := Hom.ext fun _ ↦
    (degCastHom_comp_degCastHom N.piece _ _).trans (degCastHom_eq_id N.piece _)

end LeftGradedModule

end SheafOfModules

end

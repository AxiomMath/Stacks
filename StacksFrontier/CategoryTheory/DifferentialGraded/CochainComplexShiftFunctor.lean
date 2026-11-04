module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The shift as a functor of the differential graded category of complexes

The first field of axiom (B), in either its strict form `DGCategory.ShiftAxiomB` or its
isomorphism-valued form `DGCategory.ShiftAxiomBIso`, is a family of *differential graded*
functors `x ↦ x[n]`. This file supplies that family for `CochainComplex.dgCategory B`, the
differential graded category of complexes of Tag 09L9 — the `C` of Tag 09LK.

Mathlib's shift of a cochain, `CochainComplex.HomComplex.Cochain.shift`, is not itself a
differential graded functor: by `CochainComplex.HomComplex.Cochain.δ_shift` it satisfies
`δ (γ[n]) = (-1)^n • (δ γ)[n]`, whereas a differential graded functor must commute with the
differential on the nose. The correction is a Koszul sign depending on the degree of the cochain
as well as on `n`: on a cochain of degree `k` the differential graded shift is
`(-1)^(n * k) • Cochain.shift n`, and `(-1)^(n * k) * (-1)^n = (-1)^(n * (k + 1))` is exactly
what makes the differentials agree. The sign is `1` in degree zero, so the shift of a map of
complexes is unchanged, and it is multiplicative in the degree, so composition is preserved.

## Main definitions

* `CochainComplex.dgShiftFunctor`: the shift, as a functor of the differential graded category
  of complexes.

## Main results

* `CochainComplex.dgShiftFunctor_obj` and `CochainComplex.dgShiftFunctor_map`: its value on an
  object and on a homogeneous morphism.
* `CochainComplex.HomComplex.Cochain.shift_comp_dgFunctor`: the shift of a composite of cochains
  is the composite of the shifts.

## Implementation notes

The ground ring is `ℤ`, matching `CochainComplex.dgCategory`, so `R`-linearity of the shift is
`ℤ`-linearity, which follows from additivity through
`CochainComplex.HomComplex.Cochain.shiftAddHom`. The signs are `Int.negOnePow`, units of `ℤ`
acting on cochains, as in `CochainComplex.HomComplex.Cochain.δ_shift`.

## References

* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the differential graded
  category of complexes; [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B).
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

open CochainComplex.HomComplex

namespace HomComplex.Cochain

variable {B : Type u} [Category.{v} B] [Preadditive B]

/-- The shift of a composite of cochains is the composite of the shifts, with no sign. -/
theorem shift_comp_dgFunctor {X Y Z : CochainComplex B ℤ} {n₁ n₂ n₁₂ : ℤ}
    (z₁ : Cochain X Y n₁) (z₂ : Cochain Y Z n₂) (h : n₁ + n₂ = n₁₂) (a : ℤ) :
    (z₁.comp z₂ h).shift a = (z₁.shift a).comp (z₂.shift a) h := by
  ext p q hpq
  rw [(z₁.comp z₂ h).shift_v' a p q hpq,
    Cochain.comp_v z₁ z₂ h (p + a) (p + n₁ + a) (q + a) (by lia) (by lia),
    Cochain.comp_v (z₁.shift a) (z₂.shift a) h p (p + n₁) q rfl (by lia),
    z₁.shift_v' a p (p + n₁) rfl, z₂.shift_v' a (p + n₁) q (by lia)]

/-- The shift of the identity cochain is the identity cochain. -/
theorem shift_ofHom_id_dgFunctor (X : CochainComplex B ℤ) (a : ℤ) :
    (Cochain.ofHom (𝟙 X)).shift a = Cochain.ofHom (𝟙 ((CategoryTheory.shiftFunctor
      (CochainComplex B ℤ) a).obj X)) := by
  ext p
  rw [(Cochain.ofHom (𝟙 X)).shift_v' a p p (add_zero p), Cochain.ofHom_v, Cochain.ofHom_v]
  simp

end HomComplex.Cochain

variable (B : Type u) [Category.{v} B] [Preadditive B]

/-- The shift by `n` as a functor of the differential graded category of complexes: on objects
it is Mathlib's shift of a cochain complex, and on a homogeneous morphism of degree `k` it is
Mathlib's shift of a cochain multiplied by the Koszul sign `(-1)^(n * k)`. -/
@[sga "4 XVII 1.1.4.2.1" "special case"]
noncomputable def dgShiftFunctor (n : ℤ) :
    DGCategory.DGFunctor (dgCategory B) (dgCategory B) where
  obj X := (CategoryTheory.shiftFunctor (CochainComplex B ℤ) n).obj X
  map {_ _ k} f := (n * k).negOnePow • f.shift n
  map_add {_ _ k} f g := by
    change (n * k).negOnePow • (f + g).shift n = _
    rw [Cochain.shift_add]
    change _ = (n * k).negOnePow • f.shift n + (n * k).negOnePow • g.shift n
    rw [← smul_add]
  map_smul {_ _ k} r f := by
    change (n * k).negOnePow • (r • f).shift n = r • ((n * k).negOnePow • f.shift n)
    rw [show (r • f).shift n = r • f.shift n from
      map_zsmul (Cochain.shiftAddHom _ _ k n) r f, Units.smul_def, Units.smul_def,
      smul_comm]
  map_d {X Y k} f := by
    change (n * (k + 1)).negOnePow • (δ k (k + 1) f).shift n =
      δ k (k + 1) ((n * k).negOnePow • f.shift n)
    rw [δ_units_smul, Cochain.δ_shift, show n * (k + 1) = n * k + n by ring,
      Int.negOnePow_add, smul_smul, mul_comm ((n * k).negOnePow) n.negOnePow]
  map_comp {X Y Z m k l} h g f := by
    change (n * l).negOnePow • (f.comp g (by lia : k + m = l)).shift n =
      ((n * k).negOnePow • f.shift n).comp ((n * m).negOnePow • g.shift n) (by lia : k + m = l)
    rw [Cochain.shift_comp_dgFunctor, Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul,
      ← Int.negOnePow_add, show n * k + n * m = n * l by rw [← h]; ring]
  map_id X := by
    change (n * 0).negOnePow • (Cochain.ofHom (𝟙 (show CochainComplex B ℤ from X))).shift n =
      Cochain.ofHom (𝟙 ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) n).obj X))
    rw [Cochain.shift_ofHom_id_dgFunctor, mul_zero, Int.negOnePow_zero, one_smul]

/-- `CochainComplex.dgShiftFunctor B n` is Mathlib's shift on objects. -/
@[simp] theorem dgShiftFunctor_obj (n : ℤ) (X : CochainComplex B ℤ) :
    (dgShiftFunctor B n).obj X = (CategoryTheory.shiftFunctor (CochainComplex B ℤ) n).obj X :=
  rfl

/-- `CochainComplex.dgShiftFunctor B n` sends a cochain of degree `k` to its shift multiplied by
`(-1)^(n * k)`. -/
@[simp] theorem dgShiftFunctor_map (n : ℤ) {X Y : CochainComplex B ℤ} {k : ℤ}
    (f : Cochain X Y k) :
    (dgShiftFunctor B n).map f = (n * k).negOnePow • f.shift n :=
  rfl

end CochainComplex

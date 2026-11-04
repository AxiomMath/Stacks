module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift

/-!
# Cancelling a shift of a differential graded module

Shifting a right differential graded module by `-k` and then by `k` returns the module one
started from: the underlying right module and the grading come back on the nose, and the two
signs `(-1)^{-k}` and `(-1)^k` picked up by the differential cancel. This file records that
identification as an isomorphism in `Mod_{(A,d)}`, together with the fact that a homomorphism
of `k`-shifts is already a homomorphism of the unshifted modules.

## Main definitions

* `DifferentialGradedModule.shiftShiftNegIso`: the isomorphism `(M[-k])[k] ≅ M`.
* `DifferentialGradedModule.Hom.unshift`: a homomorphism `M[k] ⟶ N[k]`, read as a homomorphism
  `M ⟶ N`.

## Main results

* `DifferentialGradedModule.shiftShiftNegIso_hom_toFun` and
  `DifferentialGradedModule.Hom.unshift_toFun`: neither construction changes the underlying
  `R`-linear map.

## Implementation notes

Both constructions are the identity on underlying linear maps, so the content is entirely in the
grading and differential conditions. The grading of `(M[-k])[k]` in degree `n` is
`M.grading ((n + k) + -k)`, which `omega` reduces to `M.grading n`; the differential is
`(-1)^k • ((-1)^{-k} • d)`, and `Int.negOnePow_add` collapses the two units. `Hom.unshift`
divides the compatibility with the differentials by the unit `(-1)^k`, which is where
`smul_left_cancel_iff` is used: the shifted compatibility is the unshifted one scaled by that
unit, so no sign survives in the conclusion.

Shifting by `k` and then by `-k` is the same statement with `k` negated, so only one of the two
directions is recorded.

## References

* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- A homomorphism of the `k`-shifts of two differential graded modules is a homomorphism of the
modules themselves, with the same underlying `R`-linear map. -/
def Hom.unshift {M N : DifferentialGradedModule A} (k : ℤ)
    (f : Hom (shift M k) (shift N k)) : Hom M N where
  toFun := f.toFun
  map_smul := f.map_smul
  map_grading := by
    intro n x hx
    have hn : n - k + k = n := by omega
    have hx' : x ∈ (shift M k).grading (n - k) := by
      change x ∈ M.grading (n - k + k)
      rw [hn]
      exact hx
    have h := f.map_grading (n - k) x hx'
    change f.toFun x ∈ N.grading (n - k + k) at h
    rwa [hn] at h
  map_d := by
    ext x
    have h := LinearMap.congr_fun f.map_d x
    rw [shift_d, shift_d] at h
    change f.toFun (k.negOnePow • M.d x) = k.negOnePow • N.d (f.toFun x) at h
    rw [Units.smul_def, map_zsmul, Units.smul_def] at h
    exact (smul_left_cancel_iff k.negOnePow).mp h

/-- `Hom.unshift` does not change the underlying `R`-linear map. -/
@[simp] theorem Hom.unshift_toFun {M N : DifferentialGradedModule A} (k : ℤ)
    (f : Hom (shift M k) (shift N k)) : (Hom.unshift k f).toFun = f.toFun := rfl

/-- Shifting by `-k` and then by `k` is the identity: `(M[-k])[k] ≅ M`, by the identity map. -/
noncomputable def shiftShiftNegIso (M : DifferentialGradedModule A) (k : ℤ) :
    shift (shift M (-k)) k ≅ M where
  hom :=
    { toFun := LinearMap.id
      map_smul := by intro x a; rfl
      map_grading := by
        intro n x hx
        have hn : n + k + -k = n := by omega
        simpa only [shift_grading, hn, LinearMap.id_coe, id_eq] using hx
      map_d := by
        ext x
        change (shift (shift M (-k)) k).d x = M.d x
        rw [shift_d, shift_d]
        change k.negOnePow • ((-k).negOnePow • M.d x) = M.d x
        rw [smul_smul, ← Int.negOnePow_add, show k + -k = 0 by omega]
        simp }
  inv :=
    { toFun := LinearMap.id
      map_smul := by intro x a; rfl
      map_grading := by
        intro n x hx
        have hn : n + k + -k = n := by omega
        simpa only [shift_grading, hn, LinearMap.id_coe, id_eq] using hx
      map_d := by
        ext x
        change M.d x = (shift (shift M (-k)) k).d x
        rw [shift_d, shift_d]
        change M.d x = k.negOnePow • ((-k).negOnePow • M.d x)
        rw [smul_smul, ← Int.negOnePow_add, show k + -k = 0 by omega]
        simp }
  hom_inv_id := by apply Hom.ext; rfl
  inv_hom_id := by apply Hom.ext; rfl

/-- The forward map of `shiftShiftNegIso M k` is the identity on underlying modules. -/
@[simp] theorem shiftShiftNegIso_hom_toFun (M : DifferentialGradedModule A) (k : ℤ) :
    (shiftShiftNegIso M k).hom.toFun = LinearMap.id := rfl

/-- The inverse map of `shiftShiftNegIso M k` is the identity on underlying modules. -/
@[simp] theorem shiftShiftNegIso_inv_toFun (M : DifferentialGradedModule A) (k : ℤ) :
    (shiftShiftNegIso M k).inv.toFun = LinearMap.id := rfl

end DifferentialGradedModule

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Shifts of differential graded modules

The shift `M[k]` of a right differential graded module `M` by an integer `k` has the same
underlying right module, the reindexed grading `M[k]^n = M^{n+k}`, and the differential
`(-1)^k • d`. The construction is functorial: a homomorphism of differential graded modules is
also a homomorphism of the shifts, with the same underlying linear map.

## Main definitions

* `DifferentialGradedModule.shift`: the shifted differential graded module `M[k]`.
* `DifferentialGradedModule.shiftMap`: a homomorphism viewed as a homomorphism of shifts.
* `DifferentialGradedModule.shiftFunctor`: shifting by a fixed integer, as a functor on
  `Mod_{(A,d)}`.

## Main results

* `DifferentialGradedModule.shift_grading` and `DifferentialGradedModule.shift_d` give the
  grading and the differential of a shift.
* `DifferentialGradedModule.shiftFunctor_map_toFun`: the shift functor does not change the
  underlying linear map of a morphism.

## Implementation notes

The grading of the shift is obtained from that of `M` by composing with the equivalence
`n ↦ n + k` of `ℤ`, so its direct-sum decomposition is transported along that equivalence; the
shifted module and the shift functor are implicitly reducible, so their projections reduce
definitionally. The sign is written with `Int.negOnePow`, acting through the canonical
action of units, matching the chapter's convention for `(-1)^k` with `k : ℤ`.

## References

* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- The `k`-shifted differential graded module `M[k]`: degree `n` is the old degree `n + k`,
the differential is multiplied by `(-1)^k`, and the right algebra action is unchanged. -/
@[stacks 09JL "the shifted module", implicit_reducible]
noncomputable def shift (M : DifferentialGradedModule A) (k : ℤ) :
    DifferentialGradedModule A where
  M := M.M
  grading n := M.grading (n + k)
  decomposition := by
    let e : ℤ ≃ ℤ := Equiv.addRight k
    have h : DirectSum.IsInternal (M.grading ∘ e) := by
      have h0 := DirectSum.Decomposition.isInternal M.grading
      rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h0 ⊢
      obtain ⟨hind, hsup⟩ := h0
      refine ⟨hind.comp e.injective, ?_⟩
      rw [← hsup]
      exact e.iSup_comp (g := M.grading)
    exact (show DirectSum.IsInternal (fun n => M.grading (n + k)) from h).chooseDecomposition
  smul_mem := by
    intro n m x a hx ha
    convert M.smul_mem (n + k) m x a hx ha using 1
    congr 1
    omega
  d := k.negOnePow • M.d
  d_comp_d := by
    ext x
    have hd : M.d (M.d x) = 0 := LinearMap.congr_fun M.d_comp_d x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Units.smul_def,
      map_zsmul, hd, smul_zero, LinearMap.zero_apply]
  d_mem := by
    intro n x hx
    rw [LinearMap.smul_apply, Units.smul_def]
    convert zsmul_mem (M.d_mem (n + k) x hx) _ using 1
    congr 1
    omega
  leibniz := by
    intro n m x a hx ha
    simp only [LinearMap.smul_apply]
    rw [M.leibniz (n + k) m x a hx ha, smul_add]
    congr 1
    · rw [Units.smul_def, Units.smul_def]
      exact (map_zsmul (DistribSMul.toAddMonoidHom M.M (MulOpposite.op a))
        (k.negOnePow : ℤ) (M.d x)).symm
    · rw [Units.smul_def, smul_smul]
      congr 1
      norm_cast
      rw [Int.negOnePow_add, mul_comm, mul_assoc, Int.units_mul_self, mul_one]

/-- The degree-`n` part of `M[k]` is the degree-`n + k` part of `M`. -/
@[simp] theorem shift_grading (M : DifferentialGradedModule A) (k n : ℤ) :
    (shift M k).grading n = M.grading (n + k) := rfl

/-- The differential of `M[k]` is the differential of `M` multiplied by `(-1)^k`. -/
@[simp] theorem shift_d (M : DifferentialGradedModule A) (k : ℤ) :
    (shift M k).d = k.negOnePow • M.d := rfl

/-- A homomorphism of differential graded modules, viewed as a homomorphism of their `k`-shifts
by the same underlying linear map. -/
@[stacks 09JL "the shifted homomorphism"]
def shiftMap {M N : DifferentialGradedModule A} (f : Hom M N) (k : ℤ) :
    Hom (shift M k) (shift N k) where
  toFun := f.toFun
  map_smul := f.map_smul
  map_grading := fun n x hx => f.map_grading (n + k) x hx
  map_d := by
    ext x
    change f.toFun (k.negOnePow • M.d x) = k.negOnePow • N.d (f.toFun x)
    rw [Units.smul_def, map_zsmul, ← Units.smul_def]
    exact congrArg (fun y => k.negOnePow • y)
      ((LinearMap.congr_fun f.map_d x) : f.toFun (M.d x) = N.d (f.toFun x))

/-- The shift of a homomorphism has the same underlying linear map as the homomorphism. -/
@[simp] theorem shiftMap_toFun {M N : DifferentialGradedModule A} (f : Hom M N) (k : ℤ) :
    (shiftMap f k).toFun = f.toFun := rfl

/-- Shifting by `k`, as a functor on the category of differential graded modules. -/
@[stacks 09JL "the shift functor", implicit_reducible]
noncomputable def shiftFunctor (A : DifferentialGradedAlgebra R) (k : ℤ) :
    DifferentialGradedModule A ⥤ DifferentialGradedModule A where
  obj M := shift M k
  map f := shiftMap f k
  map_id M := by
    change shiftMap (Hom.id M) k = Hom.id (shift M k)
    apply Hom.ext
    rfl
  map_comp f g := by
    change shiftMap (Hom.comp g f) k = Hom.comp (shiftMap g k) (shiftMap f k)
    apply Hom.ext
    rfl

/-- The shift functor by `k` sends a differential graded module `M` to `M[k]`. -/
@[simp] theorem shiftFunctor_obj (A : DifferentialGradedAlgebra R) (k : ℤ)
    (M : DifferentialGradedModule A) : (shiftFunctor A k).obj M = shift M k := rfl

/-- The shift functor by `k` does not change the underlying linear map of a morphism. -/
@[simp] theorem shiftFunctor_map_toFun (A : DifferentialGradedAlgebra R) (k : ℤ)
    {M N : DifferentialGradedModule A} (f : M ⟶ N) :
    ((shiftFunctor A k).map f).toFun = f.toFun := rfl

end DifferentialGradedModule

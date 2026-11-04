module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift
public import StacksFrontier.Algebra.DirectSum.RangeGrading

/-!
# The graded module of homogeneous maps between differential graded modules

For right differential graded `A`-modules `L` and `M`, the homogeneous right `A`-linear maps
`L → M` of all degrees assemble into the graded `R`-module
`Hom^•(L, M) = ⨁_{n} Hom^n(L, M)`, carrying the differential of the differential graded category
of differential graded modules summand by summand. This file builds that total module and its
differential, and records how it interacts with reindexing of degrees and with shifting the
target.

The right action of a differential graded algebra on `Hom^•(L, M)` exists only when `L` carries a
compatible left action, so it is not part of this file; what is here is the underlying graded
`R`-module with its differential, which is what every such construction starts from.

## Main definitions

* `DifferentialGradedModule.homogeneousMapDifferentialₗ`: the differential on degree-`n`
  homogeneous maps, as an `R`-linear map.
* `DifferentialGradedModule.HomTotal`: the total module `⨁_n Hom^n(L, M)`.
* `DifferentialGradedModule.homTotalDifferential`: its differential.
* `DifferentialGradedModule.homogeneousMapCongr`: reindexing homogeneous maps along an equality
  of degrees.
* `DifferentialGradedModule.homogeneousMapShiftEquiv`: a degree-`n` homogeneous map into `M[k]`
  is a degree-`n + k` homogeneous map into `M`.

## Main results

* `DifferentialGradedModule.homTotalDifferential_of` and
  `DifferentialGradedModule.homTotalDifferential_mem`: the differential acts summandwise and
  raises the degree by one.
* `DifferentialGradedModule.homTotalDifferential_comp_self`: it squares to zero.
* `DifferentialGradedModule.homogeneousMapShiftEquiv_differential`: shifting the target
  multiplies the differential of a homogeneous map by `(-1)^k`.

## Implementation notes

The grading of `HomTotal A L M` is the tautological grading `DirectSum.rangeGrading` of a direct
sum by the ranges of its summand inclusions, so no separate family of submodules is introduced
here.

`homogeneousMapCongr` transports along an equality of degrees without changing the underlying
linear map, which is what lets the Leibniz computations be stated as equations in a single
degree; `homogeneousMapCongr_heq` is the form in which it feeds
`DirectSum.of_eq_of_gradedMonoid_eq`.

The differential of `Hom^n(L, M[k])` differs from that of `Hom^{n+k}(L, M)` by the single factor
`(-1)^k` coming from the differential of the shift, with no dependence on `n`: the two signs
`(-1)^n` and `(-1)^{n+k}` attached to the two terms of the graded commutator differ by exactly
that factor, which is `DifferentialGraded.gradedSign_add` together with the fact that the sign
squares to one.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL)
-/

@[expose] public section

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- The differential of the differential graded category of differential graded modules, as an
`R`-linear map on degree-`n` homogeneous maps. -/
def homogeneousMapDifferentialₗ {L M : DifferentialGradedModule A} (n : ℤ) :
    HomogeneousMap A L M n →ₗ[R] HomogeneousMap A L M (n + 1) where
  toFun := homogeneousMapDifferential A
  map_add' f g := (dgCategory A).d_add f g
  map_smul' r f := (dgCategory A).d_smul r f

/-- `homogeneousMapDifferentialₗ` is the differential of the differential graded category. -/
@[simp] theorem homogeneousMapDifferentialₗ_apply {L M : DifferentialGradedModule A} (n : ℤ)
    (f : HomogeneousMap A L M n) :
    homogeneousMapDifferentialₗ A n f = homogeneousMapDifferential A f := rfl

/-- The total module `Hom^•(L, M) = ⨁_n Hom^n(L, M)` of homogeneous right `A`-linear maps from
`L` to `M`. -/
abbrev HomTotal (L M : DifferentialGradedModule A) : Type u :=
  DirectSum ℤ fun n => HomogeneousMap A L M n

variable {A}

/-- The differential of `Hom^•(L, M)`: the differential of the differential graded category,
applied summand by summand. -/
def homTotalDifferential (L M : DifferentialGradedModule A) :
    HomTotal A L M →ₗ[R] HomTotal A L M :=
  DirectSum.toModule R ℤ _ fun n =>
    (DirectSum.lof R ℤ (fun n => HomogeneousMap A L M n) (n + 1)).comp
      (homogeneousMapDifferentialₗ A n)

/-- On the summand of degree `n`, the differential of `Hom^•(L, M)` is the differential of
`Hom^n(L, M)`, landing in the summand of degree `n + 1`. -/
@[simp] theorem homTotalDifferential_of {L M : DifferentialGradedModule A} (n : ℤ)
    (f : HomogeneousMap A L M n) :
    homTotalDifferential L M (DirectSum.of (fun n => HomogeneousMap A L M n) n f) =
      DirectSum.of (fun n => HomogeneousMap A L M n) (n + 1) (homogeneousMapDifferential A f) := by
  show (DirectSum.toModule R ℤ (HomTotal A L M) fun i =>
      (DirectSum.lof R ℤ (fun j => HomogeneousMap A L M j) (i + 1)).comp
        (homogeneousMapDifferentialₗ A i))
      (DirectSum.lof R ℤ (fun i => HomogeneousMap A L M i) n f) = _
  rw [DirectSum.toModule_lof R (φ := fun i =>
    (DirectSum.lof R ℤ (fun j => HomogeneousMap A L M j) (i + 1)).comp
      (homogeneousMapDifferentialₗ A i)) n f]
  rfl

/-- The differential of `Hom^•(L, M)` raises the degree by one. -/
theorem homTotalDifferential_mem {L M : DifferentialGradedModule A} (n : ℤ)
    (x : HomTotal A L M) (hx : x ∈ DirectSum.rangeGrading R (fun n => HomogeneousMap A L M n) n) :
    homTotalDifferential L M x ∈
      DirectSum.rangeGrading R (fun n => HomogeneousMap A L M n) (n + 1) := by
  rcases hx with ⟨f, rfl⟩
  refine ⟨homogeneousMapDifferential A f, ?_⟩
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, homTotalDifferential_of]

/-- The differential of `Hom^•(L, M)` squares to zero. -/
theorem homTotalDifferential_comp_self (L M : DifferentialGradedModule A) :
    (homTotalDifferential L M).comp (homTotalDifferential L M) = 0 := by
  ext n f : 2
  show homTotalDifferential L M (homTotalDifferential L M (DirectSum.of _ n f)) = 0
  rw [homTotalDifferential_of, homTotalDifferential_of,
    show homogeneousMapDifferential A (homogeneousMapDifferential A f) = 0 from
      (dgCategory A).d_d f]
  simp

/-! ### Reindexing the degree -/

/-- Homogeneous maps of equal degrees are identified, without changing the underlying linear
map. -/
def homogeneousMapCongr {L M : DifferentialGradedModule A} {m n : ℤ} (h : m = n) :
    HomogeneousMap A L M m ≃ₗ[R] HomogeneousMap A L M n where
  toFun f := ⟨f.1, h ▸ f.2⟩
  invFun f := ⟨f.1, h.symm ▸ f.2⟩
  left_inv f := by cases h; rfl
  right_inv f := by cases h; rfl
  map_add' f g := Subtype.ext rfl
  map_smul' r f := Subtype.ext rfl

/-- `homogeneousMapCongr` does not change the underlying linear map. -/
@[simp] theorem homogeneousMapCongr_val {L M : DifferentialGradedModule A} {m n : ℤ} (h : m = n)
    (f : HomogeneousMap A L M m) : (homogeneousMapCongr h f : L.M →ₗ[R] M.M) = f.1 := rfl

/-- A homogeneous map is heterogeneously equal to its reindexing along an equality of degrees. -/
theorem homogeneousMapCongr_heq {L M : DifferentialGradedModule A} {m n : ℤ} (h : m = n)
    (f : HomogeneousMap A L M m) : HEq f (homogeneousMapCongr h f) := by
  cases h; rfl

/-- Two homogeneous maps of equal degrees with the same underlying linear map are heterogeneously
equal. This is the form `DirectSum.of_eq_of_gradedMonoid_eq` consumes. -/
theorem homogeneousMap_heq_of_val_eq {L M : DifferentialGradedModule A} {m n : ℤ} (h : m = n)
    (f : HomogeneousMap A L M m) (g : HomogeneousMap A L M n) (hv : f.1 = g.1) : HEq f g := by
  cases h
  exact heq_of_eq (Subtype.ext hv)

/-- Scalar multiplication of a homogeneous map by an integer cast agrees with the integer
scalar multiplication. -/
theorem homogeneousMap_intCast_smul {L M : DifferentialGradedModule A} {n : ℤ} (z : ℤ)
    (f : HomogeneousMap A L M n) : (z : R) • f = z • f :=
  Subtype.ext <| LinearMap.ext fun x => Int.cast_smul_eq_zsmul R z (f.1 x)

/-! ### Shifting the target -/

private theorem gradedSign_mul_self (k : ℤ) :
    DifferentialGraded.gradedSign R k * DifferentialGraded.gradedSign R k = 1 := by
  rw [DifferentialGraded.gradedSign, ← pow_add, ← two_mul, pow_mul]
  simp

/-- A degree-`n` homogeneous map into the shift `M[k]` is exactly a degree-`n + k` homogeneous
map into `M`, by the same underlying linear map. -/
def homogeneousMapShiftEquiv {L M : DifferentialGradedModule A} (k n : ℤ) :
    HomogeneousMap A L (shift M k) n ≃ₗ[R] HomogeneousMap A L M (n + k) where
  toFun f :=
    ⟨f.1, by
      refine ⟨fun i x hx => ?_, fun a x => f.2.2 a x⟩
      have h := f.2.1 i x hx
      change f.1 x ∈ M.grading (i + n + k) at h
      simpa only [add_assoc] using h⟩
  invFun f :=
    ⟨f.1, by
      refine ⟨fun i x hx => ?_, fun a x => f.2.2 a x⟩
      have h := f.2.1 i x hx
      change f.1 x ∈ (shift M k).grading (i + n)
      simpa only [shift_grading, add_assoc] using h⟩
  left_inv f := Subtype.ext rfl
  right_inv f := Subtype.ext rfl
  map_add' f g := Subtype.ext rfl
  map_smul' r f := Subtype.ext rfl

/-- `homogeneousMapShiftEquiv` does not change the underlying linear map. -/
@[simp] theorem homogeneousMapShiftEquiv_val {L M : DifferentialGradedModule A} (k n : ℤ)
    (f : HomogeneousMap A L (shift M k) n) :
    (homogeneousMapShiftEquiv k n f : L.M →ₗ[R] M.M) = f.1 := rfl

/-- The inverse of `homogeneousMapShiftEquiv` does not change the underlying linear map. -/
@[simp] theorem homogeneousMapShiftEquiv_symm_val {L M : DifferentialGradedModule A} (k n : ℤ)
    (f : HomogeneousMap A L M (n + k)) :
    (((homogeneousMapShiftEquiv (M := M) k n).symm f).1 : L.M →ₗ[R] M.M) = f.1 := rfl

/-- The differential of a homogeneous map into a shift is the differential of the corresponding
homogeneous map into the unshifted module, times the sign `(-1)^k` of the shift. -/
theorem homogeneousMapShiftEquiv_differential {L M : DifferentialGradedModule A} (k n : ℤ)
    (f : HomogeneousMap A L (shift M k) n) :
    homogeneousMapShiftEquiv k (n + 1) (homogeneousMapDifferential A f) =
      homogeneousMapCongr (show n + k + 1 = n + 1 + k by omega)
        (DifferentialGraded.gradedSign R k •
          homogeneousMapDifferential A (homogeneousMapShiftEquiv k n f)) := by
  apply Subtype.ext
  show (homogeneousMapDifferential A f).1 =
    DifferentialGraded.gradedSign R k •
      (homogeneousMapDifferential A (homogeneousMapShiftEquiv k n f)).1
  ext x
  simp only [homogeneousMapDifferential_val, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, shift_d, homogeneousMapShiftEquiv_val]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow,
    smul_sub, smul_smul, DifferentialGraded.gradedSign_add,
    show DifferentialGraded.gradedSign R k *
        (DifferentialGraded.gradedSign R n * DifferentialGraded.gradedSign R k) =
      DifferentialGraded.gradedSign R n from by
      rw [show DifferentialGraded.gradedSign R k *
          (DifferentialGraded.gradedSign R n * DifferentialGraded.gradedSign R k) =
        DifferentialGraded.gradedSign R k * DifferentialGraded.gradedSign R k *
          DifferentialGraded.gradedSign R n from by ac_rfl, gradedSign_mul_self, one_mul]]

end DifferentialGradedModule

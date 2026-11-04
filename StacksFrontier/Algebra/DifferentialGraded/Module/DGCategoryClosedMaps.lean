module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Homotopy
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift

/-!
# Closed and null-homotopic homogeneous maps of differential graded modules

The degree-`n` part of the differential graded Hom module of two right differential graded
modules consists of the homogeneous right `A`-linear maps of degree `n`, and its differential is
the signed commutator with the module differentials. Such a map is *closed* for that differential
exactly when it is a homomorphism of differential graded modules into the `n`-shift of its
target, and it is a *boundary* exactly when the corresponding homomorphism into the shift is
null-homotopic. Together these identify the degree-`n` cohomology of the Hom module with the
homotopy classes of homomorphisms into the shift.

## Main results

* `DifferentialGradedModule.homogeneousMapDifferential_eq_zero_iff_exists_hom_shift`:
  the closed homogeneous maps are the homomorphisms into the shifted target.
* `DifferentialGradedModule.homotopic_zero_iff_exists_homogeneousMapDifferential`:
  the boundaries are the maps whose homomorphism into the shift is null-homotopic.

## Implementation notes

The `n`-shift of the target has the same underlying module as the target, so the homomorphism
in the first result is required to have exactly the given underlying linear map. In the second
result the homomorphism into the shift is a hypothesis together with that equality, and equality
of boundaries is stated on underlying linear maps, which identifies the degrees `(n - 1) + 1` and
`n` without a cast.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public section

universe u

namespace DifferentialGradedModule

open DifferentialGraded

variable {R : Type u} [CommRing R]

private theorem gradedSign_mul_self (n : ℤ) : gradedSign R n * gradedSign R n = 1 := by
  simp only [gradedSign, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

private theorem gradedSign_one : gradedSign R 1 = -1 := by
  rw [show (1 : ℤ) = 0 + 1 from rfl, gradedSign_succ, gradedSign_zero]

private theorem gradedSign_sub_one_mul (n : ℤ) :
    gradedSign R (n - 1) * gradedSign R n = -1 := by
  have h : gradedSign R n = gradedSign R (n - 1) * gradedSign R 1 := by
    rw [← gradedSign_add]; congr 1; omega
  rw [h, gradedSign_one, ← mul_assoc, gradedSign_mul_self, one_mul]

private theorem neg_gradedSign_sub_one (n : ℤ) :
    -gradedSign R (n - 1) = gradedSign R n := by
  calc
    -gradedSign R (n - 1) =
        -gradedSign R (n - 1) * (gradedSign R n * gradedSign R n) := by
          rw [gradedSign_mul_self, mul_one]
    _ = gradedSign R n := by
      rw [← mul_assoc, neg_mul, gradedSign_sub_one_mul, neg_neg, one_mul]

/-- The differential of the `n`-shift is the differential multiplied by the sign of `n`. -/
private theorem shift_d_apply {A : DifferentialGradedAlgebra R} (M : DifferentialGradedModule A)
    (n : ℤ) (x : M.M) : (shift M n).d x = gradedSign R n • M.d x := by
  simp only [shift_d, LinearMap.smul_apply, Units.smul_def]
  rw [← Int.cast_smul_eq_zsmul R, intCast_negOnePow]

variable (A : DifferentialGradedAlgebra R)

/-- A homogeneous map is closed for the Hom differential if and only if it is a homomorphism
into the shifted target, with the same underlying linear map. -/
@[stacks 09LC "closed_maps"]
theorem homogeneousMapDifferential_eq_zero_iff_exists_hom_shift
    (L M : DifferentialGradedModule A) (n : ℤ) (f : HomogeneousMap A L M n) :
    homogeneousMapDifferential A f = 0 ↔
      ∃ g : Hom L (shift M n), g.toFun = f.1 := by
  constructor
  · intro h
    have hmap : M.d ∘ₗ f.1 = gradedSign R n • (f.1 ∘ₗ L.d) :=
      sub_eq_zero.mp (congrArg Subtype.val h)
    refine ⟨{
      toFun := f.1
      map_smul := fun x a => f.2.2 a x
      map_grading i x hx := by simpa only [shift_grading] using f.2.1 i x hx
      map_d := ?_
    }, rfl⟩
    ext x
    show f.1 (L.d x) = (shift M n).d (f.1 x)
    have hpoint := LinearMap.congr_fun hmap x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hpoint
    rw [shift_d_apply, hpoint, smul_smul, gradedSign_mul_self, one_smul]
  · rintro ⟨g, hg⟩
    apply Subtype.ext
    ext x
    have hpoint : f.1 (L.d x) = gradedSign R n • M.d (f.1 x) := by
      simpa only [hg, LinearMap.comp_apply, shift_d_apply] using LinearMap.congr_fun g.map_d x
    show M.d (f.1 x) - gradedSign R n • f.1 (L.d x) = 0
    rw [hpoint, smul_smul, gradedSign_mul_self, one_smul, sub_self]

/-- A closed homogeneous map is a boundary exactly when the corresponding homomorphism into the
shifted target is homotopic to zero. -/
@[stacks 09LC "boundaries_homotopies"]
theorem homotopic_zero_iff_exists_homogeneousMapDifferential
    {L M : DifferentialGradedModule A} {n : ℤ}
    (f : HomogeneousMap A L M n) (F : Hom L (shift M n)) (hF : F.toFun = f.1) :
    Homotopic F 0 ↔
      ∃ g : HomogeneousMap A L M (n - 1), (homogeneousMapDifferential A g).1 = f.1 := by
  constructor
  · rintro ⟨h⟩
    let hR : L.M →ₗ[R] M.M := h.toLinearMap.restrictScalars R
    let g : HomogeneousMap A L M (n - 1) :=
      ⟨gradedSign R n • hR, by
        constructor
        · intro i x hx
          rw [LinearMap.smul_apply]
          apply (M.grading (i + (n - 1))).smul_mem _
          show h.toLinearMap x ∈ M.grading (i + (n - 1))
          simpa only [shift_grading, show (i - 1) + n = i + (n - 1) by omega] using
            h.map_grading i x hx
        · intro a x
          have hR_apply (y : L.M) : hR y = h.toLinearMap y := rfl
          simp only [LinearMap.smul_apply]
          rw [hR_apply, hR_apply, h.toLinearMap.map_smul, smul_comm]⟩
    refine ⟨g, ?_⟩
    ext x
    have heq := h.homotopy_eq x
    change F.toFun x - (0 : (shift M n).M) =
      (shift M n).d (h.toLinearMap x) + h.toLinearMap (L.d x) at heq
    rw [homogeneousMapDifferential_val]
    show M.d ((gradedSign R n • hR) x) -
        gradedSign R (n - 1) • ((gradedSign R n • hR) (L.d x)) = f.1 x
    simp only [LinearMap.smul_apply]
    rw [M.d.map_smul, smul_smul]
    have hR_apply (y : L.M) : hR y = h.toLinearMap y := rfl
    have heq' : f.1 x = gradedSign R n • M.d (hR x) + hR (L.d x) := by
      simpa only [hF, sub_zero, hR_apply, shift_d_apply, LinearMap.zero_apply] using heq
    rw [sub_eq_add_neg, ← neg_smul, gradedSign_sub_one_mul, neg_neg, one_smul]
    exact heq'.symm
  · rintro ⟨g, hg⟩
    let hmap : L.M →ₗ[MulOpposite A.A] (shift M n).M :=
      { toFun := fun x => gradedSign R n • g.1 x
        map_add' x y := by simp [smul_add]
        map_smul' a x := by
          show gradedSign R n • g.1 (a • x) = a • (gradedSign R n • g.1 x)
          have hA : g.1 (a • x) = a • g.1 x := by
            simpa only [MulOpposite.op_unop] using g.2.2 (MulOpposite.unop a) x
          rw [hA, smul_comm] }
    refine ⟨{
      toLinearMap := hmap
      map_grading i x hx := by
        show gradedSign R n • g.1 x ∈ (shift M n).grading (i - 1)
        apply (M.grading ((i - 1) + n)).smul_mem _
        rw [show (i - 1) + n = i + (n - 1) by omega]
        exact g.2.1 i x hx
      homotopy_eq x := by
        have hval := congrArg (fun q : L.M →ₗ[R] M.M => q x) hg
        simp only [homogeneousMapDifferential_val, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smul_apply] at hval
        show F.toFun x - (0 : (shift M n).M) =
          (shift M n).d (hmap x) + hmap (L.d x)
        rw [hF]
        rw [shift_d_apply]
        show f.1 x - (0 : M.M) =
          gradedSign R n • M.d (gradedSign R n • g.1 x) + gradedSign R n • g.1 (L.d x)
        rw [M.d.map_smul, smul_smul, gradedSign_mul_self, one_smul, sub_zero]
        rw [sub_eq_add_neg, ← neg_smul, neg_gradedSign_sub_one] at hval
        simpa using hval.symm }⟩

end DifferentialGradedModule

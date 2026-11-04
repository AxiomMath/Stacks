module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Koszul contraction and the exterior power of `M × R`

For a linear functional `φ : M →ₗ[R] R` this file builds the contraction
`exteriorPower.contraction φ n : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M`, the left wedge multiplication
`exteriorPower.wedgeLeft e n : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M` by a vector `e`, and the Koszul
identity relating them. Taking `φ` to be a projection with `φ e = 1` turns the identity into a
splitting, which yields `⋀[R]^(p + 1) (M × R) ≃ ⋀[R]^(p + 1) M × ⋀[R]^p M`.

## Main definitions

* `exteriorPower.contraction`: contraction of `⋀[R]^(n + 1) M` against `φ : M →ₗ[R] R`.
* `exteriorPower.wedgeLeft`: left multiplication `x ↦ e ∧ x` on exterior powers.
* `exteriorPower.prodRightEquiv`: the decomposition
  `⋀[R]^(p + 1) (M × R) ≃ₗ[R] ⋀[R]^(p + 1) M × ⋀[R]^p M`, with
  `exteriorPower.prodRightZeroEquiv` the degenerate case `p = 0`.

## Main results

* `exteriorPower.contraction_comp_contraction`: the contraction squares to zero.
* `exteriorPower.wedgeLeft_comp_wedgeLeft`: wedging twice with the same vector is zero.
* `exteriorPower.contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction`: the **Koszul
  identity** `ι_φ ∘ (e ∧ ·) + (e ∧ ·) ∘ ι_φ = φ e • id`.
* `AlternatingMap.map_add_smul_const`: expansion of an alternating map along a single direction,
  `f (b + t • e) = f b + ∑ i, t i • f (update b i e)`.
-/

@[expose] public section

open Function

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable {ι : Type*}

/-- An alternating map vanishes on a family having two distinct entries proportional to a common
vector. -/
theorem map_eq_zero_of_eq_smul (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) (e : M) {i j : ι} (hij : i ≠ j)
    {a b : R} (hi : v i = a • e) (hj : v j = b • e) : f v = 0 := by
  classical
  calc f v = f (update v i (a • e)) := by rw [← hi, update_eq_self]
    _ = a • f (update v i e) := f.map_update_smul _ _ _ _
    _ = a • f (update (update v i e) j (b • e)) := by
      rw [← hj, ← update_of_ne hij.symm e v, update_eq_self]
    _ = a • b • f (update (update v i e) j e) := by rw [f.map_update_smul]
    _ = 0 := by
      rw [f.map_eq_zero_of_eq _ (i := i) (j := j) (by simp [hij]) hij, smul_zero, smul_zero]

variable [DecidableEq ι] [Fintype ι]

/-- Expansion of an alternating map along a single direction `e`:
`f (b + t • e) = f b + ∑ i, t i • f (update b i e)`. -/
theorem map_add_smul_const (f : M [⋀^ι]→ₗ[R] N) (b : ι → M) (t : ι → R) (e : M) :
    f (fun i ↦ b i + t i • e) = f b + ∑ i, t i • f (update b i e) := by
  have hvanish : ∀ s : Finset ι, 2 ≤ s.card →
      f (s.piecewise (fun i ↦ t i • e) b) = 0 := by
    intro s hs
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs
    exact f.map_eq_zero_of_eq_smul _ e hij (Finset.piecewise_eq_of_mem _ _ _ hi)
      (Finset.piecewise_eq_of_mem _ _ _ hj)
  have hsum := f.toMultilinearMap.map_add_eq_map_add_linearDeriv_add b (fun i ↦ t i • e)
  simp only [AlternatingMap.coe_multilinearMap, MultilinearMap.linearDeriv_apply] at hsum
  rw [show (fun i ↦ b i + t i • e) = b + fun i ↦ t i • e from rfl, hsum,
    Finset.sum_eq_zero fun s hs ↦ hvanish s (Finset.mem_filter.mp hs).2, add_zero]
  exact congrArg (f b + ·) (Finset.sum_congr rfl fun i _ ↦ f.map_update_smul _ _ _ _)

end AlternatingMap

namespace exteriorPower

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Two linear maps on `⋀[R]^n M` are equal if they agree on all `ιMulti R n v`. -/
private theorem linearMap_ext_ιMulti {n : ℕ} {f g : ⋀[R]^n M →ₗ[R] N}
    (h : ∀ v, f (ιMulti R n v) = g (ιMulti R n v)) : f = g :=
  linearMap_ext (AlternatingMap.ext h)

/-! ### Contraction against a linear functional -/

/-- Contraction of the `(n + 1)`-st exterior power against a linear functional `φ`: the unique
linear map sending `m₀ ∧ ⋯ ∧ mₙ` to `∑ i, (-1) ^ i • φ (mᵢ) • (m₀ ∧ ⋯ ∧ m̂ᵢ ∧ ⋯ ∧ mₙ)`. -/
@[sga "7 XII 1.3.1"]
noncomputable def contraction (φ : M →ₗ[R] R) (n : ℕ) :
    ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin
    (LinearMap.smulRight φ (ιMulti R n : M [⋀^Fin n]→ₗ[R] ⋀[R]^n M)))

/-- The contraction of `v₀ ∧ ⋯ ∧ vₙ` against `φ` is
`∑ i, (-1) ^ i • φ (vᵢ) • (v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ)`. -/
@[simp]
theorem contraction_ιMulti (φ : M →ₗ[R] R) (n : ℕ) (v : Fin (n + 1) → M) :
    contraction φ n (ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • φ (v i) • ιMulti R n (i.removeNth v) := by
  rw [contraction, alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.alternatizeUncurryFin_apply]
  simp [LinearMap.smulRight_apply]

/-- The Koszul contraction squares to zero. -/
theorem contraction_comp_contraction (φ : M →ₗ[R] R) (n : ℕ) :
    contraction φ n ∘ₗ contraction φ (n + 1) = 0 := by
  set w : M [⋀^Fin n]→ₗ[R] ⋀[R]^n M := ιMulti R n with hw
  set b : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] ⋀[R]^n M :=
    LinearMap.smulRight φ (LinearMap.smulRight φ w) with hb
  have hbapply (p q : M) : b p q = (φ p * φ q) • w := by
    simp only [hb, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]
  have hbsymm : ∀ x y, b x y = b y x := fun x y ↦ by rw [hbapply, hbapply, mul_comm]
  have hzero :=
    AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric hbsymm
  refine linearMap_ext_ιMulti fun v ↦ ?_
  have key : ∀ u : Fin (n + 1) → M, contraction φ n (ιMulti R (n + 1) u) =
      AlternatingMap.alternatizeUncurryFin (LinearMap.smulRight φ w) u :=
    fun u ↦ alternatingMapLinearEquiv_apply_ιMulti _ u
  have h := DFunLike.congr_fun hzero v
  rw [AlternatingMap.zero_apply] at h
  simp only [LinearMap.coe_comp, comp_apply,
    LinearMap.zero_apply, contraction_ιMulti, map_sum, map_zsmul, map_smul, key]
  rw [← h, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.comp_apply, AlternatingMap.alternatizeUncurryFinLM_apply, hb,
    LinearMap.smulRight_apply, AlternatingMap.alternatizeUncurryFin_smul,
    AlternatingMap.smul_apply]

/-! ### Left wedge multiplication -/

/-- Left multiplication by a vector `e`, as a linear map `⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M`. -/
@[ega "III 1.1.7"]
noncomputable def wedgeLeft (e : M) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M :=
  alternatingMapLinearEquiv
    ((ιMulti R (n + 1) : M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^(n + 1) M).curryLeft e)

/-- Wedging `v₀ ∧ ⋯ ∧ vₙ₋₁` with `e` on the left gives `e ∧ v₀ ∧ ⋯ ∧ vₙ₋₁`. -/
@[simp]
theorem wedgeLeft_ιMulti (e : M) (n : ℕ) (v : Fin n → M) :
    wedgeLeft e n (ιMulti R n v) = ιMulti R (n + 1) (Fin.cons e v) := by
  rw [wedgeLeft, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Left wedge multiplication, read in the exterior algebra: it is multiplication by `ι R e`. -/
@[simp, ega "III 1.1.7"]
theorem coe_wedgeLeft (e : M) (n : ℕ) (x : ⋀[R]^n M) :
    (wedgeLeft e n x : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M) := by
  have key : (⋀[R]^(n + 1) M).subtype ∘ₗ wedgeLeft (R := R) e n =
      LinearMap.mulLeft R (ExteriorAlgebra.ι R e) ∘ₗ (⋀[R]^n M).subtype := by
    ext v
    simp [wedgeLeft_ιMulti, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  exact LinearMap.congr_fun key x

/-- Wedging twice with the same vector is zero. -/
theorem wedgeLeft_comp_wedgeLeft (e : M) (n : ℕ) :
    wedgeLeft (R := R) e (n + 1) ∘ₗ wedgeLeft e n = 0 := by
  refine linearMap_ext_ιMulti fun v ↦ ?_
  simp only [LinearMap.coe_comp, comp_apply,
    wedgeLeft_ιMulti, LinearMap.zero_apply]
  refine (ιMulti R (n + 2)).map_eq_zero_of_eq (Fin.cons e (Fin.cons e v)) (i := 0)
    (j := Fin.succ 0) ?_ ?_ <;> simp

/-! ### The Koszul identity -/

/-- The Koszul identity: the anticommutator of contraction against `φ` and wedge multiplication by
`e` is multiplication by the scalar `φ e`. -/
@[ega "III 1.1.7" "partial"]
theorem contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction (φ : M →ₗ[R] R) (e : M)
    (n : ℕ) :
    contraction φ (n + 1) ∘ₗ wedgeLeft e (n + 1) + wedgeLeft e n ∘ₗ contraction φ n =
      φ e • LinearMap.id (R := R) (M := ⋀[R]^(n + 1) M) := by
  refine linearMap_ext_ιMulti fun v ↦ ?_
  have hrm (i : Fin (n + 1)) :
      Fin.removeNth i.succ (Fin.cons (α := fun _ ↦ M) e v) = Fin.cons e (i.removeNth v) :=
    Fin.cons_comp_succ_succAbove e v i
  have hfirst : contraction φ (n + 1) (wedgeLeft e (n + 1) (ιMulti R (n + 1) v)) =
      φ e • ιMulti R (n + 1) v -
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • φ (v i) •
          ιMulti R (n + 1) (Fin.cons e (i.removeNth v)) := by
    rw [wedgeLeft_ιMulti, contraction_ιMulti, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.cons_zero, Fin.removeNth_zero,
      Fin.tail_cons, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul, hrm,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  have hsecond : wedgeLeft e n (contraction φ n (ιMulti R (n + 1) v)) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • φ (v i) •
        ιMulti R (n + 1) (Fin.cons e (i.removeNth v)) := by
    rw [contraction_ιMulti, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, map_smul, wedgeLeft_ιMulti]
  simp only [LinearMap.add_apply, LinearMap.coe_comp,
    comp_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, hfirst, hsecond, sub_add_cancel]

/-- The degree-zero case of the Koszul identity: on `⋀[R]^0 M` contraction after wedging with `e`
is multiplication by `φ e`. -/
theorem contraction_comp_wedgeLeft_zero (φ : M →ₗ[R] R) (e : M) :
    contraction φ 0 ∘ₗ wedgeLeft e 0 = φ e • LinearMap.id (R := R) (M := ⋀[R]^0 M) := by
  refine linearMap_ext_ιMulti fun v ↦ ?_
  have hv : Fin.removeNth (0 : Fin 1) (Fin.cons (α := fun _ ↦ M) e v) = v :=
    funext fun i ↦ i.elim0
  simp only [LinearMap.coe_comp, comp_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, wedgeLeft_ιMulti, contraction_ιMulti,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero,
    one_zsmul, Fin.cons_zero, hv]

/-! ### Interaction with functoriality -/

/-- Contraction against `φ` kills the image of a map whose composite with `φ` vanishes. -/
theorem contraction_comp_map (φ : N →ₗ[R] R) (f : M →ₗ[R] N) (hf : φ ∘ₗ f = 0) (n : ℕ) :
    contraction φ n ∘ₗ map (n + 1) f = 0 := by
  refine linearMap_ext_ιMulti fun v ↦ ?_
  have hf' (m : M) : φ (f m) = 0 := LinearMap.congr_fun hf m
  simp only [LinearMap.coe_comp, comp_apply,
    LinearMap.zero_apply, map_apply_ιMulti, contraction_ιMulti, hf', zero_smul, smul_zero,
    Finset.sum_const_zero]

/-- A map killing `e` kills everything divisible by `e`. -/
theorem map_comp_wedgeLeft (g : M →ₗ[R] N) (e : M) (hge : g e = 0) (n : ℕ) :
    map (n + 1) g ∘ₗ wedgeLeft e n = 0 := by
  refine linearMap_ext_ιMulti fun v ↦ ?_
  simp only [LinearMap.coe_comp, comp_apply,
    wedgeLeft_ιMulti, map_apply_ιMulti, LinearMap.zero_apply]
  exact (ιMulti R (n + 1)).map_coord_zero 0 (by simp [hge])

/-- If `φ e = 1` and `φ ∘ f = 0`, then contracting against `φ` undoes wedging with `e` on the image
of `f`. -/
theorem contraction_comp_wedgeLeft_comp_map (φ : N →ₗ[R] R) (f : M →ₗ[R] N) (e : N)
    (he : φ e = 1) (hf : φ ∘ₗ f = 0) (n : ℕ) :
    contraction φ n ∘ₗ wedgeLeft e n ∘ₗ map n f = map n f := by
  refine linearMap_ext_ιMulti fun v ↦ ?_
  have hf' (m : M) : φ (f m) = 0 := LinearMap.congr_fun hf m
  simp only [LinearMap.coe_comp, comp_apply,
    map_apply_ιMulti, wedgeLeft_ιMulti, contraction_ιMulti, Fin.sum_univ_succ, Fin.val_zero,
    pow_zero, Fin.cons_zero, he, one_smul, Fin.cons_succ, hf', zero_smul, smul_zero,
    Finset.sum_const_zero, add_zero, Fin.removeNth_zero, Fin.tail_cons]

/-! ### The exterior power of a module with a free rank-one summand -/

section Prod

variable (R M)

/-- The map `⋀[R]^(p + 1) M × ⋀[R]^p M →ₗ[R] ⋀[R]^(p + 1) (M × R)` assembling a form pulled back
along `M → M × R` and a form wedged with the generator `(0, 1)` of the free summand. -/
noncomputable def prodRightMk (n : ℕ) :
    ⋀[R]^(n + 1) M × ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) (M × R) :=
  LinearMap.coprod (map (n + 1) (LinearMap.inl R M R))
    (wedgeLeft ((0, 1) : M × R) n ∘ₗ map n (LinearMap.inl R M R))

/-- The map `⋀[R]^(p + 1) (M × R) →ₗ[R] ⋀[R]^(p + 1) M × ⋀[R]^p M` given by pushing forward along
the projection `M × R → M`, together with the same after contracting against `M × R → R`. -/
noncomputable def prodRightProj (n : ℕ) :
    ⋀[R]^(n + 1) (M × R) →ₗ[R] ⋀[R]^(n + 1) M × ⋀[R]^n M :=
  (map (n + 1) (LinearMap.fst R M R)).prod
    (map n (LinearMap.fst R M R) ∘ₗ contraction (LinearMap.snd R M R) n)

/-- `exteriorPower.prodRightProj` is a left inverse of `exteriorPower.prodRightMk`. -/
theorem prodRightProj_comp_prodRightMk (n : ℕ) :
    prodRightProj R M n ∘ₗ prodRightMk R M n = LinearMap.id := by
  have hsi : LinearMap.snd R M R ∘ₗ LinearMap.inl R M R = 0 := LinearMap.ext fun _ ↦ rfl
  have hfi : LinearMap.fst R M R ∘ₗ LinearMap.inl R M R = LinearMap.id :=
    LinearMap.ext fun _ ↦ rfl
  have hid (k : ℕ) (z : ⋀[R]^k M) :
      map k (LinearMap.fst R M R) (map k (LinearMap.inl R M R) z) = z := by
    rw [← LinearMap.comp_apply, ← map_comp, hfi, map_id, LinearMap.id_apply]
  have hwedge (z : ⋀[R]^n (M × R)) :
      map (n + 1) (LinearMap.fst R M R) (wedgeLeft ((0, 1) : M × R) n z) = 0 := by
    rw [← LinearMap.comp_apply, map_comp_wedgeLeft (LinearMap.fst R M R) _ rfl n,
      LinearMap.zero_apply]
  have hcontr (z : ⋀[R]^(n + 1) M) :
      contraction (LinearMap.snd R M R) n (map (n + 1) (LinearMap.inl R M R) z) = 0 := by
    rw [← LinearMap.comp_apply, contraction_comp_map _ _ hsi n, LinearMap.zero_apply]
  have hundo (z : ⋀[R]^n M) :
      contraction (LinearMap.snd R M R) n
          (wedgeLeft ((0, 1) : M × R) n (map n (LinearMap.inl R M R) z)) =
        map n (LinearMap.inl R M R) z := by
    simpa only [LinearMap.coe_comp, comp_apply] using DFunLike.congr_fun
      (contraction_comp_wedgeLeft_comp_map (LinearMap.snd R M R) (LinearMap.inl R M R)
        ((0, 1) : M × R) rfl hsi n) z
  refine LinearMap.ext fun p ↦ Prod.ext ?_ ?_
  · show map (n + 1) (LinearMap.fst R M R) (prodRightMk R M n p) = p.1
    rw [prodRightMk, LinearMap.coprod_apply, map_add, hid, LinearMap.comp_apply, hwedge, add_zero]
  · show map n (LinearMap.fst R M R)
      (contraction (LinearMap.snd R M R) n (prodRightMk R M n p)) = p.2
    rw [prodRightMk, LinearMap.coprod_apply, map_add, hcontr, LinearMap.comp_apply, hundo,
      zero_add, hid]

/-- `exteriorPower.prodRightProj` is a right inverse of `exteriorPower.prodRightMk`. -/
theorem prodRightMk_comp_prodRightProj (n : ℕ) :
    prodRightMk R M n ∘ₗ prodRightProj R M n = LinearMap.id := by
  refine linearMap_ext_ιMulti fun u ↦ ?_
  set e : M × R := (0, 1) with he
  set b : Fin (n + 1) → M × R := fun i ↦ LinearMap.inl R M R (u i).1 with hb
  set t : Fin (n + 1) → R := fun i ↦ (u i).2 with ht
  have hu : (fun i ↦ b i + t i • e) = u := by
    funext i
    refine Prod.ext ?_ ?_ <;> simp [hb, ht, he]
  have hsnd (i : Fin (n + 1)) : LinearMap.snd R M R (u i) = t i := rfl
  have hcomp (i : Fin (n + 1)) :
      (LinearMap.inl R M R) ∘ ((LinearMap.fst R M R) ∘ i.removeNth u) = i.removeNth b := rfl
  have hsign (i : Fin (n + 1)) :
      (-1 : ℤ) ^ (i : ℕ) • ιMulti R (n + 1) (Fin.cons e (i.removeNth b)) =
        ιMulti R (n + 1) (update b i e) := by
    rw [show (Fin.cons e (i.removeNth b) : Fin (n + 1) → M × R) =
        Matrix.vecCons e (i.removeNth b) from rfl,
      ← AlternatingMap.neg_one_pow_smul_map_insertNth (ιMulti R (n + 1)) i e (i.removeNth b),
      smul_smul, ← pow_add, Even.neg_one_pow ⟨(i : ℕ), rfl⟩, one_smul, Fin.insertNth_removeNth]
  have hleft : map (n + 1) (LinearMap.inl R M R)
      (map (n + 1) (LinearMap.fst R M R) (ιMulti R (n + 1) u)) = ιMulti R (n + 1) b := by
    rw [map_apply_ιMulti, map_apply_ιMulti]
    rfl
  have hright : wedgeLeft e n (map n (LinearMap.inl R M R) (map n (LinearMap.fst R M R)
      (contraction (LinearMap.snd R M R) n (ιMulti R (n + 1) u)))) =
      ∑ i : Fin (n + 1), t i • ιMulti R (n + 1) (update b i e) := by
    rw [contraction_ιMulti, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_zsmul, map_smul, map_apply_ιMulti, wedgeLeft_ιMulti, hsnd, hcomp]
    rw [smul_comm, hsign]
  have hmk (w : ⋀[R]^(n + 1) (M × R)) :
      prodRightMk R M n (prodRightProj R M n w) =
        map (n + 1) (LinearMap.inl R M R) (map (n + 1) (LinearMap.fst R M R) w) +
          wedgeLeft e n (map n (LinearMap.inl R M R) (map n (LinearMap.fst R M R)
            (contraction (LinearMap.snd R M R) n w))) := rfl
  show prodRightMk R M n (prodRightProj R M n (ιMulti R (n + 1) u)) = ιMulti R (n + 1) u
  rw [hmk, hleft, hright, ← AlternatingMap.map_add_smul_const (ιMulti R (n + 1)) b t e, hu]

/-- The splitting `⋀[R]^(n + 1) (M × R) ≃ₗ[R] ⋀[R]^(n + 1) M × ⋀[R]^n M` of the exterior power of a
module with a free rank-one summand, given by contraction against the projection `M × R → R` and
wedging with the generator `(0, 1)`. -/
noncomputable def prodRightEquiv (n : ℕ) :
    ⋀[R]^(n + 1) (M × R) ≃ₗ[R] ⋀[R]^(n + 1) M × ⋀[R]^n M :=
  LinearEquiv.ofLinearMap (prodRightProj R M n) (prodRightMk R M n)
    (prodRightProj_comp_prodRightMk R M n) (prodRightMk_comp_prodRightProj R M n)

/-- The components of `exteriorPower.prodRightEquiv`: the pushforward along `M × R → M`, and the
pushforward of the contraction against `M × R → R`. -/
@[simp]
theorem prodRightEquiv_apply (n : ℕ) (x : ⋀[R]^(n + 1) (M × R)) :
    prodRightEquiv R M n x =
      (map (n + 1) (LinearMap.fst R M R) x,
        map n (LinearMap.fst R M R) (contraction (LinearMap.snd R M R) n x)) :=
  rfl

/-- The inverse of `exteriorPower.prodRightEquiv` sends `(x, y)` to the pullback of `x` along
`M → M × R` plus the pullback of `y` wedged with `(0, 1)`. -/
@[simp]
theorem prodRightEquiv_symm_apply (n : ℕ) (p : ⋀[R]^(n + 1) M × ⋀[R]^n M) :
    (prodRightEquiv R M n).symm p =
      map (n + 1) (LinearMap.inl R M R) p.1 +
        wedgeLeft ((0, 1) : M × R) n (map n (LinearMap.inl R M R) p.2) :=
  rfl

/-- The identification `⋀[R]^0 (M × R) ≃ₗ[R] ⋀[R]^0 M` of zeroth exterior powers, both being
identified with `R`. -/
noncomputable def prodRightZeroEquiv : ⋀[R]^0 (M × R) ≃ₗ[R] ⋀[R]^0 M :=
  (zeroEquiv (R := R) (M := M × R)).trans (zeroEquiv (R := R) (M := M)).symm

end Prod

end exteriorPower

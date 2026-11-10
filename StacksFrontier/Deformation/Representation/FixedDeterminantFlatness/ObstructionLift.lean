module

public import Mathlib.RingTheory.Filtration
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.Tangent
public import StacksFrontier.Deformation.Representation.FixedDeterminantFlatness.AdjointRepresentation

/-!
# Lifting the universal representation along a presentation of the deformation ring

Preparations for the obstruction theory of a fixed-determinant universal deformation ring `R`:

* the universal representation may be conjugated so that it reduces to `ρ₀` on the nose;
* for an ideal `J` of a local ring with a minimal generating family `f₁, …, f_r`, the
  *coefficient functionals* `φ_a(∑ pᵢ fᵢ) = ∑ aᵢ p̄ᵢ`, for `a ∈ 𝐅_ℓ^r`, are well defined on `J`,
  additive, semilinear for the residue map and zero on `𝔪 J`;
* along a surjection `F : P → R` from a local `ℤ_[ℓ]`-algebra, the universal representation has a
  set-theoretic lift `ρ̃ : π → GLₙ(P)` with determinant `δ` whose reduction modulo any ideal
  containing a power of `𝔪_P` is locally constant.

## Main definitions

* `IsLocalRing.coeffFunctional`: the coefficient functional `φ_a` on `J`.

## Main results

* `Deformation.IsUniversalFixedDeterminantDeformation.exists_reduce_eq`: the universal
  representation may be chosen to reduce to `ρ₀` exactly.
* `IsLocalRing.coeffFunctional_eq_zero_of_mem`: the coefficient functionals vanish on `𝔪 J`.
* `Deformation.IsUniversalFixedDeterminantDeformation.exists_lift`: a lift of the universal
  representation along a surjection, with determinant `δ` and locally constant reductions.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Deformation

/-! ### Conjugating the universal representation -/

/-- Conjugating `σ` by a fixed matrix `Q` does not change whether it is conjugate to `ρ`. -/
lemma isConjugate_conj_iff {G : Type*} {n : ℕ} {R : Type*} [CommRing R]
    (σ ρ : G → Matrix.GeneralLinearGroup (Fin n) R) (Q : Matrix.GeneralLinearGroup (Fin n) R) :
    IsConjugate (fun g => Q * σ g * Q⁻¹) ρ ↔ IsConjugate σ ρ := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P * Q, fun g => by rw [hP g]; group⟩
  · rintro ⟨P, hP⟩
    exact ⟨P * Q⁻¹, fun g => by rw [hP g]; group⟩

/-- A square matrix over a local ring is invertible as soon as its image under a local
surjection is. -/
private theorem isUnit_det_of_map_aux {P S : Type*} [CommRing P] [IsLocalRing P] [CommRing S]
    [IsLocalRing S] {m : ℕ} (F : P →+* S) (hF : Function.Surjective F)
    (M : Matrix (Fin m) (Fin m) P) (hM : IsUnit (M.map F).det) : IsUnit M.det := by
  by_contra hne
  have hm := Ideal.mem_map_of_mem F ((mem_maximalIdeal M.det).mpr hne)
  rw [map_maximalIdeal_of_surjective F hF, RingHom.map_det] at hm
  exact (mem_maximalIdeal _).mp hm hM

/-- An invertible matrix over `S` lifts along a local surjection `F : P → S`, entrywise via any
set-theoretic section `lift`. -/
private theorem exists_gl_lift_entries {P S : Type*} [CommRing P] [IsLocalRing P] [CommRing S]
    [IsLocalRing S] {m : ℕ} (F : P →+* S) (hF : Function.Surjective F) (lift : S → P)
    (hlift : ∀ x, F (lift x) = x) (A : Matrix.GeneralLinearGroup (Fin m) S) :
    ∃ B : Matrix.GeneralLinearGroup (Fin m) P, Matrix.GeneralLinearGroup.map F B = A ∧
      ∀ i j, (B : Matrix (Fin m) (Fin m) P) i j = lift ((A : Matrix (Fin m) (Fin m) S) i j) := by
  let M : Matrix (Fin m) (Fin m) P := fun i j => lift ((A : Matrix (Fin m) (Fin m) S) i j)
  have hMF : M.map F = A := by
    ext i j
    exact hlift _
  refine ⟨Matrix.nonsingInvUnit M (isUnit_det_of_map_aux F hF M ?_), Units.ext hMF, fun _ _ => rfl⟩
  rw [hMF]
  exact (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit

namespace IsUniversalFixedDeterminantDeformation

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [tR : TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

/-- A universal fixed-determinant deformation ring is a topological ring. -/
lemma isTopologicalRing (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) :
    IsTopologicalRing R :=
  h.isAdicTopology ▸ (maximalIdeal R).ringFilterBasis.isTopologicalRing

/-- **The universal representation may be taken to reduce to `ρ₀` on the nose.** -/
theorem exists_reduce_eq (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) :
    ∃ ρu : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R,
      IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρu ∧
        ∀ g, Matrix.GeneralLinearGroup.map reduce (ρu g) = ρ₀ g := by
  classical
  have := h.isTopologicalRing
  obtain ⟨P₀, hP₀⟩ := h.reduce_rep
  obtain ⟨Q, hQ, -⟩ := exists_gl_lift_entries reduce h.reduce_surjective
    (Function.surjInv h.reduce_surjective) (Function.surjInv_eq h.reduce_surjective) P₀
  let ρu : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R :=
    { toMonoidHom := (MulAut.conj Q).toMonoidHom.comp ρuniv.toMonoidHom
      continuous_toFun := by
        change Continuous fun g => Q * ρuniv g * Q⁻¹
        exact (continuous_const.mul ρuniv.continuous).mul continuous_const }
  have hρu : ∀ g, ρu g = Q * ρuniv g * Q⁻¹ := fun g => rfl
  have hred : ∀ g, Matrix.GeneralLinearGroup.map reduce (ρu g) = ρ₀ g := by
    intro g
    rw [hρu, map_mul, map_mul, map_inv, hQ]
    exact (hP₀ g).symm
  refine ⟨ρu, ⟨h.delta_reduce, h.isAdicTopology, h.isAdicComplete, h.reduce_surjective,
    h.reduce_continuous, h.reduce_algebraMap, ⟨1, fun g => by simp [hred]⟩, fun g => ?_,
    ?_⟩, hred⟩
  · rw [hρu, map_mul, map_mul, map_inv, h.det_rep g,
      mul_comm (Matrix.GeneralLinearGroup.det Q), mul_assoc, mul_inv_cancel, mul_one]
  · intro S _ _ tS _ htS hcS red hred1 hred2 hred3 ρ hρ hdetρ
    obtain ⟨ψ, ⟨hψc, hψ⟩, huniq⟩ := h.universal S htS hcS red hred1 hred2 hred3 ρ hρ hdetρ
    have key : ∀ ψ' : R →ₐ[ℤ_[ℓ]] S,
        IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ'.toRingHom (ρu g)) (fun g => ρ g) ↔
        IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ'.toRingHom (ρuniv g))
          (fun g => ρ g) := by
      intro ψ'
      have : (fun g => Matrix.GeneralLinearGroup.map ψ'.toRingHom (ρu g)) =
          fun g => Matrix.GeneralLinearGroup.map ψ'.toRingHom Q *
            Matrix.GeneralLinearGroup.map ψ'.toRingHom (ρuniv g) *
            (Matrix.GeneralLinearGroup.map ψ'.toRingHom Q)⁻¹ := by
        funext g
        rw [hρu, map_mul, map_mul, map_inv]
      rw [this, isConjugate_conj_iff]
    exact ⟨ψ, ⟨hψc, (key ψ).mpr hψ⟩, fun ψ' ⟨hc', h'⟩ => huniq ψ' ⟨hc', (key ψ').mp h'⟩⟩

end IsUniversalFixedDeterminantDeformation

end Deformation

/-! ### Coefficient functionals of a minimal generating family -/

namespace IsLocalRing

variable {ℓ : ℕ} {P : Type*} [CommRing P] [IsLocalRing P] (res : P →+* ZMod ℓ)
  (hres : RingHom.ker res = maximalIdeal P) {r : ℕ} (f : Fin r → P)
  (hmin : ∀ p : Fin r → P, ∑ i, p i * f i = 0 → ∀ i, p i ∈ maximalIdeal P)

/-- Coefficients of an element of `J = (f₁, …, f_r)` in terms of the generators (a choice). -/
def coeffs (x : P) : Fin r → P := by
  classical
  exact if hx : x ∈ Ideal.span (Set.range f) then
    ((Submodule.mem_span_range_iff_exists_fun P).mp hx).choose else 0

omit [IsLocalRing P] in
/-- An element `x` of `J = (f₁, …, f_r)` equals `∑ coeffs f x i * f i`. -/
lemma sum_coeffs {x : P} (hx : x ∈ Ideal.span (Set.range f)) :
    ∑ i, coeffs f x i * f i = x := by
  classical
  unfold coeffs
  rw [dite_eq_left hx]
  simpa [smul_eq_mul] using ((Submodule.mem_span_range_iff_exists_fun P).mp hx).choose_spec

/-- **Coefficient functional** `φ_a(∑ pᵢ fᵢ) = ∑ aᵢ res(pᵢ)`. -/
def coeffFunctional (a : Fin r → ZMod ℓ) (x : P) : ZMod ℓ := ∑ i, a i * res (coeffs f x i)

include hres hmin in
/-- `φ_a(x) = ∑ aᵢ res(pᵢ)` for any expression `x = ∑ pᵢ fᵢ`. -/
lemma coeffFunctional_eq {x : P} (p : Fin r → P) (hp : ∑ i, p i * f i = x) (a : Fin r → ZMod ℓ) :
    coeffFunctional res f a x = ∑ i, a i * res (p i) := by
  have hx : x ∈ Ideal.span (Set.range f) := hp ▸ Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have h0 : ∑ i, (coeffs f x i - p i) * f i = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, sum_coeffs f hx, hp, sub_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have : coeffs f x i - p i ∈ RingHom.ker res := hres ▸ hmin _ h0 i
  rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this

include hres hmin in
/-- The coefficient functional `φ_a` is additive on `J`. -/
lemma coeffFunctional_add {x y : P} (hx : x ∈ Ideal.span (Set.range f))
    (hy : y ∈ Ideal.span (Set.range f)) (a : Fin r → ZMod ℓ) :
    coeffFunctional res f a (x + y) = coeffFunctional res f a x + coeffFunctional res f a y := by
  rw [coeffFunctional_eq res hres f hmin (fun i => coeffs f x i + coeffs f y i)
    (by simp only [add_mul, Finset.sum_add_distrib, sum_coeffs f hx, sum_coeffs f hy])]
  simp only [coeffFunctional, map_add, mul_add, Finset.sum_add_distrib]

include hres hmin in
/-- `φ_a(p x) = res(p) φ_a(x)` for `p ∈ P` and `x ∈ J`. -/
lemma coeffFunctional_mul (p : P) {x : P} (hx : x ∈ Ideal.span (Set.range f))
    (a : Fin r → ZMod ℓ) :
    coeffFunctional res f a (p * x) = res p * coeffFunctional res f a x := by
  rw [coeffFunctional_eq res hres f hmin (fun i => p * coeffs f x i)
    (by simp only [mul_assoc, ← Finset.mul_sum, sum_coeffs f hx])]
  simp only [coeffFunctional, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

include hres hmin in
/-- The coefficient functional `φ_a` vanishes at `0`. -/
lemma coeffFunctional_zero (a : Fin r → ZMod ℓ) : coeffFunctional res f a 0 = 0 := by
  rw [coeffFunctional_eq res hres f hmin 0 (by simp)]
  simp

include hres hmin in
/-- `φ_a(f_k) = a_k`. -/
lemma coeffFunctional_generator (a : Fin r → ZMod ℓ) (k : Fin r) :
    coeffFunctional res f a (f k) = a k := by
  classical
  rw [coeffFunctional_eq res hres f hmin (Pi.single k 1) (by
    simp [Pi.single_apply, Finset.sum_ite_eq'])]
  simp [Pi.single_apply, Finset.sum_ite_eq']

omit [IsLocalRing P] in
/-- `φ_{a + b} = φ_a + φ_b`. -/
lemma coeffFunctional_add_left (a b : Fin r → ZMod ℓ) (x : P) :
    coeffFunctional res f (a + b) x = coeffFunctional res f a x + coeffFunctional res f b x := by
  simp only [coeffFunctional, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [IsLocalRing P] in
/-- `φ_{c • a} = c φ_a`. -/
lemma coeffFunctional_smul_left (c : ZMod ℓ) (a : Fin r → ZMod ℓ) (x : P) :
    coeffFunctional res f (c • a) x = c * coeffFunctional res f a x := by
  simp only [coeffFunctional, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [IsLocalRing P] in
/-- `φ_{∑ c_j • a_j} = ∑ c_j φ_{a_j}`. -/
lemma coeffFunctional_sum_left {s : ℕ} (c : Fin s → ZMod ℓ) (a : Fin s → Fin r → ZMod ℓ)
    (x : P) : coeffFunctional res f (∑ j, c j • a j) x =
      ∑ j, c j * coeffFunctional res f (a j) x := by
  simp only [coeffFunctional, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

include hres hmin in
/-- The coefficient functionals vanish on `𝔪 J`. -/
lemma coeffFunctional_eq_zero_of_mem (a : Fin r → ZMod ℓ) {x : P}
    (hx : x ∈ maximalIdeal P * Ideal.span (Set.range f)) : coeffFunctional res f a x = 0 := by
  have hJ : maximalIdeal P * Ideal.span (Set.range f) ≤ Ideal.span (Set.range f) :=
    Submodule.mul_le.mpr fun q _ j hj => Ideal.mul_mem_left _ q hj
  refine Submodule.mul_induction_on' (C := fun x _ => coeffFunctional res f a x = 0)
    (fun q hq j hj => ?_) (fun x hx y hy hx' hy' => ?_) hx
  · rw [coeffFunctional_mul res hres f hmin q hj,
      RingHom.mem_ker.mp (hres ▸ hq : q ∈ RingHom.ker res), zero_mul]
  · rw [coeffFunctional_add res hres f hmin (hJ hx) (hJ hy), hx', hy', add_zero]

/-- Along a surjection `F : P → S` of local rings there is a set-theoretic section whose values on
elements congruent modulo `𝔪_S ^ k` are congruent modulo `𝔪_P ^ k`. -/
lemma exists_section_sub_mem_pow {P S : Type*} [CommRing P] [IsLocalRing P] [CommRing S]
    [IsLocalRing S] (F : P →+* S) (hF : Function.Surjective F) (k : ℕ) :
    ∃ lift : S → P, (∀ x, F (lift x) = x) ∧ ∀ x x',
      Ideal.Quotient.mk (maximalIdeal S ^ k) x = Ideal.Quotient.mk (maximalIdeal S ^ k) x' →
        lift x - lift x' ∈ maximalIdeal P ^ k := by
  classical
  let rep : S → S := fun x => Function.surjInv Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (maximalIdeal S ^ k) x)
  have hc : ∀ x, ∃ c ∈ maximalIdeal P ^ k, F c = x - rep x := fun x =>
    (Ideal.mem_map_iff_of_surjective F hF).mp <| by
      rw [Ideal.map_pow, map_maximalIdeal_of_surjective F hF, ← Ideal.Quotient.eq]
      exact (Function.surjInv_eq Ideal.Quotient.mk_surjective _).symm
  choose c hcm hcF using hc
  refine ⟨fun x => Function.surjInv hF (rep x) + c x, fun x => ?_, fun x x' hxx' => ?_⟩
  · simp only [map_add, hcF, Function.surjInv_eq hF]
    ring
  · have : rep x = rep x' := by simp only [rep, hxx']
    simpa only [this, add_sub_add_left_eq_sub] using Ideal.sub_mem _ (hcm x) (hcm x')

end IsLocalRing

/-! ### A set-theoretic lift of the universal representation -/

namespace Matrix

/-- The image of `diagonal (update 1 i₀ x)` under a ring hom `φ` is
`diagonal (update 1 i₀ (φ x))`. -/
lemma map_diagonal_update_one {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ}
    (i₀ : Fin n) (x : A) :
    (diagonal (Function.update (1 : Fin n → A) i₀ x)).map φ =
      diagonal (Function.update (1 : Fin n → B) i₀ (φ x)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = i₀
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  · simp [diagonal_apply_ne _ hij]

/-- If `φ x = 1` then `diagonal (update 1 i₀ x)` maps to `1` under `φ`. -/
lemma map_diagonal_update_one_eq_one {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {n : ℕ} (i₀ : Fin n) {x : A} (hx : φ x = 1) :
    (diagonal (Function.update (1 : Fin n → A) i₀ x)).map φ = 1 := by
  rw [map_diagonal_update_one, hx]
  simp

/-- The determinant of `diagonal (update 1 i₀ x)` is `x`. -/
lemma det_diagonal_update_one {A : Type*} [CommRing A] {n : ℕ} (i₀ : Fin n) (x : A) :
    (diagonal (Function.update (1 : Fin n → A) i₀ x)).det = x := by
  rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

end Matrix

namespace Deformation.IsUniversalFixedDeterminantDeformation

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

omit [TopologicalSpace R] in
/-- A matrix over a local ring is invertible as soon as its image under a local surjection is. -/
lemma isUnit_det_of_map {P : Type*} [CommRing P] [IsLocalRing P] (F : P →+* R)
    (hF : Function.Surjective F) (M : Matrix (Fin n) (Fin n) P)
    (hM : IsUnit (M.map F).det) : IsUnit M.det :=
  isUnit_det_of_map_aux F hF M hM

/-- Along a surjection `F : P → R`, the universal representation has a set-theoretic lift whose
reduction modulo an ideal containing `𝔪_P ^ k` is locally constant. -/
lemma exists_lift_isLocallyConstant
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) {P : Type*}
    [CommRing P] [IsLocalRing P] (F : P →+* R) (hF : Function.Surjective F) (Q : Ideal P)
    (k : ℕ) (hQ : maximalIdeal P ^ k ≤ Q) :
    ∃ U : π → Matrix.GeneralLinearGroup (Fin n) P,
      (∀ g, Matrix.GeneralLinearGroup.map F (U g) = ρuniv g) ∧
      IsLocallyConstant fun g => Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q) (U g) := by
  obtain ⟨lift, hliftF, hlift⟩ := exists_section_sub_mem_pow F hF k
  choose U hUF hUlift using fun g => exists_gl_lift_entries F hF lift hliftF (ρuniv g)
  refine ⟨U, hUF, ?_⟩
  have := h.isTopologicalRing
  let : TopologicalSpace (R ⧸ maximalIdeal R ^ k) := ⊥
  have : DiscreteTopology (R ⧸ maximalIdeal R ^ k) := ⟨rfl⟩
  have hlc : IsLocallyConstant fun g => Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (maximalIdeal R ^ k)) (ρuniv g) := by
    refine (IsLocallyConstant.iff_continuous _).mpr
      ((Matrix.GeneralLinearGroup.continuous_map _ ?_).comp ρuniv.continuous)
    rw [h.isAdicTopology]
    exact RingHom.continuous_adic_of_pow_le_ker (maximalIdeal R)
      (Ideal.Quotient.mk (maximalIdeal R ^ k)) k (by rw [Ideal.mk_ker])
  rw [IsLocallyConstant.iff_exists_open]
  refine fun g₀ => ⟨{g | Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal R ^ k))
      (ρuniv g) = Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk _) (ρuniv g₀)},
    hlc.isOpen_fiber _, rfl, fun g hg => Units.ext ?_⟩
  simp only [Set.mem_ofPred_eq] at hg
  ext i j
  change Ideal.Quotient.mk Q ((U g : Matrix (Fin n) (Fin n) P) i j) =
    Ideal.Quotient.mk Q ((U g₀ : Matrix (Fin n) (Fin n) P) i j)
  rw [hUlift, hUlift]
  refine Ideal.Quotient.eq.mpr (hQ (hlift _ _ ?_))
  simpa using congrArg (fun A : Matrix.GeneralLinearGroup (Fin n) (R ⧸ maximalIdeal R ^ k) =>
    (A : Matrix (Fin n) (Fin n) (R ⧸ maximalIdeal R ^ k)) i j) hg

/-- The reduction of `δ` modulo an ideal containing `𝔪_P ^ k` is locally constant. -/
lemma isLocallyConstant_mk_algebraMap_delta
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) {P : Type*}
    [CommRing P] [IsLocalRing P] [Algebra ℤ_[ℓ] P] (F : P →+* R)
    (hFalg : ∀ c, F (algebraMap ℤ_[ℓ] P c) = algebraMap ℤ_[ℓ] R c) (Q : Ideal P) (k : ℕ)
    (hQ : maximalIdeal P ^ k ≤ Q) :
    IsLocallyConstant fun g => Ideal.Quotient.mk Q (algebraMap ℤ_[ℓ] P (δ g)) := by
  have hℓP : algebraMap ℤ_[ℓ] P ℓ ∈ maximalIdeal P := (mem_maximalIdeal _).mpr fun hu =>
    (mem_maximalIdeal _).mp h.algebraMap_mem_maximalIdeal (by rw [← hFalg]; exact hu.map F)
  rw [IsLocallyConstant.iff_exists_open]
  refine fun g₀ => ⟨(fun g => (δ g : ℤ_[ℓ])) ⁻¹'
      Metric.closedBall (δ g₀ : ℤ_[ℓ]) ((ℓ : ℝ) ^ (-(k : ℤ))),
    (IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero))).preimage
      (Units.continuous_val.comp δ.continuous),
    Metric.mem_closedBall_self (by positivity), fun g hg => Ideal.Quotient.eq.mpr ?_⟩
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] at hg
  obtain ⟨t, ht⟩ :=
    Ideal.mem_span_singleton'.mp ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).mp hg)
  rw [← map_sub, ← ht, map_mul, map_pow]
  exact hQ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hℓP k))

/-- **A lift of the universal representation along a surjection `F : P → R`** with determinant
`δ`, whose reduction modulo an ideal containing `𝔪_P ^ k` is locally constant. -/
theorem exists_lift (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (hn : 0 < n) {P : Type*} [CommRing P] [IsLocalRing P] [Algebra ℤ_[ℓ] P] (F : P →+* R)
    (hF : Function.Surjective F)
    (hFalg : ∀ c, F (algebraMap ℤ_[ℓ] P c) = algebraMap ℤ_[ℓ] R c)
    (Q : Ideal P) (k : ℕ) (hQ : maximalIdeal P ^ k ≤ Q) :
    ∃ ρt : π → Matrix.GeneralLinearGroup (Fin n) P,
      (∀ g, Matrix.GeneralLinearGroup.map F (ρt g) = ρuniv g) ∧
      (∀ g, Matrix.GeneralLinearGroup.det (ρt g) = Units.map (algebraMap ℤ_[ℓ] P) (δ g)) ∧
      IsLocallyConstant fun g => Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk Q) (ρt g) := by
  obtain ⟨U, hUF, hUlc⟩ := h.exists_lift_isLocallyConstant F hF Q k hQ
  let i₀ : Fin n := ⟨0, hn⟩
  let u : π → Pˣ := fun g => Units.map (algebraMap ℤ_[ℓ] P) (δ g) *
    (Matrix.GeneralLinearGroup.det (U g))⁻¹
  let D : π → Matrix.GeneralLinearGroup (Fin n) P := fun g =>
    Matrix.nonsingInvUnit (Matrix.diagonal (Function.update (1 : Fin n → P) i₀ (u g : P)))
      (by rw [Matrix.det_diagonal_update_one]; exact (u g).isUnit)
  have hFu : ∀ g, Units.map (F : P →* R) (u g) = 1 := fun g => by
    have hδF : Units.map (F : P →* R) (Units.map (algebraMap ℤ_[ℓ] P) (δ g)) =
        Units.map (algebraMap ℤ_[ℓ] R) (δ g) := Units.ext (hFalg _)
    simp only [u, map_mul, map_inv, hδF, ← Matrix.GeneralLinearGroup.map_det, hUF, h.det_rep,
      mul_inv_cancel]
  have hu : IsLocallyConstant fun g => Ideal.Quotient.mk Q (u g : P) := by
    convert (h.isLocallyConstant_mk_algebraMap_delta F hFalg Q k hQ).comp₂ hUlc
      fun a A => a * (((Matrix.GeneralLinearGroup.det A)⁻¹ : (P ⧸ Q)ˣ) : P ⧸ Q) using 1
    funext g
    simp [u, Matrix.GeneralLinearGroup.map_det, Units.coe_map_inv]
  refine ⟨fun g => U g * D g, fun g => ?_, fun g => ?_, ?_⟩
  · rw [map_mul, hUF, show Matrix.GeneralLinearGroup.map F (D g) = 1 from
      Units.ext (Matrix.map_diagonal_update_one_eq_one F i₀ (congrArg Units.val (hFu g))), mul_one]
  · rw [map_mul, show Matrix.GeneralLinearGroup.det (D g) = u g from
      Units.ext (Matrix.det_diagonal_update_one i₀ _)]
    simp only [u]
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  · refine IsLocallyConstant.desc _ Units.val ?_ fun _ _ => Units.ext
    convert hUlc.comp₂ hu fun A x => (A : Matrix (Fin n) (Fin n) (P ⧸ Q)) *
      Matrix.diagonal (Function.update (1 : Fin n → P ⧸ Q) i₀ x) using 1
    funext g
    simp only [Function.comp_apply, map_mul, Units.val_mul]
    congr 1
    exact Matrix.map_diagonal_update_one _ i₀ _

end Deformation.IsUniversalFixedDeterminantDeformation

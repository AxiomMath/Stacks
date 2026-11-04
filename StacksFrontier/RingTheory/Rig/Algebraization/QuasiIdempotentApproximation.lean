module

public import StacksFrontier.RingTheory.Rig.Algebraization.AlgebraicNormalBundle
public import StacksFrontier.RingTheory.Rig.Algebraization.HenselianApproximation
public import StacksFrontier.RingTheory.Rig.Algebraization.QuasiIdempotentVariety

/-!
# Approximating a formal quasi-idempotent by a henselian one

Let `A` be a Noetherian ring, `a ∈ A`, and `D` a Noetherian `A`-algebra; write `𝔡 = aD`. A
quasi-idempotent matrix `Ê` over the completion `D^∧`, `Ê² = aᶜ Ê`, is congruent modulo any
prescribed power of `𝔡` to an exact quasi-idempotent matrix over the henselization `Dʰ`.

The proof is henselian approximation (`Rig.exists_ringHom_henselization_approx`) applied to the
algebraic normal bundle `W` of the quasi-idempotent variety `{F : F² = aᶜ F}`
(`Rig.NormalBundle.QuasiIdempotent.qdata`, `Rig.NormalBundle.Data.exists_isEtaleOutside_away`):
`W` is étale off `V(a)` over `A[Z]` after inverting some `g ∈ 1 + aW`, its tautological matrix
`x'` is quasi-idempotent, and `Ê` defines a formal point `W → D^∧` with `Z ↦ Ê`, `x' ↦ Ê`, `T ↦ 0`.

## Main results

* `Rig.exists_quasiIdempotent_approx`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MvPolynomial

namespace Rig

attribute [local instance] HasDerivedCategory.standard

/-- The image of a quasi-defect under a ring map. -/
private theorem quasiDefect_map {R S : Type*} [CommRing R] [CommRing S] {ι : Type*} [Fintype ι]
    (f : R →+* S) (u : R) (M : Matrix ι ι R) :
    (NormalBundle.quasiDefect u M).map f = NormalBundle.quasiDefect (f u) (M.map f) := by
  rw [NormalBundle.quasiDefect, NormalBundle.quasiDefect, Matrix.map_sub _ (map_sub f),
    Matrix.map_mul, Matrix.map_smul' _ _ _ (map_mul f)]

/-- The polynomial lift of the normal bundle data of the quasi-idempotent variety. -/
private def qlift {A : Type u} [CommRing A] [IsNoetherianRing A] (a : A) (N c : ℕ) :
    (NormalBundle.QuasiIdempotent.qdata a N c).PolynomialLift where
  fP := NormalBundle.QuasiIdempotent.fPoly a N c
  EP := NormalBundle.QuasiIdempotent.EtPoly a N c
  f_eq := NormalBundle.QuasiIdempotent.qdata_f a N c
  Et_eq i j := by
    rw [NormalBundle.QuasiIdempotent.qdata_Et]
    rfl

open NormalBundle QuasiIdempotent in
/-- `Rig.exists_quasiIdempotent_approx` for an ideal `J` equal to `aD`. -/
private theorem exists_quasiIdempotent_approx_aux {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a : A) (N c : ℕ) (D : Type u) [CommRing D] [Algebra A D] [IsNoetherianRing D]
    (J : Ideal D) (hJ : J = (Ideal.span {a}).map (algebraMap A D)) :
    ∃ n₀ c' : ℕ, ∀ n, n₀ ≤ n →
      ∀ E : Matrix (Fin N) (Fin N) (AdicCompletion J D),
        E * E = algebraMap A (AdicCompletion J D) (a ^ c) • E →
        ∃ E₀ : Matrix (Fin N) (Fin N) (henselization D J),
          E₀ * E₀ = algebraMap D (henselization D J) (algebraMap A D (a ^ c)) • E₀ ∧
          ∀ i j, (henselizationToAdicCompletion D J).1 (E₀ i j) - E i j ∈
            (J.map (algebraMap D (AdicCompletion J D))) ^ (n - c') := by
  classical
  obtain ⟨g, hg, hEt, e, -, -⟩ := (qlift a N c).exists_isEtaleOutside_away
  have hsm : IsRigSmooth (adicCompletionObj (baseIdeal a (N * N)) (B := Localization.Away g)) :=
    isRigSmooth_of_isRigEtale _ (isRigEtale_of_algEquiv e (qdata a N c).isRigEtale)
  have hI : baseIdeal a (N * N) = Ideal.span {C a} := by
    rw [baseIdeal, Ideal.map_span, Set.image_singleton]
  have hgen : J = Ideal.span {algebraMap A D a} := by
    rw [hJ, Ideal.map_span, Set.image_singleton]
  have haJ : algebraMap A D a ∈ J := by
    rw [hJ]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self a)
  obtain ⟨n₀, c', happrox⟩ := exists_ringHom_henselization_approx (C a) _ hI
    (Localization.Away g) hEt hsm D J _ hgen
  refine ⟨n₀, c', fun n hn E hE ↦ ?_⟩
  have : IsAdicComplete (J.map (algebraMap D (AdicCompletion J D))) (AdicCompletion J D) :=
    AdicCompletion.isAdicComplete_self _ (Ideal.fg_of_isNoetherianRing _)
  -- the entries of `E`, and their approximations in `D`
  obtain ⟨e', he'⟩ : ∃ e' : Fin (N * N) → AdicCompletion J D,
      ∀ i j, e' (finProdFinEquiv (i, j)) = E i j :=
    ⟨fun v ↦ E (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2,
      fun i j ↦ by simp only [Equiv.symm_apply_apply]⟩
  have hsurj : ∀ y : AdicCompletion J D, ∃ z : D,
      algebraMap D (AdicCompletion J D) z - y ∈
        (J.map (algebraMap D (AdicCompletion J D))) ^ n := by
    intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n y)
    refine ⟨z, ?_⟩
    rw [← Ideal.map_pow,
      ← AdicCompletion.ker_evalₐ_eq_map_pow J (Ideal.fg_of_isNoetherianRing J) n, RingHom.mem_ker]
    change AdicCompletion.evalₐ J n (algebraMap D _ z - y) = 0
    rw [map_sub, (AdicCompletion.evalₐ J n).commutes]
    exact sub_eq_zero.mpr hz
  choose Z hZ using hsurj
  -- the `A[X]`-algebra structure on `D`
  let φ : MvPolynomial (Fin (N * N)) A →ₐ[A] D := aeval fun v ↦ Z (e' v)
  -- the formal point `W → D^∧`
  obtain ⟨β, hβC, hβX⟩ : ∃ β : MvPolynomial (Fin (N * N)) A →+* AdicCompletion J D,
      (∀ r, β (C r) = algebraMap A (AdicCompletion J D) r) ∧ ∀ v, β (X v) = e' v :=
    ⟨eval₂Hom (algebraMap A (AdicCompletion J D)) e', fun r ↦ eval₂Hom_C _ _ _,
      fun v ↦ eval₂Hom_X' _ _ _⟩
  obtain ⟨μ₀, hμ₀C, hμ₀X, hμ₀T⟩ : ∃ μ₀ : MvPolynomial (Fin (N * N + N * N))
      (MvPolynomial (Fin (N * N)) A) →+* AdicCompletion J D,
      (∀ x, μ₀ (C x) = β x) ∧ (∀ v, μ₀ (X (Fin.castAdd (N * N) v)) = e' v) ∧
        ∀ v, μ₀ (X (Fin.natAdd (N * N) v)) = 0 :=
    ⟨eval₂Hom β (Fin.append e' 0), fun x ↦ eval₂Hom_C _ _ _,
      fun v ↦ by rw [eval₂Hom_X', Fin.append_left],
      fun v ↦ by rw [eval₂Hom_X', Fin.append_right, Pi.zero_apply]⟩
  let κ := μ₀.comp (inclPoly (A := A) (N * N)).toRingHom
  have hκC : ∀ r, κ (C r) = algebraMap A (AdicCompletion J D) r := fun r ↦ by
    change μ₀ (inclPoly (A := A) (N * N) (C r)) = _
    rw [inclPoly_C, hμ₀C, hβC]
  have hκF : (Fpoly A N).map κ = E := Matrix.ext fun i j ↦ by
    change μ₀ (inclPoly (A := A) (N * N) (X (finProdFinEquiv (i, j)))) = _
    rw [inclPoly_X, hμ₀X, he']
  have hκG : (Gpoly a N c).map κ = 0 := by
    rw [Gpoly, quasiDefect_map, hκF, hκC, quasiDefect, ← hE, sub_self]
  have hker : (qlift a N c).idealPoly ≤ RingHom.ker μ₀ := by
    rw [Data.PolynomialLift.idealPoly, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rcases x with l | i | i
    · obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective l
      change κ (QuasiIdempotent.fPoly a N c _) = 0
      rw [fPoly_apply]
      exact congrFun (congrFun hκG i) j
    · change μ₀ ((qlift a N c).lPoly i) = 0
      rw [Data.PolynomialLift.lPoly, map_sum]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [map_mul, hμ₀T, mul_zero]
    · change μ₀ (Data.gPoly _ i) = 0
      rw [Data.gPoly, map_sub, map_sub, map_mul, hμ₀C, hβX, hμ₀X, hμ₀T, mul_zero, sub_self,
        sub_zero]
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : (qlift a N c).W →+* AdicCompletion J D,
      ∀ p, μ₁ (Ideal.Quotient.mk (qlift a N c).idealPoly p) = μ₀ p :=
    ⟨Ideal.Quotient.lift _ μ₀ hker, fun p ↦ Ideal.Quotient.lift_mk _ _ _⟩
  have hμ₁B : ∀ x, μ₁ (algebraMap (MvPolynomial (Fin (N * N)) A) (qlift a N c).W x) = β x :=
    fun x ↦ (hμ₁ (C x)).trans (hμ₀C x)
  have hle : (baseIdeal a (N * N)).map
      (algebraMap (MvPolynomial (Fin (N * N)) A) (qlift a N c).W) ≤
        (J.map (algebraMap D (AdicCompletion J D))).comap μ₁ := by
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [hI] at hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [Ideal.mem_comap, Ideal.mem_comap, hμ₁B, map_mul, hβC,
      IsScalarTower.algebraMap_apply A D (AdicCompletion J D)]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ haJ)
  have hunit : IsUnit (μ₁ g) := by
    have h0 : μ₁ (g - 1) ∈ J.map (algebraMap D (AdicCompletion J D)) := hle hg
    rw [map_sub, map_one] at h0
    exact Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (IsAdicComplete.le_jacobson_bot _ h0)
  let μ : Localization.Away g →+* AdicCompletion J D := IsLocalization.Away.lift g hunit
  have hμ : ∀ w, μ (algebraMap (qlift a N c).W (Localization.Away g) w) = μ₁ w :=
    IsLocalization.Away.lift_eq g hunit
  -- the formal point is `A[X]`-linear modulo `𝔡ⁿ`
  have hring : (Ideal.Quotient.mk ((J.map (algebraMap D (AdicCompletion J D))) ^ n)).comp β =
      (Ideal.Quotient.mk _).comp ((algebraMap D (AdicCompletion J D)).comp φ.toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun v ↦ ?_)
    · change Ideal.Quotient.mk _ (β (C r)) =
        Ideal.Quotient.mk _ (algebraMap D (AdicCompletion J D) (φ (C r)))
      rw [hβC, aeval_C, IsScalarTower.algebraMap_apply A D (AdicCompletion J D)]
    · change Ideal.Quotient.mk _ (β (X v)) =
        Ideal.Quotient.mk _ (algebraMap D (AdicCompletion J D) (φ (X v)))
      rw [hβX, aeval_X, Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]
      exact hZ _
  obtain ⟨ψ, hψB, hψ⟩ := happrox n hn φ.toRingHom.toAlgebra (aeval_C _ _) μ (fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (N * N)) A) (qlift a N c).W
      (Localization.Away g) x, hμ, hμ₁B]
    exact Ideal.Quotient.eq.mp (RingHom.congr_fun hring x))
  -- the henselian quasi-idempotent
  let π := (algebraMap (qlift a N c).W (Localization.Away g)).comp
    (Ideal.Quotient.mk (qlift a N c).idealPoly)
  let ρ := (ψ.comp π).comp (inclPoly (A := A) (N * N)).toRingHom
  have hρC : ∀ r, ρ (C r) = algebraMap D (henselization D J) (algebraMap A D r) := fun r ↦ by
    change ψ (π (inclPoly (A := A) (N * N) (C r))) = _
    rw [inclPoly_C]
    have h1 := hψB (C r)
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (N * N)) A) (qlift a N c).W
      (Localization.Away g)] at h1
    exact h1.trans (congrArg _ (aeval_C _ _))
  have hρf : ∀ l, ρ (QuasiIdempotent.fPoly a N c l) = 0 := fun l ↦ by
    change ψ (π ((qlift a N c).fPoly l)) = 0
    have hmem : (qlift a N c).fPoly l ∈ (qlift a N c).idealPoly :=
      Ideal.subset_span ⟨Sum.inl l, rfl⟩
    rw [show π ((qlift a N c).fPoly l) = 0 by
      simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr hmem], map_zero]
  refine ⟨(Fpoly A N).map ρ, ?_, fun i j ↦ ?_⟩
  · have h1 : (Gpoly a N c).map ρ = 0 := Matrix.ext fun i j ↦ by
      have h2 := hρf (finProdFinEquiv (i, j))
      rwa [fPoly_apply] at h2
    rw [Gpoly, quasiDefect_map, hρC, quasiDefect, sub_eq_zero] at h1
    exact h1
  · have h1 := hψ (π (X (Fin.castAdd (N * N) (finProdFinEquiv (i, j)))))
    rw [show ∀ p, μ (π p) = μ₀ p from fun p ↦ (hμ _).trans (hμ₁ p), hμ₀X, he'] at h1
    rw [show (Fpoly A N).map ρ i j = ψ (π (X (Fin.castAdd (N * N) (finProdFinEquiv (i, j))))) from
      congrArg (ψ.comp π) (inclPoly_X (A := A) (N * N) _)]
    exact h1

/-- **Henselian approximation of quasi-idempotents.** -/
theorem exists_quasiIdempotent_approx {A : Type u} [CommRing A] [IsNoetherianRing A] (a : A)
    (N c : ℕ) (D : Type u) [CommRing D] [Algebra A D] [IsNoetherianRing D] :
    ∃ n₀ c' : ℕ, ∀ n, n₀ ≤ n →
      ∀ E : Matrix (Fin N) (Fin N)
          (AdicCompletion ((Ideal.span {a}).map (algebraMap A D)) D),
        E * E =
          algebraMap A (AdicCompletion ((Ideal.span {a}).map (algebraMap A D)) D) (a ^ c) • E →
        ∃ E₀ : Matrix (Fin N) (Fin N) (henselization D ((Ideal.span {a}).map (algebraMap A D))),
          E₀ * E₀ = algebraMap D (henselization D ((Ideal.span {a}).map (algebraMap A D)))
            (algebraMap A D (a ^ c)) • E₀ ∧
          ∀ i j, (henselizationToAdicCompletion D ((Ideal.span {a}).map (algebraMap A D))).1
              (E₀ i j) - E i j ∈
            (((Ideal.span {a}).map (algebraMap A D)).map
              (algebraMap D (AdicCompletion ((Ideal.span {a}).map (algebraMap A D)) D))) ^
                (n - c') :=
  exists_quasiIdempotent_approx_aux a N c D _ rfl

end Rig

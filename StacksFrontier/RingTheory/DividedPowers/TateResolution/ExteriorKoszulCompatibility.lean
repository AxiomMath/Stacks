module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorDividedPowers
public import StacksFrontier.RingTheory.Koszul.DifferentialGradedAlgebra

/-! # The exterior divided powers are compatible with every Koszul differential

The divided powers of `DividedPowers.TateResolution.exteriorDividedPowerStructure` on
`⋀[R] (Fin r → R)` satisfy the compatibility `d (γₙ x) = d x · γₙ₋₁ x` of
`DividedPowers.TateResolution.IsCompatibleWithDifferential` for the contraction by any `R`-linear
functional on `Fin r → R`, hence in particular for the Koszul differential of any finite sequence
in `R`.

## Main results

* `DividedPowers.TateResolution.isCompatibleWithDifferential_exteriorDividedPowerStructure` —
  the compatibility, for every functional.
* `DividedPowers.TateResolution.exteriorProd_isCompatibleWithDifferential` — the inductive step.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u v w

section GradedFacts

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

omit [IsStrictlyGradedComm 𝒜] in
/-- The grading sign in odd degree fixes the even part. -/
public theorem signRingEquiv_apply_of_mem_evenPart (d : ℕ) {x : A} (hx : x ∈ evenPart 𝒜) :
    signRingEquiv 𝒜 d x = x := by
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
    rw [signRingEquiv_of_mem 𝒜 d (2 * k) hx, show d * (2 * k) = 2 * (d * k) by ring, pow_mul]
    simp
  | zero => simp
  | add x x' _ _ ihx ihx' => rw [_root_.map_add, ihx, ihx']

omit [GradedAlgebra 𝒜] in
/-- Two elements of the odd part of a strictly graded-commutative algebra anticommute. -/
public theorem oddPart_mul_comm_neg {x y : A} (hx : x ∈ oddPart 𝒜) (hy : y ∈ oddPart 𝒜) :
    x * y = -(y * x) := by
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem e y hy =>
      have h := IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜) hx hy
      have hpow : (2 * k + 1) * (2 * e + 1) = 2 * (2 * k * e + k + e) + 1 := by ring
      rw [hpow, pow_succ, pow_mul] at h
      simpa using h
    | zero => simp
    | add y y' _ _ ihy ihy' => rw [mul_add, add_mul, ihy, ihy', neg_add]
  | zero => simp
  | add x x' _ _ ihx ihx' => rw [add_mul, mul_add, ihx, ihx', neg_add]

omit [GradedAlgebra 𝒜] in
/-- An element of the odd part of a strictly graded-commutative algebra squares to zero. -/
public theorem mul_self_eq_zero_of_mem_oddPart {x : A} (hx : x ∈ oddPart 𝒜) : x * x = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem k x hx => simpa [pow_two] using IsStrictlyGradedComm.odd_sq_zero (𝒜 := 𝒜) hx
  | zero => simp
  | add x x' hx hx' ihx ihx' =>
    rw [mul_add, add_mul, add_mul, ihx, ihx', oddPart_mul_comm_neg 𝒜 hx hx']
    abel

omit [IsStrictlyGradedComm 𝒜] in
/-- The odd part is stable under multiplication by the even part. -/
public theorem evenPart_mul_mem_oddPart {x y : A} (hx : x ∈ evenPart 𝒜) (hy : y ∈ oddPart 𝒜) :
    x * y ∈ oddPart 𝒜 := by
  induction hx using Submodule.iSup_induction' with
  | mem k x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem e y hy =>
      refine Submodule.mem_iSup_of_mem (k + e) ?_
      rw [show 2 * (k + e) + 1 = 2 * k + (2 * e + 1) by ring]
      exact SetLike.GradedMul.mul_mem hx hy
    | zero => simp
    | add y y' _ _ ihy ihy' => rw [mul_add]; exact Submodule.add_mem _ ihy ihy'
  | zero => simp
  | add x x' _ _ ihx ihx' => rw [add_mul]; exact Submodule.add_mem _ ihx ihx'

omit [IsStrictlyGradedComm 𝒜] in
/-- An element of the positive even part of an odd-variable extension has the form `a + bT` with
`a` positive even and `b` odd. -/
public theorem exists_coeff_of_mem_positiveEvenPart_oddVariable
    {z : OddVariableExtension 𝒜 1}
    (hz : z ∈ positiveEvenPart (OddVariableExtension.grade 𝒜 1)) :
    ∃ a b : A, a ∈ positiveEvenPart 𝒜 ∧ b ∈ oddPart 𝒜 ∧
      z = OddVariableExtension.inclusion 𝒜 1 a +
        OddVariableExtension.inclusion 𝒜 1 b * OddVariableExtension.generator 𝒜 1 := by
  induction hz using Submodule.iSup_induction' with
  | mem d z hz =>
    rw [OddVariableExtension.mem_grade_iff] at hz
    obtain ⟨hfst, hsnd⟩ := hz
    refine ⟨TrivSqZeroExt.fst z, (TrivSqZeroExt.snd z : A), ?_, ?_, ?_⟩
    · exact Submodule.mem_iSup_of_mem d hfst
    · refine Submodule.mem_iSup_of_mem d ?_
      simp only [show (1 : ℕ) ≤ 2 * (d + 1) from by omega, ite_true] at hsnd
      rwa [show 2 * (d + 1) - 1 = 2 * d + 1 by omega] at hsnd
    · exact (OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator 𝒜 1 z).symm
  | zero => exact ⟨0, 0, Submodule.zero_mem _, Submodule.zero_mem _, by simp⟩
  | add z z' hz hz' ihz ihz' =>
    obtain ⟨a, b, ha, hb, rfl⟩ := ihz
    obtain ⟨a', b', ha', hb', rfl⟩ := ihz'
    refine ⟨a + a', b + b', Submodule.add_mem _ ha ha', Submodule.add_mem _ hb hb', ?_⟩
    rw [_root_.map_add, _root_.map_add, add_mul]
    abel

end GradedFacts

section ContractLeft

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Contraction commutes with the algebra map induced by a linear map, after pulling back the
functional. -/
public theorem contractLeft_exteriorAlgebraMap (l : M →ₗ[R] N) (ψ : Module.Dual R N)
    (u : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft ψ (ExteriorAlgebra.map l u) =
      ExteriorAlgebra.map l (CliffordAlgebra.contractLeft (ψ ∘ₗ l) u) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap,
      CliffordAlgebra.contractLeft_algebraMap, _root_.map_zero]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, _root_.map_add, _root_.map_add, hx, hy]
  | ι_mul x m hx =>
    rw [_root_.map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul, _root_.map_sub, _root_.map_smul, _root_.map_mul,
      ExteriorAlgebra.map_apply_ι, hx]
    rfl

/-- The graded Leibniz rule for contraction on the exterior algebra. -/
public theorem contractLeft_mul_of_mem (φ : Module.Dual R N) (n : ℕ)
    {a : ExteriorAlgebra R N} (ha : a ∈ ⋀[R]^n N) (b : ExteriorAlgebra R N) :
    CliffordAlgebra.contractLeft φ (a * b) =
      CliffordAlgebra.contractLeft φ a * b +
        ((-1 : R) ^ n) • (a * CliffordAlgebra.contractLeft φ b) :=
  (Koszul.differentialGradedAlgebra φ).differential_mul_of_mem n ha b

/-- The Leibniz rule for a left factor in a sum of exterior powers whose degrees all have sign
`ε`. -/
private theorem contractLeft_mul_of_mem_iSup (φ : Module.Dual R N) (f : ℕ → ℕ) (ε : R)
    (hε : ∀ k, (-1 : R) ^ f k = ε) {u : ExteriorAlgebra R N}
    (hu : u ∈ ⨆ k, exteriorGrade R N (f k)) (v : ExteriorAlgebra R N) :
    CliffordAlgebra.contractLeft φ (u * v) =
      CliffordAlgebra.contractLeft φ u * v + ε • (u * CliffordAlgebra.contractLeft φ v) := by
  induction hu using Submodule.iSup_induction' with
  | mem k u hu => rw [contractLeft_mul_of_mem φ (f k) hu v, hε]
  | zero => simp
  | add u u' _ _ ihu ihu' =>
    rw [add_mul, add_mul, _root_.map_add, _root_.map_add, ihu, ihu', add_mul, smul_add]
    abel

/-- The Leibniz rule with an even left factor. -/
public theorem contractLeft_mul_of_mem_evenPart (φ : Module.Dual R N)
    {u : ExteriorAlgebra R N} (hu : u ∈ evenPart (exteriorGrade R N)) (v : ExteriorAlgebra R N) :
    CliffordAlgebra.contractLeft φ (u * v) =
      CliffordAlgebra.contractLeft φ u * v + u * CliffordAlgebra.contractLeft φ v := by
  simpa using contractLeft_mul_of_mem_iSup φ (2 * ·) 1 (fun k => by simp [pow_mul]) hu v

/-- The Leibniz rule with an odd left factor. -/
public theorem contractLeft_mul_of_mem_oddPart (φ : Module.Dual R N)
    {u : ExteriorAlgebra R N} (hu : u ∈ oddPart (exteriorGrade R N)) (v : ExteriorAlgebra R N) :
    CliffordAlgebra.contractLeft φ (u * v) =
      CliffordAlgebra.contractLeft φ u * v - u * CliffordAlgebra.contractLeft φ v := by
  simpa [sub_eq_add_neg] using
    contractLeft_mul_of_mem_iSup φ (2 * · + 1) (-1) (fun k => by simp [pow_succ, pow_mul]) hu v

/-- `ExteriorAlgebra.map` preserves a sum of exterior powers. -/
private theorem map_mem_iSup_exteriorGrade (l : M →ₗ[R] N) (f : ℕ → ℕ) {u : ExteriorAlgebra R M}
    (hu : u ∈ ⨆ k, exteriorGrade R M (f k)) :
    ExteriorAlgebra.map l u ∈ ⨆ k, exteriorGrade R N (f k) := by
  induction hu using Submodule.iSup_induction' with
  | mem k u hu => exact Submodule.mem_iSup_of_mem k (ExteriorAlgebra.map_mem_exteriorPower l hu)
  | zero => simp
  | add u u' _ _ ihu ihu' => rw [_root_.map_add]; exact Submodule.add_mem _ ihu ihu'

/-- `ExteriorAlgebra.map` preserves the even part. -/
public theorem map_mem_evenPart (l : M →ₗ[R] N) {u : ExteriorAlgebra R M}
    (hu : u ∈ evenPart (exteriorGrade R M)) :
    ExteriorAlgebra.map l u ∈ evenPart (exteriorGrade R N) :=
  map_mem_iSup_exteriorGrade l (2 * ·) hu

/-- `ExteriorAlgebra.map` preserves the odd part. -/
public theorem map_mem_oddPart (l : M →ₗ[R] N) {u : ExteriorAlgebra R M}
    (hu : u ∈ oddPart (exteriorGrade R M)) :
    ExteriorAlgebra.map l u ∈ oddPart (exteriorGrade R N) :=
  map_mem_iSup_exteriorGrade l (2 * · + 1) hu

end ContractLeft

section Step

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

open ExteriorOddVariable

/-- The grading sign fixes the even part of `⋀[R] M`. -/
public theorem ExteriorOddVariable.sgn_of_mem_evenPart {u : ExteriorAlgebra R M}
    (hu : u ∈ evenPart (exteriorGrade R M)) : sgn u = u :=
  signRingEquiv_apply_of_mem_evenPart (exteriorGrade R M) 1 hu

/-- Contraction of an element of `⋀[R] (M × R)` written in the normal form `a + bT`. -/
public theorem contractLeft_incl_add_incl_mul_gen (ψ : Module.Dual R (M × R))
    (X : ExteriorAlgebra R M) {Y : ExteriorAlgebra R M}
    (hY : Y ∈ oddPart (exteriorGrade R M)) :
    CliffordAlgebra.contractLeft ψ (incl X + incl Y * gen) =
      incl (CliffordAlgebra.contractLeft (ψ ∘ₗ LinearMap.inl R M R) X -
          ψ ((0, 1) : M × R) • Y) +
        incl (CliffordAlgebra.contractLeft (ψ ∘ₗ LinearMap.inl R M R) Y) * gen := by
  have hincl : ∀ u : ExteriorAlgebra R M,
      CliffordAlgebra.contractLeft ψ (incl u) =
        incl (CliffordAlgebra.contractLeft (ψ ∘ₗ LinearMap.inl R M R) u) := fun u =>
    contractLeft_exteriorAlgebraMap (LinearMap.inl R M R) ψ u
  have hgen : CliffordAlgebra.contractLeft ψ gen =
      algebraMap R (ExteriorAlgebra R (M × R)) (ψ ((0, 1) : M × R)) :=
    CliffordAlgebra.contractLeft_ι _ _ _
  rw [_root_.map_add, hincl,
    contractLeft_mul_of_mem_oddPart ψ (u := incl Y)
      (map_mem_oddPart (LinearMap.inl R M R) hY) gen,
    hincl, hgen, incl_mul_algebraMap, _root_.map_sub]
  abel

/-- If the divided powers of `⋀[R] M` are compatible with contraction by `φ`, then those of
`⋀[R] (M × R)` are compatible with contraction by any functional restricting to `φ`. -/
public theorem exteriorProd_isCompatibleWithDifferential
    (γ : DividedPowerStructure (exteriorGrade R M)) (φ : Module.Dual R M) (c : R)
    (h : IsCompatibleWithDifferential γ (CliffordAlgebra.contractLeft φ))
    (ψ : Module.Dual R (M × R)) (hψ₁ : ψ ∘ₗ LinearMap.inl R M R = φ)
    (hψ₂ : ψ ((0, 1) : M × R) = c) :
    IsCompatibleWithDifferential (exteriorProdDividedPowerStructure γ)
      (CliffordAlgebra.contractLeft ψ) := by
  refine ⟨fun {n z} hn hz => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    rw [(exteriorProdDividedPowerStructure γ).dpow_one hz, show (1 : ℕ) - 1 = 0 from rfl,
      (exteriorProdDividedPowerStructure γ).dpow_zero hz, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hz' : equiv.symm z ∈
        positiveEvenPart (OddVariableExtension.grade (exteriorGrade R M) 1) :=
      (mem_positiveEvenPart_equiv_iff (OddVariableExtension.grade (exteriorGrade R M) 1)
        (exteriorGrade R (M × R)) equiv mem_grade_iff z).mp hz
    obtain ⟨a, b, ha, hb, hab⟩ :=
      exists_coeff_of_mem_positiveEvenPart_oddVariable (exteriorGrade R M) hz'
    have hzab : z = incl a + incl b * gen := by
      rw [← equiv.apply_symm_apply z, hab, _root_.map_add, _root_.map_mul, equiv_apply,
        equiv_apply, equiv_apply, hom_inclusion, hom_inclusion, hom_generator]
    have hg2even : γ.dpow (m + 1) a ∈ evenPart (exteriorGrade R M) :=
      dpow_mem_evenPart (exteriorGrade R M) γ _ ha
    have hg2b : γ.dpow (m + 1) a * b ∈ oddPart (exteriorGrade R M) :=
      evenPart_mul_mem_oddPart (exteriorGrade R M) hg2even hb
    have hbgb : b * (γ.dpow m a * b) = 0 := by
      rw [← mul_assoc,
        ← evenPart_mul_comm (exteriorGrade R M) (dpow_mem_evenPart (exteriorGrade R M) γ _ ha) b,
        mul_assoc,
        mul_self_eq_zero_of_mem_oddPart (exteriorGrade R M) hb, mul_zero]
    have hu1 : CliffordAlgebra.contractLeft φ (γ.dpow (m + 2) a) - c • (γ.dpow (m + 1) a * b) =
        (CliffordAlgebra.contractLeft φ a - c • b) * γ.dpow (m + 1) a := by
      rw [h.d_dpow (n := m + 2) (by omega) ha, show m + 2 - 1 = m + 1 from rfl, sub_mul,
        smul_mul_assoc, evenPart_mul_comm (exteriorGrade R M) hg2even b]
    have hu2 : CliffordAlgebra.contractLeft φ (γ.dpow (m + 1) a * b) =
        (CliffordAlgebra.contractLeft φ a - c • b) * (γ.dpow m a * b) +
          CliffordAlgebra.contractLeft φ b * γ.dpow (m + 1) a := by
      rw [contractLeft_mul_of_mem_evenPart φ hg2even b, h.d_dpow (n := m + 1) (by omega) ha,
        show m + 1 - 1 = m from rfl, sub_mul, smul_mul_assoc, hbgb, smul_zero, sub_zero,
        mul_assoc, evenPart_mul_comm (exteriorGrade R M) hg2even
          (CliffordAlgebra.contractLeft φ b)]
    have hδ : ∀ k, (exteriorProdDividedPowerStructure γ).dpow (k + 1) z =
        incl (γ.dpow (k + 1) a) + incl (γ.dpow k a * b) * gen := fun k => by
      rw [hzab, exteriorProdDividedPowerStructure_dpow γ (by omega) ha hb]
      rfl
    rw [hδ (m + 1), show m + 2 - 1 = m + 1 from rfl, hδ m, hzab,
      contractLeft_incl_add_incl_mul_gen ψ _ hg2b,
      contractLeft_incl_add_incl_mul_gen ψ _ hb, incl_add_mul_gen_mul,
      ExteriorOddVariable.sgn_of_mem_evenPart hg2even, hψ₁, hψ₂, hu1, hu2]

end Step

section Main

variable (R : Type u) [CommRing R]

/-- The divided powers of `⋀[R] (Fin r → R)` are compatible with contraction by every `R`-linear
functional, hence with the Koszul differential of every finite sequence in `R`. -/
@[stacks 09PH "compatibility with the Koszul differential"]
public theorem isCompatibleWithDifferential_exteriorDividedPowerStructure (r : ℕ) :
    ∀ φ : Module.Dual R (Fin r → R),
      IsCompatibleWithDifferential (exteriorDividedPowerStructure R r)
        (CliffordAlgebra.contractLeft φ) := by
  induction r with
  | zero =>
    refine fun φ => ⟨fun {n x} hn hx => ?_⟩
    obtain rfl : x = 0 := by rwa [positiveEvenPart_exteriorGrade_eq_bot R (Fin 0 → R)] at hx
    rw [exteriorDividedPowerStructure_zero, DividedPowerStructure.dpow_apply_zero _ hn,
      _root_.map_zero, zero_mul]
  | succ r ih =>
    intro φ
    rw [exteriorDividedPowerStructure_succ]
    refine IsCompatibleWithDifferential.transport _ _ _
      (CliffordAlgebra.contractLeft
        (φ ∘ₗ (finSuccLinearEquiv R r : ((Fin r → R) × R) →ₗ[R] (Fin (r + 1) → R))))
      (CliffordAlgebra.contractLeft φ)
      (fun x => contractLeft_exteriorAlgebraMap _ φ x)
      (exteriorProd_isCompatibleWithDifferential _
        ((φ ∘ₗ (finSuccLinearEquiv R r : ((Fin r → R) × R) →ₗ[R] (Fin (r + 1) → R))) ∘ₗ
          LinearMap.inl R (Fin r → R) R)
        ((φ ∘ₗ (finSuccLinearEquiv R r : ((Fin r → R) × R) →ₗ[R] (Fin (r + 1) → R)))
          ((0, 1) : (Fin r → R) × R))
        (ih _) _ rfl rfl)

end Main

end DividedPowers.TateResolution

end

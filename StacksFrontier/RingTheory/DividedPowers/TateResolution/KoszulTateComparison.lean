module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorFreeDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulDga
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FiniteTateResolution
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FiniteTateTowerLift

/-! # Tate resolutions interpolating between the Koszul algebras of two powers

Let `R` be a ring and `f₁, …, f_r ∈ R`. For `m ≥ 1` the Koszul divided power algebra
`K_m = R⟨ξ₁, …, ξ_r⟩` has `ξᵢ` of degree one and `d(ξᵢ) = fᵢ^m`; it is the exterior algebra of
`Rʳ` graded by its exterior powers, with the divided powers of Tag 09PH and the Koszul
differential, and for `m ≥ n` the transition map `K_m → K_n` is `ξᵢ ↦ fᵢ^(m-n) ξᵢ`. Over a
Noetherian ring Tate's construction interpolates between two of these: for every `n` there is an
`N ≥ n` and a divided power differential graded algebra `A` resolving `R/(f₁^N, …, f_r^N)` with
maps `K_N → A → R/(f₁^N, …, f_r^N)` and `A → K_n` whose composites are the canonical map and the
transition map. This is Tag 0GZ4.

The resolution is Tate's degreewise finite tower over `R` whose degree-one variables are indexed
by `Fin r`, the variable `Tᵢ` killing `fᵢ^N`; prescribing one variable per index — rather than
one per element of a generating family — is what makes `K_N → A`, `ξᵢ ↦ Tᵢ`, exist and have the
transition map as its composite with `A → K_n`.

The map `A → K_n` is built stage by stage. The target of the stage `k` is the Koszul algebra of
an exponent `e k`, the exponents running from `N` down to `n` along a chain whose consecutive
transition maps kill the homology in positive degrees; the image in the next Koszul algebra of a
degree-`k` cycle of the stage is then a boundary, and a primitive for it is the value given to
the variable killing that cycle. Above degree `r` the Koszul algebra vanishes, so the remaining
variables are sent to zero and the exponent stays at `n`. The chain exists by an Artin--Rees
argument: the ideal `(f₁^n, …, f_r^n)` annihilates the positive homology of `K_n`, so a high
enough power of it meets the cycles inside the boundaries, while the transition map from a high
enough exponent lands in that power of the ideal.

## Main definitions

* `DividedPowers.TateResolution.koszulPowerIdeal`,
  `DividedPowers.TateResolution.koszulPowerDifferential`,
  `DividedPowers.TateResolution.koszulPowerTransitionHom` and
  `DividedPowers.TateResolution.koszulPowerAugmentation` — the ideal `(f₁^N, …, f_r^N)`, the
  Koszul differential of the `N`-th powers, the transition map and the canonical map onto the
  quotient.
* `DividedPowers.TateResolution.KillsKoszulHomology` — the transition map `K_N → K_n` sends every
  cycle of a given positive degree to a boundary.
* `DividedPowers.TateResolution.koszulTateBase` and
  `DividedPowers.TateResolution.koszulTateAlgebra` — the base of Tate's tower for the powers
  `f₁^N, …, f_r^N` and its colimit.

## Main results

* `DividedPowers.TateResolution.exists_killsKoszulHomology` — the Noetherian input: for every `n`
  some transition map into `K_n` kills the homology in all positive degrees.
* `DividedPowers.TateResolution.exists_koszulTateAlpha` and
  `DividedPowers.TateResolution.exists_koszulTateBeta` — the two maps `K_N → A` and `A → K_n`.
* `DividedPowers.TateResolution.exists_tateResolution_koszulPowers` — Tag 0GZ4.

## References

* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

attribute [local instance] TateDatum.dga TateDatum.compatible

section Vanishing


/-- Above the length of the sequence the Koszul algebra vanishes. -/
public theorem exteriorGrade_eq_bot (R : Type u) [CommRing R] {r j : ℕ} (h : r < j) :
    exteriorGrade R (Fin r → R) j = ⊥ := by
  have hempty : IsEmpty (Set.powersetCard (Fin r) j) := by
    constructor
    rintro ⟨t, ht⟩
    have h2 : t.card ≤ r := by simpa using Finset.card_le_univ t
    have h3 : t.card = j := ht
    omega
  have hb := (Pi.basisFun R (Fin r)).exteriorPower (R := R) j
  rw [show exteriorGrade R (Fin r → R) j = ⋀[R]^j (Fin r → R) from rfl, Submodule.eq_bot_iff]
  intro x hx
  have hr : hb.repr ⟨x, hx⟩ = 0 := by
    ext s
    exact hempty.elim s
  exact congrArg Subtype.val (hb.repr.injective (hr.trans (map_zero _).symm))

/-- A homogeneous element of the Koszul algebra whose degree exceeds the length of the sequence
is zero. -/
public theorem eq_zero_of_mem_exteriorGrade_of_lt {R : Type u} [CommRing R] {r j : ℕ} (h : r < j)
    {x : ExteriorAlgebra R (Fin r → R)} (hx : x ∈ exteriorGrade R (Fin r → R) j) : x = 0 := by
  rwa [exteriorGrade_eq_bot R h] at hx

end Vanishing

section Setup


variable {R : Type u} [CommRing R] {r : ℕ}

/-- The ideal generated by the `N`-th powers of a finite sequence. -/
public def koszulPowerIdeal (f : Fin r → R) (N : ℕ) : Ideal R :=
  Ideal.span (Set.range fun i => f i ^ N)

/-- Each power `fᵢ^N` lies in the ideal it generates. -/
public theorem pow_mem_koszulPowerIdeal (f : Fin r → R) (N : ℕ) (i : Fin r) :
    f i ^ N ∈ koszulPowerIdeal f N :=
  Ideal.subset_span ⟨i, rfl⟩

/-- The ideals generated by the powers of a sequence decrease as the exponent grows. -/
public theorem koszulPowerIdeal_le_of_le (f : Fin r → R) {n N : ℕ} (h : n ≤ N) :
    koszulPowerIdeal f N ≤ koszulPowerIdeal f n := by
  rw [koszulPowerIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hpow : f i ^ N = f i ^ (N - n) * f i ^ n := by
    rw [← pow_add]
    congr 1
    omega
  show f i ^ N ∈ koszulPowerIdeal f n
  rw [hpow]
  exact Ideal.mul_mem_left _ _ (pow_mem_koszulPowerIdeal f n i)

/-- The Koszul differential on the `N`-th powers. -/
public noncomputable def koszulPowerDifferential (f : Fin r → R) (N : ℕ) :
    ExteriorAlgebra R (Fin r → R) →ₗ[R] ExteriorAlgebra R (Fin r → R) :=
  Koszul.contraction (Koszul.seqDual fun i => f i ^ N)

/-- The Koszul differential of the `N`-th powers makes the exterior-power grading a differential
graded algebra. -/
public theorem isDifferentialGradedAlgebra_koszulPowerDifferential (f : Fin r → R) (N : ℕ) :
    IsDifferentialGradedAlgebra (exteriorGrade R (Fin r → R)) (koszulPowerDifferential f N) :=
  isDifferentialGradedAlgebra_contraction _

/-- The Koszul differential of the `N`-th powers on a degree-one element is the corresponding
linear combination of those powers. -/
public theorem koszulPowerDifferential_ι (f : Fin r → R) (N : ℕ) (p : Fin r → R) :
    koszulPowerDifferential f N (ExteriorAlgebra.ι R p) =
      algebraMap R (ExteriorAlgebra R (Fin r → R)) (∑ i, p i * f i ^ N) := by
  rw [koszulPowerDifferential, Koszul.contraction,
    CliffordAlgebra.contractLeft_ι 0 (Koszul.seqDual fun i => f i ^ N) p, Koszul.seqDual_apply]

/-- The Koszul differential of the `N`-th powers sends the `i`-th generator to `fᵢ^N`. -/
public theorem koszulPowerDifferential_exteriorGen (f : Fin r → R) (N : ℕ) (i : Fin r) :
    koszulPowerDifferential f N (exteriorGen R r i) =
      algebraMap R (ExteriorAlgebra R (Fin r → R)) (f i ^ N) := by
  rw [exteriorGen, koszulPowerDifferential_ι,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hj => by simp [Pi.single_eq_of_ne hj])]
  simp

/-- A cycle is annihilated by the defining ideal modulo boundaries. -/
public theorem smul_cycle_eq_koszulPowerDifferential (f : Fin r → R) (N j : ℕ) (i : Fin r)
    {z : ExteriorAlgebra R (Fin r → R)} (hz : z ∈ exteriorGrade R (Fin r → R) j)
    (hdz : koszulPowerDifferential f N z = 0) :
    f i ^ N • z = koszulPowerDifferential f N (exteriorGen R r i * z) := by
  rw [IsDifferentialGradedAlgebra.leibniz
      (self := isDifferentialGradedAlgebra_koszulPowerDifferential f N)
      (exteriorGen_mem R r i) hz, hdz, mul_zero, smul_zero, add_zero,
    koszulPowerDifferential_exteriorGen, Algebra.smul_def]


/-- The transition map `K_N → K_n`: scaling the `i`-th generator by `fᵢ^(N-n)`. -/
public noncomputable def koszulPowerTransitionHom (f : Fin r → R) (N n : ℕ) :
    ExteriorAlgebra R (Fin r → R) →ₐ[R] ExteriorAlgebra R (Fin r → R) :=
  ExteriorAlgebra.map (LinearMap.mulLeft R fun i => f i ^ (N - n))

/-- The transition map scales the coordinates of a degree-one element by `fᵢ^(N-n)`. -/
public theorem koszulPowerTransitionHom_ι (f : Fin r → R) (N n : ℕ) (p : Fin r → R) :
    koszulPowerTransitionHom f N n (ExteriorAlgebra.ι R p) =
      ExteriorAlgebra.ι R (fun i => f i ^ (N - n) * p i) :=
  ExteriorAlgebra.map_apply_ι _ _

/-- The transition map sends the `i`-th generator to `fᵢ^(N-n) ξᵢ`. -/
public theorem koszulPowerTransitionHom_exteriorGen (f : Fin r → R) (N n : ℕ) (i : Fin r) :
    koszulPowerTransitionHom f N n (exteriorGen R r i) =
      f i ^ (N - n) • exteriorGen R r i := by
  rw [exteriorGen, koszulPowerTransitionHom_ι, ← LinearMap.map_smul (ExteriorAlgebra.ι R)]
  congr 1
  funext k
  show f k ^ (N - n) * (Pi.single i 1 : Fin r → R) k =
    f i ^ (N - n) * (Pi.single i 1 : Fin r → R) k
  by_cases hk : k = i
  · rw [hk]
  · rw [Pi.single_eq_of_ne hk 1, mul_zero, mul_zero]

/-- The diagonal endomorphism with entries `fᵢ^(N-n)` pulls the Koszul functional of the `n`-th
powers back to that of the `N`-th powers. -/
public theorem seqDual_comp_mulLeft_pow (f : Fin r → R) {N n : ℕ} (h : n ≤ N) :
    (Koszul.seqDual fun i => f i ^ n) ∘ₗ LinearMap.mulLeft R (fun i => f i ^ (N - n)) =
      Koszul.seqDual fun i => f i ^ N := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, Koszul.seqDual_apply, Koszul.seqDual_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hv : (LinearMap.mulLeft R (fun j => f j ^ (N - n)) v) i = f i ^ (N - n) * v i := rfl
  rw [hv, mul_comm (f i ^ (N - n)) (v i), mul_assoc, ← pow_add,
    show N - n + n = N by omega]

/-- **The transition map is a chain map.** -/
public theorem koszulPowerTransitionHom_differential (f : Fin r → R) {N n : ℕ} (h : n ≤ N)
    (x : ExteriorAlgebra R (Fin r → R)) :
    koszulPowerTransitionHom f N n (koszulPowerDifferential f N x) =
      koszulPowerDifferential f n (koszulPowerTransitionHom f N n x) := by
  rw [koszulPowerDifferential, koszulPowerDifferential, Koszul.contraction, Koszul.contraction,
    koszulPowerTransitionHom,
    contractLeft_exteriorAlgebraMap (LinearMap.mulLeft R fun i => f i ^ (N - n))
      (Koszul.seqDual fun i => f i ^ n) x, seqDual_comp_mulLeft_pow f h]

/-- The transition map preserves the exterior degree. -/
public theorem koszulPowerTransitionHom_mem (f : Fin r → R) (N n m : ℕ)
    {x : ExteriorAlgebra R (Fin r → R)} (hx : x ∈ exteriorGrade R (Fin r → R) m) :
    koszulPowerTransitionHom f N n x ∈ exteriorGrade R (Fin r → R) m :=
  ExteriorAlgebra.map_mem_exteriorPower _ hx

/-- The transition map preserves divided powers. -/
public theorem koszulPowerTransitionHom_dpow (f : Fin r → R) (N n k : ℕ)
    {x : ExteriorAlgebra R (Fin r → R)}
    (hx : x ∈ positiveEvenPart (exteriorGrade R (Fin r → R))) :
    koszulPowerTransitionHom f N n ((exteriorDividedPowerStructure R r).dpow k x) =
      (exteriorDividedPowerStructure R r).dpow k (koszulPowerTransitionHom f N n x) :=
  (exteriorDividedPowerStructure_dpow_map_mulLeft R r _ k x hx).symm

/-- Transition maps compose. -/
public theorem koszulPowerTransitionHom_comp (f : Fin r → R) {N m n : ℕ} (hnm : n ≤ m) (hmN : m ≤ N)
    (x : ExteriorAlgebra R (Fin r → R)) :
    koszulPowerTransitionHom f m n (koszulPowerTransitionHom f N m x) =
      koszulPowerTransitionHom f N n x := by
  have hcomp : (koszulPowerTransitionHom f m n).comp (koszulPowerTransitionHom f N m) =
      koszulPowerTransitionHom f N n := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    show koszulPowerTransitionHom f m n (koszulPowerTransitionHom f N m (ExteriorAlgebra.ι R v)) =
      koszulPowerTransitionHom f N n (ExteriorAlgebra.ι R v)
    rw [koszulPowerTransitionHom_ι, koszulPowerTransitionHom_ι, koszulPowerTransitionHom_ι]
    congr 1
    funext i
    rw [← mul_assoc, ← pow_add, show m - n + (N - m) = N - n by omega]
  exact congrArg (fun g : ExteriorAlgebra R (Fin r → R) →ₐ[R] ExteriorAlgebra R (Fin r → R) => g x)
    hcomp

section Acyclicity

variable {R : Type u} [CommRing R] {r : ℕ}

/-- Multiplying by a generator raises the exterior degree by one. -/
private theorem exteriorGen_mul_mem_grade_succ (i : Fin r) {j : ℕ}
    {z : ExteriorAlgebra R (Fin r → R)} (hz : z ∈ exteriorGrade R (Fin r → R) j) :
    exteriorGen R r i * z ∈ exteriorGrade R (Fin r → R) (j + 1) := by
  rw [Nat.add_comm]
  exact SetLike.mul_mem_graded (A := exteriorGrade R (Fin r → R)) (exteriorGen_mem R r i) hz

/-- An element of the ideal `(f₁^n, …, f_r^n)` carries a cycle of the Koszul algebra on the `n`-th
powers into the boundaries. -/
public theorem smul_mem_koszulBoundaries (f : Fin r → R) (n j : ℕ) {a : R}
    (ha : a ∈ koszulPowerIdeal f n) {z : ExteriorAlgebra R (Fin r → R)}
    (hz : z ∈ exteriorGrade R (Fin r → R) j) (hdz : koszulPowerDifferential f n z = 0) :
    a • z ∈ Submodule.map (koszulPowerDifferential f n) (exteriorGrade R (Fin r → R) (j + 1)) := by
  have key : koszulPowerIdeal f n ≤
      Submodule.comap (LinearMap.toSpanSingleton R (ExteriorAlgebra R (Fin r → R)) z)
        (Submodule.map (koszulPowerDifferential f n)
          (exteriorGrade R (Fin r → R) (j + 1))) := by
    rw [koszulPowerIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show f i ^ n • z ∈ Submodule.map (koszulPowerDifferential f n)
      (exteriorGrade R (Fin r → R) (j + 1))
    rw [smul_cycle_eq_koszulPowerDifferential f n j i hz hdz]
    exact Submodule.mem_map_of_mem (exteriorGen_mul_mem_grade_succ i hz)
  exact key ha

/-- **Artin--Rees for the Koszul cycles.** Some power of the ideal `(f₁^n, …, f_r^n)` meets the
cycles of a given degree inside the boundaries. -/
public theorem exists_pow_smul_cycle_mem_koszulBoundaries [IsNoetherianRing R] (f : Fin r → R)
    (n j : ℕ) :
    ∃ k : ℕ, ∀ x : ExteriorAlgebra R (Fin r → R),
      x ∈ (koszulPowerIdeal f n) ^ k • exteriorGrade R (Fin r → R) j →
      koszulPowerDifferential f n x = 0 →
      ∃ y ∈ exteriorGrade R (Fin r → R) (j + 1), koszulPowerDifferential f n y = x := by
  classical
  have hfin : Module.Finite R ↥(exteriorGrade R (Fin r → R) j) :=
    inferInstanceAs (Module.Finite R ↥(⋀[R]^j (Fin r → R)))
  set G := exteriorGrade R (Fin r → R) j with hG
  set Z : Submodule R ↥G :=
    Submodule.comap G.subtype (LinearMap.ker (koszulPowerDifferential f n)) with hZdef
  set B : Submodule R ↥G := Submodule.comap G.subtype
    (Submodule.map (koszulPowerDifferential f n) (exteriorGrade R (Fin r → R) (j + 1))) with hBdef
  obtain ⟨c, hc⟩ := (koszulPowerIdeal f n).exists_pow_inf_eq_pow_smul Z
  refine ⟨c + 1, fun x hx hdx => ?_⟩
  have hxG : x ∈ G := Submodule.smul_le_right hx
  have hmap : Submodule.map G.subtype
        ((koszulPowerIdeal f n) ^ (c + 1) • (⊤ : Submodule R ↥G)) =
      (koszulPowerIdeal f n) ^ (c + 1) • G := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  have hx' : (⟨x, hxG⟩ : ↥G) ∈ (koszulPowerIdeal f n) ^ (c + 1) • (⊤ : Submodule R ↥G) := by
    rw [← hmap] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    exact (Subtype.ext hwx : w = (⟨x, hxG⟩ : ↥G)) ▸ hw
  have hZ : (⟨x, hxG⟩ : ↥G) ∈ Z :=
    Submodule.mem_comap.2 (LinearMap.mem_ker.2 hdx)
  have hJZ : koszulPowerIdeal f n • Z ≤ B := by
    refine Submodule.smul_le.2 fun a ha z hz => ?_
    refine Submodule.mem_comap.2 ?_
    show a • (z : ExteriorAlgebra R (Fin r → R)) ∈
      Submodule.map (koszulPowerDifferential f n) (exteriorGrade R (Fin r → R) (j + 1))
    exact smul_mem_koszulBoundaries f n j ha z.2
      (LinearMap.mem_ker.1 (Submodule.mem_comap.1 hz))
  have hle : (koszulPowerIdeal f n) ^ (c + 1) • (⊤ : Submodule R ↥G) ⊓ Z ≤ B := by
    rw [hc (c + 1) (by omega)]
    refine le_trans ?_ hJZ
    rw [show c + 1 - c = 1 by omega, pow_one]
    exact smul_mono_right _ inf_le_right
  exact Submodule.mem_map.1 (Submodule.mem_comap.1 (hle ⟨hx', hZ⟩))

/-- If every `fᵢ^(N-n)` lies in `(f₁^n, …, f_r^n)^k`, the transition map carries each positive
homogeneous degree into that power of the ideal. -/
public theorem koszulPowerTransitionHom_mem_pow_smul (f : Fin r → R) (N n k j : ℕ)
    (hc : ∀ i, f i ^ (N - n) ∈ (koszulPowerIdeal f n) ^ k)
    {x : ExteriorAlgebra R (Fin r → R)} (hx : x ∈ exteriorGrade R (Fin r → R) (j + 1)) :
    koszulPowerTransitionHom f N n x ∈
      (koszulPowerIdeal f n) ^ k • exteriorGrade R (Fin r → R) (j + 1) := by
  rw [show exteriorGrade R (Fin r → R) (j + 1) = ⋀[R]^(j + 1) (Fin r → R) from rfl,
    ← ExteriorAlgebra.ιMulti_span_fixedDegree R (j + 1)] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hY : koszulPowerTransitionHom f N n (ExteriorAlgebra.ιMulti R j (Fin.tail v))
        ∈ exteriorGrade R (Fin r → R) j :=
      koszulPowerTransitionHom_mem f N n j (Koszul.ιMulti_mem j (Fin.tail v))
    rw [Koszul.ιMulti_succ_apply, map_mul, koszulPowerTransitionHom_ι,
      ι_eq_sum_exteriorGen, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_assoc, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_right _ _ (hc i))
      (exteriorGen_mul_mem_grade_succ i hY)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

/-- The property that the transition map `K_N → K_n` kills the homology in degree `j + 1`. -/
public def KillsKoszulHomology (f : Fin r → R) (n N j : ℕ) : Prop :=
  ∀ x ∈ exteriorGrade R (Fin r → R) (j + 1), koszulPowerDifferential f N x = 0 →
    ∃ y ∈ exteriorGrade R (Fin r → R) (j + 2),
      koszulPowerDifferential f n y = koszulPowerTransitionHom f N n x

/-- The vanishing of a transition map on homology persists when the source exponent is increased,
because transition maps compose. -/
public theorem killsKoszulHomology_of_le (f : Fin r → R) {n N M j : ℕ} (hn : n ≤ N) (hNM : N ≤ M)
    (h : KillsKoszulHomology f n N j) : KillsKoszulHomology f n M j := by
  intro x hx hdx
  obtain ⟨y, hy, hdy⟩ := h (koszulPowerTransitionHom f M N x)
    (koszulPowerTransitionHom_mem f M N (j + 1) hx)
    (by rw [← koszulPowerTransitionHom_differential f hNM, hdx, map_zero])
  exact ⟨y, hy, hdy.trans (koszulPowerTransitionHom_comp f hn hNM x)⟩

/-- Above the length of the sequence the Koszul algebra vanishes, so every transition map kills its
homology there. -/
public theorem killsKoszulHomology_of_lt (f : Fin r → R) (n N : ℕ) {j : ℕ} (hj : r < j + 1) :
    KillsKoszulHomology f n N j := by
  intro x hx _
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [eq_zero_of_mem_exteriorGrade_of_lt hj hx, map_zero, map_zero]

/-- Over a Noetherian ring, for a fixed degree some transition map into `K_n` sends every cycle of
that degree to a boundary. -/
public theorem exists_killsKoszulHomology_degree [IsNoetherianRing R] (f : Fin r → R) (n j : ℕ) :
    ∃ N : ℕ, n ≤ N ∧ KillsKoszulHomology f n N j := by
  obtain ⟨k, hk⟩ := exists_pow_smul_cycle_mem_koszulBoundaries f n (j + 1)
  refine ⟨n + n * k, by omega, fun x hx hdx => ?_⟩
  have hc : ∀ i, f i ^ (n + n * k - n) ∈ (koszulPowerIdeal f n) ^ k := by
    intro i
    rw [show n + n * k - n = n * k by omega, pow_mul]
    exact Ideal.pow_mem_pow (pow_mem_koszulPowerIdeal f n i) k
  exact hk _ (koszulPowerTransitionHom_mem_pow_smul f (n + n * k) n k j hc hx)
    (by rw [← koszulPowerTransitionHom_differential f (by omega : n ≤ n + n * k), hdx, map_zero])

/-- One exponent works for all degrees below a given bound. -/
public theorem exists_killsKoszulHomology_below [IsNoetherianRing R] (f : Fin r → R) (n m : ℕ) :
    ∃ N : ℕ, n ≤ N ∧ ∀ j < m, KillsKoszulHomology f n N j := by
  induction m with
  | zero => exact ⟨n, le_rfl, fun j hj => absurd hj (by omega)⟩
  | succ m ih =>
    obtain ⟨N₁, hN₁, h₁⟩ := ih
    obtain ⟨N₂, hN₂, h₂⟩ := exists_killsKoszulHomology_degree f n m
    refine ⟨max N₁ N₂, le_trans hN₁ (le_max_left _ _), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · exact killsKoszulHomology_of_le f hN₁ (le_max_left _ _) (h₁ j hj')
    · exact killsKoszulHomology_of_le f hN₂ (le_max_right _ _) h₂

/-- **The Noetherian Koszul pro-isomorphism, in the form Tate's comparison needs.** Over a
Noetherian ring, for every `n` there is an `N ≥ n` such that the transition map `K_N → K_n` sends
every cycle of positive degree to a boundary. -/
public theorem exists_killsKoszulHomology [IsNoetherianRing R] (f : Fin r → R) (n : ℕ) :
    ∃ N : ℕ, n ≤ N ∧ ∀ j : ℕ, KillsKoszulHomology f n N j := by
  obtain ⟨N, hN, h⟩ := exists_killsKoszulHomology_below f n r
  refine ⟨N, hN, fun j => ?_⟩
  by_cases hj : j < r
  · exact h j hj
  · exact killsKoszulHomology_of_lt f n N (by omega)

end Acyclicity

end Setup

section Tower


variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The base of Tate's tower for a Koszul datum.** The ring `R` concentrated in degree zero,
with the `N`-th powers `f₁^N, …, f_r^N` as the degree-zero cycles to be killed by the `r`
variables of degree one. -/
public noncomputable def koszulTateBase (f : Fin r → R) (N : ℕ) : TateStageData.{u, u} R 0 where
  datum := tateDatumOfZeroDifferential (degreeZeroDPAlgebra R R)
  kill := ULift.{u} (Fin r)
  value := fun i => f i.down ^ N
  value_mem := fun _ => mem_degreeZeroGrade_zero R R _
  value_cycle := fun _ => rfl

/-- The base of the Koszul tower prescribes exactly `r` variables of degree one. -/
public theorem finite_koszulTateBase_kill (f : Fin r → R) (N : ℕ) :
    Finite (koszulTateBase f N).kill :=
  inferInstanceAs (Finite (ULift.{u} (Fin r)))

/-- The base of the Koszul tower is concentrated in degree zero. -/
public theorem koszulTateBase_mem_grade_zero (f : Fin r → R) (N : ℕ)
    (p : (finiteTateAlgebra (koszulTateBase f N) 0).carrier) :
    p ∈ (finiteTateAlgebra (koszulTateBase f N) 0).grade 0 :=
  mem_degreeZeroGrade_zero R R p

/-- A morphism out of the base of the Koszul tower is no more than an algebra homomorphism landing
in degree zero. -/
public theorem koszulTateBase_exists_gradedDPHom (f : Fin r → R) (N : ℕ)
    (E : GradedDPAlgebra.{u, u} R)
    (g : (finiteTateAlgebra (koszulTateBase f N) 0).carrier →ₐ[R] E.carrier)
    (hg : ∀ p : (finiteTateAlgebra (koszulTateBase f N) 0).carrier, g p ∈ E.grade 0) :
    ∃ F : GradedDPHom (finiteTateAlgebra (koszulTateBase f N) 0) E,
      ∀ p : (finiteTateAlgebra (koszulTateBase f N) 0).carrier, F.hom p = g p :=
  ⟨degreeZeroDPHom R R E g hg, fun _ => rfl⟩

/-- The differential of the base of the Koszul tower is zero. -/
public theorem koszulTateBase_differential (f : Fin r → R) (N : ℕ) :
    finiteTateDifferential (koszulTateBase f N) 0 = 0 := rfl

/-- **Over a Noetherian ring every degree of every stage of the Koszul tower has a finite
spanning family of cycles**, so the tower really does kill every cycle. -/
public theorem hasFiniteSpanningCycles_koszulTateStage [IsNoetherianRing R] (f : Fin r → R) (N : ℕ)
    (M m : ℕ) :
    HasFiniteSpanningCycles (finiteTateStage (koszulTateBase f N) M).datum m := by
  classical
  let _ : CommRing (finiteTateAlgebra (koszulTateBase f N) 0).carrier :=
    inferInstanceAs (CommRing R)
  have : IsNoetherianRing (finiteTateAlgebra (koszulTateBase f N) 0).carrier :=
    inferInstanceAs (IsNoetherianRing R)
  have : ∀ i : ℕ, Finite (finiteTateIndex (koszulTateBase f N) i) :=
    finite_finiteTateIndex (koszulTateBase f N) (finite_koszulTateBase_kill f N)
  have : IsDifferentialGradedAlgebra (finiteTateAlgebra (koszulTateBase f N) M).grade
      (finiteTateDifferential (koszulTateBase f N) M) :=
    finiteTateDga (koszulTateBase f N) M
  have h0 : ∀ p : (finiteTateAlgebra (koszulTateBase f N) 0).carrier,
      chainStageCoefficient (finiteTateAlgebra (koszulTateBase f N))
          (finiteTateStep (koszulTateBase f N)) M p ∈
        (finiteTateAlgebra (koszulTateBase f N) M).grade 0 := fun p =>
    (chainMap (finiteTateAlgebra (koszulTateBase f N))
        (finiteTateStep (koszulTateBase f N)) (Nat.zero_le M)).map_grade 0 p
      (koszulTateBase_mem_grade_zero f N p)
  let _ : Algebra (finiteTateAlgebra (koszulTateBase f N) 0).carrier
      (finiteTateAlgebra (koszulTateBase f N) M).carrier :=
    coefficientAlgebra (finiteTateAlgebra (koszulTateBase f N) M).grade
      (chainStageCoefficient (finiteTateAlgebra (koszulTateBase f N))
        (finiteTateStep (koszulTateBase f N)) M) h0
  have : ∀ i : ℕ,
      Finite ((chainStagePresentation
        (finiteTateAlgebra (koszulTateBase f N))
        (finiteTateStep (koszulTateBase f N))
        (finiteTateIndex (koszulTateBase f N))
        (finiteTateGenerator (koszulTateBase f N))
        (finiteTateStage_isSetVariableExtension (koszulTateBase f N))
        (koszulTateBase_mem_grade_zero f N)
        (koszulTateBase_exists_gradedDPHom f N) M).indices i) := fun i =>
    finite_chainStagePresentation_indices
      (finiteTateAlgebra (koszulTateBase f N))
      (finiteTateStep (koszulTateBase f N))
      (finiteTateIndex (koszulTateBase f N))
      (finiteTateGenerator (koszulTateBase f N))
      (finiteTateStage_isSetVariableExtension (koszulTateBase f N))
      (koszulTateBase_mem_grade_zero f N)
      (koszulTateBase_exists_gradedDPHom f N) M i
  obtain ⟨s, hs, hspan⟩ := exists_finite_spanning_cycles
    (finiteTateAlgebra (koszulTateBase f N) M).grade
    (finiteTateDifferential (koszulTateBase f N) M)
    (chainStagePresentation
      (finiteTateAlgebra (koszulTateBase f N))
      (finiteTateStep (koszulTateBase f N))
      (finiteTateIndex (koszulTateBase f N))
      (finiteTateGenerator (koszulTateBase f N))
      (finiteTateStage_isSetVariableExtension (koszulTateBase f N))
      (koszulTateBase_mem_grade_zero f N)
      (koszulTateBase_exists_gradedDPHom f N) M)
    h0 (fun _ => rfl) m
  refine ⟨s, hs, fun x hx hdx => ?_⟩
  obtain ⟨c, hc⟩ := hspan x hx hdx
  refine ⟨fun y =>
    chainStageCoefficient (finiteTateAlgebra (koszulTateBase f N))
      (finiteTateStep (koszulTateBase f N)) M (c y),
    fun y => h0 (c y), ?_⟩
  rw [← hc]
  exact Finset.sum_congr rfl fun y _ => (Algebra.smul_def (c y) y).symm

/-- The Koszul Tate algebra: the colimit of the degreewise finite tower over `R` killing the
`N`-th powers. -/
public noncomputable abbrev koszulTateAlgebra (f : Fin r → R) (N : ℕ) : GradedDPAlgebra.{u, u} R :=
  finiteTateColimit (koszulTateBase f N)

/-- Its differential. -/
public noncomputable abbrev koszulTateDifferential (f : Fin r → R) (N : ℕ) :
    (koszulTateAlgebra f N).carrier →ₗ[R] (koszulTateAlgebra f N).carrier :=
  finiteTateColimitDifferential (koszulTateBase f N)

/-- Its degree-zero algebra, which is `R`. -/
public noncomputable def koszulTateCoefficient (f : Fin r → R) (N : ℕ) :
    R →ₐ[R] (koszulTateAlgebra f N).carrier :=
  (finiteTateCoefficient (koszulTateBase f N)).hom

/-- Its variables, indexed together with their degrees. -/
public noncomputable def koszulTateVariable (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, finiteTateIndex (koszulTateBase f N) n) :
    (koszulTateAlgebra f N).carrier :=
  finiteTateVariable (koszulTateBase f N) j.1 j.2

/-- Each variable of the Koszul Tate algebra is homogeneous of its prescribed degree. -/
public theorem koszulTateVariable_mem (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, finiteTateIndex (koszulTateBase f N) n) :
    koszulTateVariable f N j ∈ (koszulTateAlgebra f N).grade (j.1 + 1) :=
  finiteTateVariable_mem (koszulTateBase f N) j.1 j.2

/-- The degree-zero algebra of the Koszul Tate algebra lands in degree zero. -/
public theorem koszulTateCoefficient_mem_grade_zero (f : Fin r → R) (N : ℕ) (p : R) :
    koszulTateCoefficient f N p ∈ (koszulTateAlgebra f N).grade 0 :=
  (finiteTateCoefficient (koszulTateBase f N)).map_grade 0 _ (mem_degreeZeroGrade_zero R R _)

/-- The degree-zero algebra of the Koszul Tate algebra is a subalgebra. -/
public theorem koszulTateCoefficient_injective (f : Fin r → R) (N : ℕ) :
    Function.Injective (koszulTateCoefficient f N) :=
  finiteTateInclusion_injective (koszulTateBase f N) 0

/-- **The degree-zero part of the Koszul Tate algebra is `R`.** No step of the tower adds anything
in degree zero, and the base has nothing of positive degree. -/
public theorem mem_koszulTateAlgebra_grade_zero_iff (f : Fin r → R) (N : ℕ)
    (a : (koszulTateAlgebra f N).carrier) :
    a ∈ (koszulTateAlgebra f N).grade 0 ↔ ∃ p : R, koszulTateCoefficient f N p = a := by
  refine ⟨fun ha => ?_, fun ⟨p, hp⟩ => hp ▸ koszulTateCoefficient_mem_grade_zero f N p⟩
  obtain ⟨z, -, hz⟩ := exists_finiteTateInclusion_eq_of_mem_grade (koszulTateBase f N) 0 ha
  exact ⟨z, hz⟩

/-- The augmentation onto `R/(f₁^N, …, f_r^N)` exists: the morphism out of the colimit restricting
to the quotient map on the coefficients and killing every variable. -/
public theorem exists_koszulTateAugmentation (f : Fin r → R) (N : ℕ) :
    ∃ F : GradedDPHom (koszulTateAlgebra f N)
        (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N)),
      (∀ p : R, F.hom (koszulTateCoefficient f N p) =
          Ideal.Quotient.mk (koszulPowerIdeal f N) p) ∧
        ∀ (n : ℕ) (j : finiteTateIndex (koszulTateBase f N) n),
          F.hom (finiteTateVariable (koszulTateBase f N) n j) = 0 :=
  finiteTateColimit_exists_gradedDPHom (koszulTateBase f N)
    (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N))
    (degreeZeroDPHom R R (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N))
      (show R →ₐ[R] R ⧸ koszulPowerIdeal f N from Ideal.Quotient.mkₐ R (koszulPowerIdeal f N))
      (fun _ => mem_degreeZeroGrade_zero R (R ⧸ koszulPowerIdeal f N) _))
    (fun _ _ => 0) (fun _ _ => Submodule.zero_mem _)

/-- **The augmentation of the Koszul Tate algebra** onto `R/(f₁^N, …, f_r^N)`. -/
public noncomputable def koszulTateAugmentation (f : Fin r → R) (N : ℕ) :
    GradedDPHom (koszulTateAlgebra f N) (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N)) :=
  (exists_koszulTateAugmentation f N).choose

/-- The augmentation is the quotient map on the degree-zero algebra. -/
public theorem koszulTateAugmentation_coefficient (f : Fin r → R) (N : ℕ) (p : R) :
    (koszulTateAugmentation f N).hom (koszulTateCoefficient f N p) =
      Ideal.Quotient.mk (koszulPowerIdeal f N) p :=
  (exists_koszulTateAugmentation f N).choose_spec.1 p

/-- The augmentation kills every variable. -/
public theorem koszulTateAugmentation_variable (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, finiteTateIndex (koszulTateBase f N) n) :
    (koszulTateAugmentation f N).hom (koszulTateVariable f N j) = 0 :=
  (exists_koszulTateAugmentation f N).choose_spec.2 j.1 j.2

/-- The augmentation kills the positive-degree part: its target is concentrated in degree
zero. -/
public theorem koszulTateAugmentation_positive (f : Fin r → R) (N : ℕ) {n : ℕ} (hn : n ≠ 0)
    {a : (koszulTateAlgebra f N).carrier} (ha : a ∈ (koszulTateAlgebra f N).grade n) :
    (koszulTateAugmentation f N).hom a = 0 :=
  eq_zero_of_mem_degreeZeroDPAlgebra_grade R _ hn
    ((koszulTateAugmentation f N).map_grade n a ha)

/-- The differential of the Koszul Tate algebra vanishes in degree zero. -/
public theorem koszulTateDifferential_grade_zero (f : Fin r → R) (N : ℕ)
    {x : (koszulTateAlgebra f N).carrier} (hx : x ∈ (koszulTateAlgebra f N).grade 0) :
    koszulTateDifferential f N x = 0 :=
  IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := (koszulTateAlgebra f N).grade)
    (d := koszulTateDifferential f N)
    (self := finiteTateColimitDga (koszulTateBase f N)) hx

/-- The differential of the Koszul Tate algebra satisfies the signed Leibniz rule. -/
public theorem koszulTateDifferential_leibniz (f : Fin r → R) (N : ℕ) {i k : ℕ}
    {x y : (koszulTateAlgebra f N).carrier} (hx : x ∈ (koszulTateAlgebra f N).grade i)
    (hy : y ∈ (koszulTateAlgebra f N).grade k) :
    koszulTateDifferential f N (x * y) =
      koszulTateDifferential f N x * y + (-1 : R) ^ i • (x * koszulTateDifferential f N y) :=
  IsDifferentialGradedAlgebra.leibniz (𝒜 := (koszulTateAlgebra f N).grade)
    (d := koszulTateDifferential f N)
    (self := finiteTateColimitDga (koszulTateBase f N)) hx hy

/-- The finite variable stages of the Koszul Tate algebra cover it. -/
public theorem koszulTateAlgebra_finite_support (f : Fin r → R) (N : ℕ)
    (x : (koszulTateAlgebra f N).carrier) :
    ∃ T : Finset (Σ n : ℕ, finiteTateIndex (koszulTateBase f N) n),
      x ∈ finiteVariableStage (koszulTateAlgebra f N).gamma (koszulTateCoefficient f N)
        (koszulTateVariable f N) T :=
  finiteTateColimit_finite_support (koszulTateBase f N) x

/-- **The augmentation kills the boundary of every variable.** For a variable of degree one the
boundary is one of the powers `fᵢ^N`, which the quotient map kills; in higher degree the boundary
is homogeneous of positive degree, where the augmentation vanishes. -/
public theorem koszulTateAugmentation_differential_variable (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, finiteTateIndex (koszulTateBase f N) n) :
    (koszulTateAugmentation f N).hom
      (koszulTateDifferential f N (koszulTateVariable f N j)) = 0 := by
  obtain ⟨n, j⟩ := j
  rw [koszulTateVariable, finiteTateColimitDifferential_variable (koszulTateBase f N) n j]
  match n with
  | 0 =>
      refine (koszulTateAugmentation_coefficient f N
        (finiteTateCycle (koszulTateBase f N) 0 j)).trans ?_
      exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_koszulPowerIdeal f N j.down)
  | m + 1 =>
      refine koszulTateAugmentation_positive f N (Nat.succ_ne_zero m) ?_
      exact (finiteTateInclusion (koszulTateBase f N) (m + 1)).map_grade (m + 1) _
        (finiteTateCycle_mem (koszulTateBase f N) (m + 1) j)

/-- Only one homogeneous component of a homogeneous element is nonzero, so the augmentation kills
the boundary of each component as soon as it kills the boundary of the element. -/
public theorem koszulTateAugmentation_differential_gradedPart (f : Fin r → R) (N : ℕ) {k : ℕ}
    {x : (koszulTateAlgebra f N).carrier} (hx : x ∈ (koszulTateAlgebra f N).grade k)
    (h : (koszulTateAugmentation f N).hom (koszulTateDifferential f N x) = 0) (m : ℕ) :
    (koszulTateAugmentation f N).hom (koszulTateDifferential f N
      (gradedPart (koszulTateAlgebra f N).grade x m)) = 0 := by
  by_cases hm : k = m
  · subst hm
    rw [gradedPart_of_mem_same _ hx]
    exact h
  · rw [gradedPart_of_mem_ne _ hx hm, map_zero, map_zero]

/-- The elements all of whose homogeneous components have their boundary killed by the
augmentation form a subring: closure under multiplication is the Leibniz rule. -/
public noncomputable def koszulTateBoundaryKernel (f : Fin r → R) (N : ℕ) :
    Subring (koszulTateAlgebra f N).carrier where
  carrier := {x | ∀ m : ℕ, (koszulTateAugmentation f N).hom
    (koszulTateDifferential f N (gradedPart (koszulTateAlgebra f N).grade x m)) = 0}
  zero_mem' := by
    intro m
    rw [gradedPart_zero, map_zero, map_zero]
  one_mem' := by
    refine koszulTateAugmentation_differential_gradedPart f N
      (SetLike.one_mem_graded (koszulTateAlgebra f N).grade) ?_
    rw [koszulTateDifferential_grade_zero f N
      (SetLike.one_mem_graded (koszulTateAlgebra f N).grade), map_zero]
  add_mem' := by
    intro x y hx hy m
    rw [gradedPart_add, map_add, map_add, hx m, hy m, add_zero]
  neg_mem' := by
    intro x hx m
    rw [gradedPart_neg, map_neg, map_neg, hx m, neg_zero]
  mul_mem' := by
    intro x y hx hy m
    obtain ⟨s, hs⟩ := exists_gradedPart_decomposition (koszulTateAlgebra f N).grade x
    obtain ⟨t, ht⟩ := exists_gradedPart_decomposition (koszulTateAlgebra f N).grade y
    have hxy : gradedPart (koszulTateAlgebra f N).grade (x * y) m =
        ∑ i ∈ s, ∑ k ∈ t, gradedPart (koszulTateAlgebra f N).grade
          (gradedPart (koszulTateAlgebra f N).grade x i *
            gradedPart (koszulTateAlgebra f N).grade y k) m := by
      conv_lhs => rw [hs, ht]
      exact gradedPart_mul_sum (koszulTateAlgebra f N).grade _ _ m
    rw [hxy, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i + k = m
    · rw [gradedPart_mul_homogeneous _ (gradedPart_mem _ x i) (gradedPart_mem _ y k) hik,
        koszulTateDifferential_leibniz f N (gradedPart_mem _ x i) (gradedPart_mem _ y k),
        map_add, map_mul, hx i, zero_mul, zero_add, map_smul, map_mul, hy k, mul_zero,
        smul_zero]
    · rw [gradedPart_mul_homogeneous_of_ne _ (gradedPart_mem _ x i) (gradedPart_mem _ y k) hik,
        map_zero, map_zero]

/-- A homogeneous element whose boundary the augmentation kills lies in the subring. -/
public theorem mem_koszulTateBoundaryKernel_of_mem_grade (f : Fin r → R) (N : ℕ) {k : ℕ}
    {x : (koszulTateAlgebra f N).carrier} (hx : x ∈ (koszulTateAlgebra f N).grade k)
    (h : (koszulTateAugmentation f N).hom (koszulTateDifferential f N x) = 0) :
    x ∈ koszulTateBoundaryKernel f N :=
  koszulTateAugmentation_differential_gradedPart f N hx h

/-- The degree-zero algebra lies in the subring: the differential vanishes in degree zero. -/
public theorem koszulTateCoefficient_mem_koszulTateBoundaryKernel (f : Fin r → R) (N : ℕ) (p : R) :
    koszulTateCoefficient f N p ∈ koszulTateBoundaryKernel f N := by
  refine mem_koszulTateBoundaryKernel_of_mem_grade f N
    (koszulTateCoefficient_mem_grade_zero f N p) ?_
  rw [koszulTateDifferential_grade_zero f N (koszulTateCoefficient_mem_grade_zero f N p),
    map_zero]

/-- Every variable lies in the subring. -/
public theorem koszulTateVariable_mem_koszulTateBoundaryKernel (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, finiteTateIndex (koszulTateBase f N) n) :
    koszulTateVariable f N j ∈ koszulTateBoundaryKernel f N :=
  mem_koszulTateBoundaryKernel_of_mem_grade f N (koszulTateVariable_mem f N j)
    (koszulTateAugmentation_differential_variable f N j)

/-- **Every divided power of a variable lies in the subring.** It is homogeneous, and by
compatibility of the divided powers with the differential its boundary has the boundary of the
variable as a factor. -/
public theorem dpow_koszulTateVariable_mem_koszulTateBoundaryKernel (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, finiteTateIndex (koszulTateBase f N) n) (n : ℕ) :
    (koszulTateAlgebra f N).gamma.dpow n (koszulTateVariable f N j) ∈
      koszulTateBoundaryKernel f N := by
  by_cases hpos : koszulTateVariable f N j ∈ positiveEvenPart (koszulTateAlgebra f N).grade
  · match n with
    | 0 =>
        rw [(koszulTateAlgebra f N).gamma.dpow_zero hpos]
        exact one_mem _
    | n + 1 =>
        have htail : (koszulTateAugmentation f N).hom
            (koszulTateDifferential f N
              ((koszulTateAlgebra f N).gamma.dpow (n + 1) (koszulTateVariable f N j))) = 0 := by
          rw [(finiteTateColimitCompatible (koszulTateBase f N)).d_dpow
              (Nat.succ_ne_zero n) hpos, map_mul,
            koszulTateAugmentation_differential_variable f N j, zero_mul]
        rcases positiveEven_homogeneous_eq_zero_or_grade (koszulTateAlgebra f N).grade
          (koszulTateVariable_mem f N j) hpos with hzero | ⟨d, hd⟩
        · refine mem_koszulTateBoundaryKernel_of_mem_grade f N (k := 0) ?_ htail
          have hmem := (koszulTateAlgebra f N).gamma.dpow_mem_grade (d := 0)
            (Nat.succ_ne_zero n) hpos (by rw [hzero]; exact Submodule.zero_mem _)
          simpa using hmem
        · refine mem_koszulTateBoundaryKernel_of_mem_grade f N
            (k := 2 * (n + 1) * (d + 1)) ?_ htail
          exact (koszulTateAlgebra f N).gamma.dpow_mem_grade (Nat.succ_ne_zero n) hpos
            (hd ▸ koszulTateVariable_mem f N j)
  · rw [(koszulTateAlgebra f N).gamma.dpow_null hpos]
    exact zero_mem _

/-- **The augmentation kills every boundary.** -/
public theorem koszulTateAugmentation_differential (f : Fin r → R) (N : ℕ)
    (x : (koszulTateAlgebra f N).carrier) :
    (koszulTateAugmentation f N).hom (koszulTateDifferential f N x) = 0 := by
  obtain ⟨T, hT⟩ := koszulTateAlgebra_finite_support f N x
  have hx : x ∈ koszulTateBoundaryKernel f N :=
    finiteVariableStage_map_mem_subring (koszulTateAlgebra f N).gamma
      (koszulTateCoefficient f N) (koszulTateVariable f N) T
      (AlgHom.id R (koszulTateAlgebra f N).carrier) (koszulTateBoundaryKernel f N)
      (fun p => koszulTateCoefficient_mem_koszulTateBoundaryKernel f N p)
      (fun j _ => koszulTateVariable_mem_koszulTateBoundaryKernel f N j)
      (fun j _ n => dpow_koszulTateVariable_mem_koszulTateBoundaryKernel f N j n) hT
  obtain ⟨s, hs⟩ := exists_gradedPart_decomposition (koszulTateAlgebra f N).grade x
  conv_lhs => rw [hs]
  rw [map_sum, map_sum]
  exact Finset.sum_eq_zero fun m _ => hx m

/-- **Exactness in degree zero.** A degree-zero element killed by the augmentation lies in the
ideal, hence is a combination of the powers `fᵢ^N`, hence is the boundary of the corresponding
combination of the degree-one variables. -/
public theorem exists_koszulTateDifferential_boundary_of_grade_zero (f : Fin r → R) (N : ℕ)
    {a : (koszulTateAlgebra f N).carrier} (ha : a ∈ (koszulTateAlgebra f N).grade 0)
    (haug : (koszulTateAugmentation f N).hom a = 0) :
    ∃ b : (koszulTateAlgebra f N).carrier, b ∈ (koszulTateAlgebra f N).grade 1 ∧
      koszulTateDifferential f N b = a := by
  classical
  let _ : Fintype (finiteTateIndex (koszulTateBase f N) 0) :=
    inferInstanceAs (Fintype (ULift.{u} (Fin r)))
  obtain ⟨p, hp⟩ := (mem_koszulTateAlgebra_grade_zero_iff f N a).1 ha
  have hpI : p ∈ koszulPowerIdeal f N := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rwa [← koszulTateAugmentation_coefficient f N p, hp]
  obtain ⟨c, hc⟩ : ∃ c : Fin r → R, ∑ i, c i * f i ^ N = p := by
    rw [koszulPowerIdeal, show Ideal.span (Set.range fun i => f i ^ N)
        = Submodule.span R (Set.range fun i => f i ^ N) from rfl,
      Submodule.mem_span_range_iff_exists_fun] at hpI
    obtain ⟨c, hc⟩ := hpI
    exact ⟨c, by simpa [smul_eq_mul] using hc⟩
  obtain ⟨b, hb, hdb⟩ := exists_finiteTateColimitDifferential_boundary_of_combination
    (koszulTateBase f N) 0 Finset.univ (fun j => c j.down)
    (fun _ => mem_degreeZeroGrade_zero R R _)
  refine ⟨b, hb, hdb.trans ?_⟩
  rw [← hp]
  refine congrArg (finiteTateInclusion (koszulTateBase f N) 0).hom ?_
  exact Eq.trans (Fintype.sum_equiv Equiv.ulift _
    (fun i : Fin r => c i * f i ^ N) (fun j => rfl)) hc

/-- **Exactness in positive degrees.** -/
public theorem exists_koszulTateDifferential_boundary_of_cycle [IsNoetherianRing R] (f : Fin r → R)
    (N n : ℕ) {a : (koszulTateAlgebra f N).carrier}
    (ha : a ∈ (koszulTateAlgebra f N).grade (n + 1))
    (hda : koszulTateDifferential f N a = 0) :
    ∃ b : (koszulTateAlgebra f N).carrier, b ∈ (koszulTateAlgebra f N).grade (n + 2) ∧
      koszulTateDifferential f N b = a :=
  exists_finiteTateColimitDifferential_boundary_of_cycle (koszulTateBase f N)
    (fun k => hasFiniteSpanningCycles_koszulTateStage f N (k + 1) (k + 1)) n ha hda

/-- The Koszul Tate algebra has degree-zero coefficients and homogeneous variables. -/
public instance koszulTateIsHomogeneousVariableFamily (f : Fin r → R) (N : ℕ) :
    IsHomogeneousVariableFamily (koszulTateAlgebra f N).grade (koszulTateCoefficient f N)
      (koszulTateVariable f N) where
  coefficient_mem := koszulTateCoefficient_mem_grade_zero f N
  variable_homogeneous j := ⟨j.1 + 1, koszulTateVariable_mem f N j⟩

/-- **The Koszul Tate algebra is free on its coefficients and its variables**: the mapping property
of the colimit of the tower. -/
public theorem koszulTateAlgebra_hasVariableMappingProperty (f : Fin r → R) (N : ℕ) :
    HasVariableMappingProperty (koszulTateAlgebra f N).gamma (koszulTateCoefficient f N)
      (koszulTateVariable f N) := by
  intro E g hg t ht
  obtain ⟨F, hF1, hF2⟩ := finiteTateColimit_exists_gradedDPHom (koszulTateBase f N) E
    (degreeZeroDPHom R R E g hg) (fun n j => t ⟨n, j⟩) (fun n j => ht ⟨n, j⟩)
  exact ⟨F.hom.toRingHom, hF1, fun j => hF2 j.1 j.2, F.map_grade, F.map_dpow⟩

/-- **The Koszul Tate algebra is a graded divided power polynomial algebra over `R`**, on the
variables adjoined by the tower. -/
public noncomputable def koszulTatePolynomial (f : Fin r → R) (N : ℕ) :
    GradedDividedPowerPolynomial (koszulTateAlgebra f N).grade (koszulTateAlgebra f N).gamma
      (koszulTateCoefficient f N) :=
  gradedDividedPowerPolynomialOfMappingProperty (koszulTateAlgebra f N).gamma
    (koszulTateCoefficient f N) (koszulTateVariable f N) (koszulTateVariable_mem f N)
    (koszulTateCoefficient_injective f N) (koszulTateAlgebra_finite_support f N)
    (koszulTateAlgebra_hasVariableMappingProperty f N)

end Tower

section Chain

variable (P : ℕ → ℕ → ℕ → Prop)

/-- A relation which can always be continued upwards admits a nondecreasing chain of any finite
length starting at a prescribed point, each consecutive pair related. This packages the choice of
the exponents `n = n₀ < n₁ < … < n_r` of Tag 0GZ4 into a single function. -/
public theorem exists_monotone_chain (n L : ℕ)
    (hex : ∀ a : ℕ, ∃ b : ℕ, a ≤ b ∧ ∀ j, P a b j) :
    ∃ m : ℕ → ℕ, m 0 = n ∧ (∀ i, m i ≤ m (i + 1)) ∧
      ∀ i < L, ∀ j, P (m i) (m (i + 1)) j := by
  induction L with
  | zero => exact ⟨fun _ => n, rfl, fun _ => le_rfl, fun i hi => absurd hi (by omega)⟩
  | succ L ih =>
    obtain ⟨m, hm0, hmono, hkill⟩ := ih
    obtain ⟨b, hb, hbk⟩ := hex (m L)
    refine ⟨fun i => if i ≤ L then m i else b, by simp [hm0], fun i => ?_, fun i hi j => ?_⟩
    · dsimp only
      split_ifs with h1 h2 h2
      · exact hmono i
      · exact (show i = L by omega) ▸ hb
      · omega
      · exact le_rfl
    · dsimp only
      split_ifs with h1 h2 h2
      · exact hkill i (by omega) j
      · exact (show i = L by omega) ▸ hbk j
      · omega
      · omega

end Chain

section Comparison

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The divided powers of the Koszul algebra are compatible with the Koszul differential of the
`N`-th powers. -/
public theorem isCompatibleWithDifferential_koszulPowerDifferential (f : Fin r → R) (N : ℕ) :
    IsCompatibleWithDifferential (exteriorDividedPowerStructure R r)
      (koszulPowerDifferential f N) :=
  isCompatibleWithDifferential_exteriorDividedPowerStructure R r _

/-- The Koszul transition map as a morphism of graded divided power algebras. -/
public noncomputable def koszulTransitionDPHom (f : Fin r → R) (N n : ℕ) :
    GradedDPHom (koszulGradedDPAlgebra R r) (koszulGradedDPAlgebra R r) where
  hom := koszulPowerTransitionHom f N n
  map_grade := fun m _ ha => koszulPowerTransitionHom_mem f N n m ha
  map_dpow := fun k _ ha => (koszulPowerTransitionHom_dpow f N n k ha).symm

/-- **The map `K_N → A` of Tag 0GZ4.** The `i`-th Koszul generator is sent to the degree-one
variable killing `fᵢ^N`, which exists because the base of the tower prescribes one variable per
index `i`. -/
public theorem exists_koszulTateAlpha (f : Fin r → R) (N : ℕ) :
    ∃ α : ExteriorAlgebra R (Fin r → R) →ₐ[R] (koszulTateAlgebra f N).carrier,
      (∀ i : Fin r, α (exteriorGen R r i) = koszulTateVariable f N ⟨0, ULift.up i⟩) ∧
      (∀ (m : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ exteriorGrade R (Fin r → R) m → α x ∈ (koszulTateAlgebra f N).grade m) ∧
      (∀ x, α (koszulPowerDifferential f N x) = koszulTateDifferential f N (α x)) ∧
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
          α ((exteriorDividedPowerStructure R r).dpow k x) =
            (koszulTateAlgebra f N).gamma.dpow k (α x)) := by
  have hdt : ∀ i : Fin r, koszulTateDifferential f N (koszulTateVariable f N ⟨0, ULift.up i⟩) =
      algebraMap R (koszulTateAlgebra f N).carrier (f i ^ N) := by
    intro i
    rw [koszulTateVariable,
      finiteTateColimitDifferential_variable (koszulTateBase f N) 0 (ULift.up i)]
    exact (koszulTateCoefficient f N).commutes (f i ^ N)
  exact exists_algHom_exterior_of_mem_grade_one R r (koszulTateAlgebra f N).grade
    (koszulTateAlgebra f N).gamma (koszulTateDifferential f N)
    (finiteTateColimitDga (koszulTateBase f N)) (fun i => f i ^ N)
    (fun i => koszulTateVariable f N ⟨0, ULift.up i⟩)
    (fun i => koszulTateVariable_mem f N ⟨0, ULift.up i⟩) hdt

/-- **Tate's lifting argument of Tag 0GZ4.** Over a Noetherian ring there is an `N ≥ n` and a
morphism of differential graded divided power algebras `A → K_n` out of the Tate resolution of
`R/(f₁^N, …, f_r^N)` which is the identity of `R` in degree zero and sends the degree-one variable
killing `fᵢ^N` to `fᵢ^(N-n) ξᵢ`.

The map is built stage by stage along the tower. The target of the stage `k` is the Koszul
algebra of an exponent `e k`, the exponents decreasing from `N` to `n` along a chain whose
consecutive transition maps kill the homology in positive degrees; a cycle of degree `k` of the
stage therefore has a boundary as its image in the next Koszul algebra, which is the value given
to the variable killing it. Above degree `r` the Koszul algebra vanishes, so the remaining
variables are sent to zero and the exponent stays at `n`. -/
public theorem exists_koszulTateBeta [IsNoetherianRing R] (f : Fin r → R) (n : ℕ) :
    ∃ N : ℕ, n ≤ N ∧
      ∃ β : GradedDPHom (koszulTateAlgebra f N) (koszulGradedDPAlgebra R r),
        (∀ a, β.hom (koszulTateDifferential f N a) =
            koszulPowerDifferential f n (β.hom a)) ∧
          (∀ p : R, β.hom (koszulTateCoefficient f N p) =
              algebraMap R (ExteriorAlgebra R (Fin r → R)) p) ∧
            ∀ i : Fin r, β.hom (koszulTateVariable f N ⟨0, ULift.up i⟩) =
              koszulPowerTransitionHom f N n (exteriorGen R r i) := by
  classical
  obtain ⟨m, hm0, hmono, hkill⟩ :=
    exists_monotone_chain (KillsKoszulHomology f) n r (fun a => exists_killsKoszulHomology f a)
  have hmmono : Monotone m := monotone_nat_of_le_succ hmono
  refine ⟨m r, by rw [← hm0]; exact hmmono (Nat.zero_le r), ?_⟩
  set N := m r with hNdef
  set A₀ := koszulTateBase f N with hA₀
  set ee : ℕ → ℕ := fun k => m (r - (k - 1)) with hee
  have hee0 : ee 0 = N := rfl
  have hee1 : ee 1 = N := rfl
  have heesucc : ∀ k, ee (k + 1) = m (r - k) := fun _ => rfl
  have heeanti : ∀ k, ee (k + 1) ≤ ee k := fun k => hmmono (by omega)
  have heen : ∀ k, n ≤ ee k := fun k => by rw [← hm0]; exact hmmono (Nat.zero_le _)
  have hkk : ∀ k : ℕ, KillsKoszulHomology f (ee (k + 2)) (ee (k + 1)) k := by
    intro k
    by_cases hk : k < r
    · rw [heesucc, heesucc]
      have h3 : r - (k + 1) + 1 = r - k := by omega
      exact h3 ▸ hkill (r - (k + 1)) (by omega) k
    · have h1 : ee (k + 1) = n := by rw [heesucc, show r - k = 0 by omega, hm0]
      have h2 : ee (k + 2) = n := by rw [heesucc, show r - (k + 1) = 0 by omega, hm0]
      rw [h1, h2]
      exact killsKoszulHomology_of_lt f n n (by omega)
  -- the morphism out of the base: the structure map of the Koszul algebra
  have hbase : ∀ p : (finiteTateAlgebra A₀ 0).carrier,
      Algebra.ofId R (ExteriorAlgebra R (Fin r → R)) p ∈
        (koszulGradedDPAlgebra R r).grade 0 :=
    fun p => SetLike.algebraMap_mem_graded (exteriorGrade R (Fin r → R)) p
  set G0 : GradedDPHom (finiteTateAlgebra A₀ 0) (koszulGradedDPAlgebra R r) :=
    degreeZeroDPHom R R (koszulGradedDPAlgebra R r)
      (Algebra.ofId R (ExteriorAlgebra R (Fin r → R))) hbase with hG0def
  have hG0val : ∀ p : R, G0.hom p = algebraMap R (ExteriorAlgebra R (Fin r → R)) p :=
    fun _ => rfl
  have hG0d : ∀ (e : ℕ) (a : (finiteTateAlgebra A₀ 0).carrier),
      G0.hom (finiteTateDifferential A₀ 0 a) = koszulPowerDifferential f e (G0.hom a) := by
    intro e a
    have hR : koszulPowerDifferential f e (G0.hom a) = 0 :=
      IsDifferentialGradedAlgebra.d_grade_zero
        (self := isDifferentialGradedAlgebra_koszulPowerDifferential f e) (hbase a)
    rw [show finiteTateDifferential A₀ 0 a = 0 from rfl, hR]
    exact _root_.map_zero G0.hom
  -- the first step: the degree-one variables go to the Koszul generators
  have hG0comp : ∀ a : (finiteTateAlgebra A₀ 0).carrier,
      ((koszulTransitionDPHom f (ee 0) (ee 1)).comp G0).hom (finiteTateDifferential A₀ 0 a) =
        koszulPowerDifferential f (ee 1)
          (((koszulTransitionDPHom f (ee 0) (ee 1)).comp G0).hom a) := by
    intro a
    have hR : koszulPowerDifferential f (ee 1)
        (koszulPowerTransitionHom f (ee 0) (ee 1) (G0.hom a)) = 0 :=
      IsDifferentialGradedAlgebra.d_grade_zero
        (self := isDifferentialGradedAlgebra_koszulPowerDifferential f (ee 1))
        (koszulPowerTransitionHom_mem f (ee 0) (ee 1) 0 (hbase a))
    show koszulPowerTransitionHom f (ee 0) (ee 1) (G0.hom (finiteTateDifferential A₀ 0 a)) =
      koszulPowerDifferential f (ee 1) (koszulPowerTransitionHom f (ee 0) (ee 1) (G0.hom a))
    rw [show finiteTateDifferential A₀ 0 a = 0 from rfl, hR, _root_.map_zero G0.hom]
    exact _root_.map_zero (koszulPowerTransitionHom f (ee 0) (ee 1))
  have hdt0 : ∀ j : finiteTateIndex A₀ 0,
      koszulPowerDifferential f (ee 1) (exteriorGen R r j.down) =
        ((koszulTransitionDPHom f (ee 0) (ee 1)).comp G0).hom (finiteTateCycle A₀ 0 j) := by
    intro j
    show _ = koszulPowerTransitionHom f (ee 0) (ee 1) (G0.hom (f j.down ^ N))
    rw [hG0val, AlgHom.commutes, hee1, koszulPowerDifferential_exteriorGen]
  obtain ⟨G1, hG1res, hG1gen, hG1d⟩ :=
    finiteTateStep_exists_gradedDPHom_comm_differential A₀ 0 (koszulGradedDPAlgebra R r)
      (koszulPowerDifferential f (ee 1))
      (isDifferentialGradedAlgebra_koszulPowerDifferential f (ee 1))
      (isCompatibleWithDifferential_koszulPowerDifferential f (ee 1))
      ((koszulTransitionDPHom f (ee 0) (ee 1)).comp G0) hG0comp
      (fun j => exteriorGen R r j.down) (fun j => exteriorGen_mem R r j.down) hdt0
  -- the inductive step
  have hstep : ∀ (k : ℕ)
      (G : GradedDPHom (finiteTateAlgebra A₀ (k + 1)) (koszulGradedDPAlgebra R r)),
      (∀ a, G.hom (finiteTateDifferential A₀ (k + 1) a) =
        koszulPowerDifferential f (ee (k + 1)) (G.hom a)) →
      ∃ G' : GradedDPHom (finiteTateAlgebra A₀ (k + 2)) (koszulGradedDPAlgebra R r),
        (∀ a, G'.hom (finiteTateDifferential A₀ (k + 2) a) =
            koszulPowerDifferential f (ee (k + 2)) (G'.hom a)) ∧
          ∀ x, G'.hom ((finiteTateStep A₀ (k + 1)).hom x) =
            koszulPowerTransitionHom f (ee (k + 1)) (ee (k + 2)) (G.hom x) := by
    intro k G hG
    have hGcomp : ∀ a : (finiteTateAlgebra A₀ (k + 1)).carrier,
        ((koszulTransitionDPHom f (ee (k + 1)) (ee (k + 2))).comp G).hom
            (finiteTateDifferential A₀ (k + 1) a) =
          koszulPowerDifferential f (ee (k + 2))
            (((koszulTransitionDPHom f (ee (k + 1)) (ee (k + 2))).comp G).hom a) := by
      intro a
      show koszulPowerTransitionHom f (ee (k + 1)) (ee (k + 2))
          (G.hom (finiteTateDifferential A₀ (k + 1) a)) =
        koszulPowerDifferential f (ee (k + 2))
          (koszulPowerTransitionHom f (ee (k + 1)) (ee (k + 2)) (G.hom a))
      rw [hG a]
      exact koszulPowerTransitionHom_differential f
        (show ee (k + 2) ≤ ee (k + 1) from heeanti (k + 1)) (G.hom a)
    have hvals : ∀ j : finiteTateIndex A₀ (k + 1),
        ∃ t : ExteriorAlgebra R (Fin r → R), t ∈ (koszulGradedDPAlgebra R r).grade (k + 2) ∧
          koszulPowerDifferential f (ee (k + 2)) t =
            ((koszulTransitionDPHom f (ee (k + 1)) (ee (k + 2))).comp G).hom
              (finiteTateCycle A₀ (k + 1) j) := by
      intro j
      have hz : G.hom (finiteTateDifferential A₀ (k + 1)
          (finiteTateCycle A₀ (k + 1) j)) = 0 := by
        rw [finiteTateCycle_cycle A₀ (k + 1) j]
        exact _root_.map_zero G.hom
      exact hkk k _ (G.map_grade (k + 1) _ (finiteTateCycle_mem A₀ (k + 1) j))
        ((hG (finiteTateCycle A₀ (k + 1) j)).symm.trans hz)
    choose t ht hdt using hvals
    obtain ⟨G', hG'res, -, hG'd⟩ :=
      finiteTateStep_exists_gradedDPHom_comm_differential A₀ (k + 1) (koszulGradedDPAlgebra R r)
        (koszulPowerDifferential f (ee (k + 2)))
        (isDifferentialGradedAlgebra_koszulPowerDifferential f (ee (k + 2)))
        (isCompatibleWithDifferential_koszulPowerDifferential f (ee (k + 2)))
        ((koszulTransitionDPHom f (ee (k + 1)) (ee (k + 2))).comp G) hGcomp t ht hdt
    exact ⟨G', hG'd, hG'res⟩
  -- iterate the step
  let Seq : (k : ℕ) → {G : GradedDPHom (finiteTateAlgebra A₀ (k + 1)) (koszulGradedDPAlgebra R r) //
      ∀ a, G.hom (finiteTateDifferential A₀ (k + 1) a) =
        koszulPowerDifferential f (ee (k + 1)) (G.hom a)} := fun k =>
    Nat.rec (motive := fun k =>
        {G : GradedDPHom (finiteTateAlgebra A₀ (k + 1)) (koszulGradedDPAlgebra R r) //
        ∀ a, G.hom (finiteTateDifferential A₀ (k + 1) a) =
          koszulPowerDifferential f (ee (k + 1)) (G.hom a)})
      ⟨G1, hG1d⟩ (fun k p => ⟨(hstep k p.1 p.2).choose, (hstep k p.1 p.2).choose_spec.1⟩) k
  let G : (k : ℕ) → GradedDPHom (finiteTateAlgebra A₀ k) (koszulGradedDPAlgebra R r) := fun k =>
    Nat.rec (motive := fun k => GradedDPHom (finiteTateAlgebra A₀ k) (koszulGradedDPAlgebra R r))
      G0 (fun k _ => (Seq k).1) k
  have hGd : ∀ (k : ℕ) (a : (finiteTateAlgebra A₀ k).carrier),
      (G k).hom (finiteTateDifferential A₀ k a) =
        koszulPowerDifferential f (ee k) ((G k).hom a) := by
    intro k
    match k with
    | 0 => exact hG0d (ee 0)
    | k + 1 => exact (Seq k).2
  have hGres : ∀ (k : ℕ) (x : (finiteTateAlgebra A₀ k).carrier),
      (G (k + 1)).hom ((finiteTateStep A₀ k).hom x) =
        koszulPowerTransitionHom f (ee k) (ee (k + 1)) ((G k).hom x) := by
    intro k
    match k with
    | 0 => exact hG1res
    | k + 1 => exact (hstep k (Seq k).1 (Seq k).2).choose_spec.2
  -- pass to the colimit
  let H : (k : ℕ) → GradedDPHom (finiteTateAlgebra A₀ k) (koszulGradedDPAlgebra R r) := fun k =>
    (koszulTransitionDPHom f (ee k) n).comp (G k)
  have hHstep : ∀ (k : ℕ) (x : (finiteTateAlgebra A₀ k).carrier),
      (H (k + 1)).hom ((finiteTateStep A₀ k).hom x) = (H k).hom x := by
    intro k x
    show koszulPowerTransitionHom f (ee (k + 1)) n ((G (k + 1)).hom ((finiteTateStep A₀ k).hom x))
      = koszulPowerTransitionHom f (ee k) n ((G k).hom x)
    rw [hGres k x]
    exact koszulPowerTransitionHom_comp f (heen (k + 1)) (heeanti k) ((G k).hom x)
  have hHd : ∀ (k : ℕ) (a : (finiteTateAlgebra A₀ k).carrier),
      (H k).hom (finiteTateDifferential A₀ k a) =
        koszulPowerDifferential f n ((H k).hom a) := by
    intro k a
    show koszulPowerTransitionHom f (ee k) n ((G k).hom (finiteTateDifferential A₀ k a)) = _
    rw [hGd k a]
    exact koszulPowerTransitionHom_differential f (heen k) ((G k).hom a)
  obtain ⟨F, hFres, hFd⟩ := finiteTateColimit_exists_gradedDPHom_of_family A₀
    (koszulGradedDPAlgebra R r)
    (koszulPowerDifferential f n) H hHstep hHd
  refine ⟨F, hFd, fun p => ?_, fun i => ?_⟩
  · refine (hFres 0 p).trans ?_
    show koszulPowerTransitionHom f (ee 0) n (G0.hom p) = _
    rw [hG0val, AlgHom.commutes]
  · rw [koszulTateVariable, finiteTateVariable, hFres 1 (finiteTateGenerator A₀ 0 (ULift.up i))]
    show koszulPowerTransitionHom f (ee 1) n ((G 1).hom (finiteTateGenerator A₀ 0 (ULift.up i)))
      = _
    rw [show (G 1).hom (finiteTateGenerator A₀ 0 (ULift.up i)) = exteriorGen R r i from
      hG1gen (ULift.up i), hee1]

/-- **The canonical map from the Koszul algebra onto the quotient.** It kills the Koszul
generators and is the quotient map in degree zero. -/
public noncomputable def koszulPowerAugmentation (f : Fin r → R) (N : ℕ) :
    ExteriorAlgebra R (Fin r → R) →ₐ[R] R ⧸ koszulPowerIdeal f N :=
  ExteriorAlgebra.lift R ⟨0, fun _ => by simp⟩

/-- The canonical map kills the degree-one part of the Koszul algebra. -/
public theorem koszulPowerAugmentation_ι (f : Fin r → R) (N : ℕ) (p : Fin r → R) :
    koszulPowerAugmentation f N (ExteriorAlgebra.ι R p) = 0 := by
  rw [koszulPowerAugmentation, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- The canonical map is the quotient map on the degree-zero part of the Koszul algebra. -/
public theorem koszulPowerAugmentation_algebraMap (f : Fin r → R) (N : ℕ) (c : R) :
    koszulPowerAugmentation f N (algebraMap R (ExteriorAlgebra R (Fin r → R)) c) =
      Ideal.Quotient.mk (koszulPowerIdeal f N) c :=
  (koszulPowerAugmentation f N).commutes c

end Comparison

section Main

variable {R : Type u} [CommRing R] {r : ℕ}

/-- Algebra homomorphisms out of the Koszul algebra agreeing on the generators are equal. -/
private theorem algHom_exterior_ext_gen {B : Type*} [Semiring B] [Algebra R B]
    {g h : ExteriorAlgebra R (Fin r → R) →ₐ[R] B}
    (hgh : ∀ i, g (exteriorGen R r i) = h (exteriorGen R r i)) : g = h := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun p => ?_)
  change g (ExteriorAlgebra.ι R p) = h (ExteriorAlgebra.ι R p)
  rw [ι_eq_sum_exteriorGen, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hgh i, AlgHom.commutes, AlgHom.commutes]

/-- **Tag 0GZ4.** Let `R` be a Noetherian ring and `f₁, …, f_r ∈ R`. Write `K_m` for the Koszul
divided power algebra `R⟨ξ₁, …, ξ_r⟩` with `ξᵢ` of degree one and `d(ξᵢ) = fᵢ^m`, and `K_M → K_m`
for the transition map `ξᵢ ↦ fᵢ^(M-m) ξᵢ`. Then for every `n` there is an `N ≥ n` and maps
`K_N → A → R/(f₁^N, …, f_r^N)` and `A → K_n` such that `(A, d, γ)` is a divided power
differential graded algebra as in Definition 09PJ, `A → R/(f₁^N, …, f_r^N)` is a
quasi-isomorphism, the composition `K_N → A → R/(f₁^N, …, f_r^N)` is the canonical map, the
composition `K_N → A → K_n` is the transition map, `A₀ = R → R/(f₁^N, …, f_r^N)` is the canonical
surjection, `A` is a graded divided power polynomial algebra over `R` with finitely many
generators in each degree, and `A → K_n` is a homomorphism of differential graded `R`-algebras
compatible with divided powers inducing the canonical map
`R/(f₁^N, …, f_r^N) → R/(f₁^n, …, f_r^n)` on homology in degree zero. -/
@[stacks 0GZ4]
public theorem exists_tateResolution_koszulPowers [IsNoetherianRing R] (f : Fin r → R) (n : ℕ) :
    ∃ (N : ℕ) (hN : n ≤ N) (A : GradedDPAlgebra.{u, u} R) (d : A.carrier →ₗ[R] A.carrier)
        (ι : R →ₐ[R] A.carrier) (ε : A.carrier →ₐ[R] R ⧸ koszulPowerIdeal f N)
        (α : ExteriorAlgebra R (Fin r → R) →ₐ[R] A.carrier)
        (β : A.carrier →ₐ[R] ExteriorAlgebra R (Fin r → R)),
      -- (1) `(A, d, γ)` is as in Definition 09PJ
      IsDifferentialGradedAlgebra A.grade d ∧ IsCompatibleWithDifferential A.gamma d ∧
      -- (6) a graded divided power polynomial algebra over `R`, degreewise finitely generated
      (∃ P : GradedDividedPowerPolynomial A.grade A.gamma ι, ∀ i : ℕ, Finite (P.indices i)) ∧
      -- (5) `A₀ = R`, and `A₀ → R/(f₁^N, …, f_r^N)` is the canonical surjection
      Function.Injective ι ∧
      (∀ a : A.carrier, a ∈ A.grade 0 ↔ ∃ c : R, ι c = a) ∧
      (∀ c : R, ε (ι c) = Ideal.Quotient.mk (koszulPowerIdeal f N) c) ∧
      -- (2) `ε` is a quasi-isomorphism onto `R/(f₁^N, …, f_r^N)`
      Function.Surjective ε ∧
      (∀ (k : ℕ) (a : A.carrier), 0 < k → a ∈ A.grade k → ε a = 0) ∧
      (∀ a : A.carrier, ε (d a) = 0) ∧
      (∀ a : A.carrier, a ∈ A.grade 0 → ε a = 0 → ∃ b ∈ A.grade 1, d b = a) ∧
      (∀ (k : ℕ) (a : A.carrier), a ∈ A.grade (k + 1) → d a = 0 →
        ∃ b ∈ A.grade (k + 2), d b = a) ∧
      -- `α : K_N → A` is a morphism of differential graded divided power algebras
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ exteriorGrade R (Fin r → R) k → α x ∈ A.grade k) ∧
      (∀ x, α (koszulPowerDifferential f N x) = d (α x)) ∧
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
          α ((exteriorDividedPowerStructure R r).dpow k x) = A.gamma.dpow k (α x)) ∧
      -- (7) `β : A → K_n` is a morphism of differential graded divided power algebras
      (∀ (k : ℕ) (a : A.carrier), a ∈ A.grade k → β a ∈ exteriorGrade R (Fin r → R) k) ∧
      (∀ a, β (d a) = koszulPowerDifferential f n (β a)) ∧
      (∀ (k : ℕ) (a : A.carrier), a ∈ positiveEvenPart A.grade →
        β (A.gamma.dpow k a) = (exteriorDividedPowerStructure R r).dpow k (β a)) ∧
      -- (3) the composition `K_N → A → R/(f₁^N, …, f_r^N)` is the canonical map
      (∀ x, ε (α x) = koszulPowerAugmentation f N x) ∧
      -- (4) the composition `K_N → A → K_n` is the transition map
      (∀ x, β (α x) = koszulPowerTransitionHom f N n x) ∧
      -- (7) `β` is the identity of `R` in degree zero, hence induces the canonical map
      -- `R/(f₁^N, …, f_r^N) → R/(f₁^n, …, f_r^n)` on homology in degree zero
      (∀ c : R, β (ι c) = algebraMap R (ExteriorAlgebra R (Fin r → R)) c) ∧
      (∀ a : A.carrier, a ∈ A.grade 0 →
        koszulPowerAugmentation f n (β a) =
          Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f hN) (ε a)) := by
  obtain ⟨N, hnN, β, hβd, hβcoeff, hβvar⟩ := exists_koszulTateBeta f n
  obtain ⟨α, hαgen, hαgrade, hαd, hαdpow⟩ := exists_koszulTateAlpha f N
  refine ⟨N, hnN, koszulTateAlgebra f N, koszulTateDifferential f N, koszulTateCoefficient f N,
    (koszulTateAugmentation f N).hom, α, β.hom,
    finiteTateColimitDga (koszulTateBase f N), finiteTateColimitCompatible (koszulTateBase f N),
    ⟨koszulTatePolynomial f N, fun i =>
      finite_finiteTateIndex (koszulTateBase f N) (finite_koszulTateBase_kill f N) i⟩,
    koszulTateCoefficient_injective f N,
    mem_koszulTateAlgebra_grade_zero_iff f N, koszulTateAugmentation_coefficient f N, ?_,
    fun k a hk ha => koszulTateAugmentation_positive f N (by omega) ha,
    koszulTateAugmentation_differential f N,
    fun a ha haug => exists_koszulTateDifferential_boundary_of_grade_zero f N ha haug,
    fun k a ha hda => exists_koszulTateDifferential_boundary_of_cycle f N k ha hda,
    hαgrade, hαd, hαdpow, β.map_grade, hβd, fun k a ha => (β.map_dpow k a ha).symm,
    ?_, ?_, hβcoeff, ?_⟩
  · intro z
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨koszulTateCoefficient f N c, (koszulTateAugmentation_coefficient f N c).trans hc⟩
  · have hcomp : (koszulTateAugmentation f N).hom.comp α = koszulPowerAugmentation f N :=
      algHom_exterior_ext_gen fun i => ?_
    · exact AlgHom.congr_fun hcomp
    change (koszulTateAugmentation f N).hom (α (exteriorGen R r i)) =
      koszulPowerAugmentation f N (exteriorGen R r i)
    rw [hαgen i, koszulTateAugmentation_variable, exteriorGen_eq, koszulPowerAugmentation_ι]
    rfl
  · have hcomp : β.hom.comp α = koszulPowerTransitionHom f N n :=
      algHom_exterior_ext_gen fun i => ?_
    · exact AlgHom.congr_fun hcomp
    change β.hom (α (exteriorGen R r i)) = koszulPowerTransitionHom f N n (exteriorGen R r i)
    rw [hαgen i, hβvar i]
  · intro a ha
    obtain ⟨c, rfl⟩ := (mem_koszulTateAlgebra_grade_zero_iff f N a).1 ha
    refine Eq.trans (congrArg (koszulPowerAugmentation f n) (hβcoeff c)) ?_
    refine Eq.trans (koszulPowerAugmentation_algebraMap f n c) ?_
    refine Eq.trans (Ideal.Quotient.factor_mk (koszulPowerIdeal_le_of_le f hnN) c).symm ?_
    exact congrArg (Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f hnN))
      (koszulTateAugmentation_coefficient f N c).symm

end Main

end DividedPowers.TateResolution

end

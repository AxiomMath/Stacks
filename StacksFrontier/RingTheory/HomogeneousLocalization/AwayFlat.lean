module

public import StacksFrontier.RingTheory.Flat.DirectLimit
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayDirectLimit

/-!
# Flatness of the degree-zero localization at a homogeneous element

Let `A` be a graded algebra over a commutative ring `R`, with grading `𝒜 : ι → Submodule R A`,
and let `a ∈ 𝒜 d` be homogeneous. If the graded pieces `𝒜 (n • d)` are flat `R`-modules for all
large `n`, then the degree-zero localization `HomogeneousLocalization.Away 𝒜 a` is a flat
`R`-module.

The degree-zero localization is the direct limit of the system

`𝒜 0 → 𝒜 d → 𝒜 (2 • d) → ⋯`,

the maps being multiplication by `a` (`HomogeneousLocalization.Away.directLimitEquiv`). It is
also the direct limit of the truncated system `𝒜 (N • d) → 𝒜 ((N + 1) • d) → ⋯`, for every `N`,
and a direct limit of flat modules is flat.

## Main definitions

* `HomogeneousLocalization.Away.tailMulPow` is the transition map of the truncated system.
* `HomogeneousLocalization.Away.tailDirectLimitEquiv` identifies `Away 𝒜 a` with the direct
  limit of the truncated system.

## Main results

* `HomogeneousLocalization.Away.flat_of_eventually_flat`: if `𝒜 (n • d)` is a flat `R`-module
  for every `n ≥ N`, then so is `HomogeneousLocalization.Away 𝒜 a`.

## Implementation notes

The truncated system is reindexed by `ℕ` rather than carried as a subtype `{n // N ≤ n}` of the
original index, so that the directedness, nonemptiness and decidable-equality hypotheses of
`colimit_flat_of_flat` are the ones already available for `ℕ`.

## References

* [Stacks Project, Tag 05UT](https://stacks.math.columbia.edu/tag/05UT)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

namespace HomogeneousLocalization.Away

universe u v w

variable {ι : Type u} {R : Type v} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → Submodule R A) [GradedRing 𝒜]
  {d : ι} {a : A} (ha : a ∈ 𝒜 d) (N : ℕ)

/-- **The transition map of the system truncated below `N`.** The `n`-th term of the truncated
system is `𝒜 ((N + n) • d)`, and the map from the `n`-th to the `m`-th term is multiplication by
`a ^ (m - n)`, exactly as in the untruncated system
`HomogeneousLocalization.Away.mulPow`. -/
public def tailMulPow (n m : ℕ) (h : n ≤ m) : 𝒜 ((N + n) • d) →ₗ[R] 𝒜 ((N + m) • d) :=
  mulPow 𝒜 ha (N + n) (N + m) (by omega)

/-- The system truncated below `N` is a directed system. -/
public instance tailDirectedSystem :
    DirectedSystem (fun n : ℕ ↦ (𝒜 ((N + n) • d) : Type _)) (tailMulPow 𝒜 ha N · · ·) := by
  refine ⟨fun i x ↦ Subtype.ext ?_, fun k j i hij hjk x ↦ Subtype.ext ?_⟩
  · simp [tailMulPow]
  · simp only [tailMulPow, coe_mulPow, ← mul_assoc, ← pow_add]
    congr 2
    omega

/-- The map out of the direct limit of the truncated system induced by the fractions
`x ↦ x / a ^ (N + n)`. -/
public def tailLift :
    Module.DirectLimit (fun n : ℕ ↦ (𝒜 ((N + n) • d) : Type _)) (tailMulPow 𝒜 ha N) →ₗ[R]
      Away 𝒜 a :=
  Module.DirectLimit.lift R ℕ _ _ (fun n ↦ mkLinearMap 𝒜 ha (N + n))
    fun _ _ h x ↦ mkLinearMap_mulPow 𝒜 ha _ _ (by omega) x

/-- `HomogeneousLocalization.Away.tailLift` sends `x` in the `n`-th term of the truncated system
to the fraction `x / a ^ (N + n)`. -/
@[simp]
public theorem tailLift_of (n : ℕ) (x : 𝒜 ((N + n) • d)) :
    tailLift 𝒜 ha N (Module.DirectLimit.of R ℕ _ (tailMulPow 𝒜 ha N) n x) =
      Away.mk 𝒜 ha (N + n) x x.2 :=
  Module.DirectLimit.lift_of ..

/-- **Every element of `Away 𝒜 a` comes from the truncated system**:
`HomogeneousLocalization.Away.tailLift` is surjective. -/
public theorem tailLift_surjective : Function.Surjective (tailLift 𝒜 ha N) := by
  intro z
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 ha z
  have hle : n ≤ N + n := Nat.le_add_left n N
  have hmem : a ^ (N + n - n) * x ∈ 𝒜 ((N + n) • d) := by
    have := pow_mul_mem 𝒜 ha hx (N + n - n)
    rwa [Nat.add_sub_cancel' hle] at this
  refine ⟨Module.DirectLimit.of R ℕ _ (tailMulPow 𝒜 ha N) n ⟨a ^ (N + n - n) * x, hmem⟩, ?_⟩
  rw [tailLift_of]
  exact mk_eq_mk_of_le 𝒜 ha hle x hx hmem

/-- The map `HomogeneousLocalization.Away.tailLift` out of the direct limit of the truncated
system is injective. -/
public theorem tailLift_injective : Function.Injective (tailLift 𝒜 ha N) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨n, x, rfl⟩ := Module.DirectLimit.exists_of z
  rw [tailLift_of] at hz
  obtain ⟨k, hk⟩ := (mk_eq_zero_iff 𝒜 ha (N + n) x x.2).mp hz
  have hstep : tailMulPow 𝒜 ha N n (n + k) (Nat.le_add_right n k) x = 0 := by
    refine Subtype.ext ?_
    simp only [tailMulPow, coe_mulPow, ZeroMemClass.coe_zero]
    rwa [show N + (n + k) - (N + n) = k by omega]
  rw [show Module.DirectLimit.of R ℕ _ (tailMulPow 𝒜 ha N) n x =
      Module.DirectLimit.of R ℕ _ (tailMulPow 𝒜 ha N) (n + k)
        (tailMulPow 𝒜 ha N n (n + k) (Nat.le_add_right n k) x) from Module.DirectLimit.of_f.symm,
    hstep, map_zero]

/-- **`Away 𝒜 a` is the direct limit of the graded pieces `𝒜 ((N + n) • d)` along multiplication
by `a`,** for any `N`. The fraction `x / a ^ (N + n)` is the image of `x` in the `n`-th term of
the truncated system. For `N = 0` this is
`HomogeneousLocalization.Away.directLimitEquiv`. -/
public def tailDirectLimitEquiv :
    Module.DirectLimit (fun n : ℕ ↦ (𝒜 ((N + n) • d) : Type _)) (tailMulPow 𝒜 ha N) ≃ₗ[R]
      Away 𝒜 a :=
  LinearEquiv.ofBijective (tailLift 𝒜 ha N)
    ⟨tailLift_injective 𝒜 ha N, tailLift_surjective 𝒜 ha N⟩

/-- `HomogeneousLocalization.Away.tailDirectLimitEquiv` sends `x` in the `n`-th term of the
truncated system to the fraction `x / a ^ (N + n)`. -/
@[simp]
public theorem tailDirectLimitEquiv_of (n : ℕ) (x : 𝒜 ((N + n) • d)) :
    tailDirectLimitEquiv 𝒜 ha N (Module.DirectLimit.of R ℕ _ (tailMulPow 𝒜 ha N) n x) =
      Away.mk 𝒜 ha (N + n) x x.2 :=
  tailLift_of 𝒜 ha N n x

include ha in
/-- **The degree-zero localization at a homogeneous element of degree `d` is flat as soon as the
graded pieces of degree a large multiple of `d` are flat.** If `𝒜 (n • d)` is a flat `R`-module
for every `n ≥ N`, then so is `HomogeneousLocalization.Away 𝒜 a`. -/
public theorem flat_of_eventually_flat
    (hflat : ∀ n : ℕ, N ≤ n → Module.Flat R (𝒜 (n • d))) :
    Module.Flat R (Away 𝒜 a) := by
  classical
  have _ : ∀ n : ℕ, Module.Flat R (𝒜 ((N + n) • d)) := fun n ↦ hflat (N + n) (by omega)
  have _ : Module.Flat R
      (Module.DirectLimit (fun n : ℕ ↦ (𝒜 ((N + n) • d) : Type _)) (tailMulPow 𝒜 ha N)) :=
    colimit_flat_of_flat _ (tailMulPow 𝒜 ha N)
  exact Module.Flat.of_linearEquiv (tailDirectLimitEquiv 𝒜 ha N).symm

end HomogeneousLocalization.Away

end

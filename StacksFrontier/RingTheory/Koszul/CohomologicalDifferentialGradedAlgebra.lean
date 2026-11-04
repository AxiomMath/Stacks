module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulTransition
public import StacksFrontier.RingTheory.Koszul.Cone
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul algebra as a cohomologically graded differential graded algebra

For an `R`-module `E` and a functional `φ : E →ₗ[R] R`, the Koszul algebra of `φ` is the
exterior algebra `⋀[R] E` with contraction by `φ` as its differential. The natural grading by
exterior powers is homological: contraction lowers the exterior degree by one. Reading the
`k`-th exterior power in degree `-k` turns this into a cohomologically `ℤ`-graded differential
graded algebra, whose differential raises the degree by one; that is the shape of the bundled
object `DifferentialGradedAlgebra`.

Specialising to `E = Rʳ` and `φ = Koszul.seqDual (fun i ↦ fᵢ ^ n)` gives, for a finite sequence
`f₁, …, f_r ∈ R`, the algebra `K_n = R⟨ξ₁, …, ξ_r⟩` with `ξᵢ` of degree `-1` and
`d ξᵢ = fᵢ ^ n`. For `1 ≤ n ≤ m` the map scaling `ξᵢ` by `fᵢ ^ (m - n)` is a homomorphism
`K_m → K_n` of differential graded algebras, and these maps compose, so the `K_n` form an
inverse system.

## Main definitions

* `Koszul.cohomologicalExteriorGrade`: the exterior algebra graded by `ℤ`, with the `k`-th
  exterior power in degree `-k` and nothing in positive degrees.
* `Koszul.cohomologicalDifferentialGradedAlgebra`: the Koszul algebra of a functional, as an
  object of `DifferentialGradedAlgebra`.
* `Koszul.cohomologicalDifferentialGradedAlgebraHom`: the homomorphism induced by a linear map
  of the underlying modules.
* `Koszul.powAlgebra`: the algebra `K_n` of a finite sequence of ring elements.
* `Koszul.powTransition`: the transition homomorphism `K_m → K_n` for `1 ≤ n ≤ m`.

## Main results

* `Koszul.cohomologicalExteriorGrade_neg_natCast`: degree `-k` is the `k`-th exterior power.
* `Koszul.powAlgebra_d_ι`: the differential of `K_n` sends `ξᵢ` to `fᵢ ^ n`.
* `Koszul.powTransition_apply_ι`: the transition homomorphism scales `ξᵢ` by `fᵢ ^ (m - n)`.
* `Koszul.powTransition_comp`: the transition homomorphisms compose.

## Implementation notes

`DifferentialGradedAlgebra` bundles its grading as a `GradedAlgebra`, hence as a genuine
`DirectSum.Decomposition` indexed by `ℤ`. Mathlib grades the exterior algebra by `ℕ`
(`ExteriorAlgebra.gradedAlgebra`), so the `ℤ`-indexed decomposition is obtained by transporting
that one along `k ↦ -k`: the additive map `Koszul.toCohomologicalDirectSum` reindexes the direct
sum summandwise, using `LinearEquiv.ofEq` to identify the `k`-th exterior power with the piece of
degree `-k`, and the two round-trip identities are checked on the summands with
`DirectSum.addHom_ext`. The sign in the Leibniz rule is unchanged by the regrading, because
`(-1) ^ (-k) = (-1) ^ k`.

## References

* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 0GZ3](https://stacks.math.columbia.edu/tag/0GZ3)
-/

@[expose] public section

namespace Koszul

universe u v

open scoped DirectSum ExteriorAlgebra

open DividedPowers.TateResolution (exteriorGrade)

section Grading

variable (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]

/-- The exterior algebra of `E`, graded by `ℤ` with the `k`-th exterior power in degree `-k`
and nothing in positive degrees. This is the cohomological reading of the exterior grading. -/
def cohomologicalExteriorGrade (n : ℤ) : Submodule R (ExteriorAlgebra R E) :=
  if n ≤ 0 then exteriorGrade R E (-n).toNat else ⊥

/-- In nonpositive degree `n`, the cohomological piece is the `(-n)`-th exterior power. -/
theorem cohomologicalExteriorGrade_of_nonpos {n : ℤ} (hn : n ≤ 0) :
    cohomologicalExteriorGrade R E n = exteriorGrade R E (-n).toNat := by
  simp [cohomologicalExteriorGrade, hn]

/-- In positive degree the cohomological piece is zero. -/
theorem cohomologicalExteriorGrade_of_pos {n : ℤ} (hn : 0 < n) :
    cohomologicalExteriorGrade R E n = ⊥ := by
  simp [cohomologicalExteriorGrade, show ¬ n ≤ 0 from by omega]

/-- The piece of cohomological degree `-k` is the `k`-th exterior power. -/
@[simp]
theorem cohomologicalExteriorGrade_neg_natCast (k : ℕ) :
    cohomologicalExteriorGrade R E (-(k : ℤ)) = exteriorGrade R E k := by
  rw [cohomologicalExteriorGrade_of_nonpos R E (by omega)]
  congr 1
  omega

/-- The piece of cohomological degree `0` is the `0`-th exterior power. -/
theorem cohomologicalExteriorGrade_zero :
    cohomologicalExteriorGrade R E 0 = exteriorGrade R E 0 := by
  simpa using cohomologicalExteriorGrade_neg_natCast R E 0

/-- An element of a cohomological piece of positive degree is zero. -/
theorem eq_zero_of_mem_cohomologicalExteriorGrade_of_pos {n : ℤ} (hn : 0 < n)
    {x : ExteriorAlgebra R E} (hx : x ∈ cohomologicalExteriorGrade R E n) : x = 0 := by
  rw [cohomologicalExteriorGrade_of_pos R E hn] at hx
  simpa using hx

/-- An element of a cohomological piece is zero or lies in an exterior power `k` with degree
`-k`. -/
private theorem exists_or_eq_zero_of_mem_cohomologicalExteriorGrade {n : ℤ}
    {x : ExteriorAlgebra R E} (hx : x ∈ cohomologicalExteriorGrade R E n) :
    (∃ k : ℕ, n = -(k : ℤ) ∧ x ∈ exteriorGrade R E k) ∨ x = 0 := by
  by_cases hn : n ≤ 0
  · refine Or.inl ⟨(-n).toNat, by omega, ?_⟩
    rwa [cohomologicalExteriorGrade_of_nonpos R E hn] at hx
  · exact Or.inr (eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R E (by omega) hx)

/-- The cohomological pieces of the exterior algebra form a graded monoid. -/
instance cohomologicalExteriorGrade.gradedMonoid :
    SetLike.GradedMonoid (cohomologicalExteriorGrade R E) where
  one_mem := by
    rw [cohomologicalExteriorGrade_zero]
    exact SetLike.one_mem_graded (exteriorGrade R E)
  mul_mem := by
    intro i j a b ha hb
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
        rw [cohomologicalExteriorGrade_neg_natCast] at ha hb
        rw [show -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ) by push_cast; ring,
          cohomologicalExteriorGrade_neg_natCast]
        exact SetLike.mul_mem_graded ha hb
      · rw [eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R E (by omega) hb, mul_zero]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R E (by omega) ha, zero_mul]
      exact Submodule.zero_mem _

/-- The `k`-th exterior power, read as the homogeneous piece of cohomological degree `-k`. -/
def exteriorPowerToCohomologicalGrade (k : ℕ) :
    exteriorGrade R E k ≃ₗ[R] cohomologicalExteriorGrade R E (-(k : ℤ)) :=
  LinearEquiv.ofEq _ _ (cohomologicalExteriorGrade_neg_natCast R E k).symm

/-- The identification of the `k`-th exterior power with the piece of degree `-k` is the identity
on underlying elements. -/
@[simp]
theorem coe_exteriorPowerToCohomologicalGrade (k : ℕ) (x : exteriorGrade R E k) :
    (exteriorPowerToCohomologicalGrade R E k x : ExteriorAlgebra R E) = x := rfl

/-- The reindexing `k ↦ -k` of a direct sum of exterior powers as a direct sum of
cohomological pieces. -/
def toCohomologicalDirectSum :
    (⨁ k : ℕ, exteriorGrade R E k) →+ ⨁ n : ℤ, cohomologicalExteriorGrade R E n :=
  DirectSum.toAddMonoid fun k =>
    (DirectSum.of _ (-(k : ℤ))).comp
      (exteriorPowerToCohomologicalGrade R E k).toLinearMap.toAddMonoidHom

/-- On the summand of index `k`, `Koszul.toCohomologicalDirectSum` is the inclusion of the summand
of index `-k`. -/
@[simp]
theorem toCohomologicalDirectSum_of (k : ℕ) (x : exteriorGrade R E k) :
    toCohomologicalDirectSum R E (DirectSum.of _ k x) =
      DirectSum.of _ (-(k : ℤ)) (exteriorPowerToCohomologicalGrade R E k x) :=
  DirectSum.toAddMonoid_of _ _ _

/-- Reindexing a direct sum of exterior powers by `k ↦ -k` does not change the sum of its
components in the exterior algebra. -/
theorem coe_toCohomologicalDirectSum (x : ⨁ k : ℕ, exteriorGrade R E k) :
    DirectSum.coeAddMonoidHom (cohomologicalExteriorGrade R E)
        (toCohomologicalDirectSum R E x) =
      DirectSum.coeAddMonoidHom (exteriorGrade R E) x := by
  have h : (DirectSum.coeAddMonoidHom (cohomologicalExteriorGrade R E)).comp
      (toCohomologicalDirectSum R E) = DirectSum.coeAddMonoidHom (exteriorGrade R E) :=
    DirectSum.addHom_ext fun k y => by simp
  exact DFunLike.congr_fun h x

/-- The decomposition of the exterior algebra into its cohomological pieces: decompose into
exterior powers, then reindex by `k ↦ -k`. -/
noncomputable def cohomologicalDecompose :
    ExteriorAlgebra R E →+ ⨁ n : ℤ, cohomologicalExteriorGrade R E n :=
  (toCohomologicalDirectSum R E).comp
    (DirectSum.decomposeAddEquiv (exteriorGrade R E)).toAddMonoidHom

/-- `Koszul.cohomologicalDecompose` is the decomposition into exterior powers followed by the
reindexing `k ↦ -k`. -/
theorem cohomologicalDecompose_apply (a : ExteriorAlgebra R E) :
    cohomologicalDecompose R E a =
      toCohomologicalDirectSum R E (DirectSum.decompose (exteriorGrade R E) a) :=
  rfl

/-- Summing the cohomological components of an element of the exterior algebra recovers it. -/
theorem coe_cohomologicalDecompose (a : ExteriorAlgebra R E) :
    DirectSum.coeAddMonoidHom (cohomologicalExteriorGrade R E)
        (cohomologicalDecompose R E a) = a := by
  rw [cohomologicalDecompose_apply, coe_toCohomologicalDirectSum]
  exact (DirectSum.decompose (exteriorGrade R E)).symm_apply_apply a

/-- Decomposing the sum of a family of cohomological components recovers the family. -/
theorem cohomologicalDecompose_coe (y : ⨁ n : ℤ, cohomologicalExteriorGrade R E n) :
    cohomologicalDecompose R E
        (DirectSum.coeAddMonoidHom (cohomologicalExteriorGrade R E) y) = y := by
  have h : (cohomologicalDecompose R E).comp
      (DirectSum.coeAddMonoidHom (cohomologicalExteriorGrade R E)) = AddMonoidHom.id _ := by
    refine DirectSum.addHom_ext fun n x => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply]
    rcases exists_or_eq_zero_of_mem_cohomologicalExteriorGrade R E x.2 with
      ⟨k, rfl, hx⟩ | h0
    · have hdec : DirectSum.decompose (exteriorGrade R E) (x : ExteriorAlgebra R E) =
          DirectSum.of _ k (⟨(x : ExteriorAlgebra R E), hx⟩ : exteriorGrade R E k) :=
        DirectSum.decompose_coe (exteriorGrade R E)
          (⟨(x : ExteriorAlgebra R E), hx⟩ : exteriorGrade R E k)
      rw [cohomologicalDecompose_apply, hdec, toCohomologicalDirectSum_of]
      exact congrArg (fun z => DirectSum.of _ (-(k : ℤ)) z) (Subtype.ext rfl)
    · obtain rfl : x = 0 := Subtype.ext h0
      simp
  exact DFunLike.congr_fun h y

/-- The exterior algebra is the direct sum of its cohomological pieces. -/
noncomputable instance cohomologicalExteriorGrade.decomposition :
    DirectSum.Decomposition (cohomologicalExteriorGrade R E) where
  decompose' := cohomologicalDecompose R E
  left_inv := coe_cohomologicalDecompose R E
  right_inv := cohomologicalDecompose_coe R E

/-- The exterior algebra, graded cohomologically by `ℤ`, is a graded algebra. -/
noncomputable instance cohomologicalExteriorGrade.gradedAlgebra :
    GradedAlgebra (cohomologicalExteriorGrade R E) :=
  { cohomologicalExteriorGrade.gradedMonoid R E,
    cohomologicalExteriorGrade.decomposition R E with }

end Grading

section Differential

variable (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]

/-- Contraction by a functional raises the cohomological degree by one. -/
theorem contraction_mem_cohomologicalExteriorGrade (φ : Module.Dual R E) {n : ℤ}
    {x : ExteriorAlgebra R E} (hx : x ∈ cohomologicalExteriorGrade R E n) :
    contraction φ x ∈ cohomologicalExteriorGrade R E (n + 1) := by
  rcases exists_or_eq_zero_of_mem_cohomologicalExteriorGrade R E hx with ⟨k, rfl, hx⟩ | rfl
  · cases k with
    | zero =>
      rw [show -((0 : ℕ) : ℤ) + 1 = 1 by norm_num,
        cohomologicalExteriorGrade_of_pos R E (by omega),
        Stacks.MappingCone.NatIndexed.contraction_eq_zero_of_mem_exteriorPower_zero φ hx]
      exact Submodule.zero_mem _
    | succ j =>
      rw [show -((j + 1 : ℕ) : ℤ) + 1 = -(j : ℤ) by push_cast; ring,
        cohomologicalExteriorGrade_neg_natCast]
      exact contraction_mem φ j hx
  · simp

/-- The signed Leibniz rule for contraction, read in the cohomological grading. The sign is
unchanged by the regrading, since `(-1) ^ (-k) = (-1) ^ k`. -/
theorem contraction_mul_of_mem_cohomologicalExteriorGrade (φ : Module.Dual R E) {n : ℤ}
    {a : ExteriorAlgebra R E} (ha : a ∈ cohomologicalExteriorGrade R E n)
    (b : ExteriorAlgebra R E) :
    contraction φ (a * b) =
      contraction φ a * b + (n.negOnePow : ℤ) • (a * contraction φ b) := by
  rcases exists_or_eq_zero_of_mem_cohomologicalExteriorGrade R E ha with ⟨k, rfl, hk⟩ | rfl
  · have hcast : (((-1 : ℤ) ^ k : ℤ) : R) = (-1 : R) ^ k := by push_cast; ring
    rw [contraction, DividedPowers.TateResolution.contractLeft_mul_of_mem φ k hk b,
      Int.negOnePow_neg, Int.coe_negOnePow_natCast, ← Int.cast_smul_eq_zsmul R, hcast]
  · simp

/-- The Koszul differential graded algebra of a functional `φ : E →ₗ[R] R`, as an object of
`DifferentialGradedAlgebra R`: the exterior algebra `⋀[R] E`, with the `k`-th exterior power in
cohomological degree `-k` and with contraction by `φ` as differential. -/
@[ega "III 1.1.1" "more general"]
noncomputable def cohomologicalDifferentialGradedAlgebra (φ : Module.Dual R E) :
    DifferentialGradedAlgebra.{u, max u v} R where
  A := ExteriorAlgebra R E
  grading := cohomologicalExteriorGrade R E
  d := contraction φ
  d_comp_d := LinearMap.ext fun x => CliffordAlgebra.contractLeft_contractLeft φ x
  d_mem := fun _ _ hx => contraction_mem_cohomologicalExteriorGrade R E φ hx
  leibniz := fun _ _ _ b ha _ =>
    contraction_mul_of_mem_cohomologicalExteriorGrade R E φ ha b

/-- The underlying algebra of the Koszul differential graded algebra is the exterior algebra. -/
theorem cohomologicalDifferentialGradedAlgebra_A (φ : Module.Dual R E) :
    (cohomologicalDifferentialGradedAlgebra R E φ).A = ExteriorAlgebra R E := rfl

/-- The grading of the Koszul differential graded algebra is the cohomological exterior grading. -/
@[simp]
theorem cohomologicalDifferentialGradedAlgebra_grading (φ : Module.Dual R E) :
    (cohomologicalDifferentialGradedAlgebra R E φ).grading =
      cohomologicalExteriorGrade R E := rfl

/-- The differential of the Koszul differential graded algebra of `φ` is contraction by `φ`. -/
@[simp]
theorem cohomologicalDifferentialGradedAlgebra_d (φ : Module.Dual R E) :
    (cohomologicalDifferentialGradedAlgebra R E φ).d = contraction φ := rfl

end Differential

section Functoriality

variable (R : Type u) [CommRing R] (E F : Type v) [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

/-- The algebra map induced by a linear map preserves the cohomological grading. -/
theorem map_mem_cohomologicalExteriorGrade (l : E →ₗ[R] F) {n : ℤ}
    {x : ExteriorAlgebra R E} (hx : x ∈ cohomologicalExteriorGrade R E n) :
    ExteriorAlgebra.map l x ∈ cohomologicalExteriorGrade R F n := by
  rcases exists_or_eq_zero_of_mem_cohomologicalExteriorGrade R E hx with ⟨k, rfl, hk⟩ | rfl
  · rw [cohomologicalExteriorGrade_neg_natCast]
    exact ExteriorAlgebra.map_mem_exteriorPower l hk
  · simp

/-- A linear map `l : E → F` induces a homomorphism of differential graded algebras from the
Koszul algebra of `ψ ∘ l` to the Koszul algebra of `ψ`. -/
noncomputable def cohomologicalDifferentialGradedAlgebraHom (l : E →ₗ[R] F)
    (ψ : Module.Dual R F) :
    (cohomologicalDifferentialGradedAlgebra R E (ψ ∘ₗ l)).Hom
      (cohomologicalDifferentialGradedAlgebra R F ψ) where
  toAlgebraHom := ExteriorAlgebra.map l
  map_grading := fun _ _ ha => map_mem_cohomologicalExteriorGrade R E F l ha
  map_d := fun a =>
    (DividedPowers.TateResolution.contractLeft_exteriorAlgebraMap l ψ a).symm

end Functoriality

section Sequence

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The differential graded Koszul algebra `K_n = R⟨ξ₁, …, ξ_r⟩` of a sequence `f₁, …, f_r` in
`R`: the exterior algebra on `r` generators `ξᵢ` of cohomological degree `-1`, with differential
determined by `d ξᵢ = fᵢ ^ n`. -/
noncomputable def powAlgebra (f : Fin r → R) (n : ℕ) : DifferentialGradedAlgebra.{u, u} R :=
  cohomologicalDifferentialGradedAlgebra R (Fin r → R) (seqDual fun i => f i ^ n)

/-- The underlying algebra of `K_n` is the exterior algebra of `Rʳ`. -/
theorem powAlgebra_A (f : Fin r → R) (n : ℕ) :
    (powAlgebra f n).A = ExteriorAlgebra R (Fin r → R) := rfl

/-- The grading of `K_n` is the cohomological exterior grading of `Rʳ`. -/
theorem powAlgebra_grading (f : Fin r → R) (n : ℕ) :
    (powAlgebra f n).grading = cohomologicalExteriorGrade R (Fin r → R) := rfl

/-- The piece of `K_n` in cohomological degree `-k` is the `k`-th exterior power of `Rʳ`. -/
theorem powAlgebra_grading_neg_natCast (f : Fin r → R) (n k : ℕ) :
    (powAlgebra f n).grading (-(k : ℤ)) = ⋀[R]^k (Fin r → R) :=
  cohomologicalExteriorGrade_neg_natCast R (Fin r → R) k

/-- The algebra `K_n` vanishes in positive cohomological degrees. -/
theorem powAlgebra_grading_of_pos (f : Fin r → R) (n : ℕ) {m : ℤ} (hm : 0 < m) :
    (powAlgebra f n).grading m = ⊥ :=
  cohomologicalExteriorGrade_of_pos R (Fin r → R) hm

/-- The differential of `K_n` is contraction by the functional `ξᵢ ↦ fᵢ ^ n`. -/
theorem powAlgebra_d (f : Fin r → R) (n : ℕ) :
    (powAlgebra f n).d = contraction (seqDual fun i => f i ^ n) := rfl

/-- The generators of `K_n` lie in cohomological degree `-1`. -/
theorem ι_mem_powAlgebra_grading (f : Fin r → R) (n : ℕ) (x : Fin r → R) :
    ExteriorAlgebra.ι R x ∈ (powAlgebra f n).grading (-1) := by
  have h := powAlgebra_grading_neg_natCast f n 1
  rw [show -((1 : ℕ) : ℤ) = -1 by norm_num] at h
  rw [h]
  exact ι_mem_one x

/-- The differential of `K_n` sends the generator `ξᵢ` to `fᵢ ^ n`. -/
theorem powAlgebra_d_ι (f : Fin r → R) (n : ℕ) (i : Fin r) :
    (powAlgebra f n).d (ExteriorAlgebra.ι R (Pi.single i 1)) =
      algebraMap R (ExteriorAlgebra R (Fin r → R)) (f i ^ n) := by
  have h : contraction (seqDual fun j => f j ^ n) (ExteriorAlgebra.ι R (Pi.single i 1)) =
      algebraMap R (ExteriorAlgebra R (Fin r → R))
        ((seqDual fun j => f j ^ n) (Pi.single i 1)) :=
    CliffordAlgebra.contractLeft_ι (0 : QuadraticForm R (Fin r → R)) _ _
  simp only [seqDual_single] at h
  exact h

/-- Scaling the `i`-th coordinate of `Rʳ` by `cᵢ` sends the `i`-th basis vector to `cᵢ` times
itself. -/
theorem mulLeft_single (c : Fin r → R) (i : Fin r) :
    LinearMap.mulLeft R c (Pi.single i 1) = Pi.single i (c i) := by
  funext j
  simp only [LinearMap.mulLeft_apply, Pi.mul_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- The transition homomorphism `K_m → K_n` for `1 ≤ n ≤ m`: the homomorphism of differential
graded algebras induced by scaling the `i`-th coordinate of `Rʳ` by `fᵢ ^ (m - n)`. -/
noncomputable def powTransition (f : Fin r → R) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    (powAlgebra f m).Hom (powAlgebra f n) where
  toAlgebraHom := ExteriorAlgebra.map (LinearMap.mulLeft R fun i => f i ^ (m - n))
  map_grading := fun _ _ ha =>
    map_mem_cohomologicalExteriorGrade R (Fin r → R) (Fin r → R) _ ha
  map_d := by
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = p + 1 := ⟨n - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q + 1 := ⟨m - 1, by omega⟩
    rw [show q + 1 - (p + 1) = q - p from by omega]
    exact fun a =>
      (DividedPowers.TateResolution.contraction_map_mulLeft f (by omega) a).symm

/-- The transition homomorphism `K_m → K_n` is the algebra map induced by scaling the `i`-th
coordinate of `Rʳ` by `fᵢ ^ (m - n)`. -/
theorem powTransition_apply (f : Fin r → R) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m)
    (x : ExteriorAlgebra R (Fin r → R)) :
    (powTransition f hn hnm).toAlgebraHom x =
      ExteriorAlgebra.map (LinearMap.mulLeft R fun i => f i ^ (m - n)) x := rfl

/-- The transition homomorphism `K_m → K_n` scales the generator `ξᵢ` by `fᵢ ^ (m - n)`. -/
theorem powTransition_apply_ι (f : Fin r → R) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (i : Fin r) :
    (powTransition f hn hnm).toAlgebraHom (ExteriorAlgebra.ι R (Pi.single i 1)) =
      ExteriorAlgebra.ι R (Pi.single i (f i ^ (m - n))) := by
  rw [powTransition_apply, ExteriorAlgebra.map_apply_ι, mulLeft_single]

/-- Scaling by `fᵢ ^ (m - n)` and then by `fᵢ ^ (n - p)` is scaling by `fᵢ ^ (m - p)`. -/
theorem mulLeft_comp_mulLeft_pow (f : Fin r → R) {p n m : ℕ} (hpn : p ≤ n) (hnm : n ≤ m) :
    (LinearMap.mulLeft R fun i => f i ^ (n - p)).comp
        (LinearMap.mulLeft R fun i => f i ^ (m - n)) =
      LinearMap.mulLeft R fun i => f i ^ (m - p) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Pi.mul_apply]
  rw [← mul_assoc, ← pow_add, show n - p + (m - n) = m - p from by omega]

/-- The transition homomorphisms compose, elementwise. -/
theorem powTransition_comp_apply (f : Fin r → R) {p n m : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n)
    (hnm : n ≤ m) (x : ExteriorAlgebra R (Fin r → R)) :
    (powTransition f hp hpn).toAlgebraHom
        ((powTransition f (hp.trans hpn) hnm).toAlgebraHom x) =
      (powTransition f hp (hpn.trans hnm)).toAlgebraHom x := by
  rw [powTransition_apply, powTransition_apply, powTransition_apply, ← AlgHom.comp_apply,
    ExteriorAlgebra.map_comp_map, mulLeft_comp_mulLeft_pow f hpn hnm]

/-- The transition homomorphisms compose: `K_m → K_n` followed by `K_n → K_p` is the
transition homomorphism `K_m → K_p`, so the `K_n` form an inverse system. -/
theorem powTransition_comp (f : Fin r → R) {p n m : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n)
    (hnm : n ≤ m) :
    (powTransition f hp hpn).toAlgebraHom.comp
        (powTransition f (hp.trans hpn) hnm).toAlgebraHom =
      (powTransition f hp (hpn.trans hnm)).toAlgebraHom :=
  AlgHom.ext fun x => powTransition_comp_apply f hp hpn hnm x

/-- The ideal generated by the `n`-th powers of the sequence. -/
def powIdeal (f : Fin r → R) (n : ℕ) : Ideal R := Ideal.span (Set.range fun i => f i ^ n)

/-- The ideals generated by the powers of the sequence decrease. -/
theorem powIdeal_le (f : Fin r → R) {n m : ℕ} (h : n ≤ m) : powIdeal f m ≤ powIdeal f n := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  have hp : f i ^ m = f i ^ n * f i ^ (m - n) := by
    rw [← pow_add]
    congr 1
    omega
  show f i ^ m ∈ powIdeal f n
  rw [hp]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The transition homomorphism from `K_n` to itself is the identity: it scales `ξᵢ` by
`fᵢ ^ 0 = 1`. -/
theorem powTransition_self_toAlgebraHom (f : Fin r → R) {n : ℕ} (hn : 1 ≤ n) :
    (powTransition f hn (le_refl n)).toAlgebraHom
      = AlgHom.id R (ExteriorAlgebra R (Fin r → R)) := by
  have h : (LinearMap.mulLeft R fun i => f i ^ (n - n)) = LinearMap.id := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp
  refine AlgHom.ext fun x => ?_
  show ExteriorAlgebra.map (LinearMap.mulLeft R fun i => f i ^ (n - n)) x = x
  rw [h, ExteriorAlgebra.map_id]
  rfl

end Sequence

end Koszul

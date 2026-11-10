module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TorComparison
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TransportDividedPowers

/-!
# The divided power algebra structure on graded Tor

Let `R` be a commutative ring and let `S` and `T` be commutative `R`-algebras. The homology of
the base change `T ⊗[R] A` of a Tate resolution `A` of `S` carries a strictly graded-commutative
graded `R`-algebra structure with divided powers, and
`DividedPowers.TateResolution.torDirectSumEquivHomology` identifies `⨁ n, Tor_n^R(S, T)` with
that homology, degreewise. This file transports the structure along that identification, so that
the direct sum of the `Tor_n^R(S, T)` itself becomes a strictly graded-commutative graded
`R`-algebra with divided powers, which is the assertion of Tag 09PQ.

## Main definitions

* `DividedPowers.TateResolution.directSumClass` — the class map `cycles dB → ⨁ n, M n` obtained
  from an identification of the direct sum with the homology.
* `DividedPowers.TateResolution.rangeLofDecomposition` — the canonical decomposition of a direct
  sum into the ranges of its inclusions.
* `DividedPowers.TateResolution.directSumRing` and
  `DividedPowers.TateResolution.directSumAlgebra` — the ring and `R`-algebra structures on the
  direct sum, with the direct sum's own addition and scalar multiplication.
* `DividedPowers.TateResolution.cycleSubalgebra` and
  `DividedPowers.TateResolution.cycleAlgHom` — the cycles as an `R`-subalgebra and the class map
  as a map of `R`-algebras.
* `DividedPowers.TateResolution.rangeLofGradedAlgebra` — the transported grading, as a graded
  algebra structure.
* `DividedPowers.TateResolution.directSumDividedPowerStructure` — the transported divided power
  structure.

## Main results

* `DividedPowers.TateResolution.directSumRing_toAddCommGroup` and
  `DividedPowers.TateResolution.directSumAlgebra_toSMul` — the transported ring and algebra
  structures reproduce the direct sum's own additive and scalar structure.
* `DividedPowers.TateResolution.rangeLofIsStrictlyGradedComm` — the transported grading is
  strictly graded commutative.
* `DividedPowers.TateResolution.directSumDividedPowerStructure_dpow` — the transported divided
  powers, on the class of a positive even cycle.
* `DividedPowers.TateResolution.exists_dividedPowerStructure_directSum` — the induced divided
  power structure of Tag 09PK, transported to a direct sum identified degreewise with the
  homology.
* `DividedPowers.TateResolution.exists_dividedPowerStructure_torDirectSum` — Tag 09PQ: the
  divided power algebra structure on `⨁ n, Tor_n^R(S, T)`.

## Implementation notes

The predicate `DividedPowers.TateResolution.HasInducedDividedPowers` quantifies the ring, the
algebra, the grading and the divided powers on the homology existentially. Its recorded clauses
for the unit and for products determine the multiplication of the homology on the classes of
cycles, and its recorded clause for the divided powers determines them on the classes of positive
even cycles; the clauses for zero, addition and scalar multiplication hold for the quotient's
canonical module structure and are therefore not constraints on the existential witnesses. For
that reason nothing here is read off the witnesses' additive structure: everything is built on
the direct sum's own additive and scalar structure, and the only data taken from the homology are
the functions giving the multiplication, the unit and the divided powers, together with the
equations expressing them on classes of cycles. Each structure is then assembled by choosing a
cycle representing a given class, which is possible because the class map is surjective.

## References

* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open TensorProduct

universe u v w

section RangeLof

variable {R : Type u} {M : ℕ → Type v} [CommRing R] [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)]

/-- **A direct sum is decomposed by the ranges of its inclusions.** This is the grading onto
which a grading of an isomorphic module is transported. -/
@[instance_reducible]
public def rangeLofDecomposition :
    DirectSum.Decomposition fun n => LinearMap.range (DirectSum.lof R ℕ M n) := by
  classical
  refine DirectSum.Decomposition.ofLinearMap _
    (DirectSum.toModule R ℕ _ fun n =>
      (DirectSum.lof R ℕ (fun m => ↥(LinearMap.range (DirectSum.lof R ℕ M m))) n).comp
        (DirectSum.lof R ℕ M n).rangeRestrict) ?_ ?_
  · refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => ?_
    simp [DirectSum.toModule_lof]
  · refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => ?_
    obtain ⟨y, hy⟩ := x.2
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
    rw [← hy]
    simp only [DirectSum.toModule_lof]
    exact congrArg (DirectSum.lof R ℕ (fun m => ↥(LinearMap.range (DirectSum.lof R ℕ M m))) n)
      (Subtype.ext hy)

end RangeLof

section ClassMap

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} [IsDifferentialGradedAlgebra ℬ dB]

/-- The class map of an identification of a direct sum with the homology of a differential graded
algebra: a cycle is sent to the element of the direct sum corresponding to its homology class. -/
public def directSumClass (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB) :
    cycles dB →ₗ[R] DirectSum ℕ M :=
  (e.symm : Homology (𝒜 := ℬ) dB →ₗ[R] DirectSum ℕ M).comp
    (boundaries (𝒜 := ℬ) dB).mkQ

/-- The class map sends a cycle to the preimage under the identification of its homology class. -/
@[simp]
public theorem directSumClass_apply (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
    (x : cycles dB) :
    directSumClass e x = e.symm (Submodule.Quotient.mk x) := rfl

/-- The class map is surjective: the quotient map onto the homology is, and the identification
is bijective. -/
public theorem surjective_directSumClass
    (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB) :
    Function.Surjective (directSumClass e) :=
  e.symm.surjective.comp (Submodule.mkQ_surjective _)

/-- Every element of the direct sum is the class of a cycle. -/
public theorem exists_cycle_directSumClass_eq
    (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB) (z : DirectSum ℕ M) :
    ∃ (x : B) (h : dB x = 0), directSumClass e ⟨x, h⟩ = z := by
  obtain ⟨y, hy⟩ := surjective_directSumClass e z
  exact ⟨(y : B), y.property, hy⟩

/-- The class map takes the sum of two cycles to the sum of their classes. -/
public theorem directSumClass_add (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
    (x y : B) (hx : dB x = 0) (hy : dB y = 0) (hxy : dB (x + y) = 0) :
    directSumClass e ⟨x + y, hxy⟩ =
      directSumClass e ⟨x, hx⟩ + directSumClass e ⟨y, hy⟩ :=
  map_add (directSumClass e) ⟨x, hx⟩ ⟨y, hy⟩

/-- The class map takes a scalar multiple of a cycle to the scalar multiple of its class. -/
public theorem directSumClass_smul (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
    (r : R) (x : B) (hx : dB x = 0) (hrx : dB (r • x) = 0) :
    directSumClass e ⟨r • x, hrx⟩ = r • directSumClass e ⟨x, hx⟩ :=
  map_smul (directSumClass e) r ⟨x, hx⟩

/-- The class of the zero cycle is zero. -/
public theorem directSumClass_zero (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
    (h0 : dB (0 : B) = 0) : directSumClass e ⟨0, h0⟩ = 0 :=
  map_zero (directSumClass e)

end ClassMap

section RingStructure

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} [IsDifferentialGradedAlgebra ℬ dB]
  (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
  (mulD : DirectSum ℕ M → DirectSum ℕ M → DirectSum ℕ M) (oneD : DirectSum ℕ M)
  (hcyc : ∀ x y : B, dB x = 0 → dB y = 0 → dB (x * y) = 0)
  (hmulD : ∀ (x y : B) (hx : dB x = 0) (hy : dB y = 0),
    mulD (directSumClass e ⟨x, hx⟩) (directSumClass e ⟨y, hy⟩) =
      directSumClass e ⟨x * y, hcyc x y hx hy⟩)

include hmulD

/-- The transported multiplication is associative. -/
public theorem directSum_mul_assoc (a b c : DirectSum ℕ M) :
    mulD (mulD a b) c = mulD a (mulD b c) := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  obtain ⟨y, hy, rfl⟩ := exists_cycle_directSumClass_eq e b
  obtain ⟨w, hw, rfl⟩ := exists_cycle_directSumClass_eq e c
  rw [hmulD x y hx hy, hmulD (x * y) w _ hw, hmulD y w hy hw, hmulD x (y * w) hx _]
  exact congrArg (directSumClass e) (Subtype.ext (mul_assoc x y w))

/-- The transported multiplication is additive in its second argument. -/
public theorem directSum_mul_add (a b c : DirectSum ℕ M) :
    mulD a (b + c) = mulD a b + mulD a c := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  obtain ⟨y, hy, rfl⟩ := exists_cycle_directSumClass_eq e b
  obtain ⟨w, hw, rfl⟩ := exists_cycle_directSumClass_eq e c
  have hyw : dB (y + w) = 0 := by simp [hy, hw]
  rw [← directSumClass_add e y w hy hw hyw, hmulD x (y + w) hx hyw,
    hmulD x y hx hy, hmulD x w hx hw,
    ← directSumClass_add e (x * y) (x * w) _ _
      (by simp [hcyc x y hx hy, hcyc x w hx hw])]
  exact congrArg (directSumClass e) (Subtype.ext (mul_add x y w))

/-- The transported multiplication is additive in its first argument. -/
public theorem directSum_add_mul (a b c : DirectSum ℕ M) :
    mulD (a + b) c = mulD a c + mulD b c := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  obtain ⟨y, hy, rfl⟩ := exists_cycle_directSumClass_eq e b
  obtain ⟨w, hw, rfl⟩ := exists_cycle_directSumClass_eq e c
  have hxy : dB (x + y) = 0 := by simp [hx, hy]
  rw [← directSumClass_add e x y hx hy hxy, hmulD (x + y) w hxy hw,
    hmulD x w hx hw, hmulD y w hy hw,
    ← directSumClass_add e (x * w) (y * w) _ _
      (by simp [hcyc x w hx hw, hcyc y w hy hw])]
  exact congrArg (directSumClass e) (Subtype.ext (add_mul x y w))

/-- The transported multiplication kills zero on the left. -/
public theorem directSum_zero_mul (a : DirectSum ℕ M) : mulD 0 a = 0 := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  have h0 : dB (0 : B) = 0 := by simp
  have key := hmulD 0 x h0 hx
  rw [directSumClass_zero e h0] at key
  refine key.trans ?_
  rw [congrArg (directSumClass e) (Subtype.ext (zero_mul x) :
      (⟨(0 : B) * x, hcyc 0 x h0 hx⟩ : cycles dB) = ⟨0, h0⟩),
    directSumClass_zero e h0]

/-- The transported multiplication kills zero on the right. -/
public theorem directSum_mul_zero (a : DirectSum ℕ M) : mulD a 0 = 0 := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  have h0 : dB (0 : B) = 0 := by simp
  have key := hmulD x 0 hx h0
  rw [directSumClass_zero e h0] at key
  refine key.trans ?_
  rw [congrArg (directSumClass e) (Subtype.ext (mul_zero x) :
      (⟨x * (0 : B), hcyc x 0 hx h0⟩ : cycles dB) = ⟨0, h0⟩),
    directSumClass_zero e h0]

/-- The transported multiplication commutes with scalars in its first argument. -/
public theorem directSum_smul_mul (r : R) (a b : DirectSum ℕ M) :
    mulD (r • a) b = r • mulD a b := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  obtain ⟨y, hy, rfl⟩ := exists_cycle_directSumClass_eq e b
  have hrx : dB (r • x) = 0 := by simp [hx]
  rw [← directSumClass_smul e r x hx hrx, hmulD (r • x) y hrx hy, hmulD x y hx hy,
    ← directSumClass_smul e r (x * y) _ (by simp [hcyc x y hx hy])]
  exact congrArg (directSumClass e) (Subtype.ext (Algebra.smul_mul_assoc r x y))

/-- The transported multiplication commutes with scalars in its second argument. -/
public theorem directSum_mul_smul (r : R) (a b : DirectSum ℕ M) :
    mulD a (r • b) = r • mulD a b := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  obtain ⟨y, hy, rfl⟩ := exists_cycle_directSumClass_eq e b
  have hry : dB (r • y) = 0 := by simp [hy]
  rw [← directSumClass_smul e r y hy hry, hmulD x (r • y) hx hry, hmulD x y hx hy,
    ← directSumClass_smul e r (x * y) _ (by simp [hcyc x y hx hy])]
  exact congrArg (directSumClass e) (Subtype.ext (Algebra.mul_smul_comm r x y))

variable (h1 : dB (1 : B) = 0) (h1D : oneD = directSumClass e ⟨1, h1⟩)

include h1D

/-- The transported unit is a left unit. -/
public theorem directSum_one_mul (a : DirectSum ℕ M) : mulD oneD a = a := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  rw [h1D, hmulD 1 x h1 hx]
  exact congrArg (directSumClass e) (Subtype.ext (one_mul x))

/-- The transported unit is a right unit. -/
public theorem directSum_mul_one (a : DirectSum ℕ M) : mulD a oneD = a := by
  obtain ⟨x, hx, rfl⟩ := exists_cycle_directSumClass_eq e a
  rw [h1D, hmulD x 1 hx h1]
  exact congrArg (directSumClass e) (Subtype.ext (mul_one x))

/-- **The transported ring structure on a direct sum.** Given a multiplication and a unit on the
direct sum which, on the classes of cycles, are the multiplication and the unit of the algebra of
cycles, the direct sum is a ring for its own addition. -/
@[instance_reducible]
public def directSumRing : Ring (DirectSum ℕ M) :=
  { (inferInstance : AddCommGroup (DirectSum ℕ M)) with
    mul := mulD
    one := oneD
    mul_assoc := directSum_mul_assoc e mulD hcyc hmulD
    one_mul := directSum_one_mul e mulD oneD hcyc hmulD h1 h1D
    mul_one := directSum_mul_one e mulD oneD hcyc hmulD h1 h1D
    left_distrib := directSum_mul_add e mulD hcyc hmulD
    right_distrib := directSum_add_mul e mulD hcyc hmulD
    zero_mul := directSum_zero_mul e mulD hcyc hmulD
    mul_zero := directSum_mul_zero e mulD hcyc hmulD }

/-- The transported ring structure has the direct sum's own additive structure. -/
public theorem directSumRing_toAddCommGroup :
    (directSumRing e mulD oneD hcyc hmulD h1 h1D).toAddCommGroup =
      (inferInstance : AddCommGroup (DirectSum ℕ M)) :=
  rfl

/-- The transported multiplication is the given one. -/
public theorem directSumRing_mul (a b : DirectSum ℕ M) :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    a * b = mulD a b :=
  rfl

/-- The transported unit is the given one. -/
public theorem directSumRing_one :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    (1 : DirectSum ℕ M) = oneD :=
  rfl

/-- **The transported `R`-algebra structure on a direct sum**, with the direct sum's own scalar
multiplication. -/
@[instance_reducible]
public def directSumAlgebra :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    Algebra R (DirectSum ℕ M) :=
  letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
  Algebra.ofModule (directSum_smul_mul e mulD hcyc hmulD)
    (directSum_mul_smul e mulD hcyc hmulD)

/-- The transported algebra structure has the direct sum's own scalar multiplication. -/
public theorem directSumAlgebra_toSMul :
    @Algebra.toSMul R (DirectSum ℕ M) _
        (directSumRing e mulD oneD hcyc hmulD h1 h1D).toSemiring
        (directSumAlgebra e mulD oneD hcyc hmulD h1 h1D) =
      (inferInstance : SMul R (DirectSum ℕ M)) :=
  rfl

end RingStructure

section Grading

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} [IsDifferentialGradedAlgebra ℬ dB]
  (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
  (he : ∀ n, Submodule.map (e : DirectSum ℕ M →ₗ[R] Homology (𝒜 := ℬ) dB)
    (LinearMap.range (DirectSum.lof R ℕ M n)) = totalHomologyGrade ℬ dB n)

include he

/-- A class lies in the range of the `n`-th inclusion exactly when the corresponding homology
class lies in the degree-`n` graded piece of the homology. -/
public theorem directSumClass_mem_range_lof_iff (n : ℕ) (x : cycles dB) :
    directSumClass e x ∈ LinearMap.range (DirectSum.lof R ℕ M n) ↔
      (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) dB) ∈ totalHomologyGrade ℬ dB n := by
  rw [← he n, Submodule.mem_map_equiv]
  rfl

/-- The class of a cycle of degree `n` lies in the range of the `n`-th inclusion. -/
public theorem directSumClass_mem_range_lof (n : ℕ) (x : B) (h : dB x = 0) (hx : x ∈ ℬ n) :
    directSumClass e ⟨x, h⟩ ∈ LinearMap.range (DirectSum.lof R ℕ M n) := by
  rw [directSumClass_mem_range_lof_iff e he]
  exact Submodule.subset_span ⟨⟨x, h⟩, hx, rfl⟩

/-- Every element of the range of the `n`-th inclusion is the class of a cycle of degree `n`. -/
public theorem exists_homogeneous_cycle_directSumClass_eq (n : ℕ) {z : DirectSum ℕ M}
    (hz : z ∈ LinearMap.range (DirectSum.lof R ℕ M n)) :
    ∃ (x : B) (h : dB x = 0), x ∈ ℬ n ∧ directSumClass e ⟨x, h⟩ = z := by
  obtain ⟨y, hy, rfl⟩ := exists_cycle_directSumClass_eq e z
  rw [directSumClass_mem_range_lof_iff e he, totalHomologyGrade_eq_range] at hz
  obtain ⟨w, hw⟩ := hz
  refine ⟨((w : ↥(ℬ n)) : B), (w : ↥(gradeCycles ℬ dB n)).2, (w : ↥(ℬ n)).2, ?_⟩
  have : (Submodule.Quotient.mk (⟨((w : ↥(ℬ n)) : B), (w : ↥(gradeCycles ℬ dB n)).2⟩ :
      cycles dB) : Homology (𝒜 := ℬ) dB) = Submodule.Quotient.mk (⟨y, hy⟩ : cycles dB) := hw
  simpa using congrArg (fun t => e.symm t) this

end Grading

section GradedStructure

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  {dB : B →ₗ[R] B} [IsDifferentialGradedAlgebra ℬ dB]
  (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
  (mulD : DirectSum ℕ M → DirectSum ℕ M → DirectSum ℕ M) (oneD : DirectSum ℕ M)
  (hcyc : ∀ x y : B, dB x = 0 → dB y = 0 → dB (x * y) = 0)
  (hmulD : ∀ (x y : B) (hx : dB x = 0) (hy : dB y = 0),
    mulD (directSumClass e ⟨x, hx⟩) (directSumClass e ⟨y, hy⟩) =
      directSumClass e ⟨x * y, hcyc x y hx hy⟩)
  (h1 : dB (1 : B) = 0) (h1D : oneD = directSumClass e ⟨1, h1⟩)
  (he : ∀ n, Submodule.map (e : DirectSum ℕ M →ₗ[R] Homology (𝒜 := ℬ) dB)
    (LinearMap.range (DirectSum.lof R ℕ M n)) = totalHomologyGrade ℬ dB n)

include hcyc hmulD h1 h1D he

/-- **The transported grading is a graded algebra structure.** The degree-`n` piece is the range
of the `n`-th inclusion of the direct sum, whose decomposition is the direct sum's own; the unit
and products are homogeneous because they are so on the classes of homogeneous cycles. -/
@[instance_reducible]
public def rangeLofGradedAlgebra :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
    GradedAlgebra fun n => LinearMap.range (DirectSum.lof R ℕ M n) :=
  letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
  letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
  { rangeLofDecomposition with
    one_mem := by
      change oneD ∈ LinearMap.range (DirectSum.lof R ℕ M 0)
      have key : directSumClass e (⟨1, h1⟩ : cycles dB) ∈
          LinearMap.range (DirectSum.lof R ℕ M 0) :=
        directSumClass_mem_range_lof e he 0 1 h1 SetLike.GradedOne.one_mem
      rwa [← h1D] at key
    mul_mem := by
      intro i j a b ha hb
      obtain ⟨x, hx, hxi, rfl⟩ := exists_homogeneous_cycle_directSumClass_eq e he i ha
      obtain ⟨y, hy, hyj, rfl⟩ := exists_homogeneous_cycle_directSumClass_eq e he j hb
      rw [directSumRing_mul e mulD oneD hcyc hmulD h1 h1D, hmulD x y hx hy]
      exact directSumClass_mem_range_lof e he (i + j) (x * y) _
        (SetLike.GradedMul.mul_mem hxi hyj) }

/-- **The transported grading is strictly graded commutative.** Both the Koszul commutation rule
and the vanishing of the squares of odd homogeneous elements hold on classes because they hold on
homogeneous cycles. -/
public theorem rangeLofIsStrictlyGradedComm :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
    IsStrictlyGradedComm fun n => LinearMap.range (DirectSum.lof R ℕ M n) := by
  let : Ring (DirectSum ℕ M) := directSumRing e mulD oneD hcyc hmulD h1 h1D
  let : Algebra R (DirectSum ℕ M) := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
  constructor
  · intro i j a b ha hb
    obtain ⟨x, hx, hxi, rfl⟩ := exists_homogeneous_cycle_directSumClass_eq e he i ha
    obtain ⟨y, hy, hyj, rfl⟩ := exists_homogeneous_cycle_directSumClass_eq e he j hb
    rw [directSumRing_mul e mulD oneD hcyc hmulD h1 h1D, hmulD x y hx hy,
      directSumRing_mul e mulD oneD hcyc hmulD h1 h1D, hmulD y x hy hx,
      ← directSumClass_smul e ((-1 : R) ^ (i * j)) (y * x) _
        (by simp [hcyc y x hy hx])]
    exact congrArg (directSumClass e)
      (Subtype.ext (IsStrictlyGradedComm.graded_comm (𝒜 := ℬ) hxi hyj))
  · intro d a ha
    obtain ⟨x, hx, hxd, rfl⟩ := exists_homogeneous_cycle_directSumClass_eq e he (2 * d + 1) ha
    have h0 : dB (0 : B) = 0 := by simp
    have hsq : (⟨x * x, hcyc x x hx hx⟩ : cycles dB) = ⟨0, h0⟩ :=
      Subtype.ext ((pow_two x).symm.trans (IsStrictlyGradedComm.odd_sq_zero (𝒜 := ℬ) hxd))
    rw [pow_two, directSumRing_mul e mulD oneD hcyc hmulD h1 h1D, hmulD x x hx hx, hsq,
      directSumClass_zero e h0]

end GradedStructure

section CycleClosure

variable {R : Type u} {B : Type v} [CommRing R] [Ring B] [Algebra R B] {dB : B →ₗ[R] B}

/-- A natural number is a cycle, once the unit is. -/
public theorem dB_natCast_eq_zero (h1 : dB (1 : B) = 0) (k : ℕ) : dB ((k : ℕ) : B) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, map_add, ih, h1, add_zero]

/-- A power of a cycle is a cycle, once products of cycles are. -/
public theorem dB_pow_eq_zero (hcyc : ∀ x y : B, dB x = 0 → dB y = 0 → dB (x * y) = 0)
    (h1 : dB (1 : B) = 0) {x : B} (hx : dB x = 0) (n : ℕ) : dB (x ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero]; exact h1
  | succ n ih => rw [pow_succ]; exact hcyc _ _ ih hx

end CycleClosure

section CycleAlgebra

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} [IsDifferentialGradedAlgebra ℬ dB]
  (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
  (mulD : DirectSum ℕ M → DirectSum ℕ M → DirectSum ℕ M) (oneD : DirectSum ℕ M)
  (hcyc : ∀ x y : B, dB x = 0 → dB y = 0 → dB (x * y) = 0)
  (hmulD : ∀ (x y : B) (hx : dB x = 0) (hy : dB y = 0),
    mulD (directSumClass e ⟨x, hx⟩) (directSumClass e ⟨y, hy⟩) =
      directSumClass e ⟨x * y, hcyc x y hx hy⟩)
  (h1 : dB (1 : B) = 0) (h1D : oneD = directSumClass e ⟨1, h1⟩)

/-- **The cycles of a differential graded algebra form an `R`-subalgebra**, once products of
cycles are known to be cycles. -/
public def cycleSubalgebra : Subalgebra R B where
  carrier := cycles dB
  mul_mem' ha hb := hcyc _ _ ha hb
  one_mem' := h1
  add_mem' ha hb := Submodule.add_mem (cycles dB) ha hb
  zero_mem' := Submodule.zero_mem (cycles dB)
  algebraMap_mem' r := by
    have hr : algebraMap R B r = r • (1 : B) := Algebra.algebraMap_eq_smul_one r
    have : dB (algebraMap R B r) = 0 := by rw [hr, map_smul, h1, smul_zero]
    exact this

/-- An element lies in the subalgebra of cycles if and only if its differential vanishes. -/
@[simp]
public theorem mem_cycleSubalgebra {x : B} :
    x ∈ cycleSubalgebra (dB := dB) hcyc h1 ↔ dB x = 0 := Iff.rfl

/-- **The class map as a map of `R`-algebras** from the algebra of cycles to the direct sum with
its transported ring and algebra structures. -/
public def cycleAlgHom :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
    cycleSubalgebra (dB := dB) hcyc h1 →ₐ[R] DirectSum ℕ M :=
  letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
  letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
  { toFun := fun x => directSumClass e ⟨(x : B), x.2⟩
    map_one' := h1D.symm
    map_mul' := fun x y => by
      rw [directSumRing_mul e mulD oneD hcyc hmulD h1 h1D, hmulD (x : B) (y : B) x.2 y.2]
      exact congrArg (directSumClass e) (Subtype.ext rfl)
    map_zero' := map_zero (directSumClass e)
    map_add' := fun x y => map_add (directSumClass e) ⟨(x : B), x.2⟩ ⟨(y : B), y.2⟩
    commutes' := fun r => by
      have hr : ((algebraMap R (cycleSubalgebra (dB := dB) hcyc h1) r : _) : B) =
          r • (1 : B) := Algebra.algebraMap_eq_smul_one r
      have hone : directSumClass e (⟨r • (1 : B), by simp [h1]⟩ : cycles dB) =
          r • directSumClass e (⟨1, h1⟩ : cycles dB) :=
        directSumClass_smul e r 1 h1 _
      have halg : algebraMap R (DirectSum ℕ M) r = r • (1 : DirectSum ℕ M) :=
        Algebra.algebraMap_eq_smul_one r
      rw [halg, directSumRing_one e mulD oneD hcyc hmulD h1 h1D, h1D, ← hone]
      exact congrArg (directSumClass e) (Subtype.ext hr) }

/-- The algebra map on cycles agrees with the class map. -/
@[simp]
public theorem cycleAlgHom_apply (x : cycleSubalgebra (dB := dB) hcyc h1) :
    cycleAlgHom e mulD oneD hcyc hmulD h1 h1D x =
      directSumClass e ⟨(x : B), x.2⟩ := rfl

/-- The class of a product of cycles is the product of their classes. -/
public theorem directSumClass_mul_eq (a b : B) (ha : dB a = 0) (hb : dB b = 0)
    (hab : dB (a * b) = 0) :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    directSumClass e ⟨a * b, hab⟩ =
      directSumClass e ⟨a, ha⟩ * directSumClass e ⟨b, hb⟩ := by
  let : Ring (DirectSum ℕ M) := directSumRing e mulD oneD hcyc hmulD h1 h1D
  rw [directSumRing_mul e mulD oneD hcyc hmulD h1 h1D, hmulD a b ha hb]

/-- The class of a power of a cycle is the power of its class. -/
public theorem directSumClass_pow (a : B) (ha : dB a = 0) (n : ℕ) (han : dB (a ^ n) = 0) :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    directSumClass e ⟨a ^ n, han⟩ = directSumClass e ⟨a, ha⟩ ^ n := by
  let : Ring (DirectSum ℕ M) := directSumRing e mulD oneD hcyc hmulD h1 h1D
  let : Algebra R (DirectSum ℕ M) := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
  have hf := map_pow (cycleAlgHom e mulD oneD hcyc hmulD h1 h1D) ⟨a, ha⟩ n
  rw [cycleAlgHom_apply, cycleAlgHom_apply] at hf
  rw [← hf]
  exact congrArg (directSumClass e) (Subtype.ext (by simp))

/-- The class of a natural number is that natural number. -/
public theorem directSumClass_natCast (k : ℕ) (hk : dB ((k : ℕ) : B) = 0) :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    directSumClass e ⟨((k : ℕ) : B), hk⟩ = ((k : ℕ) : DirectSum ℕ M) := by
  let : Ring (DirectSum ℕ M) := directSumRing e mulD oneD hcyc hmulD h1 h1D
  let : Algebra R (DirectSum ℕ M) := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
  have hf := map_natCast (cycleAlgHom e mulD oneD hcyc hmulD h1 h1D) k
  rw [cycleAlgHom_apply] at hf
  rw [← hf]
  exact congrArg (directSumClass e) (Subtype.ext (by simp))

/-- The class of a finite sum of cycles is the sum of their classes. -/
public theorem directSumClass_sum {ι : Type*} (s : Finset ι) (g : ι → B)
    (hg : ∀ i, dB (g i) = 0) (hs : dB (∑ i ∈ s, g i) = 0) :
    directSumClass e ⟨∑ i ∈ s, g i, hs⟩ =
      ∑ i ∈ s, directSumClass e ⟨g i, hg i⟩ := by
  have hsub : (⟨∑ i ∈ s, g i, hs⟩ : cycles dB) =
      ∑ i ∈ s, (⟨g i, hg i⟩ : cycles dB) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
  rw [hsub, map_sum]

end CycleAlgebra

section EvenParts

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ]
  {dB : B →ₗ[R] B} [IsDifferentialGradedAlgebra ℬ dB]

/-- A homogeneous component of an element of `⨆ d, ℬ (f d)`, in a degree outside the range of
`f`, vanishes. -/
private theorem decompose_eq_zero_of_mem_iSup {y : B} (f : ℕ → ℕ) (hy : y ∈ ⨆ d, ℬ (f d))
    {i : ℕ} (hi : ∀ d : ℕ, i ≠ f d) : ((DirectSum.decompose ℬ y i : ℬ i) : B) = 0 := by
  induction hy using Submodule.iSup_induction' with
  | mem d z hz => rw [DirectSum.decompose_of_mem_ne ℬ hz (Ne.symm (hi d))]
  | zero => simp
  | add a b _ _ iha ihb =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, iha, ihb, add_zero]

/-- A homogeneous component of an element of the positive even part, in a degree which is not
positive even, vanishes. -/
public theorem decompose_eq_zero_of_mem_positiveEvenPart {y : B}
    (hy : y ∈ positiveEvenPart ℬ) {i : ℕ} (hi : ∀ d : ℕ, i ≠ 2 * (d + 1)) :
    ((DirectSum.decompose ℬ y i : ℬ i) : B) = 0 :=
  decompose_eq_zero_of_mem_iSup (fun d => 2 * (d + 1)) hy hi

/-- A homogeneous component of an element of the even part, in an odd degree, vanishes. -/
public theorem decompose_eq_zero_of_mem_evenPart {y : B}
    (hy : y ∈ evenPart ℬ) {i : ℕ} (hi : ∀ d : ℕ, i ≠ 2 * d) :
    ((DirectSum.decompose ℬ y i : ℬ i) : B) = 0 :=
  decompose_eq_zero_of_mem_iSup (fun d => 2 * d) hy hi

variable (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
  (he : ∀ n, Submodule.map (e : DirectSum ℕ M →ₗ[R] Homology (𝒜 := ℬ) dB)
    (LinearMap.range (DirectSum.lof R ℕ M n)) = totalHomologyGrade ℬ dB n)

include he

/-- The class of a cycle lies in the span of the pieces indexed by the degrees in which the cycle
has a nonzero homogeneous component. -/
public theorem directSumClass_mem_iSup_of_decompose_eq_zero {y : B} (h : dB y = 0)
    (p : ℕ → Prop) (hy : ∀ i : ℕ, ¬ p i → ((DirectSum.decompose ℬ y i : ℬ i) : B) = 0) :
    directSumClass e ⟨y, h⟩ ∈
      ⨆ i : ℕ, ⨆ _ : p i, LinearMap.range (DirectSum.lof R ℕ M i) := by
  classical
  have hcy : ∀ i : ℕ, dB ((DirectSum.decompose ℬ y i : ℬ i) : B) = 0 :=
    fun i => d_decompose_eq_zero ℬ dB h i
  have hsum : (⟨y, h⟩ : cycles dB) =
      ∑ i ∈ (DirectSum.decompose ℬ y).support,
        (⟨((DirectSum.decompose ℬ y i : ℬ i) : B), hcy i⟩ : cycles dB) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa using (DirectSum.sum_support_decompose ℬ y).symm
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hpi : p i := by
    by_contra hc
    refine (DFinsupp.mem_support_iff.mp hi) ?_
    exact Subtype.ext (hy i hc)
  exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hpi
    (directSumClass_mem_range_lof e he i _ _ (DirectSum.decompose ℬ y i).property))

/-- The class of a cycle in `⨆ d, ℬ (f d)` lies in `⨆ d, range (lof (f d))`. -/
private theorem directSumClass_mem_iSup_of_mem_iSup {y : B} (h : dB y = 0) (f : ℕ → ℕ)
    (hy : y ∈ ⨆ d, ℬ (f d)) :
    directSumClass e ⟨y, h⟩ ∈ ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (f d)) := by
  have hle : (⨆ i : ℕ, ⨆ _ : (∃ d : ℕ, i = f d), LinearMap.range (DirectSum.lof R ℕ M i)) ≤
      ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (f d)) := by
    refine iSup_le fun i => iSup_le ?_
    rintro ⟨d, rfl⟩
    exact le_iSup_of_le d le_rfl
  exact hle (directSumClass_mem_iSup_of_decompose_eq_zero e he h (fun i => ∃ d : ℕ, i = f d)
    (fun i hi => decompose_eq_zero_of_mem_iSup f hy fun d hd => hi ⟨d, hd⟩))

/-- The class of a positive even cycle lies in the positive even part of the transported
grading. -/
public theorem directSumClass_mem_iSup_positiveEven {y : B} (h : dB y = 0)
    (hy : y ∈ positiveEvenPart ℬ) :
    directSumClass e ⟨y, h⟩ ∈
      ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (2 * (d + 1))) :=
  directSumClass_mem_iSup_of_mem_iSup e he h (fun d => 2 * (d + 1)) hy

/-- The class of an even cycle lies in the even part of the transported grading. -/
public theorem directSumClass_mem_iSup_even {y : B} (h : dB y = 0)
    (hy : y ∈ evenPart ℬ) :
    directSumClass e ⟨y, h⟩ ∈ ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (2 * d)) :=
  directSumClass_mem_iSup_of_mem_iSup e he h (fun d => 2 * d) hy

/-- Every element of `⨆ d, range (lof (f d))` is the class of a cycle in `⨆ d, ℬ (f d)`. -/
private theorem exists_cycle_directSumClass_eq_of_mem_iSup (f : ℕ → ℕ) {z : DirectSum ℕ M}
    (hz : z ∈ ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (f d))) :
    ∃ (y : B) (h : dB y = 0), y ∈ ⨆ d, ℬ (f d) ∧ directSumClass e ⟨y, h⟩ = z := by
  induction hz using Submodule.iSup_induction' with
  | mem d w hw =>
      obtain ⟨x, hx, hxg, hxw⟩ := exists_homogeneous_cycle_directSumClass_eq e he (f d) hw
      exact ⟨x, hx, Submodule.mem_iSup_of_mem d hxg, hxw⟩
  | zero => exact ⟨0, by simp, Submodule.zero_mem _, map_zero (directSumClass e)⟩
  | add a b _ _ iha ihb =>
      obtain ⟨y₁, hy₁, hp₁, rfl⟩ := iha
      obtain ⟨y₂, hy₂, hp₂, rfl⟩ := ihb
      exact ⟨y₁ + y₂, by simp [hy₁, hy₂], Submodule.add_mem _ hp₁ hp₂,
        directSumClass_add e y₁ y₂ hy₁ hy₂ _⟩

/-- Every element of the positive even part of the transported grading is the class of a positive
even cycle. -/
public theorem exists_positiveEven_cycle_directSumClass_eq {z : DirectSum ℕ M}
    (hz : z ∈ ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (2 * (d + 1)))) :
    ∃ (y : B) (h : dB y = 0), y ∈ positiveEvenPart ℬ ∧ directSumClass e ⟨y, h⟩ = z :=
  exists_cycle_directSumClass_eq_of_mem_iSup e he (fun d => 2 * (d + 1)) hz

/-- Every element of the even part of the transported grading is the class of an even cycle. -/
public theorem exists_even_cycle_directSumClass_eq {z : DirectSum ℕ M}
    (hz : z ∈ ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (2 * d))) :
    ∃ (y : B) (h : dB y = 0), y ∈ evenPart ℬ ∧ directSumClass e ⟨y, h⟩ = z :=
  exists_cycle_directSumClass_eq_of_mem_iSup e he (fun d => 2 * d) hz

end EvenParts

section Degree

variable {R : Type u} {M : ℕ → Type v} [CommRing R] [∀ n, AddCommGroup (M n)]
  [∀ n, Module R (M n)]

/-- An element of the positive even part of a direct sum has vanishing degree-zero
coordinate. -/
public theorem apply_zero_eq_zero_of_mem_iSup_positiveEven {z : DirectSum ℕ M}
    (hz : z ∈ ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (2 * (d + 1)))) : z 0 = 0 := by
  induction hz using Submodule.iSup_induction' with
  | mem d w hw =>
      obtain ⟨v, rfl⟩ := hw
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ v (by omega)]
  | zero => rfl
  | add a b _ _ iha ihb => rw [DirectSum.add_apply, iha, ihb, add_zero]

/-- The degree-zero piece of a direct sum meets its positive even part only in zero. -/
public theorem eq_zero_of_mem_range_lof_zero_of_mem_iSup_positiveEven {z : DirectSum ℕ M}
    (h0 : z ∈ LinearMap.range (DirectSum.lof R ℕ M 0))
    (hz : z ∈ ⨆ d : ℕ, LinearMap.range (DirectSum.lof R ℕ M (2 * (d + 1)))) : z = 0 := by
  obtain ⟨v, rfl⟩ := h0
  have hv : v = 0 := by
    have hcoord := apply_zero_eq_zero_of_mem_iSup_positiveEven hz
    rwa [DirectSum.lof_eq_of, DirectSum.of_eq_same] at hcoord
  rw [hv, map_zero]

end Degree

section DividedPowerTransport

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  {dB : B →ₗ[R] B} [IsDifferentialGradedAlgebra ℬ dB]
  (γB : DividedPowerStructure ℬ)
  (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
  (mulD : DirectSum ℕ M → DirectSum ℕ M → DirectSum ℕ M) (oneD : DirectSum ℕ M)
  (hcyc : ∀ x y : B, dB x = 0 → dB y = 0 → dB (x * y) = 0)
  (hmulD : ∀ (x y : B) (hx : dB x = 0) (hy : dB y = 0),
    mulD (directSumClass e ⟨x, hx⟩) (directSumClass e ⟨y, hy⟩) =
      directSumClass e ⟨x * y, hcyc x y hx hy⟩)
  (h1 : dB (1 : B) = 0) (h1D : oneD = directSumClass e ⟨1, h1⟩)
  (he : ∀ n, Submodule.map (e : DirectSum ℕ M →ₗ[R] Homology (𝒜 := ℬ) dB)
    (LinearMap.range (DirectSum.lof R ℕ M n)) = totalHomologyGrade ℬ dB n)
  (dpowD : ℕ → DirectSum ℕ M → DirectSum ℕ M)
  (hdpcyc : ∀ (n : ℕ) (x : B), x ∈ positiveEvenPart ℬ → dB x = 0 →
    dB (γB.dpow n x) = 0)
  (hdpowD : ∀ (n : ℕ) (x : B) (hx : x ∈ positiveEvenPart ℬ) (hd : dB x = 0),
    dpowD n (directSumClass e ⟨x, hd⟩) = directSumClass e ⟨γB.dpow n x, hdpcyc n x hx hd⟩)

open scoped Classical in
/-- **The transported divided power structure on a direct sum.** Given a system of divided powers
on the direct sum which, on the classes of positive even cycles, is the system of divided powers
of the differential graded algebra, the direct sum carries a divided power structure for its
transported ring, algebra and graded structures. -/
public def directSumDividedPowerStructure :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
    letI := rangeLofGradedAlgebra e mulD oneD hcyc hmulD h1 h1D he
    letI := rangeLofIsStrictlyGradedComm e mulD oneD hcyc hmulD h1 h1D he
    DividedPowerStructure (R := R) fun n => LinearMap.range (DirectSum.lof R ℕ M n) := by
  letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
  letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
  letI := rangeLofGradedAlgebra e mulD oneD hcyc hmulD h1 h1D he
  letI := rangeLofIsStrictlyGradedComm e mulD oneD hcyc hmulD h1 h1D he
  have hmemP : ∀ (y : B) (h : dB y = 0), y ∈ positiveEvenPart ℬ →
      directSumClass e ⟨y, h⟩ ∈
        positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i) :=
    fun y h hy => directSumClass_mem_iSup_positiveEven e he h hy
  have hrepP : ∀ z : DirectSum ℕ M,
      z ∈ (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i)) →
      ∃ (y : B) (h : dB y = 0), y ∈ positiveEvenPart ℬ ∧ directSumClass e ⟨y, h⟩ = z :=
    fun z hz => exists_positiveEven_cycle_directSumClass_eq e he hz
  have hrepE : ∀ z : DirectSum ℕ M,
      z ∈ (evenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i)) →
      ∃ (y : B) (h : dB y = 0), y ∈ evenPart ℬ ∧ directSumClass e ⟨y, h⟩ = z :=
    fun z hz => exists_even_cycle_directSumClass_eq e he hz
  have key : ∀ (n : ℕ) (y : B) (hy : y ∈ positiveEvenPart ℬ) (h : dB y = 0),
      (if directSumClass e (⟨y, h⟩ : cycles dB) ∈
          (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i))
        then dpowD n (directSumClass e (⟨y, h⟩ : cycles dB)) else 0) =
        directSumClass e ⟨γB.dpow n y, hdpcyc n y hy h⟩ := fun n y hy h => by
    rw [ite_eq_left (hmemP y h hy), hdpowD n y hy h]
  have h0 : dB (0 : B) = 0 := by simp
  have hp0 : (0 : B) ∈ positiveEvenPart ℬ := Submodule.zero_mem _
  have hzero0 : directSumClass e (⟨0, h0⟩ : cycles dB) = 0 := map_zero _
  have keyzero : ∀ (n : ℕ), n ≠ 0 → ∀ (y : B) (hy : y ∈ positiveEvenPart ℬ) (h : dB y = 0),
      directSumClass e (⟨y, h⟩ : cycles dB) = 0 →
      (if directSumClass e (⟨y, h⟩ : cycles dB) ∈
          (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i))
        then dpowD n (directSumClass e (⟨y, h⟩ : cycles dB)) else 0) = 0 := by
    intro n hn y hy h hy0
    have hcongr := congrArg
      (fun z : DirectSum ℕ M =>
        if z ∈ (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i))
          then dpowD n z else 0)
      (hy0.trans hzero0.symm)
    refine hcongr.trans ?_
    rw [key n 0 hp0 h0,
      (Subtype.ext (γB.dpow_apply_zero hn) :
        (⟨γB.dpow n 0, hdpcyc n 0 hp0 h0⟩ : cycles dB) = ⟨0, h0⟩), hzero0]
  refine
    { dpow := fun n z =>
        if z ∈ (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i))
          then dpowD n z else 0
      dpow_null := ?_
      dpow_zero := ?_
      dpow_one := ?_
      dpow_mem := ?_
      dpow_mem_grade := ?_
      dpow_mul := ?_
      dpow_mul_even := ?_
      dpow_mul_odd := ?_
      dpow_add := ?_
      dpow_dpow := ?_ }
  · intro n x hx
    exact ite_eq_right hx
  · intro x hx
    obtain ⟨y, hy, hyp, rfl⟩ := hrepP x hx
    rw [key 0 y hyp hy,
      (Subtype.ext (γB.dpow_zero hyp) :
        (⟨γB.dpow 0 y, hdpcyc 0 y hyp hy⟩ : cycles dB) = ⟨1, h1⟩), ← h1D]
    exact (directSumRing_one e mulD oneD hcyc hmulD h1 h1D).symm
  · intro x hx
    obtain ⟨y, hy, hyp, rfl⟩ := hrepP x hx
    rw [key 1 y hyp hy]
    exact congrArg (directSumClass e) (Subtype.ext (γB.dpow_one hyp))
  · intro n x hn hx
    obtain ⟨y, hy, hyp, rfl⟩ := hrepP x hx
    rw [key n y hyp hy]
    exact hmemP _ _ (γB.dpow_mem hn hyp)
  · intro n d x hn hx hxg
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨y, hy, hyp, rfl⟩ := hrepP x hx
      have hy0 : directSumClass e (⟨y, hy⟩ : cycles dB) = 0 :=
        eq_zero_of_mem_range_lof_zero_of_mem_iSup_positiveEven (by simpa using hxg) hx
      rw [keyzero n hn y hyp hy hy0]
      exact Submodule.zero_mem _
    · obtain ⟨y, hy, hyg, rfl⟩ :=
        exists_homogeneous_cycle_directSumClass_eq e he (2 * d) hxg
      have hyp : y ∈ positiveEvenPart ℬ := mem_positiveEvenPart_of_mem_grade ℬ hd hyg
      rw [key n y hyp hy]
      exact directSumClass_mem_range_lof e he (2 * n * d) _ _
        (γB.dpow_mem_grade hn hyp hyg)
  · intro m n x hx
    obtain ⟨y, hy, hyp, rfl⟩ := hrepP x hx
    have hdn := hdpcyc n y hyp hy
    have hdm := hdpcyc m y hyp hy
    have hdnm := hdpcyc (n + m) y hyp hy
    have hC : dB (((n + m).choose n : ℕ) : B) = 0 := dB_natCast_eq_zero h1 _
    rw [key n y hyp hy, key m y hyp hy, key (n + m) y hyp hy,
      ← directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D _ _ hdn hdm
        (hcyc _ _ hdn hdm),
      (Subtype.ext (γB.dpow_mul hyp) :
        (⟨γB.dpow n y * γB.dpow m y, hcyc _ _ hdn hdm⟩ : cycles dB) =
          ⟨((n + m).choose n : B) * γB.dpow (n + m) y, hcyc _ _ hC hdnm⟩),
      directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D _ _ hC hdnm,
      directSumClass_natCast e mulD oneD hcyc hmulD h1 h1D]
  · intro n x y hn hx hy
    obtain ⟨a, ha, hae, rfl⟩ := hrepE x hx
    obtain ⟨b, hb, hbp, rfl⟩ := hrepP y hy
    have hab : dB (a * b) = 0 := hcyc a b ha hb
    have habp : a * b ∈ positiveEvenPart ℬ := evenPart_mul_positiveEvenPart ℬ hae hbp
    have han : dB (a ^ n) = 0 := dB_pow_eq_zero hcyc h1 ha n
    have hdb := hdpcyc n b hbp hb
    rw [← directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D a b ha hb hab,
      key n (a * b) habp hab, key n b hbp hb,
      ← directSumClass_pow e mulD oneD hcyc hmulD h1 h1D a ha n han,
      ← directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D _ _ han hdb
        (hcyc _ _ han hdb)]
    exact congrArg (directSumClass e) (Subtype.ext (γB.dpow_mul_even hn hae hbp))
  · intro n d' e' x y hn hxd hye
    obtain ⟨a, ha, hag, rfl⟩ :=
      exists_homogeneous_cycle_directSumClass_eq e he (2 * d' + 1) hxd
    obtain ⟨b, hb, hbg, rfl⟩ :=
      exists_homogeneous_cycle_directSumClass_eq e he (2 * e' + 1) hye
    have hab : dB (a * b) = 0 := hcyc a b ha hb
    have habp : a * b ∈ positiveEvenPart ℬ := by
      refine Submodule.mem_iSup_of_mem (d' + e') ?_
      have hdeg : 2 * (d' + e' + 1) = 2 * d' + 1 + (2 * e' + 1) := by omega
      rw [hdeg]
      exact SetLike.GradedMul.mul_mem hag hbg
    rw [← directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D a b ha hb hab,
      key n (a * b) habp hab,
      (Subtype.ext (γB.dpow_mul_odd hn hag hbg) :
        (⟨γB.dpow n (a * b), hdpcyc n (a * b) habp hab⟩ : cycles dB) = ⟨0, h0⟩), hzero0]
  · intro n x y hx hy
    obtain ⟨a, ha, hap, rfl⟩ := hrepP x hx
    obtain ⟨b, hb, hbp, rfl⟩ := hrepP y hy
    have hab : dB (a + b) = 0 := by simp [ha, hb]
    have habp : a + b ∈ positiveEvenPart ℬ := Submodule.add_mem _ hap hbp
    have hterms : ∀ ij : ℕ × ℕ, dB (γB.dpow ij.1 a * γB.dpow ij.2 b) = 0 :=
      fun ij => hcyc _ _ (hdpcyc ij.1 a hap ha) (hdpcyc ij.2 b hbp hb)
    have hRHS : ∀ ij : ℕ × ℕ,
        (if directSumClass e (⟨a, ha⟩ : cycles dB) ∈
            (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i))
          then dpowD ij.1 (directSumClass e (⟨a, ha⟩ : cycles dB)) else 0) *
        (if directSumClass e (⟨b, hb⟩ : cycles dB) ∈
            (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i))
          then dpowD ij.2 (directSumClass e (⟨b, hb⟩ : cycles dB)) else 0) =
          directSumClass e ⟨γB.dpow ij.1 a * γB.dpow ij.2 b, hterms ij⟩ := by
      intro ij
      rw [key ij.1 a hap ha, key ij.2 b hbp hb,
        ← directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D _ _
          (hdpcyc ij.1 a hap ha) (hdpcyc ij.2 b hbp hb) (hterms ij)]
    rw [← directSumClass_add e a b ha hb hab, key n (a + b) habp hab,
      Finset.sum_congr rfl fun ij _ => hRHS ij,
      ← directSumClass_sum e (Finset.antidiagonal n)
        (fun ij : ℕ × ℕ => γB.dpow ij.1 a * γB.dpow ij.2 b) hterms
        (by rw [← AddSubmonoidClass.coe_finsetSum (s := Finset.antidiagonal n)
              (f := fun ij : ℕ × ℕ => (⟨γB.dpow ij.1 a * γB.dpow ij.2 b, hterms ij⟩ : cycles dB))]
            exact (∑ ij ∈ Finset.antidiagonal n,
              (⟨γB.dpow ij.1 a * γB.dpow ij.2 b, hterms ij⟩ : cycles dB)).property)]
    exact congrArg (directSumClass e) (Subtype.ext (γB.dpow_add hap hbp))
  · intro m n x hm hn hx
    obtain ⟨y, hy, hyp, rfl⟩ := hrepP x hx
    have hdm := hdpcyc m y hyp hy
    have hdmem : γB.dpow m y ∈ positiveEvenPart ℬ := γB.dpow_mem hm hyp
    have hdnm := hdpcyc (n * m) y hyp hy
    have hc : dB ((((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) : ℕ) : B) = 0 :=
      dB_natCast_eq_zero h1 _
    rw [key m y hyp hy, key n (γB.dpow m y) hdmem hdm, key (n * m) y hyp hy,
      (Subtype.ext (γB.dpow_dpow hm hn hyp) :
        (⟨γB.dpow n (γB.dpow m y), hdpcyc n (γB.dpow m y) hdmem hdm⟩ : cycles dB) =
          ⟨(((n * m).factorial / (n.factorial * m.factorial ^ n) : ℕ) : B) *
            γB.dpow (n * m) y, hcyc _ _ hc hdnm⟩),
      directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D _ _ hc hdnm,
      directSumClass_natCast e mulD oneD hcyc hmulD h1 h1D]

open scoped Classical in
/-- **The transported divided powers on classes of positive even cycles.** -/
public theorem directSumDividedPowerStructure_dpow (n : ℕ) (x : B)
    (hx : x ∈ positiveEvenPart ℬ) (hd : dB x = 0) :
    letI := directSumRing e mulD oneD hcyc hmulD h1 h1D
    letI := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
    letI := rangeLofGradedAlgebra e mulD oneD hcyc hmulD h1 h1D he
    letI := rangeLofIsStrictlyGradedComm e mulD oneD hcyc hmulD h1 h1D he
    (directSumDividedPowerStructure γB e mulD oneD hcyc hmulD h1 h1D he dpowD
        hdpcyc hdpowD).dpow n (directSumClass e ⟨x, hd⟩) =
      directSumClass e ⟨γB.dpow n x, hdpcyc n x hx hd⟩ := by
  let : Ring (DirectSum ℕ M) := directSumRing e mulD oneD hcyc hmulD h1 h1D
  let : Algebra R (DirectSum ℕ M) := directSumAlgebra e mulD oneD hcyc hmulD h1 h1D
  let : GradedAlgebra fun i => LinearMap.range (DirectSum.lof R ℕ M i) :=
    rangeLofGradedAlgebra e mulD oneD hcyc hmulD h1 h1D he
  let : IsStrictlyGradedComm fun i => LinearMap.range (DirectSum.lof R ℕ M i) :=
    rangeLofIsStrictlyGradedComm e mulD oneD hcyc hmulD h1 h1D he
  change (if directSumClass e (⟨x, hd⟩ : cycles dB) ∈
      (positiveEvenPart fun i => LinearMap.range (DirectSum.lof R ℕ M i))
    then dpowD n (directSumClass e (⟨x, hd⟩ : cycles dB)) else 0) = _
  rw [ite_eq_left (directSumClass_mem_iSup_positiveEven e he hd hx), hdpowD n x hx hd]

end DividedPowerTransport

section Assembly

variable {R : Type u} {B : Type v} {M : ℕ → Type w}
  [CommRing R] [Ring B] [Algebra R B]
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
  (dB : B →ₗ[R] B) [IsDifferentialGradedAlgebra ℬ dB]

/-- **The induced divided power structure, transported to a direct sum.** If the homology of a
strictly graded-commutative divided power differential graded algebra carries the induced divided
power structure of Tag 09PK, and a direct sum is identified with that homology degreewise, then
the direct sum carries a strictly graded-commutative graded `R`-algebra structure with divided
powers whose addition and scalar multiplication are the direct sum's own and whose degree-`n`
piece is the range of the `n`-th inclusion. The structure is the transported one: the class map
`cycles dB → ⨁ n, M n` is unital, multiplicative, degreewise, and carries the divided powers of
the algebra to those of the direct sum. -/
public theorem exists_dividedPowerStructure_directSum (γB : DividedPowerStructure ℬ)
    (hind : HasInducedDividedPowers ℬ dB γB)
    (e : DirectSum ℕ M ≃ₗ[R] Homology (𝒜 := ℬ) dB)
    (he : ∀ n, Submodule.map (e : DirectSum ℕ M →ₗ[R] Homology (𝒜 := ℬ) dB)
      (LinearMap.range (DirectSum.lof R ℕ M n)) = totalHomologyGrade ℬ dB n) :
    let κ : cycles dB →ₗ[R] DirectSum ℕ M := directSumClass e
    ∃ hRing : Ring (DirectSum ℕ M),
      ∃ hAlgebra : @Algebra R (DirectSum ℕ M) _ hRing.toSemiring,
        hRing.toAddCommGroup = (inferInstance : AddCommGroup (DirectSum ℕ M)) ∧
        @Algebra.toSMul R (DirectSum ℕ M) _ hRing.toSemiring hAlgebra =
          (inferInstance : SMul R (DirectSum ℕ M)) ∧
        (letI := hRing
         letI := hAlgebra
         letI : AddCommMonoid (DirectSum ℕ M) := hRing.toAddCommMonoid
         letI : Module R (DirectSum ℕ M) := Algebra.toModule
         ∃ 𝒟 : ℕ → Submodule R (DirectSum ℕ M),
           (∀ n, (𝒟 n : Set (DirectSum ℕ M)) = Set.range (DirectSum.lof R ℕ M n)) ∧
           ∃ hGraded : GradedAlgebra 𝒟,
             letI := hGraded
             ∃ hStrict : IsStrictlyGradedComm 𝒟,
               letI := hStrict
               ∃ γD : @DividedPowerStructure R (DirectSum ℕ M) _ hRing hAlgebra 𝒟
                   hGraded hStrict,
                 (∀ (n : ℕ) (x : B) (h : dB x = 0), x ∈ ℬ n → κ ⟨x, h⟩ ∈ 𝒟 n) ∧
                 (∃ h1 : dB (1 : B) = 0, κ ⟨1, h1⟩ = 1) ∧
                 (∀ {x y : B} (hx : dB x = 0) (hy : dB y = 0),
                   ∃ hxy : dB (x * y) = 0, κ ⟨x * y, hxy⟩ = κ ⟨x, hx⟩ * κ ⟨y, hy⟩) ∧
                 (∀ {n : ℕ} {x : B}, x ∈ positiveEvenPart ℬ → ∀ hd : dB x = 0,
                   ∃ hγ : dB (γB.dpow n x) = 0,
                     γD.dpow n (κ ⟨x, hd⟩) = κ ⟨γB.dpow n x, hγ⟩)) := by
  intro κ
  obtain ⟨hRingH, hAlgebraH, hGradedH, hStrictH, γH, hz, hadd, hsmul, hone, hmul, hdpow⟩ := hind
  let : Ring (Homology (𝒜 := ℬ) dB) := hRingH
  let : Algebra R (Homology (𝒜 := ℬ) dB) := hAlgebraH
  have hcyc : ∀ x y : B, dB x = 0 → dB y = 0 → dB (x * y) = 0 :=
    fun _ _ hx hy => (hmul hx hy).choose
  set mulD : DirectSum ℕ M → DirectSum ℕ M → DirectSum ℕ M :=
    fun a b => e.symm (e a * e b) with hmulDdef
  set oneD : DirectSum ℕ M := e.symm 1 with honeDdef
  set dpowD : ℕ → DirectSum ℕ M → DirectSum ℕ M :=
    fun n a => e.symm (γH.dpow n (e a)) with hdpowDdef
  have hclass : ∀ (x : B) (h : dB x = 0),
      e (directSumClass e (⟨x, h⟩ : cycles dB)) =
        (Submodule.Quotient.mk (⟨x, h⟩ : cycles dB) : Homology (𝒜 := ℬ) dB) :=
    fun x h => e.apply_symm_apply _
  have hmulD : ∀ (x y : B) (hx : dB x = 0) (hy : dB y = 0),
      mulD (directSumClass e ⟨x, hx⟩) (directSumClass e ⟨y, hy⟩) =
        directSumClass e ⟨x * y, hcyc x y hx hy⟩ := by
    intro x y hx hy
    rw [hmulDdef]
    simp only [hclass]
    exact congrArg e.symm (hmul hx hy).choose_spec.symm
  have h1 : dB (1 : B) = 0 := hone.choose
  have h1D : oneD = directSumClass e ⟨1, h1⟩ := by
    rw [honeDdef]
    exact congrArg e.symm hone.choose_spec.symm
  have hdpcyc : ∀ (n : ℕ) (x : B), x ∈ positiveEvenPart ℬ → dB x = 0 →
      dB (γB.dpow n x) = 0 := fun n x hx hd => (hdpow hx hd).choose
  have hdpowD : ∀ (n : ℕ) (x : B) (hx : x ∈ positiveEvenPart ℬ) (hd : dB x = 0),
      dpowD n (directSumClass e ⟨x, hd⟩) =
        directSumClass e ⟨γB.dpow n x, hdpcyc n x hx hd⟩ := by
    intro n x hx hd
    rw [hdpowDdef]
    simp only [hclass]
    exact congrArg e.symm (hdpow hx hd).choose_spec
  refine ⟨directSumRing e mulD oneD hcyc hmulD h1 h1D,
    directSumAlgebra e mulD oneD hcyc hmulD h1 h1D, rfl, rfl,
    fun n => LinearMap.range (DirectSum.lof R ℕ M n),
    fun n => LinearMap.coe_range _,
    rangeLofGradedAlgebra e mulD oneD hcyc hmulD h1 h1D he,
    rangeLofIsStrictlyGradedComm e mulD oneD hcyc hmulD h1 h1D he,
    directSumDividedPowerStructure γB e mulD oneD hcyc hmulD h1 h1D he dpowD hdpcyc hdpowD,
    fun n x h hx => directSumClass_mem_range_lof e he n x h hx,
    ⟨h1, h1D.symm⟩,
    fun {x y} hx hy => ⟨hcyc x y hx hy,
      directSumClass_mul_eq e mulD oneD hcyc hmulD h1 h1D x y hx hy (hcyc x y hx hy)⟩,
    fun {n x} hx hd => ⟨hdpcyc n x hx hd, ?_⟩⟩
  exact directSumDividedPowerStructure_dpow γB e mulD oneD hcyc hmulD h1 h1D he dpowD
    hdpcyc hdpowD n x hx hd

end Assembly

section TorAlgebra

attribute [local instance] Resolution.ring Resolution.algebra Resolution.graded
  Resolution.strict Resolution.dga Resolution.compatible

attribute [local instance] isDifferentialGradedAlgebra_baseChange

/-- **Divided powers on `Tor_*^R(S, T)`.** For a commutative ring `R` and commutative
`R`-algebras `S` and `T`, the direct sum `⨁ n, Tor_n^R(S, T)` carries a ring structure, an
`R`-algebra structure, a grading whose degree-`n` piece is the range of the `n`-th inclusion of
the direct sum, a graded algebra structure for that grading, strict graded commutativity, and a
divided power structure — with the addition and the scalar multiplication being the direct sum's
own.

The structure is the one transported along
`DividedPowers.TateResolution.torDirectSumEquivHomology` from the induced structure on the
homology of `T ⊗[R] A`, for `A` the Tate resolution of `S` along the tautological presentation:
the class map `κ` of that identification, which sends a cycle of `T ⊗[R] A` to the element of the
direct sum corresponding to its homology class, is unital and multiplicative, takes a cycle of
degree `n` into the degree-`n` piece, and takes the divided powers of `T ⊗[R] A` to those of the
direct sum. Those divided powers are in turn the base change of the divided powers of the Tate
resolution. -/
@[stacks 09PQ]
public theorem exists_dividedPowerStructure_torDirectSum
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    ∃ Res : Resolution R S S (tautologicalPresentation R S),
      Res = tateResolution (tautologicalPresentation R S)
          (surjective_tautologicalPresentation R S) ∧
      (let ℬ : ℕ → Submodule R (T ⊗[R] Res.A) :=
         restrictGrade R fun i => (Res.grade i).baseChange T
       let dB : T ⊗[R] Res.A →ₗ[R] T ⊗[R] Res.A :=
         (LinearMap.baseChange T Res.differential).restrictScalars R
       ∃ hStrict : IsStrictlyGradedComm ℬ,
         letI := hStrict
         ∃ γB : DividedPowerStructure ℬ,
           IsCompatibleWithDifferential γB dB ∧
           (∀ (n : ℕ) (x : Res.A), x ∈ positiveEvenPart Res.grade →
             γB.dpow n (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] Res.gamma.dpow n x) ∧
           (let κ : cycles dB →ₗ[R] DirectSum ℕ fun n => torGraded R S T n :=
              directSumClass (torDirectSumEquivHomology Res T
                (surjective_tautologicalPresentation R S))
            ∃ hRing : Ring (DirectSum ℕ fun n => torGraded R S T n),
              ∃ hAlgebra : @Algebra R (DirectSum ℕ fun n => torGraded R S T n) _
                  hRing.toSemiring,
                hRing.toAddCommGroup =
                  (inferInstance : AddCommGroup (DirectSum ℕ fun n => torGraded R S T n)) ∧
                @Algebra.toSMul R (DirectSum ℕ fun n => torGraded R S T n) _
                    hRing.toSemiring hAlgebra =
                  (inferInstance : SMul R (DirectSum ℕ fun n => torGraded R S T n)) ∧
                (letI := hRing
                 letI := hAlgebra
                 letI : AddCommMonoid (DirectSum ℕ fun n => torGraded R S T n) :=
                   hRing.toAddCommMonoid
                 letI : Module R (DirectSum ℕ fun n => torGraded R S T n) := Algebra.toModule
                 ∃ 𝒟 : ℕ → Submodule R (DirectSum ℕ fun n => torGraded R S T n),
                   (∀ n, (𝒟 n : Set (DirectSum ℕ fun m => torGraded R S T m)) =
                     Set.range (DirectSum.lof R ℕ (fun m => torGraded R S T m) n)) ∧
                   ∃ hGraded : GradedAlgebra 𝒟,
                     letI := hGraded
                     ∃ hStrictD : IsStrictlyGradedComm 𝒟,
                       letI := hStrictD
                       ∃ γD : @DividedPowerStructure R
                           (DirectSum ℕ fun n => torGraded R S T n) _ hRing hAlgebra 𝒟
                           hGraded hStrictD,
                         (∀ (n : ℕ) (x : T ⊗[R] Res.A) (h : dB x = 0), x ∈ ℬ n →
                           κ ⟨x, h⟩ ∈ 𝒟 n) ∧
                         (∃ h1 : dB (1 : T ⊗[R] Res.A) = 0, κ ⟨1, h1⟩ = 1) ∧
                         (∀ {x y : T ⊗[R] Res.A} (hx : dB x = 0) (hy : dB y = 0),
                           ∃ hxy : dB (x * y) = 0,
                             κ ⟨x * y, hxy⟩ = κ ⟨x, hx⟩ * κ ⟨y, hy⟩) ∧
                         (∀ {n : ℕ} {x : T ⊗[R] Res.A}, x ∈ positiveEvenPart ℬ →
                           ∀ hd : dB x = 0,
                             ∃ hγ : dB (γB.dpow n x) = 0,
                               γD.dpow n (κ ⟨x, hd⟩) = κ ⟨γB.dpow n x, hγ⟩)))) := by
  obtain ⟨Res, hRes, hbody⟩ :=
    exists_dividedPowerStructure_homology_tateResolution R S T
  refine ⟨Res, hRes, ?_⟩
  obtain ⟨hStrict, hDGA, γB, hcompat, hγB, hind⟩ := hbody
  refine ⟨hStrict, γB, hcompat, hγB, ?_⟩
  exact exists_dividedPowerStructure_directSum _ _ γB hind
    (torDirectSumEquivHomology Res T (surjective_tautologicalPresentation R S))
    (map_torDirectSumEquivHomology_range_lof Res T
      (surjective_tautologicalPresentation R S))

end TorAlgebra

end DividedPowers.TateResolution

end

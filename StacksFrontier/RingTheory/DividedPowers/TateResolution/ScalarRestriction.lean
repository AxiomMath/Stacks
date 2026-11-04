module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-! # Restricting the coefficients of a graded divided power algebra

A grading of an algebra by `R`-submodules is in particular a grading by `S`-submodules for any
subring of scalars `S`, and every structure in this development — the grading, strict graded
commutativity, and the divided powers on the positive even part — depends on the coefficient ring
only through the submodules. Restricting scalars therefore loses nothing.

The two cases used are `S = ℤ`, where the gain is that the `ℤ`-algebra structure of a ring is
unique so that every ring homomorphism is a `ℤ`-algebra homomorphism, and `S = R'` for a
surjection `R' → R`, where the gain is that an `R`-algebra may be read as an `R'`-algebra and so
compared with a lift of it.

This is what makes the one-variable constructions usable at a subring of a graded divided power
algebra: such a subring carries no canonical `R`-algebra structure, and the structure supplied
abstractly with it (for instance by the `successor` field of
`DividedPowers.TateResolution.GradedDividedPowerPolynomial`) need not restrict the ambient one, so
a map out of the subring need not be an `R`-algebra homomorphism. Over `ℤ` the question does not
arise.

## Main definitions

* `DividedPowers.TateResolution.restrictGrade` — a grading by `R`-submodules read as a grading by
  `S`-submodules.
* `DividedPowers.TateResolution.DividedPowerStructure.restrictScalars` — the same divided powers,
  for the restricted grading.

## Main results

* `DividedPowers.TateResolution.mem_positiveEvenPart_restrictGrade` and
  `DividedPowers.TateResolution.mem_evenPart_restrictGrade` — the even and positive even parts are
  unchanged as sets.

## Implementation notes

`Submodule.restrictScalars` preserves the carrier, so membership in `restrictGrade 𝒜 i` is
definitionally membership in `𝒜 i` and the two subtypes are definitionally equal. The grading
transports with no work; only the suprema cutting out the even and positive even parts, which are
formed in different lattices, need an argument.

## References

* [Stacks Project, Tag 09PG](https://stacks.math.columbia.edu/tag/09PG)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

variable {R : Type u} {M : Type v} (S : Type w) [CommRing R] [Ring M] [Algebra R M]
  [CommRing S] [Algebra S M] [Module S R] [IsScalarTower S R M]

/-- A grading by `R`-submodules read as a grading by `S`-submodules. -/
public def restrictGrade (𝒜 : ℕ → Submodule R M) (i : ℕ) : Submodule S M :=
  (𝒜 i).restrictScalars S

/-- Membership in a component of the restricted grading is membership in the original
component. -/
@[simp]
public theorem mem_restrictGrade (𝒜 : ℕ → Submodule R M) (i : ℕ) (x : M) :
    x ∈ restrictGrade S 𝒜 i ↔ x ∈ 𝒜 i := Iff.rfl

/-- Scalar multiplication by a power of `-1` is multiplication by that power of `-1`. -/
private theorem neg_one_pow_smul_eq {T : Type*} [CommRing T] [Algebra T M] (k : ℕ) (z : M) :
    ((-1 : T) ^ k) • z = (-1 : M) ^ k * z := by
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

/-- A graded `R`-algebra is graded as an `S`-algebra by the restricted grading. -/
public noncomputable instance instGradedAlgebraRestrictGrade (𝒜 : ℕ → Submodule R M)
    [GradedAlgebra 𝒜] : GradedAlgebra (restrictGrade S 𝒜) where
  one_mem := SetLike.one_mem_graded 𝒜
  mul_mem := by
    intro i j x y hx hy
    exact SetLike.mul_mem_graded (A := 𝒜) hx hy
  decompose' := DirectSum.decompose 𝒜
  left_inv := DirectSum.Decomposition.left_inv (ℳ := 𝒜)
  right_inv := DirectSum.Decomposition.right_inv (ℳ := 𝒜)

/-- Strict graded commutativity is unchanged by restricting scalars. -/
public instance instIsStrictlyGradedCommRestrictGrade (𝒜 : ℕ → Submodule R M)
    [IsStrictlyGradedComm 𝒜] : IsStrictlyGradedComm (restrictGrade S 𝒜) where
  graded_comm hx hy := by
    rw [IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜) hx hy, neg_one_pow_smul_eq (T := R),
      neg_one_pow_smul_eq (T := S)]
  odd_sq_zero hx := IsStrictlyGradedComm.odd_sq_zero (𝒜 := 𝒜) hx

/-- The positive even part is unchanged by restricting scalars. -/
public theorem mem_positiveEvenPart_restrictGrade (𝒜 : ℕ → Submodule R M) (x : M) :
    x ∈ positiveEvenPart (restrictGrade S 𝒜) ↔ x ∈ positiveEvenPart 𝒜 := by
  exact (SetLike.ext_iff.1 (Submodule.restrictScalars_iSup S fun d => 𝒜 (2 * (d + 1))) x).symm

/-- The even part is unchanged by restricting scalars. -/
public theorem mem_evenPart_restrictGrade (𝒜 : ℕ → Submodule R M) (x : M) :
    x ∈ evenPart (restrictGrade S 𝒜) ↔ x ∈ evenPart 𝒜 := by
  exact (SetLike.ext_iff.1 (Submodule.restrictScalars_iSup S fun d => 𝒜 (2 * d)) x).symm

namespace DividedPowerStructure

/-- The same divided powers, read for the grading restricted to the integers. -/
public def restrictScalars {𝒜 : ℕ → Submodule R M} [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜) :
    DividedPowerStructure (restrictGrade S 𝒜) where
  dpow := γ.dpow
  dpow_null hx := γ.dpow_null fun h =>
    hx ((mem_positiveEvenPart_restrictGrade S 𝒜 _).2 h)
  dpow_zero hx := γ.dpow_zero ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx)
  dpow_one hx := γ.dpow_one ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx)
  dpow_mem hn hx := (mem_positiveEvenPart_restrictGrade S 𝒜 _).2
    (γ.dpow_mem hn ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx))
  dpow_mem_grade hn hx hd := γ.dpow_mem_grade hn
    ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx) hd
  dpow_mul hx := γ.dpow_mul ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx)
  dpow_mul_even hn hx hy := γ.dpow_mul_even hn
    ((mem_evenPart_restrictGrade S 𝒜 _).1 hx)
    ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hy)
  dpow_mul_odd hn hx hy := γ.dpow_mul_odd hn hx hy
  dpow_add hx hy := γ.dpow_add ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx)
    ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hy)
  dpow_dpow hm hn hx := γ.dpow_dpow hm hn
    ((mem_positiveEvenPart_restrictGrade S 𝒜 _).1 hx)

/-- Restricting scalars does not change the divided powers. -/
@[simp]
public theorem restrictScalars_dpow {𝒜 : ℕ → Submodule R M} [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜) :
    (γ.restrictScalars S).dpow = γ.dpow := rfl

end DividedPowerStructure

end DividedPowers.TateResolution

end

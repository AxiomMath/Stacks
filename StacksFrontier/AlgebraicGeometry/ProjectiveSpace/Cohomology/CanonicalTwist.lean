module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of the canonical twist on projective space

Let `R` be a commutative ring and `n ≥ 0`. This file reads off two consequences of Serre's
computation [Stacks, Tag 01XT] at the *canonical* twist `d = -n - 1` and in the range
`-n ≤ d ≤ -1` just above it.

The first is the **trace isomorphism**

`Hⁿ(ℙⁿ_R, 𝒪(-n-1)) ≅ R`,

an `R`-module free of rank one. The top row of [Stacks, Tag 01XT] identifies
`Hⁿ(ℙⁿ_R, 𝒪(d))` with the free `R`-module on the exponent vectors `e : ℤ^{n+1}` that are
negative in every coordinate and sum to `d`. At `d = -n - 1` there are `n + 1` coordinates, each
at most `-1`, summing to `-(n + 1)`, so every coordinate is exactly `-1`: the index set is the
single vector `(-1, …, -1)`, the Laurent monomial `1/(T₀ ⋯ Tₙ)`, and the module is `R`.

The second is the **total acyclicity of the twists strictly between `𝒪(-n-1)` and `𝒪`**:

`H^q(ℙⁿ_R, 𝒪(d)) = 0` for every `q`, whenever `-n ≤ d ≤ -1`.

Here the degree-zero row of [Stacks, Tag 01XT] is empty because `d < 0` and the top-degree row is
empty because there is no vector with `n + 1` negative coordinates summing to `d > -n - 1`; the
remaining degrees vanish outright.

Both statements are what the Stacks project's computation of the twisted inverse image on a
projective bundle, [Stacks, Tag 0A9W], consumes. There `f : 𝐏(ℰ) ⟶ Y` is the projection of a
finite locally free module of rank `n + 1` with determinant `ℒ`, and the asserted isomorphism
`f^*ℒ(-n-1)[n] ≅ a(𝒪_Y)` is tested against the generators `𝒪, 𝒪(-1), …, 𝒪(-n)` of
`D_{QCoh}(𝒪_{𝐏(ℰ)})`: the trace isomorphism is what makes `Rf_*(f^*ℒ(-n-1))[n] ≅ 𝒪_Y`, and the
acyclicity is what makes the comparison vacuous on the remaining generators.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.negativeTwistPartCanonicalEquiv` — the monomial model of
  `Hⁿ(ℙⁿ_R, 𝒪(-n-1))` is `R`.
* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyCanonicalIsoCoeff` —
  **`Hⁿ(ℙⁿ_R, 𝒪(-n-1)) ≅ R`**, as modules over the coefficients.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomials_canonical` — at `d = -n - 1` the
  degree-`d` Laurent monomials with every exponent negative are the single monomial
  `1/(T₀ ⋯ Tₙ)`.
* `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_canonical` —
  **`H^q(ℙⁿ_R, 𝒪(-n-1)) = 0` for `q ≠ n`**, so the cohomology of the canonical twist is
  concentrated in the top degree.
* `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_neg_le` —
  **`H^q(ℙⁿ_R, 𝒪(d)) = 0` for every `q`, when `-n ≤ d ≤ -1`.**

## Implementation notes

No `@[stacks]` attribute is attached to anything in this file. Every statement below is a
specialization of [Stacks, Tag 01XT] to one value or one range of the twist, and the covering set
of that tag is already registered, on
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoHomogeneous`,
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoNegative`,
`Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology` and
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyMonomial` in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/TwistCohomologyMonomial.lean`. Nothing
here is a new reading of the source.

The two non-vanishing rows of [Stacks, Tag 01XT] overlap at `n = 0`, and so do the two sides of
this file: for `n = 0` the canonical twist is `𝒪(-1)` and the trace isomorphism says
`H⁰(ℙ⁰_R, 𝒪(-1)) ≅ R`, while the acyclicity range `-0 ≤ d ≤ -1` is empty. No case split on `n` is
needed for either, because the general top-degree row
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoNegative` already covers `n = 0`.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### The single negative Laurent monomial in the canonical degree -/

/-- The sum of `n + 1` copies of `-1` is `-n - 1`. -/
private theorem sum_const_neg_one (n : ℕ) : ∑ _j : Fin (n + 1), (-1 : ℤ) = -(n : ℤ) - 1 := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- **The Laurent monomial `1/(T₀ ⋯ Tₙ)` has every exponent negative and total degree `-n-1`.** -/
theorem mem_negativeLaurentMonomials_canonical (n : ℕ) :
    (fun _ => (-1 : ℤ)) ∈ negativeLaurentMonomials n (-(n : ℤ) - 1) := by
  exact (mem_negativeLaurentMonomials).2 ⟨sum_const_neg_one n, fun _ => by norm_num⟩

/-- **In the canonical degree `d = -n - 1` there is exactly one degree-`d` Laurent monomial with
every exponent negative**, namely `1/(T₀ ⋯ Tₙ)`. The `n + 1` exponents are each at most `-1` and
sum to `-(n + 1)`, so none of them can be smaller than `-1`. -/
theorem negativeLaurentMonomials_canonical (n : ℕ) :
    negativeLaurentMonomials n (-(n : ℤ) - 1) = {fun _ => (-1 : ℤ)} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_negativeLaurentMonomials_canonical n, ?_⟩
  rintro e he
  obtain ⟨hsum, hneg⟩ := (mem_negativeLaurentMonomials).1 he
  funext i
  by_contra hi
  have hlt : e i < -1 := by have := hneg i; omega
  have hsum' : (∑ j, e j) < ∑ _j : Fin (n + 1), (-1 : ℤ) :=
    Finset.sum_lt_sum (fun j _ => by have := hneg j; omega) ⟨i, Finset.mem_univ i, hlt⟩
  rw [hsum, sum_const_neg_one] at hsum'
  omega

/-- The index set of the top-degree cohomology of the canonical twist is a subsingleton. -/
theorem subsingleton_negativeLaurentMonomials_canonical (n : ℕ) :
    Subsingleton ↥(negativeLaurentMonomials n (-(n : ℤ) - 1)) := by
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  rw [negativeLaurentMonomials_canonical] at ha hb
  exact Subtype.ext (ha.trans hb.symm)

/-! ### The trace isomorphism -/

/-- **The monomial model of `Hⁿ(ℙⁿ_R, 𝒪(-n-1))` is `R`**: it is the free `R`-module on the
degree-`(-n-1)` Laurent monomials with every exponent negative, and there is exactly one of
those. -/
def negativeTwistPartCanonicalEquiv (R : Type u) [CommRing R] (n : ℕ) :
    negativeTwistPart R n (-(n : ℤ) - 1) ≃ₗ[R] R :=
  letI := subsingleton_negativeLaurentMonomials_canonical n
  (negativeTwistPartEquivFinsupp R n (-(n : ℤ) - 1)).trans
    (Finsupp.uniqueLinearEquiv R R
      (⟨_, mem_negativeLaurentMonomials_canonical n⟩ :
        ↥(negativeLaurentMonomials n (-(n : ℤ) - 1))))

/-- **The trace isomorphism `Hⁿ(ℙⁿ_R, 𝒪(-n-1)) ≅ R`.** The top cohomology of the canonical twist
on projective `n`-space is free of rank one over the coefficients, generated by the Laurent
monomial `1/(T₀ ⋯ Tₙ)`. This is the top-degree row of [Stacks, Tag 01XT] at `d = -n - 1`, where
the index set of negative exponent vectors collapses to a single element. -/
def twistCohomologyCanonicalIsoCoeff (R : Type u) [CommRing R] (n : ℕ) :
    twistCohomology R n (-(n : ℤ) - 1) n ≅ ModuleCat.of R R :=
  twistCohomologyIsoNegative R n (-(n : ℤ) - 1) (by omega) ≪≫
    LinearEquiv.toModuleIso (negativeTwistPartCanonicalEquiv R n)

/-- The cohomology of a negative twist vanishes in every degree `q ≠ n`. -/
private theorem isZero_twistCohomology_of_neg_of_ne (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (hd : d < 0) (q : ℕ) (hq : q ≠ n) : IsZero (twistCohomology R n d q) :=
  isZero_twistCohomology R n d q (by
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · omega
    · exact hq h)

/-- **The cohomology of the canonical twist is concentrated in the top degree**:
`H^q(ℙⁿ_R, 𝒪(-n-1)) = 0` for every `q ≠ n`. Together with
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyCanonicalIsoCoeff` this says that
`Rπ_*𝒪(-n-1)[n] ≅ 𝒪` for the structure morphism `π : ℙⁿ_R ⟶ Spec R`. -/
@[ega "III 2.1.12" "(i), special case"]
theorem isZero_twistCohomology_canonical (R : Type u) [CommRing R] (n : ℕ) (q : ℕ) (hq : q ≠ n) :
    IsZero (twistCohomology R n (-(n : ℤ) - 1) q) :=
  isZero_twistCohomology_of_neg_of_ne R n _ (by omega) q hq

/-! ### Acyclicity just above the canonical twist -/

/-- **The twists `𝒪(-1), …, 𝒪(-n)` on `ℙⁿ_R` have no cohomology at all**: if `-n ≤ d` and
`d < 0` then `H^q(ℙⁿ_R, 𝒪(d)) = 0` for every `q`.

In the degree `q = n` this is the vanishing of the module on the negative Laurent monomials,
`Stacks.ProjectiveSpace.Cohomology.negativeTwistPart_eq_bot_of_le`: there is no exponent vector
with `n + 1` coordinates, each at most `-1`, summing to a `d` greater than `-n - 1`. In every
other degree it is the vanishing row of [Stacks, Tag 01XT], the degree-zero case being covered
because `d` is negative. -/
@[sga "7 XXII 6.2" "(6.2.4), special case"]
theorem isZero_twistCohomology_of_neg_le (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (hd₁ : -(n : ℤ) ≤ d) (hd₂ : d < 0) (q : ℕ) :
    IsZero (twistCohomology R n d q) := by
  by_cases hq : q = n
  · subst hq
    refine (twistCohomologyIsoNegative R q d hd₂).isZero_iff.2 ?_
    have : Subsingleton (negativeTwistPart R q d) := by
      rw [negativeTwistPart_eq_bot_of_le R q d hd₁]
      infer_instance
    exact ModuleCat.isZero_of_subsingleton _
  · exact isZero_twistCohomology_of_neg_of_ne R n d hd₂ q hq

end Stacks.ProjectiveSpace.Cohomology

end

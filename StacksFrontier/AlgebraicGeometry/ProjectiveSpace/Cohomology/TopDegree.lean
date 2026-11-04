module

public import Mathlib.LinearAlgebra.Projection
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLine

/-!
# The extreme Čech cohomology of `𝒪(d)` on projective space

Projective `n`-space over a ring `R` is covered by the `n + 1` standard opens `D₊(T₀), …,
D₊(Tₙ)`, and the ordered Čech complex of that cover for the twist `𝒪(d)` has a single term in
its top degree `n`, namely the sections over the total intersection `D₊(T₀ ⋯ Tₙ)`, and one term
for each `i` in degree `n - 1`, namely the sections over `D₊(∏_{j ≠ i} Tⱼ)`. On the monomial
charts of `Stacks.ProjectiveSpace.Cohomology.twistChart` the degree-`(n-1)` term attached to `i`
is the chart inverting every variable but `Tᵢ`, i.e. the chart of `{i}ᶜ`, and the top term is the
chart of `Set.univ`. This file computes the resulting cokernel for every `n` and every `d`, and
likewise the kernel of the degree-zero differential of that cover.

A degree-`d` Laurent monomial `T₀^{e₀} ⋯ Tₙ^{eₙ}` either has some exponent `eᵢ ≥ 0`, in which
case it is allowed in the chart of `{i}ᶜ`, or has every exponent negative. The monomials of the
first kind span the image of the top Čech differential and the monomials of the second kind span
a complement of that image inside the chart of `Set.univ`. Since `∑ eᵢ = d` and every exponent
is at most `-1`, monomials of the second kind exist exactly when `d ≤ -n - 1`; equivalently the
cokernel vanishes exactly when `-n ≤ d`, and in particular for every `d ≥ 0`.

This generalises to every `n` the two-chart computation of
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLine`, which is the case
`n = 1`: `negativeTwistPart R 1 d` is `lineNegativePart R d` and the image of `topCechDiff R 1 d`
is the image of `lineCechDiff R d`, both proved here.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomials` — the exponent vectors of total
  degree `d` all of whose entries are negative.
* `Stacks.ProjectiveSpace.Cohomology.negativeTwistPart` — the free `R`-module on those.
* `Stacks.ProjectiveSpace.Cohomology.topCechDiff` — the top-degree Čech differential of the
  standard cover, `s ↦ ∑ᵢ (-1)ⁱ sᵢ`.
* `Stacks.ProjectiveSpace.Cohomology.topCechCohomologyEquiv` — the cokernel of that
  differential, as a module.
* `Stacks.ProjectiveSpace.Cohomology.degreeZeroCechDiff` — the degree-zero Čech differential of
  the standard cover, `s ↦ (sⱼ - sᵢ)_{i < j}`.
* `Stacks.ProjectiveSpace.Cohomology.diagonalCocycle` — a polynomial section read as a
  degree-zero Čech cocycle.
* `Stacks.ProjectiveSpace.Cohomology.degreeZeroCechCohomologyEquiv` — the kernel of the
  degree-zero differential, as a module.

## Main results

* `range_topCechDiff` — the image of the top Čech differential is the join of the charts of the
  complements of the singletons.
* `topCechDiff_sup_negativeTwistPart` and `topCechDiff_disjoint_negativeTwistPart` —
  `negativeTwistPart` is a complement of that image inside the chart of `Set.univ`; hence
  `isCompl_negativeTwistPart` and `topCechCohomologyEquiv`.
* `negativeTwistPartEquivFinsupp` — the cokernel is free on the degree-`d` Laurent monomials
  with every exponent negative.
* `negativeLaurentMonomials_eq_empty_iff`, `negativeTwistPart_eq_bot_of_le`,
  `negativeTwistPart_eq_bot_of_nonneg` and `topCechDiff_range_eq_twistChart_univ` — the
  top-degree Čech cohomology vanishes exactly when `-n ≤ d`, so in particular for `0 ≤ d`.
* `range_diagonalCocycle` and `degreeZeroCechCohomologyEquiv` — for `0 < n` the degree-zero Čech
  cocycles are exactly the polynomial sections, so the degree-zero Čech cohomology is the chart
  of `∅`.
* `ker_degreeZeroCechDiff_eq_bot` and `iInf_twistChart_singleton_eq_bot` — for `0 < n` and
  `d < 0` the degree-zero Čech cohomology vanishes.
* `not_strictMono_fin_of_lt` — above degree `n` the ordered Čech complex of a cover by `n + 1`
  opens has no index tuples at all.

## Implementation notes

The image of the differential is computed rather than assumed: `topCechDiff` carries the Čech
signs `(-1)ⁱ`, and `range_topCechDiff` identifies its image with the join `⨆ i, twistChart R n d
{i}ᶜ` because each sign is a unit, so no sign bookkeeping enters the computation of the
cokernel.

The complement is exhibited by the pair `topCechDiff_sup_negativeTwistPart` and
`topCechDiff_disjoint_negativeTwistPart`, in the same shape as the two `ℙ¹` results it
generalises, and `isCompl_negativeTwistPart` is the resulting `IsCompl` inside the chart of
`Set.univ`, obtained by pulling both submodules back along the inclusion of that chart.

No `@[stacks]` attribute is attached. The computation of `Hᵠ(ℙⁿ_R, 𝒪(d))` is Tag 01XT, whose
covering set needs, besides the monomial computation carried out here, the identification of the
Čech complex of the standard cover with these charts for every `n` — available at the pin only
for `n = 1`, in
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CechComparison.OverlapRestriction` — and the
comparison of Čech with derived cohomology, Tag 01XD.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ}

section Monomials

/-- The exponent vectors of a Laurent monomial in `T₀, …, Tₙ` of total degree `d` all of whose
entries are negative. These index the top-degree Čech cohomology of the standard cover. -/
def negativeLaurentMonomials (n : ℕ) (d : ℤ) : Set (Fin (n + 1) → ℤ) :=
  {e | (∑ i, e i) = d ∧ ∀ i, e i < 0}

/-- An exponent vector lies in `negativeLaurentMonomials n d` exactly when its entries sum to `d`
and are all negative. -/
@[simp]
theorem mem_negativeLaurentMonomials {e : Fin (n + 1) → ℤ} :
    e ∈ negativeLaurentMonomials n d ↔ (∑ i, e i) = d ∧ ∀ i, e i < 0 :=
  Iff.rfl

/-- A monomial with every exponent negative has total degree `d`, so it is a Laurent monomial
of the chart inverting every variable. -/
theorem negativeLaurentMonomials_subset_univ (n : ℕ) (d : ℤ) :
    negativeLaurentMonomials n d ⊆ laurentMonomials n d (Set.univ : Set (Fin (n + 1))) :=
  fun _ he => ⟨he.1, fun i hi => absurd (Set.mem_univ i) hi⟩

/-- The chart inverting every variable but `Tᵢ` allows exactly the degree-`d` Laurent monomials
whose exponent at `i` is nonnegative. -/
theorem laurentMonomials_compl_singleton (n : ℕ) (d : ℤ) (i : Fin (n + 1)) :
    laurentMonomials n d ({i}ᶜ : Set (Fin (n + 1))) =
      {e : Fin (n + 1) → ℤ | (∑ j, e j) = d ∧ 0 ≤ e i} := by
  ext e
  simp only [mem_laurentMonomials, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
    not_not]
  refine ⟨fun h => ⟨h.1, h.2 i rfl⟩, fun h => ⟨h.1, fun j hj => ?_⟩⟩
  subst hj
  exact h.2

/-- **Every degree-`d` Laurent monomial is either regular along some variable or has every
exponent negative.** This is the decomposition of the top term of the Čech complex which
computes the top-degree cohomology of `𝒪(d)`. -/
theorem laurentMonomials_univ_eq_union (n : ℕ) (d : ℤ) :
    laurentMonomials n d (Set.univ : Set (Fin (n + 1))) =
      (⋃ i, laurentMonomials n d ({i}ᶜ : Set (Fin (n + 1)))) ∪ negativeLaurentMonomials n d := by
  ext e
  simp only [laurentMonomials_univ, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion,
    laurentMonomials_compl_singleton, mem_negativeLaurentMonomials]
  refine ⟨fun he => ?_, ?_⟩
  · rcases forall_or_exists_not (fun i => e i < 0) with h | ⟨i, hi⟩
    · exact Or.inr ⟨he, h⟩
    · exact Or.inl ⟨i, he, not_lt.1 hi⟩
  · rintro (⟨_, hi, _⟩ | ⟨hsum, _⟩)
    · exact hi
    · exact hsum

/-- A monomial with every exponent negative lies in no chart of the complement of a
singleton. -/
theorem disjoint_negativeLaurentMonomials (n : ℕ) (d : ℤ) :
    Disjoint (⋃ i, laurentMonomials n d ({i}ᶜ : Set (Fin (n + 1))))
      (negativeLaurentMonomials n d) := by
  rw [Set.disjoint_left]
  rintro e he hneg
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
  rw [laurentMonomials_compl_singleton] at hi
  exact absurd hi.2 (not_le.2 (hneg.2 i))

/-- **There is a degree-`d` Laurent monomial in `n + 1` variables with every exponent negative
exactly when `d ≤ -n - 1`.** Both directions are the inequality `∑ eᵢ ≤ -(n + 1)` for exponents
at most `-1`; the extremal monomial is `T₀^{d + n} T₁^{-1} ⋯ Tₙ^{-1}`. -/
theorem negativeLaurentMonomials_eq_empty_iff (n : ℕ) (d : ℤ) :
    negativeLaurentMonomials n d = ∅ ↔ -(n : ℤ) ≤ d := by
  refine ⟨fun h => ?_, fun hd => Set.eq_empty_iff_forall_notMem.2 fun e he => ?_⟩
  · by_contra hd
    rw [not_le] at hd
    refine Set.eq_empty_iff_forall_notMem.1 h
      (Function.update (fun _ => (-1 : ℤ)) 0 (d + n)) ⟨?_, fun i => ?_⟩
    · have hc : ((Finset.univ : Finset (Fin (n + 1))) \ {0}).card = n := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ 0),
          Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
      rw [Finset.sum_update_of_mem (Finset.mem_univ 0), Finset.sum_const, hc, nsmul_eq_mul]
      ring
    · rcases eq_or_ne i 0 with hi | hi
      · subst hi; simpa using by omega
      · simp only [Function.update_of_ne hi]
        omega
  · have hle : (∑ i, e i) ≤ ∑ _i : Fin (n + 1), (-1 : ℤ) :=
      Finset.sum_le_sum fun i _ => by have := he.2 i; omega
    rw [he.1, Finset.sum_const, nsmul_eq_mul] at hle
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hle
    omega

/-- **Above degree `n` the ordered Čech complex of a cover by `n + 1` opens has no terms**: there
is no strictly increasing tuple of length `q + 1 > n + 1` in `Fin (n + 1)`. -/
theorem not_strictMono_fin_of_lt {q : ℕ} (hq : n < q) (i : Fin (q + 1) → Fin (n + 1)) :
    ¬ StrictMono i := fun hi => by
  have h := Fintype.card_le_of_injective i hi.injective
  simp only [Fintype.card_fin] at h
  omega

end Monomials

section Charts

variable (R n d)

/-- The free `R`-module on the degree-`d` Laurent monomials with every exponent negative. It is
a complement inside the chart of `Set.univ` to the image of the top-degree Čech differential,
hence computes `Hⁿ(ℙⁿ_R, 𝒪(d))`. -/
def negativeTwistPart (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Submodule R ((Fin (n + 1) → ℤ) →₀ R) :=
  Finsupp.supported R R (negativeLaurentMonomials n d)

/-- `negativeTwistPart R n d` is contained in the chart of `Set.univ`. -/
theorem negativeTwistPart_le_twistChart_univ :
    negativeTwistPart R n d ≤ twistChart R n d (Set.univ : Set (Fin (n + 1))) :=
  Finsupp.supported_mono (negativeLaurentMonomials_subset_univ n d)

/-- **The top-degree Čech differential of the standard cover of `ℙⁿ_R`.** A family of sections of
`𝒪(d)`, one on each `D₊(∏_{j ≠ i} Tⱼ)`, is sent to the alternating sum `∑ᵢ (-1)ⁱ sᵢ` of their
restrictions to the total intersection `D₊(T₀ ⋯ Tₙ)`. -/
def topCechDiff (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    (∀ i : Fin (n + 1), twistChart R n d ({i}ᶜ : Set (Fin (n + 1)))) →ₗ[R]
      ((Fin (n + 1) → ℤ) →₀ R) :=
  ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ)) •
    ((twistChart R n d ({i}ᶜ : Set (Fin (n + 1)))).subtype ∘ₗ LinearMap.proj i)

/-- `topCechDiff R n d` sends `s` to the alternating sum `∑ᵢ (-1)ⁱ sᵢ`. -/
@[simp]
theorem topCechDiff_apply
    (s : ∀ i : Fin (n + 1), twistChart R n d ({i}ᶜ : Set (Fin (n + 1)))) :
    topCechDiff R n d s =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ)) • (s i : (Fin (n + 1) → ℤ) →₀ R) := by
  simp [topCechDiff]

/-- **The image of the top Čech differential is the join of the charts of the complements of the
singletons.** The Čech signs are units, so they do not restrict the image. -/
theorem range_topCechDiff :
    LinearMap.range (topCechDiff R n d) =
      ⨆ i, twistChart R n d ({i}ᶜ : Set (Fin (n + 1))) := by
  refine le_antisymm ?_ (iSup_le fun i x hx => ?_)
  · rintro x ⟨s, rfl⟩
    rw [topCechDiff_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (le_iSup (fun j => twistChart R n d ({j}ᶜ : Set (Fin (n + 1)))) i (s i).2)
  · refine ⟨Pi.single i ⟨((-1 : R) ^ (i : ℕ)) • x, Submodule.smul_mem _ _ hx⟩, ?_⟩
    rw [topCechDiff_apply, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj]; simp) (fun h => absurd (Finset.mem_univ i) h)]
    rw [Pi.single_eq_same]
    change ((-1 : R) ^ (i : ℕ)) • (((-1 : R) ^ (i : ℕ)) • x) = x
    rw [smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]

/-- The image of the top Čech differential is the module supported on the monomials of the
charts of the complements of the singletons. -/
private theorem range_topCechDiff_eq_supported :
    LinearMap.range (topCechDiff R n d) = Finsupp.supported R R
      (⋃ i, laurentMonomials n d ({i}ᶜ : Set (Fin (n + 1)))) := by
  rw [range_topCechDiff, Finsupp.supported_iUnion]
  rfl

/-- The image of the top Čech differential is contained in the chart of `Set.univ`. -/
theorem range_topCechDiff_le_twistChart_univ :
    LinearMap.range (topCechDiff R n d) ≤
      twistChart R n d (Set.univ : Set (Fin (n + 1))) := by
  rw [range_topCechDiff]
  exact iSup_le fun i => twistChart_mono (Set.subset_univ _)

/-- **The image of the top Čech differential and `negativeTwistPart` together exhaust the chart
of `Set.univ`.** -/
theorem topCechDiff_sup_negativeTwistPart :
    LinearMap.range (topCechDiff R n d) ⊔ negativeTwistPart R n d =
      twistChart R n d (Set.univ : Set (Fin (n + 1))) := by
  rw [range_topCechDiff_eq_supported, negativeTwistPart, twistChart,
    ← Finsupp.supported_union, ← laurentMonomials_univ_eq_union]

/-- **The image of the top Čech differential and `negativeTwistPart` meet in zero.** With
`topCechDiff_sup_negativeTwistPart` this exhibits `negativeTwistPart` as a complement of the
image inside the chart of `Set.univ`. -/
theorem topCechDiff_disjoint_negativeTwistPart :
    Disjoint (LinearMap.range (topCechDiff R n d)) (negativeTwistPart R n d) := by
  rw [range_topCechDiff_eq_supported]
  exact Finsupp.disjoint_supported_supported (disjoint_negativeLaurentMonomials n d)

/-- The module on the negative monomials vanishes as soon as `-n ≤ d`, in particular for every
`d ≥ 0`: the top-degree Čech cohomology of `𝒪(d)` on `ℙⁿ_R` then vanishes. -/
theorem negativeTwistPart_eq_bot_of_le (hd : -(n : ℤ) ≤ d) :
    negativeTwistPart R n d = ⊥ := by
  rw [negativeTwistPart, (negativeLaurentMonomials_eq_empty_iff n d).2 hd,
    Finsupp.supported_empty]

/-- The module on the negative monomials vanishes for every nonnegative twist. -/
theorem negativeTwistPart_eq_bot_of_nonneg (hd : 0 ≤ d) :
    negativeTwistPart R n d = ⊥ :=
  negativeTwistPart_eq_bot_of_le R n d (le_trans (by omega) hd)

/-- **The top-degree Čech differential is onto for `-n ≤ d`.** Every degree-`d` Laurent section
on `D₊(T₀ ⋯ Tₙ)` is then an alternating sum of sections regular along one variable. -/
theorem topCechDiff_range_eq_twistChart_univ (hd : -(n : ℤ) ≤ d) :
    LinearMap.range (topCechDiff R n d) =
      twistChart R n d (Set.univ : Set (Fin (n + 1))) := by
  rw [← topCechDiff_sup_negativeTwistPart R n d, negativeTwistPart_eq_bot_of_le R n d hd,
    sup_bot_eq]

/-- The top-degree Čech cohomology vanishes exactly when `-n ≤ d`. -/
theorem negativeTwistPart_eq_bot_iff [Nontrivial R] :
    negativeTwistPart R n d = ⊥ ↔ -(n : ℤ) ≤ d := by
  refine ⟨fun h => ?_, negativeTwistPart_eq_bot_of_le R n d⟩
  rw [← negativeLaurentMonomials_eq_empty_iff n d]
  refine Set.eq_empty_iff_forall_notMem.2 fun e he => ?_
  have h1 : Finsupp.single e (1 : R) ∈ negativeTwistPart R n d :=
    Finsupp.single_mem_supported R 1 he
  rw [h, Submodule.mem_bot, Finsupp.single_eq_zero] at h1
  exact one_ne_zero h1

/-- **`negativeTwistPart` is a complement of the image of the top Čech differential inside the
chart of `Set.univ`**, both pulled back along the inclusion of that chart. -/
theorem isCompl_negativeTwistPart :
    IsCompl
      ((LinearMap.range (topCechDiff R n d)).comap
        (twistChart R n d (Set.univ : Set (Fin (n + 1)))).subtype)
      ((negativeTwistPart R n d).comap
        (twistChart R n d (Set.univ : Set (Fin (n + 1)))).subtype) := by
  constructor
  · rw [_root_.disjoint_iff, ← Submodule.comap_inf,
      _root_.disjoint_iff.1 (topCechDiff_disjoint_negativeTwistPart R n d),
      Submodule.comap_bot, Submodule.ker_subtype]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : (x : (Fin (n + 1) → ℤ) →₀ R) ∈
        LinearMap.range (topCechDiff R n d) ⊔ negativeTwistPart R n d := by
      rw [topCechDiff_sup_negativeTwistPart]
      exact x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
    refine Submodule.mem_sup.2
      ⟨⟨y, range_topCechDiff_le_twistChart_univ R n d hy⟩, hy,
        ⟨z, negativeTwistPart_le_twistChart_univ R n d hz⟩, hz, Subtype.ext hyz⟩

/-- **The top-degree Čech cohomology of `𝒪(d)` on `ℙⁿ_R`, in the monomial model.** The cokernel
of the top Čech differential is the free `R`-module on the degree-`d` Laurent monomials with
every exponent negative. -/
def topCechCohomologyEquiv :
    (↥(twistChart R n d (Set.univ : Set (Fin (n + 1)))) ⧸
        (LinearMap.range (topCechDiff R n d)).comap
          (twistChart R n d (Set.univ : Set (Fin (n + 1)))).subtype) ≃ₗ[R]
      negativeTwistPart R n d :=
  (Submodule.quotientEquivOfIsCompl _ _ (isCompl_negativeTwistPart R n d)).trans
    (Submodule.comapSubtypeEquivOfLe (negativeTwistPart_le_twistChart_univ R n d))

/-- **The top-degree Čech cohomology is free on the negative Laurent monomials.** -/
def negativeTwistPartEquivFinsupp :
    negativeTwistPart R n d ≃ₗ[R] (negativeLaurentMonomials n d →₀ R) :=
  Finsupp.supportedEquivFinsupp _

/-- **The degree-zero Čech cocycles of the standard cover vanish for a negative twist**, as soon
as `n > 0`: a Laurent section regular on every `D₊(Tᵢ)` is a polynomial section, and there is no
polynomial section in negative degree. -/
theorem iInf_twistChart_singleton_eq_bot (hn : 0 < n) (hd : d < 0) :
    ⨅ i : Fin (n + 1), twistChart R n d {i} = ⊥ := by
  rw [twistChart_iInf_singleton n hn d, twistChart_eq_bot_of_neg n hd]

/-- The degree-zero Čech differential of the standard cover of `ℙⁿ_R`: a family of sections of
`𝒪(d)`, one on each `D₊(Tᵢ)`, is sent to the family of differences `sⱼ - sᵢ` on the overlaps
`D₊(Tᵢ Tⱼ)`, indexed by the increasing pairs `i < j`. -/
def degreeZeroCechDiff (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    (∀ i : Fin (n + 1), twistChart R n d {i}) →ₗ[R]
      ({p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2} → ((Fin (n + 1) → ℤ) →₀ R)) :=
  LinearMap.pi fun p =>
    (twistChart R n d {p.val.2}).subtype ∘ₗ LinearMap.proj p.val.2 -
      (twistChart R n d {p.val.1}).subtype ∘ₗ LinearMap.proj p.val.1

/-- The component of `degreeZeroCechDiff R n d s` at the pair `i < j` is `sⱼ - sᵢ`. -/
@[simp]
theorem degreeZeroCechDiff_apply (s : ∀ i : Fin (n + 1), twistChart R n d {i})
    (p : {p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2}) :
    degreeZeroCechDiff R n d s p =
      (s p.val.2 : (Fin (n + 1) → ℤ) →₀ R) - (s p.val.1 : (Fin (n + 1) → ℤ) →₀ R) :=
  rfl

/-- A degree-`d` polynomial section, read as a Čech cocycle: the same section on every standard
open. Its image is the kernel of the degree-zero Čech differential. -/
def diagonalCocycle (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    twistChart R n d (∅ : Set (Fin (n + 1))) →ₗ[R]
      (∀ i : Fin (n + 1), twistChart R n d {i}) :=
  LinearMap.pi fun _ =>
    LinearMap.codRestrict _ (twistChart R n d (∅ : Set (Fin (n + 1)))).subtype
      fun z => twistChart_mono (Set.empty_subset _) z.2

/-- Every component of `diagonalCocycle R n d z` is the section `z`. -/
@[simp]
theorem diagonalCocycle_apply_coe (z : twistChart R n d (∅ : Set (Fin (n + 1))))
    (i : Fin (n + 1)) :
    ((diagonalCocycle R n d z i : twistChart R n d {i}) : (Fin (n + 1) → ℤ) →₀ R) =
      (z : (Fin (n + 1) → ℤ) →₀ R) :=
  rfl

/-- The map `diagonalCocycle R n d` is injective. -/
theorem diagonalCocycle_injective : Function.Injective (diagonalCocycle R n d) := fun x y h =>
  Subtype.ext (by
    simpa using congrArg
      (fun w => ((w 0 : twistChart R n d {(0 : Fin (n + 1))}) : (Fin (n + 1) → ℤ) →₀ R)) h)

/-- **The degree-zero Čech cocycles of the standard cover are the polynomial sections**, for
`0 < n`: a family of Laurent sections agreeing on every overlap has one common value, which is
then allowed in every one-variable chart and so has all exponents nonnegative. -/
theorem range_diagonalCocycle (hn : 0 < n) :
    LinearMap.range (diagonalCocycle R n d) = LinearMap.ker (degreeZeroCechDiff R n d) := by
  refine le_antisymm ?_ fun s hs => ?_
  · rintro _ ⟨z, rfl⟩
    refine LinearMap.mem_ker.2 (funext fun p => ?_)
    rw [degreeZeroCechDiff_apply, diagonalCocycle_apply_coe, diagonalCocycle_apply_coe, sub_self]
    rfl
  · have hconst : ∀ i : Fin (n + 1),
        (s i : (Fin (n + 1) → ℤ) →₀ R) = (s 0 : (Fin (n + 1) → ℤ) →₀ R) := by
      intro i
      rcases lt_trichotomy (0 : Fin (n + 1)) i with h | h | h
      · simpa [sub_eq_zero] using congrFun (LinearMap.mem_ker.1 hs) ⟨(0, i), h⟩
      · rw [h]
      · simpa [sub_eq_zero, eq_comm] using congrFun (LinearMap.mem_ker.1 hs) ⟨(i, 0), h⟩
    have hmem : (s 0 : (Fin (n + 1) → ℤ) →₀ R) ∈
        twistChart R n d (∅ : Set (Fin (n + 1))) := by
      rw [← twistChart_iInf_singleton n hn d]
      exact Submodule.mem_iInf _ |>.2 fun i => by rw [← hconst i]; exact (s i).2
    exact ⟨⟨_, hmem⟩, funext fun i => Subtype.ext (hconst i).symm⟩

/-- **The degree-zero Čech cohomology of the standard cover of `ℙⁿ_R` is the polynomial chart**,
for `0 < n`. Composing with `Stacks.ProjectiveSpace.Cohomology.twistChartEmptyLinearEquiv`
identifies it with the degree-`d` homogeneous polynomials in `T₀, …, Tₙ` when `0 ≤ d`. -/
def degreeZeroCechCohomologyEquiv (hn : 0 < n) :
    twistChart R n d (∅ : Set (Fin (n + 1))) ≃ₗ[R]
      LinearMap.ker (degreeZeroCechDiff R n d) :=
  (LinearEquiv.ofInjective (diagonalCocycle R n d) (diagonalCocycle_injective R n d)).trans
    (LinearEquiv.ofEq _ _ (range_diagonalCocycle R n d hn))

/-- **The degree-zero Čech cohomology of the standard cover vanishes for a negative twist**, as
soon as `0 < n`. -/
theorem ker_degreeZeroCechDiff_eq_bot (hn : 0 < n) (hd : d < 0) :
    LinearMap.ker (degreeZeroCechDiff R n d) = ⊥ := by
  rw [← range_diagonalCocycle R n d hn, LinearMap.range_eq_bot]
  refine LinearMap.ext fun z => funext fun i => Subtype.ext ?_
  have hz : (z : (Fin (n + 1) → ℤ) →₀ R) = 0 :=
    (Submodule.eq_bot_iff _).1 (twistChart_eq_bot_of_neg n hd) _ z.2
  simp [hz]

end Charts

section ProjectiveLine

/-- The degree-`d` Laurent monomials of the projective line with both exponents negative are the
negative monomials in two variables: the `n = 1` case of `negativeLaurentMonomials`. -/
theorem lineNegativeMonomials_eq (d : ℤ) :
    lineNegativeMonomials d = negativeLaurentMonomials 1 d := by
  ext e
  rw [mem_negativeLaurentMonomials, Fin.sum_univ_two, Fin.forall_fin_two]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- `Stacks.ProjectiveSpace.Cohomology.lineNegativePart` is the `n = 1` case of
`negativeTwistPart`. -/
theorem lineNegativePart_eq (R : Type u) [CommRing R] (d : ℤ) :
    lineNegativePart R d = negativeTwistPart R 1 d := by
  rw [lineNegativePart, negativeTwistPart, lineNegativeMonomials_eq]

/-- The image of the top Čech differential of the two-chart cover of the projective line is the
image of `Stacks.ProjectiveSpace.Cohomology.lineCechDiff`: the `n = 1` case of
`range_topCechDiff`. -/
theorem range_topCechDiff_fin_two (R : Type u) [CommRing R] (d : ℤ) :
    LinearMap.range (topCechDiff R 1 d) = LinearMap.range (lineCechDiff R d) := by
  rw [range_topCechDiff, range_lineCechDiff]
  have h0 : ({(0 : Fin 2)}ᶜ : Set (Fin 2)) = {1} := by
    ext i; fin_cases i <;> simp
  have h1 : ({(1 : Fin 2)}ᶜ : Set (Fin 2)) = {0} := by
    ext i; fin_cases i <;> simp
  refine le_antisymm (iSup_le ?_) (sup_le ?_ ?_)
  · rw [Fin.forall_fin_two]
    exact ⟨by rw [h0]; exact le_sup_right, by rw [h1]; exact le_sup_left⟩
  · rw [← h1]
    exact le_iSup (fun i : Fin 2 => twistChart R 1 d ({i}ᶜ : Set (Fin 2))) 1
  · rw [← h0]
    exact le_iSup (fun i : Fin 2 => twistChart R 1 d ({i}ᶜ : Set (Fin 2))) 0

end ProjectiveLine

end Stacks.ProjectiveSpace.Cohomology

end

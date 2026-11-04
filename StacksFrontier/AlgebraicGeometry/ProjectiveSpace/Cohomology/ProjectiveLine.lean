module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentCharts

/-!
# The Čech computation of the cohomology of `𝒪(d)` on the projective line

The projective line `ℙ¹_R` is covered by the two standard opens `D₊(T₀)` and `D₊(T₁)`, whose
intersection is `D₊(T₀T₁)`. The Čech complex of that cover for the twist `𝒪(d)` is therefore
the two-term complex

`(R[T₀, T₁][1/T₀])_d ⊕ (R[T₀, T₁][1/T₁])_d ⟶ (R[T₀, T₁][1/T₀T₁])_d`,  `(a, b) ↦ a - b`,

whose kernel computes `H⁰` and whose cokernel computes `H¹`. On the monomial charts of
`Stacks.ProjectiveSpace.Cohomology.twistChart` this file computes both.

A Laurent monomial `T₀^{e₀}T₁^{e₁}` of total degree `d` falls into exactly one of three classes:
both exponents nonnegative, exactly one negative, or both negative. The first class is the
image of the diagonal and computes the kernel; the first two together are the image of the
differential; the third is a complement to that image and computes the cokernel. Since
`e₀ + e₁ = d`, the third class is empty precisely when `-1 ≤ d`, which is the vanishing
`H¹(ℙ¹_R, 𝒪(d)) = 0` for `d ≥ -1`, and in particular for every `d ≥ 0`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.lineNegativeMonomials` — the degree-`d` Laurent monomials
  of the projective line with both exponents negative.
* `Stacks.ProjectiveSpace.Cohomology.lineNegativePart` — the free `R`-module on those.
* `Stacks.ProjectiveSpace.Cohomology.lineCechDiff` — the Čech differential `(a, b) ↦ a - b` of
  the two-chart cover.
* `Stacks.ProjectiveSpace.Cohomology.lineDiag` — a binary form read as a Čech cocycle.

## Main results

* `range_lineCechDiff` — the image of the differential is the join of the two charts.
* `lineCechDiff_range_eq_overlap` — for `-1 ≤ d` that image is the whole overlap chart, so the
  differential is onto: the first Čech cohomology vanishes.
* `lineCechDiff_sup_lineNegativePart` and `lineCechDiff_disjoint_lineNegativePart` — in every
  degree `lineNegativePart` is a complement of the image inside the overlap chart, so the first
  Čech cohomology is free on the Laurent monomials with both exponents negative.
* `lineNegativePart_eq_bot_iff` — that complement vanishes exactly when `-1 ≤ d`.
* `range_lineDiag` and `lineCechH0Equiv` — the kernel of the differential is the polynomial
  chart, hence by `twistChartEmptyLinearEquiv` the module of degree-`d` binary forms when
  `0 ≤ d`.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {d : ℤ}

section Monomials

/-- On `Fin 2` the complement of `{0}` is `{1}` and conversely, so the nonnegativity condition
cutting out a one-variable chart is a condition at the other index. -/
theorem notMem_singleton_fin_two {i j : Fin 2} (h : i ∉ ({j} : Set (Fin 2))) : i = 1 - j := by
  have hij : i ≠ j := h
  revert hij
  fin_cases i <;> fin_cases j <;> simp +decide

/-- A Laurent monomial of the projective line lies in the chart inverting only `T₀` exactly
when its exponent at `1` is nonnegative. -/
theorem mem_laurentMonomials_zero {e : Fin 2 → ℤ} :
    e ∈ laurentMonomials 1 d ({0} : Set (Fin 2)) ↔ e 0 + e 1 = d ∧ 0 ≤ e 1 := by
  simp

/-- A Laurent monomial of the projective line lies in the chart inverting only `T₁` exactly
when its exponent at `0` is nonnegative. -/
theorem mem_laurentMonomials_one {e : Fin 2 → ℤ} :
    e ∈ laurentMonomials 1 d ({1} : Set (Fin 2)) ↔ e 0 + e 1 = d ∧ 0 ≤ e 0 := by
  simp

/-- A Laurent monomial of the projective line is a polynomial monomial exactly when both of its
exponents are nonnegative. -/
theorem mem_laurentMonomials_empty_fin_two {e : Fin 2 → ℤ} :
    e ∈ laurentMonomials 1 d (∅ : Set (Fin 2)) ↔ e 0 + e 1 = d ∧ 0 ≤ e 0 ∧ 0 ≤ e 1 := by
  rw [mem_laurentMonomials, Fin.sum_univ_two]
  refine and_congr_right fun _ => ⟨fun h => ⟨h 0 (by simp), h 1 (by simp)⟩, fun h i _ => ?_⟩
  fin_cases i <;> simp [h.1, h.2]

/-- The degree-`d` Laurent monomials of the projective line whose two exponents are both
negative. These index the first Čech cohomology of the two-chart cover. -/
def lineNegativeMonomials (d : ℤ) : Set (Fin 2 → ℤ) :=
  {e | e 0 + e 1 = d ∧ e 0 < 0 ∧ e 1 < 0}

/-- Every degree-`d` Laurent monomial of the projective line is regular along one of the two
coordinates or has both exponents negative. -/
theorem laurentMonomials_univ_fin_two (d : ℤ) :
    laurentMonomials 1 d (Set.univ : Set (Fin 2)) =
      (laurentMonomials 1 d ({0} : Set (Fin 2)) ∪ laurentMonomials 1 d ({1} : Set (Fin 2))) ∪
        lineNegativeMonomials d := by
  ext e
  rw [Set.mem_union, Set.mem_union, mem_laurentMonomials_zero, mem_laurentMonomials_one,
    mem_laurentMonomials]
  constructor
  · intro he
    have hsum : e 0 + e 1 = d := by rw [← Fin.sum_univ_two e]; exact he.1
    rcases le_or_gt 0 (e 1) with h | h
    · exact Or.inl (Or.inl ⟨hsum, h⟩)
    · rcases le_or_gt 0 (e 0) with h' | h'
      · exact Or.inl (Or.inr ⟨hsum, h'⟩)
      · exact Or.inr ⟨hsum, h', h⟩
  · intro he
    refine ⟨?_, fun i hi => absurd (Set.mem_univ i) hi⟩
    rw [Fin.sum_univ_two]
    rcases he with (h | h) | h <;> exact h.1

/-- A monomial with both exponents negative is in neither one-variable chart. -/
theorem disjoint_lineNegativeMonomials (d : ℤ) :
    Disjoint (laurentMonomials 1 d ({0} : Set (Fin 2)) ∪ laurentMonomials 1 d ({1} : Set (Fin 2)))
      (lineNegativeMonomials d) := by
  rw [Set.disjoint_left]
  rintro e (he | he) hneg
  · exact absurd (mem_laurentMonomials_zero.1 he).2 (not_le.2 hneg.2.2)
  · exact absurd (mem_laurentMonomials_one.1 he).2 (not_le.2 hneg.2.1)

/-- There is a degree-`d` Laurent monomial with both exponents negative exactly when
`d ≤ -2`. -/
theorem lineNegativeMonomials_eq_empty_iff (d : ℤ) :
    lineNegativeMonomials d = ∅ ↔ -1 ≤ d := by
  refine ⟨fun h => ?_, fun hd => Set.eq_empty_iff_forall_notMem.2 fun e ⟨_, _, _⟩ => by omega⟩
  by_contra! hd
  exact Set.eq_empty_iff_forall_notMem.1 h ![-1, d + 1] ⟨by simp, by simp, by simp; omega⟩

/-- A degree-`d` Laurent monomial of the projective line is a polynomial monomial exactly when
it lies in both one-variable charts. -/
theorem laurentMonomials_inter_fin_two (d : ℤ) :
    laurentMonomials 1 d ({0} : Set (Fin 2)) ∩ laurentMonomials 1 d ({1} : Set (Fin 2)) =
      laurentMonomials 1 d (∅ : Set (Fin 2)) := by
  ext e
  rw [Set.mem_inter_iff, mem_laurentMonomials_zero, mem_laurentMonomials_one,
    mem_laurentMonomials_empty_fin_two]
  tauto

end Monomials

variable (R d)

/-- The free `R`-module on the degree-`d` Laurent monomials of the projective line with both
exponents negative. It is a complement inside the overlap chart to the image of the Čech
differential, hence computes `H¹(ℙ¹_R, 𝒪(d))`. -/
def lineNegativePart : Submodule R ((Fin 2 → ℤ) →₀ R) :=
  Finsupp.supported R R (lineNegativeMonomials d)

/-- The degree-one Čech differential of the standard two-chart cover of the projective line:
a pair of sections of `𝒪(d)`, one on `D₊(T₀)` and one on `D₊(T₁)`, is sent to the difference
of their restrictions to `D₊(T₀T₁)`. -/
def lineCechDiff :
    (twistChart R 1 d ({0} : Set (Fin 2))) × (twistChart R 1 d ({1} : Set (Fin 2))) →ₗ[R]
      ((Fin 2 → ℤ) →₀ R) :=
  LinearMap.coprod (twistChart R 1 d ({0} : Set (Fin 2))).subtype
    (-(twistChart R 1 d ({1} : Set (Fin 2))).subtype)

/-- The Čech differential sends a pair of chart sections to the difference of the underlying
Laurent sections. -/
@[simp]
theorem lineCechDiff_apply
    (x : twistChart R 1 d ({0} : Set (Fin 2))) (y : twistChart R 1 d ({1} : Set (Fin 2))) :
    lineCechDiff R d (x, y) = x.1 - y.1 := by
  simp [lineCechDiff, sub_eq_add_neg]

/-- The image of the Čech differential is the sum of the two one-variable charts. -/
theorem range_lineCechDiff :
    LinearMap.range (lineCechDiff R d) =
      twistChart R 1 d ({0} : Set (Fin 2)) ⊔ twistChart R 1 d ({1} : Set (Fin 2)) := by
  rw [lineCechDiff, LinearMap.range_coprod, Submodule.range_subtype, LinearMap.range_neg,
    Submodule.range_subtype]

variable {R d}

/-- **Stacks 01XT for `ℙ¹`, the vanishing of the first Čech cohomology.** For `-1 ≤ d` — in
particular for every `d ≥ 0` — the Čech differential of the two-chart cover of the projective
line is onto the overlap chart: every degree-`d` Laurent section on `D₊(T₀T₁)` is a difference
of sections on `D₊(T₀)` and `D₊(T₁)`. -/
theorem lineCechDiff_range_eq_overlap (hd : -1 ≤ d) :
    LinearMap.range (lineCechDiff R d) = twistChart R 1 d (Set.univ : Set (Fin 2)) := by
  rw [range_lineCechDiff, twistChart_sup, twistChart, laurentMonomials_univ_fin_two,
    (lineNegativeMonomials_eq_empty_iff d).2 hd, Set.union_empty]

/-- **Stacks 01XT for `ℙ¹`, the first Čech cohomology in general.** The image of the Čech
differential and `lineNegativePart` together exhaust the overlap chart. -/
theorem lineCechDiff_sup_lineNegativePart (R : Type u) [CommRing R] (d : ℤ) :
    LinearMap.range (lineCechDiff R d) ⊔ lineNegativePart R d =
      twistChart R 1 d (Set.univ : Set (Fin 2)) := by
  rw [range_lineCechDiff, twistChart_sup, lineNegativePart, ← Finsupp.supported_union,
    twistChart, laurentMonomials_univ_fin_two]

/-- The image of the Čech differential and `lineNegativePart` meet in zero. With
`lineCechDiff_sup_lineNegativePart` this exhibits `lineNegativePart` as a complement of the
image inside the overlap chart, so the first Čech cohomology of the two-chart cover of the
projective line is free on the degree-`d` Laurent monomials with both exponents negative. -/
theorem lineCechDiff_disjoint_lineNegativePart (R : Type u) [CommRing R] (d : ℤ) :
    Disjoint (LinearMap.range (lineCechDiff R d)) (lineNegativePart R d) := by
  rw [range_lineCechDiff, twistChart_sup, lineNegativePart]
  exact Finsupp.disjoint_supported_supported (disjoint_lineNegativeMonomials d)

/-- The first Čech cohomology of the two-chart cover vanishes exactly when `-1 ≤ d`. -/
theorem lineNegativePart_eq_bot_iff (R : Type u) [CommRing R] [Nontrivial R] (d : ℤ) :
    lineNegativePart R d = ⊥ ↔ -1 ≤ d := by
  rw [lineNegativePart, ← lineNegativeMonomials_eq_empty_iff d]
  refine ⟨fun h => Set.eq_empty_iff_forall_notMem.2 fun e he => ?_, fun h => by
    rw [h, Finsupp.supported_empty]⟩
  have h1 : (Finsupp.single e (1 : R)) ∈ Finsupp.supported R R (lineNegativeMonomials d) :=
    Finsupp.single_mem_supported R 1 he
  rw [h, Submodule.mem_bot, Finsupp.single_eq_zero] at h1
  exact one_ne_zero h1

/-- A pair of Laurent sections is a Čech cocycle exactly when the two agree on the overlap. -/
theorem mem_ker_lineCechDiff_iff
    (z : (twistChart R 1 d ({0} : Set (Fin 2))) × (twistChart R 1 d ({1} : Set (Fin 2)))) :
    z ∈ LinearMap.ker (lineCechDiff R d) ↔
      (z.1 : (Fin 2 → ℤ) →₀ R) = (z.2 : (Fin 2 → ℤ) →₀ R) := by
  rw [LinearMap.mem_ker, lineCechDiff_apply, sub_eq_zero]

variable (R d)

/-- A degree-`d` binary form, read as a Čech cocycle: the same section on both standard opens.
Its image is the kernel of the Čech differential. -/
def lineDiag :
    twistChart R 1 d (∅ : Set (Fin 2)) →ₗ[R]
      (twistChart R 1 d ({0} : Set (Fin 2))) × (twistChart R 1 d ({1} : Set (Fin 2))) :=
  LinearMap.prod
    (LinearMap.codRestrict _ (twistChart R 1 d (∅ : Set (Fin 2))).subtype
      (fun z => twistChart_mono (Set.empty_subset _) z.2))
    (LinearMap.codRestrict _ (twistChart R 1 d (∅ : Set (Fin 2))).subtype
      (fun z => twistChart_mono (Set.empty_subset _) z.2))

/-- The first component of `lineDiag R d z` is `z` itself, as a Laurent section. -/
@[simp]
theorem lineDiag_apply_fst (z : twistChart R 1 d (∅ : Set (Fin 2))) :
    ((lineDiag R d z).1 : (Fin 2 → ℤ) →₀ R) = (z : (Fin 2 → ℤ) →₀ R) := rfl

/-- The second component of `lineDiag R d z` is `z` itself, as a Laurent section. -/
@[simp]
theorem lineDiag_apply_snd (z : twistChart R 1 d (∅ : Set (Fin 2))) :
    ((lineDiag R d z).2 : (Fin 2 → ℤ) →₀ R) = (z : (Fin 2 → ℤ) →₀ R) := rfl

/-- The diagonal map from degree-`d` binary forms to pairs of chart sections is injective. -/
theorem lineDiag_injective : Function.Injective (lineDiag R d) := by
  intro x y h
  exact Subtype.ext (by
    have := congrArg (fun w => ((w.1 : twistChart R 1 d ({0} : Set (Fin 2))) :
      (Fin 2 → ℤ) →₀ R)) h
    simpa using this)

/-- **Stacks 01XT for `ℙ¹`, the degree-zero cohomology.** The Čech cocycles of the two-chart
cover are exactly the diagonal copies of the degree-`d` binary forms: a pair of Laurent
sections agreeing on `D₊(T₀T₁)` has both exponents nonnegative. -/
theorem range_lineDiag :
    LinearMap.range (lineDiag R d) = LinearMap.ker (lineCechDiff R d) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    rw [mem_ker_lineCechDiff_iff]
    rfl
  · rintro ⟨x, y⟩ hz
    have hxy : (x : (Fin 2 → ℤ) →₀ R) = (y : (Fin 2 → ℤ) →₀ R) :=
      (mem_ker_lineCechDiff_iff (x, y)).1 hz
    have hx : (x : (Fin 2 → ℤ) →₀ R) ∈ twistChart R 1 d (∅ : Set (Fin 2)) := by
      rw [mem_twistChart, ← laurentMonomials_inter_fin_two d]
      exact Set.subset_inter (mem_twistChart.1 x.2) (hxy ▸ mem_twistChart.1 y.2)
    exact ⟨⟨(x : (Fin 2 → ℤ) →₀ R), hx⟩, Prod.ext (Subtype.ext rfl) (Subtype.ext hxy)⟩

/-- The degree-zero Čech cohomology of the two-chart cover of the projective line is the
polynomial chart; composing with `twistChartEmptyLinearEquiv` identifies it with the
degree-`d` binary forms when `0 ≤ d`. -/
def lineCechH0Equiv :
    twistChart R 1 d (∅ : Set (Fin 2)) ≃ₗ[R] LinearMap.ker (lineCechDiff R d) :=
  (LinearEquiv.ofInjective (lineDiag R d) (lineDiag_injective R d)).trans
    (LinearEquiv.ofEq _ _ (range_lineDiag R d))

end Stacks.ProjectiveSpace.Cohomology

end

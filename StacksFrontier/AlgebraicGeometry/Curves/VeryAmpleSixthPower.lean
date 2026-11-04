module

public import StacksFrontier.RingTheory.GradedAlgebra.Veronese
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# The very ample sixth power of an ample invertible sheaf on a curve

Let `k` be a field, let `X` be a proper scheme over `k` of dimension `1` with
`H⁰(X, 𝒪_X) = k`, and let `ℒ` be an invertible `𝒪_X`-module which has a regular global section,
has `H¹(X, ℒ) = 0` and is ample. [Stacks, Tag 0E8V] says that `ℒ^{⊗ 6}` is then very ample on `X`
over `k`.

The source's proof has two halves. The first is cohomological: the zero scheme `Z = Z(s)` of the
regular section is zero-dimensional, hence the spectrum of an Artinian ring, so `ℒ|_Z ≅ 𝒪_Z`; the
short exact sequences `0 → ℒ^{⊗ n} → ℒ^{⊗ n+1} → i_*(ℒ^{⊗ n+1}|_Z) → 0` then give
`H¹(X, ℒ^{⊗ n}) = 0` for every `n > 0` and make the multiplication maps
`Γ(ℒ) ⊗ Γ(ℒ^{⊗ n}) ⊕ Γ(ℒ^{⊗ 2}) ⊗ Γ(ℒ^{⊗ n-1}) → Γ(ℒ^{⊗ n+1})` surjective for `n ≥ 3`, so that
the graded section ring `S = Γ_*(X, ℒ)` is generated over `S₀` in degrees `1`, `2` and `3`. The
second is the closing sentence: `X = Proj S`, so the sixth Veronese subring `S^{(6)}` being
generated in degree one makes `ℒ^{⊗ 6}` very ample.

**What joins the two halves, and is the arithmetic reason the exponent is `6`, is proved here**: a
graded ring generated over its degree-zero part by homogeneous elements of degrees in `{1, 2, 3}`
has its sixth Veronese subring generated in degree one. Equivalently, a multiset drawn from
`{1, 2, 3}` whose total is a positive multiple of `6` always has a sub-multiset of total exactly
`6` — which fails for `4` and for `5` in place of `6`, so no smaller exponent is available by this
argument.

The two halves themselves are carried as named hypotheses, because neither is available over
library names: `Stacks.Curves.VeryAmpleSixthPower.SectionRingGeneratedInDegreesLeThree` is the
first half and `Stacks.Curves.VeryAmpleSixthPower.VeroneseVeryAmpleBridge` the second. Their
docstrings name the Stacks tags each rests on and which of those tags the repository lacks.

## Main results

* `Stacks.Curves.VeryAmpleSixthPower.exists_split_sum_eq_six`: the arithmetic core — if
  `a + 2b + 3c` is a positive multiple of `6` then there are `k₁ ≤ a`, `k₂ ≤ b` and `k₃ ≤ c` with
  `k₁ + 2k₂ + 3k₃ = 6`.
* `Stacks.Curves.VeryAmpleSixthPower.exists_le_exponents_weight_eq_six`: the same for an exponent
  vector weighted by degrees in `{1, 2, 3}`.
* `Stacks.Curves.VeryAmpleSixthPower.monomial_mem_degOneProducts_six`: a monomial in generators of
  degrees in `{1, 2, 3}` whose total degree is `6n` is an `n`-fold product of elements of `S₆`.
* `Stacks.Curves.VeryAmpleSixthPower.veroneseGeneratedInDegOne_six`: hence `S^{(6)}` is generated
  in degree one over `S₀`.
* `Stacks.Curves.VeryAmpleSixthPower.isRelativelyVeryAmple_tensorPowModule_six`:
  **[Stacks, Tag 0E8V]**, on the two named hypotheses above.

## References

* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 0EGH](https://stacks.math.columbia.edu/tag/0EGH)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Ample
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.GradedSections (sectionRing)

universe u

namespace Stacks.Curves.VeryAmpleSixthPower

section GradedAlgebra

/-! ### The arithmetic of degrees one, two and three -/

/-- **A multiset of `1`s, `2`s and `3`s whose total is a positive multiple of `6` has a
sub-multiset of total exactly `6`.** Written in terms of the three multiplicities: if
`a + 2b + 3c = 6n` with `n ≥ 1` then there are `k₁ ≤ a`, `k₂ ≤ b` and `k₃ ≤ c` with
`k₁ + 2k₂ + 3k₃ = 6`.

The witnesses used are `3 + 3`, `3 + 2 + 1`, `3 + 1 + 1 + 1`, `2 + 2 + 2`, `2 + 2 + 1 + 1`,
`2 + 1 + 1 + 1 + 1` and `1 + 1 + 1 + 1 + 1 + 1`; which one is available is decided by the
multiplicities, using divisibility of the total by `6` to rule out the remaining cases. -/
theorem exists_split_sum_eq_six {a b c n : ℕ} (hn : 1 ≤ n) (h : a + 2 * b + 3 * c = 6 * n) :
    ∃ k₁ k₂ k₃ : ℕ, k₁ ≤ a ∧ k₂ ≤ b ∧ k₃ ≤ c ∧ k₁ + 2 * k₂ + 3 * k₃ = 6 := by
  rcases (show c = 0 ∨ c = 1 ∨ 2 ≤ c by omega) with hc | hc | hc
  · rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ 3 ≤ b by omega) with hb | hb | hb | hb
    · exact ⟨6, 0, 0, by omega, by omega, by omega, by omega⟩
    · exact ⟨4, 1, 0, by omega, by omega, by omega, by omega⟩
    · exact ⟨2, 2, 0, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 3, 0, by omega, by omega, by omega, by omega⟩
  · rcases (show a ≤ 2 ∨ 3 ≤ a by omega) with ha | ha
    · exact ⟨1, 1, 1, by omega, by omega, by omega, by omega⟩
    · exact ⟨3, 0, 1, by omega, by omega, by omega, by omega⟩
  · exact ⟨0, 0, 2, by omega, by omega, by omega, by omega⟩

/-- **A pointwise-smaller function with a prescribed total.** For `e : ι → ℕ`, a finite set `t`
and `k ≤ ∑_{i ∈ t} e i`, there is `e' ≤ e` vanishing off `t` with `∑_{i ∈ t} e' i = k`. -/
theorem exists_le_fun_sum_eq {ι : Type*} (e : ι → ℕ) (t : Finset ι) :
    ∀ k, k ≤ (∑ i ∈ t, e i) →
      ∃ e' : ι → ℕ, (∀ i, e' i ≤ e i) ∧ (∀ i, i ∉ t → e' i = 0) ∧ ∑ i ∈ t, e' i = k := by
  classical
  induction t using Finset.induction with
  | empty =>
    intro k hk
    simp only [Finset.sum_empty, Nat.le_zero] at hk
    exact ⟨fun _ => 0, fun i => Nat.zero_le _, fun i _ => rfl, by simp [hk]⟩
  | @insert j t hj ih =>
    intro k hk
    rw [Finset.sum_insert hj] at hk
    obtain ⟨e₀, hle, hsupp, hsum⟩ := ih (k - min k (e j)) (by omega)
    have hoff : ∑ i ∈ t, (if i = j then min k (e j) else e₀ i) = ∑ i ∈ t, e₀ i :=
      Finset.sum_congr rfl fun i hi => by
        have hij : i ≠ j := fun hh => hj (hh ▸ hi)
        simp [hij]
    refine ⟨fun i => if i = j then min k (e j) else e₀ i, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · simp [hi]
      · simpa [hi] using hle i
    · intro i hi
      have hij : i ≠ j := fun hh => hi (by simp [hh])
      have hit : i ∉ t := fun hh => hi (Finset.mem_insert_of_mem hh)
      simp [hij, hsupp i hit]
    · rw [Finset.sum_insert hj, hoff, hsum]
      simp

/-- **The weight of an exponent vector, split by degree class.** When every degree lies in
`{1, 2, 3}`, the weight `∑ v i * deg i` is `a + 2b + 3c`, where `a`, `b` and `c` are the totals of
`v` over the indices of degree `1`, `2` and `3`. -/
theorem weight_eq_sum_filter {r : ℕ} (deg : Fin r → ℕ) (hdeg1 : ∀ i, 1 ≤ deg i)
    (hdeg3 : ∀ i, deg i ≤ 3) (v : Fin r → ℕ) :
    ∑ i, v i * deg i =
      (∑ i ∈ Finset.univ.filter fun i => deg i = 1, v i) +
        2 * (∑ i ∈ Finset.univ.filter fun i => deg i = 2, v i) +
          3 * (∑ i ∈ Finset.univ.filter fun i => deg i = 3, v i) := by
  classical
  have hterm : ∀ i : Fin r, v i * deg i =
      (if deg i = 1 then v i else 0) + 2 * (if deg i = 2 then v i else 0)
        + 3 * (if deg i = 3 then v i else 0) := by
    intro i
    have h1 := hdeg1 i
    have h3 := hdeg3 i
    rcases (show deg i = 1 ∨ deg i = 2 ∨ deg i = 3 by omega) with h | h | h <;>
      simp [h, Nat.mul_comm]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hterm i

/-- **A sub-exponent vector of weight exactly six.** If every degree lies in `{1, 2, 3}` and the
weight `∑ e i * deg i` is a positive multiple of `6`, there is `e' ≤ e` of weight exactly `6`. -/
theorem exists_le_exponents_weight_eq_six {r : ℕ} (deg : Fin r → ℕ) (hdeg1 : ∀ i, 1 ≤ deg i)
    (hdeg3 : ∀ i, deg i ≤ 3) (e : Fin r → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hsum : ∑ i, e i * deg i = 6 * n) :
    ∃ e' : Fin r → ℕ, (∀ i, e' i ≤ e i) ∧ ∑ i, e' i * deg i = 6 := by
  classical
  obtain ⟨k₁, k₂, k₃, hk₁, hk₂, hk₃, hk⟩ :=
    exists_split_sum_eq_six hn (by rw [← hsum, weight_eq_sum_filter deg hdeg1 hdeg3 e])
  obtain ⟨e₁, hle₁, hsupp₁, hsum₁⟩ :=
    exists_le_fun_sum_eq e (Finset.univ.filter fun i => deg i = 1) k₁ hk₁
  obtain ⟨e₂, hle₂, hsupp₂, hsum₂⟩ :=
    exists_le_fun_sum_eq e (Finset.univ.filter fun i => deg i = 2) k₂ hk₂
  obtain ⟨e₃, hle₃, hsupp₃, hsum₃⟩ :=
    exists_le_fun_sum_eq e (Finset.univ.filter fun i => deg i = 3) k₃ hk₃
  refine ⟨fun i => e₁ i + e₂ i + e₃ i, ?_, ?_⟩
  · intro i
    have h1 := hdeg1 i
    have h3 := hdeg3 i
    rcases (show deg i = 1 ∨ deg i = 2 ∨ deg i = 3 by omega) with h | h | h
    · have hb : e₂ i = 0 := hsupp₂ i (by simp [h])
      have hc : e₃ i = 0 := hsupp₃ i (by simp [h])
      simpa [hb, hc] using hle₁ i
    · have ha : e₁ i = 0 := hsupp₁ i (by simp [h])
      have hc : e₃ i = 0 := hsupp₃ i (by simp [h])
      simpa [ha, hc] using hle₂ i
    · have ha : e₁ i = 0 := hsupp₁ i (by simp [h])
      have hb : e₂ i = 0 := hsupp₂ i (by simp [h])
      simpa [ha, hb] using hle₃ i
  · have hw : ∀ (d : ℕ) (e₀ : Fin r → ℕ) (k : ℕ),
        (∀ i, i ∉ Finset.univ.filter (fun i => deg i = d) → e₀ i = 0) →
          ∑ i ∈ Finset.univ.filter (fun i => deg i = d), e₀ i = k →
            ∑ i, e₀ i * deg i = k * d := by
      intro d e₀ k hs hk
      rw [← hk, Finset.sum_mul, ← Finset.sum_subset (Finset.filter_subset (fun i => deg i = d) _)
        fun i _ hi => by simp [hs i hi]]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hw 1 e₁ k₁ hsupp₁ hsum₁, hw 2 e₂ k₂ hsupp₂ hsum₂, hw 3 e₃ k₃ hsupp₃ hsum₃]
    omega

/-! ### Monomials in generators of degrees one, two and three -/

variable {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **A monomial of total degree `6n` is an `n`-fold product of elements of `S₆`.** The exponent
vector is peeled `n` times by `exists_le_exponents_weight_eq_six`: each peel removes a
sub-exponent vector of weight exactly `6`, whose monomial is a single homogeneous element of
degree `6`. -/
theorem monomial_mem_degOneProducts_six {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg1 : ∀ i, 1 ≤ deg i) (hdeg3 : ∀ i, deg i ≤ 3) (hfdeg : ∀ i, f i ∈ 𝒜 (deg i)) (n : ℕ) :
    ∀ e : Fin r → ℕ, ∑ i, e i * deg i = 6 * n →
      (∏ i, f i ^ e i) ∈ Stacks.Veronese.degOneProducts 𝒜 6 n := by
  induction n with
  | zero =>
    intro e hsum
    have he : ∀ i, e i = 0 := by
      intro i
      by_contra hcon
      have hpos : 0 < e i * deg i := Nat.mul_pos (Nat.pos_of_ne_zero hcon) (hdeg1 i)
      have hle : e i * deg i ≤ ∑ j, e j * deg j :=
        Finset.single_le_sum (f := fun j => e j * deg j) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [he]⟩
  | succ m ih =>
    intro e hsum
    obtain ⟨e', hle', hw'⟩ :=
      exists_le_exponents_weight_eq_six deg hdeg1 hdeg3 e (n := m + 1) (by omega) hsum
    have hdiff : ∀ i, (e i - e' i) * deg i + e' i * deg i = e i * deg i := by
      intro i
      have h1 : e' i * deg i ≤ e i * deg i := Nat.mul_le_mul_right _ (hle' i)
      rw [Nat.sub_mul, Nat.sub_add_cancel h1]
    have hsum'' : ∑ i, (e i - e' i) * deg i = 6 * m := by
      have hadd : (∑ i, (e i - e' i) * deg i) + ∑ i, e' i * deg i = ∑ i, e i * deg i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hdiff i
      omega
    obtain ⟨g, hg, hgeq⟩ := ih (fun i => e i - e' i) hsum''
    have hmem6 : (∏ i, f i ^ e' i) ∈ 𝒜 6 := by
      have hprod : (∏ i, f i ^ e' i) ∈ 𝒜 (∑ i, e' i * deg i) :=
        SetLike.prod_mem_graded 𝒜 (fun i => e' i * deg i) (fun i => f i ^ e' i)
          fun i _ => Stacks.Veronese.pow_mem_grade 𝒜 f deg hfdeg i (e' i)
      rwa [hw'] at hprod
    refine ⟨Fin.cons (∏ i, f i ^ e' i) g, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hmem6
      · intro j; simpa using hg j
    · rw [Fin.prod_cons, ← hgeq, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add]
      congr 1
      have := hle' i
      omega

/-- **The sixth Veronese subring of a graded ring generated in degrees one, two and three is
generated in degree one.** Let `S` be a graded ring generated over `S₀` by finitely many
homogeneous elements whose degrees lie in `{1, 2, 3}`. Then for every `n ≥ 1` the `S₀`-module
`S_{6n}` is spanned by the `n`-fold products of elements of `S₆`.

The two inclusions are `Stacks.Veronese.span_degOneProducts_subset`, which needs no hypothesis,
and the composite of `Stacks.Veronese.mem_span_monomials` with
`Stacks.Curves.VeryAmpleSixthPower.monomial_mem_degOneProducts_six`. -/
@[ega "II 2.1.6" "(v) with h = 6"]
theorem veroneseGeneratedInDegOne_six {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ)
    (hdeg1 : ∀ i, 1 ≤ deg i) (hdeg3 : ∀ i, deg i ≤ 3) (hfdeg : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (Stacks.Veronese.gradeZero 𝒜) (Set.range f) = ⊤) :
    Stacks.Veronese.VeroneseGeneratedInDegOne 𝒜 6 := by
  intro n _
  refine Set.Subset.antisymm ?_ (Stacks.Veronese.span_degOneProducts_subset 𝒜 6 n)
  refine (Stacks.Veronese.mem_span_monomials 𝒜 f deg hfdeg hgen (n * 6)).trans fun x hx => ?_
  refine Submodule.span_mono ?_ hx
  rintro y ⟨e, hsum, rfl⟩
  exact monomial_mem_degOneProducts_six 𝒜 f deg hdeg1 hdeg3 hfdeg n e (by omega)

end GradedAlgebra

/-! ### Stacks Tag 0E8V -/

section Geometry

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- **The cohomological half of the proof of [Stacks, Tag 0E8V]**, as a statement in its own
right: for a proper scheme `X` of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and an
ample invertible `𝒪_X`-module `ℒ` that has a regular global section and satisfies
`H¹(X, ℒ) = 0`, the graded section ring `Γ_*(X, ℒ) = ⨁_{n ≥ 0} Γ(X, ℒ^{⊗ n})` of
[Stacks, Tag 01CV] is generated over its degree-zero part by finitely many homogeneous elements of
degrees `1`, `2` and `3`.

The source reaches this by taking the zero scheme `Z = Z(s)` of the regular section
([Stacks, Tag 0C4S]), which is zero-dimensional ([Stacks, Tag 056N]) and hence the spectrum of an
Artinian ring ([Stacks, Tag 06LH]), so that `ℒ|_Z ≅ 𝒪_Z` ([Stacks, Tag 02M9]); the short exact
sequences `0 → ℒ^{⊗ n} → ℒ^{⊗ n+1} → i_*(ℒ^{⊗ n+1}|_Z) → 0` then give `H¹(X, ℒ^{⊗ n}) = 0` for
every `n > 0` together with global sections trivialising `ℒ^{⊗ n}|_Z`, and the multiplication
maps `Γ(ℒ) ⊗ Γ(ℒ^{⊗ n}) ⊕ Γ(ℒ^{⊗ 2}) ⊗ Γ(ℒ^{⊗ n-1}) → Γ(ℒ^{⊗ n+1})` are surjective for `n ≥ 3`
([Stacks, Tag 0AYT] supplies the vanishing on the right-hand term).

Carrying out that argument needs the long exact cohomology sequence of a short exact sequence of
quasi-coherent modules on a scheme over a field, which this repository does not have over library
names, so the conclusion is stated here as a hypothesis rather than proved. -/
def SectionRingGeneratedInDegreesLeThree (k : Type u) [Field k] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
      (L : X.Modules) [IsInvertibleModule X L] (s : 𝟙_ X.Modules ⟶ L),
    topologicalKrullDim X = 1 → Mono s →
      IsZero (AlgebraicGeometry.cohomologyOverField k f L 1) → IsAmple X L →
        ∃ (r : ℕ) (g : Fin r → sectionRing L) (deg : Fin r → ℕ), (∀ i, 1 ≤ deg i) ∧
          (∀ i, deg i ≤ 3) ∧ (∀ i, g i ∈ grading L (deg i)) ∧
            Algebra.adjoin (Stacks.Veronese.gradeZero (grading L)) (Set.range g) = ⊤

/-- **The geometric half of the proof of [Stacks, Tag 0E8V]**, as a degree-agnostic statement: if
`ℒ` is an ample invertible `𝒪_X`-module whose graded section ring `S = Γ_*(X, ℒ)` has its `d`-th
Veronese subring `S^{(d)}` generated in degree one over `S₀`, then `ℒ^{⊗ d}` is very ample
relative to the morphism `X ⟶ Spec k`.

This is the source's closing sentence, and it rests on four inputs.

* `X = Proj S`, which is [Stacks, Tag 0C6J]. Its library form,
  `Stacks.SectionRingProjIso.isIso_projHomOfIsAmple`, is proved, but takes as an argument the
  universal closedness of the structure morphism of `X` over `Spec S₀`; identifying that morphism
  with `X ⟶ Spec k` is not available. The relative form of the tag,
  `Stacks.RelativeAmple.isIso_relativeAmpleProjHom`, takes universal closedness of `X ⟶ Spec k`
  itself, but its target is the relative `Proj` over `Spec k` of `f_*(⨁_d ℒ^{⊗ d})`, which is not
  compared with `Proj S` here.
* The identification of `ℒ^{⊗ n}` with the pullback of the twisting sheaf `𝒪_{Proj S}(n)` along
  the canonical morphism of [Stacks, Tag 01PZ]. This is clause (2) of [Stacks, Tag 01QI], that is
  **[Stacks, Tag 01NK]**; the repository carries only clause (1) of Tag 01QI
  (`Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible`), and no comparison
  map between those two modules exists in either tree.
* The closed immersion `Proj S^{(d)} ⟶ 𝐏ⁿ_{S₀}` that generation in degree one furnishes, which is
  part (2) of [Stacks, Tag 01N0] and is proved
  (`Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_projToProjectiveSpaceGradeZero`),
  together with part (3) of that tag, which identifies the twisting sheaves along it and is not
  proved anywhere in either tree.
* The comparison of `𝐏ⁿ` with the projective bundle `𝐏(𝒪^{⊕ n+1})` that [Stacks, Tag 01VM]'s
  definition of relative very ampleness is stated at, together with the matching of the two
  degree-one twists across it. The scheme-level comparison is reduced by
  `Stacks.AlgebraicGeometry.ProjPolynomialSections.exists_iso_relativeProj` to the purely
  algebraic datum `Stacks.AlgebraicGeometry.ProjPolynomialSections.PolynomialSections` — graded
  ring isomorphisms of `Γ(U, Sym(𝒪^{⊕ n+1}))` with `Γ(U)[T₀, …, Tₙ]`, compatible with
  restriction — which is constructed for no graded algebra in either tree, and the twist matching
  is not stated.

Of the four, the first is available up to one unlanded identification and the second, third and
fourth are not, so the implication is carried here as a hypothesis pending their landing.

Nothing about properness, dimension one, `H⁰(X, 𝒪_X) = k`, the regular global section or the
exponent `6` enters this statement: the exponent `6` of [Stacks, Tag 0E8V] comes from
`Stacks.Curves.VeryAmpleSixthPower.veroneseGeneratedInDegOne_six`, which is proved. -/
def VeroneseVeryAmpleBridge (k : Type u) [Field k] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (L : X.Modules) [IsInvertibleModule X L] (d : ℕ),
    IsAmple X L → 0 < d → Stacks.Veronese.VeroneseGeneratedInDegOne (grading L) d →
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ))

/-- **[Stacks, Tag 0E8V].** Let `k` be a field, let `X` be a proper scheme over `k` of dimension
`1` with `H⁰(X, 𝒪_X) = k`, and let `ℒ` be an invertible `𝒪_X`-module. Assume that `ℒ` has a
regular global section, that `H¹(X, ℒ) = 0` and that `ℒ` is ample. Then `ℒ^{⊗ 6}` is very ample
on `X` over `k`.

The hypothesis `hcoh` is the cohomological half of the source's proof and `hbridge` its closing
sentence; both are carried as named hypotheses, and the identification of the immersion with the
morphism trivialising `ℒ` — [Stacks, Tag 01NK], clause (2) of [Stacks, Tag 01QI] — is among the
inputs of `hbridge` that the repository lacks, as its docstring records. Both are assumed pending
the landing of those inputs.

What is proved here is the step that joins the two halves and that is the reason the exponent is
`6`: the section ring, being generated in degrees `1`, `2` and `3`, has its sixth Veronese subring
generated in degree one, which is
`Stacks.Curves.VeryAmpleSixthPower.veroneseGeneratedInDegOne_six`.

The unconditional statement is
`Stacks.Curves.VeryAmpleSixthPower.isRelativelyVeryAmple_tensorPowModule_six_of_regularSection`
(`StacksFrontier/AlgebraicGeometry/Curves/VeryAmpleSixthPowerCriterion.lean`), which carries the tag:
`hcoh` holds outright (`sectionRingGeneratedInDegreesLeThree` there), and the use of `hbridge` is
replaced by `Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_tensorPowModule_of_generators`, its
instance for a proper `X` with finitely generated section ring. -/
theorem isRelativelyVeryAmple_tensorPowModule_six (k : Type u) [Field k]
    (hcoh : SectionRingGeneratedInDegreesLeThree k) (hbridge : VeroneseVeryAmpleBridge k)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (L : X.Modules) [IsInvertibleModule X L] (s : 𝟙_ X.Modules ⟶ L)
    (hdim : topologicalKrullDim X = 1) (hs : Mono s)
    (hH1 : IsZero (AlgebraicGeometry.cohomologyOverField k f L 1)) (hample : IsAmple X L) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (6 : ℤ)) := by
  obtain ⟨r, g, deg, hdeg1, hdeg3, hgmem, hgen⟩ := hcoh f L s hdim hs hH1 hample
  exact hbridge f L 6 hample (by omega)
    (veroneseGeneratedInDegOne_six (grading L) g deg hdeg1 hdeg3 hgmem hgen)

end Geometry

end Stacks.Curves.VeryAmpleSixthPower

end

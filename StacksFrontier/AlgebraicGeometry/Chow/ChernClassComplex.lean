module

public import Mathlib.Algebra.Ring.NegOnePow
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# Characteristic classes of a complex of finite locally free modules

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL: a locally
Noetherian, universally catenary scheme `S` together with a dimension function `δ : S → 𝐙`. Let
`X` be a scheme locally of finite type over `S`. Section 42.46 of the source attaches to a
bounded complex

  `ℰ^a ⟶ ℰ^{a + 1} ⟶ … ⟶ ℰ^b`

of finite locally free `𝒪_X`-modules of constant rank the three classes

  `c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n} ∈ ∏_{p ≥ 0} A^p(X)`,
  `ch(ℰ^•) = ∑_n (-1)^n ch(ℰ^n) ∈ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`,
  `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n) ∈ A^p(X)`,

the inverse being the formal inverse of a series with constant term `1`. **Stacks 0ESZ** asserts
that a slight generalization of these constructions — the ranks are no longer assumed constant
and the complex is only assumed locally bounded — depends only on the object of `D(𝒪_X)` the
complex represents.

This file constructs the three classes and proves that independence, in the following form. All
three are functions of the alternating class

  `∑_n (-1)^n [ℰ^n] ∈ K_0(Vect(X))`

of Stacks 0FDK, because each of them is additive — multiplicative for `c` — on short exact
sequences of finite locally free modules: that is Stacks 02UI for `c` and Stacks 0F9C for `P_p`
and `ch`. So the whole of Stacks 0ESZ reduces to the statement that the alternating class in
`K_0(Vect(X))` depends only on the derived object, and that is what is proved here, by the
source's own argument: the degreewise short exact sequences

  `0 ⟶ Ker(d^n) ⟶ ℰ^n ⟶ Im(d^n) ⟶ 0`

turn the alternating class into `∑_n (-1)^n ([Ker(d^n)] - [Im(d^{n-1})])`, the images
telescoping away, and Schanuel's lemma makes each summand depend only on the cohomology module
`H^n = Ker(d^n)/Im(d^{n-1})`.

## Where Stacks 0ESZ is registered

Nothing in this file carries `@[stacks 0ESZ]`: the classes here are built from the carried data
`Stacks.Chow.TotalChernClassSeries` and `Stacks.Chow.PowerSumClassRule`, the complexes are bounded
in one window of degrees, and the independence is proved from a carried
`Stacks.Chow.ComplexCohomologyComparison` instead of an isomorphism in `D(𝒪_X)`. The tag is
registered on the complete statement, for the constructed classes of a locally bounded complex
and an isomorphism in the derived category, with the reduction of the source through Stacks
02UC, 0ESR and 0F8J carried out: `Stacks.Chow.complexChern_eq_of_iso` (for `c`),
`Stacks.Chow.powerSumComplex_eq_of_iso` (for `P_p`) and
`Stacks.Chow.chernCharacterComplex_eq_of_iso` (for `ch`), together with the definitions
`Stacks.Chow.complexChern`, `Stacks.Chow.complexPowerSumComponent` and
`Stacks.Chow.complexChernCharacter` and the independence statements
`Stacks.Chow.complexPowerSumComponent_eq_of_iso` and `Stacks.Chow.complexChernCharacter_eq_of_iso`.

## Main definitions

* `Stacks.Chow.alternatingKClass` — the class `∑_n (-1)^n [ℰ^n]` in `K_0(Vect(X))` of a complex
  bounded in the degrees `a, …, a + k`.
* `Stacks.Chow.BoundedComplexSplitting` — the degreewise exactness data of a complex of finite
  locally free modules whose kernels and images are again finite locally free, which is what the
  source takes from Stacks 0F8J.
* `Stacks.Chow.ComplexCohomologyComparison` — two such complexes with the same cohomology modules,
  together with the module Schanuel's lemma (Stacks 00O3) produces from the two presentations of
  each cohomology module. This is the datum the source extracts from an isomorphism in
  `D(𝒪_X)`; see the implementation notes.
* `Stacks.Chow.PowerSumClassRule` — the power sum classes `P_p(ℰ)` of a finite locally free
  module, as a datum, with their additivity on short exact sequences (Stacks 0F9C).
* `Stacks.Chow.totalChernClassComplex` — the total Chern class `c(ℰ^•)`, in carried form.
* `Stacks.Chow.powerSumClassComplex` — the class `P_p(ℰ^•)`, in carried form.
* `Stacks.Chow.chernCharacterComplexComponent` — the component `ch_p(ℰ^•) = P_p(ℰ^•)/p!`, in
  carried form.

## Main results

* `Stacks.Chow.sum_negOnePow_smul_add_succ` — the alternating telescope.
* `Stacks.Chow.alternatingKClass_eq_sum_sub` — the alternating class of a complex equals
  `∑_n (-1)^n ([Ker(d^n)] - [Im(d^{n-1})])`.
* `Stacks.Chow.alternatingKClass_eq_zero_of_acyclic` — an acyclic complex has zero alternating
  class.
* `Stacks.Chow.classOf_sub_eq_of_schanuel` — Schanuel's lemma in `K_0(Vect(X))`: the difference
  `[ℰ] - [ℰ']` of a two-term presentation of a module depends only on the module.
* `Stacks.Chow.alternatingKClass_eq_of_cohomologyComparison` — the alternating class depends only
  on the cohomology modules.
* `Stacks.Chow.totalChernClassComplex_eq_prod`, `Stacks.Chow.powerSumClassComplex_eq_sum` — the
  three classes are given by the formulas of the source.
* `Stacks.Chow.totalChernClassComplex_eq_of_cohomologyComparison`,
  `Stacks.Chow.powerSumClassComplex_eq_of_cohomologyComparison`,
  `Stacks.Chow.chernCharacterComplexComponent_eq_of_cohomologyComparison` — the independence of
  the representative, for each of the three classes, from the carried comparison datum.

## Implementation notes

### What the hypothesis "representing the same object of `D(𝒪_X)`" is replaced by

No derived category appears below. The source's proof does not use the isomorphism
`ℰ^• ≅ ℱ^•` in `D(𝒪_X)` directly; it uses the two things that isomorphism yields, and those are
exactly the fields of `Stacks.Chow.ComplexCohomologyComparison`:

* the cohomology modules of the two complexes are the same, each presented as
  `Ker(d^n)/Im(d^{n-1})` by the complex it comes from; and
* for each `n` a single finite locally free module fitting into the two short exact sequences
  that Schanuel's lemma produces from those two presentations.

Both are **carried**, and so is everything the source spends to produce them: the reduction to
an integral test scheme by Stacks 02UC, the proper birational modification making the
cohomology modules perfect of tor dimension at most one by Stacks 0ESR, the finite local
freeness of the kernels and images by Stacks 0F8J (carried as
`Stacks.Chow.BoundedComplexSplitting`), and Schanuel's lemma itself, Stacks 00O3. What would
discharge them is a sheaf-level form of Stacks 0F8J producing the splitting from the perfectness
of the cohomology, together with Stacks 00O3 for modules on a scheme and the two reductions
Stacks 02UC and Stacks 0ESR. This file keeps the degreewise data as the hypothesis; the
reduction itself is carried out in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Independence` and
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumIndependence`, which prove the
unconditional statement.

Nothing in the proofs below uses the fields presenting the cohomology modules — only the
Schanuel module and its two short exact sequences. Those fields are kept because without them
the datum would not say that the two complexes have the same cohomology, which is what makes
the theorem a formalization of Stacks 0ESZ rather than a statement about unrelated complexes.

### Bounded, not locally bounded

The complex is required to be bounded in the degrees `a, …, a + k`, in the form that the two
images at the ends of that range vanish; for a complex whose terms vanish outside the range this
is automatic, the bottom image having zero source and the top image zero target. The source's
generalization is to a *locally* bounded complex, where the bound varies over a decomposition of
`X` into open and closed subschemes and the classes are assembled over it by Stacks 0FDZ. That
assembly is available for a single module of non-constant rank — it is
`Stacks.Chow.rankLocusAssembly` and `Stacks.Chow.chernClassArbitraryRank`, Stacks 0ESW — but not
for a complex, whose decomposition is indexed by the rank function of all the terms at once, and
the locally bounded case of Stacks 0ESZ is not treated in this file; it is
`Stacks.Chow.complexChern` and `Stacks.Chow.powerSumComplex`.

The other half of the generalization *is* delivered: no rank is assumed constant anywhere below.
The total Chern class datum `Stacks.Chow.TotalChernClassSeries` assigns a series to every module,
and that is how the arbitrary-rank Chern classes of Stacks 0ESW enter.

### Why the Chern classes are data

In this file the total Chern class `c(ℰ)` of Stacks 0B7H and the multiplication of `A^*(X)` of
Stacks 0FE0 are carried rather than taken from their constructions (which the definitions
`Stacks.Chow.complexChern` and `Stacks.Chow.powerSumComplex` use), exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup`: the parameters here are a
`Stacks.Chow.ChowCohomologySeriesRing` and a `Stacks.Chow.TotalChernClassSeries`, whose field
`ch_shortExact` is the Whitney sum formula of Stacks 02UI in the product form the construction
consumes. For the power sums the same device is used, as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter`: the parameter
`Stacks.Chow.PowerSumClassRule` carries `P_p(ℰ)` together with its additivity, Stacks 0F9C.
What is *constructed* here is the alternating class, the formulas, and the independence.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0ESR](https://stacks.math.columbia.edu/tag/0ESR)
* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
* [Stacks Project, Tag 00O3](https://stacks.math.columbia.edu/tag/00O3)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Stacks.Chow

/-! ### An alternating telescope -/

/-- **The alternating telescope.** For a family `g` indexed by the integers, the alternating sum
of `g n + g (n + 1)` over a range of degrees collapses to its two ends. This is what makes the
images of the differentials disappear from the alternating class of a complex. -/
theorem sum_negOnePow_smul_add_succ {A : Type*} [AddCommGroup A] (g : ℤ → A) (a : ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1),
        ((a + (i : ℤ)).negOnePow : ℤ) • (g (a + (i : ℤ)) + g (a + (i : ℤ) + 1)) =
      (a.negOnePow : ℤ) • g a - ((a + (k : ℤ) + 1).negOnePow : ℤ) • g (a + (k : ℤ) + 1) := by
  have h (n : ℤ) : ((n + 1).negOnePow : ℤ) = -(n.negOnePow : ℤ) := by
    rw [Int.negOnePow_succ, Units.val_neg]
  induction k with
  | zero =>
      rw [Finset.sum_range_one]
      simp only [Nat.cast_zero, add_zero]
      rw [h a, neg_smul, sub_neg_eq_add, smul_add]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [e1, show a + ((k : ℤ) + 1) = a + (k : ℤ) + 1 from (add_assoc a (k : ℤ) 1).symm]
      rw [h (a + (k : ℤ) + 1), neg_smul, sub_neg_eq_add, smul_add]
      abel

/-! ### The alternating class of a complex in the Grothendieck group -/

variable {X : Scheme.{u}}

/-- **The alternating class `∑_n (-1)^n [ℰ^n]` of a complex** in the Grothendieck group
`K_0(Vect(X))` of Stacks 0FDK, for a complex bounded in the degrees `a, …, a + k`. The sign is
that of the degree, as in the source, not that of the position in the range. -/
def alternatingKClass (X : Scheme.{u}) (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) :
    AlgebraicGeometry.VectorBundleKZero X :=
  ∑ i ∈ Finset.range (k + 1), ((a + (i : ℤ)).negOnePow : ℤ) •
    AlgebraicGeometry.VectorBundleKZero.classOf X (P.X (a + (i : ℤ)))

/-- A sheaf of modules which is a zero object has class zero in `K_0(Vect(X))`: it is isomorphic
to the zero module, which is finite locally free, so the defining relations identify the two
classes, and the class of the zero module vanishes. -/
theorem _root_.AlgebraicGeometry.VectorBundleKZero.classOf_eq_zero_of_isZero {M : X.Modules}
    (h : IsZero M) : AlgebraicGeometry.VectorBundleKZero.classOf X M = 0 :=
  (AlgebraicGeometry.VectorBundleKZero.classOf_eq_of_iso h.isoZero.symm
    (AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_zero X)).symm.trans
      (AlgebraicGeometry.VectorBundleKZero.classOf_zero X)

/-- The alternating class of a complex, written as a sum over the window of degrees `a, …, a + k`
itself rather than over the range of offsets from `a`. -/
theorem alternatingKClass_eq_sum_Icc (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) :
    alternatingKClass X P a k =
      ∑ n ∈ Finset.Icc a (a + (k : ℤ)),
        ((n.negOnePow : ℤ) • AlgebraicGeometry.VectorBundleKZero.classOf X (P.X n)) := by
  rw [alternatingKClass]
  refine Finset.sum_nbij' (fun i : ℕ => a + (i : ℤ)) (fun n : ℤ => (n - a).toNat)
    (fun i hi => ?_) (fun n hn => ?_) (fun i hi => ?_) (fun n hn => ?_) (fun i _ => rfl)
  · rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    omega
  · rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  · omega
  · rw [Finset.mem_Icc] at hn
    omega

/-- **The alternating class does not depend on the chosen window.** If the terms of `P` vanish
outside the degrees `a, …, a + k`, then enlarging the window to any `a', …, a' + k'` containing
it leaves `∑_n (-1)^n [ℰ^n]` unchanged, because the extra terms are zero objects and so have
class zero in `K_0(Vect(X))`. This is what makes the classes of Stacks 0ESZ well defined for a
complex which is merely bounded, with no preferred window. -/
theorem alternatingKClass_eq_of_isZero_outside (P : CochainComplex X.Modules ℤ) {a a' : ℤ}
    {k k' : ℕ} (hbot : a' ≤ a) (htop : a + (k : ℤ) ≤ a' + (k' : ℤ))
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) :
    alternatingKClass X P a k = alternatingKClass X P a' k' := by
  rw [alternatingKClass_eq_sum_Icc, alternatingKClass_eq_sum_Icc]
  refine Finset.sum_subset (fun n hn => ?_) (fun n _ hn => ?_)
  · rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Icc]
    omega
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rw [AlgebraicGeometry.VectorBundleKZero.classOf_eq_zero_of_isZero (hvanish n hn), smul_zero]

/-- **Any two windows containing the support of a complex give the same alternating class.** If
the terms of `P` vanish outside the degrees `b, …, b + m`, then every window `a, …, a + k`
containing `b, …, b + m` computes one and the same class `∑_n (-1)^n [ℰ^n]` in `K_0(Vect(X))`.
So `Stacks.Chow.alternatingKClass`, and with it every class built from it, depends only on the
complex and not on the window chosen to present it. -/
theorem alternatingKClass_eq_of_isZero_outside_of_subset (P : CochainComplex X.Modules ℤ)
    {b : ℤ} {m : ℕ} (hvanish : ∀ n : ℤ, (n < b ∨ b + (m : ℤ) < n) → IsZero (P.X n))
    {a a' : ℤ} {k k' : ℕ} (hbot : a ≤ b) (htop : b + (m : ℤ) ≤ a + (k : ℤ))
    (hbot' : a' ≤ b) (htop' : b + (m : ℤ) ≤ a' + (k' : ℤ)) :
    alternatingKClass X P a k = alternatingKClass X P a' k' :=
  (alternatingKClass_eq_of_isZero_outside P hbot htop hvanish).symm.trans
    (alternatingKClass_eq_of_isZero_outside P hbot' htop' hvanish)

/-- **The degreewise exactness data of a complex of finite locally free modules.** For a complex
`P` bounded in the degrees `a, …, a + k`: each term is finite locally free, and so are the
kernel `Ker(d^n)` and the image `Im(d^{n-1})` of its differentials, which sit in the short exact
sequences

  `0 ⟶ Ker(d^n) ⟶ ℰ^n ⟶ Im(d^n) ⟶ 0`.

The two images at the ends of the range of degrees vanish; for a complex whose terms vanish
outside `a, …, a + k` that is automatic. Finite local freeness of the kernels and images is what
the source takes from Stacks 0F8J, under the hypothesis that the cohomology modules are perfect
of tor dimension at most one; it is carried here. -/
structure BoundedComplexSplitting (X : Scheme.{u}) (P : CochainComplex X.Modules ℤ)
    (a : ℤ) (k : ℕ) where
  /-- The kernel `Ker(d^n)` of the differential out of degree `n`. -/
  cocycles : ℤ → X.Modules
  /-- The image `Im(d^{n-1})` of the differential into degree `n`. -/
  coboundaries : ℤ → X.Modules
  /-- The terms of the complex are finite locally free. -/
  isFiniteLocallyFree_X : ∀ n : ℤ,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n)
  /-- The kernels are finite locally free: Stacks 0F8J. -/
  isFiniteLocallyFree_cocycles : ∀ n : ℤ,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (cocycles n)
  /-- The images are finite locally free: Stacks 0F8J. -/
  isFiniteLocallyFree_coboundaries : ∀ n : ℤ,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (coboundaries n)
  /-- The inclusion of the kernel into the term. -/
  cocyclesι : ∀ n : ℤ, cocycles n ⟶ P.X n
  /-- The surjection of the term onto the image of its differential. -/
  toCoboundaries : ∀ n : ℤ, P.X n ⟶ coboundaries (n + 1)
  /-- The inclusion of the image into the term. -/
  coboundariesι : ∀ n : ℤ, coboundaries n ⟶ P.X n
  /-- The kernel includes as a subobject. -/
  mono_cocyclesι : ∀ n : ℤ, Mono (cocyclesι n)
  /-- The term surjects onto the image. -/
  epi_toCoboundaries : ∀ n : ℤ, Epi (toCoboundaries n)
  /-- The image includes as a subobject. -/
  mono_coboundariesι : ∀ n : ℤ, Mono (coboundariesι n)
  /-- The composite of the two maps of the degreewise sequence is zero. -/
  cocyclesι_comp_toCoboundaries : ∀ n : ℤ, cocyclesι n ≫ toCoboundaries n = 0
  /-- The degreewise sequence `0 ⟶ Ker(d^n) ⟶ ℰ^n ⟶ Im(d^n) ⟶ 0` is exact. -/
  exact : ∀ n : ℤ,
    (ShortComplex.mk (cocyclesι n) (toCoboundaries n) (cocyclesι_comp_toCoboundaries n)).Exact
  /-- The surjection onto the image followed by its inclusion is the differential: this is what
  makes `coboundaries (n + 1)` the image of `d^n` and `cocycles n` its kernel. -/
  toCoboundaries_comp_coboundariesι : ∀ n : ℤ,
    toCoboundaries n ≫ coboundariesι (n + 1) = P.d n (n + 1)
  /-- Nothing enters the bottom degree of the range. -/
  isZero_coboundaries_bot : IsZero (coboundaries a)
  /-- Nothing leaves the top degree of the range. -/
  isZero_coboundaries_top : IsZero (coboundaries (a + (k : ℤ) + 1))

namespace BoundedComplexSplitting

variable {P : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}

/-- A finite locally free module which is a zero object has class zero in `K_0(Vect(X))`.

Finite local freeness is not needed: this is
`AlgebraicGeometry.VectorBundleKZero.classOf_eq_zero_of_isZero`, which assumes only that the
module is a zero object. The hypothesis is kept here because consumers in this namespace already
have it to hand. -/
theorem classOf_eq_zero_of_isZero (M : X.Modules)
    (_hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (h : IsZero M) : AlgebraicGeometry.VectorBundleKZero.classOf X M = 0 :=
  AlgebraicGeometry.VectorBundleKZero.classOf_eq_zero_of_isZero h

/-- The class of a term of the complex splits as the class of the kernel plus the class of the
image of its differential. -/
theorem classOf_X (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    AlgebraicGeometry.VectorBundleKZero.classOf X (P.X n) =
      AlgebraicGeometry.VectorBundleKZero.classOf X (S.cocycles n) +
        AlgebraicGeometry.VectorBundleKZero.classOf X (S.coboundaries (n + 1)) := by
  have := S.mono_cocyclesι n
  have := S.epi_toCoboundaries n
  exact AlgebraicGeometry.VectorBundleKZero.classOf_shortExact (S.cocyclesι n)
    (S.toCoboundaries n) (S.cocyclesι_comp_toCoboundaries n) (S.isFiniteLocallyFree_cocycles n)
    (S.isFiniteLocallyFree_X n) (S.isFiniteLocallyFree_coboundaries (n + 1)) (S.exact n)

end BoundedComplexSplitting

/-- **The alternating class is the alternating sum of the cohomology differences.** Writing
`Z^n = Ker(d^n)` and `B^n = Im(d^{n-1})`, the degreewise sequences give
`[ℰ^n] = [Z^n] + [B^{n+1}]`, and the images telescope away, so

  `∑_n (-1)^n [ℰ^n] = ∑_n (-1)^n ([Z^n] - [B^n])`.

This is the first reduction of the proof of Stacks 0ESZ: the right hand side mentions the
complex only through the two-term presentations `0 ⟶ B^n ⟶ Z^n ⟶ H^n ⟶ 0` of its cohomology
modules. -/
theorem alternatingKClass_eq_sum_sub (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (S : BoundedComplexSplitting X P a k) :
    alternatingKClass X P a k =
      ∑ i ∈ Finset.range (k + 1), ((a + (i : ℤ)).negOnePow : ℤ) •
        (AlgebraicGeometry.VectorBundleKZero.classOf X (S.cocycles (a + (i : ℤ))) -
          AlgebraicGeometry.VectorBundleKZero.classOf X (S.coboundaries (a + (i : ℤ)))) := by
  have htel : ∑ i ∈ Finset.range (k + 1), ((a + (i : ℤ)).negOnePow : ℤ) •
      (AlgebraicGeometry.VectorBundleKZero.classOf X (S.coboundaries (a + (i : ℤ))) +
        AlgebraicGeometry.VectorBundleKZero.classOf X
          (S.coboundaries (a + (i : ℤ) + 1))) = 0 := by
    rw [sum_negOnePow_smul_add_succ
      (fun n => AlgebraicGeometry.VectorBundleKZero.classOf X (S.coboundaries n)) a k,
      AlgebraicGeometry.VectorBundleKZero.classOf_eq_zero_of_isZero S.isZero_coboundaries_bot,
      AlgebraicGeometry.VectorBundleKZero.classOf_eq_zero_of_isZero S.isZero_coboundaries_top,
      smul_zero, smul_zero, sub_zero]
  have hsplit : ∀ i ∈ Finset.range (k + 1), ((a + (i : ℤ)).negOnePow : ℤ) •
      AlgebraicGeometry.VectorBundleKZero.classOf X (P.X (a + (i : ℤ))) =
      ((a + (i : ℤ)).negOnePow : ℤ) •
          (AlgebraicGeometry.VectorBundleKZero.classOf X (S.cocycles (a + (i : ℤ))) -
            AlgebraicGeometry.VectorBundleKZero.classOf X (S.coboundaries (a + (i : ℤ)))) +
        ((a + (i : ℤ)).negOnePow : ℤ) •
          (AlgebraicGeometry.VectorBundleKZero.classOf X (S.coboundaries (a + (i : ℤ))) +
            AlgebraicGeometry.VectorBundleKZero.classOf X
              (S.coboundaries (a + (i : ℤ) + 1))) := by
    intro i _
    rw [S.classOf_X (a + (i : ℤ)), ← smul_add]
    congr 1
    abel
  rw [alternatingKClass, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, htel, add_zero]

/-- **An acyclic complex has zero alternating class.** If every kernel `Ker(d^n)` is isomorphic
to the image `Im(d^{n-1})`, that is if the complex is exact, then `∑_n (-1)^n [ℰ^n] = 0`. -/
theorem alternatingKClass_eq_zero_of_acyclic (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (S : BoundedComplexSplitting X P a k)
    (hac : ∀ n : ℤ, Nonempty (S.cocycles n ≅ S.coboundaries n)) :
    alternatingKClass X P a k = 0 := by
  rw [alternatingKClass_eq_sum_sub P a k S]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [AlgebraicGeometry.VectorBundleKZero.classOf_eq_of_iso (hac (a + (i : ℤ))).some
    (S.isFiniteLocallyFree_cocycles (a + (i : ℤ))), sub_self, smul_zero]

/-! ### Schanuel's lemma in the Grothendieck group -/

/-- **Schanuel's lemma in `K_0(Vect(X))`**, the last paragraph of the proof of Stacks 0ESZ. Let
`0 ⟶ ℰ' ⟶ ℰ ⟶ 𝒬 ⟶ 0` and `0 ⟶ ℱ' ⟶ ℱ ⟶ 𝒬 ⟶ 0` be two presentations of one module `𝒬` by
finite locally free modules. Schanuel's lemma, Stacks 00O3, produces a finite locally free `𝒢`
with `0 ⟶ ℰ' ⟶ 𝒢 ⟶ ℱ ⟶ 0` and `0 ⟶ ℱ' ⟶ 𝒢 ⟶ ℰ ⟶ 0`; given those two sequences, the difference
`[ℰ] - [ℰ']` is `[ℱ] - [ℱ']`, so it depends only on `𝒬`.

The two sequences are the hypothesis: Stacks 00O3 is a statement about modules over a ring and
the diagram chase producing `𝒢` as the kernel of `ℰ ⊕ ℱ ⟶ 𝒬` is not formalized here for
modules on a scheme. -/
theorem classOf_sub_eq_of_schanuel {Ecy Ebd Fcy Fbd M : X.Modules}
    (hEcy : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) Ecy)
    (hEbd : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) Ebd)
    (hFcy : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) Fcy)
    (hFbd : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) Fbd)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (f₁ : Ebd ⟶ M) (g₁ : M ⟶ Fcy) (w₁ : f₁ ≫ g₁ = 0) (hf₁ : Mono f₁) (hg₁ : Epi g₁)
    (hex₁ : (ShortComplex.mk f₁ g₁ w₁).Exact)
    (f₂ : Fbd ⟶ M) (g₂ : M ⟶ Ecy) (w₂ : f₂ ≫ g₂ = 0) (hf₂ : Mono f₂) (hg₂ : Epi g₂)
    (hex₂ : (ShortComplex.mk f₂ g₂ w₂).Exact) :
    AlgebraicGeometry.VectorBundleKZero.classOf X Ecy -
        AlgebraicGeometry.VectorBundleKZero.classOf X Ebd =
      AlgebraicGeometry.VectorBundleKZero.classOf X Fcy -
        AlgebraicGeometry.VectorBundleKZero.classOf X Fbd := by
  have := hf₁
  have := hg₁
  have := hf₂
  have := hg₂
  have h₁ := AlgebraicGeometry.VectorBundleKZero.classOf_shortExact f₁ g₁ w₁ hEbd hM hFcy hex₁
  have h₂ := AlgebraicGeometry.VectorBundleKZero.classOf_shortExact f₂ g₂ w₂ hFbd hM hEcy hex₂
  have h := h₁.symm.trans h₂
  have hC : AlgebraicGeometry.VectorBundleKZero.classOf X Fcy =
      AlgebraicGeometry.VectorBundleKZero.classOf X Fbd +
        AlgebraicGeometry.VectorBundleKZero.classOf X Ecy -
          AlgebraicGeometry.VectorBundleKZero.classOf X Ebd := by
    rw [← h]; abel
  rw [hC]
  abel

/-! ### Two complexes with the same cohomology -/

/-- **Two complexes of finite locally free modules with the same cohomology modules**, together
with the comparison datum Schanuel's lemma produces. For each degree `n`:

* the cohomology module `H^n`, presented as `Z^n_P/B^n_P` by the first complex and as
  `Z^n_Q/B^n_Q` by the second; and
* a finite locally free module `𝒢^n` with short exact sequences
  `0 ⟶ B^n_P ⟶ 𝒢^n ⟶ Z^n_Q ⟶ 0` and `0 ⟶ B^n_Q ⟶ 𝒢^n ⟶ Z^n_P ⟶ 0`.

This is what the proof of Stacks 0ESZ extracts from an isomorphism `ℰ^• ≅ ℱ^•` in `D(𝒪_X)`,
after the reductions of Stacks 02UC and Stacks 0ESR; the module `𝒢^n` is the one Schanuel's
lemma, Stacks 00O3, builds as the kernel of `Z^n_P ⊕ Z^n_Q ⟶ H^n`. Only the last two sequences
are used below; the presentations of `H^n` are what make this datum say that the two complexes
have the same cohomology. -/
structure ComplexCohomologyComparison {P Q : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k) where
  /-- The common cohomology module in degree `n`. It is not assumed finite locally free; in the
  source it is only perfect of tor dimension at most one, which is why Schanuel's lemma is
  needed. -/
  cohomology : ℤ → X.Modules
  /-- The inclusion of the image into the kernel, for the first complex. -/
  firstCoboundariesι : ∀ n : ℤ, S.coboundaries n ⟶ S.cocycles n
  /-- That inclusion is compatible with the inclusions into the term of the complex. -/
  firstCoboundariesι_comp : ∀ n : ℤ,
    firstCoboundariesι n ≫ S.cocyclesι n = S.coboundariesι n
  /-- The projection of the kernel onto the cohomology, for the first complex. -/
  firstπ : ∀ n : ℤ, S.cocycles n ⟶ cohomology n
  /-- The first presentation is a complex. -/
  firstw : ∀ n : ℤ, firstCoboundariesι n ≫ firstπ n = 0
  /-- The image includes as a subobject of the kernel. -/
  mono_firstCoboundariesι : ∀ n : ℤ, Mono (firstCoboundariesι n)
  /-- The kernel surjects onto the cohomology. -/
  epi_firstπ : ∀ n : ℤ, Epi (firstπ n)
  /-- `H^n` is the cohomology of the first complex: `0 ⟶ B^n_P ⟶ Z^n_P ⟶ H^n ⟶ 0` is exact. -/
  firstExact : ∀ n : ℤ,
    (ShortComplex.mk (firstCoboundariesι n) (firstπ n) (firstw n)).Exact
  /-- The inclusion of the image into the kernel, for the second complex. -/
  secondCoboundariesι : ∀ n : ℤ, T.coboundaries n ⟶ T.cocycles n
  /-- That inclusion is compatible with the inclusions into the term of the complex. -/
  secondCoboundariesι_comp : ∀ n : ℤ,
    secondCoboundariesι n ≫ T.cocyclesι n = T.coboundariesι n
  /-- The projection of the kernel onto the cohomology, for the second complex. -/
  secondπ : ∀ n : ℤ, T.cocycles n ⟶ cohomology n
  /-- The second presentation is a complex. -/
  secondw : ∀ n : ℤ, secondCoboundariesι n ≫ secondπ n = 0
  /-- The image includes as a subobject of the kernel. -/
  mono_secondCoboundariesι : ∀ n : ℤ, Mono (secondCoboundariesι n)
  /-- The kernel surjects onto the cohomology. -/
  epi_secondπ : ∀ n : ℤ, Epi (secondπ n)
  /-- `H^n` is the cohomology of the second complex: `0 ⟶ B^n_Q ⟶ Z^n_Q ⟶ H^n ⟶ 0` is exact. -/
  secondExact : ∀ n : ℤ,
    (ShortComplex.mk (secondCoboundariesι n) (secondπ n) (secondw n)).Exact
  /-- The module Schanuel's lemma produces from the two presentations of `H^n`. -/
  schanuel : ℤ → X.Modules
  /-- It is finite locally free. -/
  isFiniteLocallyFree_schanuel : ∀ n : ℤ,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (schanuel n)
  /-- The inclusion of the first image into the Schanuel module. -/
  firstSchanuelι : ∀ n : ℤ, S.coboundaries n ⟶ schanuel n
  /-- The surjection of the Schanuel module onto the second kernel. -/
  firstSchanuelπ : ∀ n : ℤ, schanuel n ⟶ T.cocycles n
  /-- The first Schanuel sequence is a complex. -/
  firstSchanuelw : ∀ n : ℤ, firstSchanuelι n ≫ firstSchanuelπ n = 0
  /-- The first image includes as a subobject. -/
  mono_firstSchanuelι : ∀ n : ℤ, Mono (firstSchanuelι n)
  /-- The Schanuel module surjects onto the second kernel. -/
  epi_firstSchanuelπ : ∀ n : ℤ, Epi (firstSchanuelπ n)
  /-- `0 ⟶ B^n_P ⟶ 𝒢^n ⟶ Z^n_Q ⟶ 0` is exact. -/
  firstSchanuelExact : ∀ n : ℤ,
    (ShortComplex.mk (firstSchanuelι n) (firstSchanuelπ n) (firstSchanuelw n)).Exact
  /-- The inclusion of the second image into the Schanuel module. -/
  secondSchanuelι : ∀ n : ℤ, T.coboundaries n ⟶ schanuel n
  /-- The surjection of the Schanuel module onto the first kernel. -/
  secondSchanuelπ : ∀ n : ℤ, schanuel n ⟶ S.cocycles n
  /-- The second Schanuel sequence is a complex. -/
  secondSchanuelw : ∀ n : ℤ, secondSchanuelι n ≫ secondSchanuelπ n = 0
  /-- The second image includes as a subobject. -/
  mono_secondSchanuelι : ∀ n : ℤ, Mono (secondSchanuelι n)
  /-- The Schanuel module surjects onto the first kernel. -/
  epi_secondSchanuelπ : ∀ n : ℤ, Epi (secondSchanuelπ n)
  /-- `0 ⟶ B^n_Q ⟶ 𝒢^n ⟶ Z^n_P ⟶ 0` is exact. -/
  secondSchanuelExact : ∀ n : ℤ,
    (ShortComplex.mk (secondSchanuelι n) (secondSchanuelπ n) (secondSchanuelw n)).Exact

/-- **The alternating class in `K_0(Vect(X))` depends only on the cohomology.** For two complexes
of finite locally free modules whose kernels and images are finite locally free and whose
cohomology modules agree degreewise, the alternating classes agree. This is the whole content of
Stacks 0ESZ: the three characteristic classes of the source are functions of this one class. -/
theorem alternatingKClass_eq_of_cohomologyComparison {P Q : CochainComplex X.Modules ℤ} {a : ℤ}
    {k : ℕ} (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (cmp : ComplexCohomologyComparison S T) :
    alternatingKClass X P a k = alternatingKClass X Q a k := by
  rw [alternatingKClass_eq_sum_sub P a k S, alternatingKClass_eq_sum_sub Q a k T]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact classOf_sub_eq_of_schanuel (S.isFiniteLocallyFree_cocycles (a + (i : ℤ)))
    (S.isFiniteLocallyFree_coboundaries (a + (i : ℤ)))
    (T.isFiniteLocallyFree_cocycles (a + (i : ℤ)))
    (T.isFiniteLocallyFree_coboundaries (a + (i : ℤ)))
    (cmp.isFiniteLocallyFree_schanuel (a + (i : ℤ)))
    (cmp.firstSchanuelι (a + (i : ℤ))) (cmp.firstSchanuelπ (a + (i : ℤ)))
    (cmp.firstSchanuelw (a + (i : ℤ))) (cmp.mono_firstSchanuelι (a + (i : ℤ)))
    (cmp.epi_firstSchanuelπ (a + (i : ℤ))) (cmp.firstSchanuelExact (a + (i : ℤ)))
    (cmp.secondSchanuelι (a + (i : ℤ))) (cmp.secondSchanuelπ (a + (i : ℤ)))
    (cmp.secondSchanuelw (a + (i : ℤ))) (cmp.mono_secondSchanuelι (a + (i : ℤ)))
    (cmp.epi_secondSchanuelπ (a + (i : ℤ))) (cmp.secondSchanuelExact (a + (i : ℤ)))

/-! ### The total Chern class of a complex -/

section TotalChernClass

open ChowCohomologySeriesRing

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] {R : ChowCohomologySeriesRing C Gy sX}

/-- **Stacks 0ESZ, carried form.** The total Chern class `c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n}` of a complex
of finite locally free modules bounded in the degrees `a, …, a + k`, as an element of the group of
series with constant term `1` inside `∏_{p ≥ 0} A^p(X)`; the negative exponents are the formal
inverses of Stacks 0FEL. No rank is assumed constant. -/
def totalChernClassComplex (D : TotalChernClassSeries C Gy sX R)
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) : UnitalSeries R :=
  Additive.toMul (chernClassKGroupHom D (alternatingKClass X P a k))

/-- **Stacks 0ESZ, carried form.** The total Chern class of a complex is the alternating product
`∏_n c(ℰ^n)^{(-1)^n}` of the total Chern classes of its terms, which is the formula of the source.
-/
theorem totalChernClassComplex_eq_prod (D : TotalChernClassSeries C Gy sX R)
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) :
    totalChernClassComplex C Gy sX D P a k =
      ∏ i ∈ Finset.range (k + 1),
        (⟨D.ch (P.X (a + (i : ℤ))), D.ch_apply_zero (P.X (a + (i : ℤ)))⟩ : UnitalSeries R) ^
          ((a + (i : ℤ)).negOnePow : ℤ) := by
  rw [totalChernClassComplex, alternatingKClass, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zsmul, toMul_zsmul, chernClassKGroupHom_classOf]
  rfl

/-- **Stacks 0ESZ, carried form.** The total Chern class of a complex of finite locally free modules
depends only on the cohomology modules of the complex. Two complexes representing the same object of
`D(𝒪_X)` have the same cohomology modules, and this is the form in which the independence of the
representative is delivered here; see the implementation notes of this file. The statement for two
complexes isomorphic in `D(𝒪_X)`, with no carried datum, is `Stacks.Chow.complexChern_eq_of_iso`. -/
theorem totalChernClassComplex_eq_of_cohomologyComparison (D : TotalChernClassSeries C Gy sX R)
    {P Q : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (cmp : ComplexCohomologyComparison S T) :
    totalChernClassComplex C Gy sX D P a k = totalChernClassComplex C Gy sX D Q a k := by
  rw [totalChernClassComplex, totalChernClassComplex,
    alternatingKClass_eq_of_cohomologyComparison S T cmp]

end TotalChernClass

/-! ### The power sums and the Chern character of a complex -/

section PowerSum

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- **The power sum classes `P_p(ℰ)` of a finite locally free module, as a datum.** For each
module a family of classes `P_p(ℰ) ∈ A^p(X)`, vanishing off the finite locally free modules and
additive on their short exact sequences, which is Stacks 0F9C.

The classes themselves are the evaluated power sums `P_p(c_1(ℰ), …, c_p(ℰ))` of Stacks 0F9B;
they are not constructed in this repository, the multiplication of `A^*(X)` being Stacks 0FE0,
so they are carried, exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter`. The normalisation on
a module that is not finite locally free matches `AlgebraicGeometry.VectorBundleKZero.classOf`
and is not a mathematical assumption. -/
structure PowerSumClassRule (C : ChowSituation.{u}) (Gy : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] where
  /-- The family `(P_p(ℰ))_{p ≥ 0}` of classes of a module. -/
  cls : X.Modules → ∀ p : ℕ, chowCohomologyComponent C Gy sX (p : ℤ)
  /-- A module that is not finite locally free gets the zero family. -/
  cls_eq_zero_of_not_isFiniteLocallyFree : ∀ M : X.Modules,
    ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M → cls M = 0
  /-- **Stacks 0F9C.** A short exact sequence `0 ⟶ ℰ_1 ⟶ ℰ_2 ⟶ ℰ_3 ⟶ 0` of finite locally free
  modules gives `P_p(ℰ_2) = P_p(ℰ_1) + P_p(ℰ_3)`. -/
  cls_shortExact : ∀ {E F H : X.Modules} (f : E ⟶ F) (g : F ⟶ H) (w : f ≫ g = 0),
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) H →
          Mono f → Epi g → (ShortComplex.mk f g w).Exact → cls F = cls E + cls H

/-- The power sum classes as a homomorphism out of `K_0(Vect(X))`: the additivity of Stacks 0F9C
is exactly the relation defining the Grothendieck group. -/
def powerSumKGroupHom (W : PowerSumClassRule C Gy sX) :
    AlgebraicGeometry.VectorBundleKZero X →+
      ∀ p : ℕ, chowCohomologyComponent C Gy sX (p : ℤ) :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom W.cls
    W.cls_eq_zero_of_not_isFiniteLocallyFree
    fun f g w hE hF hH hmono hepi hex => W.cls_shortExact f g w hE hF hH hmono hepi hex

/-- The power sum homomorphism on the class of a module is the power sum family of that
module. -/
theorem powerSumKGroupHom_classOf (W : PowerSumClassRule C Gy sX) (M : X.Modules) :
    powerSumKGroupHom C Gy sX W (AlgebraicGeometry.VectorBundleKZero.classOf X M) = W.cls M := by
  rw [powerSumKGroupHom, AlgebraicGeometry.VectorBundleKZero.liftAddHom_classOf]

/-- **Stacks 0ESZ, carried form.** The class `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n) ∈ A^p(X)` of a complex
of finite locally free modules bounded in the degrees `a, …, a + k`. No rank is assumed constant. -/
def powerSumClassComplex (W : PowerSumClassRule C Gy sX) (P : CochainComplex X.Modules ℤ)
    (a : ℤ) (k : ℕ) (p : ℕ) : chowCohomologyComponent C Gy sX (p : ℤ) :=
  powerSumKGroupHom C Gy sX W (alternatingKClass X P a k) p

/-- **Stacks 0ESZ, carried form.** The class `P_p` of a complex is the alternating sum of the
classes `P_p` of its terms, which is the formula of the source. -/
theorem powerSumClassComplex_eq_sum (W : PowerSumClassRule C Gy sX)
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) (p : ℕ) :
    powerSumClassComplex C Gy sX W P a k p =
      ∑ i ∈ Finset.range (k + 1),
        ((a + (i : ℤ)).negOnePow : ℤ) • W.cls (P.X (a + (i : ℤ))) p := by
  rw [powerSumClassComplex, alternatingKClass, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, powerSumKGroupHom_classOf]

/-- **Stacks 0ESZ, carried form.** The class `P_p` of a complex of finite locally free modules
depends only on the cohomology modules of the complex. Two complexes representing the same object of
`D(𝒪_X)` have the same cohomology modules, and this is the form in which the independence of the
representative is delivered here; see the implementation notes of this file. The statement for two
complexes isomorphic in `D(𝒪_X)`, with no carried datum, is `Stacks.Chow.powerSumComplex_eq_of_iso`.
-/
theorem powerSumClassComplex_eq_of_cohomologyComparison (W : PowerSumClassRule C Gy sX)
    {P Q : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (cmp : ComplexCohomologyComparison S T) (p : ℕ) :
    powerSumClassComplex C Gy sX W P a k p = powerSumClassComplex C Gy sX W Q a k p := by
  rw [powerSumClassComplex, powerSumClassComplex,
    alternatingKClass_eq_of_cohomologyComparison S T cmp]

/-- **Stacks 0ESZ, carried form.** The degree-`p` component `ch_p(ℰ^•) = P_p(ℰ^•)/p! ∈ A^p(X) ⊗ 𝐐`
of the Chern character of a complex of finite locally free modules bounded in the degrees
`a, …, a + k`. -/
def chernCharacterComplexComponent (W : PowerSumClassRule C Gy sX)
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) (p : ℕ) :
    rationalChowCohomologyComponent C Gy sX (p : ℤ) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumClassComplex C Gy sX W P a k p

/-- **Stacks 0ESZ, carried form.** The Chern character of a complex of finite locally free modules
depends only on the cohomology modules of the complex. Two complexes representing the same object of
`D(𝒪_X)` have the same cohomology modules, and this is the form in which the independence of the
representative is delivered here; see the implementation notes of this file. The statement for two
complexes isomorphic in `D(𝒪_X)`, with no carried datum, is
`Stacks.Chow.chernCharacterComplex_eq_of_iso`. -/
theorem chernCharacterComplexComponent_eq_of_cohomologyComparison (W : PowerSumClassRule C Gy sX)
    {P Q : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (cmp : ComplexCohomologyComparison S T) (p : ℕ) :
    chernCharacterComplexComponent C Gy sX W P a k p =
      chernCharacterComplexComponent C Gy sX W Q a k p := by
  rw [chernCharacterComplexComponent, chernCharacterComplexComponent,
    powerSumClassComplex_eq_of_cohomologyComparison C Gy sX W S T cmp p]

end PowerSum

end Stacks.Chow

end

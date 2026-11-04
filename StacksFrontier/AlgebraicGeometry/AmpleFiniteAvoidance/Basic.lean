module

public import StacksFrontier.Algebra.DirectSum.ExternalGrading
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.GradedSections.Avoidance

/-!
# One section nonvanishing on a whole finite set

Stacks Tag 09NV and part (3) of Stacks Tag 01ZY both rest on the same step: run graded prime
avoidance in the graded ring `S = Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` against the ideals of
sections vanishing at the finitely many given points. This file carries out that step.

It combines two inputs.

* **Graded prime avoidance**, `Stacks.GradedAvoidance.exists_homogeneous_pos_forall_notMem`
  (Stacks, Algebra, Lemma 10.57.6, tag 00JS): a homogeneous ideal inside the irrelevant ideal and
  inside none of finitely many homogeneous primes contains a homogeneous element of positive
  degree outside all of them.
* **`X_{st} = X_s ∩ X_t`**, `Stacks.SectionProduct.nonvanishingLocus_mul`: the product of the
  section ring is multiplicative on nonvanishing loci.

Avoidance consumes homogeneous ideals of `S`. This file constructs the ones the argument needs:
the primes `𝔭_x` of sections vanishing at `x`, and the ideal of sections whose nonvanishing locus
is confined to a prescribed subset. One definition serves both.

## Main definitions

* `Stacks.AmpleFiniteAvoidance.nvLocus`, `Stacks.AmpleFiniteAvoidance.nvOpen`: the nonvanishing
  locus `X_s` of a homogeneous element `s` of `S` of degree `n`, as a set and as an open. These
  put `Stacks.Ample.nonvanishingLocus` into the section ring's own vocabulary, where the product
  lemma lives.
* `Stacks.AmpleFiniteAvoidance.sectionsIdeal L T`: for a subset `T ⊆ X`, the ideal of elements of
  `S` all of whose homogeneous components have nonvanishing locus inside `T`. **The two ideals
  the source uses are both instances of it**: `T = ↑U` gives the ideal of sections vanishing
  outside an open `U`, and `T = {x}ᶜ` gives the prime `𝔭_x` of sections vanishing at `x`.

## Main results

* `Stacks.AmpleFiniteAvoidance.sectionsIdeal_isHomogeneous`: it is a homogeneous ideal.
* `Stacks.AmpleFiniteAvoidance.isPrime_vanishIdeal`: `𝔭_x` is prime, on the sole hypothesis that
  *some* homogeneous element does not vanish at `x`. This is where `X_{st} = X_s ∩ X_t` is spent:
  the primality of `𝔭_x` on homogeneous elements *is* that identity.
* `Stacks.AmpleFiniteAvoidance.exists_homogeneous_forall_mem_nvLocus`: **the main theorem.**
  Given a finite `E ⊆ X` and a subset `T` such that each point of `E` has *some* homogeneous
  section of positive degree not vanishing there whose nonvanishing locus is inside `T`, there is
  a *single* homogeneous section of positive degree not vanishing at *any* point of `E`, whose
  nonvanishing locus is still inside `T`.
* `Stacks.AmpleFiniteAvoidance.exists_homogeneous_forall_mem_nvLocus_of_isAmple`: the same with
  the covering hypothesis discharged from ampleness at `T = Set.univ`, so with no hypothesis
  beyond `L` ample: **a finite set of points of a scheme with an ample invertible module lies in
  a single `X_s`.**

## Implementation notes

**One ideal, two uses.** `sectionsIdeal` is indexed by an arbitrary *subset* of `X`, not by an
open. That is deliberate: the complement of a point is not open, so the prime `𝔭_x` is not an
instance of a construction indexed by opens, and stating the ideal twice would duplicate the
multiplicativity argument, which is the only non-trivial part.

**Why the ideal axioms are not routine.** Closure under multiplication by an arbitrary element is
not a one-liner, because the ring is an external direct sum and there is no formula at hand for
the components of a product. The proof instead decomposes both factors: an arbitrary element
is a finite sum of `DirectSum.of` terms (`DirectSum.sum_support_of`), and on those the product is
`DirectSum.of_mul_of`, where `Stacks.SectionProduct.nonvanishingLocus_mul_subset_right` applies.
So the argument is: the carrier is an additive subgroup; `of i a * of j b` is in it whenever
`of j b` is; every member is a finite sum of such `of j b`; hence so is every multiple.

**The commutative ring structure must be the direct sum's own.** `GradedRing` is stated for a
`Semiring` and the graded-ideal API resolves it from whatever `CommRing` is in scope. With
`Stacks.SectionRingGeometric.schemeSectionCommRing` installed as a local instance, the
`GradedRing` instance `Stacks.ExternalGrading.gradedRing` is *not found*,
and every call to avoidance fails with `failed to synthesize GradedRing`. This file therefore does
**not** install it, and lets instance search build `CommRing (Γ_*(X, L))` from
`Stacks.GradedSections.instGCommRing` through `DirectSum.commRing`. The two are the same ring —
`schemeSectionCommRing` is literally `inferInstance` for it — but only the unaided one is
syntactically the `Semiring` that `GradedRing` was proved over.

**The degree is a natural number and positivity is free.** Avoidance returns a homogeneous
element of positive degree; `Stacks.ExternalGrading.mem_summand_iff` reads that back as
`DirectSum.of _ d a` for a unique `a : Γ(X, L ^⊗ d)`, and `1 ≤ d` is `0 < d`. No separate
argument that the output is nonzero is needed, or available: the zero section is a legitimate
output of avoidance in the degenerate case `E = ∅`, and its nonvanishing locus is empty, which
satisfies the conclusion.

## References

* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 00JS](https://stacks.math.columbia.edu/tag/00JS)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)

## Consumers

This file attaches no stacks attribute. Combined with Stacks Tag 01PV
(`Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`), its main theorem
gives part (3) of Tag 01ZY,
`Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample`, and Tag 09NV,
`Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite_sections`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace DirectSum
open Stacks.Ample Stacks.GradedSections Stacks.SectionProduct

universe u

namespace Stacks.AmpleFiniteAvoidance

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules)

/-! ### The grading of the section ring -/

/-- The internal grading of the section ring `Γ_*(X, L)` of Stacks Tag 01CV: the `n`-th piece is
the image of `Γ(X, L ^⊗ n)` under the structure map of the direct sum. -/
abbrev grading : ℕ → AddSubgroup (sectionRing L) :=
  Stacks.ExternalGrading.summand (powSections L)

/-! ### Nonvanishing loci in the section ring's vocabulary -/

/-- **`X_s` for `s` a homogeneous element of the section ring of degree `n`.** This is
`Stacks.Ample.nonvanishingLocus` of the honest global section attached to `s` by the carrier
comparison `Stacks.SectionProduct.globalSection`. -/
def nvLocus {n : ℕ} (s : powSections L n) : Set X :=
  nonvanishingLocus (Stacks.TensorPowers.natTensorPow L n) (globalSection X _ s)

/-- The nonvanishing locus of the zero section is empty. -/
@[simp] theorem nvLocus_zero (n : ℕ) : nvLocus L (0 : powSections L n) = ∅ := by
  rw [nvLocus, show globalSection X (Stacks.TensorPowers.natTensorPow L n)
    (0 : powSections L n) = 0 from map_zero _, nonvanishingLocus_zero]

/-- `X_{s + t} ⊆ X_s ∪ X_t`. -/
theorem nvLocus_add_subset {n : ℕ} (s t : powSections L n) :
    nvLocus L (s + t) ⊆ nvLocus L s ∪ nvLocus L t := by
  rw [nvLocus, show globalSection X (Stacks.TensorPowers.natTensorPow L n) (s + t) =
    globalSection X _ s + globalSection X _ t from map_add _ s t]
  exact nonvanishingLocus_add_subset _ _ _

/-- **A product vanishes wherever its right factor does.** -/
theorem nvLocus_mul_subset_right {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    nvLocus L (Stacks.GradedSections.mul s t) ⊆ nvLocus L t :=
  nonvanishingLocus_mul_subset_right L n m s t

variable [IsInvertibleModule X L]

/-- `X_s` as an open subset of `X`. -/
def nvOpen {n : ℕ} (s : powSections L n) : X.Opens :=
  Stacks.NonvanishingOpen.nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L n)
    (globalSection X _ s)

/-- The underlying set of `nvOpen L s` is `nvLocus L s`. -/
@[simp] theorem coe_nvOpen {n : ℕ} (s : powSections L n) :
    (nvOpen L s : Set X) = nvLocus L s :=
  Stacks.NonvanishingOpen.coe_nonvanishingOpen X _ _

/-- **`X_{st} = X_s ∩ X_t`.** -/
theorem nvLocus_mul {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    nvLocus L (Stacks.GradedSections.mul s t) = nvLocus L s ∩ nvLocus L t :=
  nonvanishingLocus_mul L n m s t

/-! ### The ideal of sections confined to a subset -/

/-- **The ideal of elements of `Γ_*(X, L)` all of whose homogeneous components have nonvanishing
locus inside `T`.** For `T = ↑U` an open this is the ideal of sections vanishing on `X \ U`, and
for `T = {x}ᶜ` it is the ideal `𝔭_x` of sections vanishing at `x`. -/
def sectionsIdeal (T : Set X) : Ideal (sectionRing L) where
  carrier := {f | ∀ n, nvLocus L (f n) ⊆ T}
  zero_mem' n := by
    rw [show (0 : sectionRing L) n = 0 from rfl, nvLocus_zero]
    exact Set.empty_subset T
  add_mem' {f g} hf hg n := by
    rw [DFinsupp.add_apply]
    exact (nvLocus_add_subset L _ _).trans (Set.union_subset (hf n) (hg n))
  smul_mem' c f hf := by
    classical
    -- the carrier is closed under finite sums, being the carrier of an additive subgroup
    have hsum : ∀ (ι' : Type) (t : Finset ι') (F : ι' → sectionRing L),
        (∀ i ∈ t, ∀ n, nvLocus L ((F i) n) ⊆ T) → ∀ n, nvLocus L ((∑ i ∈ t, F i) n) ⊆ T := by
      intro ι' t F hF
      induction t using Finset.induction with
      | empty => intro n; rw [Finset.sum_empty, show (0 : sectionRing L) n = 0 from rfl,
          nvLocus_zero]; exact Set.empty_subset T
      | insert a t ha ih =>
          intro n
          rw [Finset.sum_insert ha, DFinsupp.add_apply]
          refine (nvLocus_add_subset L _ _).trans (Set.union_subset
            (hF a (Finset.mem_insert_self a t) n) ?_)
          exact ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) n
    -- a single `of`-term of a member is a member
    have hof : ∀ (j : ℕ) (b : powSections L j), nvLocus L b ⊆ T →
        ∀ n, nvLocus L ((DirectSum.of (powSections L) j b) n) ⊆ T := by
      intro j b hb n
      by_cases h : n = j
      · subst h; rw [DirectSum.of_eq_same]; exact hb
      · rw [DirectSum.of_eq_of_ne j n b h, nvLocus_zero]; exact Set.empty_subset T
    -- multiplying a single `of`-term by an arbitrary element keeps it a member
    have hmul : ∀ (j : ℕ) (b : powSections L j), nvLocus L b ⊆ T →
        ∀ (c : sectionRing L) (n : ℕ),
          nvLocus L ((c * DirectSum.of (powSections L) j b) n) ⊆ T := by
      intro j b hb c
      induction c using DirectSum.induction_on with
      | zero => intro n; rw [zero_mul, show (0 : sectionRing L) n = 0 from rfl, nvLocus_zero]
                exact Set.empty_subset T
      | of i a =>
          rw [DirectSum.of_mul_of, Stacks.GradedSections.gMul_def]
          exact hof _ _ ((nvLocus_mul_subset_right L a b).trans hb)
      | add c d hc hd =>
          intro n
          rw [add_mul, DFinsupp.add_apply]
          exact (nvLocus_add_subset L _ _).trans (Set.union_subset (hc n) (hd n))
    -- decompose `f` and apply the previous step summand by summand
    have hfsum : c • f = ∑ j ∈ f.support, c * DirectSum.of (powSections L) j (f j) := by
      rw [show c • f = c * f from rfl, ← Finset.mul_sum, DirectSum.sum_support_of]
    rw [hfsum]
    exact hsum ℕ f.support _ (fun j _ => hmul j (f j) (hf j) c)

variable {L}

omit [IsInvertibleModule X L] in
/-- `f` lies in `sectionsIdeal L T` if and only if every homogeneous component of `f` has
nonvanishing locus contained in `T`. -/
theorem mem_sectionsIdeal_iff {T : Set X} {f : sectionRing L} :
    f ∈ sectionsIdeal L T ↔ ∀ n, nvLocus L (f n) ⊆ T := Iff.rfl

omit [IsInvertibleModule X L] in
/-- A homogeneous element `s` lies in `sectionsIdeal L T` if and only if `X_s ⊆ T`. -/
theorem of_mem_sectionsIdeal_iff {T : Set X} {n : ℕ} {s : powSections L n} :
    DirectSum.of (powSections L) n s ∈ sectionsIdeal L T ↔ nvLocus L s ⊆ T := by
  classical
  refine ⟨fun h => by simpa only [DirectSum.of_eq_same] using h n, fun h m => ?_⟩
  by_cases hm : m = n
  · subst hm; rw [DirectSum.of_eq_same]; exact h
  · rw [DirectSum.of_eq_of_ne n m s hm, nvLocus_zero]; exact Set.empty_subset T

omit [IsInvertibleModule X L] in
/-- `sectionsIdeal L T` is monotone in `T`. -/
theorem sectionsIdeal_mono {T T' : Set X} (h : T ⊆ T') :
    sectionsIdeal L T ≤ sectionsIdeal L T' :=
  fun _ hf n => (hf n).trans h

omit [IsInvertibleModule X L] in
/-- **The ideal is homogeneous.** `sectionsIdeal L T` is a homogeneous ideal for `grading L`. -/
theorem sectionsIdeal_isHomogeneous (T : Set X) :
    (sectionsIdeal L T).IsHomogeneous (grading L) := by
  intro i f hf
  rw [Stacks.ExternalGrading.coe_decompose_apply]
  exact of_mem_sectionsIdeal_iff.mpr (hf i)

/-! ### The prime of sections vanishing at a point -/

/-- **`𝔭_x`, the ideal of sections of `Γ_*(X, L)` vanishing at `x`.** -/
abbrev vanishIdeal (L : X.Modules) [IsInvertibleModule X L] (x : X) : Ideal (sectionRing L) :=
  sectionsIdeal L {x}ᶜ

/-- A homogeneous element `s` lies in `vanishIdeal L x` if and only if `x ∉ X_s`. -/
theorem of_mem_vanishIdeal_iff {x : X} {n : ℕ} {s : powSections L n} :
    DirectSum.of (powSections L) n s ∈ vanishIdeal L x ↔ x ∉ nvLocus L s := by
  rw [of_mem_sectionsIdeal_iff, Set.subset_compl_singleton_iff]

/-- **`𝔭_x` is prime**, as soon as some homogeneous element does not vanish at `x`.

Primality on homogeneous elements is exactly `X_{st} = X_s ∩ X_t`: a product of two homogeneous
sections vanishes at `x` if and only if one of the factors does. The hypothesis rules out
`𝔭_x = ⊤`. -/
theorem isPrime_vanishIdeal {x : X}
    (hx : ∃ (n : ℕ) (s : powSections L n), x ∈ nvLocus L s) :
    (vanishIdeal L x).IsPrime := by
  obtain ⟨n₀, s₀, hs₀⟩ := hx
  refine (sectionsIdeal_isHomogeneous {x}ᶜ).isPrime_of_homogeneous_mem_or_mem ?_ ?_
  · intro htop
    exact (of_mem_vanishIdeal_iff.mp (htop ▸ Submodule.mem_top)) hs₀
  · rintro f g ⟨i, hi⟩ ⟨j, hj⟩ hfg
    obtain ⟨a, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hi
    obtain ⟨b, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hj
    rw [DirectSum.of_mul_of, Stacks.GradedSections.gMul_def] at hfg
    rw [of_mem_vanishIdeal_iff] at hfg
    rw [of_mem_vanishIdeal_iff, of_mem_vanishIdeal_iff]
    rw [nvLocus_mul] at hfg
    exact (not_and_or.mp fun h => hfg h).imp id id

/-! ### The main theorem -/

variable (L)

/-- **One homogeneous section nonvanishing on a whole finite set, confined to a prescribed
subset.** Let `E ⊆ X` be finite and `T ⊆ X` arbitrary. Suppose every point of `E` has *some*
homogeneous section of positive degree not vanishing there whose nonvanishing locus lies in `T`.
Then there is a *single* homogeneous section of positive degree whose nonvanishing locus contains
all of `E` and still lies in `T`.

This is the graded prime avoidance step of Stacks Tag 09NV and of part (3) of Stacks Tag 01ZY,
with the ideals supplied: avoidance is run on the ideal of sections confined to `T`, intersected
with the irrelevant ideal, against the primes `𝔭_x` for `x ∈ E`. -/
theorem exists_homogeneous_forall_mem_nvLocus {E : Set X} (hE : E.Finite) (T : Set X)
    (hcov : ∀ x ∈ E, ∃ (n : ℕ) (s : powSections L n), 1 ≤ n ∧ x ∈ nvLocus L s ∧
      nvLocus L s ⊆ T) :
    ∃ (d : ℕ) (a : powSections L d), 1 ≤ d ∧ E ⊆ nvLocus L a ∧ nvLocus L a ⊆ T := by
  classical
  set I : Ideal (sectionRing L) :=
    sectionsIdeal L T ⊓ (HomogeneousIdeal.irrelevant (grading L)).toIdeal with hI
  -- each chosen witness lies in `I` and outside `𝔭_x`
  have hwit : ∀ x ∈ E, ∃ y : sectionRing L, y ∈ I ∧ y ∉ vanishIdeal L x := by
    intro x hx
    obtain ⟨n, s, hn, hxs, hsT⟩ := hcov x hx
    refine ⟨DirectSum.of (powSections L) n s, ⟨of_mem_sectionsIdeal_iff.mpr hsT,
      Stacks.ExternalGrading.of_mem_irrelevant (by omega) s⟩, ?_⟩
    rw [of_mem_vanishIdeal_iff]
    exact fun h => h hxs
  obtain ⟨d, y, hd, hyd, hyI, hy⟩ :=
    Stacks.GradedAvoidance.exists_homogeneous_pos_forall_notMem (grading L)
      (fun x : X => vanishIdeal L x) hE.toFinset
      (fun x _ => sectionsIdeal_isHomogeneous _)
      (fun x hx => isPrime_vanishIdeal
        (by obtain ⟨n, s, -, hxs, -⟩ := hcov x (hE.mem_toFinset.mp hx); exact ⟨n, s, hxs⟩))
      I ((sectionsIdeal_isHomogeneous T).inf
        (HomogeneousIdeal.irrelevant (grading L)).isHomogeneous)
      inf_le_right
      (fun x hx => by
        obtain ⟨y, hyI, hy⟩ := hwit x (hE.mem_toFinset.mp hx)
        exact fun hle => hy (hle hyI))
  obtain ⟨a, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hyd
  refine ⟨d, a, hd, fun x hx => ?_, of_mem_sectionsIdeal_iff.mp hyI.1⟩
  by_contra hxa
  exact hy x (hE.mem_toFinset.mpr hx) (of_mem_vanishIdeal_iff.mpr hxa)

end Stacks.AmpleFiniteAvoidance

end

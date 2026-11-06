module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.RingTheory.AffineBlowup.Rescale
public import StacksFrontier.RingTheory.Flat.BlowupDescent
public import StacksFrontier.RingTheory.Flat.BlowupStrictTransformFlat
public import StacksFrontier.RingTheory.Flat.BlowupValuationModel

/-!
# Flattening by blowing up: assembling the steps of Stacks Tag 053I

Let `(R, 𝔪)` be a local domain with fraction field `K`, let `𝔪 ≠ 0`, let `A ⊆ K` be a valuation
ring dominating `R` and let `M` be a finite module over `P = R[x_1, …, x_n]`.  The proof of
[Stacks, Tag 053I] runs as follows.

* Over the valuation ring one kills the `A`-torsion of the base change `A[x] ⊗_P M`; the result
  `N_A` is flat over `A` and — by Nagata — finitely presented over `A[x]`.  This is
  `MvPolynomial.flat_and_finitePresentation_torsionFreeQuot_moduleBaseChange` of
  `StacksFrontier.RingTheory.Flat.BlowupValuationModel`.
* A finite presentation of `N_A` over `A[x]` involves only finitely many coefficients in `A`, and
  `A` is the directed union of the affine blowup charts of Stacks Tag 052M, so the presentation
  already lives over a single chart.
* Stacks Tag 02JO (3) then descends flatness from `A` to a chart; this is
  `Stacks.Flatness.BlowupFlattening.exists_chart_flat_quotient` of
    `StacksFrontier.RingTheory.Flat.BlowupDescent`.

This file performs that assembly, up to and including the descended flat model:
`Stacks.Flatness.BlowupFlattening.exists_chart_flat_model`.  It also collects the bridges the
  assembly needs between
the vocabulary of Stacks Tag 052M (charts as subrings of `K`) and the vocabulary of the strict
transform (the quotient model `Blowup I a`).

What is **not** here is the identification of the descended flat model with the strict transform
of `M`, and hence the conclusion `Stacks053IConclusion` of `StacksFrontier.RingTheory.Flat.Blowup`
itself; that is completed in `StacksFrontier.RingTheory.Flat.BlowupFlattenAssembly`, and see the
implementation notes for how the pieces below feed into it.  Nothing in this file carries the
`053I` tag.

## Main definitions

* `Stacks.AffineBlowup.Dominates.toValRing`, `Stacks.AffineBlowup.Dominates.algebra`: a valuation
  ring dominating
  `R` is an `R`-algebra, by restricting `algebraMap R K` to it.
* `Stacks.AffineBlowup.AdmissibleChart.blowupRingEquiv`: the ring isomorphism between the quotient
  model
  `Blowup c.I c.a` of the chart of an admissible chart `c` and the chart ring `chartRing c`, a
  subring of `K`.
* `Stacks.Flatness.BlowupFlattening.mvPolynomialBaseChangeEquiv`: the comparison `C[x] ⊗_{R[x]} M
  ≃ₗ[C] C ⊗_R M`
  between the two spellings of the base change of a module over a polynomial ring.
* `Stacks.Flatness.BlowupFlattening.relSpanOf`,
  `Stacks.Flatness.BlowupFlattening.tensorQuotEquivOf`: base change of a presentation whose
  kernel is not assumed finitely generated.
* `Stacks.Flatness.BlowupFlattening.quotTorsionEquiv`: dividing out the torsion of `F ⧸ Z` produces
  `F ⧸ L` for a
  saturated `L`.

## Main results

* `Stacks.AffineBlowup.ne_zero_of_isAdmissiblePair`,
  `Stacks.AffineBlowup.AdmissibleChart.a_ne_zero` and
  `Stacks.AffineBlowup.AdmissibleChart.isDomain_blowup`: the denominator of an admissible pair is
    nonzero,
  so the quotient model of its chart is a domain.
* `Stacks.Flatness.BlowupFlattening.exists_chart_relGenTop_eq`: **coefficient descent.** Finitely
  many vectors of
  polynomials over `A` come from a single admissible chart.
* `Stacks.Flatness.BlowupFlattening.exists_common_denominator`: finitely many polynomials over `A`
  become polynomials
  over `R` after multiplication by one nonzero element of `R`.
* `Stacks.Flatness.BlowupFlattening.exists_presentation_valuationModel`: a finite presentation of
  the valuation-ring
  model `N_A`, in the shape the descent step consumes.
* `Stacks.Flatness.BlowupFlattening.exists_chart_flat_model`: **the descended flat model.** There
  are an admissible
  chart `c`, a rank `r`, finitely many relation vectors over a chart `c₀ ≤ c`, and an
  identification of the corresponding quotient over `A` with the valuation-ring model `N_A`, such
  that the corresponding quotient over `chartRing c` is flat over `chartRing c`.
* `Stacks.Flatness.BlowupFlattening.exists_quotient_equiv_baseChange`: the scalar extension `C ⊗_R
  M` of a finite
  `R[x]`-module to an `R`-algebra `C` is `C[x]ʳ` modulo the base-changed relations.
* `Stacks.Flatness.BlowupFlattening.comap_torsion'_eq`,
  `Stacks.Flatness.BlowupFlattening.mem_of_smul_pow_mem`: a saturated relation
  submodule is the preimage of the torsion, and flatness over a domain supplies the saturation.
* `Stacks.Flatness.BlowupFlattening.nonempty_strictTransform_equiv` and
  `Stacks.Flatness.BlowupFlattening.flat_strictTransform_of_flat_quotient`: **the last step.**
    Given a `C[x]`-submodule
  `L` of `C[x]ʳ` which contains the base-changed relations of `M`, all of whose elements are
  `a`-power torsion modulo them, the strict transform of `M` on the chart is `C[x]ʳ / L`; if that
  quotient is moreover flat over `C`, the strict transform is flat over `C`.

## Implementation notes

The file stops short of Stacks Tag 053I: what is missing here is the production of the submodule
`L` of `Stacks.Flatness.BlowupFlattening.flat_strictTransform_of_flat_quotient` from the chart
  produced by
`Stacks.Flatness.BlowupFlattening.exists_chart_flat_model`, together with the remaining clauses.
  All five steps below
are **closed**, the first and fourth in
`StacksFrontier.RingTheory.Flat.BlowupStrictTransformAlg` and the second, third and fifth in
`StacksFrontier.RingTheory.Flat.BlowupFlattenAssembly`, where
  `Stacks.Flatness.BlowupFlattening.stacks053I` carries the
`053I` tag.  Precisely:

1. **Transport.** `Stacks.Flatness.BlowupFlattening.exists_chart_flat_model` gives flatness over
  `chartRing c`,
   a subring of `K`, while the strict transform is built over `Blowup c.I c.a`; the two are
   identified by `Stacks.AffineBlowup.AdmissibleChart.blowupRingEquiv`.  The relation vectors, the
     quotient
   and its flatness are carried along that ring isomorphism by
   `Stacks.Flatness.BlowupFlattening.flat_quotient_of_ringEquiv`, whose instantiation at the chart
     system is
   `Stacks.Flatness.BlowupFlattening.exists_blowupChart_flat_model`.
2. **`hZL`: the base-changed relations lie in `L`.** This needs the presentation of `N_A` to be
   the base change of one fixed surjection `π : R[x]ʳ → M`, which
   `Stacks.Flatness.BlowupFlattening.exists_presentation_valuationModel` does *not* arrange, as it
     takes an arbitrary
   surjection onto `N_A`; `Stacks.Flatness.BlowupFlattening.exists_saturating_family` replaces it,
     taking `L` to be the
   saturation of the base change of `ker π` itself.  The argument is then: an element of the
   base-changed relation submodule over the chart lies, over `A`, in the span of the descended
   relation vectors; `Stacks.Flatness.BlowupFlattening.exists_common_denominator` turns that
     representation into one
   with coefficients in `R[x]`, hence in the chart; the chart ring injects into `A`, so the
   identity descends up to a nonzero factor in `R`
   (`Stacks.Flatness.BlowupFlattening.exists_smul_mem_of_vecMap_mem_span`); and
     `Stacks.Flatness.BlowupFlattening.mem_of_smul_mem` cancels
   that factor against the flatness already obtained.  Both halves are
   `Stacks.Flatness.BlowupFlattening.le_span_and_exists_smul_mem_relSpanOf`.
3. **`hLsat`: each relation vector is `a`-power torsion.** Each descended relation vector is
   killed, modulo the base-changed relations, by a nonzero element of `A`; clearing denominators
   again replaces it by a nonzero element of `R`.  Rescaling the chart by the product of these
   (`Stacks.AffineBlowup.AdmissibleChart.rescale`, which changes the pair `(I, a)` but not the
     chart ring,
   and `Stacks.Flatness.BlowupFlattening.blowupRescaleAlgEquiv` for the induced isomorphism of
     quotient models) makes
   the denominator divisible by all of them, so the first power of `a` suffices —
   `Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_of_dvd`.  The polynomial
     case of 053I is
   `Stacks.Flatness.BlowupFlattening.exists_admissiblePair_mvPolynomial`.
4. **The rest of clause (4).**
  `Stacks.Flatness.BlowupFlattening.strictTransformAlgMvPolynomialEquiv` is the
   identification `strictTransformAlg I a R[x] ≃ₐ[C] C[x]`, giving flatness and finite
   presentation of the strict transform of `S = R[x]` over the chart
   (`Stacks.Flatness.BlowupFlattening.flat_strictTransformAlg_mvPolynomial`,
   `Stacks.Flatness.BlowupFlattening.finitePresentation_strictTransformAlg_mvPolynomial`).  Finite
     presentation of the
   strict transform of `M` over the strict transform of `S` is
   `Stacks.Flatness.BlowupFlattening.finitePresentation_strictTransform_of_fg`: the equivalence of
   `Stacks.Flatness.BlowupFlattening.nonempty_strictTransform_equiv` is `C[x]`-linear and not
     merely `C`-linear
   (`Stacks.Flatness.BlowupFlattening.strictTransformQuotEquiv_smul`, resting on
   `Stacks.Flatness.BlowupFlattening.mvPolynomialBaseChangeEquiv_symm_smul`), which transports the
     presentation of
   `C[x]ʳ / L` across it.  All four conjuncts, for a finitely generated `L` satisfying the
   hypotheses of steps 2 and 3, are
   `Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_mvPolynomial`.
5. **The finite-type reduction.** Passing from `S = R[x_1, …, x_n]` to a general finite type
   `R`-algebra `S`, by applying the polynomial case to `N = S ⊕ M` over `R[x]`, uses the ring
   theory of `StacksFrontier.RingTheory.Flat.BlowupFiniteTypeReduction` together with the
   functoriality of the strict transform algebra
     (`Stacks.Flatness.BlowupFlattening.strictTransformAlgMap`) and the
   `strictTransformAlg I a R[x]`-linear forms of the two comparison maps
   (`Stacks.Flatness.BlowupFlattening.prodLinearEquiv`,
     `Stacks.Flatness.BlowupFlattening.strictTransformAlgLinearEquiv`).

## References

* [Stacks Project, Tag 053I](https://stacks.math.columbia.edu/tag/053I)
* [Stacks Project, Tag 052M](https://stacks.math.columbia.edu/tag/052M)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-! ### Bridges between the chart of Stacks Tag 052M and the quotient model -/

namespace Stacks.AffineBlowup

section Bridge

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] {A : ValuationSubring K}

omit [IsDomain R] in
/-- **The denominator of an admissible pair is nonzero.** Condition (3) of admissibility is the
nonvanishing of the fibre ring of `R → R[I/a]` at `𝔪`, and for `a = 0` the chart is the zero
ring; this is `Stacks.AffineBlowup.not_fibreNonzero_of_zero`. -/
theorem ne_zero_of_isAdmissiblePair {I : Ideal R} {a : R} (ha : a ∈ I)
    (h : IsAdmissiblePair R A I a ha) : a ≠ 0 := by
  rintro rfl
  exact not_fibreNonzero_of_zero I ha h.2.2.1

namespace AdmissibleChart

omit [IsDomain R] in
/-- The denominator of an admissible chart is nonzero. -/
theorem a_ne_zero (c : AdmissibleChart R A) : c.a ≠ 0 :=
  ne_zero_of_isAdmissiblePair c.ha c.adm

/-- The denominator of an admissible chart lies in its ideal; this is `c.ha`, registered as an
instance so that `Blowup c.I c.a` elaborates. -/
instance instFactMem (c : AdmissibleChart R A) : Fact (c.a ∈ c.I) :=
  ⟨c.ha⟩

/-- **The two models of the chart of an admissible chart agree.** The quotient model
`Blowup c.I c.a` of `StacksFrontier.RingTheory.Blowup.Basic` is isomorphic to the chart ring
`chartRing c`, a subring of `K`: this is `Stacks.AffineBlowup.blowupEquivAffineBlowupImage'`, whose
  target
`affineBlowupImageAlg c.I c.a c.ha` has `chartRing c` as its underlying type.

This is the bridge the assembly of Stacks Tag 053I needs: the flatness-descent step speaks about
`chartRing c`, the strict transform about `Blowup c.I c.a`. -/
noncomputable def blowupRingEquiv (c : AdmissibleChart R A) : Blowup c.I c.a ≃+* chartRing c :=
  (blowupEquivAffineBlowupImage' (K := K) c.a_ne_zero).toRingEquiv

/-- The quotient model of the chart of an admissible chart is a domain, `R` being one. -/
theorem isDomain_blowup (c : AdmissibleChart R A) : IsDomain (Blowup c.I c.a) :=
  Blowup.isDomain c.I c.a c.a_ne_zero

end AdmissibleChart

/-- **A valuation ring dominating `R` is an `R`-algebra**: domination says in particular that the
image of `R` in `K` is contained in `A`, so `algebraMap R K` restricts to `A`. -/
def Dominates.toValRing (hdom : Dominates R A) : R →+* valRing A :=
  RingHom.codRestrict (algebraMap R K) A.toSubring fun r => hdom.1 ⟨r, rfl⟩

omit [IsDomain R] in
/-- The image of `r : R` under `Dominates.toValRing`, viewed in `K`, is `algebraMap R K r`. -/
@[simp]
theorem Dominates.coe_toValRing_apply (hdom : Dominates R A) (r : R) :
    ((hdom.toValRing r : valRing A) : K) = algebraMap R K r :=
  rfl

/-- The `R`-algebra structure on a valuation ring dominating `R`, given by
`Stacks.AffineBlowup.Dominates.toValRing`. -/
@[instance_reducible]
def Dominates.algebra (hdom : Dominates R A) : Algebra R (valRing A) :=
  hdom.toValRing.toAlgebra

end Bridge

end Stacks.AffineBlowup

/-! ### Assembling the descent step -/

namespace Stacks.Flatness.BlowupFlattening

open Stacks.AffineBlowup

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Descent

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] {A : ValuationSubring K}

/-- **Coefficient descent for the relation vectors.** Finitely many vectors of polynomials with
coefficients in the valuation ring `A` are the images of vectors of polynomials over a single
admissible chart.

Each such vector has finitely many coefficients, each of which lies in the ring of some chart by
`Stacks.AffineBlowup.chartToVal_surjective` (the substance of Stacks Tag 052M, whence the
hypothesis `𝔪 ≠ 0`), and the finitely many charts so obtained have a common refinement because the
chart system is directed.  This is `Stacks.Flatness.BlowupFlattening.exists_stage_map_eq_family`
  instantiated at that
system. -/
theorem exists_chart_relGenTop_eq (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (hdom : Dominates R A)
    {n r m : ℕ} (k : Fin m → (Fin r → MvPolynomial (Fin n) (valRing A))) :
    ∃ (c₀ : AdmissibleChart R A) (k₀ : Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c₀))),
      relGenTop k₀ = k := by
  have hne := AdmissibleChart.nonempty_of_maximalIdeal_ne_bot hm hdom
  have := AdmissibleChart.isDirected_of_dominates hdom
  obtain ⟨c₀⟩ := id hne
  obtain ⟨c, -, q, hq⟩ :=
    exists_stage_map_eq_family (Ar := fun c : AdmissibleChart R A => chartRing c)
      (fun c d h => chartMap c d h) (fun c => chartToVal c)
      (fun _ _ h x => chartToVal_chartMap h x) (chartToVal_surjective hm A hdom)
      (κ := Fin m × Fin r) c₀ fun z => k z.1 z.2
  exact ⟨c, fun j i => q (j, i), funext fun j => funext fun i => hq (j, i)⟩

variable (hdom : Dominates R A)

omit [IsDomain R] in
/-- **A common denominator in `R` for finitely many polynomials over `A`.** For `R` a domain with
fraction field `K` and `A ⊆ K` a valuation ring dominating `R`, finitely many polynomials with
coefficients in `A` become polynomials with coefficients in `R` after multiplication by a single
nonzero element of `R`.

There are finitely many coefficients in all, each an element of `A ⊆ K = Frac R`, and
`IsLocalization.exist_integer_multiples` clears their denominators simultaneously; the
polynomials are then rebuilt from the cleared coefficients.

This is the move that the remaining step of Stacks Tag 053I needs in order to compare a relation
holding over `A` with one holding over a chart: the descended relation vectors span a submodule
over the chart's polynomial ring, and a representation of an element over `A[x]` becomes one over
`R[x]` — hence over the chart — after clearing denominators. -/
theorem exists_common_denominator {n t : ℕ} (γ : Fin t → MvPolynomial (Fin n) (valRing A)) :
    letI := hdom.algebra
    ∃ s : R, s ≠ 0 ∧ ∀ i, ∃ q : MvPolynomial (Fin n) R,
      MvPolynomial.map (algebraMap R (valRing A)) q = s • γ i := by
  classical
  let _ := hdom.algebra
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors R) (S := K)
    (Finset.univ.biUnion fun i : Fin t => (γ i).support.image (Sigma.mk i))
    fun p : (i : Fin t) × (Fin n →₀ ℕ) => (((γ p.1).coeff p.2 : valRing A) : K)
  refine ⟨(b : R), nonZeroDivisors.ne_zero b.2, fun i => ?_⟩
  have key : ∀ d : Fin n →₀ ℕ, ∃ y : R, d ∈ (γ i).support →
      (algebraMap R (valRing A)) y = (b : R) • (γ i).coeff d := by
    intro d
    by_cases hd : d ∈ (γ i).support
    · obtain ⟨y, hy⟩ := hb ⟨i, d⟩ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hd⟩)
      refine ⟨y, fun _ => ?_⟩
      apply Subtype.ext
      have h1 : ((algebraMap R (valRing A) y : valRing A) : K) = algebraMap R K y := rfl
      have h2 : (((b : R) • (γ i).coeff d : valRing A) : K)
          = algebraMap R K (b : R) * (((γ i).coeff d : valRing A) : K) := by
        rw [Algebra.smul_def]
        rfl
      rw [h1, h2]
      simpa [Algebra.smul_def] using hy
    · exact ⟨0, fun h => absurd h hd⟩
  choose y hy using key
  refine ⟨∑ d ∈ (γ i).support, MvPolynomial.monomial d (y d), ?_⟩
  rw [map_sum]
  have hterm : ∀ d ∈ (γ i).support,
      MvPolynomial.map (algebraMap R (valRing A)) (MvPolynomial.monomial d (y d))
        = MvPolynomial.monomial d ((b : R) • (γ i).coeff d) := fun d hd => by
    rw [MvPolynomial.map_monomial, hy d hd]
  rw [Finset.sum_congr rfl hterm]
  have hsm : ((b : R) • γ i) = ∑ d ∈ (γ i).support,
      MvPolynomial.monomial d ((b : R) • (γ i).coeff d) := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff (γ i)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.smul_monomial]
  exact hsm.symm

omit [IsDomain R] in
/-- **A finite presentation of the valuation-ring model.** Let `M` be a finite module over
`R[x_1, …, x_n]` and let `N_A` be the quotient of its base change to `A[x_1, …, x_n]` by the
`A`-torsion.  Then `N_A` is the quotient of a finite free `A[x_1, …, x_n]`-module by a submodule
spanned by finitely many vectors.

Surjectivity comes from finiteness of `N_A` over `A[x]`
(`Module.instFiniteTorsionFreeQuot`) and finite generation of the kernel from finite
presentation of `N_A` over `A[x]` (`Module.instFinitePresentationTorsionFreeQuot`, i.e. Nagata's
theorem, Stacks Tag 053E). -/
theorem exists_presentation_valuationModel (n : ℕ) (M : Type w) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] [Module.Finite (MvPolynomial (Fin n) R) M] :
    letI := hdom.algebra
    ∃ (r m : ℕ) (k : Fin m → (Fin r → MvPolynomial (Fin n) (valRing A)))
      (π : (Fin r → MvPolynomial (Fin n) (valRing A)) →ₗ[MvPolynomial (Fin n) (valRing A)]
        Module.torsionFreeQuot (valRing A) (MvPolynomial (Fin n) (valRing A))
          (MvPolynomial.moduleBaseChange R (valRing A) n M)),
      Function.Surjective π ∧
        LinearMap.ker π = Submodule.span (MvPolynomial (Fin n) (valRing A)) (Set.range k) := by
  let _ := hdom.algebra
  let _ : ValuationRing (valRing A) := inferInstanceAs (ValuationRing A)
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' (MvPolynomial (Fin n) (valRing A))
    (Module.torsionFreeQuot (valRing A) (MvPolynomial (Fin n) (valRing A))
      (MvPolynomial.moduleBaseChange R (valRing A) n M))
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.FinitePresentation.fg_ker π hπ)
  exact ⟨r, m, k, π, hπ, hk.symm⟩

/-- **The descended flat model of Stacks Tag 053I.** Let `(R, 𝔪)` be a local domain with fraction
field `K` and `𝔪 ≠ 0`, let `A ⊆ K` be a valuation ring dominating `R`, and let `M` be a finite
module over `R[x_1, …, x_n]`.  Then there are a rank `r`, a number `m` of relations, admissible
charts `c₀ ≤ c` of Stacks Tag 052M and relation vectors `k₁, …, k_m` in `R[I₀/a₀][x]^r` such that

* the quotient of `A[x]^r` by the span of the images of the `k_j` is the valuation-ring model
  `N_A` of `M`, that is, the `A`-torsion-free quotient of `A[x] ⊗_{R[x]} M`, and
* the quotient of `R[I/a][x]^r` by the span of the images of the `k_j` is **flat** over the chart
  `R[I/a]`.

The three ingredients are: the valuation-ring model (Stacks Tags 0537, 0539, 053E, packaged as
`MvPolynomial.flat_and_finitePresentation_torsionFreeQuot_moduleBaseChange`), coefficient descent
along the directed system of Stacks Tag 052M
  (`Stacks.Flatness.BlowupFlattening.exists_chart_relGenTop_eq`), and the
descent of flatness of Stacks Tag 02JO (3)
  (`Stacks.Flatness.BlowupFlattening.exists_chart_flat_quotient`).

The conclusion is flatness over the chart, not over `R`. -/
theorem exists_chart_flat_model (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (n : ℕ) (M : Type w)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
    [Module.Finite (MvPolynomial (Fin n) R) M] :
    letI := hdom.algebra
    ∃ (r m : ℕ) (c₀ c : AdmissibleChart R A) (h : c₀ ≤ c)
      (k : Fin m → (Fin r → MvPolynomial (Fin n) (chartRing c₀))),
      Nonempty (((Fin r → MvPolynomial (Fin n) (valRing A)) ⧸ relSpanTop k)
          ≃ₗ[MvPolynomial (Fin n) (valRing A)]
        Module.torsionFreeQuot (valRing A) (MvPolynomial (Fin n) (valRing A))
          (MvPolynomial.moduleBaseChange R (valRing A) n M)) ∧
        Module.Flat (chartRing c)
          ((Fin r → MvPolynomial (Fin n) (chartRing c)) ⧸ relSpan h k) := by
  let _ := hdom.algebra
  let _ : ValuationRing (valRing A) := inferInstanceAs (ValuationRing A)
  obtain ⟨r, m, k, π, hπ, hker⟩ := exists_presentation_valuationModel hdom n M
  obtain ⟨c₀, k₀, hk₀⟩ := exists_chart_relGenTop_eq hm hdom k
  have hspan : relSpanTop k₀ = LinearMap.ker π := by rw [relSpanTop, hk₀, hker]
  have e : ((Fin r → MvPolynomial (Fin n) (valRing A)) ⧸ relSpanTop k₀)
      ≃ₗ[MvPolynomial (Fin n) (valRing A)]
      Module.torsionFreeQuot (valRing A) (MvPolynomial (Fin n) (valRing A))
        (MvPolynomial.moduleBaseChange R (valRing A) n M) :=
    hspan ▸ π.quotKerEquivOfSurjective hπ
  have hflat : Module.Flat (valRing A)
      ((Fin r → MvPolynomial (Fin n) (valRing A)) ⧸ relSpanTop k₀) :=
    Module.Flat.of_linearEquiv (e.restrictScalars (valRing A))
  obtain ⟨c, hc, hflatc⟩ := exists_chart_flat_quotient hm hdom c₀ k₀ hflat
  exact ⟨r, m, c₀, c, hc, k₀, ⟨e⟩, hflatc⟩

end Descent

/-! ### The two spellings of the base change of a module over a polynomial ring -/

section BaseChange

variable (R : Type u) [CommRing R] (C : Type v) [CommRing C] [Algebra R C] (n : ℕ)
  (M : Type w) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
  [IsScalarTower R (MvPolynomial (Fin n) R) M]

/-- **The two spellings of the base change of a module over a polynomial ring agree.** For `M` a
module over `P = R[x_1, …, x_n]` and `C` an `R`-algebra, the base change of `M` along
`P → C[x_1, …, x_n]` and the scalar extension of `M` along `R → C` are identified as
`C`-modules:
`C[x_1, …, x_n] ⊗_P M ≃ₗ[C] C ⊗_R M`.

This is the comparison that the valuation-ring model step of Stacks Tag 053I is phrased *around*
rather than through (see the module docstring of
`StacksFrontier.RingTheory.Flat.BlowupValuationModel`): the strict transform of Stacks Tag 053H is
built on the scalar extension `C ⊗_R M`, while the descent step works with the polynomial-ring
base change.  It is `Algebra.IsPushout.cancelBaseChange` applied to the pushout square
`C[x] = C ⊗_R R[x]`, i.e. to `MvPolynomial.instIsPushout`. -/
noncomputable def mvPolynomialBaseChangeEquiv :
    MvPolynomial (Fin n) C ⊗[MvPolynomial (Fin n) R] M ≃ₗ[C] C ⊗[R] M :=
  Algebra.IsPushout.cancelBaseChange R C (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) C) M

/-- `mvPolynomialBaseChangeEquiv` sends `1 ⊗ x` to `1 ⊗ x`. -/
@[simp]
theorem mvPolynomialBaseChangeEquiv_one_tmul (x : M) :
    mvPolynomialBaseChangeEquiv R C n M (1 ⊗ₜ[MvPolynomial (Fin n) R] x) = 1 ⊗ₜ[R] x :=
  Algebra.IsPushout.cancelBaseChange_tmul R C (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) C) M x

end BaseChange

/-! ### Base change of a presentation whose kernel is not finitely generated -/

section GeneralPresentation

variable (S : Type u) [CommRing S] (T : Type v) [CommRing T] [Algebra S T] (r : ℕ)

/-- **The relation submodule of a base-changed presentation**, for a relation submodule that is
not assumed finitely generated: the `T`-span inside `Tʳ` of the image of `Z ⊆ Sʳ`.

For `Z` the span of a finite family this is `Stacks.Flatness.BlowupFlattening.relSubmodule`, by
`Stacks.Flatness.BlowupFlattening.relSubmodule_eq_span_image`. -/
def relSpanOf (Z : Submodule S (Fin r → S)) : Submodule T (Fin r → T) :=
  Submodule.span T (freeBaseChange S T r '' (Z : Set (Fin r → S)))

variable {S T r} {M : Type w} [AddCommGroup M] [Module S M]

/-- The comparison map from `Sʳ / ker π` to `Tʳ / relSpanOf S T r (ker π)` induced by
componentwise application of `algebraMap S T`; the version of
  `Stacks.Flatness.BlowupFlattening.quotComparison` that
does not name a finite generating family of the kernel. -/
def quotComparisonOf (π : (Fin r → S) →ₗ[S] M) :
    ((Fin r → S) ⧸ LinearMap.ker π) →ₗ[S]
      ((Fin r → T) ⧸ relSpanOf S T r (LinearMap.ker π)) :=
  Submodule.liftQ (LinearMap.ker π)
    (((relSpanOf S T r (LinearMap.ker π)).mkQ.restrictScalars S).comp (freeBaseChange S T r))
    fun x hx => (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x, hx, rfl⟩)

/-- **The base-changed presentation is a base change**, for a kernel that is not assumed finitely
generated.  This is right exactness of the tensor product, in the form
`Stacks.QuasiregularSequence.FlatBaseChange.isBaseChange_of_quotient`. -/
theorem isBaseChange_quotComparisonOf (π : (Fin r → S) →ₗ[S] M) :
    IsBaseChange T (quotComparisonOf (T := T) π) :=
  Stacks.QuasiregularSequence.FlatBaseChange.isBaseChange_of_quotient (isBaseChange_freeBaseChange S
      T r) (LinearMap.ker π)
    (relSpanOf S T r (LinearMap.ker π)) rfl _ fun _ => rfl

/-- **Base change of a presentation is the base-changed presentation.** If `π : Sʳ → M` is a
surjection of `S`-modules then `T ⊗_S M` is `Tʳ` modulo the `T`-span of the image of `ker π`, for
every commutative `S`-algebra `T`.

This is `Stacks.Flatness.BlowupFlattening.tensorQuotEquiv` without the hypothesis that `ker π` be
  finitely generated —
which for Stacks Tag 053I matters, since a finite module over `R[x_1, …, x_n]` for `R` a
non-noetherian local domain need not be finitely presented. -/
noncomputable def tensorQuotEquivOf (π : (Fin r → S) →ₗ[S] M) (hπ : Function.Surjective π) :
    T ⊗[S] M ≃ₗ[T] ((Fin r → T) ⧸ relSpanOf S T r (LinearMap.ker π)) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T)
      (π.quotKerEquivOfSurjective hπ).symm ≪≫ₗ
    (isBaseChange_quotComparisonOf (T := T) π).equiv

end GeneralPresentation

section ChartPresentation

variable (R : Type u) [CommRing R] (C : Type v) [CommRing C] [Algebra R C] (n : ℕ)
  (M : Type w) [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
  [IsScalarTower R (MvPolynomial (Fin n) R) M] [Module.Finite (MvPolynomial (Fin n) R) M]

/-- **The scalar extension of a finite module over a polynomial ring is a quotient of a finite
free module over the extended polynomial ring.** For `M` a finite module over
`P = R[x_1, …, x_n]` and `C` an `R`-algebra there are a rank `r` and a surjection
`π : Pʳ → M` with

`C ⊗_R M ≃ₗ[C] C[x_1, …, x_n]ʳ / relSpanOf P C[x] r (ker π)`.

This combines `Stacks.Flatness.BlowupFlattening.mvPolynomialBaseChangeEquiv` with
`Stacks.Flatness.BlowupFlattening.tensorQuotEquivOf`; the scalar extension on the left is the one
  on which the strict
transform of Stacks Tag 053H is built. -/
theorem exists_quotient_equiv_baseChange :
    ∃ (r : ℕ) (π : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M),
      Function.Surjective π ∧
        Nonempty (C ⊗[R] M ≃ₗ[C]
          ((Fin r → MvPolynomial (Fin n) C) ⧸
            relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) C) r (LinearMap.ker π))) := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' (MvPolynomial (Fin n) R) M
  exact ⟨r, π, hπ, ⟨(mvPolynomialBaseChangeEquiv R C n M).symm ≪≫ₗ
    (tensorQuotEquivOf (T := MvPolynomial (Fin n) C) π hπ).restrictScalars C⟩⟩

end ChartPresentation

/-! ### Saturated relation submodules and the strict transform -/

section Saturation

variable {C : Type u} [CommRing C] {F : Type v} [AddCommGroup F] [Module C F]

/-- A linear equivalence carries the submonoid-torsion submodule onto the submonoid-torsion
submodule. -/
theorem map_torsion' {Y : Type w} [AddCommGroup Y] [Module C Y] (e : F ≃ₗ[C] Y)
    (s : Submonoid C) :
    Submodule.map (e : F →ₗ[C] Y) (Submodule.torsion' C F s) = Submodule.torsion' C Y s := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_torsion'_iff]
  constructor
  · rintro ⟨x, ⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_⟩
    have h : ((c : C)) • x = 0 := hc
    change ((c : C)) • e x = 0
    rw [← map_smul, h, map_zero]
  · rintro ⟨c, hc⟩
    have h : ((c : C)) • y = 0 := hc
    refine ⟨e.symm y, ⟨c, ?_⟩, by simp⟩
    change ((c : C)) • e.symm y = 0
    rw [← map_smul, h, map_zero]

/-- A scalar kills the class of `v` in `F ⧸ Z` iff it carries `v` into `Z`. -/
private theorem smul_mk_eq_zero_iff (Z : Submodule C F) (c : C) (v : F) :
    c • Submodule.Quotient.mk (p := Z) v = 0 ↔ c • v ∈ Z := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

/-- **A saturated relation submodule is the preimage of the torsion.** Let `Z ≤ L` be submodules
of `F` and `α` a scalar such that every element of `L` is carried into `Z` by some power of `α`,
and such that `L` is `α`-saturated: `αᴺ v ∈ L → v ∈ L`.  Then `L` is exactly the preimage in `F`
of the `α`-power torsion of `F ⧸ Z`.

This is the combinatorial heart of the last step of Stacks Tag 053I: `Z` is the relation
submodule of the base-changed presentation of `M`, `L` the relation submodule descended from the
valuation ring, `α` the image of the denominator `a`, and the quotient by the `α`-power torsion of
`F ⧸ Z` is the strict transform. -/
theorem comap_torsion'_eq (Z L : Submodule C F) {α : C} (hZL : Z ≤ L)
    (hLsat : ∀ v ∈ L, ∃ N : ℕ, α ^ N • v ∈ Z)
    (hsat : ∀ (N : ℕ) (v : F), α ^ N • v ∈ L → v ∈ L) :
    Submodule.comap Z.mkQ (Submodule.torsion' C (F ⧸ Z) (Submonoid.powers α)) = L := by
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · obtain ⟨⟨s, N, rfl⟩, hs⟩ := hv
    exact hsat N v (hZL ((smul_mk_eq_zero_iff Z _ v).mp hs))
  · obtain ⟨N, hN⟩ := hLsat v hv
    exact ⟨⟨α ^ N, N, rfl⟩, (smul_mk_eq_zero_iff Z _ v).mpr hN⟩

/-- **The quotient of `F ⧸ Z` by its `α`-power torsion is `F ⧸ L`**, under the hypotheses of
`Stacks.Flatness.BlowupFlattening.comap_torsion'_eq`. -/
def quotTorsionEquiv (Z L : Submodule C F) {α : C} (hZL : Z ≤ L)
    (hLsat : ∀ v ∈ L, ∃ N : ℕ, α ^ N • v ∈ Z)
    (hsat : ∀ (N : ℕ) (v : F), α ^ N • v ∈ L → v ∈ L) :
    ((F ⧸ Z) ⧸ Submodule.torsion' C (F ⧸ Z) (Submonoid.powers α)) ≃ₗ[C] (F ⧸ L) := by
  have hmap : (Submodule.comap Z.mkQ (Submodule.torsion' C (F ⧸ Z) (Submonoid.powers α))).map
      Z.mkQ = Submodule.torsion' C (F ⧸ Z) (Submonoid.powers α) :=
    Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)
  refine Submodule.quotEquivOfEq _ _ hmap.symm ≪≫ₗ ?_
  refine Submodule.quotientQuotientEquivQuotient Z _ ?_ ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (comap_torsion'_eq Z L hZL hLsat hsat)
  intro z hz
  refine ⟨⟨1, 0, pow_zero α⟩, ?_⟩
  change (1 : C) • Submodule.Quotient.mk (p := Z) z = 0
  rw [one_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hz

/-- **A torsion-free quotient has a saturated relation submodule.** If `F ⧸ L` is torsion free
over the domain `C` and `α ≠ 0`, then `αᴺ v ∈ L` forces `v ∈ L`.

Over a domain a flat module is torsion free (Stacks Tag 0538, `Module.Flat.isTorsionFree`), so
this is how the `hsat` hypothesis of `Stacks.Flatness.BlowupFlattening.comap_torsion'_eq` is met in
  Stacks Tag 053I:
from the flatness produced by the descent step. -/
theorem mem_of_smul_pow_mem [IsDomain C] (L : Submodule C F) {α : C} (hα : α ≠ 0)
    (htf : Module.IsTorsionFree C (F ⧸ L)) {N : ℕ} {v : F} (h : α ^ N • v ∈ L) : v ∈ L := by
  have h2 := (smul_mk_eq_zero_iff L _ v).mpr h
  rcases Module.isTorsionFree_iff_smul_eq_zero.mp htf _ _ h2 with hz | hz
  · exact absurd hz (pow_ne_zero N hα)
  · exact (Submodule.Quotient.mk_eq_zero _).mp hz

/-- The first-power form of `Stacks.Flatness.BlowupFlattening.mem_of_smul_pow_mem`: a torsion-free
  quotient lets one
cancel a nonzero scalar. -/
theorem mem_of_smul_mem [IsDomain C] (L : Submodule C F) {α : C} (hα : α ≠ 0)
    (htf : Module.IsTorsionFree C (F ⧸ L)) {v : F} (h : α • v ∈ L) : v ∈ L :=
  mem_of_smul_pow_mem L hα htf (N := 1) (by rwa [pow_one])

end Saturation

section StrictTransformIdentification

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)] (n : ℕ) (M : Type w)
  [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
  [IsScalarTower R (MvPolynomial (Fin n) R) M]

/-- **The strict transform is the descended quotient.** Let `M` be a module over
`P = R[x_1, …, x_n]`, let `π : Pʳ → M` be a surjection, write `C = R[I/a]` and
`Cx = C[x_1, …, x_n]`, and let `Z = relSpanOf P Cx r (ker π)` be the relation submodule of the
base-changed presentation.  Let `L` be a `Cx`-submodule of `Cxʳ` with

* `Z ≤ L`,
* every element of `L` killed, modulo `Z`, by a power of the image `α` of `a` in `C`, and
* `L` `α`-saturated.

Then the strict transform of `M` on the chart `R[I/a]` (Stacks Tag 053H) is `Cxʳ / L`.

This is the final step of Stacks Tag 053I once the relation submodule `L` has been produced:
`Stacks.Flatness.BlowupFlattening.exists_quotient_equiv_baseChange` identifies the scalar extension
  `C ⊗_R M` with
`Cxʳ / Z`, `Stacks.Flatness.BlowupFlattening.map_torsion'` transports the `a`-power torsion across
  that identification,
and `Stacks.Flatness.BlowupFlattening.quotTorsionEquiv` divides it out. -/
theorem nonempty_strictTransform_equiv {r : ℕ}
    {π : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M}
    (hπ : Function.Surjective π)
    (L : Submodule (MvPolynomial (Fin n) (Blowup I a))
      (Fin r → MvPolynomial (Fin n) (Blowup I a)))
    (hZL : relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
        (LinearMap.ker π) ≤ L)
    (hLsat : ∀ v ∈ L, ∃ N : ℕ, algebraMap R (Blowup I a) a ^ N • v ∈
        relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
          (LinearMap.ker π))
    (hsat : ∀ (N : ℕ) (v : Fin r → MvPolynomial (Fin n) (Blowup I a)),
        algebraMap R (Blowup I a) a ^ N • v ∈ L → v ∈ L) :
    Nonempty (strictTransform I a M ≃ₗ[Blowup I a]
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L)) := by
  let E := (mvPolynomialBaseChangeEquiv R (Blowup I a) n M).symm ≪≫ₗ
    (tensorQuotEquivOf (T := MvPolynomial (Fin n) (Blowup I a)) π hπ).restrictScalars
      (Blowup I a)
  refine ⟨Submodule.Quotient.equiv _ _ E
    (map_torsion' E (Submonoid.powers (algebraMap R (Blowup I a) a))) ≪≫ₗ ?_⟩
  exact quotTorsionEquiv
    ((relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
      (LinearMap.ker π)).restrictScalars (Blowup I a))
    (L.restrictScalars (Blowup I a)) (fun _ hv => hZL hv) (fun v hv => hLsat v hv)
    fun N v h => hsat N v h

/-- **The strict transform is flat as soon as the descended quotient is.** Under the hypotheses of
`Stacks.Flatness.BlowupFlattening.nonempty_strictTransform_equiv`, with the `α`-saturation of `L`
  replaced by flatness
of `Cxʳ / L` over the chart — which is what Stacks Tag 02JO (3) produces, and which implies
saturation because a flat module over a domain is torsion free — the strict transform of `M` is
flat over the chart `R[I/a]`.

This is clause (4) of Stacks Tag 053I for the module `M`, read as flatness over the chart,
reduced to the production of the relation submodule `L`. -/
theorem flat_strictTransform_of_flat_quotient [IsDomain (Blowup I a)] {r : ℕ}
    {π : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M}
    (hπ : Function.Surjective π)
    (L : Submodule (MvPolynomial (Fin n) (Blowup I a))
      (Fin r → MvPolynomial (Fin n) (Blowup I a)))
    (hZL : relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
        (LinearMap.ker π) ≤ L)
    (hLsat : ∀ v ∈ L, ∃ N : ℕ, algebraMap R (Blowup I a) a ^ N • v ∈
        relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
          (LinearMap.ker π))
    (hflat : Module.Flat (Blowup I a)
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L)) :
    Module.Flat (Blowup I a) (strictTransform I a M) := by
  have hα : algebraMap R (Blowup I a) a ≠ 0 := strictTransform.algebraMap_a_ne_zero I a
  have htf : Module.IsTorsionFree (Blowup I a)
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L) :=
    Module.Flat.isTorsionFree
  obtain ⟨e⟩ := nonempty_strictTransform_equiv I a n M hπ L hZL hLsat
    fun N v h => mem_of_smul_pow_mem (L.restrictScalars (Blowup I a)) hα htf (N := N) h
  exact Module.Flat.of_linearEquiv e

end StrictTransformIdentification

end Stacks.Flatness.BlowupFlattening

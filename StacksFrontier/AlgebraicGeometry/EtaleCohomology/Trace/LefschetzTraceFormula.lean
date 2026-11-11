module

public import StacksCore.CategoryTheory.Filtration.Single
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalLefschetzNumber
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FilteredTrace

/-!
# The Lefschetz trace formula

Let `Λ` be a finite ring, `X` a projective curve over a finite field `k` and `K` an object of
`D_ctf(X, Λ)`. The Lefschetz trace formula is the identity

  `Tr(π_X^* | RΓ(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in the additive commutator quotient `Λ^natural`, between the global Lefschetz number of `K` and
its local Lefschetz number.

This file carries the dévissage the source runs for it. Let `U = X - X(k)` be the open
complement of the finite set of rational points, and remove the points of `X(k)` from `X` one at
a time: each removal of a closed point `i : Y → X` with open complement `j : U' → X` gives a
short exact sequence `0 → j_! j^{-1}K → K → i_* i^{-1}K → 0`, and these assemble `RΓ(X_k̄, K)`
into a filtered perfect complex of `Λ`-modules whose graded pieces are `RΓ_c(U_k̄, K|_U)` and
the stalks `K_x̄`, one for each `x ∈ X(k)`. That is the datum `LefschetzDevissage`, and it is
the input the source does not prove: it is the content of the two forward references in Step 1
of the proof of Tag 03UG.

Additivity of the trace along a filtration, Tag 03TK, then computes the global Lefschetz number
as the sum of the global Lefschetz number of the open part and the local Lefschetz number. Two
consequences follow. When the open graded piece vanishes — a curve all of whose points are
rational, in particular a scheme of dimension zero, which is Step 2 of the source's proof — the
global and local Lefschetz numbers agree with no further hypothesis. In general they agree
exactly when the global Lefschetz number of the open part vanishes, the goal the source reaches
in Step 3.

That vanishing is reached here from the Galois descent the source runs in Steps 7 to 9. After
the reductions of Steps 3 to 6 the open part is a smooth irreducible affine curve `U` with no
rational points, the coefficients are a finite locally constant sheaf `F` with finite projective
stalks, and `Λ` is killed by a power `ℓ^m` of a prime `ℓ` invertible in `k`. Fixing a finite
étale Galois cover `f : V → U` with group `G` and `f^{-1}F` constant with value the `Λ[G]`-module
`M`, and writing `A = Z/ℓ^n Z` with `n` large, the trace on the open part becomes

  `Tr(π_U^* | RΓ_c(U_k̄, F)) = ∑_{g ∈ G} Tr_A^{Z_g}((g, π_U^*) | RΓ_c(U_k̄, f_*A)) · Tr_Λ(g | M)`,

each coefficient trace is annihilated by the order `ℓ^{a_g}` of the stabiliser `Z_g`, because
`#Z_g` times it is the trace of `(g^{-1} π_V)^*` on `RΓ_c(V_k̄, A)` and that trace counts the
fixed points of `g^{-1}π_V`, of which there are none. So each coefficient trace is divisible by
`ℓ^{n - a_g}`, hence by `ℓ^m` once `n ≥ a + m` for a bound `a` on the exponents `a_g`, hence it
annihilates `Λ^natural`: every term of the sum vanishes, and with it the trace on the open part.
That is the datum `LefschetzGaloisDescent`, and the trace formula follows from it.

## Main definitions

* `Stacks.EtaleCohomology.LefschetzDevissage` — the filtered perfect complex `RΓ(X_k̄, K)`
  together with the action of `π_X^*` on it and the bookkeeping of its graded pieces: one for
  the open complement of `X(k)` and one for each rational point.
* `Stacks.EtaleCohomology.LefschetzGaloisDescent` — the Galois descent of Steps 7 to 9 of the
  source's proof: the decomposition of the trace on the open complement over a finite group,
  the orders of the stabilisers, and the annihilation of the coefficient traces.
* `Stacks.EtaleCohomology.forgetDatum`, `Stacks.EtaleCohomology.gradedDatum` and
  `Stacks.EtaleCohomology.gradedTrace` — the complex underlying a filtered perfect complex with
  an endomorphism, its graded piece at an index, and the trace of the endomorphism there.
* `Stacks.EtaleCohomology.StratifiedDevissage` — the same dévissage along an arbitrary finite
  stratification, with `Stacks.EtaleCohomology.StratifiedDevissage.globalDatum` and
  `Stacks.EtaleCohomology.StratifiedDevissage.stratumDatum`.  A Lefschetz dévissage is an
  instance of it, by `Stacks.EtaleCohomology.LefschetzDevissage.toStratifiedDevissage`.
* `Stacks.EtaleCohomology.LefschetzDevissage.globalDatum`,
  `Stacks.EtaleCohomology.LefschetzDevissage.openDatum` and
  `Stacks.EtaleCohomology.LefschetzDevissage.stalkDatum` — the data of Tags 03TX and 03TY read
  off the dévissage: the whole complex, its open graded piece, and its point graded pieces.

## Main results

* `Stacks.EtaleCohomology.StratifiedDevissage.globalLefschetzNumber_eq_sum` — the dévissage
  along a stratification: the global Lefschetz number is the sum over the strata.
* `Stacks.EtaleCohomology.LefschetzDevissage.globalLefschetzNumber_eq_add` — the dévissage: the
  global Lefschetz number of `X` is the global Lefschetz number of the open complement of
  `X(k)` plus the local Lefschetz number.  It is the stratified sum over `Option points`.
* `Stacks.EtaleCohomology.LefschetzDevissage`.`globalLefschetzNumber_eq_localLefschetzNumber`
  `_of_openDatum_eq_zero` — the two numbers agree when the global Lefschetz number of the open
  complement vanishes.
* `Stacks.EtaleCohomology.LefschetzDevissage`.`globalLefschetzNumber_eq_localLefschetzNumber`
  `_of_isZero` — the two numbers agree with no further hypothesis when the open graded piece
  vanishes.
* `Stacks.EtaleCohomology.LefschetzDevissage.globalLefschetzNumber_eq_localLefschetzNumber_iff`
  — the two numbers agree exactly when that vanishing does, so no weaker hypothesis would
  serve.
* `Stacks.EtaleCohomology.LefschetzGaloisDescent.openDatum_eq_zero` — the global Lefschetz
  number of the open complement vanishes, from the Galois descent of Steps 7 to 9.
* `Stacks.EtaleCohomology.LefschetzGaloisDescent.globalLefschetzNumber_eq_localLefschetzNumber`
  — the global and local Lefschetz numbers of a dévissage with a Galois descent agree.  The
  Lefschetz trace formula of Tag 03TZ itself, for a projective curve over a finite field and
  `K ∈ D_ctf(X, Λ)`, is proved in
  `Stacks.EtaleCohomology.globalLefschetzNumberOfCtf_eq_sum_rationalPointStalkTrace`.
* `Stacks.EtaleCohomology.projectiveLineLefschetzDevissage` and
  `Stacks.EtaleCohomology.projectiveLine_globalLefschetzNumber_eq_localLefschetzNumber` — a
  dévissage with `n` rational points and non-zero graded pieces, realised on the projective line
  over a finite field with constant coefficients, and the agreement of the two numbers for it.
  This exhibits the hypotheses as consistent and not satisfied only vacuously.
* `Stacks.EtaleCohomology.projectiveLineLefschetzGaloisDescent` — a Galois descent with a
  non-zero coefficient trace and an arbitrary module trace, realised on that dévissage over a
  finite ring killed by `ℓ^m`, for instance `Z/ℓ^m Z`. This exhibits the hypotheses of
  `LefschetzGaloisDescent` as consistent and not satisfied only by zero data.

## Implementation notes

The coefficient ring is an arbitrary, possibly noncommutative, finite ring, as in the source,
and the traces are those of `CategoryTheory.FilteredDerived.perfectDerivedTrace`, valued in
`Λ^natural`. The ring, module and point universes are independent.

No field of `LefschetzDevissage` is an identity between traces: the structure carries the
filtered complex, the Frobenius action on it, the filtration indices of the graded pieces and
the statement that there are no further graded pieces. The global datum of Tag 03TX is the
underlying complex of the filtration, and the stalk `K_x̄` of Tag 03TY is *defined* as the
graded piece at the index of `x`, which is the identification the source makes in Step 2 of the
proof of Tag 03UG for a scheme of dimension zero; so that step is a definition here rather than
a hypothesis. That the complex underlying the filtration is perfect, which a filtered perfect
complex presupposes, is Tag 03TV, proved in
`Stacks.EtaleCohomology.CurveGlobalSections.isPerfect`.

The vanishing of the global Lefschetz number of the open complement is not a theorem about
`LefschetzDevissage` alone: the open datum of a dévissage is an arbitrary perfect complex of
`Λ`-modules carrying an arbitrary endomorphism, whose trace can be any element of
`Λ^natural`. It is a theorem about a dévissage equipped with a `LefschetzGaloisDescent`, whose
fields are the two inputs the source produces in Steps 7 to 9 and which this file does not
prove: the decomposition `openDatum_trace_eq` of the trace on the open complement as a sum over
the Galois group, which rests on the sorites for traces of a monoid extension acting on a
perfect complex, Tags 03UC and 03UD; and the annihilation `prime_pow_dvd_coefficientTrace` of
each coefficient trace by the order of its stabiliser, which rests on the comparison of a trace
with the trace of its restriction to a stabiliser, Tag 03UB, and on the vanishing of the trace
of `(g^{-1}π_V)^*` on the Galois cover, which the source gets from Weil's trace formula, Tag
03U1, and the absence of fixed points. The reductions that bring an arbitrary situation into the
shape where those two inputs are available — Steps 3 to 6, which pass to a smooth irreducible
affine curve with no rational points, to a finite locally constant sheaf with finite projective
stalks, and to an `ℓ`-primary coefficient ring — are not formalized here either.

The coefficient trace `Tr_A^{Z_g}` takes its values in `A = Z/ℓ^n Z` and multiplies the trace
`Tr_Λ(g | M)` in `Λ^natural` through the central map `A → Λ`. It is recorded here by an integer
lifting its class, acting on `Λ^natural` through the `ℤ`-module structure of that abelian group.
The lift is harmless: `level_smul_eq_zero` shows that `ℓ^n` annihilates `Λ^natural`, so the
product depends only on the class of the integer modulo `ℓ^n`.

Two elementary facts about the trace are proved on the way and kept private: the trace of an
endomorphism of a zero perfect object vanishes, computed on the complex all of whose terms are
the zero module, and a sum over `ℤ` supported on one integer together with the image of an
injection from a finite type splits accordingly.

The namespace `Stacks.EtaleCohomology.GradedWitness` builds the filtered perfect complex used for
the non-vacuity statement: the skyscraper filtered modules of
`StacksCore.CategoryTheory.Filtration.Single`, their iterated binary biproduct, which is free of
rank
`n` with graded pieces free of rank one at the filtration indices `1, …, n` and zero elsewhere,
and that object placed in cochain degree zero. With `n = q + 1 = #P¹(F_q)` and constant
coefficients `K = Λ`, the graded pieces are the stalks `K_x̄` at the `q + 1` rational points of
the projective line, on which the geometric Frobenius acts trivially, and the graded piece at the
index of the open complement vanishes, so the trace formula holds there unconditionally.

## References

* [Stacks Project, Tag 03TZ](https://stacks.math.columbia.edu/tag/03TZ)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03TK](https://stacks.math.columbia.edu/tag/03TK)
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
* [Stacks Project, Tag 03TY](https://stacks.math.columbia.edu/tag/03TY)
* [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1)
* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
* [Stacks Project, Tag 03UB](https://stacks.math.columbia.edu/tag/03UB)
* [Stacks Project, Tag 03UC](https://stacks.math.columbia.edu/tag/03UC)
* [Stacks Project, Tag 03UD](https://stacks.math.columbia.edu/tag/03UD)
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.FilteredDerived
open CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The cochain complex of `Λ`-modules all of whose terms are the zero module and all of whose
differentials are zero. -/
public def zeroCochainComplex (Λ : Type u) [Ring Λ] : CochainComplex (ModuleCat.{v} Λ) ℤ where
  X _ := ModuleCat.of Λ PUnit
  d _ _ := 0

/-- Each term of `zeroCochainComplex` has at most one element. -/
public instance zeroCochainComplex_subsingleton_X (Λ : Type u) [Ring Λ] (i : ℤ) :
    Subsingleton ((zeroCochainComplex.{u, v} Λ).X i) :=
  inferInstanceAs (Subsingleton PUnit.{v + 1})

/-- Each term of `zeroCochainComplex` is a zero object. -/
public lemma zeroCochainComplex_isZero_X (Λ : Type u) [Ring Λ] (i : ℤ) :
    Limits.IsZero ((zeroCochainComplex.{u, v} Λ).X i) :=
  ModuleCat.isZero_of_subsingleton _

/-- `zeroCochainComplex` is a zero object of the category of cochain complexes. -/
public lemma zeroCochainComplex_isZero (Λ : Type u) [Ring Λ] :
    Limits.IsZero (zeroCochainComplex.{u, v} Λ) := by
  refine (Limits.IsZero.iff_id_eq_zero _).mpr (HomologicalComplex.hom_ext _ _ fun i => ?_)
  exact (zeroCochainComplex_isZero_X.{u, v} Λ i).eq_of_src _ _

/-- `zeroCochainComplex` is a bounded complex of finite projective modules. -/
public lemma zeroCochainComplex_finiteProjective (Λ : Type u) [Ring Λ] :
    finiteProjectiveComplex.{u, v} Λ (zeroCochainComplex.{u, v} Λ) := by
  refine ⟨⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩, fun _ => ⟨inferInstance, inferInstance⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff (zeroCochainComplex.{u, v} Λ) 0).mpr
      fun i _ => zeroCochainComplex_isZero_X.{u, v} Λ i
  · exact (CochainComplex.isStrictlyLE_iff (zeroCochainComplex.{u, v} Λ) 0).mpr
      fun i _ => zeroCochainComplex_isZero_X.{u, v} Λ i

/-- The trace of every endomorphism of a zero perfect object of the derived category vanishes. -/
public theorem perfectDerivedTrace_eq_zero_of_isZero (Λ : Type u) [Ring Λ]
    (K : PerfectDerivedCategory.{u, v} Λ) (hK : Limits.IsZero K.obj) (f : K.obj ⟶ K.obj) :
    perfectDerivedTrace Λ K f = 0 := by
  classical
  have hP : finiteProjectiveComplex.{u, v} Λ (zeroCochainComplex.{u, v} Λ) :=
    zeroCochainComplex_finiteProjective.{u, v} Λ
  have hQ : Limits.IsZero (DerivedCategory.Q.obj (zeroCochainComplex.{u, v} Λ)) :=
    Functor.map_isZero _ (zeroCochainComplex_isZero.{u, v} Λ)
  rw [perfectDerivedTrace_eq_alternatingTrace Λ K f (zeroCochainComplex.{u, v} Λ) hP
    (hQ.iso hK) 0 (hQ.eq_of_src _ _)]
  have key : alternatingTrace Λ (zeroCochainComplex.{u, v} Λ) hP 0
      = ∑ᶠ _ : ℤ, (0 : AdditiveCommutatorQuotient Λ) := by
    simp only [alternatingTrace]
    refine finsum_congr fun i => ?_
    split
    · exact projectiveModuleTrace_eq_zero_of_subsingleton Λ _ _
    · rw [neg_eq_zero]
      exact projectiveModuleTrace_eq_zero_of_subsingleton Λ _ _
  rw [key, finsum_zero]

/-! ### The data attached to a filtered perfect complex with an endomorphism -/

section FilteredData

variable {Λ : Type u} [Ring Λ] [Finite Λ]
  (F : CategoryTheory.FilteredDerived.FilteredPerfectData.{u, v} Λ) (φ : F.obj ⟶ F.obj)

/-- The perfect complex underlying a filtered perfect complex, with its endomorphism: the
filtration forgotten. -/
public def forgetDatum : FrobeniusActionOnCohomology.{u, max u v} Λ where
  cohomology :=
    ⟨(CochainComplex.FilteredDerivedCategory.forgetDF).obj F.obj, F.forgetPerfect Λ⟩
  frobeniusAction := (CochainComplex.FilteredDerivedCategory.forgetDF).map φ

/-- The graded piece of a filtered perfect complex at an index, with its endomorphism. -/
public def gradedDatum (p : ℤ) : FrobeniusActionOnCohomology.{u, max u v} Λ where
  cohomology :=
    ⟨(CochainComplex.FilteredDerivedCategory.grDF p).obj F.obj, F.gradedPerfect Λ p⟩
  frobeniusAction := (CochainComplex.FilteredDerivedCategory.grDF p).map φ

/-- The trace of the endomorphism on the graded piece at an index. -/
public def gradedTrace (p : ℤ) : AdditiveCommutatorQuotient Λ :=
  perfectDerivedTrace Λ (gradedDatum F φ p).cohomology (gradedDatum F φ p).frobeniusAction

/-- The graded trace at an index is the global Lefschetz number of the graded piece there. -/
public lemma gradedTrace_eq_globalLefschetzNumber (p : ℤ) :
    gradedTrace F φ p = globalLefschetzNumber Λ (gradedDatum F φ p) :=
  rfl

/-- The graded trace vanishes at an index whose graded piece is zero. -/
public lemma gradedTrace_eq_zero_of_isZero (p : ℤ)
    (hz : Limits.IsZero ((CochainComplex.FilteredDerivedCategory.grDF p).obj F.obj)) :
    gradedTrace F φ p = 0 :=
  perfectDerivedTrace_eq_zero_of_isZero Λ _ hz _

end FilteredData

/-! ### Sums over the integers supported on a finite set -/

/-- A sum over `ℤ` of a function supported on the image of an injection `e` from a finite type
is the finite sum of the values of the function on that image. -/
private theorem finsum_eq_sum_of_support_subset_range (A : Type*) [AddCommGroup A]
    {strata : Type w} [Fintype strata] (g : ℤ → A) (e : strata → ℤ)
    (he : Function.Injective e) (hsupp : ∀ p : ℤ, (∀ s, p ≠ e s) → g p = 0) :
    (∑ᶠ p : ℤ, g p) = ∑ s : strata, g (e s) := by
  classical
  have hsub : Function.support g ⊆ (Finset.image e Finset.univ : Finset ℤ) := by
    intro p hp
    by_cases hx : ∃ s, p = e s
    · obtain ⟨s, hs⟩ := hx
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hs.symm⟩)
    · exact absurd (hsupp p fun s h => hx ⟨s, h⟩) hp
  rw [finsum_eq_finsetSum_of_support_subset g hsub, Finset.sum_image he.injOn]

/-! ### The stratified dévissage -/

/-- The dévissage of `RΓ_c(X_k̄, K)` along a finite stratification of `X`: a filtered perfect
complex of `Λ`-modules with an endomorphism `π_X^*`, whose graded pieces are the
`RΓ_c` of the strata, the stratum `s` sitting at the filtration index `stratumIndex s`, and
which has no other graded pieces.

This generalises `Stacks.EtaleCohomology.LefschetzDevissage`, whose graded pieces are one
distinguished open piece together with one piece for each rational point.

See [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3) and
[Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1. -/
public structure StratifiedDevissage.{u', v', w'} (Λ : Type u') [Ring Λ] [Finite Λ]
    (strata : Type w') where
  /-- The filtered perfect complex `RΓ_c(X_k̄, K)` assembled from the short exact sequences
  `0 → j_! j^{-1}K → K → i_* i^{-1}K → 0` of the strata and their complements. -/
  filtered : CategoryTheory.FilteredDerived.FilteredPerfectData.{u', v'} Λ
  /-- The action `π_X^*` on it, induced by the canonical map `c_K`. -/
  frobeniusAction : filtered.obj ⟶ filtered.obj
  /-- The filtration index whose graded piece is the `RΓ_c` of the stratum `s`. -/
  stratumIndex : strata → ℤ
  /-- Distinct strata occupy distinct filtration steps. -/
  stratumIndex_injective : Function.Injective stratumIndex
  /-- The filtration has no graded pieces beyond those of the strata. -/
  graded_isZero : ∀ p : ℤ, (∀ s, p ≠ stratumIndex s) →
    Limits.IsZero ((CochainComplex.FilteredDerivedCategory.grDF p).obj filtered.obj)

namespace StratifiedDevissage

variable {Λ : Type u} [Ring Λ] [Finite Λ] {strata : Type w}
  (D : StratifiedDevissage.{u, v, w} Λ strata)

/-- The perfect complex `RΓ_c(X_k̄, K)` with its Frobenius action: the complex underlying the
filtration, with the filtration forgotten. -/
public def globalDatum : FrobeniusActionOnCohomology.{u, max u v} Λ :=
  forgetDatum D.filtered D.frobeniusAction

/-- The perfect complex `RΓ_c` of the stratum `s` with its Frobenius action: the graded piece of
the filtration at the index `stratumIndex s`. -/
public def stratumDatum (s : strata) : FrobeniusActionOnCohomology.{u, max u v} Λ :=
  gradedDatum D.filtered D.frobeniusAction (D.stratumIndex s)

/-- The trace of `π_X^*` on the graded piece of the filtration at the index `p`. -/
private def gradedTrace (p : ℤ) : AdditiveCommutatorQuotient Λ :=
  Stacks.EtaleCohomology.gradedTrace D.filtered D.frobeniusAction p

/-- The graded trace at the index of a stratum is the global Lefschetz number of that
stratum. -/
private lemma gradedTrace_stratumIndex (s : strata) :
    D.gradedTrace (D.stratumIndex s) = globalLefschetzNumber Λ (D.stratumDatum s) :=
  rfl

/-- The graded traces away from the strata vanish. -/
private lemma gradedTrace_eq_zero (p : ℤ) (hs : ∀ s, p ≠ D.stratumIndex s) :
    D.gradedTrace p = 0 :=
  gradedTrace_eq_zero_of_isZero _ _ p (D.graded_isZero p hs)

/-- **Dévissage of the global Lefschetz number along a stratification.** The global Lefschetz
number of `X` is the sum over the strata of their global Lefschetz numbers.

This is the additivity of Tag 03TK read off a stratified dévissage, and is the general form of
Step 1 of the proof of Tag 03UG. -/
public theorem globalLefschetzNumber_eq_sum [Fintype strata] :
    globalLefschetzNumber Λ D.globalDatum
      = ∑ s : strata, globalLefschetzNumber Λ (D.stratumDatum s) :=
  calc globalLefschetzNumber Λ D.globalDatum
      = ∑ᶠ p : ℤ, D.gradedTrace p :=
        perfectDerivedTrace_eq_sum_grDF Λ D.filtered D.frobeniusAction
    _ = ∑ s : strata, D.gradedTrace (D.stratumIndex s) :=
        finsum_eq_sum_of_support_subset_range _ D.gradedTrace D.stratumIndex
          D.stratumIndex_injective D.gradedTrace_eq_zero
    _ = ∑ s : strata, globalLefschetzNumber Λ (D.stratumDatum s) :=
        Finset.sum_congr rfl fun s _ => D.gradedTrace_stratumIndex s

/-- A stratification with no strata has global Lefschetz number zero. -/
public theorem globalLefschetzNumber_eq_zero_of_isEmpty [IsEmpty strata] :
    globalLefschetzNumber Λ D.globalDatum = 0 := by
  let : Fintype strata := Fintype.ofIsEmpty
  rw [D.globalLefschetzNumber_eq_sum]
  exact Finset.sum_empty

end StratifiedDevissage

/-- The dévissage of `RΓ(X_k̄, K)` along the rational points of `X`: a filtered perfect complex
of `Λ`-modules with an endomorphism `π_X^*`, whose graded pieces are `RΓ_c(U_k̄, K|_U)` for the
open complement `U = X - X(k)`, at the index `openIndex`, and the stalk `K_x̄` for each
`x ∈ X(k)`, at the index `pointIndex x`.

See [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1. -/
public structure LefschetzDevissage.{u', v', w'} (Λ : Type u') [Ring Λ] [Finite Λ]
    (points : Type w') where
  /-- The filtered perfect complex `RΓ(X_k̄, K̃)` assembled from the short exact sequences
  `0 → j_! j^{-1}K → K → i_* i^{-1}K → 0`. -/
  filtered : CategoryTheory.FilteredDerived.FilteredPerfectData.{u', v'} Λ
  /-- The action `π_X^*` on it, induced by the canonical map `c_K`. -/
  frobeniusAction : filtered.obj ⟶ filtered.obj
  /-- The filtration index whose graded piece is `RΓ_c(U_k̄, K|_U)`. -/
  openIndex : ℤ
  /-- The filtration index whose graded piece is the stalk `K_x̄` at the rational point `x`. -/
  pointIndex : points → ℤ
  /-- Distinct rational points occupy distinct filtration steps. -/
  pointIndex_injective : Function.Injective pointIndex
  /-- The open complement and the rational points occupy distinct filtration steps. -/
  openIndex_ne_pointIndex : ∀ x, openIndex ≠ pointIndex x
  /-- The filtration has no graded pieces beyond the open complement and the stalks at the
  rational points. -/
  graded_isZero : ∀ p : ℤ, p ≠ openIndex → (∀ x, p ≠ pointIndex x) →
    Limits.IsZero ((CochainComplex.FilteredDerivedCategory.grDF p).obj filtered.obj)

namespace LefschetzDevissage

variable {Λ : Type u} [Ring Λ] [Finite Λ] {points : Type w}
  (D : LefschetzDevissage.{u, v, w} Λ points)

/-- A Lefschetz dévissage is the stratified dévissage whose strata are the open complement
together with the rational points: `Option points` indexes them, `none` the open complement
`U = X - X(k)` and `some x` the rational point `x`.  This is the sense in which
`Stacks.EtaleCohomology.StratifiedDevissage` generalises this structure. -/
public def toStratifiedDevissage : StratifiedDevissage.{u, v, w} Λ (Option points) where
  filtered := D.filtered
  frobeniusAction := D.frobeniusAction
  stratumIndex := (Option.elim · D.openIndex D.pointIndex)
  stratumIndex_injective := by
    intro a b hab
    match a, b with
    | none, none => rfl
    | none, some y => exact absurd hab (D.openIndex_ne_pointIndex y)
    | some x, none => exact absurd hab.symm (D.openIndex_ne_pointIndex x)
    | some x, some y => exact congrArg some (D.pointIndex_injective hab)
  graded_isZero p hs := D.graded_isZero p (hs none) fun x => hs (some x)

/-- The perfect complex `RΓ(X_k̄, K)` with its Frobenius action: the complex underlying the
filtration, with the filtration forgotten.  This is the global datum of the stratified dévissage
`toStratifiedDevissage`, so the two carry one definition between them. -/
public def globalDatum : FrobeniusActionOnCohomology.{u, max u v} Λ :=
  D.toStratifiedDevissage.globalDatum

/-- The perfect complex `RΓ_c(U_k̄, K|_U)` of the open complement `U = X - X(k)` with its
Frobenius action: the graded piece of the filtration at the index `openIndex`. -/
public def openDatum : FrobeniusActionOnCohomology.{u, max u v} Λ :=
  gradedDatum D.filtered D.frobeniusAction D.openIndex

/-- The stalks `K_x̄` at the rational points with their Frobenius actions: the graded pieces of
the filtration at the indices `pointIndex x`. -/
public def stalkDatum : FrobeniusActionOnStalks.{u, max u v, w} Λ points where
  stalk x := (gradedDatum D.filtered D.frobeniusAction (D.pointIndex x)).cohomology
  frobeniusAction x := (gradedDatum D.filtered D.frobeniusAction (D.pointIndex x)).frobeniusAction

/-- The underlying perfect complex is unchanged by passing to the stratified dévissage. -/
public lemma toStratifiedDevissage_globalDatum :
    D.toStratifiedDevissage.globalDatum = D.globalDatum :=
  rfl

/-- The stratum of `none` is the open complement. -/
public lemma toStratifiedDevissage_stratumDatum_none :
    D.toStratifiedDevissage.stratumDatum none = D.openDatum :=
  rfl

/-- The stratum of `some x` is the stalk at the rational point `x`. -/
public lemma toStratifiedDevissage_stratumDatum_some (x : points) :
    D.toStratifiedDevissage.stratumDatum (some x)
      = ⟨D.stalkDatum.stalk x, D.stalkDatum.frobeniusAction x⟩ :=
  rfl

/-- **Dévissage of the global Lefschetz number.** The global Lefschetz number of `X` is the
global Lefschetz number of the open complement of `X(k)` plus the local Lefschetz number of
`K`. -/
public theorem globalLefschetzNumber_eq_add [Fintype points] :
    globalLefschetzNumber Λ D.globalDatum =
      globalLefschetzNumber Λ D.openDatum + localLefschetzNumber Λ points D.stalkDatum := by
  have h := D.toStratifiedDevissage.globalLefschetzNumber_eq_sum
  rw [Fintype.sum_option] at h
  exact h

/-- If the global Lefschetz number of the open complement of `X(k)` vanishes then the global
Lefschetz number of `X` equals the local Lefschetz number of `K`. The vanishing is a hypothesis
and not a theorem about a dévissage: the trace of the Frobenius action on the open datum of a
dévissage is unconstrained. -/
public theorem globalLefschetzNumber_eq_localLefschetzNumber_of_openDatum_eq_zero
    [Fintype points] (hopen : globalLefschetzNumber Λ D.openDatum = 0) :
    globalLefschetzNumber Λ D.globalDatum = localLefschetzNumber Λ points D.stalkDatum := by
  rw [D.globalLefschetzNumber_eq_add, hopen, zero_add]

/-- **Agreement of the Lefschetz numbers in dimension zero.** If the graded piece at the index
of the open complement vanishes — the case of a curve all of whose points are rational, in
particular a scheme of dimension zero — then the global and local Lefschetz numbers agree with
no further hypothesis.

See [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2. -/
public theorem globalLefschetzNumber_eq_localLefschetzNumber_of_isZero [Fintype points]
    (hU : Limits.IsZero
      ((CochainComplex.FilteredDerivedCategory.grDF D.openIndex).obj D.filtered.obj)) :
    globalLefschetzNumber Λ D.globalDatum = localLefschetzNumber Λ points D.stalkDatum :=
  D.globalLefschetzNumber_eq_localLefschetzNumber_of_openDatum_eq_zero
    (perfectDerivedTrace_eq_zero_of_isZero Λ _ hU _)

/-- The global and local Lefschetz numbers of a dévissage agree exactly when the global
Lefschetz number of the open complement of `X(k)` vanishes. -/
public theorem globalLefschetzNumber_eq_localLefschetzNumber_iff [Fintype points] :
    globalLefschetzNumber Λ D.globalDatum = localLefschetzNumber Λ points D.stalkDatum ↔
      globalLefschetzNumber Λ D.openDatum = 0 := by
  rw [D.globalLefschetzNumber_eq_add]
  constructor
  · intro h
    refine add_right_cancel (b := localLefschetzNumber Λ points D.stalkDatum) ?_
    rw [zero_add]
    exact h
  · intro h
    rw [h, zero_add]

/-- A curve with no rational points has global Lefschetz number equal to that of its own open
part, so the trace formula there is exactly the vanishing of the latter. -/
public theorem globalLefschetzNumber_eq_of_isEmpty [IsEmpty points] :
    globalLefschetzNumber Λ D.globalDatum = globalLefschetzNumber Λ D.openDatum := by
  let : Fintype points := Fintype.ofIsEmpty
  rw [D.globalLefschetzNumber_eq_add, localLefschetzNumber_of_isEmpty, add_zero]

end LefschetzDevissage

namespace GradedWitness

/-! ### Additive functors and binary biproducts -/

section Biprod

variable {C : Type*} [Category C] {D : Type*} [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

/-- An additive functor preserves binary biproducts: the two comparison maps are inverse. -/
public def addBiprodIso (G : C ⥤ D) [G.Additive] (X Y : C) : G.obj (X ⊞ Y) ≅ G.obj X ⊞ G.obj Y where
  hom := G.biprodComparison X Y
  inv := G.biprodComparison' X Y
  hom_inv_id := by
    rw [Functor.biprodComparison, Functor.biprodComparison', biprod.lift_desc,
      ← G.map_comp, ← G.map_comp, ← G.map_add, biprod.total, G.map_id]
  inv_hom_id := (Functor.splitEpiBiprodComparison G X Y).id

/-- A binary biproduct of two zero objects is a zero object. -/
public lemma isZero_biprod {X Y : C} (hX : IsZero X) (hY : IsZero Y) : IsZero (X ⊞ Y) := by
  rw [IsZero.iff_id_eq_zero, ← biprod.total, hX.eq_of_tgt biprod.fst 0,
    hY.eq_of_tgt biprod.snd 0, zero_comp, zero_comp, add_zero]

/-- A binary biproduct whose second summand is zero is its first summand. -/
public def biprodIsoLeft {X Y : C} (hY : IsZero Y) : X ⊞ Y ≅ X where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    rw [← biprod.total, hY.eq_of_tgt biprod.snd 0, zero_comp, add_zero]
  inv_hom_id := biprod.inl_fst

/-- A binary biproduct whose first summand is zero is its second summand. -/
public def biprodIsoRight {X Y : C} (hX : IsZero X) : X ⊞ Y ≅ Y where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    rw [← biprod.total, hX.eq_of_tgt biprod.fst 0, zero_comp, zero_add]
  inv_hom_id := biprod.inr_snd

end Biprod

variable (R : Type u) [Ring R]

/-! ### Finite projective modules -/

/-- A zero module is finite and projective. -/
public lemma finiteProjective_of_isZero {M : ModuleCat.{max u v} R} (h : IsZero M) :
    Module.Finite R M ∧ Projective M := by
  have := ModuleCat.subsingleton_of_isZero h
  exact ⟨inferInstance, h.projective⟩

/-- Being finite and projective is invariant under isomorphism. -/
public lemma finiteProjective_of_iso {M N : ModuleCat.{max u v} R} (e : M ≅ N)
    (h : Module.Finite R M ∧ Projective M) : Module.Finite R N ∧ Projective N := by
  have := h.1
  exact ⟨Module.Finite.equiv e.toLinearEquiv, Projective.of_iso e h.2⟩

/-- A binary biproduct of finite projective modules is finite and projective. -/
public lemma finiteProjective_biprod {M N : ModuleCat.{max u v} R}
    (hM : Module.Finite R M ∧ Projective M) (hN : Module.Finite R N ∧ Projective N) :
    Module.Finite R (M ⊞ N : ModuleCat.{max u v} R) ∧
      Projective (M ⊞ N : ModuleCat.{max u v} R) := by
  have := hM.1
  have := hN.1
  have := hM.2
  have := hN.2
  exact ⟨Module.Finite.equiv (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv, inferInstance⟩

/-! ### Skyscraper finite filtered objects -/

/-- The finite filtered object with underlying module `M`, with `F^q = M` for `q ≤ j` and
`F^q = 0` for `q > j`; its `j`-th graded piece is `M` and all its other graded pieces vanish. -/
public def sky (j : ℤ) (M : ModuleCat.{max u v} R) : FiniteFilteredObject (ModuleCat.{max u v} R) :=
  ⟨FilteredObject.single j M, Filtration.isFinite_single j M⟩

/-- The step `F^{j+1} ⟶ F^j` of a skyscraper is zero, its source being a zero object. -/
public lemma sky_step_eq_zero (j : ℤ) (M : ModuleCat.{max u v} R) :
    (sky.{u, v} R j M).obj.filtration.step (FilteredObject.succHom j) = 0 :=
  (Filtration.isZero_single_obj_of_lt M (lt_add_one j)).eq_of_src _ _

/-- The `j`-th graded piece of the skyscraper at `j` is its underlying module. -/
public def grSkySelf (j : ℤ) (M : ModuleCat.{max u v} R) :
    (FiniteFilteredObject.grP j).obj (sky.{u, v} R j M) ≅ M :=
  cokernelIsoOfEq (sky_step_eq_zero.{u, v} R j M) ≪≫ cokernelZeroIsoTarget ≪≫
    @asIso _ _ _ _ ((Filtration.single j M).ι.app (op j))
      (Filtration.isIso_single_ι_app j M)

/-- Every graded piece of the skyscraper at `j` other than the `j`-th one vanishes. -/
public lemma isZero_grP_sky_of_ne (j : ℤ) (M : ModuleCat.{max u v} R) (p : ℤ) (h : p ≠ j) :
    IsZero ((FiniteFilteredObject.grP p).obj (sky.{u, v} R j M)) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact FilteredObject.isZero_gr_obj_of_isIso_ι_app _ (n := j) (by omega)
      (Filtration.isIso_single_ι_app j M)
  · exact FilteredObject.isZero_gr_obj_of_isZero _ (m := j + 1) (by omega)
      (Filtration.isZero_single_obj_of_lt M (lt_add_one j))

/-! ### The staircase -/

/-- The free `R`-module of rank one, as an object of `ModuleCat.{max u v} R`. -/
public abbrev freeRankOne : ModuleCat.{max u v} R := ModuleCat.of R (ULift.{v} R)

/-- The free module of rank one is finite and projective. -/
public lemma finiteProjective_freeRankOne :
    Module.Finite R (freeRankOne.{u, v} R) ∧ Projective (freeRankOne.{u, v} R) :=
  ⟨inferInstanceAs (Module.Finite R (ULift.{v} R)),
    (IsProjective.iff_projective (R := R) (ULift.{v} R)).1 inferInstance⟩

/-- The finite filtered module which is free of rank `n` with graded pieces free of rank one at
the filtration indices `1, …, n` and zero at every other index. -/
public def stair : ℕ → FiniteFilteredObject (ModuleCat.{max u v} R)
  | 0 => 0
  | k + 1 => sky.{u, v} R ((k : ℤ) + 1) (freeRankOne.{u, v} R) ⊞ stair k

/-- `stair R 0` is a zero object. -/
public lemma stair_zero : stair.{u, v} R 0 = 0 := rfl

/-- `stair R (k + 1)` adds one skyscraper at the filtration index `k + 1`. -/
public lemma stair_succ (k : ℕ) : stair.{u, v} R (k + 1) =
    (sky.{u, v} R ((k : ℤ) + 1) (freeRankOne.{u, v} R) ⊞ stair.{u, v} R k) := rfl

/-- The graded pieces of `stair R n` vanish outside the filtration indices `1, …, n`. -/
public lemma isZero_grP_stair (n : ℕ) (p : ℤ) (h : p < 1 ∨ (n : ℤ) < p) :
    IsZero ((FiniteFilteredObject.grP p).obj (stair.{u, v} R n)) := by
  induction n with
  | zero => exact (FiniteFilteredObject.grP p).map_isZero (isZero_zero _)
  | succ k ih =>
    have hsky : IsZero ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj
        (sky.{u, v} R ((k : ℤ) + 1) (freeRankOne.{u, v} R))) := by
      refine isZero_grP_sky_of_ne.{u, v} R _ _ p ?_
      push_cast at h
      omega
    have hrest : IsZero ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj
        (stair.{u, v} R k)) := by
      refine ih ?_
      push_cast at h
      omega
    exact (isZero_biprod hsky hrest).of_iso
      (addBiprodIso (FiniteFilteredObject.grP p) _ _)

/-- The `j`-th graded piece of `stair R n` is free of rank one for `1 ≤ j ≤ n`. -/
public lemma grP_stair_iso (n : ℕ) (j : ℤ) (h1 : 1 ≤ j) (h2 : j ≤ (n : ℤ)) :
    Nonempty ((FiniteFilteredObject.grP j).obj (stair.{u, v} R n) ≅ freeRankOne.{u, v} R) := by
  induction n with
  | zero =>
    exfalso
    push_cast at h2
    omega
  | succ k ih =>
    rw [stair_succ]
    by_cases hj : j = (k : ℤ) + 1
    · subst hj
      exact ⟨addBiprodIso (FiniteFilteredObject.grP ((k : ℤ) + 1)) _ _ ≪≫
        biprodIsoLeft (isZero_grP_stair.{u, v} R k ((k : ℤ) + 1) (Or.inr (by omega)))
        ≪≫ grSkySelf.{u, v} R ((k : ℤ) + 1) (freeRankOne.{u, v} R)⟩
    · refine ⟨addBiprodIso (FiniteFilteredObject.grP j) _ _ ≪≫
        biprodIsoRight (isZero_grP_sky_of_ne.{u, v} R _ _ j hj) ≪≫ ?_⟩
      refine (ih ?_).some
      push_cast at h2
      omega

/-- Each graded piece of `stair R n` is a finite projective module. -/
public lemma isFilteredFiniteProjective_stair (n : ℕ) :
    IsFilteredFiniteProjective (stair.{u, v} R n) := by
  induction n with
  | zero =>
    intro p
    rw [stair_zero]
    exact finiteProjective_of_isZero.{u, v} R
      ((FiniteFilteredObject.grP p).map_isZero (isZero_zero _))
  | succ k ih =>
    intro p
    rw [stair_succ]
    refine finiteProjective_of_iso.{u, v} R
      (addBiprodIso (FiniteFilteredObject.grP p) _ _).symm (finiteProjective_biprod R ?_ (ih p))
    by_cases hp : p = (k : ℤ) + 1
    · subst hp
      exact finiteProjective_of_iso.{u, v} R
        (grSkySelf.{u, v} R ((k : ℤ) + 1) (freeRankOne.{u, v} R)).symm
        (finiteProjective_freeRankOne.{u, v} R)
    · exact finiteProjective_of_isZero.{u, v} R (isZero_grP_sky_of_ne.{u, v} R _ _ p hp)

/-! ### The filteredPerfect -/

/-- The representing complex: `stair R n` placed in cochain degree `0`. -/
public def rep (n : ℕ) : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (stair.{u, v} R n)

/-- A complex concentrated in degree `0` is bounded on both sides. -/
public lemma rep_bounded (n : ℕ) :
    CochainComplex.plus _ (rep.{u, v} R n) ∧ CochainComplex.minus _ (rep.{u, v} R n) := by
  constructor
  · refine ⟨0, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · refine ⟨0, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- A finite filtered object which is a zero object is filtered finite projective. -/
public lemma isFilteredFiniteProjective_of_isZero
    {P : FiniteFilteredObject (ModuleCat.{max u v} R)} (h : IsZero P) :
    IsFilteredFiniteProjective P := fun p =>
  finiteProjective_of_isZero.{u, v} R ((FiniteFilteredObject.grP p).map_isZero h)

/-- Filtered finite projectivity is invariant under isomorphism. -/
public lemma isFilteredFiniteProjective_of_iso
    {P Q : FiniteFilteredObject (ModuleCat.{max u v} R)} (e : P ≅ Q)
    (h : IsFilteredFiniteProjective P) : IsFilteredFiniteProjective Q := fun p =>
  finiteProjective_of_iso.{u, v} R ((FiniteFilteredObject.grP p).mapIso e) (h p)

/-- Every term of the representing complex is filtered finite projective. -/
public lemma rep_finiteProjective (n : ℕ) (i : ℤ) :
    IsFilteredFiniteProjective ((rep.{u, v} R n).X i) := by
  by_cases hi : i = 0
  · subst hi
    exact isFilteredFiniteProjective_of_iso.{u, v} R
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (stair.{u, v} R n)).symm (isFilteredFiniteProjective_stair.{u, v} R n)
  · exact isFilteredFiniteProjective_of_isZero.{u, v} R
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- The witness: a filtered perfect complex concentrated in cochain degree `0`, free of rank
`n`, with graded pieces free of rank one at the filtration indices `1, …, n`. -/
public def filteredPerfect (n : ℕ) : FilteredPerfectData.{u, v} R where
  obj := (CochainComplex.FilteredDerivedCategory.Qh).obj
    ((HomotopyCategory.quotient _ _).obj (rep.{u, v} R n))
  representative := rep.{u, v} R n
  bounded := rep_bounded.{u, v} R n
  finiteProjective := rep_finiteProjective.{u, v} R n
  iso := ⟨Iso.refl _⟩

/-- `gr^p` of the witness in the filtered derived category is the image in the derived
category of the complex of `p`-th graded pieces of the representing complex. -/
public lemma graded_iso (n : ℕ) (p : ℤ) :
    Nonempty (DerivedCategory.Q.obj
        (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (rep.{u, v} R n)) ≅
      (CochainComplex.FilteredDerivedCategory.grDF p).obj
        (filteredPerfect.{u, v} R n).obj) := by
  let P := ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (rep.{u, v} R n)
  let qP := (HomotopyCategory.quotient (FiniteFilteredObject
    (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)).obj (rep.{u, v} R n)
  obtain ⟨e⟩ := (filteredPerfect.{u, v} R n).iso
  let η := CategoryTheory.Localization.fac
    ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (CochainComplex.FilteredDerivedCategory.grP_inverts p)
    (CochainComplex.FilteredDerivedCategory.Qh (𝒜 := ModuleCat.{max u v} R))
  exact ⟨((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).app P).symm ≪≫
    (η.app qP).symm ≪≫ (CochainComplex.FilteredDerivedCategory.grDF p).mapIso e⟩

/-- The complex of `p`-th graded pieces of the representing complex is the `p`-th graded piece of
`stair R n` placed in cochain degree `0`. -/
public def repGradedIso (n : ℕ) (p : ℤ) :
    ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (rep.{u, v} R n) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((FiniteFilteredObject.grP p).obj (stair.{u, v} R n)) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p) (ComplexShape.up ℤ)
      (0 : ℤ)).app (stair.{u, v} R n)

/-- **The vanishing.** The `p`-th graded piece of the witness in the filtered derived category
is a zero object for every index `p` outside `1, …, n`; in particular for `p = 0`. -/
public theorem graded_isZero (n : ℕ) (p : ℤ) (h : p < 1 ∨ (n : ℤ) < p) :
    IsZero ((CochainComplex.FilteredDerivedCategory.grDF p).obj
      (filteredPerfect.{u, v} R n).obj) := by
  obtain ⟨e⟩ := graded_iso.{u, v} R n p
  refine IsZero.of_iso ?_ e.symm
  refine DerivedCategory.Q.map_isZero ?_
  refine IsZero.of_iso ?_ (repGradedIso.{u, v} R n p)
  exact (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map_isZero
    (isZero_grP_stair.{u, v} R n p h)

/-- **The non-vanishing.** For `1 ≤ j ≤ n` the `j`-th graded piece of the witness in the
filtered derived category is the image under `DerivedCategory.Q` of the free module of rank one
placed in cochain degree `0`. -/
public theorem graded_iso_freeRankOne (n : ℕ) (j : ℤ) (h1 : 1 ≤ j) (h2 : j ≤ (n : ℤ)) :
    Nonempty ((CochainComplex.FilteredDerivedCategory.grDF j).obj (filteredPerfect.{u, v} R n).obj ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (freeRankOne.{u, v} R))) := by
  obtain ⟨e⟩ := graded_iso.{u, v} R n j
  obtain ⟨i⟩ := grP_stair_iso.{u, v} R n j h1 h2
  exact ⟨e.symm ≪≫ DerivedCategory.Q.mapIso (repGradedIso.{u, v} R n j ≪≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso i)⟩

end GradedWitness

/-! ### Non-vacuity -/

/-- The dévissage realised on the projective line over a finite field with `n` rational points
and constant coefficients `K = Λ`: the filtration of `RΓ(P¹_k̄, Λ)` whose graded pieces are the
free rank-one module `Λ` at the filtration indices `1, …, n`, one for each rational point, with
the Frobenius acting trivially on each, and zero at the index `0` of the open complement. This
exhibits the hypotheses of `LefschetzDevissage` as consistent with `n` rational points and
non-zero graded pieces. -/
public def projectiveLineLefschetzDevissage (Λ : Type u) [Ring Λ] [Finite Λ] (n : ℕ) :
    LefschetzDevissage.{u, v, 0} Λ (Fin n) where
  filtered := GradedWitness.filteredPerfect.{u, v} Λ n
  frobeniusAction := 𝟙 _
  openIndex := 0
  pointIndex x := (x : ℤ) + 1
  pointIndex_injective := by
    intro a b hab
    have hab' : (a : ℤ) + 1 = (b : ℤ) + 1 := hab
    exact Fin.ext (by omega)
  openIndex_ne_pointIndex x := by
    have := x.isLt
    omega
  graded_isZero p _ hx := by
    refine GradedWitness.graded_isZero.{u, v} Λ n p ?_
    rcases lt_or_ge p 1 with h1 | h1
    · exact Or.inl h1
    rcases lt_or_ge (n : ℤ) p with h2 | h2
    · exact Or.inr h2
    exfalso
    have hlt : (p - 1).toNat < n := by omega
    refine hx ⟨(p - 1).toNat, hlt⟩ ?_
    have h0 : (0 : ℤ) ≤ p - 1 := by omega
    change p = ((p - 1).toNat : ℤ) + 1
    rw [Int.toNat_of_nonneg h0]
    ring

/-- Each stalk of the projective-line dévissage is the free rank-one module `Λ` placed in
cochain degree zero, so the model is not the zero model. -/
public theorem projectiveLineLefschetzDevissage_stalk_iso (Λ : Type u) [Ring Λ] [Finite Λ]
    (n : ℕ) (x : Fin n) :
    Nonempty (((projectiveLineLefschetzDevissage.{u, v} Λ n).stalkDatum.stalk x).obj ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (GradedWitness.freeRankOne.{u, v} Λ))) := by
  have := x.isLt
  exact GradedWitness.graded_iso_freeRankOne.{u, v} Λ n ((x : ℤ) + 1) (by omega) (by omega)

/-- **The Lefschetz numbers of the projective line agree.** In the projective-line dévissage the
graded piece of the open complement vanishes, so the global and local Lefschetz numbers agree
with no further hypothesis. Taking `n = q + 1 = #P¹(𝔽_q)` this is the identity of Tag 03TZ for
the projective line over a finite field with constant coefficients. -/
public theorem projectiveLine_globalLefschetzNumber_eq_localLefschetzNumber
    (Λ : Type u) [Ring Λ] [Finite Λ] (n : ℕ) :
    globalLefschetzNumber Λ (projectiveLineLefschetzDevissage.{u, v} Λ n).globalDatum =
      localLefschetzNumber Λ (Fin n)
        (projectiveLineLefschetzDevissage.{u, v} Λ n).stalkDatum :=
  LefschetzDevissage.globalLefschetzNumber_eq_localLefschetzNumber_of_isZero
    (projectiveLineLefschetzDevissage.{u, v} Λ n)
    (GradedWitness.graded_isZero.{u, v} Λ n 0 (Or.inl (by omega)))

/-! ### Galois descent and the trace formula -/

universe t'

/-- If a natural number annihilates a ring then it annihilates its additive commutator
quotient. -/
public theorem natCast_smul_additiveCommutatorQuotient_eq_zero (Λ : Type u) [Ring Λ] (n : ℕ)
    (hn : (n : Λ) = 0) (x : AdditiveCommutatorQuotient Λ) : (n : ℤ) • x = 0 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (additiveCommutatorSubgroup Λ) x
  rw [← map_zsmul]
  have : (n : ℤ) • a = 0 := by
    rw [zsmul_eq_mul]
    simp [hn]
  rw [this, map_zero]

/-- The Galois descent of Steps 7 to 9 of the source's proof of the trace formula, for a
dévissage `D` of `RΓ(X_k̄, K)` along the rational points of `X` and a finite group `group`.

After the reductions of Steps 3 to 6 the open complement `U = X - X(k)` is a smooth irreducible
affine curve with no rational points, the coefficients are a finite locally constant sheaf `F`
with finite projective stalks, and `Λ` is killed by a power `ℓ^m` of a prime `ℓ` invertible in
`k`. Fix a finite étale Galois cover `f : V → U` with group `G = group` such that `f^{-1}F` is
the constant sheaf with value the `Λ[G]`-module `M`, and set `A = Z/ℓ^n Z`. The field
`openDatum_trace_eq` is the decomposition of Step 7 of the trace on the open complement as the
sum over `g ∈ G` of the products of `coefficientTrace g`, the trace
`Tr_A^{Z_g}((g, π_U^*) | RΓ_c(U_k̄, f_*A))`, with `moduleTrace g`, the trace `Tr_Λ(g | M)`. The
field `prime_pow_dvd_coefficientTrace` is the conjunction of Steps 8 and 9: the order
`ℓ^{a_g} = #Z_g` of the stabiliser times `coefficientTrace g` is the trace of `(g^{-1}π_V)^*` on
`RΓ_c(V_k̄, A)`, which vanishes because `g^{-1}π_V` has no fixed point on `V_k̄`.

See [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 7 to 9. -/
public structure LefschetzGaloisDescent.{u', v', w', t''} (Λ : Type u') [Ring Λ] [Finite Λ]
    {points : Type w'} (D : LefschetzDevissage.{u', v', w'} Λ points) (group : Type t'')
    [Fintype group] where
  /-- The prime `ℓ`, invertible in `k`, a power of which annihilates `Λ`. -/
  prime : ℕ
  /-- The number `ℓ` is prime. -/
  prime_prime : Nat.Prime prime
  /-- The exponent `m` of the `ℓ`-power annihilating `Λ`. -/
  exponent : ℕ
  /-- `ℓ^m` annihilates `Λ^natural`. -/
  exponent_smul : ∀ x : AdditiveCommutatorQuotient Λ, ((prime : ℤ) ^ exponent) • x = 0
  /-- A bound `a` on the exponents `a_g` with `#Z_g = ℓ^{a_g}`. -/
  stabilizerBound : ℕ
  /-- The level `n` of the coefficient ring `A = Z/ℓ^n Z`. -/
  level : ℕ
  /-- The level is taken large: `n ≥ a + m`. -/
  stabilizerBound_add_exponent_le : stabilizerBound + exponent ≤ level
  /-- The exponent `a_g` with `#Z_g = ℓ^{a_g}`, for the stabiliser `Z_g` of `g` in the monoid
  extension of `G` by `N`. -/
  stabilizerExponent : group → ℕ
  /-- Each exponent `a_g` is at most the bound `a`. -/
  stabilizerExponent_le : ∀ g : group, stabilizerExponent g ≤ stabilizerBound
  /-- An integer lifting the class of the trace
  `Tr_A^{Z_g}((g, π_U^*) | RΓ_c(U_k̄, f_*A))` in `A = Z/ℓ^n Z`. -/
  coefficientTrace : group → ℤ
  /-- The trace `Tr_Λ(g | M)` of `g` on the `Λ[G]`-module `M = Γ(V, f^{-1}F)`. -/
  moduleTrace : group → AdditiveCommutatorQuotient Λ
  /-- The trace on the open complement is the sum over `G` of the products of the coefficient
  traces with the module traces. -/
  openDatum_trace_eq : globalLefschetzNumber Λ D.openDatum =
    ∑ g : group, coefficientTrace g • moduleTrace g
  /-- The order `ℓ^{a_g}` of the stabiliser `Z_g` annihilates the coefficient trace in
  `A = Z/ℓ^n Z`, the trace of `(g^{-1}π_V)^*` on `RΓ_c(V_k̄, A)` having no fixed point to
  count. -/
  prime_pow_dvd_coefficientTrace : ∀ g : group,
    ((prime : ℤ) ^ level) ∣ ((prime : ℤ) ^ stabilizerExponent g) * coefficientTrace g

namespace LefschetzGaloisDescent

variable {Λ : Type u} [Ring Λ] [Finite Λ] {points : Type w}
  {D : LefschetzDevissage.{u, v, w} Λ points} {group : Type t'} [Fintype group]
  (G : LefschetzGaloisDescent.{u, v, w, t'} Λ D group)

/-- A multiple of `ℓ^m` annihilates `Λ^natural`. -/
private theorem smul_eq_zero_of_prime_pow_exponent_dvd {k : ℤ}
    (hk : ((G.prime : ℤ) ^ G.exponent) ∣ k) (x : AdditiveCommutatorQuotient Λ) : k • x = 0 := by
  obtain ⟨c, rfl⟩ := hk
  rw [mul_comm, mul_smul, G.exponent_smul, smul_zero]

/-- The level `ℓ^n` annihilates `Λ^natural`, so the product of a coefficient trace with a module
trace depends only on the class of the coefficient trace in `A = Z/ℓ^n Z`. -/
public theorem level_smul_eq_zero (x : AdditiveCommutatorQuotient Λ) :
    ((G.prime : ℤ) ^ G.level) • x = 0 :=
  G.smul_eq_zero_of_prime_pow_exponent_dvd
    (pow_dvd_pow _ (le_trans (Nat.le_add_left _ _) G.stabilizerBound_add_exponent_le)) x

/-- Each coefficient trace is divisible by `ℓ^m`: it is annihilated by the order `ℓ^{a_g}` of its
stabiliser in `A = Z/ℓ^n Z`, so it is divisible by `ℓ^{n - a_g}`, and `n - a_g ≥ m`. -/
public theorem prime_pow_exponent_dvd_coefficientTrace (g : group) :
    ((G.prime : ℤ) ^ G.exponent) ∣ G.coefficientTrace g := by
  have hp : (G.prime : ℤ) ≠ 0 := by exact_mod_cast G.prime_prime.ne_zero
  have hle : G.stabilizerExponent g + G.exponent ≤ G.level := by
    have h1 := G.stabilizerExponent_le g
    have h2 := G.stabilizerBound_add_exponent_le
    omega
  have h1 : ((G.prime : ℤ) ^ G.stabilizerExponent g * (G.prime : ℤ) ^ G.exponent) ∣
      ((G.prime : ℤ) ^ G.stabilizerExponent g * G.coefficientTrace g) := by
    rw [← pow_add]
    exact dvd_trans (pow_dvd_pow _ hle) (G.prime_pow_dvd_coefficientTrace g)
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ hp)).mp h1

/-- Every term of the Galois decomposition of the trace on the open complement vanishes: the
coefficient trace is divisible by `ℓ^m` and `ℓ^m` annihilates `Λ^natural`. -/
public theorem coefficientTrace_smul_moduleTrace_eq_zero (g : group) :
    G.coefficientTrace g • G.moduleTrace g = 0 :=
  G.smul_eq_zero_of_prime_pow_exponent_dvd (G.prime_pow_exponent_dvd_coefficientTrace g) _

include G in
/-- **The vanishing of the Lefschetz number of the open complement.** The global Lefschetz number
of the open complement `U = X - X(k)` vanishes, every term of its Galois decomposition doing so.

See [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 7 to 9. -/
public theorem openDatum_eq_zero : globalLefschetzNumber Λ D.openDatum = 0 := by
  rw [G.openDatum_trace_eq]
  exact Finset.sum_eq_zero fun g _ => G.coefficientTrace_smul_moduleTrace_eq_zero g

include G in
/-- **The Lefschetz numbers of a dévissage with a Galois descent agree.** For a dévissage `D` of
`RΓ(X_k̄, K)` along the rational points of `X` equipped with a Galois descent `G`, the global and
local Lefschetz numbers read off `D` are equal:

  `Tr(π_X^* | RΓ(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in `Λ^natural`. The dévissage splits the left hand side into the trace on the open complement of
`X(k)` plus the right hand side, and the Galois descent makes the trace on the open complement
vanish. This is the shape of the argument of Steps 7 to 9 of the proof of Tag 03UG, for the data
of a `LefschetzDevissage` and a `LefschetzGaloisDescent`; the Lefschetz trace formula of
Tag 03TZ itself, for a projective curve over a finite field and `K ∈ D_ctf(X, Λ)`, is
`Stacks.EtaleCohomology.globalLefschetzNumberOfCtf_eq_sum_rationalPointStalkTrace`. -/
public theorem globalLefschetzNumber_eq_localLefschetzNumber [Fintype points] :
    globalLefschetzNumber Λ D.globalDatum = localLefschetzNumber Λ points D.stalkDatum :=
  D.globalLefschetzNumber_eq_localLefschetzNumber_of_openDatum_eq_zero G.openDatum_eq_zero

end LefschetzGaloisDescent

/-- A Galois descent realised on the projective-line dévissage, over a finite ring `Λ` killed by
`ℓ^m` for a prime `ℓ`: one group element, the coefficient trace `ℓ^m`, which is non-zero, and an
arbitrary module trace. This exhibits the hypotheses of
`Stacks.EtaleCohomology.LefschetzGaloisDescent` as consistent and as not forcing the data to
vanish. -/
public def projectiveLineLefschetzGaloisDescent (Λ : Type u) [Ring Λ] [Finite Λ]
    (ℓ m a n : ℕ) (hℓ : Nat.Prime ℓ) (hΛ : ((ℓ ^ m : ℕ) : Λ) = 0)
    (x : AdditiveCommutatorQuotient Λ) :
    LefschetzGaloisDescent.{u, v, 0, 0} Λ
      (projectiveLineLefschetzDevissage.{u, v} Λ n) PUnit where
  prime := ℓ
  prime_prime := hℓ
  exponent := m
  exponent_smul y := by
    simpa using natCast_smul_additiveCommutatorQuotient_eq_zero Λ (ℓ ^ m) hΛ y
  stabilizerBound := a
  level := a + m
  stabilizerBound_add_exponent_le := le_refl _
  stabilizerExponent _ := a
  stabilizerExponent_le _ := le_refl _
  coefficientTrace _ := (ℓ : ℤ) ^ m
  moduleTrace _ := x
  openDatum_trace_eq := by
    have hopen : globalLefschetzNumber Λ
        (projectiveLineLefschetzDevissage.{u, v} Λ n).openDatum = 0 :=
      perfectDerivedTrace_eq_zero_of_isZero Λ _
        (GradedWitness.graded_isZero.{u, v} Λ n 0 (Or.inl (by omega))) _
    have hterm : ((ℓ : ℤ) ^ m) • x = 0 := by
      simpa using natCast_smul_additiveCommutatorQuotient_eq_zero Λ (ℓ ^ m) hΛ x
    rw [hopen]
    simp [hterm]
  prime_pow_dvd_coefficientTrace _ := dvd_of_eq (pow_add _ _ _)

/-- The hypothesis of `Stacks.EtaleCohomology.projectiveLineLefschetzGaloisDescent` that `ℓ^m`
annihilate the coefficient ring is satisfied by the finite ring `Z/ℓ^m Z`. -/
public theorem zmod_natCast_prime_pow_eq_zero (ℓ m : ℕ) [NeZero (ℓ ^ m)] :
    ((ℓ ^ m : ℕ) : ZMod (ℓ ^ m)) = 0 :=
  ZMod.natCast_self _

end Stacks.EtaleCohomology

end

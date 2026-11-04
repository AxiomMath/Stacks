module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LefschetzTraceFormula

/-!
# Dévissage of the Lefschetz number along a finite stratification

Let `Λ` be a finite ring, `k` a finite field, `X` a separated scheme of finite type over `k`
and `K` an object of `D_ctf(X, Λ)`. The trace formula of Tag 03V3 is the identity

  `Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in the additive commutator quotient `Λ^natural`, together with the perfectness
`RΓ_c(X_k̄, K) ∈ D_perf(Λ)`. The source proves it by reduction: the identity is established
first for schemes of dimension at most one, which is Tag 03UG, and the general case follows
from that case together with proper base change.

This file carries that reduction. Writing `X` as a finite disjoint union of strata, the short
exact sequences `0 → j_! j^{-1}K → K → i_* i^{-1}K → 0` of a stratum and its complement
assemble `RΓ_c(X_k̄, K)` into a filtered perfect complex of `Λ`-modules whose graded pieces are
the `RΓ_c` of the strata, one for each stratum and nothing else. That is the datum
`StratifiedDevissage`, which generalises the `LefschetzDevissage` of Tag 03TZ: the latter has
one distinguished open graded piece and one graded piece for each rational point, whereas here
the graded pieces are indexed by an arbitrary finite family of strata.

Additivity of the trace along a filtration, Tag 03TK, then computes the global Lefschetz number
of `X` as the sum over the strata of their global Lefschetz numbers. If each stratum satisfies
the trace identity of Tag 03UG — the hypothesis the source discharges for strata of dimension
at most one — then, since `X(k)` is the disjoint union of the sets of rational points of the
strata, the sum over the strata of their local Lefschetz numbers is the local Lefschetz number
of `X`, and the trace formula for `X` follows. That last step is where this file stops: the
identity on a stratum is a hypothesis here and not a theorem, so nothing in this file is
offered as a formalization of the trace formula itself.

`Stacks.EtaleCohomology.StratifiedDevissage` itself, its data and its dévissage identity live in
`Stacks.EtaleCohomology.LefschetzTraceFormula`, below this file: a Lefschetz dévissage is an
instance of it, so the general notion has to be available there.

## Main definitions

* `Stacks.EtaleCohomology.sigmaStalkDatum` — the stalk data of Tag 03TY on the disjoint union
  `X(k) = ⊔_s (stratum s)(k)` of the rational points of the strata.
* `Stacks.EtaleCohomology.pointStalkDatum` — a perfect complex with an endomorphism read as the
  stalk datum at a single rational point.

## Main results

* `Stacks.EtaleCohomology.localLefschetzNumber_sigmaStalkDatum` — the local Lefschetz number of
  the disjoint union of the rational points of the strata is the sum over the strata of their
  local Lefschetz numbers.
* `Stacks.EtaleCohomology.globalLefschetzNumber_eq_localLefschetzNumber_sigma` — the reduction
  itself: given the trace identity on each stratum, the global and local Lefschetz numbers of
  `X` agree. This carries no tag, for the reason recorded under the implementation notes.
* `Stacks.EtaleCohomology.stairStratifiedDevissage` and
  `Stacks.EtaleCohomology.stair_globalLefschetzNumber_eq_localLefschetzNumber` — a stratified
  dévissage with `n` strata and non-zero graded pieces, each stratum a single rational point,
  and the agreement of the two numbers for it. This exhibits the hypotheses as consistent and
  not satisfied only vacuously; it is the zero-dimensional case.

## Implementation notes

The coefficient ring is an arbitrary, possibly noncommutative, finite ring, as in the source,
and the traces are those of `CategoryTheory.FilteredDerived.perfectDerivedTrace`, valued in
`Λ^natural`. The ring, module and stratum universes are independent.

The dévissage is taken as data rather than constructed from the geometry. No field of
`StratifiedDevissage` is an identity between traces: the structure carries the filtered perfect
complex, the Frobenius action on it, the filtration indices of the graded pieces and the
statement that there are no further graded pieces. In particular the perfectness of
`RΓ_c(X_k̄, K)` over a finite possibly noncommutative `Λ`, which is Tag 03TV, is carried by
`CategoryTheory.FilteredDerived.FilteredPerfectData` rather than proved; this is the same
convention under which Tags 03TX and 03TY are stated in this development, the geometric input
entering only as the perfect complex and the endomorphism of it. Producing that datum from a
separated finite type `X` over `k` and an object of `D_ctf(X, Λ)` needs Tag 03TV, which is not
available here.

`globalLefschetzNumber_eq_sum` is unconditional and is the substance of this file: additivity
of the trace along the filtration, Tag 03TK, applied to a family of graded pieces indexed by an
arbitrary finite type. Together with `localLefschetzNumber_sigmaStalkDatum` it is the engine of
the reduction the source runs, and both are theorems about the structure with no hypotheses
beyond it.

`globalLefschetzNumber_eq_localLefschetzNumber_sigma` deliberately carries no tag. Its
hypothesis is that the trace identity holds on each stratum, and a single stratum is a
stratification of `X` by `X` itself, so in that instance the hypothesis is the conclusion; a tag
on it would therefore record the trace formula as established on the strength of itself. The
identity on a stratum of dimension at most one is Tag 03UG, and what the source proves there is
not derivable from a `StratifiedDevissage`: the graded piece at a stratum is an arbitrary
perfect complex of `Λ`-modules carrying an arbitrary endomorphism, whose trace can be any
element of `Λ^natural`, so nothing about the strata follows from the structure alone. The
missing geometric input is Steps 1 to 6 of the source's proof — the reduction of a separated
finite type scheme of dimension at most one to a smooth irreducible affine curve with no
rational points, a finite étale Galois cover trivialising the coefficients, and the
identification of `f_* f^{-1}F` through the trace map of Tag 03SE. Once that input is available,
the hypothesis of this theorem is discharged stratum by stratum and the tag can be placed
without the degeneracy just described.

The non-vacuity statement reuses the filtered perfect complex of
`Stacks.EtaleCohomology.GradedWitness`: the iterated binary biproduct of skyscraper filtered
modules, free of rank `n` with graded pieces free of rank one at the filtration indices
`1, …, n` and zero elsewhere, placed in cochain degree zero. Taking each stratum to be a single
rational point, on whose stalk the geometric Frobenius acts trivially, every graded piece is
non-zero and the identity holds unconditionally.

One elementary fact is proved on the way and kept private: a sum over `ℤ` supported on the image
of an injection from a finite type is the finite sum over that type.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03TK](https://stacks.math.columbia.edu/tag/03TK)
* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
* [Stacks Project, Tag 03TY](https://stacks.math.columbia.edu/tag/03TY)
* [Stacks Project, Tag 03TZ](https://stacks.math.columbia.edu/tag/03TZ)
* [Stacks Project, Tag 03U3](https://stacks.math.columbia.edu/tag/03U3)
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.FilteredDerived
open CategoryTheory.Limits

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The rational points of the strata -/

/-- The stalk data of Tag 03TY on the disjoint union `X(k) = ⊔_s (stratum s)(k)` of the sets of
rational points of the strata: at a point of the stratum `s` it is the stalk datum of `s`
there. -/
public def sigmaStalkDatum (Λ : Type u) [Ring Λ] [Finite Λ] {strata : Type w}
    {pts : strata → Type w}
    (St : (s : strata) → FrobeniusActionOnStalks.{u, v, w} Λ (pts s)) :
    FrobeniusActionOnStalks.{u, v, w} Λ (Σ s : strata, pts s) where
  stalk x := (St x.1).stalk x.2
  frobeniusAction x := (St x.1).frobeniusAction x.2

/-- The local Lefschetz number over the disjoint union of the rational points of the strata is
the sum over the strata of their local Lefschetz numbers. -/
public theorem localLefschetzNumber_sigmaStalkDatum (Λ : Type u) [Ring Λ] [Finite Λ]
    {strata : Type w} [Fintype strata] {pts : strata → Type w} [∀ s, Fintype (pts s)]
    (St : (s : strata) → FrobeniusActionOnStalks.{u, v, w} Λ (pts s)) :
    localLefschetzNumber Λ (Σ s : strata, pts s) (sigmaStalkDatum.{u, v, w} Λ St)
      = ∑ s : strata, localLefschetzNumber Λ (pts s) (St s) := by
  rw [localLefschetzNumber, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  exact Finset.sum_congr rfl fun s _ => rfl

/-- A perfect complex with an endomorphism, read as the stalk datum of Tag 03TY at a single
rational point. -/
public def pointStalkDatum (Λ : Type u) [Ring Λ] [Finite Λ]
    (D : FrobeniusActionOnCohomology.{u, v} Λ) :
    FrobeniusActionOnStalks.{u, v, 0} Λ Unit where
  stalk _ := D.cohomology
  frobeniusAction _ := D.frobeniusAction

/-- The local Lefschetz number of a single rational point is the global Lefschetz number of the
complex sitting there. This is the identification the source makes in Step 2 of the proof of
Tag 03UG for a scheme of dimension zero. -/
public theorem localLefschetzNumber_pointStalkDatum (Λ : Type u) [Ring Λ] [Finite Λ]
    (D : FrobeniusActionOnCohomology.{u, v} Λ) :
    localLefschetzNumber Λ Unit (pointStalkDatum.{u, v} Λ D) = globalLefschetzNumber Λ D := by
  rw [localLefschetzNumber_unique]
  rfl

/-! ### The trace formula for a stratified scheme -/

/-- **The trace formula for a stratified scheme, from the trace formula on the strata.** Let `Λ`
be a finite ring, `k` a finite field, `X` a separated scheme of finite type over `k` and `K` an
object of `D_ctf(X, Λ)`. Write `X` as a finite disjoint union of strata and let `D` be the
resulting dévissage of `RΓ_c(X_k̄, K)`, whose graded pieces are the `RΓ_c` of the strata.
Suppose each stratum satisfies the trace identity, namely that its global Lefschetz number is
the local Lefschetz number of its own rational points. Then the global Lefschetz number of `X`
is the local Lefschetz number of `X`, the set `X(k)` of rational points of `X` being the
disjoint union of those of the strata:

  `Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`.

This is the shape of the reduction by which the source deduces the general-dimension trace
formula from the case of dimension at most one. It carries no tag: a single stratum is a
stratification of `X` by `X` itself, so in that instance the hypothesis `hstratum` is the
conclusion, and the discussion under the implementation notes of this file records what is
needed before the tag can be placed. -/
public theorem globalLefschetzNumber_eq_localLefschetzNumber_sigma {Λ : Type u} [Ring Λ]
    [Finite Λ] {strata : Type w} [Fintype strata]
    (D : StratifiedDevissage.{u, v, w} Λ strata) {pts : strata → Type w}
    [∀ s, Fintype (pts s)]
    (St : (s : strata) → FrobeniusActionOnStalks.{u, max u v, w} Λ (pts s))
    (hstratum : ∀ s, globalLefschetzNumber Λ (D.stratumDatum s)
      = localLefschetzNumber Λ (pts s) (St s)) :
    globalLefschetzNumber Λ D.globalDatum
      = localLefschetzNumber Λ (Σ s : strata, pts s)
          (sigmaStalkDatum.{u, max u v, w} Λ St) := by
  rw [D.globalLefschetzNumber_eq_sum, localLefschetzNumber_sigmaStalkDatum]
  exact Finset.sum_congr rfl fun s _ => hstratum s

/-! ### Non-vacuity -/

/-- The stratified dévissage with `n` strata realised on the filtered perfect complex of
`Stacks.EtaleCohomology.GradedWitness`: the graded piece of the stratum `s` is the free
rank-one module `Λ` at the filtration index `s + 1`, with the Frobenius acting trivially, and
there are no other graded pieces. This exhibits the hypotheses of `StratifiedDevissage` as
consistent with `n` strata and non-zero graded pieces. -/
public def stairStratifiedDevissage (Λ : Type u) [Ring Λ] [Finite Λ] (n : ℕ) :
    StratifiedDevissage.{u, v, 0} Λ (Fin n) where
  filtered := GradedWitness.filteredPerfect.{u, v} Λ n
  frobeniusAction := 𝟙 _
  stratumIndex x := (x : ℤ) + 1
  stratumIndex_injective := by
    intro a b hab
    have hab' : (a : ℤ) + 1 = (b : ℤ) + 1 := hab
    exact Fin.ext (by omega)
  graded_isZero p hs := by
    refine GradedWitness.graded_isZero.{u, v} Λ n p ?_
    rcases lt_or_ge p 1 with h1 | h1
    · exact Or.inl h1
    rcases lt_or_ge (n : ℤ) p with h2 | h2
    · exact Or.inr h2
    exfalso
    have hlt : (p - 1).toNat < n := by omega
    refine hs ⟨(p - 1).toNat, hlt⟩ ?_
    have h0 : (0 : ℤ) ≤ p - 1 := by omega
    change p = ((p - 1).toNat : ℤ) + 1
    rw [Int.toNat_of_nonneg h0]
    ring

/-- Each graded piece of the staircase stratified dévissage is the free rank-one module `Λ`
placed in cochain degree zero, so the model is not the zero model. -/
public theorem stairStratifiedDevissage_stratum_iso (Λ : Type u) [Ring Λ] [Finite Λ] (n : ℕ)
    (s : Fin n) :
    Nonempty (((stairStratifiedDevissage.{u, v} Λ n).stratumDatum s).cohomology.obj ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (GradedWitness.freeRankOne.{u, v} Λ))) := by
  have := s.isLt
  exact GradedWitness.graded_iso_freeRankOne.{u, v} Λ n ((s : ℤ) + 1) (by omega) (by omega)

/-- **The trace formula for the staircase stratified dévissage.** Taking each of the `n` strata
to be a single rational point, every stratum satisfies the identity of Tag 03UG by
`localLefschetzNumber_pointStalkDatum`, so the global and local Lefschetz numbers agree with no
further hypothesis. The graded pieces are all non-zero, so the hypotheses of
`globalLefschetzNumber_eq_localLefschetzNumber_sigma` are not satisfied only vacuously; this is
the zero-dimensional case, where every stratum is a rational point. -/
public theorem stair_globalLefschetzNumber_eq_localLefschetzNumber (Λ : Type u) [Ring Λ]
    [Finite Λ] (n : ℕ) :
    globalLefschetzNumber Λ (stairStratifiedDevissage.{u, v} Λ n).globalDatum
      = localLefschetzNumber Λ (Σ _ : Fin n, Unit)
          (sigmaStalkDatum.{u, max u v, 0} Λ fun s =>
            pointStalkDatum.{u, max u v} Λ
              ((stairStratifiedDevissage.{u, v} Λ n).stratumDatum s)) :=
  globalLefschetzNumber_eq_localLefschetzNumber_sigma
    (stairStratifiedDevissage.{u, v} Λ n) _
    fun _ => (localLefschetzNumber_pointStalkDatum.{u, max u v} Λ _).symm

end Stacks.EtaleCohomology

end

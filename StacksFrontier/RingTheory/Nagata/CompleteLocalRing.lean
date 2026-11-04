module

import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PowerSeries.Ideal

public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.Nagata.PowerSeries
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# A Noetherian complete local ring is a Nagata ring

Let `R` be a Noetherian local ring which is complete for the topology defined by its maximal
ideal. This file proves that `R` is a Nagata ring: every quotient of `R` by a prime ideal is
N-2 (Japanese).

The proof is the source's. A quotient `R ⧸ p` of a Noetherian complete local ring is again one
(Stacks 0325), so the content is that a Noetherian complete local *domain* `R` is N-2. Such an `R`
is a finite extension of a power series ring `Λ[[X_1, …, X_d]]` over a field or over a Cohen ring
`Λ`, by an injective map (Stacks 032D), and N-2 ascends along an injective quasi-finite — in
particular along an injective finite — extension of domains (Stacks 032I); so it suffices to see
that `Λ[[X_1, …, X_d]]` is N-2. Adjoining one variable at a time preserves N-2 (Stacks 032Q), and
this leaves `Λ`. A field is N-2, its integral closure in a finite extension `L` of its fraction
field being a submodule of the finite-dimensional space `L`. A Cohen ring `Λ` is N-2 by Tate's
theorem (Stacks 032P) applied with `x = p` the prime generating its maximal ideal: `Λ` is a
Noetherian integrally closed domain, it is `p`-adically complete, and `Λ ⧸ pΛ` is its residue
field, hence N-2 by the case of a field again.

## Main results

* `Stacks.Nagata.CompleteLocalRing.solution`: the proof of
  `IsNagataRing.of_isPrecomplete_maximalIdeal`, Stacks 032W.

## Implementation notes

The domain case of the theorem is `isJapaneseRing_of_isPrecomplete_maximalIdeal`; it is where
Stacks 032D and Stacks 032I meet, and everything else in the file feeds it. Four of its steps are
named here as private lemmas because the source states them nowhere and Mathlib has none of them:
N-2 for a field (`isJapaneseRing_of_isField`), N-2 for a Cohen ring
(`isJapaneseRing_of_isCohenRing`), and N-2 for a power series ring in finitely many variables
(`isJapaneseRing_mvPowerSeries_fin`, the iteration of Stacks 032Q along
`MvPowerSeries.finSuccEquiv`).

The quotient step, Stacks 0325, is proved here from its general module-theoretic reason:
`I`-adic precompleteness passes to surjective images (`isPrecomplete_of_surjective`). Indeed
precompleteness of `M` says exactly that `M → AdicCompletion I M` is surjective
(`AdicCompletion.of_surjective_iff`) and adic completion preserves surjections
(`AdicCompletion.map_surjective`), so for `f : M → N` surjective the composite
`M → N → AdicCompletion I N`, which is `AdicCompletion I f` after `M → AdicCompletion I M`, is
surjective, and hence so is `N → AdicCompletion I N`. The ring statement
`isPrecomplete_maximalIdeal_of_surjective` follows by reading the maximal ideal of the image as the
image of the maximal ideal and changing the base ring back along
`IsPrecomplete.map_algebraMap_iff`.
Mathlib has neither the module statement nor the ring one.

Completeness of `R` is `IsPrecomplete (maximalIdeal R) R`, as in the statement, at every step; the
Hausdorff half of `IsAdicComplete` is an instance for a Noetherian local ring, so the
`IsAdicComplete` that Stacks 032D consumes is assembled from the hypothesis by `⟨⟩`.

## References

* [Stacks Project, Tag 032W](https://stacks.math.columbia.edu/tag/032W)
* [Stacks Project, Tag 0325](https://stacks.math.columbia.edu/tag/0325)
* [Stacks Project, Tag 032D](https://stacks.math.columbia.edu/tag/032D)
* [Stacks Project, Tag 032I](https://stacks.math.columbia.edu/tag/032I)
* [Stacks Project, Tag 032P](https://stacks.math.columbia.edu/tag/032P)
* [Stacks Project, Tag 032Q](https://stacks.math.columbia.edu/tag/032Q)
-/

@[expose] public section

namespace Stacks.Nagata.CompleteLocalRing

open IsLocalRing



/-- The multivariable power series ring over a domain is a domain. Mathlib has both halves,
`MvPowerSeries.instNoZeroDivisors` and nontriviality, but not the bundled `IsDomain`; it is a local
instance here because `IsJapaneseRing (MvPowerSeries σ A)` cannot be stated without it. -/
private theorem isDomain_mvPowerSeries {σ : Type*} {A : Type*} [CommRing A] [IsDomain A] :
    IsDomain (MvPowerSeries σ A) := by constructor

attribute [local instance] isDomain_mvPowerSeries

open _root_.AdicCompletion in
/-- Precompleteness passes to surjective images: if `M` is `I`-adically precomplete and
`f : M → N` is a surjective linear map, then `N` is `I`-adically precomplete.

Precompleteness of `M` is surjectivity of `M → AdicCompletion I M`, and adic completion preserves
surjections, so `N → AdicCompletion I N` is surjective already on the image of `f`. -/
private theorem isPrecomplete_of_surjective {R : Type*} [CommRing R] {I : Ideal R}
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsPrecomplete I M] {f : M →ₗ[R] N} (hf : Function.Surjective f) : IsPrecomplete I N := by
  rw [← of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := map_surjective I hf y
  obtain ⟨m, rfl⟩ := of_surjective (I := I) (M := M) x
  exact ⟨f m, (map_of I f m).symm⟩

/-- A local ring which is a quotient of a local ring complete for its maximal-ideal-adic topology
is again complete for its own maximal-ideal-adic topology, the maximal ideal of the image being the
image of the maximal ideal. This is the quotient case of Stacks 0325, without the Noetherian
hypothesis. -/
private theorem isPrecomplete_maximalIdeal_of_surjective {R S : Type u} [CommRing R]
    [IsLocalRing R] [IsPrecomplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) : IsPrecomplete (maximalIdeal S) S := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) h,
    IsPrecomplete.map_algebraMap_iff]
  exact isPrecomplete_of_surjective (f := Algebra.linearMap R S) h

/-- A field is N-2: the integral closure of a field `K` in a finite extension `L` of its field of
fractions is a submodule of `L`, which is finite-dimensional over `K`. -/
private theorem isJapaneseRing_of_isField {K : Type u} [CommRing K] [IsDomain K]
    (hK : IsField K) : IsJapaneseRing K := by
  let := hK.toField
  refine { finite := fun L _ _ _ _ _ => ?_ }
  have : Module.Finite K (FractionRing K) :=
    Module.Finite.equiv (FractionRing.algEquiv K K).symm.toLinearEquiv
  have : Module.Finite K L := Module.Finite.trans (FractionRing K) L
  exact Module.Finite.of_injective (Subalgebra.val (integralClosure K L)).toLinearMap
    Subtype.val_injective

/-- A Cohen ring is N-2. It is a Noetherian integrally closed domain, complete for the `p`-adic
topology defined by the prime `p` generating its maximal ideal, and its quotient by that ideal is
its residue field, so Tate's theorem (Stacks 032P) applies. -/
@[ega "0 23.1.5" "special case"]
private theorem isJapaneseRing_of_isCohenRing {Λ : Type u} [CommRing Λ] [IsDomain Λ]
    (hΛ : IsCohenRing Λ) : IsJapaneseRing Λ := by
  have := hΛ
  obtain ⟨p, -, hspan⟩ := IsCohenRing.exists_prime_maximalIdeal_eq_span (R := Λ)
  have hmax : (Ideal.span {(p : Λ)}).IsMaximal := hspan ▸ maximalIdeal.isMaximal Λ
  have : (Ideal.span {(p : Λ)}).IsPrime := hmax.isPrime
  have : IsPrecomplete (Ideal.span {(p : Λ)}) Λ := hspan ▸ inferInstance
  exact IsJapaneseRing.of_quotient_span_singleton (p : Λ)
    (isJapaneseRing_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax))

/-- The coefficient ring of a Cohen presentation — a field or a Cohen ring — is Noetherian. -/
private theorem isNoetherianRing_of_isField_or_isCohenRing {Λ : Type u} [CommRing Λ] [IsDomain Λ]
    (h : IsField Λ ∨ IsCohenRing Λ) : IsNoetherianRing Λ := by
  obtain hfield | hcohen := h
  · let := hfield.toField; infer_instance
  · have := hcohen; infer_instance

/-- The coefficient ring of a Cohen presentation — a field or a Cohen ring — is N-2. -/
@[ega "0 23.1.5" "special case"]
private theorem isJapaneseRing_of_isField_or_isCohenRing {Λ : Type u} [CommRing Λ] [IsDomain Λ]
    (h : IsField Λ ∨ IsCohenRing Λ) : IsJapaneseRing Λ :=
  h.elim isJapaneseRing_of_isField isJapaneseRing_of_isCohenRing

/-- The power series ring in `d` variables over a Noetherian N-2 domain is N-2, by `d`-fold
application of Stacks 032Q along `MvPowerSeries.finSuccEquiv`. -/
@[ega "0 23.1.4" "more general", ega "0 23.1.5" "special case"]
private theorem isJapaneseRing_mvPowerSeries_fin {Λ : Type u} [CommRing Λ] [IsDomain Λ]
    [IsNoetherianRing Λ] (hΛ : IsJapaneseRing Λ) (d : ℕ) :
    IsJapaneseRing (MvPowerSeries (Fin d) Λ) := by
  induction d with
  | zero =>
      exact IsJapaneseRing.of_ringEquiv
        (MvPowerSeries.isEmptyEquiv (Fin 0) Λ).symm.toRingEquiv hΛ
  | succ n ih =>
      exact IsJapaneseRing.of_ringEquiv
        (MvPowerSeries.finSuccEquiv Λ n).symm.toRingEquiv (PowerSeries.isJapaneseRing ih)

/-- **A Noetherian complete local domain is N-2.** This is the content of Stacks 032W: `R` is an
injective finite extension of a power series ring `Λ[[X_1, …, X_d]]` whose coefficient ring `Λ` is
a field or a Cohen ring (Stacks 032D), that power series ring is N-2, and N-2 ascends along an
injective quasi-finite extension of domains (Stacks 032I). -/
@[ega "0 23.1.5"]
private theorem isJapaneseRing_of_isPrecomplete_maximalIdeal (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] [IsPrecomplete (maximalIdeal R) R] :
    IsJapaneseRing R := by
  have : IsAdicComplete (maximalIdeal R) R := ⟨⟩
  obtain ⟨d, Λ, hring, hdom, hcase, -, -, f, hinj, hfin, -⟩ :=
    IsLocalRing.exists_injective_finite_mvPowerSeries R
  let := hring
  let := hdom
  let := isNoetherianRing_of_isField_or_isCohenRing hcase
  let : Algebra (MvPowerSeries (Fin d) Λ) R := f.toAlgebra
  have : FaithfulSMul (MvPowerSeries (Fin d) Λ) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Module.Finite (MvPowerSeries (Fin d) Λ) R := hfin
  exact isJapaneseRing_of_quasiFinite
    (isJapaneseRing_mvPowerSeries_fin (isJapaneseRing_of_isField_or_isCohenRing hcase) d)

/-- **Stacks Tag 032W.** A Noetherian local ring that is complete with respect to its maximal ideal
is a Nagata ring. -/
public theorem solution {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (IsLocalRing.maximalIdeal R) R] :
    IsNagataRing R := by
  refine ⟨inferInstance, fun p hp => ?_⟩
  have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  let : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsPrecomplete (maximalIdeal (R ⧸ p)) (R ⧸ p) :=
    isPrecomplete_maximalIdeal_of_surjective (R := R) Ideal.Quotient.mk_surjective
  exact isJapaneseRing_of_isPrecomplete_maximalIdeal (R ⧸ p)

end Stacks.Nagata.CompleteLocalRing

end

/-!
# A Noetherian complete local ring is a Nagata ring

Let `R` be a Noetherian local ring that is complete for the topology defined by its maximal
ideal `m`. Then `R` is a **Nagata ring**: it is Noetherian, and for every prime `p ⊆ R` the
quotient domain `R ⧸ p` is N-2 (Japanese), i.e. its integral closure in every finite extension
of `Frac(R ⧸ p)` is a finite `R ⧸ p`-module.

Completeness is what carries the statement. Every quotient `R ⧸ p` is again a Noetherian complete
local ring (Tag 0325), so the content is that a Noetherian complete local *domain* is N-2, and
the Cohen structure theorem reduces that to `k[[X_1, …, X_d]]` for a field `k` and to
`Λ[[X_1, …, X_d]]` for a Cohen ring `Λ` (Tags 032I and 032D). Tate's theorem (Tag 032P), applied
along the variables `X_i` and, in the mixed characteristic case, once more along `p ∈ Λ`, brings
both down to the statement that a field is N-2, which is trivial.

## Main results

* `IsNagataRing.of_isPrecomplete_maximalIdeal`: a Noetherian complete local ring is a Nagata
  ring.

## Implementation notes

"Complete local ring" is, as in Tag 032B and Definition 0316, a local ring `R` for which the
canonical map `R → lim_n R ⧸ mⁿ` is an isomorphism, and the Noetherian hypothesis is carried
separately; here that is `[IsLocalRing R]`, `[IsNoetherianRing R]` and completeness for the
`m`-adic filtration. Nothing is bundled: the three are instance binders, so a caller with a
Noetherian complete local ring in hand needs no packaging step, and the project's structure
`IsNoetherianCompleteLocalRing` (Tag 0325) is not interposed between the source's hypothesis and
Lean's.

Completeness is asked for as `IsPrecomplete (IsLocalRing.maximalIdeal R) R`, the surjectivity
half of `IsAdicComplete`, rather than `IsAdicComplete` itself: the Hausdorff half `⋂ₙ mⁿ = 0` is
automatic for a Noetherian local ring by Krull's intersection theorem, and is already an instance
in Mathlib (`instIsHausdorffMaximalIdeal`), so asking for it would be asking for something free.
A ring carrying `IsAdicComplete (IsLocalRing.maximalIdeal R) R` satisfies the hypothesis by
instance inference, `IsAdicComplete` bundling `IsPrecomplete`. This follows the sibling statement
of Tag 032P, whose completeness hypothesis is weakened the same way for the same reason.

The Noetherian hypothesis is not redundant with `IsNagataRing`'s own first clause: it is what the
proof consumes, through Tag 0325 and the Cohen structure theorem, to produce the second clause,
and a complete local ring is Noetherian only once its maximal ideal is known to be finitely
generated (Tag 032B). Stating the conclusion as the single predicate `IsNagataRing R` rather than
as its N-2 clause alone keeps the tag's wording, and costs nothing, the Noetherian clause being
the hypothesis.

Faithfulness, point by point.
1. No hypothesis is dead: `IsLocalRing R` and `IsPrecomplete (maximalIdeal R) R` are both needed
   for the conclusion — there are Noetherian local domains that are not even N-1 (Nagata's
   examples), and a Noetherian non-local ring is not covered by any of the reductions — while
   `IsNoetherianRing R` is used by the reduction to the Cohen structure theorem as well as being
   the first clause of the conclusion.
2. The scalars and base are the source's: N-2 for `R ⧸ p` asserts finiteness of an integral
   closure as a module over `R ⧸ p` itself, not over `R` nor over a fraction field, and the
   completion is of `R` with respect to `R`'s own maximal ideal.
3. The filtration the source names is pinned rather than merely assumed to exist: completeness is
   with respect to the powers `(IsLocalRing.maximalIdeal R)ⁿ` of the maximal ideal of `R`, not
   with respect to an unspecified isomorphism `R ≅ lim_n R ⧸ mⁿ` or an arbitrary ideal.
4. The instantiation is not degenerate: `ℤ_[p]` satisfies the hypotheses by instance inference
   alone, and `k[[X]]` does after `PowerSeries.maximalIdeal_eq_span_X`; the completion
   `AdicCompletion m R` of a Noetherian local ring satisfies them once its Noetherianity (Tag
   05GH) is available, which is the application Tag 032X makes of this lemma. For all of these
   the conclusion is a statement about integral closures in infinitely many nontrivial finite
   extensions, and it is false for Noetherian local rings in general.

## References

* [Stacks Project, Tag 032W](https://stacks.math.columbia.edu/tag/032W)
* [Stacks Project, Tag 032R](https://stacks.math.columbia.edu/tag/032R)
* [Stacks Project, Tag 0325](https://stacks.math.columbia.edu/tag/0325)
* [Stacks Project, Tag 032P](https://stacks.math.columbia.edu/tag/032P)
-/

@[expose] public section



/-- **A Noetherian complete local ring is a Nagata ring.** If `R` is Noetherian, local, and
complete for the topology defined by its maximal ideal `m`, then `R` is a Nagata ring: for every
prime `p ⊆ R` the quotient domain `R ⧸ p` is N-2 (Japanese).

Completeness is asked for as `IsPrecomplete (IsLocalRing.maximalIdeal R) R`; the Hausdorff half
of `IsAdicComplete` is automatic for a Noetherian local ring, so a ring with
`IsAdicComplete (IsLocalRing.maximalIdeal R) R` satisfies the hypothesis by inference. -/
@[stacks 032W, ega "0 23.1.5" "more general"]
public theorem IsNagataRing.of_isPrecomplete_maximalIdeal {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsPrecomplete (IsLocalRing.maximalIdeal R) R] :
    IsNagataRing R := by apply Stacks.Nagata.CompleteLocalRing.solution

end

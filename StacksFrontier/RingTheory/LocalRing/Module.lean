module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# A finite locally free module over a semi-local ring with connected spectrum is free

Let `R` be a semi-local ring, that is, a ring with finitely many maximal ideals, and let `M` be a
finite locally free `R`-module, spelled as finitely presented and flat. This file proves that `M`
is free as soon as `Spec(R)` is preconnected, which is the second assertion of Stacks 02M9.

The source's argument has three steps: the fibre dimensions `dim_{R/𝔪} M/𝔪M` agree at all maximal
ideals `𝔪`; the Chinese remainder theorem lifts a common basis of the fibres to `d` elements of
`M`; and Nakayama makes those elements a basis. The last two steps are Mathlib's
`Module.free_of_flat_of_finrank_eq`, which takes the equality of the fibre dimensions as its
hypothesis, so the first step is the one proved here. It is
`Stacks.LocalRing.SemiLocalFreeness.finrank_quotient_tensor_eq_of_preconnectedSpace`: the rank of a
finitely presented flat module is a locally constant function of the point of `Spec(R)`
(`Module.isLocallyConstant_rankAtStalk`), a locally constant function on a preconnected space is
constant (`IsLocallyConstant.apply_eq_of_preconnectedSpace`), and at a maximal ideal that rank is
the fibre dimension there. If `R` has no maximal ideal at all, the hypothesis of
`Module.free_of_flat_of_finrank_eq` is vacuous and any value of `d` will do.

## Main results

* `Stacks.LocalRing.SemiLocalFreeness.solution`: the statement of Stacks 02M9,
  `Module.free_of_flat_of_preconnectedSpace`.

## Implementation notes

Mathlib spells the fibre of `M` at `𝔭` twice over, and the two spellings are not interchangeable by
`rfl`: `Module.rankAtStalk M 𝔭` is computed on `Ideal.Fiber`, the base change of `M` to the residue
field `κ(𝔭)` of `R_𝔭`, whereas `Module.free_of_flat_of_finrank_eq` asks for the dimension of `(R/𝔭)
⊗_R M` over `R/𝔭`, which is the source's `M/𝔭M`. At a *maximal* ideal the two agree, and that is
`Stacks.LocalRing.SemiLocalFreeness.finrank_quotient_tensor_eq_rankAtStalk`, proved by base change
along `R/𝔪 → κ(𝔪)` and cancellation of the intermediate tensor factor. Maximality enters there only
through `Field (R/𝔪)`, which is what makes the fibre free over `R/𝔪` and hence its dimension
invariant under that base change; it is a general fact about a finite flat module at a maximal
ideal, not a step of the source's argument.

## References

* [StacksProject 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

namespace Stacks.LocalRing.SemiLocalFreeness

open TensorProduct



section Fibre

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

/-- At a **maximal** ideal `𝔪` of `R` the rank of a finite flat module `M` at `𝔪` is the dimension
of the fibre `(R/𝔪) ⊗_R M` over the field `R/𝔪`. This is `Ideal.finrank_fiber_eq_rankAtStalk` in
the spelling used by `Module.free_of_flat_of_finrank_eq`: the fibre over the residue field `κ(𝔪)`
of `R_𝔪` is obtained from `(R/𝔪) ⊗_R M` by base change along `R/𝔪 → κ(𝔪)`, and `R/𝔪` being a
field, that base change does not change the dimension. -/
@[ega "III 7.9.1" "special case", ega "IV 21.10.11" "partial"]
private theorem finrank_quotient_tensor_eq_rankAtStalk [Module.Finite R M]
    (P : MaximalSpectrum R) :
    Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      Module.rankAtStalk M P.toPrimeSpectrum := by
  let _ : Field (R ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  rw [Module.rankAtStalk_eq, ← Module.finrank_baseChange (R := P.asIdeal.ResidueField)
    (S := R ⧸ P.asIdeal) (M' := (R ⧸ P.asIdeal) ⊗[R] M)]
  exact (AlgebraTensorModule.cancelBaseChange R (R ⧸ P.asIdeal) P.asIdeal.ResidueField
    P.asIdeal.ResidueField M).finrank_eq

/-- **The fibres of a finite locally free module over a ring with preconnected spectrum have a
common dimension.** This is the first step of the source's argument, and the only place
preconnectedness is used: the rank of `M` is a locally constant function on `Spec(R)`, hence
constant, and at a maximal ideal it is the dimension of the fibre `(R/𝔪) ⊗_R M`, the source's
`M/𝔪M`. -/
private theorem finrank_quotient_tensor_eq_of_preconnectedSpace [Module.FinitePresentation R M]
    [PreconnectedSpace (PrimeSpectrum R)] (P Q : MaximalSpectrum R) :
    Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      Module.finrank (R ⧸ Q.asIdeal) ((R ⧸ Q.asIdeal) ⊗[R] M) := by
  rw [finrank_quotient_tensor_eq_rankAtStalk, finrank_quotient_tensor_eq_rankAtStalk]
  exact Module.isLocallyConstant_rankAtStalk.apply_eq_of_preconnectedSpace _ _

end Fibre

/-- **A finite locally free module over a semi-local ring with connected spectrum is free.**
Let `R` be a semi-local ring whose spectrum is preconnected and let `M` be a finite locally free
`R`-module, spelled as finitely presented and flat. Then `M` is free: the fibres of `M` at the
maximal ideals of `R` all have the same dimension, and a finite locally free module whose fibres
have a common dimension over a semi-local ring is free. -/
public theorem solution (R : Type u) [CommRing R]
    [Finite (MaximalSpectrum R)] [PreconnectedSpace (PrimeSpectrum R)] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    Module.Free R M := by
  rcases isEmpty_or_nonempty (MaximalSpectrum R) with _ | hne
  · -- `R` has no maximal ideal, so there is no fibre and the common dimension may be `0`.
    exact Module.free_of_flat_of_finrank_eq R M 0 isEmptyElim
  · -- If there is one, the common dimension is that of the fibre at a maximal ideal `P`.
    exact hne.elim fun P ↦ Module.free_of_flat_of_finrank_eq R M _
      (finrank_quotient_tensor_eq_of_preconnectedSpace · P)

end Stacks.LocalRing.SemiLocalFreeness

/-!
# Finite locally free modules over a semilocal ring with connected spectrum

Let `R` be a semi-local ring, that is, a ring with finitely many maximal ideals, and let `M` be a
finite locally free `R`-module: finitely presented and flat, equivalently finite projective, by
Lemma 00NX. The rank of `M` at a point `𝔭` of `Spec(R)` is `rank_{R_𝔭} M_𝔭`, and it is a locally
constant function of `𝔭`. If that function is constant, then `M` is free: this is the main
assertion of the source, and it is Mathlib's `Module.free_of_flat_of_finrank_eq`.

On a preconnected space a locally constant function is constant, so the rank of `M` is
automatically constant as soon as `Spec(R)` is preconnected. Hence a finite locally free module
over a semi-local ring with connected spectrum is free, with no hypothesis on its rank; that is
the statement recorded here, the "in particular" of the source.

Semi-locality is essential, and is what makes the conclusion global rather than local: over the
Dedekind domain `ℤ[√-5]`, whose spectrum is connected because the ring is a domain, a non-principal
ideal such as `(2, 1 + √-5)` is finite locally free of rank `1` and is not free.

## Main results

* `Module.free_of_flat_of_preconnectedSpace`: a finitely presented flat module over a semi-local
  ring whose spectrum is preconnected is free.

## Implementation notes

The source is two sentences, and only the second is stated here. The first, "constant rank implies
free", is Mathlib's `Module.free_of_flat_of_finrank_eq`, with the basis-producing refinement
`Module.nonempty_basis_of_flat_of_finrank_eq`; both already carry `@[stacks 02M9]`, and restating
either would duplicate a Mathlib lemma. Mathlib's form is in fact more general than the source's
in two ways: it asks only `Module.Finite` and `Module.Flat` in place of finite local freeness, and
it asks for equality of the fibre dimensions `dim_{κ(𝔪)} M ⊗_R κ(𝔪)` at the *maximal* ideals only,
rather than constancy of the rank on all of `Spec(R)`. The two readings of the rank at a maximal
ideal `𝔪` agree: `Module.rankAtStalk M 𝔪 = dim_{κ(𝔪)} M ⊗_R κ(𝔪)` by `Module.rankAtStalk_eq`, and
`κ(𝔪)` is `R ⧸ 𝔪` itself, `R ⧸ 𝔪` being a field and `κ(𝔪)` its fraction field.

Semi-locality is spelled `Finite (MaximalSpectrum R)`, as in Mathlib's `free_of_flat_of_finrank_eq`
and in `Module.Finite.of_localized_maximal`.

Connectedness of `Spec(R)` is weakened to `PreconnectedSpace (PrimeSpectrum R)`, dropping
non-emptiness: this is the hypothesis under which a locally constant function is constant
(`IsLocallyConstant.apply_eq_of_preconnectedSpace`), and the extra case it admits, `Spec(R) = ∅`,
is `R` the zero ring, where `M` is zero and free. So the statement is never weaker than the
source's.

Finite local freeness is spelled `Module.FinitePresentation` together with `Module.Flat`, one of
the equivalent forms of Lemma 00NX, and the one in which Mathlib states local constancy of the
rank (`Module.isLocallyConstant_rankAtStalk`). It is not weakened to `Module.Finite` with
`Module.Flat`, the hypotheses of `Module.free_of_flat_of_finrank_eq`, because it is through local
constancy that connectedness acts, and over a ring that is not coherent a finite flat module need
not be locally free (Remark 00NY).

Faithfulness. (1) Every hypothesis is used. Semi-locality: `ℤ[√-5]` has connected spectrum and the
finite locally free module `(2, 1 + √-5)` is not free. Preconnectedness: over `R = k × k`, which
has two maximal ideals, the summand `M = k × 0` is finite locally free with rank `1` at one point
of the two-point discrete space `Spec(R)` and rank `0` at the other, and is not free. Flatness:
over the local, hence semi-local, ring `k[x] ⧸ (x²)`, whose spectrum is a point and so connected,
the finite module `k[x] ⧸ (x)` is not free. Finite presentation enters through local constancy of
the rank, and carries `Module.Finite R M`, which the constant-rank theorem needs. (2) The scalars
and the base are the source's: freeness is over `R`, the rank at `𝔭` is taken over `R_𝔭` and the
space is `Spec(R)` with its Zariski topology; no localization of `R` other than at its own primes
occurs. (3) The source names no canonical map, and none is needed: the conclusion `Module.Free R M`
is the existence of an `R`-basis of `M`. The one function in play, the rank, is Mathlib's
`Module.rankAtStalk M`, and it does not appear in the statement because connectedness makes any
hypothesis on it superfluous. (4) The instantiation is not degenerate: let `R` be the localization
of `ℤ[√-5]` at the multiplicative set of elements lying outside both `𝔭 = (2, 1 + √-5)` and
`𝔮 = (3, 1 + √-5)`. Then `R` is a semi-local domain with exactly the two maximal ideals `𝔭R`
and `𝔮R`, it is not
local, and `Spec(R)` is connected, so the theorem applies and says that `𝔭R` is free of rank `1`,
which `𝔭` is not over `ℤ[√-5]`.

## References

* [StacksProject 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

@[expose] public section



/-- **A finite locally free module over a semi-local ring with connected spectrum is free.**
Let `R` be a semi-local ring, so with finitely many maximal ideals, whose spectrum is
(pre)connected, and let `M` be a finite locally free `R`-module, spelled here as finitely
presented and flat. Then `M` is free. The rank of `M` is a locally constant function on
`Spec(R)`, hence constant, and a finite locally free module of constant rank over a semi-local
ring is free (`Module.free_of_flat_of_finrank_eq`). -/
@[stacks 02M9 "The second assertion; the first, for a module of constant rank, is Mathlib's \
`Module.free_of_flat_of_finrank_eq`.",
  ega "IV 11.3.12" "more general",
  ega "IV 15.2.4" "Freeness clause"]
public theorem Module.free_of_flat_of_preconnectedSpace (R : Type u) [CommRing R]
    [Finite (MaximalSpectrum R)] [PreconnectedSpace (PrimeSpectrum R)] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    Module.Free R M := by apply Stacks.LocalRing.SemiLocalFreeness.solution

end

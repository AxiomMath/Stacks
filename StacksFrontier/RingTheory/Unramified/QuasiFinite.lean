module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Topology.Sheaves.Init

public import StacksFrontier.RingTheory.QuasiFinite.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# An unramified ring map is quasi-finite

Let `R → S` be of finite type and let `𝔮` be a prime of `S`, lying over `𝔭 ⊆ R`. If `R → S` is
unramified at `𝔮` then it is quasi-finite at `𝔮`: the point `𝔮` is isolated in the fibre
`F = Spec (κ(𝔭) ⊗_R S)` of `Spec S → Spec R` through it. This is Stacks 02UR.

The proof is the source's, in two steps. Unramifiedness at `𝔮` says that `S_𝔮` is formally
unramified over `R`, and `S_𝔮` is essentially of finite type over `R` because `S` is of finite
type; by Stacks 00UW this forces `𝔭S_𝔮 = 𝔮S_𝔮` with `κ(𝔮)/κ(𝔭)` finite separable, so that the
local ring `S_𝔮/𝔭S_𝔮 = κ(𝔭) ⊗_R S_𝔮` of `F` at `𝔮` is the finite extension `κ(𝔮)` of `κ(𝔭)`.
That finiteness is condition (2) of Lemma 00PK, whose condition (1) is the isolated point.

## Main results

* `Stacks.Unramified.QuasiFinite.solution`: the statement of Stacks 02UR.

## Implementation notes

The first step is `finite_fiber_localization_of_isUnramifiedAt` below, stated for *every* prime
`𝔭` of `R` and with `S` only essentially of finite type, which is all it needs: a formally
unramified, essentially finite type algebra is quasi-finite, and quasi-finiteness *is* the
finiteness of every fibre. The source uses it at the single prime that `𝔮` lies over. So the
route through `𝔭S_𝔮 = 𝔮S_𝔮` and `κ(𝔮)` is not taken here; the conclusion of Stacks 00UW that
the source needs is reached directly. The second step is Lemma 00PK,
`Algebra.isOpen_singleton_fiber_tfae_of_finiteType`, at `(2) → (1)`, and it is that lemma, not
the first step, that wants `S` of finite type rather than essentially of finite type.

Lemma 00PK is stated for a prime `𝔭` of `R` together with `[𝔮.LiesOver 𝔭]` and a `κ(𝔭)`-algebra
structure on `S_𝔮`; here `𝔭` is `Ideal.under R 𝔮`, over which `𝔮` lies by definition, and the
structure is the canonical `Localization.AtPrime.algebraOfLiesOver`. Neither the condition
assumed nor the condition concluded mentions that structure, so no compatibility beyond its
existence is used.

## References

* [StacksProject 02UR](https://stacks.math.columbia.edu/tag/02UR)
-/

@[expose] public section

namespace Stacks.Unramified.QuasiFinite

/-- The conclusion of **Stacks 00UW** that the proof of Stacks 02UR uses: if `S` is essentially
of finite type over `R` and unramified at a prime `𝔮`, then the fibre `S_𝔮/𝔭S_𝔮 = κ(𝔭) ⊗_R S_𝔮`
of `S_𝔮` over any prime `𝔭` of `R` is finite over `κ(𝔭)`.

Stacks 00UW gets this for the prime `𝔮` lies over by way of `𝔭S_𝔮 = 𝔮S_𝔮`, which identifies the
fibre with `κ(𝔮)`; here it is the definition of quasi-finiteness of `S_𝔮` over `R`, which a
formally unramified, essentially finite type algebra has. -/
private lemma finite_fiber_localization_of_isUnramifiedAt {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] (𝔭 : Ideal R) [𝔭.IsPrime] (𝔮 : Ideal S)
    [𝔮.IsPrime] [Algebra.IsUnramifiedAt R 𝔮] :
    Module.Finite 𝔭.ResidueField (𝔭.Fiber (Localization.AtPrime 𝔮)) :=
  Algebra.QuasiFinite.finite_fiber 𝔭

public theorem solution {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    [Algebra.IsUnramifiedAt R q.asIdeal] :
    IsOpen (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)})
      {⟨q, rfl⟩} := by
  -- The canonical `κ(𝔭)`-algebra structure on `S_q`, for `𝔭` the prime `q` lies over.
  let _ := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  -- Stacks 00PK, (2) → (1): finiteness of the fibre is the isolated point of the fibre.
  exact ((Algebra.isOpen_singleton_fiber_tfae_of_finiteType _ q.asIdeal).out 2 1).mp
    (finite_fiber_localization_of_isUnramifiedAt _ q.asIdeal)

end Stacks.Unramified.QuasiFinite

end

/-!
# An unramified ring map is quasi-finite

Let `R → S` be a ring map of finite type and let `q` be a prime of `S` lying over `p ⊆ R`. If
`R → S` is unramified at `q` — the localization `S_q` is formally unramified over `R`,
equivalently `R → S_g` is unramified for some `g ∈ S`, `g ∉ q` — then `R → S` is quasi-finite at
`q`: writing `F = Spec (κ(p) ⊗_R S)` for the fibre of `Spec S → Spec R` containing `q`, the point
of `F` corresponding to `q` is isolated. Taking this at every prime of `S` gives the second
sentence of the source: an unramified ring map is quasi-finite.

The source argues through the characterization of isolated points in fibres of Lemma 00PK, part
(2), that `S_q/pS_q` is finite over `κ(p)`, which unramifiedness at `q` supplies by Lemma 00UW:
that lemma gives `pS_q = qS_q` with `κ(q)/κ(p)` finite separable, so `S_q/pS_q = κ(q)`. In
Mathlib the finiteness of every fibre of a formally unramified algebra essentially of finite type
is an instance, and the passage from that finiteness back to the isolated point of the fibre is
`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`; the statement below is their composite, which
is the source's Definition 00PL at `q`.

## Main results

* `Algebra.isOpen_singleton_fiber_of_isUnramifiedAt`: Stacks 02UR, unramified at `q` implies
  quasi-finite at `q`.

## Implementation notes

*The conclusion is the source's definition, not Mathlib's proxy for it.* "`R → S` is quasi-finite
at `q`" is Definition 00PL, the equivalent conditions of Lemma 00PK, of which (1) is that `q` is
an isolated point of its fibre; that is the conclusion below, in the spelling Mathlib uses for it
in `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`. The other member of that equivalence,
finiteness of `S_q/pS_q` over `κ(p)` — Lemma 00PK (2), Mathlib's `Algebra.QuasiFiniteAt R q` —
already follows from unramifiedness by instance resolution alone, through
`Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified`, and does so under
hypotheses weaker than the source's: only `Algebra.EssFiniteType R S_q` is needed, and the
finiteness is obtained over every prime of `R` rather than over the one `q` lies over. So the
content of this tag that is not already a Mathlib declaration is the isolated point, and that is
what is stated.

*Unramifiedness at `q` is the sole local hypothesis, and finite type is the source's.*
`Algebra.IsUnramifiedAt R q` is Definition 00UT (3), the two directions being
`Algebra.exists_unramified_of_isUnramifiedAt` and `Algebra.basicOpen_subset_unramifiedLocus_iff`;
it is the spelling used by the companion statement for tag 00QF. It cannot be dropped:
`Polynomial.not_quasiFiniteAt` denies the fibre-finiteness, hence the conclusion, at every prime
of `R[X]`, an algebra of finite type. `Algebra.FiniteType R S` is the source's hypothesis and is
the one Lemma 00PK carries, so it is what the identification of the isolated point with
fibre-finiteness needs; unlike the fibre-finiteness alone, the topological conclusion is not
available from the weaker essential finiteness of `S_q`.

*The name mutates its Mathlib sibling's.* Mathlib calls this conclusion `isOpen_singleton_fiber`,
in `Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber` and in the `iff`; swapping the hypothesis
that is assumed for the one assumed here names this lemma.

*The second sentence needs no declaration of its own.* For `[Algebra.Unramified R S]` the
statement `Algebra.QuasiFinite R S` is closed by `inferInstance`: `Algebra.Unramified.finiteType`
and `Algebra.EssFiniteType.of_finiteType` give essential finite type,
`Algebra.Unramified.formallyUnramified` the formal condition, and the instance named above
concludes.

## References

* [Stacks 02UR](https://stacks.math.columbia.edu/tag/02UR), Lemma 10.151.6, in Section 10.151
  "Unramified ring maps" (Section 00US).
* [Stacks 00PK](https://stacks.math.columbia.edu/tag/00PK) and
  [Stacks 00UW](https://stacks.math.columbia.edu/tag/00UW), the two lemmas the source's proof
  uses; [Stacks 00PL](https://stacks.math.columbia.edu/tag/00PL) and
  [Stacks 00UT](https://stacks.math.columbia.edu/tag/00UT), the definitions of quasi-finite at a
  prime and of unramified at a prime.
-/

@[expose] public section

/-- **Stacks 02UR.** Let `S` be an `R`-algebra of finite type and let `q` be a prime of `S`. If
`R → S` is unramified at `q` then it is quasi-finite at `q`: the point `q` is isolated in the
fibre of `Spec S → Spec R` through it. In particular an unramified ring map is quasi-finite: for
`[Algebra.Unramified R S]`, `Algebra.QuasiFinite R S` is found by instance resolution. -/
@[stacks 02UR "Unramified at `q` is `Algebra.IsUnramifiedAt R q` (Definition 00UT (3), via
`Algebra.exists_unramified_of_isUnramifiedAt`). Quasi-finite at `q` is Definition 00PL, the
equivalent conditions of Lemma 00PK, and the conclusion is condition (1), `q` isolated in its
fibre; condition (2), `Algebra.QuasiFiniteAt R q`, is instead Mathlib's instance
`Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified`, which holds under
weaker hypotheses than the source's. The second sentence needs no declaration:
`Algebra.QuasiFinite R S` for `[Algebra.Unramified R S]` is `inferInstance`. See the module
docstring.", ega "IV 17.4.3" "affine case", ega "IV 17.4.1.2" "quasi-finite (ring case)"]
public theorem Algebra.isOpen_singleton_fiber_of_isUnramifiedAt {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    [Algebra.IsUnramifiedAt R q.asIdeal] :
    IsOpen (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)}) {⟨q, rfl⟩} :=
      by apply Stacks.Unramified.QuasiFinite.solution

end

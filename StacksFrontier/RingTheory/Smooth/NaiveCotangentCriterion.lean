module

public import Mathlib.RingTheory.Smooth.Locus
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
public import Mathlib.RingTheory.Radical.NatInt
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

/-!
# Smoothness at a prime, in terms of the naive cotangent complex

Let `R → S` be of finite presentation, let `q` be a prime of `S` and let `Sq` be a model of the
localization `S_q`. This file proves Stacks 07BU: smoothness of `R → S` at `q` — the existence of
`g ∉ q` with `R → S_g` smooth — is equivalent to the vanishing of `H_1(L_{S/R})_q` together with
`Ω_{S/R, q}` being a finite free `S_q`-module, and freeness may be weakened to projectivity or to
flatness without changing the class of primes so described.

Three of the equivalences are local algebra over the local ring `S_q`, and none of them mentions
`H_1`: for a *finite* module over a local ring, freeness, projectivity and flatness are one
condition (`tfae_free_projective_flat`). The hypothesis is met because `Ω_{S/R}` is a finitely
presented `S`-module, so `Ω_{Sq⁄R}`, being its localization at `q`, is finite over `S_q`. This is
where the finite presentation of `R → S` and the primality of `q` are used, and it is why the
finiteness conjunct of (2) is a consequence rather than an extra hypothesis.

The remaining content is the equivalence of the cotangent-complex conditions with smoothness at
`q`. Projectivity of `Ω` together with the vanishing of `H_1` is formal smoothness of `Sq` over `R`
(`Algebra.formallySmooth_iff`), and formal smoothness does not depend on the model chosen for
`S_q` (`formallySmooth_iff_isSmoothAt`), so items (2)–(4) are conditions on the point `q` and not
on `Sq`. That smoothness at `q` in this sense is smoothness of `R → S_g` for some `g ∉ q` is the
openness of the smooth locus, in the two halves `Algebra.IsSmoothAt.exists_notMem_smooth` and
`isSmoothAt_of_smooth_away`.

## Main results

* `Stacks.Smooth.NaiveCotangentCriterion.solution`: the five conditions of Stacks 07BU are
  equivalent.

## Implementation notes

The source spreads the vanishing of `H_1` from `q` to a basic open by hand: it writes `S_q` as a
colimit of principal localizations to make `(Ω_{S/R})_g` finite free (Lemma 05N7), chooses a
presentation `α : R[x_1, …, x_n] → S` with kernel `I` and works with `NL(α)` (Lemma 00S1), splits
the surjection `Ω_{R[x]/R} ⊗ S_g → (Ω_{S/R})_g` using projectivity, and concludes that
`H_1(L_{S/R})_g` is a quotient of `(I/I²)_g`, hence a finite `S_g`-module, whose vanishing at `q`
therefore propagates to a smaller basic open. That whole argument is the proof that the smooth
locus is open, and it is available in Mathlib as
`Algebra.basicOpen_subset_smoothLocus_iff_smooth`, so the step is a reference here rather than a
proof. Lemma 00S7, that the naive cotangent complex commutes with localization, enters the same
way, through the instance `KaehlerDifferential.isLocalizedModule_map`, which is what identifies
`Ω_{Sq⁄R}` with `(Ω_{S/R})_q` and so makes it finite.

Item (1) is read on `Localization.Away g` and item (5) is Mathlib's `Algebra.IsSmoothAt R q`,
which is formal smoothness of `Localization.AtPrime q` over `R`; the model `Sq` of items (2)–(4)
is an arbitrary `IsLocalization.AtPrime Sq q`, which is why the passage between the two readings
is isolated as `formallySmooth_iff_isSmoothAt`.

## References

* [StacksProject 07BU](https://stacks.math.columbia.edu/tag/07BU)
-/

namespace Stacks.Smooth.NaiveCotangentCriterion

/-- Over a local ring, a finite module is free as soon as it is flat, so for such a module
freeness, projectivity and flatness are the same condition. -/
@[ega "0 10.1.3" "partial", sga "1 IV 4.3" "(b)", sga "3 VIIA 7.4.3" "partial"]
private theorem tfae_free_projective_flat (A : Type*) [CommRing A] [IsLocalRing A] (M : Type*)
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    List.TFAE [Module.Free A M, Module.Projective A M, Module.Flat A M] := by
  tfae_have 1 → 2 := fun h ↦ have := h; .of_free
  tfae_have 2 → 3 := fun h ↦ have := h; Module.Flat.of_projective
  tfae_have 3 → 1 := fun h ↦ have := h; Module.free_of_flat_of_isLocalRing
  tfae_finish

/-- Formal smoothness over `R` of a localization of `S` at a prime `q` does not depend on the
model chosen for it: for any `Sq` it is `Algebra.IsSmoothAt R q`. -/
private theorem formallySmooth_iff_isSmoothAt {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq] :
    Algebra.FormallySmooth R Sq ↔ Algebra.IsSmoothAt R q :=
  Algebra.FormallySmooth.iff_of_equiv
    ((IsLocalization.algEquiv q.primeCompl Sq (Localization.AtPrime q)).restrictScalars R)

/-- Smoothness of `R → S_g` for a single `g ∉ q` already gives smoothness at `q`: the basic open
`D(g)` is contained in the smooth locus, and `q` lies in `D(g)`. This is the converse of
`Algebra.IsSmoothAt.exists_notMem_smooth`. -/
public theorem isSmoothAt_of_smooth_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] {g : S} (hg : g ∉ q)
    (hsm : Algebra.Smooth R (Localization.Away g)) : Algebra.IsSmoothAt R q :=
  Set.mem_of_subset_of_mem (a := ⟨q, ‹q.IsPrime›⟩)
    (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm) (by simpa using hg)

/-- The five-term equivalence of Stacks 07BU: for `R → S` of finite presentation, a prime `q`
of `S` and a model `Sq` of `S_q`, smoothness at `q` (as `R → S_g` smooth for some `g ∉ q`, and
as `Algebra.IsSmoothAt R q`) is equivalent to `H_1(L_{S/R})_q = 0` together with `Ω[Sq⁄R]`
being finite free, or projective, or flat over `Sq`. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq] :
    List.TFAE
      [∃ g ∉ q, Algebra.Smooth R (Localization.Away g),
       Subsingleton (Algebra.H1Cotangent R Sq) ∧
         Module.Finite Sq Ω[Sq⁄R] ∧ Module.Free Sq Ω[Sq⁄R],
       Subsingleton (Algebra.H1Cotangent R Sq) ∧ Module.Projective Sq Ω[Sq⁄R],
       Subsingleton (Algebra.H1Cotangent R Sq) ∧ Module.Flat Sq Ω[Sq⁄R],
       Algebra.IsSmoothAt R q] := by
  have : IsLocalRing Sq := IsLocalization.AtPrime.isLocalRing Sq q
  -- `Ω_{Sq⁄R}` is finite over `S_q`, being the localization of the finitely presented module
  -- `Ω_{S⁄R}`: this is the hypothesis of `tfae_free_projective_flat`, and the reason the
  -- finiteness conjunct of (2) is free.
  have hfin : Module.Finite Sq Ω[Sq⁄R] :=
    Module.Finite.of_isLocalizedModule q.primeCompl (KaehlerDifferential.map R R S Sq)
  have h := tfae_free_projective_flat Sq Ω[Sq⁄R]
  tfae_have 1 → 5 := fun ⟨_, hg, hsm⟩ ↦ isSmoothAt_of_smooth_away q hg hsm
  tfae_have 5 → 1 := fun _ ↦ Algebra.IsSmoothAt.exists_notMem_smooth R q
  tfae_have 3 ↔ 5 := (and_comm.trans (Algebra.formallySmooth_iff R Sq).symm).trans
    (formallySmooth_iff_isSmoothAt q Sq)
  tfae_have 2 ↔ 3 := and_congr_right' ((and_iff_right hfin).trans (h.out 1 2))
  tfae_have 3 ↔ 4 := and_congr_right' (h.out 2 3)
  tfae_finish

end Stacks.Smooth.NaiveCotangentCriterion

/-!
# Smoothness at a prime, in terms of the naive cotangent complex

Let `R → S` be a ring map of finite presentation and let `q` be a prime of `S`. Smoothness of
`R → S` at `q` — the existence of `g ∉ q` with `R → S_g` smooth (Definition 00TB) — is detected
by the naive cotangent complex at `q`: it holds if and only if `H_1(L_{S/R})_q = 0` and the
localized module of differentials `Ω_{S/R, q}` is a finite free `S_q`-module, and the freeness
may be weakened to projectivity or even to flatness without changing the class of primes so
described. So the smooth locus of a finitely presented algebra is cut out by the vanishing of
`H_1` together with local freeness of `Ω`, one prime at a time.

The source's proof. Formation of the naive cotangent complex commutes with localization
(Lemma 00S7), and `Ω_{S/R}` is a finitely presented `S`-module (Lemma 00RY); over the local ring
`S_q` a finitely presented flat module is finite free, so conditions (2), (3), (4) are equivalent
(Lemma 00NX). That (1) implies them is immediate from the definition of smoothness. Conversely,
assume (2). Writing `S_q` as a colimit of principal localizations, `(Ω_{S/R})_g` is already finite
free for some `g ∉ q` (Lemma 05N7). Choose a presentation `α : R[x_1, …, x_n] → S` with kernel
`I`, so `NL(α)` computes the complex (Lemma 00S1). Projectivity of `(Ω_{S/R})_g` splits the
surjection `Ω_{R[x]/R} ⊗ S_g → (Ω_{S/R})_g`, hence the image of
`d : (I/I²)_g → Ω_{R[x]/R} ⊗ S_g` is a direct summand and `H_1(L_{S/R})_g` is a quotient of
`(I/I²)_g`, in particular a finite `S_g`-module. A finite module vanishing at `q` vanishes on a
smaller basic open, so `H_1(L_{S/R})_{gg'} = 0` for some `g' ∉ q`, and `R → S_{gg'}` is smooth by
definition.

## Main results

* `Algebra.isSmoothAt_tfae_h1Cotangent_and_kaehlerDifferential`: Lemma 07BU, as a five-term
  `List.TFAE`.

## Implementation notes

The localizations `H_1(L_{S/R})_q` and `Ω_{S/R, q}` are spelled as the invariants of the localized
algebra, `Algebra.H1Cotangent R Sq` and `Ω[Sq⁄R]` for a model `Sq` of `S_q`. This is the source's
own Lemma 00S7 ("the naive cotangent complex commutes with localization") and is not a weakening:
Mathlib carries it as the instances `Algebra.H1Cotangent.isLocalizedModule` and
`KaehlerDifferential.isLocalizedModule_map`, which exhibit `Algebra.H1Cotangent.map R R S Sq` and
`KaehlerDifferential.map R R S Sq` as localizations at `q.primeCompl`, so the two readings of each
condition are interchangeable by `IsLocalizedModule.iso`. The model `Sq` is an arbitrary
`IsLocalization.AtPrime Sq q`, not `Localization.AtPrime q`, and it is an `R`-algebra over `S`
(`IsScalarTower R S Sq`), which is what makes `Ω[Sq⁄R]` the differentials of `S_q` over the base
`R` of the source rather than over some unrelated one.

`H_1(L_{S/R})_q = 0` is `Subsingleton`, Mathlib's spelling of the vanishing of a module, as in
`Algebra.formallySmooth_iff`. "Finite free" is the conjunction `Module.Finite` and `Module.Free`;
finiteness is in fact automatic here, since `Ω[Sq⁄R]` is the localization of the finitely
presented module `Ω[S⁄R]` (Lemma 00RY), and it is kept because it is what the source asserts.

Item (1) is the source's Definition 00TB verbatim, the existence of `g ∉ q` with `R → S_g` smooth,
with `S_g` the model `Localization.Away g`, as in `Algebra.IsSmoothAt.exists_notMem_smooth`. It is
stated a second time as Mathlib's `Algebra.IsSmoothAt R q`, that is formal smoothness of `S_q`
over `R`, which is the spelling the rest of the smoothness API uses; that is item (5), so that
items (1)–(4) carry the source's numbering.

Faithfulness to [StacksProject 07BU]. (1) No hypothesis is idle: `Algebra.FinitePresentation R S`
is used in both directions — through `Algebra.Smooth` in item (1), and through the finite
presentation of `Ω[S⁄R]`, which is what makes flatness at `q` give finite freeness and what makes
the vanishing of `H_1` at `q` spread to a basic open; `q.IsPrime` is needed for `Sq` to be a local
ring, without which (2), (3), (4) are inequivalent. (2) The scalars and the base are the source's:
the base is `R` throughout, and `Ω[Sq⁄R]` is asked to be free, projective or flat over `S_q` — not
over `S` and not over `R`. (3) The canonical maps are pinned: `Sq` is pinned as a localization of
`S` at `q` compatibly with `R`, and the localizations of `H_1` and `Ω` are pinned by the
`IsLocalizedModule` instances on `Algebra.H1Cotangent.map R R S Sq` and
`KaehlerDifferential.map R R S Sq` rather than left as an unspecified isomorphism. (4) The
instantiation is not degenerate: for `R = ℚ`, `S = ℚ[x]` and `q = (x)` all five conditions hold,
with `Ω[Sq⁄R]` free of rank one; for `S = ℚ[x, y]/(y² - x³)` and `q = (x, y)`, the cusp, all five
fail, so the equivalence is not a statement about an empty or an always-true class of primes.

## References

* [StacksProject 07BU](https://stacks.math.columbia.edu/tag/07BU)
  (`algebra-lemma-smooth-at-point`), in the section "Smooth ring maps". Smoothness at a prime is
  Definition 00TB.
-/

@[expose] public section

/-- **Smoothness at a prime is the vanishing of `H_1` together with freeness of `Ω`**
(Stacks 07BU). Let `R → S` be of finite presentation, let `q` be a prime of `S` and let `Sq` be a
model of `S_q`. The following are equivalent: (1) `R → S` is smooth at `q`, that is `R → S_g` is
smooth for some `g ∉ q`; (2) `H_1(L_{S/R})_q = 0` and `Ω_{S/R, q}` is a finite free
`S_q`-module; (3) `H_1(L_{S/R})_q = 0` and `Ω_{S/R, q}` is projective; (4) `H_1(L_{S/R})_q = 0`
and `Ω_{S/R, q}` is flat; (5) `S_q` is formally smooth over `R`. -/
@[stacks 07BU "The localizations `H_1(L_{S/R})_q` and `Ω_{S/R, q}` are read on an arbitrary model
`Sq` of `S_q` as `Algebra.H1Cotangent R Sq` and `Ω[Sq⁄R]`, which is Lemma 00S7 and is witnessed by
the instances `Algebra.H1Cotangent.isLocalizedModule` and
`KaehlerDifferential.isLocalizedModule_map`; vanishing is `Subsingleton` and `finite free` is
`Module.Finite` and `Module.Free`. Item (1) is Definition 00TB verbatim, and Mathlib's
`Algebra.IsSmoothAt` is added as item (5). See the module docstring.",
  ega "0 22.6.4" "special case"]
public theorem Algebra.isSmoothAt_tfae_h1Cotangent_and_kaehlerDifferential
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq] [Algebra S Sq]
    [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq] :
    List.TFAE
      [∃ g ∉ q, Algebra.Smooth R (Localization.Away g),
       Subsingleton (Algebra.H1Cotangent R Sq) ∧
         Module.Finite Sq Ω[Sq⁄R] ∧ Module.Free Sq Ω[Sq⁄R],
       Subsingleton (Algebra.H1Cotangent R Sq) ∧ Module.Projective Sq Ω[Sq⁄R],
       Subsingleton (Algebra.H1Cotangent R Sq) ∧ Module.Flat Sq Ω[Sq⁄R],
       Algebra.IsSmoothAt R q] :=
         by apply Stacks.Smooth.NaiveCotangentCriterion.solution

end

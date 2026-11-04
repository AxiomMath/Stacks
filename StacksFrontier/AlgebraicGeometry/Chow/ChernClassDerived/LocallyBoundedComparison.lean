module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexDerivedCohomology
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BoundedComplex
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod

/-!
# The locally bounded independence of the representative, with the splittings discharged

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. **Stacks 0ESZ** says that the classes

  `c(ℰ^•) ∈ ∏_{p ≥ 0} A^p(X)`,  `ch(ℰ^•) ∈ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`,  `P_p(ℰ^•) ∈ A^p(X)`

of a locally bounded complex of finite locally free `𝒪_X`-modules depend only on the object of
`D(𝒪_X)` it represents.

`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexIndependence` delivers that at the locally
bounded generality of the source, for all three classes, from the hypothesis
`Stacks.Chow.HasCohomologyComparisonAtCommonWindow`: a window outside which both complexes
vanish, a `Stacks.Chow.BoundedComplexSplitting` of each there, and a
`Stacks.Chow.ComplexCohomologyComparison` between them. This file produces that hypothesis, and
with it the three conclusions, from

* an isomorphism of the two complexes in `D(𝒪_X)` — which is what "representing the same object"
  means, and is the source's hypothesis; and
* the conclusion of **Stacks 0ESR** read on each complex: every cohomology sheaf is a perfect
  `𝒪_X`-module of tor amplitude in `[-1, 0]`.

Nothing else. No comparison datum, no splitting and no window is carried.

## Main results

* `Stacks.Chow.nonempty_boundedComplexSplitting_of_isZero_outside` — a splitting at a window
  presented as vanishing data rather than as two `HomologicalComplex.IsStrictly*` instances.
* `Stacks.Chow.hasCohomologyComparisonAtCommonWindow_of_derivedIso_of_isLocallyBounded` — **the
  bridge**: the hypothesis of the locally bounded independence statements, on `X` itself.
* `Stacks.Chow.totalChernClassComplexLocallyBounded_eq_of_derivedIso`,
  `Stacks.Chow.powerSumClassComplexLocallyBounded_eq_of_derivedIso`,
  `Stacks.Chow.chernCharacterLocallyBounded_eq_of_derivedIso` — Stacks 0ESZ at the locally
  bounded generality for all three classes, with the comparison datum discharged.

## Implementation notes

### The fixed window is not an obstruction

`Stacks.FiniteLocallyFree.boundedComplexSplitting` takes the window through the two instances
`[P.IsStrictlyGE a]` and `[P.IsStrictlyLE (a + k)]`, while
`Stacks.Chow.HasCohomologyComparisonAtCommonWindow` quantifies the window existentially and
`Stacks.Chow.exists_common_window_of_isLocallyBoundedFiniteLocallyFree` produces it as vanishing
data. That mismatch looks like it separates the two, and it does not: both classes are
propositions with `CochainComplex.isStrictlyGE_iff` and `CochainComplex.isStrictlyLE_iff` as
their characterisations, so the window obtained from the existential supplies both instances by
`haveI`, and the splitting is then built at exactly that window.
`Stacks.Chow.nonempty_boundedComplexSplitting_of_isZero_outside` is that step, isolated so that
nothing downstream has to hold a window as an instance.

So the difference between the two readings of Stacks 0ESZ in this repository is not where the
window lives.

### What is carried, and why it is not the source's hypothesis

The perfectness and the tor amplitude of the cohomology sheaves, **on `X` itself**. The source
does not assume them there: its proof reduces by Stacks 02UC to an integral test scheme, replaces
that scheme by one proper and birational over it, and only on the modification arranges that each
`H^i(Lg^*E)` is perfect of tor dimension at most one. Stacks 0ESR is what does the arranging, and
in this repository it is available only on an admissible blowup, as
`AlgebraicGeometry.exists_admissibleBlowup_isHomologyPerfectTorLEOne`.

The hypothesis is therefore genuinely stronger than the source's, and it is not vacuous: it fails
for complexes Stacks 0ESZ is about. On `X = Spec 𝐤[x, y]` the complex `𝒪_X^2 ⟶ 𝒪_X` with matrix
`(x, y)` is a bounded complex of finite locally free modules, so it is one of the tag's
representatives, and its cohomology in the top degree is the residue field at the origin, whose
tor amplitude is `[-2, 0]` and not `[-1, 0]`. A complex of finite locally free modules has no
reason to have cohomology of tor dimension at most one, which is exactly why the source passes to
a modification first.

### Why the splitting cannot instead be imported from the blowup

The tor bound *is* available after a blowup, by restricted Stacks 0ESR. What a splitting there
proves, though, is an equality of classes in `A^p(Y')` for the blowup `Y' ⟶ X`, and carrying it
back to `A^p(X)` needs the restriction map of Stacks 0B7F — which is the route
`Stacks.Chow.powerSumClassComplex_eq_of_hasPowerSumComparisonOnModifications` already takes, and
which is confined to the power sums and the Chern character because restricting an alternating
*product* needs the restriction map to be multiplicative, Stacks 0FE0 hence Stacks 0B6Y. So the
blowup-side tor bound is usable only through a restriction, and the restriction is where the
total Chern class is lost.

The two obstructions are therefore disjoint, and discharging either one alone delivers the total
class: either Stacks 0FE0, which opens the Stacks 02UC route to it, or the tor bound on `X`,
which is what this file asks for.

### The total Chern class reading survives

It does, and the three statements below include it. The proof reads one and the same class at a
different window of degrees and never restricts it along a morphism, so the multiplicativity of
the restriction map does not arise; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexIndependence`.

### The two finite-local-freeness classes

`Stacks.Chow.IsLocallyBoundedFiniteLocallyFree` records the finite local freeness of the terms as
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, while
`Stacks.Chow.BoundedComplexSplitting` records it as
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, a reducible abbreviation of the first, so the
hypothesis is passed on unchanged; no copy is made here. It is applied as a term rather than
through instance search, because the ring sheaf of the first
spelling is `Stacks.StrictlyPerfect.structureSheafOfRings X.toRingedSpace` and of the second
`AlgebraicGeometry.Scheme.ringCatSheaf X`, equal only at default transparency.

### How a consumer at an envelope presentation uses this

The three statements below ask for an isomorphism `ℰ^• ≅ ℱ^•` in `D(𝒪_X)`, which is the form the
independence of the representative takes. A consumer holding two
`Stacks.Chow.EnvelopePresentation`s of one object `E` over a common envelope `f : X ⟶ Z` holds
instead two isomorphisms `Lf^*E ≅ ℰ^•` and `Lf^*E ≅ ℱ^•`, and passes `eP.symm ≪≫ eQ`. No separate
statement is made for that composite: it is the whole of the step, and
`Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is kept out of the hypotheses here
precisely so that the statements are about `D(𝒪_X)` and not about one way of arriving in it.

What this does *not* supply, and what Stacks 0GUD existence needs beyond it, is the compatibility
of the classes with restriction — `pbCh` of
`StacksFrontier.AlgebraicGeometry.Chow.AdamsOperatorChernScaling` — which is what makes the two
restrictions of `c_p(Lf^*E)` to `X ×_Z X` agree, the hypothesis of Stacks 0GUC.

### Which derived category

`CategoryTheory.HasDerivedCategory` is a class and two instances of it for `X.Modules` give two
different categories. The standard model is fixed here by a file-level local instance, as in
`StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BoundedComplex`, whose hypotheses on the
cohomology sheaves are stated at it, and in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined`, where
`Stacks.Chow.EnvelopePresentation.representation` — the natural source of the isomorphism asked
for below — lives. The statements of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexDerivedCohomology` take the model as a
parameter and are usable at either.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0ESR](https://stacks.math.columbia.edu/tag/0ESR)
* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### A splitting at a window given as vanishing data -/

/-- **A bounded complex of finite locally free modules with perfect cohomology of tor dimension
at most one has a splitting at any window outside which it vanishes.**

This is `Stacks.FiniteLocallyFree.nonempty_boundedComplexSplitting` with the window supplied as
vanishing data rather than as the two instances `[P.IsStrictlyGE a]` and
`[P.IsStrictlyLE (a + k)]`. The two forms carry the same content —
`CochainComplex.isStrictlyGE_iff` and `CochainComplex.isStrictlyLE_iff` are the
characterisations — and this is the form in which a window extracted from an existential arrives,
so the apparent mismatch between the fixed-window constructor and the locally bounded statements
is dissolved here once; see the implementation notes of this file. -/
theorem nonempty_boundedComplexSplitting_of_isZero_outside (P : CochainComplex X.Modules ℤ)
    (a : ℤ) (k : ℕ) (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
    (hterm : ∀ n : ℤ, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (P.X n))
    (hperf : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htor : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0) :
    Nonempty (BoundedComplexSplitting X P a k) :=
  have : P.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff P a).2 fun i hi => hvanish i (Or.inl hi)
  have : P.IsStrictlyLE (a + (k : ℤ)) :=
    (CochainComplex.isStrictlyLE_iff P _).2 fun i hi => hvanish i (Or.inr hi)
  Stacks.FiniteLocallyFree.nonempty_boundedComplexSplitting P a k hterm hperf htor

/-- The terms of a locally bounded complex of finite locally free modules are finite locally free
in the spelling `Stacks.Chow.BoundedComplexSplitting` uses.

`Stacks.Chow.IsLocallyBoundedFiniteLocallyFree` already records this with the canonical
spelling `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, of which
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` is a reducible abbreviation. See the
implementation notes of this file for why it is applied as a term. -/
theorem isFiniteLocallyFree_X_of_isLocallyBounded {P : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (n : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n) :=
  hP.1 n

/-! ### The bridge to the locally bounded independence statements -/

/-- **The hypothesis of the locally bounded independence statements of Stacks 0ESZ, from a
derived isomorphism and the conclusion of Stacks 0ESR on `X`.**

Two locally bounded complexes of finite locally free modules on a quasi-compact scheme, each of
whose cohomology sheaves is a perfect `𝒪_X`-module of tor amplitude in `[-1, 0]`, and which are
isomorphic in `D(𝒪_X)`, satisfy `Stacks.Chow.HasCohomologyComparisonAtCommonWindow`.

A common window exists by
`Stacks.Chow.exists_common_window_of_isLocallyBoundedFiniteLocallyFree`; at it each complex has a
splitting by `Stacks.Chow.nonempty_boundedComplexSplitting_of_isZero_outside`, which is Stacks
0F8J; and the two splittings together with the derived isomorphism give the comparison datum by
`Stacks.Chow.hasCohomologyComparisonAtCommonWindow_of_derivedIso`.

**What this carries**: the perfectness and the tor amplitude, *on `X`*, which the source arranges
only on a modification of a test scheme, and quasi-compactness of `X`, which the locally bounded
classes themselves require. Nothing else: no comparison datum, no splitting, no window. See the
implementation notes of this file for why the hypothesis on `X` cannot be replaced by the
source's. -/
theorem hasCohomologyComparisonAtCommonWindow_of_derivedIso_of_isLocallyBounded [CompactSpace X]
    {P Q : CochainComplex X.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (hperfP : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htorP : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0)
    (hperfQ : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)))
    (htorQ : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)) (-1) 0)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    HasCohomologyComparisonAtCommonWindow P Q := by
  obtain ⟨w, hwP, hwQ⟩ := exists_common_window_of_isLocallyBoundedFiniteLocallyFree hP hQ
  obtain ⟨S⟩ := nonempty_boundedComplexSplitting_of_isZero_outside P w.1 w.2 hwP
    (isFiniteLocallyFree_X_of_isLocallyBounded hP) hperfP htorP
  obtain ⟨T⟩ := nonempty_boundedComplexSplitting_of_isZero_outside Q w.1 w.2 hwQ
    (isFiniteLocallyFree_X_of_isLocallyBounded hQ) hperfQ htorQ
  exact hasCohomologyComparisonAtCommonWindow_of_derivedIso w.1 w.2 hwP hwQ S T e

/-! ### Stacks 0ESZ for a locally bounded complex, with the comparison datum discharged -/

section TotalChernClass

open ChowCohomologySeriesRing

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [CompactSpace X] {R : ChowCohomologySeriesRing C Gy sX}

/-- **Stacks 0ESZ for the total Chern class of a locally bounded complex, with the comparison
datum discharged.** Two locally bounded complexes of finite locally free modules on a
quasi-compact scheme that are isomorphic in `D(𝒪_X)` and whose cohomology sheaves are perfect of
tor amplitude in `[-1, 0]` carry the same total Chern class:

  `c(ℰ^•) = c(ℱ^•)` in `∏_{p ≥ 0} A^p(X)`.

This is
`Stacks.Chow.totalChernClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow` with
its hypothesis supplied by
`Stacks.Chow.hasCohomologyComparisonAtCommonWindow_of_derivedIso_of_isLocallyBounded`. What
replaces the comparison datum is the conclusion of Stacks 0ESR read on `X`, which the source
arranges only on a modification; see the implementation notes of this file. -/
theorem totalChernClassComplexLocallyBounded_eq_of_derivedIso
    (D : TotalChernClassSeries C Gy sX R) {P Q : CochainComplex X.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (hperfP : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htorP : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0)
    (hperfQ : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)))
    (htorQ : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)) (-1) 0)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    totalChernClassComplexLocallyBounded C Gy sX D P hP =
      totalChernClassComplexLocallyBounded C Gy sX D Q hQ :=
  totalChernClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow C Gy sX D
    hP hQ (hasCohomologyComparisonAtCommonWindow_of_derivedIso_of_isLocallyBounded hP hQ
      hperfP htorP hperfQ htorQ e)

end TotalChernClass

section PowerSum

variable (C : ChowSituation.{u}) (Gy : GysinSystem C) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [CompactSpace X]

/-- **Stacks 0ESZ for `P_p` of a locally bounded complex, with the comparison datum
discharged.** Two locally bounded complexes of finite locally free modules on a quasi-compact
scheme that are isomorphic in `D(𝒪_X)` and whose cohomology sheaves are perfect of tor amplitude
in `[-1, 0]` carry the same class `P_p`, for every `p`. -/
theorem powerSumClassComplexLocallyBounded_eq_of_derivedIso (W : PowerSumClassRule C Gy sX)
    {P Q : CochainComplex X.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (hperfP : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htorP : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0)
    (hperfQ : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)))
    (htorQ : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)) (-1) 0)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (p : ℕ) :
    powerSumClassComplexLocallyBounded C Gy sX W P hP p =
      powerSumClassComplexLocallyBounded C Gy sX W Q hQ p :=
  powerSumClassComplexLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow C Gy sX W
    hP hQ (hasCohomologyComparisonAtCommonWindow_of_derivedIso_of_isLocallyBounded hP hQ
      hperfP htorP hperfQ htorQ e) p

/-- **Stacks 0ESZ for the Chern character of a locally bounded complex, with the comparison datum
discharged.** The components `ch_p = P_p/p!` of two such complexes agree in `A^p(X) ⊗ 𝐐`.

The statement is made at the pure-tensor shape in which the Stacks 0GUD uniqueness theorem
`Stacks.Chow.eq_of_restriction_eq_chernCharacterComplexLocallyBounded` takes its hypothesis,
there being no definition of the Chern character of a locally bounded complex in this
repository. -/
theorem chernCharacterLocallyBounded_eq_of_derivedIso (W : PowerSumClassRule C Gy sX)
    {P Q : CochainComplex X.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (hperfP : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htorP : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0)
    (hperfQ : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)))
    (htorQ : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)) (-1) 0)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (p : ℕ) :
    ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumClassComplexLocallyBounded C Gy sX W P hP p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumClassComplexLocallyBounded C Gy sX W Q hQ p :=
  chernCharacterLocallyBounded_eq_of_hasCohomologyComparisonAtCommonWindow C Gy sX W
    hP hQ (hasCohomologyComparisonAtCommonWindow_of_derivedIso_of_isLocallyBounded hP hQ
      hperfP htorP hperfQ htorQ e) p

end PowerSum

end Stacks.Chow

end

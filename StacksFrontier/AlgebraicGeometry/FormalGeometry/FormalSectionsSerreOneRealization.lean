module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparisonLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementQuotientTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAssociatedPointBridge
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import
StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionBounded
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Realizing formal sections under condition (3)(a) of Stacks 0EIF

Stacks 0EIF under its condition (3)(a) is all that the induction of Stacks 0EG2 consumes
(`StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionSerreOne`). This file
assembles the source's proof of it over the pieces the library has, and isolates what it still
lacks.

The source's proof runs: Stacks 0BK0 writes `F` as `M̃|_U` for a finite `A`-module `M`; conditions
(2) and (3) verify the hypotheses of Stacks 0EFL at `s = 1` and `d = cd(A, I)`, giving an ideal
`J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` for which `H^i_{J₀}(M) → H^i(RΓ_𝔞(M)^∧)` is an
isomorphism for `i = 0, 1`; comparing the localization triangle of `J₀` with its completion then
makes `Γ(V, F) → H⁰(RΓ(V, F)^∧)` an isomorphism, where `V = Spec(A) ∖ V(J₀)`; and finally
Stacks 0BLX, 0A0K and 0D60 identify `H⁰(RΓ(V, F)^∧)` with `lim H⁰(U, F / Iⁿ F)`.

Everything up to and including the third step is in the library, as
`Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf`. What
this file adds on the near side of Stacks 0BLX is the two inputs that declaration still takes in a
form the sheaf-level hypotheses of Stacks 0EIF do not directly supply — the extreme
values of a dimension function, and condition (3)(a) read at the associated primes of `M` — and,
on the far side, the exact shape in which the three closing tags are consumed.

## Main definitions

* `Stacks.Algebraization.CompletedComplementIsFormalSections` — **the one remaining input**:
  Stacks 0BLX, 0A0K and 0D60 combined, in the shape the proof of Stacks 0EIF consumes. See the
  implementation notes for why this is exactly Stacks 0BLX and nothing more.

## Main results

* `Stacks.Algebraization.exists_isGreatest_isLeast_dualizingDimension` — **condition (1) of
  Stacks 0EIF supplies the extreme values of a dimension function on `V(𝔞) ∩ V(I)`**, as soon as
  that set is nonempty. The route note of
  `StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative` recorded their
  existence under condition (3)(a) as owed; it is not, because the dimension function of a
  dualizing complex is bounded.
* `Stacks.Algebraization.supportDim_le_zero_of_isSerreOneOffVanishing` — **condition (3)(a) of
  Stacks 0EIF gives the ring-theoretic form of condition (5)(a) of Stacks 0EFL**: at an associated
  prime of `M` off `V(I)` the support of `M_𝔭` has dimension at most `0`. The route note recorded
  this as owed too; it is a consequence of Stacks 0346 and Stacks 02OJ, and needs nothing about
  the two module structures on a stalk.
* `Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_of_serreOne` — **the
  first half of the source's proof, with every input discharged**: under conditions (1), (2) and
  (3)(a) alone, for a proper `𝔞`, there is an ideal `J₀ ⊆ 𝔞` with
  `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` making `Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)` an isomorphism.
* `Stacks.Algebraization.opensNearVanishingOfInterEq` — the ideal `J₀` produced by Stacks 0EFL
  cuts out a neighbourhood of the formal locus `U ∩ V(I)` inside `U`.
* `Stacks.Algebraization.nonempty_zeroLocus_inter_of_ne_top` — `V(𝔞) ∩ V(I)` is nonempty as soon
  as `𝔞` is a proper ideal, `I` being contained in `𝔞`.

## What is still owed

With the two results above, everything the source does *before* invoking Stacks 0BLX is proved at
the source's own hypotheses. What is not proved is the passage from
`H⁰(RΓ(V, M̃)^∧)` to `lim Γ(U, M̃ / Iⁿ M̃)`, and it needs three things, of which only the first is
Stacks 0BLX:

1. `Stacks.Algebraization.CompletedComplementIsFormalSections`, below — Stacks 0BLX.
2. The Milnor sequence of a general `NoetherianAdicCompletion.IsDerivedLimitWithProjections` in
   `D(ModuleCat A)`, with its projections normalized. This is now proved, as
   `DerivedCategory.exists_milnor_shortExact_of_isDerivedLimitWithProjections` in
   `StacksFrontier.Homology.DerivedComplete.NormalizedDerivedLimitMilnor`, whose right-hand map is
   the named comparison map `DerivedCategory.derivedLimitHomologyToLimit` determined by the
   projections. `Dualizing.exists_milnor_shortExact_of_isDerivedLimit` and
   `Dualizing.completedLocalCohomologyToLimitOfProjections_shortExact`, which were the only
   forms the library had and were tied to `Dualizing.adicQuotientLocalCohomologySystem`, are its
   specializations to the tower of Stacks 0EEW.
3. The comparison of `Stacks.LocalCohomology.LocalizationTriangleData.sectionsIso` — which reads
   `H⁰(RΓ(V, N^~))` as `Γ(V, N^~)` on the scheme `Spec(A) ∖ V(J₀)` — with the sections of the
   same sheaf over the same open read inside `U`, namely over
   `Stacks.Algebraization.opensOffVanishing A J₀ 𝔞`. For `J₀ = 𝔞` this is
   `Stacks.LocalCohomology.sectionsOnAffineComplementIso` in
   `StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections`. The
   `J₀ ⊆ 𝔞` generalization is now proved, as `Stacks.Algebraization.sectionsOffVanishingIso` in
   `StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionsOffVanishing`, together with its
   naturality `Stacks.Algebraization.offVanishingSectionsHom_naturality`.

So of the three, only Stacks 0BLX remains as mathematical input, and the assembly over it is now
written:
`Stacks.Algebraization.isIso_comparisonMap_of_serreOne_of_completedComplementIsFormalSections` in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneClosure` derives Stacks 0EIF
under condition (3)(a) from `CompletedComplementIsFormalSections` and nothing
else, over the tower comparison of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAssembly`.

One seam of that assembly does not have to be crossed: `comparisonAt` and
`Stacks.Algebraization.sectionsNearVanishing` are valued in `Ab` while `sectionsOffVanishingIso`
is an isomorphism of `A`-modules. The difference is real for the two `A`-module
structures and irrelevant to the comparison map, which is a map of abelian groups: after
`forget₂ (ModuleCat A) Ab` the two descriptions are *equal*, by
`Stacks.Algebraization.forget₂_sectionsOffVanishingFunctor_map`, which is `rfl`.

Two hypotheses of this file's results were weakened for that assembly, and for one reason: the
source applies Stacks 0BK0 to replace `F` by `M̃|_U`, and condition (3)(a) cannot follow it across
that isomorphism, `AlgebraicGeometry.SheafHasPropertySk` having no iso-invariance lemma in this
library. So `Stacks.Algebraization.supportDim_le_zero_of_isSerreOneOffVanishing` and
`Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_of_serreOne` take a coherent
`F` together with an isomorphism `F ≅ M̃|_U` and read condition (3)(a) on `F`; the associated-point
identification crosses the isomorphism instead, by `Stacks.Divisors.associatedPoints_congr`.

## Implementation notes

### Why `CompletedComplementIsFormalSections` is exactly Stacks 0BLX

The source closes with three tags, and two of them are proved in this library:

* Stacks 0A0K identifies `F^∧` with `R lim F / Iⁿ F`; it is available as
  `Stacks.Algebraization.isDerivedLimit_single_limit_powerQuotients`.
* Stacks 0D60 moves a derived limit across derived sections; it is available as
  `Stacks.Cohomology.DerivedSectionsOverBase.isDerivedLimit_map_derivedSectionsOver`, with the
  Milnor sequence of the result and its normalized projections as
  `Stacks.Cohomology.DerivedSectionsOverBase.exists_shortExact_homology_derivedSectionsOver`.
* Stacks 0BLX is the identity `RΓ(V, F)^∧ = RΓ(V, F^∧)`. It is registered three times in this
  library and not once in that form — see the route note of
  `StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative`.

Composing the three gives one statement, and that statement is what the proof uses:

`RΓ(V, F)^∧ = R lim_n RΓ(V, F / Iⁿ F)`.

So `CompletedComplementIsFormalSections` asserts that the derived `I`-adic completion of the
derived sections of `M̃` on `V = Spec(A) ∖ V(J)` is a derived limit of the tower
`n ↦ RΓ(V, (M/IⁿM)^~)`, with the projections normalized against the completion unit. Granting it,
the two tags above are redundant and the remaining content is Stacks 0BLX alone; granting those two
tags, its remaining content is again Stacks 0BLX alone. Nothing about `U`, about the
comparison map, or about the three conditions of Stacks 0EIF enters it, so it does not smuggle in
any part of the conclusion.

The whole statement lives in `D(ModuleCat A)`: derived sections on `V` appear as the third vertex
`Stacks.LocalCohomology.LocalizationTriangleData.complement` of the affine localization triangle
of Stacks 0DWR, which is how the first half of the source's proof is already written in this
library, and the tower `n ↦ M/IⁿM` of modules is
`Stacks.LocalCohomology.idealPowerQuotientTower` — the same tower
`Stacks.Algebraization.formalSectionsRestrictedTildeIso` identifies `formalSections` with. No
ringed site, no sheaf-level completion and no universe enlargement occur, so a sheaf-level 0BLX
has to be transported into this shape, but nothing else does.

The projections are specified rather than existentially quantified. A bare `IsDerivedLimit`
determines its object only up to non-unique isomorphism, and the Milnor sequence it produces then
says nothing about which map `H⁰(RΓ(V, F)^∧) ⟶ lim H⁰(V, F / Iⁿ F)` it is; the normalization
`unit ≫ π n = RΓ(V, -)` applied to `M ⟶ M/IⁿM` is what makes the composite with the completion
unit the reduction map, and so what lets it be compared with
`Stacks.Algebraization.comparisonAt`. This is the same normalization part (1) of
Stacks 0EEW carries, as
`Stacks.Algebraization`'s
`isDerivedLimitWithProjections_completedLocalCohomologyNormalizedProjection_of_finite`.

### The extreme values of a dimension function

Condition (5) of Stacks 0EFL is stated against the greatest and least values of a dimension
function `δ` on `V(𝔞) ∩ V(I)`, so `Stacks.Algebraization.AlgebraizationHypotheses` carries them
as data. Under condition (3)(b) of Stacks 0EIF they come from the hypothesis itself, through
`Stacks.Algebraization.exists_isGreatest_isLeast_of_le_add_two`. Under condition (3)(a) they come
from condition (1): a dualizing complex of injective amplitude `[a, b]` has
`-N ≤ δ_K ≤ N` with `N = |a| + |b|` on the whole of `Spec(A)`
(`Dualizing.exists_bound_dualizingDimensionFunction`), and a two-sidedly bounded nonempty set of
integers has extreme values
(`Stacks.Algebraization.exists_isGreatest_isLeast_of_bddBelow_bddAbove`). Neither step needs the
closed subset to be anything but nonempty, so the maximum lemma of Stacks 0EIY
(`Stacks.Algebraization.exists_max_dimensionFunction_on_closed`), which has no companion for the
minimum, is not on this route at all.

Nonemptiness is a real hypothesis and not an oversight: for `𝔞 = A` the set `V(𝔞) ∩ V(I)` is
empty, `IsGreatest` of the empty set is false, and `AlgebraizationHypotheses` — hence the
library's Stacks 0EFL — is unsatisfiable.

That degenerate case is nevertheless proved, and without any affine statement `M ⟶ lim M/IⁿM`.
The declaration
`Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_of_eq_top` reaches the
conclusion of the theorem below by taking the ideal of Stacks 0EFL to be `A` itself.
`V(A) = ∅` makes the local cohomology object of the localization triangle have zero homology in
every degree, hence be a zero object, hence makes the triangle's second map an isomorphism
`RΓ(V, M̃) ≅ M`, and the completion unit is invertible there because `A` is `I`-adically complete
and `M` finite.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### The extreme values of a dimension function, from the dualizing complex -/

/-- **`V(𝔞) ∩ V(I)` is nonempty for a proper `𝔞` containing `I`.** A proper ideal is contained in
a maximal ideal, which then lies in both zero loci. -/
public theorem nonempty_zeroLocus_inter_of_ne_top {A : Type u} [CommRing A] (I a : Ideal A)
    (hle : I ≤ a) (hne : a ≠ ⊤) :
    (PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)).Nonempty := by
  obtain ⟨m, hm, ham⟩ := a.exists_le_maximal hne
  exact ⟨⟨m, hm.isPrime⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 ham,
    (PrimeSpectrum.mem_zeroLocus _ _).2 (hle.trans ham)⟩

/-- **Condition (1) of Stacks 0EIF supplies the data `δ`, `δmax`, `δmin` of condition (5) of
Stacks 0EFL.** A Noetherian ring with a dualizing complex carries a dimension function on its
spectrum which attains a greatest and a least value on every nonempty closed subset of the shape
`V(𝔞) ∩ V(I)`.

The dimension function is the one attached to the dualizing complex by Stacks 0A7Z, and what makes
its extreme values exist is that it is *bounded* — a dualizing complex of injective amplitude
`[a, b]` has `-(|a| + |b|) ≤ δ_K ≤ |a| + |b|` on all of `Spec(A)`, by
`Dualizing.exists_bound_dualizingDimensionFunction`. No maximum-attaining argument on the closed
subset is needed, and in particular the asymmetry of Stacks 0EIY — which produces a maximum at a
generic point and has no companion for the minimum — is not an obstruction here. -/
public theorem exists_isGreatest_isLeast_dualizingDimension {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I a : Ideal A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hne : (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty) :
    ∃ (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ), IsDimensionFunctionProp δ ∧
      IsGreatest (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmax ∧
      IsLeast (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmin := by
  obtain ⟨K, hK⟩ := hdualizing
  obtain ⟨N, hN⟩ := Dualizing.exists_bound_dualizingDimensionFunction.{u} hK
  obtain ⟨z₀, hz₀⟩ := hne
  set d := Dualizing.dualizingDimensionFunction.{u, u} K hK with hd
  obtain ⟨δmax, δmin, hmax, hmin⟩ :=
    exists_isGreatest_isLeast_of_bddBelow_bddAbove
      (S := d.toFun '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A)))
      ⟨d.toFun z₀, ⟨z₀, hz₀, rfl⟩⟩ (lo := -(N : ℤ)) (hi := (N : ℤ))
      (by rintro y ⟨x, -, rfl⟩; exact (hN x).1) (by rintro y ⟨x, -, rfl⟩; exact (hN x).2)
  exact ⟨d.toFun, δmax, δmin, isDimensionFunctionProp_toFun d, hmax, hmin⟩

/-! ### The ideal of Stacks 0EFL cuts out a neighbourhood of the formal locus -/

/-- **The ideal produced by Stacks 0EFL cuts out a neighbourhood of the formal locus.** If
`J ⊆ 𝔞` and `V(J) ∩ V(I) = V(𝔞) ∩ V(I)` then `V = Spec(A) ∖ V(J)`, read as an open of
`U = Spec(A) ∖ V(𝔞)`, contains `U ∩ V(I)`.

A point of `U` in `V(J) ∩ V(I)` would lie in `V(𝔞) ∩ V(I)` and hence in `V(𝔞)`, which is what
lying in `U` forbids. -/
public def opensNearVanishingOfInterEq {A : Type u} [CommRing A] (I a J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    OpensNearVanishing A I a where
  openSet := opensOffVanishing A J a
  contains_vanishing x hxI := by
    rw [mem_opensOffVanishing]
    intro hxJ
    have hx : x.1 ∈ PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) :=
      ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 hxJ, (PrimeSpectrum.mem_zeroLocus _ _).2 hxI⟩
    rw [hV] at hx
    exact x.2 hx.1

/-! ### Condition (3)(a) of Stacks 0EIF in its ring-theoretic form -/

/-- **Condition (3)(a) of Stacks 0EIF gives the ring-theoretic form of condition (5)(a) of
Stacks 0EFL.** If the restriction of `M̃|_U` to `U ∖ V(I)` satisfies Serre's condition `(S₁)`,
then at every associated prime `𝔭` of `M` not containing `I` the support of `M_𝔭` has
dimension at most `0`.

This is the bridge that the route note of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative` records as owed,
and it does not go through the stalks at all. Serre's `(S₁)` for a coherent module on a locally
Noetherian scheme is the absence of embedded associated points, by Stacks 0346
(`AlgebraicGeometry.hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one`); the associated points
of a restriction along an open immersion are the associated points of the sheaf lying there, by
Stacks 02OJ (`AlgebraicGeometry.isAssociatedPoint_restrict_iff`); and the associated points of
`M̃|_U` are the associated primes of `M` lying in `U`, by
`Stacks.LocalCohomology.mem_associatedPoints_complementTilde_iff`. So an associated prime `𝔮 ⊊ 𝔭`
would exhibit `𝔭` as an embedded associated point of the restriction — `𝔮` lies in `U ∖ V(I)`
because `I ⊆ 𝔮 ⊆ 𝔭` is excluded and `I ⊆ 𝔞`, and specialization is inherited by a subspace. That
no associated prime is strictly inside `𝔭` is exactly `dim Supp(M_𝔭) ≤ 0`, by
`Module.supportDim_localized_le_zero_iff`.

Only the last of those four was out of reach, and only because it was `private`; the comparison of
the two module structures on a stalk that the route note calls missing is not on this route. -/
@[ega "IV 5.7.5" "partial"]
public theorem supportDim_le_zero_of_isSerreOneOffVanishing {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I a : Ideal A) (hle : I ≤ a)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {F : (complementZeroLocus A a : Scheme).Modules} (hFc : F.IsCoherent)
    (e : F ≅ (complementTilde A a (ModuleCat.of A M) :
      (complementZeroLocus A a : Scheme).Modules))
    (hS : IsSerreOneOffVanishing A I a F)
    (p : PrimeSpectrum A) (hp : p.asIdeal ∈ associatedPrimes A M) (hpI : ¬ I ≤ p.asIdeal) :
    Module.supportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) ≤ (0 : WithBot ℕ∞) := by
  have hAss := (Stacks.Divisors.associatedPoints_congr e).symm.subset
  have _ : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion (complementZeroLocus A a).ι
  have _ : IsLocallyNoetherian (opensOffVanishing A I a).toScheme :=
    AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion (opensOffVanishing A I a).ι
  have _ : ((Scheme.Modules.restrictFunctor (opensOffVanishing A I a).ι).obj F).IsCoherent :=
    isCoherent_restrict_of_isOpenImmersion (opensOffVanishing A I a).ι F
  have hNo := (AlgebraicGeometry.hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one
    (opensOffVanishing A I a).toScheme _).2 hS
  have key : ∀ (r : PrimeSpectrum A) (hrI : ¬ I ≤ r.asIdeal), r.asIdeal ∈ associatedPrimes A M →
      Stacks.Divisors.IsAssociatedPoint (Scheme.Modules.restrict F (opensOffVanishing A I a).ι)
        (⟨⟨r, fun h => hrI (hle.trans h)⟩, (mem_opensOffVanishing A I a _).2 hrI⟩ :
          (opensOffVanishing A I a).toScheme) := fun r hrI hr =>
    (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff
      (opensOffVanishing A I a).ι F _).2
      (hAss ((mem_associatedPoints_complementTilde_iff A a (ModuleCat.of A M) _).2 hr))
  refine (Module.supportDim_localized_le_zero_iff (M := M) p).2 fun q hq hqp => ?_
  have hqprime : q.IsPrime := (AssociatedPrimes.mem_iff.mp hq).isPrime
  have hqI : ¬ I ≤ q := fun h => hpI (h.trans hqp.le)
  refine hNo ⟨⟨p, fun h => hpI (hle.trans h)⟩, (mem_opensOffVanishing A I a _).2 hpI⟩
    ⟨key p hpI hp, ⟨⟨⟨q, hqprime⟩, fun h => hqI (hle.trans h)⟩,
      (mem_opensOffVanishing A I a _).2 hqI⟩, key ⟨q, hqprime⟩ hqI hq, ?_, ?_⟩
  · exact (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).specializes_iff.mp
      ((PrimeSpectrum.le_iff_specializes ⟨q, hqprime⟩ p).mp hqp.le)
  · exact fun heq => hqp.ne (congrArg (fun w : (opensOffVanishing A I a).toScheme =>
      (w.1.1 : PrimeSpectrum A).asIdeal) heq)

/-! ### The first half of the source's proof, at the hypotheses of condition (3)(a) -/

/-- **The first half of the source's proof of Stacks 0EIF, with every input discharged from the
hypotheses of condition (3)(a).** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` with `𝔞` proper,
and let `M` be a finite `A`-module whose sheaf `M̃|_U` on `U = Spec(A) ∖ V(𝔞)` satisfies
conditions (1), (2) and (3) of Stacks 0EIF with the third in the form (3)(a). Then there is an
ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` for which the unit of derived `I`-adic
completion is invertible on `H⁰` of the derived sections of `M̃` on `V = Spec(A) ∖ V(J₀)`:

`Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)`

is an isomorphism, for every localization triangle datum of `J₀`.

This is `Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf`
with its two remaining ring-theoretic inputs supplied from the sheaf-level hypotheses: the
dimension function and its extreme values come from condition (1) through
`Stacks.Algebraization.exists_isGreatest_isLeast_dualizingDimension`, and condition (3) in its
ring-theoretic form comes from condition (3)(a) through
`Stacks.Algebraization.supportDim_le_zero_of_isSerreOneOffVanishing`. Nothing beyond
`Stacks.Algebraization.FormalSectionsHypotheses`, the standing assumption `I ⊆ 𝔞`,
`Stacks.Algebraization.IsSerreOneOffVanishing` and `𝔞 ≠ A` is assumed, so everything the source
does before invoking Stacks 0BLX is now proved at the source's own hypotheses.

The properness of `𝔞` is where the library's Stacks 0EFL stops applying rather than a gap in this
argument: `V(𝔞) ∩ V(I)` is empty for `𝔞 = A`, and `IsGreatest` of the empty set is false, so
`Stacks.Algebraization.AlgebraizationHypotheses` has no instances there. -/
public theorem exists_ideal_isIso_homology_zero_completionUnit_of_serreOne
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {F : (complementZeroLocus A a : Scheme).Modules} (hFc : F.IsCoherent)
    (e : F ≅ (complementTilde A a (ModuleCat.of A M) :
      (complementZeroLocus A a : Scheme).Modules))
    (hIa : I ≤ a) (hFSH : FormalSectionsHypotheses A I a F)
    (hS : IsSerreOneOffVanishing A I a F)
    (hane : a ≠ ⊤) :
    ∃ J₀ : Ideal A, J₀ ≤ a ∧
      ∃ _hV : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A),
        ∀ D : LocalizationTriangleData.{u, u} A J₀ J₀.fg_of_isNoetherianRing,
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
              (D.complement.obj (ModuleCat.of A M)))) := by
  obtain ⟨K, hK⟩ := hFSH.dualizing
  obtain ⟨δ, δmax, δmin, hδ, hmax, hmin⟩ :=
    exists_isGreatest_isLeast_dualizingDimension I a hFSH.dualizing
      (nonempty_zeroLocus_inter_of_ne_top I a hIa hane)
  exact exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf I a K δ δmax δmin
    hFSH.adicComplete hK hδ hmax hmin
    (fun x hx => hFSH.associatedPointsDimension x
      ((Stacks.Divisors.associatedPoints_congr e).symm.subset hx))
    (Or.inl fun p hp hpI =>
      supportDim_le_zero_of_isSerreOneOffVanishing I a hIa hFc e hS p hp hpI)

/-! ### Stacks 0BLX in the shape the proof of Stacks 0EIF consumes -/

/-- **Stacks 0BLX, 0A0K and 0D60 combined, in the shape the proof of Stacks 0EIF consumes.** For
an ideal `J` of a Noetherian ring `A`, a finite `A`-module `M` and a localization triangle datum
`D` of `J` — whose third vertex `D.complement.obj M` is the derived sections `RΓ(V, M̃)` on
`V = Spec(A) ∖ V(J)` — the derived `I`-adic completion of `RΓ(V, M̃)` is a derived limit of the
tower `n ↦ RΓ(V, (M/IⁿM)^~)`, with projections normalized against the completion unit.

This is the identity `RΓ(V, F)^∧ = RΓ(V, F^∧) = RΓ(V, R lim F/IⁿF) = R lim RΓ(V, F/IⁿF)` with
which the source closes, written out once. Its first equality is Stacks 0BLX, its second
Stacks 0A0K and its third Stacks 0D60; the last two are proved in this library, so what the
hypothesis still carries is Stacks 0BLX and nothing else.

The normalization clause is what makes the hypothesis usable: the Milnor sequence of a derived
limit identifies `H⁰` of the limit object with `lim H⁰` of the tower *through the projections*, so
without pinning them down the resulting map is not comparable with
`Stacks.Algebraization.comparisonAt`. With it, the composite of the completion unit with the
level-`n` projection is the map induced by the reduction `M ⟶ M/IⁿM`, which is exactly what the
comparison map reduces a section by. -/
public def CompletedComplementIsFormalSections : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (D : LocalizationTriangleData.{u, u} A J J.fg_of_isNoetherianRing),
    ∃ _h : HasProduct (fun n : ℕ ↦
        (idealPowerQuotientTower.{u, u} I M ⋙ D.complement).obj ⟨n⟩),
      ∃ π : ∀ n : ℕ, (adicCompletionFunctor A I I.fg_of_isNoetherianRing).obj
          (D.complement.obj M) ⟶ (idealPowerQuotientTower.{u, u} I M ⋙ D.complement).obj ⟨n⟩,
        NoetherianAdicCompletion.IsDerivedLimitWithProjections
            (idealPowerQuotientTower.{u, u} I M ⋙ D.complement)
            ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).obj (D.complement.obj M)) π ∧
          ∀ n : ℕ, (adicCompletionUnit A I I.fg_of_isNoetherianRing).app
              (D.complement.obj M) ≫ π n =
            D.complement.map ((idealPowerQuotientCone.{u, u} I M).π.app ⟨n⟩)

end Stacks.Algebraization

end

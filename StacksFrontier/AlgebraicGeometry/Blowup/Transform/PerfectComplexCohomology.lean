module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingNormalForm
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingProduct
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.KernelTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdeal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealAlternatingRank
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness

/-!
# Blowing up to improve the cohomology of a perfect complex

Let `E` be a perfect object of `D(𝒪_X)` on a scheme `X` whose cohomology on a
scheme-theoretically dense open `U ⊆ X` is finite locally free of constant rank `r_i` in every
degree. Stacks tag 0ESQ produces a `U`-admissible blowup `b : X' ⟶ X` after which every
cohomology module `H^i(Lb^*E)` is a perfect `𝒪_{X'}`-module of Tor dimension at most one.

The blowup of the source is the blowup of `X` in the product of the Fitting ideal sheaves
`Fit_{i, k_i}(E)` of tag 0ESP, one for each degree, with `k_i` the alternating sum
`r_{i+1} - r_{i+2} + ⋯` of the ranks above `i`. This file constructs that blowup, for the
product over a finite set of degrees, and proves the two properties of it that the source's
proof uses: it is a `U`-admissible blowup, and each factor `Fit_{i, k_i}(E)` pulls back to an
effective Cartier divisor on it.

## Main definitions

* `AlgebraicGeometry.HomologyIsPerfectTorLEOne`: the conclusion of tag 0ESQ in one degree, that
  `H^i(Lb^*E)` is a perfect `𝒪_{X'}`-module of Tor dimension at most one.
* `AlgebraicGeometry.HasHomologyTwoTermResolution`: that `H^i(Lb^*E)` is the cokernel of a
  monomorphism of finite locally free modules on the whole of `X'`.
* `AlgebraicGeometry.HasHomologyTwoTermResolutionLocally`: that `H^i(Lb^*E)` is such a cokernel
  on a neighbourhood of every point, which is what the source's affine-local argument produces
  and what the last step of its second paragraph consumes.
* `AlgebraicGeometry.fittingIdealSheafProd`: the centre of the blowup, the product of the
  Fitting ideal sheaves `Fit_{i, k_i}(E)` over a finite set of degrees.

## Main results

* `Stacks.Blowup.exists_admissibleBlowup_forall`: finitely many `U`-admissible blowups, each
  achieving a property that survives a further admissible blowup, are dominated by a single
  `U`-admissible blowup achieving all of them. This is the step the source performs with tags
  080A and 080N ("tiny detail omitted; compare with the proof of Divisors, Lemma 080N").
* `AlgebraicGeometry.isAdmissibleBlowup_blowUpToBase_fittingIdealSheafProd`: the blowup of `X`
  in the product of the Fitting ideal sheaves of `E` is a `U`-admissible blowup.
* `AlgebraicGeometry.isEffectiveCartierDivisor_comap_fittingIdealSheafProd`: on that blowup each
  of the Fitting ideal sheaves in the product pulls back to an effective Cartier divisor, which
  is the hypothesis "`Fit_{i, k_i}(E)` is an invertible ideal for all `i`" of the second half of
  the source's proof.
* `isPerfect_and_hasTorAmplitude_of_locally_hasTwoTermFiniteLocallyFreeResolution` and
  `AlgebraicGeometry.isHomologyPerfectTorLEOne_of_hasHomologyTwoTermResolutionLocally`: the last
  step of the second half of the source's proof, that a module which on a neighbourhood of every
  point is the cokernel of a monomorphism of finite locally free modules is perfect of Tor
  dimension at most one. Both halves of that conclusion are local conditions, so the resolution
  is needed only locally, which is all the source's affine-local argument gives; perfectness
  descends by `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect` and Tor
  amplitude by `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top_restrictFunctor`.
* `AlgebraicGeometry.isHomologyPerfectTorLEOne_of_hasHomologyTwoTermResolution`: the same from a
  resolution on the whole of `X'`, the strictly stronger hypothesis. It reads
  `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution` of
  `StacksFrontier/AlgebraicGeometry/Blowup/Transform/TwoTermResolution.lean` at the cohomology of a
  derived pullback.
The statement of tag 0ESQ itself is
`AlgebraicGeometry.exists_admissibleBlowup_forall_isHomologyPerfectTorLEOne` of
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/PerfectComplexAdmissibleBlowup.lean`, which
reaches it at the source's hypotheses through the chart description of the Fitting ideal sheaves;
the implementation notes say how the material here stands to it.

## Implementation notes

**The index of the Fitting ideal sheaves.** `k` is the source's alternating sum
`k_i = r_{i+1} - r_{i+2} + ⋯ + (-1)^{m-i+1} r_m`, `Stacks.FittingComplex.alternatingRankSum r m`:
it is determined by the ranks `r` of the cohomology of `E` on `U` together with a degree `m`
above which those ranks vanish; perfectness bounds the amplitude of `E` only locally, so such a
degree comes either from a hypothesis or, as in the unconditional proof of the tag, from a single
affine chart.
`Stacks.FittingComplex.alternatingRankSum_eq_of_vanishing` says that nothing turns on which such
bound is taken.

Pinning the index is what keeps the statement from being empty. At a freely chosen index the
assertion that the support of `Fit_{i, k_i}(E)` avoids `U` is *false*, by
`AlgebraicGeometry.not_disjoint_support_fittingIdealSheaf_of_card_lt_minorSize`: on an affine open
carrying a finite free model whose prescribed size of minors exceeds the size of the matrix of
`d_i` the Fitting ideal sheaf vanishes, and then its support contains the whole open. For a model
all of whose ranks are `0` the prescribed size is `-k_i`, so every negative index does this. At
the alternating rank sum the prescribed size of the minors of a model whose ranks are `r` is
exactly `0` and the ideal of its minors is the unit ideal, so that mechanism is unavailable:
`AlgebraicGeometry.FreeModel.not_card_lt_minorSize_alternatingRankSum`.

**Where tag 0ESQ is proved.** The statement of the tag, at the source's hypotheses and nothing
further, is `AlgebraicGeometry.exists_admissibleBlowup_forall_isHomologyPerfectTorLEOne` of
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/PerfectComplexAdmissibleBlowup.lean`. It runs
against the chart description of the Fitting ideal sheaves,
`AlgebraicGeometry.ComplexAndDivisorSituation.chartFittingIdeal`, for which the local description
of tag 0ESP holds in both directions
(`AlgebraicGeometry.ComplexAndDivisorSituation.ideal_chartFittingIdeal`), and it takes the
source's own centre, the locally finite product over every degree
`AlgebraicGeometry.ComplexAndDivisorSituation.fittingIdealProdOfRanks`. The second paragraph of
the source's proof is
`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_and_hasTorAmplitude_homology_pullback`.

**What this file contributes.** The first half of the source's proof against the
`fittingIdealSheaf` encoding of tag 0ESP: the centre as a product over a `Finset` of degrees, its
`U`-admissibility, the invertibility of each factor on the blowup, and — from the local
description of tag 0ESP over `U`, `AlgebraicGeometry.HasLocalFittingDescription` — the
disjointness of the supports of the factors from `U`. And the last step of the second half,
`AlgebraicGeometry.isHomologyPerfectTorLEOne_of_hasHomologyTwoTermResolutionLocally`: a
cohomology module which on a neighbourhood of every point is the cokernel of a monomorphism of
finite locally free modules is perfect of Tor dimension at most one. That step is where the
*local* form of the resolution, which is all the source's affine-local argument produces, is
shown to suffice, and it does not depend on how the Fitting ideal sheaves are described.

**One inclusion of tag 0ESP for this encoding.** `AlgebraicGeometry.fittingIdealSheaf` is the
largest quasi-coherent ideal sheaf below the ideals of minors of every bounded-above finite free
model of every complex representing `E`, so `AlgebraicGeometry.ideal_fittingIdealSheaf_le` is
immediate while every *lower* bound on it — finite type, the unit ideal, the local equality with
the ideal of minors — passes through
`AlgebraicGeometry.le_fittingIdealSheaf_of_le_minorIdeal` and so through a quasi-coherent ideal
sheaf realizing those minors. `AlgebraicGeometry.HasLocalFittingDescription` is exactly such a
witness over a given open, and `AlgebraicGeometry.hasLocalFittingDescription_of_minorIdeal_le`
cuts it down to the reverse inclusion over that open alone. The chart description cited above
obtains the two-sided local description instead by *constructing* the ideal sheaf from the charts,
with `AlgebraicGeometry.Scheme.IdealSheafData.ofAffineFamily`.

**The restriction to finitely many degrees.** The source takes the product of `Fit_{i, k_i}(E)`
over all `i ∈ ℤ`, which makes sense because locally almost all of them are the unit ideal. The
centre built here is the product over a `Finset` of degrees, through
`Stacks.Blowup.isFiniteType_prod` and `Stacks.Blowup.disjoint_support_prod`, exactly as in
`AlgebraicGeometry.fittingIdealProd` for tag 0ESU. The source's own product over every degree is
`AlgebraicGeometry.Scheme.IdealSheafData.locallyFiniteProd` of
`StacksFrontier/AlgebraicGeometry/IdealSheafLocallyFiniteProduct/Basic.lean`.

**Vocabulary.** `Lb^*` is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom`, the
derived pullback of tag 079W; `H^i` is `DerivedCategory.homologyFunctor`; perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect` (tag 08CM) of the module placed in degree zero;
and "of Tor dimension at most one" is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude` in
`[-1, 0]` (tag 08CG). These are the spellings of the neighbouring tags 0ESN, 0ESS and 0EST in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/FittingNormalForm.lean` and
`StacksFrontier/AlgebraicGeometry/Blowup/PerfectPullback.lean`. Admissibility of a blowup is
`Stacks.Blowup.IsAdmissibleBlowup` (tag 080K), whose centre is a
`AlgebraicGeometry.Scheme.IdealSheafData`; it is phrased against `Stacks.Blowup.blowUp`, while
the Fitting and effective-Cartier material is phrased against `AlgebraicGeometry.blowUp`, and
`Stacks.Blowup.isAdmissibleBlowup_iff` is what crosses between the two.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080N](https://stacks.math.columbia.edu/tag/080N)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect AlgebraicGeometry
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.FittingComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Blowup

/-- **Finitely many `U`-admissible blowups are dominated by one.** Let `P Y f i` be a property of
a morphism `f : Y ⟶ X` depending on an index `i` from a finite type, which survives
precomposition with an `f ⁻¹ᵁ U`-admissible blowup. If for each index there is a `U`-admissible
blowup with that property, then there is a single `U`-admissible blowup `b : X' ⟶ X` with every
one of them.

This is the combination step of the proof of Stacks tag 0ESQ, which the source performs by
blowing up a product of centres and invoking Stacks tags 080A and 080N. Here it is
`Stacks.Blowup.exists_admissibleBlowup_dominating`, tag 080N, which already produces the
dominating blowup together with factor maps that are themselves admissible blowups of the
inverse images of `U`. -/
theorem exists_admissibleBlowup_forall {X : Scheme.{u}} (U : X.Opens) {ι : Type*} [Finite ι]
    (P : ∀ Y : Scheme.{u}, (Y ⟶ X) → ι → Prop)
    (hstab : ∀ (Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y) (i : ι),
      IsAdmissibleBlowup (f ⁻¹ᵁ U) g → P Y f i → P Z (g ≫ f) i)
    (hex : ∀ i : ι, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsAdmissibleBlowup U f ∧ P Y f i) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), IsAdmissibleBlowup U b ∧ ∀ i : ι, P X' b i := by
  choose Y f hfP using hex
  obtain ⟨X', b, hb, g, hg, hgadm⟩ :=
    exists_admissibleBlowup_dominating U Y f fun i => (hfP i).1
  refine ⟨X', b, hb, fun i => ?_⟩
  have h := hstab (Y i) X' (f i) (g i) i (hgadm i) (hfP i).2
  rwa [hg i] at h

end Stacks.Blowup

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (k : ℤ → ℤ)

/-- **The conclusion of Stacks tag 0ESQ in one degree.** For a morphism `b : Y ⟶ X` and a degree
`i`, the `i`-th cohomology module of the derived pullback of `E` along `b` is a perfect
`𝒪_Y`-module of Tor dimension at most one. -/
def HomologyIsPerfectTorLEOne {Y : Scheme.{u}} (b : Y ⟶ X) (i : ℤ) : Prop :=
  IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) i).obj
          ((derivedPullback b.toLRSHom.toShHom).obj E))) ∧
    HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) i).obj
          ((derivedPullback b.toLRSHom.toShHom).obj E))) (-1) 0

/-- **The hypothesis `hres` of Stacks tag 0ESQ in one degree.** For a morphism `b : Y ⟶ X` and a
degree `i`, the `i`-th cohomology module of the derived pullback of `E` along `b` is the cokernel
of a monomorphism of finite locally free `𝒪_Y`-modules.

This is what the second paragraph of the source's proof produces in the degree `i` from a finite
free model of the pullback: the short exact sequence
`0 ⟶ Im(d_{i-1}) ⟶ Ker(d_i) ⟶ H^i(Lb^*E) ⟶ 0` with both outer terms finite locally free. It is
written as a predicate of `b` and `i`, like
`AlgebraicGeometry.HomologyIsPerfectTorLEOne` above, so that the hypothesis of the tag can name
the single morphism the theorem produces without spelling the centre of the blowup out three
times. -/
def HasHomologyTwoTermResolution {Y : Scheme.{u}} (b : Y ⟶ X) (i : ℤ) : Prop :=
  HasTwoTermFiniteLocallyFreeResolution
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) i).obj
      ((derivedPullback b.toLRSHom.toShHom).obj E))

/-- **The last step of the second paragraph of the proof of Stacks tag 0ESQ.** If `H^i(Lb^*E)` is
the cokernel of a monomorphism of finite locally free `𝒪_Y`-modules, then it is a perfect
`𝒪_Y`-module of Tor dimension at most one.

This is
`AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution` read
through the two predicates above, which are its hypothesis and its conclusion at the cohomology
of a derived pullback. -/
theorem isHomologyPerfectTorLEOne_of_hasHomologyTwoTermResolution {Y : Scheme.{u}} (b : Y ⟶ X)
    (i : ℤ) (h : HasHomologyTwoTermResolution E b i) : HomologyIsPerfectTorLEOne E b i :=
  isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution _ h

/-- Perfectness of an object of the derived category of `𝒪_X`-modules is invariant under
isomorphism: a perfect complex representing one object represents the other. -/
theorem isPerfect_of_iso_derived {Z : RingedSpace.{u, u}}
    {K L : DerivedCategory (OXMod.{u, u} Z)} (e : K ≅ L)
    (h : IsPerfect.{u, u, u + 1} K) : IsPerfect.{u, u, u + 1} L := by
  obtain ⟨C, hC, ⟨eC⟩⟩ := h
  exact ⟨C, hC, ⟨eC ≪≫ e⟩⟩

/-- **A two-term finite locally free resolution is only needed locally.** A module on a scheme
which, on a neighbourhood of every point, is the cokernel of a monomorphism of finite locally
free modules is perfect of Tor dimension at most one.

`AlgebraicGeometry.HasTwoTermFiniteLocallyFreeResolution` asks for a short exact sequence
`0 ⟶ ℒ₁ ⟶ ℒ₂ ⟶ ℳ ⟶ 0` with both outer terms finite locally free on the whole scheme, which is
*not* what the second paragraph of the proof of Stacks tag 0ESQ produces: that argument reads the
sequence `0 ⟶ Im(d_{i-1}) ⟶ Ker(d_i) ⟶ H^i ⟶ 0` off a finite free model of the complex on an
affine open, so it produces one sequence per member of a covering. Both halves of the conclusion
are local conditions, so the local sequences suffice: perfectness descends by
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`, and Tor amplitude in
`[-1, 0]` by `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top_restrictFunctor`,
which carries the interval unchanged. On each member of the covering the two are
`AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution`.

Restriction of modules to an open subscheme appears in two spellings, as
`AlgebraicGeometry.RingedSpace.restrictModules` on a ringed space and as
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` on a scheme, and the two local-to-global
results are stated in different ones; both crossings are made here, on derived categories by
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor` and for the degree-zero
single functor by `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
theorem isPerfect_and_hasTorAmplitude_of_locally_hasTwoTermFiniteLocallyFreeResolution
    {Y : Scheme.{u}} (M : Y.Modules)
    (h : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      HasTwoTermFiniteLocallyFreeResolution ((Scheme.Modules.restrictFunctor V.ι).obj M)) :
    IsPerfect.{u, u, u + 1}
        ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj M) ∧
      HasTorAmplitude Y.toRingedSpace
        ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj M) (-1) 0 := by
  choose V hV hloc using h
  have hlocal : ∀ y : Y,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor
          (OXMod.{u, u} (V y).toScheme.toRingedSpace) 0).obj
            ((Scheme.Modules.restrictFunctor (V y).ι).obj M)) ∧
        HasTorAmplitude (V y).toScheme.toRingedSpace
          ((DerivedCategory.singleFunctor (OXMod.{u, u} (V y).toScheme.toRingedSpace) 0).obj
            ((Scheme.Modules.restrictFunctor (V y).ι).obj M)) (-1) 0 := fun y =>
    isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution _ (hloc y)
  have hcross : ∀ y : Y,
      (Scheme.Modules.restrictFunctor (V y).ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj M) ≅
        (DerivedCategory.singleFunctor (OXMod.{u, u} (V y).toScheme.toRingedSpace) 0).obj
          ((Scheme.Modules.restrictFunctor (V y).ι).obj M) := fun y =>
    ((Scheme.Modules.restrictFunctor (V y).ι).mapDerivedCategorySingleFunctor 0).app M
  refine ⟨?_, ?_⟩
  · refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect.{u, u + 1}
      (X := Y.toRingedSpace) _ fun y => ?_
    exact ⟨V y, hV y, isPerfect_of_iso_derived
      (((RingedSpace.derivedRestrictModulesIsoRestrictFunctor Y (V y)).app _).trans
        (hcross y)).symm (hlocal y).1⟩
  · refine hasTorAmplitude_of_iSup_eq_top_restrictFunctor Y _ (-1) 0 V ?_ fun y => ?_
    · exact le_antisymm le_top fun x _ =>
        TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hV x⟩
    · exact hasTorAmplitude_of_retract (X := (V y).toScheme.toRingedSpace) (-1) 0
        (hcross y).hom (hcross y).inv (hcross y).hom_inv_id (hlocal y).2

/-- **The hypothesis `hres` of Stacks tag 0ESQ in one degree, in the form the source's proof
produces it.** For a morphism `b : Y ⟶ X` and a degree `i`, every point of `Y` has a
neighbourhood on which the `i`-th cohomology module of the derived pullback of `E` along `b` is
the cokernel of a monomorphism of finite locally free modules.

`AlgebraicGeometry.HasHomologyTwoTermResolution` asks for one such sequence on the whole of `Y`.
The source's argument is affine-local — it reads
`0 ⟶ Im(d_{i-1}) ⟶ Ker(d_i) ⟶ H^i(Lb^*E) ⟶ 0` off a finite free model of the complex on an
affine open — so this is what it delivers, and it is enough, by
`AlgebraicGeometry.isHomologyPerfectTorLEOne_of_hasHomologyTwoTermResolutionLocally`. -/
def HasHomologyTwoTermResolutionLocally {Y : Scheme.{u}} (b : Y ⟶ X) (i : ℤ) : Prop :=
  ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    HasTwoTermFiniteLocallyFreeResolution
      ((Scheme.Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y.toRingedSpace) i).obj
          ((derivedPullback b.toLRSHom.toShHom).obj E)))

/-- **The last step of the second paragraph of the proof of Stacks tag 0ESQ, from the local
resolution.** If every point of `Y` has a neighbourhood on which `H^i(Lb^*E)` is the cokernel of
a monomorphism of finite locally free `𝒪_Y`-modules, then `H^i(Lb^*E)` is a perfect
`𝒪_Y`-module of Tor dimension at most one.

Its hypothesis is strictly weaker than that of
`AlgebraicGeometry.isHomologyPerfectTorLEOne_of_hasHomologyTwoTermResolution`: restriction to an
open subscheme is exact and carries finite locally free modules to finite locally free modules,
so a global resolution restricts to a resolution on every open, while the converse fails for a
module admitting no global surjection from a finite locally free module. -/
theorem isHomologyPerfectTorLEOne_of_hasHomologyTwoTermResolutionLocally {Y : Scheme.{u}}
    (b : Y ⟶ X) (i : ℤ) (h : HasHomologyTwoTermResolutionLocally E b i) :
    HomologyIsPerfectTorLEOne E b i :=
  isPerfect_and_hasTorAmplitude_of_locally_hasTwoTermFiniteLocallyFreeResolution _ h

/-- **The centre of the blowup of Stacks tag 0ESQ.** The product of the Fitting ideal sheaves
`Fit_{i, k_i}(E)` of tag 0ESP over a finite set `s` of degrees. -/
abbrev fittingIdealSheafProd (s : Finset ℤ) : X.IdealSheafData :=
  ∏ i ∈ s, fittingIdealSheaf.{u, u + 1} E i (k i)

/-- **The blowup of Stacks tag 0ESQ for the `fittingIdealSheaf` encoding.** The blowup of `X` in
the product of the Fitting ideal sheaves of `E` over a finite set of degrees is a `U`-admissible
blowup, as soon as each factor is of finite type and supported away from `U`.

A finite product of ideal sheaves of finite type is of finite type and the support of a product
is the union of the supports, so the centre is of finite type and avoids `U`; finite
presentation of its closed subscheme is then tag 01TV.

Finite type and the disjointness from `U` are hypotheses here, where the source derives them, and
the centre is a product over a `Finset` of degrees rather than the source's product over every
degree. The tag's registration for this clause is therefore on
`AlgebraicGeometry.ComplexAndDivisorSituation.isAdmissibleBlowup_fittingIdealProdOfRanks` of
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/PerfectComplexAdmissibleBlowup.lean`, which
proves both and takes the source's centre. -/
theorem isAdmissibleBlowup_blowUpToBase_fittingIdealSheafProd (U : X.Opens) (s : Finset ℤ)
    (hft : ∀ i : ℤ, (fittingIdealSheaf.{u, u + 1} E i (k i)).IsFiniteType)
    (hdisj : ∀ i : ℤ,
      Disjoint (U : Set X) ((fittingIdealSheaf.{u, u + 1} E i (k i)).support : Set X)) :
    Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase (fittingIdealSheafProd E k s)) := by
  refine (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr
    ⟨fittingIdealSheafProd E k s, ?_, ?_, Iso.refl _, Category.id_comp _⟩
  · rw [finitePresentation_subschemeι_iff_isFiniteType]
    exact Stacks.Blowup.isFiniteType_prod s _ hft
  · exact Stacks.Blowup.disjoint_support_prod U s _ fun i _ => hdisj i

/-- **The Fitting ideals of Stacks tag 0ESQ become invertible, for the `fittingIdealSheaf`
encoding.** On the blowup of `X` in the product of the Fitting ideal sheaves of `E` over a finite
set of degrees, each factor pulls back to an effective Cartier divisor.

The inverse image of the whole product is the exceptional divisor, an effective Cartier divisor
by tag 02OS (2), and a factor of an effective Cartier divisor is one by tag 07ZV.

The degree is restricted to the finite set by `hi`, where the source asserts invertibility at
every degree, and the centre is again a product over a `Finset`. The tag's registration for this
clause is therefore on
`AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor_comap_fittingIdealOfRanks`
of `StacksFrontier/AlgebraicGeometry/Blowup/Transform/PerfectComplexAdmissibleBlowup.lean`, which
holds at every degree with no membership hypothesis and on the source's centre. -/
theorem isEffectiveCartierDivisor_comap_fittingIdealSheafProd (s : Finset ℤ) {i : ℤ}
    (hi : i ∈ s) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((fittingIdealSheaf.{u, u + 1} E i (k i)).comap
        (blowUpToBase (fittingIdealSheafProd E k s))) :=
  isEffectiveCartierDivisor_comap_of_mem_prod _ s _
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (fittingIdealSheafProd E k s)) hi

end AlgebraicGeometry

end

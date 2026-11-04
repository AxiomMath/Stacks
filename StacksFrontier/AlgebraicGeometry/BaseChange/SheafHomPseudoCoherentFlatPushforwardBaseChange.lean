module

public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFromGlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeSheafHomComparisonFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Case (2) of Stacks 08IE, corrected: base change along a flat morphism

Case (2) of [Stacks, Tag 08IE] asserts that for `f : X ⟶ S` quasi-compact and quasi-separated, a
pseudo-coherent `E ∈ D(𝒪_X)` and a bounded complex `𝒢^•` of quasi-coherent `𝒪_X`-modules flat
over `S`, the canonical map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

is an isomorphism for **every** base change `g : S' ⟶ S`. That is false: for `S = X = Spec ℤ/4`,
`f = id`, `E = (ℤ/2)~`, `𝒢^• = 𝒪_X` and `g : Spec ℤ/2 ⟶ Spec ℤ/4`, the self-injectivity of
`ℤ/4` gives `R𝓗om(E, 𝒪_X) = (ℤ/2)~[0]`, so the source is `(ℤ/2 ⊗^L_{ℤ/4} ℤ/2)~`, with
`H^{-1} = Tor_1^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2`, while the target `R𝓗om(L(g')^*E, 𝒪_{X'})` lies in
`D^{≥ 0}` because `L(g')^*E` lies in `D^{≤ 0}`. The failing step is the one of the proof of
[Stacks, Tag 0DJA] (3) that computes `L(g')^*` of the Hom complex `𝓗om^•(P, 𝒢^•)` out of a
bounded above complex `P` of finite free modules term by term: that Hom complex is a bounded
*below* complex of `S`-flat modules, which need not be K-flat. The counterexample is proved as
`not_forall_isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent` in the namespace
`Stacks.Examples.SheafHomCounterexample`, in
`StacksFrontier/Examples/BaseChange/SheafHomPseudoCoherentCounterexample.lean`.

This file proves the statement for base change along a **flat** `g`, which is what survives with
no change to the hypotheses on `E` and `𝒢^•`; there the flatness of the terms of `𝒢^•` over
`S` and its boundedness above are not needed, and only boundedness below of `𝒢^•` is used.

## Main results

* `AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_flat`: the corrected
  case (2).

## The proof

The canonical map is the derived base-change map of Stacks 08HY at `R𝓗om(E, 𝒢^•)`, followed by
`Rf'_*` of the map of Stacks 08I3 and of `R𝓗om(L(g')^*E, -)` applied to
`L(g')^*𝒢^• ⟶ (g')^*𝒢^•`. Each of the three is invertible:

* `R𝓗om(E, 𝒢^•)` has quasi-coherent cohomology by Stacks 0A6H (1), and `X` and `S'` are Tor
  independent over `S` because `g` is flat, so the first is Stacks 08IB;
* `g'` is flat, `E` is pseudo-coherent and `𝒢^•` is bounded below, so the second is
  Stacks 0GM7 (2);
* the derived pullback along the flat `g'` is computed term by term, which is the third.

## References

* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeSheafHomComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.SheafOfModules (derivedSheafHom)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-- **Stacks 08IE, case (2), corrected to base change along a flat morphism.** Let
`f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, let `E` be a
pseudo-coherent object of `D(𝒪_X)` and let `𝒢^•` be a complex of quasi-coherent `𝒪_X`-modules
vanishing in degrees below some `a`. For every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `g` **flat**, the canonical map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

of `AlgebraicGeometry.sheafHomFlatBaseChangeMap` is an isomorphism. The source's case (2), for a
bounded `𝒢^•` with terms flat over `S` and an *arbitrary* `g`, is false: see the module
documentation. -/
@[stacks 08IE "case (2), CORRECTED: as stated (E pseudo-coherent, 𝒢^• bounded with terms flat \
over S, arbitrary base change) it is false -- for S = X = Spec ℤ/4, f = id, E = (ℤ/2)~, \
𝒢^• = 𝒪_X and g : Spec ℤ/2 ⟶ Spec ℤ/4 the source has H^{-1} = Tor_1^{ℤ/4}(ℤ/2, ℤ/2) ≠ 0 \
while the target lies in D^{≥0}; the gap is in the proof of Tag 0DJA (3). Proved here for base \
change along a FLAT g, with E pseudo-coherent and 𝒢^• any complex of quasi-coherent modules \
bounded below (so in particular for 𝒢^• bounded with terms flat over S)"]
public theorem isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_flat
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f) [Flat g]
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (a : ℤ) (hGge : G.IsStrictlyGE a)
    (hGqcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent) :
    IsIso (sheafHomFlatBaseChangeMap f g f' g' sq E G) := by
  have hg' : AlgebraicGeometry.IsFlat g'.toLRSHom.toShHom :=
    Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isFlat_toShHom_of_isPullback hsq
  have hGa : (DerivedCategory.Q.obj G).IsGE a :=
    (DerivedCategory.isGE_Q_obj_iff G a).2 inferInstance
  have hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj
      (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G))).IsQuasicoherent :=
    derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X E (DerivedCategory.Q.obj G) hE
      ⟨⟨a, fun n hn => (DerivedCategory.Q.obj G).isZero_of_isGE a n hn⟩,
        fun n => isQuasicoherent_derived_homology G hGqcoh n⟩
  have h₁ : IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom sq
      (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G))) :=
    derivedBaseChangeIsIsoOnQuasicoherent g' f' f g hsq hqc hqs
      (torIndependent_of_flat_right f g) sq _ hK
  have h₂ :=
    Stacks.Cohomology.DerivedBaseChangeComparison.isIso_baseChangeSheafHomComparison_of_isFlat
      g'.toLRSHom.toShHom hg' E
      ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).2 hE) G
      (isLocallyBoundedBelow_of_plus _ ⟨a, hGa⟩)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁
    ((derivedPushforward f'.toLRSHom.toShHom).mapIso (@asIso _ _ _ _ _ h₂)).isIso_hom

end AlgebraicGeometry

end

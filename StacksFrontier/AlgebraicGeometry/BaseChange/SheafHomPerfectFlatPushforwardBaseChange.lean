module

public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorFlat
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDualizable
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedPullbackOfADual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change for `Rf_*R𝓗om(E, 𝒢^•)` with `E` perfect and `𝒢^•` flat over the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, let `E` be a perfect
object of `D(𝒪_X)` and let `𝒢^•` be a bounded above complex of quasi-coherent `𝒪_X`-modules
flat over `S`. Then the canonical map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

of `AlgebraicGeometry.sheafHomFlatBaseChangeMap` — with the ordinary pullback `(g')^*𝒢^•` on the
right — is an isomorphism. This is case (1) of [Stacks, Tag 08IE], with no hypothesis beyond
those of the source.

## Main results

* `AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_isPerfect`: **Stacks 08IE, case (1)**.

## The proof

The source reduces to Stacks 0DJ9 and Stacks 0DJA (2). Here the reduction is to Stacks 0A1D,
which this library proves unconditionally
(`AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`). The derived dual `E^∨` of a
perfect `E` is a left dual of `E` (Stacks 0FPC), so `R𝓗om(E, -) ≅ - ⊗^L E^∨` (Stacks 08DQ), and
the base-change comparison for `R𝓗om(E, 𝒢^•)` is identified with the base-change comparison for
`E^∨ ⊗^L 𝒢^•` by `map_braiding_dualTensorToSheafHom_comp_baseChangeSheafHomComparison` (in
`Stacks.Cohomology.DerivedInternalHomPullback`); the two base-change maps are then isomorphic,
and the second is invertible by Stacks 0A1D applied to the perfect, hence quasi-coherent, object
`E^∨`.

## Case (2) of the source is false as stated

Case (2) asserts the same conclusion for a pseudo-coherent `E` and a bounded `𝒢^•` with terms
flat over `S`. Take `S = X = Spec ℤ/4`, `f = id`, `E = (ℤ/2)~`, `𝒢^• = 𝒪_X` in degree zero and
`g : Spec ℤ/2 ⟶ Spec ℤ/4`. As `ℤ/4` is self-injective, `R𝓗om(E, 𝒪_X) = (ℤ/2)~[0]`, so the
source is `(ℤ/2 ⊗^L_{ℤ/4} ℤ/2)~`, whose `H^{-1}` is `Tor_1^{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2 ≠ 0`; the target
`R𝓗om(L(g')^*E, 𝒪_{X'})` lies in `D^{≥ 0}`. The step of the proof of Stacks 0DJA (3) that fails
is the computation of `L(g')^*` of `𝓗om^•(P, 𝒢^•)`, a bounded below complex of flat modules,
degreewise. See `AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_flat`
for the corrected statement and
`not_forall_isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent` (in
`Stacks.Examples.SheafHomCounterexample`) for the counterexample.

## References

* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeSheafHomComparison
  baseChangeTensorComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.SheafOfModules (derivedSheafHom derivedDual)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-- **Stacks 08IE, case (1).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism
of schemes, let `E` be a perfect object of `D(𝒪_X)` and let `𝒢^•` be a bounded above complex of
quasi-coherent `𝒪_X`-modules whose terms are flat over `S`. For every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the canonical map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

of `AlgebraicGeometry.sheafHomFlatBaseChangeMap`, with the **ordinary** pullback `(g')^*𝒢^•` on
the right as the source insists, is an isomorphism: the formation of `Rf_*R𝓗om(E, 𝒢^•)`
commutes with arbitrary base change. -/
@[stacks 08IE "case (1): E perfect, 𝒢^• bounded above with terms quasi-coherent and flat over \
S, f quasi-compact and quasi-separated, an arbitrary cartesian square; the canonical map of the \
source's proof, with the ORDINARY pullback (g')^*𝒢^• on the right, is an isomorphism. Case (2) \
is false as stated (see the module documentation); its corrected form is \
`isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_flat`"]
public theorem isIso_sheafHomFlatBaseChangeMap_of_isPerfect
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ)
    (hGminus : CochainComplex.minus X.Modules G)
    (hGqcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n)) :
    IsIso (sheafHomFlatBaseChangeMap f g f' g' sq E G) := by
  let pE : @ExactPairing _ _ (Stacks.Cohomology.DerivedInternalHomPullback.kflatMonoidal
      X.toRingedSpace) E (derivedDual X.sheaf E) :=
    Stacks.Cohomology.DerivedInternalHomPullback.kflatExactPairing X.toRingedSpace
      (Stacks.SheafOfModules.exactPairingDerivedDualCanonical X.sheaf E
        (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace E hE))
  have hEd : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (derivedDual X.sheaf E) :=
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace E hE
  have key := isIso_tensorFlatBaseChangeMap_of_isPullback f g f' g' hsq hqc hqs sq
    (derivedDual X.sheaf E)
    (fun n => PerfectApproximation.isQuasicoherent_homology_of_isPerfect X _ hEd n)
    G hGminus hGqcoh hGflat
  have k₂ := (isIso_derivedBaseChangeComp_iff_of_iso f g f' g' hsq.w _ _ _ _
    (Stacks.Cohomology.DerivedInternalHomPullback.isIso_kflatBraiding _ _ _)
    (Stacks.Cohomology.DerivedInternalHomPullback.isIso_kflatBraiding _ _ _)
    (Stacks.Cohomology.DerivedInternalHomPullback.map_kflatBraiding_comp_baseChangeComparison
      g'.toLRSHom.toShHom (derivedDual X.sheaf E) (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G))).1 key
  let := Stacks.Cohomology.DerivedInternalHomPullback.kflatPullbackExactPairing
    g'.toLRSHom.toShHom E (derivedDual X.sheaf E) pE
  exact (isIso_derivedBaseChangeComp_iff_of_iso f g f' g' hsq.w _ _ _ _
    (Stacks.Cohomology.DerivedInternalHomPullback.isIso_dualTensorToSheafHom _ _ _ _)
    (Stacks.Cohomology.DerivedInternalHomPullback.isIso_dualTensorToSheafHom _ _ _ _)
    (Stacks.Cohomology.DerivedInternalHomPullback.map_dualTensorToSheafHom_comp_baseChangeSheafHomComparison
      g'.toLRSHom.toShHom E (derivedDual X.sheaf E) (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj G))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app G))).1 k₂

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles

/-!
# A uniform lower bound for `E ⊗^L Lf^*N` when `E` is relatively perfect

Let `f : X ⟶ S` be a flat morphism of schemes, locally of finite presentation, with `X`
quasi-compact, and let `E ∈ D(𝒪_X)` be `S`-perfect (Stacks 0DI0). Then there is an integer `a`
such that for every `m` and every `N ∈ D^{≥ m}(𝒪_S)`,

`E ⊗^L_{𝒪_X} Lf^*N ∈ D^{≥ m + a}(𝒪_X)`.

This is the bound the proof of Stacks 0DJU uses in the form "`E` has tor amplitude in `[a, b]`
as a complex of `f^{-1}𝒪_S`-modules, so tensoring with `E` moves lower bounds by `a`".

## Main results

* `exists_hasTorAmplitude_of_locallyHasFiniteTorDimension_of_compactSpace` (in
  `Stacks.Cohomology.TorAmplitude`): on a quasi-compact ringed space, an object of locally finite
  Tor dimension has Tor amplitude in a single interval.
* `exists_isGE_derivedTensor_derivedPullback_of_isRelativelyPerfect` (in
  `Stacks.AlgebraicGeometry.RelativeDerivedHomDual`): the uniform lower bound above.

## Implementation notes

The proof is the source's. Relative perfectness gives, on an open covering of `X`, Tor amplitude
of `E` over `f^{-1}𝒪_S` in some interval; `X` being quasi-compact, finitely many members cover
`X`, so one interval `[a, b]` works on each, and Tor amplitude in a fixed interval is local
(`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`). After restriction of scalars
to `f^{-1}𝒪_S`, Stacks 08DE
(`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.derivedMixedTensorIso`) identifies
`E ⊗^L_{𝒪_X} Lf^*N` with `E ⊗^L_{f^{-1}𝒪_S} f^{-1}N`; the inverse image `f^{-1}` is exact, so
keeps `N` in degrees `≥ m`, and the Tor bound of `E` places the tensor product in degrees
`≥ a + m` (`Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE`).
Restriction of scalars reflects lower bounds, and the two canonical derived tensor products of
`𝒪_X` are identified by
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`. No bound above on `N` is
needed.

Everything is at the standard model of the derived categories, seated as in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore`, whose abbreviations `DStd`
and `pullStd` the statement uses.

## References

* [Stacks Project, Tag 0DJU](https://stacks.math.columbia.edu/tag/0DJU)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry StrictlyPerfect

universe u

namespace Stacks.Cohomology.TorAmplitude

section StandardModel

-- The model of `D(𝒪)` the Tor-amplitude predicates are read at in relative perfectness below.
attribute [local instance] HasDerivedCategory.standard

/-- **On a quasi-compact ringed space, locally finite Tor dimension is Tor amplitude in one
interval.** The covering witnessing local finiteness has a finite subcover, the finitely many
intervals lie in a single one, and Tor amplitude in a fixed interval is local on a covering. -/
theorem exists_hasTorAmplitude_of_locallyHasFiniteTorDimension_of_compactSpace
    (Z : RingedSpace.{u, u}) [CompactSpace Z.carrier] (E : DerivedCategory (OXMod.{u, u} Z))
    (h : Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension Z E) :
    ∃ a b : ℤ, Stacks.Cohomology.TorAmplitude.HasTorAmplitude Z E a b := by
  classical
  obtain ⟨J, W, hW, hTor⟩ := h
  choose a b hAmp using hTor
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set Z.carrier)).elim_finite_subcover
    (fun j => (W j : Set Z.carrier)) (fun j => (W j).isOpen) (by
      intro x _
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ iSup W by rw [hW]; trivial)
      exact Set.mem_iUnion.2 ⟨j, hj⟩)
  obtain ⟨a₀, ha₀⟩ := Finite.bddBelow_range (fun j : {j // j ∈ s} => a j.1)
  obtain ⟨b₀, hb₀⟩ := Finite.bddAbove_range (fun j : {j // j ∈ s} => b j.1)
  refine ⟨a₀, b₀, Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top Z E a₀ b₀
    (fun j : {j // j ∈ s} => W j.1) ?_ fun j => ?_⟩
  · refine top_unique fun x _ => Opens.mem_iSup.mpr ?_
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨j, hj⟩, hx⟩
  · exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (X := Z.restrict (W j.1).isOpenEmbedding)
      (hAmp j.1) (ha₀ ⟨j, rfl⟩) (hb₀ ⟨j, rfl⟩)

end StandardModel

end Stacks.Cohomology.TorAmplitude

namespace Stacks.AlgebraicGeometry.RelativeDerivedHomDual

open Stacks.SheafOfModules

-- As in `StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore`: the structure sheaf
-- is named `X.sheaf` by the schemes and through `sheafCompose` by the derived tensor product.
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

section StandardModel

-- The standard model, seated as in `RelativeDerivedHomDualCore`.
attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace Stacks.Cohomology.TorAmplitude in
/-- **A relatively perfect object moves lower bounds uniformly under `- ⊗^L Lf^*(-)`.** Let
`f : X ⟶ S` be flat and locally of finite presentation with `X` quasi-compact, and let `E` be
`S`-perfect. There is an integer `a` such that `E ⊗^L_{𝒪_X} Lf^*N ∈ D^{≥ m + a}(𝒪_X)` for every
`m` and every `N ∈ D^{≥ m}(𝒪_S)`; `a` is the lower end of a Tor-amplitude interval of `E` over
`f^{-1}𝒪_S`. -/
theorem exists_isGE_derivedTensor_derivedPullback_of_isRelativelyPerfect
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X]
    [Flat f] [LocallyOfFinitePresentation f] (E : DStd X) (hE : f.IsRelativelyPerfect E) :
    ∃ a : ℤ, ∀ (N : DStd S) (m : ℤ), N.IsGE m →
      (((derivedTensor X.sheaf).obj E).obj ((pullStd f).obj N)).IsGE (m + a) := by
  have : CompactSpace (RingedSpace.inverseImage S.toRingedSpace f.base).carrier :=
    inferInstanceAs (CompactSpace X)
  obtain ⟨a, b, hab⟩ := exists_hasTorAmplitude_of_locallyHasFiniteTorDimension_of_compactSpace
    (RingedSpace.inverseImage S.toRingedSpace f.base) _ hE.2
  refine ⟨a, fun N m hN => ?_⟩
  have hW := Stacks.Cohomology.DerivedInternalHomPullback.isGE_derivedPullback_auxHomG
    f.toLRSHom.toShHom N m hN
  have hK' := Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_hasTorAmplitude
    (RingedSpace.inverseImage S.toRingedSpace f.base) _ a b hab
  rw [Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_eq_site] at hK'
  have hamp := Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE
    (Stacks.Cohomology.TorAmplitude.derTensorSite
      (RingedSpace.inverseImage S.toRingedSpace f.base)) _ _ a m hK' hW
  have h1 : ((spaceDerivedTensorInverseImage f.toLRSHom.toShHom).obj (E, N)).IsGE (a + m) :=
    hamp
  have h2 : ((spaceDerivedTensorPullback f.toLRSHom.toShHom).obj (E, N)).IsGE (a + m) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((derivedMixedTensorIso f.toLRSHom.toShHom).app (E, N)).symm (a + m)
  have h3 : (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      X.toRingedSpace.sheaf).obj E).obj ((pullStd f).obj N)).IsGE (a + m) :=
    Stacks.Cohomology.DerivedInternalHomPullback.isGE_of_isGE_derivedRestrictTensor
      f.toLRSHom.toShHom _ _ h2
  rw [add_comm]
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso
      (Stacks.SheafOfModules.ringedSite X.sheaf)).app E).app _).symm (a + m)

end StandardModel

end Stacks.AlgebraicGeometry.RelativeDerivedHomDual

module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedTensorTorAmplitudeOver
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TorDimensionDirectImage

/-!
# The derived direct image of `E ⊗^L 𝒢` over a Noetherian base

Let `S` be a Noetherian scheme, `f : X ⟶ S` locally of finite type, `E` a perfect object of
`D(𝒪_X)` and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, whose support is
proper over `S`. [Stacks, Tag 0DJQ] asserts that `Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a perfect object of
`D(𝒪_S)`. The statement of
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforward.lean` carries the two residues of
[Stacks, Tag 08EV] and the Tor-dimension clause of its hypothesis as inputs; this file proves the
statement with none of them, as the source does: [Stacks, Tag 08EV] applied to
`E ⊗^L_{𝒪_X} 𝒢^•`.

## Main results

* `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforwardOX_of_properSupport`:
  [Stacks, Tag 08EV] at the `StrictlyPerfect.OXMod` spelling, with nothing granted.
* `Stacks.Cohomology.PerfectPushforward.hasFiniteTorDimension_derivedTensor`: the Tor-dimension
  clause of [Stacks, Tag 08EV] for `E ⊗^L_{𝒪_X} 𝒢^•`.
* `Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect`:
  [Stacks, Tag 0DJQ], with nothing granted.

## References

* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace StrictlyPerfect

namespace Stacks.Cohomology.PerfectPushforward

open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 08EV], at the `StrictlyPerfect.OXMod` spelling, with nothing granted.** Let `S`
be a Noetherian scheme and `f : X ⟶ S` a morphism locally of finite type. Let `K` be an object of
`D(𝒪_X)` which is bounded with coherent cohomology sheaves, whose cohomology sheaves are supported
in closed subsets proper over `S`, and which has finite Tor dimension as an object of
`D(f⁻¹𝒪_S)`. Then `Rf_*K` is a perfect object of `D(𝒪_S)`.

Here boundedness is stated as vanishing of the cohomology sheaves outside an interval, and the
support condition as containment of each support in a closed subset proper over `S`. -/
theorem isPerfect_derivedPushforwardOX_of_properSupport [IsNoetherian S] [LocallyOfFiniteType f]
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K))
    (hcoherent : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K).IsCoherent)
    (hproperSupport : ∀ i : ℤ, ∃ Z : Closeds X, IsProperOver f Z ∧
      SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj K) ⊆
        (Z : Set X))
    (hTor : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base)
      ((Scheme.Hom.derivedScalarRestriction f).obj K)) :
    RingedSpace.IsPerfect (X := S.toRingedSpace) ((derivedPushforwardOX f).obj K) := by
  obtain ⟨a, b, hab⟩ := hbounded
  have hGE : K.IsGE a := (DerivedCategory.isGE_iff K a).2 fun i hi =>
    hab i fun h => by have := h.1; omega
  have hLE : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun i hi =>
    hab i fun h => by have := h.2; omega
  exact
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp
      f K a b hGE hLE hcoherent (fun j => by
        obtain ⟨Z, hZ, hsub⟩ := hproperSupport j
        exact isProperOver_of_le f (Y := ⟨_, _⟩) (show _ ≤ Z from hsub) hZ) hTor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).obj
    M).Additive]
  [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
      (ComplexShape.up ℤ)]

/-- **The Tor-dimension clause of [Stacks, Tag 08EV] for `E ⊗^L_{𝒪_X} 𝒢`.** For `E` perfect and
`𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with support proper over `S`, the
object `E ⊗^L_{𝒪_X} 𝒢` has finite Tor dimension as an object of `D(f⁻¹𝒪_S)`.

The support of `𝒢` is compact, being proper over the quasi-compact `S`, so
`AlgebraicGeometry.exists_hasTorAmplitudeOver_derivedTensor` bounds the Tor amplitude of
`E ⊗^L 𝒢` over the base, stalk by stalk; this is finite Tor dimension over `f⁻¹𝒪_S` by
`AlgebraicGeometry.hasFiniteTorDimension_derivedScalarRestriction_iff`. -/
theorem hasFiniteTorDimension_derivedTensor [IsNoetherian S] [LocallyOfFiniteType f]
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : FlatProperSupportComplex f G) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base)
      ((Scheme.Hom.derivedScalarRestriction f).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) := by
  obtain ⟨c, d, hc, hd⟩ := hG.bounded
  obtain ⟨Z, hZ, hsub⟩ := hG.properSupport
  exact (hasFiniteTorDimension_derivedScalarRestriction_iff f _).2
    (exists_hasTorAmplitudeOver_derivedTensor f T E hE G c d hc hd hG.isFlatOver Z
      (isCompact_of_isProperOver f Z hZ) hsub)

/-- **[Stacks, Tag 0DJQ], with nothing granted.** Let `S` be a Noetherian scheme, `f : X ⟶ S` a
morphism locally of finite type, `E` a perfect object of `D(𝒪_X)` and `𝒢` a bounded complex of
coherent `𝒪_X`-modules, flat over `S`, whose support is proper over `S`. Then
`Rf_*(E ⊗^L_{𝒪_X} 𝒢)` is a perfect object of `D(𝒪_S)`, `Rf_*` being
`Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f` and `- ⊗^L_{𝒪_X} -` any
derived tensor product `T` of [Stacks, Tag 06YU].

As in the source, this is [Stacks, Tag 08EV] (`isPerfect_derivedPushforwardOX_of_properSupport`)
applied to `E ⊗^L_{𝒪_X} 𝒢`: boundedness is `exists_isZero_homology_derivedTensor`, coherence
`isCoherent_homology_derivedTensor`, the support clause `supp_homology_derivedTensor_subset` and
the Tor-dimension clause `hasFiniteTorDimension_derivedTensor`. -/
theorem isPerfect_derivedPushforward_derivedTensor_of_isPerfect [IsNoetherian S]
    [LocallyOfFiniteType f]
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : FlatProperSupportComplex f G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardOX f).obj ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) :=
  isPerfect_derivedPushforwardOX_of_properSupport f _
    (exists_isZero_homology_derivedTensor f T E G hE hG)
    (isCoherent_homology_derivedTensor f T E G hE hG)
    (fun i => by
      obtain ⟨Z, hZ, hsub⟩ := hG.properSupport
      exact ⟨Z, hZ, supp_homology_derivedTensor_subset X T E G hE _ hsub i⟩)
    (hasFiniteTorDimension_derivedTensor f T E G hE hG)

end Stacks.Cohomology.PerfectPushforward

end

module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject

/-!
# A single Tor-amplitude interval on a quasi-compact part of the source

Let `f : X ⟶ S` be a morphism of schemes and let `E` be an object of `D(𝒪_X)` which, read over
`f^{-1}𝒪_S`, locally has finite Tor dimension — the Tor conjunct of relative perfectness, Stacks
0DI0. By `locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover` of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject` that condition is an open
covering of `X` on each member of which one interval bounds the Tor amplitude of every stalk. The
interval is quantified *per member*, as part (3) of Stacks 08CG quantifies it.

This file collapses that covering over a quasi-compact part of `X`: on a compact subset finitely
many members suffice, and finitely many intervals are contained in one. The resulting bound is the
form every consumer of an affine chart needs, an affine open being quasi-compact.

## Main results

* `Scheme.Hom.exists_stalkTorAmplitude_of_locallyHasFiniteTorDimension_of_isCompact`: on a compact
  subset of `X` a single interval bounds the Tor amplitude of the stalk at every point, for every
  family of certificates pinned to the genuine tensor product of sheaves of modules.
* `Scheme.Hom.exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_isCompact`: the same, with the
  hypothesis read off a relatively perfect object. This is the forward extractor from Stacks 0DI0
  to a Tor-amplitude interval on a chart.
* `Scheme.Hom.exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_compactSpace`: the instance at a
  quasi-compact `X`, where the interval is uniform on the whole source.

## Implementation notes

The pinning `AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily` is what makes a forward
extraction possible at all. The `tensor` field of a
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` is free, and at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` the Tor condition
degenerates to boundedness of the cohomology, by
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff`. So an unpinned family
carries no information about Tor amplitude and nothing can be extracted from it.

Widening the interval is `hasTorAmplitudeCanonical_widen` below, kept `private`. Tor amplitude at
the canonical derived tensor product is by definition the vanishing of cohomology outside the
interval, so the proof is one term; the same term appears inline in
`AlgebraicGeometry.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension` of
`StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine`, and under other names in several other
files, none of them exported.

Compactness is taken as `IsCompact` on a subset rather than as `CompactSpace` on the source: an
affine open of `X` is a compact subset of `X`, and passing to it as a space would change the
ringed space the stalks are read on.

## References

* [Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.48.8 (09U9)](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Tor amplitude in an interval is inherited by every larger interval.** By Stacks 0654 Tor
amplitude in `[a, b]` at the canonical derived tensor product is representability by a complex of
flat modules concentrated in degrees `[a, b]`; such a complex is concentrated in every larger
interval.

Stated here for want of a public instance: every statement of it in this repository is `private`
to the file that needed it. -/
private theorem hasTorAmplitudeCanonical_widen {A : Type u} [CommRing A]
    {K : DerivedCategory (ModuleCat.{u} A)} {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (h : HasTorAmplitudeCanonical A K a b) : HasTorAmplitudeCanonical A K a' b' := by
  obtain ⟨P, hflat, hGE, hLE, e⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative A K a b).mp h
  let : P.IsStrictlyGE a := hGE
  let : P.IsStrictlyLE b := hLE
  exact (hasTorAmplitudeCanonical_iff_hasFlatRepresentative A K a' b').mpr
    ⟨P, hflat, P.isStrictlyGE_of_ge a' a ha, P.isStrictlyLE_of_le b b' hb, e⟩

/-- The stalk ring of the inverse-image ringed space of `f` is commutative, at every point.

The sibling module `StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject` seats
the same fact as a `local instance`, whose attribute does not reach this module, so it is
re-seated here under a name of its own. -/
local instance commRing_stalk_inverseImage_compact (y : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- **One Tor-amplitude interval on a compact subset of the source.** If `E` read over `f^{-1}𝒪_S`
locally has finite Tor dimension, for a family of certificates pinned to the genuine tensor
product of sheaves of modules, then on every compact subset `W` of `X` there is a single interval
`[a, b]` containing the Tor amplitude of the stalk at `y` of `E` read over `f^{-1}𝒪_S`, over the
stalk ring `(f^{-1}𝒪_S)_y`, for every `y ∈ W`.

The covering with a per-member interval is
`locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover`; compactness of `W`
extracts a finite subcover and the finitely many intervals are contained in one. -/
public theorem exists_stalkTorAmplitude_of_locallyHasFiniteTorDimension_of_isCompact
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) D
      ((derivedScalarRestriction f).obj E))
    (W : Set X) (hW : IsCompact W) :
    ∃ a b : ℤ, ∀ y : X, y ∈ W →
      HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y))
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory.obj
          ((derivedScalarRestriction f).obj E)) a b := by
  classical
  obtain ⟨J, U, hUtop, hbound⟩ :=
    (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f D hD E).mp hE
  choose a b hab using hbound
  have hc : W ⊆ ⋃ j, {y : X | y ∈ U j} := by
    intro y _
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show y ∈ iSup U by rw [hUtop]; trivial)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun j => {y : X | y ∈ U j})
    (fun j => (U j).isOpen) hc
  obtain ⟨a₀, ha₀⟩ := (t.finite_toSet.image a).bddBelow
  obtain ⟨b₀, hb₀⟩ := (t.finite_toSet.image b).bddAbove
  refine ⟨a₀, b₀, fun y hy => ?_⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (ht hy)
  obtain ⟨hjt, hyj⟩ := Set.mem_iUnion.mp hj
  have hlow : a₀ ≤ a j := ha₀ ⟨j, hjt, rfl⟩
  have hhigh : b j ≤ b₀ := hb₀ ⟨j, hjt, rfl⟩
  exact hasTorAmplitudeCanonical_widen hlow hhigh (hab j y hyj)

/-- **The forward extractor from relative perfectness to a Tor-amplitude interval on a chart.**
For a relatively perfect `E` and a family of certificates pinned to the genuine tensor product of
sheaves of modules, every compact subset `W` of `X` carries a single interval `[a, b]` containing
the Tor amplitude of the stalk at `y` of `E` read over `f^{-1}𝒪_S`, over `(f^{-1}𝒪_S)_y`, for
every `y ∈ W`.

An affine open is a compact subset, so this is the interval the source's proof of Stacks 0DJZ
reads off a chart; it is the direction opposite to
`locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_bound`. -/
public theorem exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_isCompact
    [Flat f] [LocallyOfFinitePresentation f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo D E)
    (W : Set X) (hW : IsCompact W) :
    ∃ a b : ℤ, ∀ y : X, y ∈ W →
      HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y))
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory.obj
          ((derivedScalarRestriction f).obj E)) a b :=
  exists_stalkTorAmplitude_of_locallyHasFiniteTorDimension_of_isCompact f D hD E hE.2 W hW

/-- **On a quasi-compact source the extracted interval is uniform.** The instance of the previous
statement at `W = Set.univ`, which is compact exactly when `X` is quasi-compact.

Together with
`locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_bound` this says that
over a quasi-compact source the Tor conjunct of relative perfectness is a *single* interval
bounding every stalk. -/
public theorem exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_compactSpace
    [Flat f] [LocallyOfFinitePresentation f] [CompactSpace X]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo D E) :
    ∃ a b : ℤ, ∀ y : X,
      HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y))
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory.obj
          ((derivedScalarRestriction f).obj E)) a b := by
  obtain ⟨a, b, hab⟩ := exists_stalkTorAmplitude_of_isPerfectRelativeTo_of_isCompact f D hD E hE
    Set.univ isCompact_univ
  exact ⟨a, b, fun y => hab y (Set.mem_univ y)⟩

end AlgebraicGeometry.Scheme.Hom

end

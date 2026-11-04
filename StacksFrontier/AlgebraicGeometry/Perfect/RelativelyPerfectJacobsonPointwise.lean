module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkPointwise
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibre

/-!
# Stacks 0DJZ with its Tor clause reduced to a pointwise bound over the base

Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, write `S = Spec R` and
`S₀ = Spec (R/I)`, let `f : X ⟶ S` be proper, flat and locally of finite presentation and put
`X₀ = S₀ ×_S X`. Stacks 0DJZ says that a pseudo-coherent object `E` of `D(𝒪_X)` whose derived
restriction to `X₀` is `S₀`-perfect is itself `S`-perfect.

The pseudo-coherence conjunct of the conclusion is the hypothesis on `E`, so the content is the
Tor conjunct. This module restates that residual as a **pointwise** demand: one interval `[a, b]`
containing, for every point `y` of `X`, the Tor amplitude over the local ring `𝒪_{S, f y}` of the
derived stalk of `E` at `y`. That is the shape the source's proof actually produces it in — its
interval `[a_i - d_i, b_i]` comes from the fibrewise criterion of Stacks 0DJH applied to
`R ⟶ Γ(X, U_i)` and is a Tor amplitude over a localisation of `R`, never over a stalk of
`f^{-1}𝒪_S` — and it is the shape in which commutative algebra can discharge it.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.PointwiseBaseStalkTorAmplitudeFromClosedFibre`: **the residual of
  Stacks 0DJZ as a pointwise Tor-amplitude bound over the local rings of the base.**

## Main results

* `Scheme.Hom.locallyFiniteTorDimensionFromClosedFibre_of_pointwiseBaseStalkBound`: the pointwise
  residual gives the Tor clause
  `AlgebraicGeometry.Scheme.Hom.LocallyFiniteTorDimensionFromClosedFibre`, at a family of
  certificates pinned to the genuine tensor product of sheaves of modules.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_closedFibre_of_pointwiseBaseStalkBound`:
  **Stacks 0DJZ carrying the pointwise residual.**
* `AlgebraicGeometry.Scheme.Hom.pointwiseBaseStalkTorAmplitudeFromClosedFibre_of_forall`: the
  pointwise residual demanded only at a pinned family on the closed fibre is the weaker demand.

## Why this residual rather than the chartwise one

`AlgebraicGeometry.Scheme.Hom.ChartwiseStalkTorAmplitudeFromClosedFibre` and
`AlgebraicGeometry.Scheme.Hom.GenuineChartwiseStalkTorAmplitudeFromClosedFibre` of the sibling
modules ask for an open covering of `X` and one interval per member, with the Tor amplitude read
over the stalk rings `(f^{-1}𝒪_S)_y` of the inverse-image sheaf of rings. Two things are changed
here.

* The covering is gone: the bound is asked at every point of `X` with one interval. This is not a
  strengthening of what the source proves — the source's covering is *finite*, so its intervals
  merge — and it removes the open-covering bookkeeping from the residual entirely.
* The coefficient ring is the local ring `𝒪_{S, f y}` of the base rather than the stalk
  `(f^{-1}𝒪_S)_y`. The two are equivalent demands, by
  `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff`, which is an
  iff; but only the base-local-ring side is the side every commutative-algebra input speaks.

Both changes are carried by
`Scheme.Hom.locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound`.

## Where the bound is proved

At every family `D₀` pinned to the tensor product of sheaves of modules, the conclusion of
`PointwiseBaseStalkTorAmplitudeFromClosedFibre` is
`AlgebraicGeometry.Scheme.Hom.exists_uniform_derivedStalk_bound_of_closedFibre`, and
Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`.

## Implementation notes

The family `D` on the base is pinned by
`AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily`, because the reduction it is fed to
is. The family `D₀` on the closed fibre is left free in
`PointwiseBaseStalkTorAmplitudeFromClosedFibre` and pinned only in
`pointwiseBaseStalkTorAmplitudeFromClosedFibre_of_forall`, which measures that the pinned demand
is the weaker one; this mirrors the split between
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreChartwise` and
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreGenuine`.

No `stacks` attribute is placed on anything here.

## References

* [Stacks Project, Lemma 37.71.3 (Tag 0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 15.85.9 (Tag 0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Lemma 25.5.1 (Tag 01HV)](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-! ### The residual, as a pointwise Tor-amplitude bound over the base -/

/-- **The residual of Stacks 0DJZ, as a pointwise Tor-amplitude bound over the local rings of the
base.** For every pseudo-coherent `E` whose derived restriction to the closed fibre is
`S₀`-perfect for the family `D₀`, and given that every point of `X` specializes into the closed
fibre: there is a *single* interval `[a, b]` containing, for every point `y` of `X`, the Tor
amplitude over the local ring `𝒪_{S, f y}` of the derived stalk of `E` at `y`, read over
`𝒪_{S, f y}` along the stalk map of `f`.

This is what the source's proof produces: its interval `[a_i - d_i, b_i]` is the conclusion of the
fibrewise criterion of Stacks 0DJH, a Tor amplitude over a localisation of `R`, and its covering
is finite so the finitely many intervals merge.

The specialization conclusion is written out as a hypothesis rather than derived from properness,
so that the predicate says exactly what remains once
`exists_specializes_mem_range_closedFibreToTotal` has been applied, as in
`AlgebraicGeometry.Scheme.Hom.LocallyFiniteTorDimensionFromClosedFibre`. -/
public def PointwiseBaseStalkTorAmplitudeFromClosedFibre [Flat f]
    [LocallyOfFinitePresentation f]
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding)) : Prop :=
  ∀ E : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
      (closedFibreToBase f I).IsPerfectRelativeTo D₀
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (closedFibreToTotal f I).toLRSHom.toShHom).obj E) →
        (∀ x : X, ∃ x₀ : X, x ⤳ x₀ ∧ x₀ ∈ Set.range (closedFibreToTotal f I).base) →
          ∃ a b : ℤ, ∀ y : X,
            HasTorAmplitudeCanonical
              (ToType ((Spec (CommRingCat.of R)).presheaf.stalk (f.base y)))
              ((ModuleCat.restrictScalars.{u}
                  ((SemilinearStalk.commStalkRingEquiv X.presheaf y).symm.toRingHom.comp
                    (f.stalkMap y).hom)).mapDerivedCategory.obj
                ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                  (structureSheafOfRings.{u} X.toRingedSpace) y).mapDerivedCategory.obj E)) a b

/-! ### The pointwise residual gives the Tor clause -/

/-- **The pointwise residual gives the Tor clause of Stacks 0DJZ.** At a family of certificates on
the base pinned to the genuine tensor product of sheaves of modules, the pointwise bound over the
local rings of the base is
`AlgebraicGeometry.Scheme.Hom.LocallyFiniteTorDimensionFromClosedFibre`.

The coefficient crossing at each point and the passage from a uniform stalk bound to local
finiteness of the Tor dimension are both
`locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound`. -/
public theorem locallyFiniteTorDimensionFromClosedFibre_of_pointwiseBaseStalkBound [Flat f]
    [LocallyOfFinitePresentation f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (h : PointwiseBaseStalkTorAmplitudeFromClosedFibre f I D₀) :
    LocallyFiniteTorDimensionFromClosedFibre f I D D₀ :=
  fun E hE hE₀ hspec =>
    locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound f D hD E
      (h E hE hE₀ hspec)

/-- **The pointwise residual demanded only at a pinned family on the closed fibre is the weaker
demand.** If the residual held at every family of certificates on the closed fibre, it would in
particular hold at the pinned ones.

This is the measurement that nothing is lost by proving only the pinned form, the analogue of
`AlgebraicGeometry.Scheme.Hom.genuineChartwiseStalkTorAmplitudeFromClosedFibre_of_forall`. -/
public theorem pointwiseBaseStalkTorAmplitudeFromClosedFibre_of_forall [Flat f]
    [LocallyOfFinitePresentation f]
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (h : ∀ D₀' : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
        RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
          ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
            (closedFibreToBase f I).base).restrict U.isOpenEmbedding),
      PointwiseBaseStalkTorAmplitudeFromClosedFibre f I D₀') :
    PointwiseBaseStalkTorAmplitudeFromClosedFibre f I D₀ :=
  h D₀

/-! ### Stacks 0DJZ carrying the pointwise residual -/

/-- **Stacks 0DJZ carrying the pointwise residual.** Let `R` be a ring, let `I` be an ideal
contained in the Jacobson radical of `R`, let `f : X ⟶ Spec R` be proper, flat and locally of
finite presentation, and let `X₀ = Spec (R/I) ×_{Spec R} X`. If `E` is a pseudo-coherent object of
`D(𝒪_X)` whose derived restriction to `X₀` is `Spec (R/I)`-perfect, then `E` is `Spec R`-perfect.

The pseudo-coherence conjunct of the conclusion is `hE`; the Tor conjunct is `hTor`, fed through
`locallyFiniteTorDimensionFromClosedFibre_of_pointwiseBaseStalkBound` and the specialization step,
which is where properness and the Jacobson-radical hypothesis are consumed.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`. -/
public theorem isPerfectRelativeTo_of_closedFibre_of_pointwiseBaseStalkBound [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hTor : PointwiseBaseStalkTorAmplitudeFromClosedFibre f I D₀)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo D E :=
  isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre f I hI D D₀
    (locallyFiniteTorDimensionFromClosedFibre_of_pointwiseBaseStalkBound f I D hD D₀ hTor) E hE hE₀

end AlgebraicGeometry.Scheme.Hom

end

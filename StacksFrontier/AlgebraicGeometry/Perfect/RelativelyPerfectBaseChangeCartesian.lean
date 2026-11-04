module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOverSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso

/-!
# Stacks 0DI5: base change of relatively perfect objects, along any cartesian square

Let `f : X ⟶ S` be flat and locally of finite presentation, let `g : S' ⟶ S` be any morphism of
schemes, set `X' = S' ×_S X` and let `g' : X' ⟶ X` be the projection. Stacks 0DI5 asserts that
if `K` in `D(𝒪_X)` is `S`-perfect, then `L(g')^*K` is `S'`-perfect.

Relative perfectness is `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, which is Stacks 0DI0
read at the genuine derived tensor product of Stacks 06YU: pseudo-coherence, together with local
finiteness of the Tor dimension over `f'^{-1}𝒪_{S'}`. The statement below holds for every
cartesian square `X' ⟶ X`, `X' ⟶ S'` over `f` and `g`, so `X'` need not be the chosen fibre
product, and no quasi-compactness is assumed anywhere.

## Main results

* `AlgebraicGeometry.hasTorAmplitudeCanonical_derivedStalk_derivedPullback_of_isPullback`: Stacks
  0C0V at a single point, for derived stalks. Across a Tor-independent cartesian square, a
  Tor-amplitude bound on the derived stalk of `E` at `g'(x')`, read over `𝒪_{S, f g'(x')}`, gives
  the same bound for the derived stalk of `L(g')^*E` at `x'`, read over `𝒪_{S', f'(x')}`.
* `AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_derivedPullback_of_isPullback`: **Stacks
  0DI5.**

## How the proof goes

This is the second proof in the source.

* Pseudo-coherence of `L(g')^*K` is Stacks 09U7, which is
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_derivedPullback`.
* For the Tor conjunct, Stacks 09U9 in the form (in the namespace `AlgebraicGeometry`)
  `Scheme.Hom.locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover` turns
  the hypothesis into an open covering `{U_i}` of `X` with one interval `[a_i, b_i]` on each member
  that bounds the Tor amplitude of every stalk in `U_i`. The preimages `g'^{-1}U_i` cover `X'`,
  and Stacks 0C0V, taken one point at a time, bounds the stalks of `L(g')^*K` on `g'^{-1}U_i` by
  the same interval. A flat morphism is Tor independent of every morphism with the same target,
  by `AlgebraicGeometry.torIndependent_of_flat_left`. The stalk rings of the inverse-image sheaf
  of rings are replaced by the local rings of the base by
  `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff`.

The pointwise form of Stacks 0C0V is needed because the interval is uniform only on each member
of the covering, not on all of `X`. It is
`AlgebraicGeometry.relativeStalkAmplitude_pullback_of_kFlat` at a K-flat representative of `E`,
moved to the derived stalks by `AlgebraicGeometry.relativeStalkComplexDerivedStalkIso` on both
sides.

## References

* [Stacks Project, Lemma 36.35.6 (Tag 0DI5)](https://stacks.math.columbia.edu/tag/0DI5)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.22.8 (Tag 0C0V)](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Lemma 20.47.3 (Tag 09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0C0V at one point, for derived stalks.** Let `g' : X' ⟶ X`, `f' : X' ⟶ S'`,
`f : X ⟶ S` and `g : S' ⟶ S` form a cartesian square with `f` and `g` Tor independent, and let
`E` be an object of `D(𝒪_X)`. If the derived stalk of `E` at `g'(x')`, read over `𝒪_{S, f g'(x')}`
along the stalk map of `f`, has Tor amplitude in `[a, b]`, then so does the derived stalk of
`L(g')^*E` at `x'`, read over `𝒪_{S', f'(x')}` along the stalk map of `f'`.

The proof is that of `AlgebraicGeometry.derivedPullback_hasTorAmplitudeOver` carried out at one
point: on a K-flat representative of `E` derived pullback is degreewise pullback, and the
transfer at the point is `AlgebraicGeometry.relativeStalkAmplitude_pullback_of_kFlat`. -/
public theorem hasTorAmplitudeCanonical_derivedStalk_derivedPullback_of_isPullback
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hpb : IsPullback g' f' f g) (htor : TorIndependent f g)
    (E : DerivedCategory X.Modules) (a b : ℤ) (x' : X')
    (hE : HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base (g'.base x'))))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X.presheaf (g'.base x')).symm.toRingHom.comp
            (f.stalkMap (g'.base x')).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) (g'.base x')).mapDerivedCategory.obj E))
      a b) :
    HasTorAmplitudeCanonical (ToType (S'.presheaf.stalk (f'.base x')))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X'.presheaf x').symm.toRingHom.comp
            (f'.stalkMap x').hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X'.toRingedSpace) x').mapDerivedCategory.obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            g'.toLRSHom.toShHom).obj E)))
      a b := by
  obtain ⟨K, q, hK, -, hq, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toSheafedSpace
      (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  let eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let eK' : DerivedCategory.Q.obj
      (((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g'.toLRSHom.toShHom).obj E :=
    (Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat g'.toLRSHom.toShHom K hK).symm ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g'.toLRSHom.toShHom).mapIso eK
  have hdown : HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (relativeStalkComplex f K (g'.base x'))) a b :=
    (hasTorAmplitudeCanonical_iff_lift _ _ a b).1
      (BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
        (relativeStalkComplexDerivedStalkIso f K E eK (g'.base x')).symm a b hE)
  have hup := relativeStalkAmplitude_pullback_of_kFlat g' f' f g hpb htor K a b x'
    (kFlat_modulesStalkFunctor (g'.base x') K hK) hdown
  exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    (relativeStalkComplexDerivedStalkIso f' _ _ eK' x') a b
    ((hasTorAmplitudeCanonical_iff_lift _ _ a b).2 hup)

namespace Scheme.Hom

/-- **Stacks 0DI5.** Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite
presentation, let `g : S' ⟶ S` be a morphism of schemes, and let `X'` with `g' : X' ⟶ X` and
`f' : X' ⟶ S'` be a fibre product `S' ×_S X`. If `K` in `D(𝒪_X)` is `S`-perfect, then `L(g')^*K`
is `S'`-perfect.

Relative perfectness is `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, Stacks 0DI0 at the
derived tensor product of Stacks 06YU, on both sides. `Flat f'` and
`LocallyOfFinitePresentation f'`, which the conclusion needs in order to be stated, are the base
changes of the corresponding properties of `f` along `g`. -/
@[stacks 0DI5]
public theorem isRelativelyPerfect_derivedPullback_of_isPullback
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (hpb : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
    haveI : LocallyOfFinitePresentation f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
    f.IsRelativelyPerfect K →
      f'.IsRelativelyPerfect
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          g'.toLRSHom.toShHom).obj K) := by
  have : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
  intro hK
  refine ⟨isPseudoCoherent_derivedPullback g' K hK.1, ?_⟩
  obtain ⟨I, U, hUtop, hbnd⟩ :=
    (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f _
      (isGenuineRelativeTensorFamily_canonical f) K).mp hK.2
  refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f' _
      (isGenuineRelativeTensorFamily_canonical f') _).mpr
    ⟨I, fun k => g' ⁻¹ᵁ (U k : X.Opens), ?_, fun k => ?_⟩
  · refine le_antisymm le_top fun z _ => ?_
    have hz : g'.base z ∈ iSup U := by rw [hUtop]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩
  · obtain ⟨a, b, hab⟩ := hbnd k
    refine ⟨a, b, fun z hz => ?_⟩
    exact (hasTorAmplitudeCanonical_derivedStalk_relative_iff f' z _ a b).mpr
      (hasTorAmplitudeCanonical_derivedStalk_derivedPullback_of_isPullback hpb
        (torIndependent_of_flat_left f g) K a b z
        ((hasTorAmplitudeCanonical_derivedStalk_relative_iff f (g'.base z) K a b).mp
          (hab (g'.base z) hz)))

end Scheme.Hom

end AlgebraicGeometry

end

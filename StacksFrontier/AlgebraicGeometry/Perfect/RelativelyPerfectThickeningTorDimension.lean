module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonAffineStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout

/-!
# Stacks 0DJY: relative perfectness across a finite-order thickening of the base

Consider a cartesian diagram of schemes with `i : X ⟶ X'`, `f : X ⟶ Y`, `f' : X' ⟶ Y'` and
`j : Y ⟶ Y'`, in which `f'` is flat and locally of finite presentation and `j` is a finite-order
thickening. Stacks 0DJY asserts that an object `E'` of `D(𝒪_{X'})` whose derived pullback
`E = Li^*E'` is `Y`-perfect is itself `Y'`-perfect.

Relative perfectness (Stacks 0DI0) is the conjunction of pseudo-coherence and locally finite Tor
dimension over `f^{-1}𝒪_Y`. This file supplies the Tor-dimension conjunct and assembles the tag.

## Main results

* `Stacks.Thickenings.locallyHasFiniteTorDimension_of_isPullback_of_isFiniteOrderThickening`: the
  Tor-dimension conjunct of the conclusion of Stacks 0DJY.
* `Stacks.Thickenings.isPerfectRelativeTo_of_isPullback_of_isFiniteOrderThickening`: Stacks 0DJY
  at any families of certificates pinned to the genuine tensor product of sheaves of modules.
* `Stacks.Thickenings.isRelativelyPerfect_of_isPullback_of_isFiniteOrderThickening`: **Stacks
  0DJY** with both sides read at `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, which is
  Stacks 0DI0 at the canonical derived tensor products.

## How the Tor conjunct is assembled

Both conjuncts of relative perfectness are conditions on an open covering, so the proof is a
transport of a covering together with a pointwise transfer.

The *pointwise* transfer is
`Stacks.Thickenings.hasTorAmplitudeCanonical_derivedStalk_of_isPullback` of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening`: at a point `x` of `X`, a
Tor-amplitude bound for the derived stalk of `Li^*E'` over `𝒪_{Y, f x}` gives the same bound for
the derived stalk of `E'` over `𝒪_{Y', j (f x)}`. It is stated over the local rings of the base,
which is not the side the Tor conjunct is read on; the two sides are matched by

* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff`, which
  replaces the stalk ring `(f^{-1}𝒪_S)_x` of the inverse-image sheaf of rings by the local ring
  `𝒪_{S, f x}` of the base, and
* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_iff_structureSheafOfRings`,
  which crosses between the derived stalk over `𝒪_{X, x}` and the derived stalk over the
  `RingCat`-valued stalk of the structure sheaf.

Both are equivalences, so nothing is weakened in passing, and the `AlgebraicGeometry.Scheme.Hom`
declaration
`locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover`
— Stacks 09U9 for the Tor conjunct — is used in both directions: to read the hypothesis as a
covering of `X` with a uniform interval on each member, and to build the conclusion from a
covering of `X'`.

The *covering* is transported by `Stacks.Thickenings.IsThickening.opensCongr`. The base change `i`
of `j` is a finite-order thickening by Stacks 09ZU, hence a thickening, hence a homeomorphism on
underlying spaces, so the opens of `X` and of `X'` correspond and a covering of `X` becomes one of
`X'` with the same index set and the same intervals. This is what removes any need for `X` to be
quasi-compact: the interval has to be uniform only on each member of the covering.

The base point of the pointwise transfer is written `j (f x)` and not `f' (i x)`: those are equal
only propositionally. `hasTorAmplitudeCanonical_stalkCongr_iff` below moves a Tor-amplitude bound
between the two spellings; the comparison between the two stalks is a ring isomorphism, and
restricting scalars along a ring isomorphism does not move canonical Tor amplitude.

## Implementation notes

The pseudo-coherence conjunct is proved one module upstream, by
`Stacks.Thickenings.isPseudoCoherent_of_isPullback_of_isFiniteOrderThickening`, which needs
nothing of the square beyond that `i` is a finite-order thickening; it is applied below rather
than restated. That upstream declaration is registered for the pseudo-coherence
conjunct alone; the full statement, both conjuncts, is registered here on
`Stacks.Thickenings.isRelativelyPerfect_of_isPullback_of_isFiniteOrderThickening`.

`Flat f` and `LocallyOfFinitePresentation f` are not hypotheses: they are the base changes along
`j` of the corresponding properties of `f'`, by
`CategoryTheory.MorphismProperty.of_isPullback`. They are needed only to *state* that `Li^*E'` is
`Y`-perfect, since `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` takes them as instance
arguments, and they appear in the statements below as the instances that `haveI` seats.

## References

* [Stacks Project, Lemma 37.71.4 (Tag 0DJY)](https://stacks.math.columbia.edu/tag/0DJY)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 37.71.2 (Tag 0DJX)](https://stacks.math.columbia.edu/tag/0DJX)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Lemma 37.2.6 (Tag 09ZU)](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect StacksDraft.TorAmplitude

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Thickenings

/-! ### A Tor-amplitude bound at the other spelling of one point -/

/-- **Canonical Tor amplitude does not see the comparison of the stalks at two equal points.**
For points `p = q` of a scheme `W` and a ring map `σ` out of the stalk at `q`, an object read over
the stalk at `p` along `σ` precomposed with `TopCat.Presheaf.stalkCongr` has Tor amplitude in
`[a, b]` exactly when it has Tor amplitude in `[a, b]` read over the stalk at `q` along `σ`.

The comparison is a ring isomorphism, and restriction of scalars along a ring isomorphism does not
move canonical Tor amplitude, by
`AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff`; the two
restrictions of scalars are composed into one by `PseudoCoherence.restrictScalarsCompObjIso`. -/
private theorem hasTorAmplitudeCanonical_stalkCongr_iff {W : Scheme.{u}} {p q : W} (hpq : p = q)
    {B : Type u} [CommRing B] (σ : ToType (W.presheaf.stalk q) →+* B)
    (K : DerivedCategory (ModuleCat.{u} B)) (a b : ℤ) :
    HasTorAmplitudeCanonical (W.presheaf.stalk p)
        ((ModuleCat.restrictScalars
            (σ.comp (W.presheaf.stalkCongr (Inseparable.of_eq hpq)).hom.hom)
          ).mapDerivedCategory.obj K) a b ↔
      HasTorAmplitudeCanonical (W.presheaf.stalk q)
        ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj K) a b := by
  let e := RingEquiv.ofBijective _ ((ConcreteCategory.isIso_iff_bijective
    (W.presheaf.stalkCongr (Inseparable.of_eq hpq)).hom).mp inferInstance)
  have ec := PseudoCoherence.restrictScalarsCompObjIso e.toRingHom σ K
  refine Iff.trans ⟨fun h =>
      AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ec.symm a b h,
    fun h =>
      AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ec a b h⟩ ?_
  exact AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff
    e _ a b

/-! ### Transporting an open covering along a thickening -/

/-- A point of `X` lies in an open `V` exactly when its image lies in the matching open of `X'`.
Both directions are `Stacks.Thickenings.IsThickening.preimage_opensCongr`, membership in a
preimage being membership of the image. -/
private theorem mem_opensCongr_iff {X X' : Scheme.{u}} {i : X ⟶ X'} (hi : IsThickening i)
    (V : X.Opens) (y : X) : i.base y ∈ hi.opensCongr V ↔ y ∈ V :=
  SetLike.ext_iff.mp (hi.preimage_opensCongr V) y

/-- **An open covering of `X` becomes one of `X'` across a thickening.** The opens of the two
schemes correspond by an order isomorphism, which preserves suprema and the top element. -/
private theorem iSup_opensCongr_eq_top {X X' : Scheme.{u}} {i : X ⟶ X'} (hi : IsThickening i)
    {I : Type*} (V : I → X.Opens) (hV : iSup V = ⊤) :
    ⨆ k, hi.opensCongr (V k) = ⊤ := by
  rw [← hi.opensCongr.map_iSup, hV, hi.opensCongr.map_top]

/-! ### The Tor-dimension conjunct of Stacks 0DJY -/

open AlgebraicGeometry.Scheme.Hom in
/-- **The Tor-dimension conjunct of Stacks 0DJY.** In a cartesian diagram of schemes with
`i : X ⟶ X'`, `f : X ⟶ Y`, `f' : X' ⟶ Y'` and `j : Y ⟶ Y'`, with `f'` flat and `j` a finite-order
thickening, let `E'` be an object of `D(𝒪_{X'})`. If `Li^*E'`, read over `f^{-1}𝒪_Y`, locally has
finite Tor dimension, then so does `E'` read over `f'^{-1}𝒪_{Y'}`.

Both families of certificates are pinned to the genuine tensor product of sheaves of modules, as
in Stacks 0DI0.

The covering is transported along the homeomorphism of a thickening and the bound at each point is
`Stacks.Thickenings.hasTorAmplitudeCanonical_derivedStalk_of_isPullback`; see the "How the Tor
conjunct is assembled" section of this module. -/
public theorem locallyHasFiniteTorDimension_of_isPullback_of_isFiniteOrderThickening
    {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) (hj : IsFiniteOrderThickening j) [Flat f']
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage Y.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage Y.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily f D)
    (D' : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage Y'.toRingedSpace f'.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage Y'.toRingedSpace f'.base).restrict U.isOpenEmbedding))
    (hD' : AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily f' D')
    (E' : DerivedCategory (OXMod.{u, u} X'.toRingedSpace))
    (hE : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage Y.toRingedSpace f.base) D
      ((AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction f).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          i.toLRSHom.toShHom).obj E'))) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage Y'.toRingedSpace f'.base) D'
      ((AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction f').obj E') := by
  have hthick : IsThickening i := (isFiniteOrderThickening_of_isPullback hpb hj).isThickening
  have hpt : ∀ z : X, j.base (f.base z) = f'.base (i.base z) := fun z => by
    simpa using (congrArg (fun φ : X ⟶ Y' => φ.base z) hpb.w).symm
  obtain ⟨I, U, hUtop, hbnd⟩ :=
    (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f D hD _).mp hE
  refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover
    f' D' hD' E').mpr ⟨I, fun k => hthick.opensCongr (U k), ?_, fun k => ?_⟩
  · exact iSup_opensCongr_eq_top hthick U hUtop
  · obtain ⟨a, b, hab⟩ := hbnd k
    refine ⟨a, b, fun z hz => ?_⟩
    obtain ⟨y, rfl⟩ := hthick.2 z
    have h₁ := (hasTorAmplitudeCanonical_derivedStalk_relative_iff f y _ a b).mp
      (hab y ((mem_opensCongr_iff hthick (U k) y).mp hz))
    have h₂ :=
      (hasTorAmplitudeCanonical_derivedStalk_iff_structureSheafOfRings f y _ a b).mpr h₁
    have h₃ := hasTorAmplitudeCanonical_derivedStalk_of_isPullback hpb hj y (hpt y) E' a b h₂
    have h₄ := (hasTorAmplitudeCanonical_stalkCongr_iff (hpt y)
      (f'.stalkMap (i.base y)).hom _ a b).mp (by simpa only [CommRingCat.hom_comp] using h₃)
    exact (hasTorAmplitudeCanonical_derivedStalk_relative_iff f' (i.base y) E' a b).mpr
      ((hasTorAmplitudeCanonical_derivedStalk_iff_structureSheafOfRings
        f' (i.base y) E' a b).mp h₄)

/-! ### Stacks 0DJY -/

/-- **Stacks 0DJY.** Consider a cartesian diagram of schemes with `i : X ⟶ X'`, `f : X ⟶ Y`,
`f' : X' ⟶ Y'` and `j : Y ⟶ Y'`, in which `f'` is flat and locally of finite presentation and `j`
is a finite-order thickening. Let `E'` be an object of `D(𝒪_{X'})`. If `E = Li^*E'` is
`Y`-perfect, then `E'` is `Y'`-perfect.

Relative perfectness is read at families of certified derived tensor products on the open
subspaces of the inverse-image ringed spaces, pinned to the tensor product of sheaves of modules,
which is the tensor product of the source's definition.

`Flat f` and `LocallyOfFinitePresentation f`, which the hypothesis needs in order to be stated,
are the base changes of the corresponding properties of `f'` along `j`. -/
public theorem isPerfectRelativeTo_of_isPullback_of_isFiniteOrderThickening
    {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) (hj : IsFiniteOrderThickening j)
    [Flat f'] [LocallyOfFinitePresentation f']
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage Y.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage Y.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily f D)
    (D' : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage Y'.toRingedSpace f'.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage Y'.toRingedSpace f'.base).restrict U.isOpenEmbedding))
    (hD' : AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily f' D')
    (E' : DerivedCategory (OXMod.{u, u} X'.toRingedSpace)) :
    haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
    haveI : LocallyOfFinitePresentation f :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
    f.IsPerfectRelativeTo D
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          i.toLRSHom.toShHom).obj E') →
      f'.IsPerfectRelativeTo D' E' := fun hE =>
  ⟨isPseudoCoherent_of_isPullback_of_isFiniteOrderThickening i f f' j hpb hj E' hE.1,
    locallyHasFiniteTorDimension_of_isPullback_of_isFiniteOrderThickening hpb hj D hD D' hD' E'
      hE.2⟩

/-- **Stacks 0DJY at the canonical derived tensor products.** Consider a cartesian diagram of
schemes with `i : X ⟶ X'`, `f : X ⟶ Y`, `f' : X' ⟶ Y'` and `j : Y ⟶ Y'`, in which `f'` is flat and
locally of finite presentation and `j` is a finite-order thickening. Let `E'` be an object of
`D(𝒪_{X'})`. If `E = Li^*E'` is `Y`-perfect, then `E'` is `Y'`-perfect, relative perfectness being
`AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect` — Stacks 0DI0 read at the canonical derived
tensor products — on both sides. -/
@[stacks 0DJY]
public theorem isRelativelyPerfect_of_isPullback_of_isFiniteOrderThickening
    {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) (hj : IsFiniteOrderThickening j)
    [Flat f'] [LocallyOfFinitePresentation f']
    (E' : DerivedCategory (OXMod.{u, u} X'.toRingedSpace)) :
    haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
    haveI : LocallyOfFinitePresentation f :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
    f.IsRelativelyPerfect
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          i.toLRSHom.toShHom).obj E') →
      f'.IsRelativelyPerfect E' := fun hE =>
  isPerfectRelativeTo_of_isPullback_of_isFiniteOrderThickening hpb hj _
    (AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical f) _
    (AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical f') E' hE

end Stacks.Thickenings

end

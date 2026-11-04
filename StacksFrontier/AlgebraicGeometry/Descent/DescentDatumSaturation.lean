module

public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The subset of a chart cut out by a descent datum descends

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of a scheme `S`, let
`h : yoneda.obj a ⟶ Y` be a chart of its target, let `q : c ⟶ a` be a surjective étale morphism
of the site, and let `(m, r)` present a presheaf `A` as the base change of `f` along
`yoneda.map q ≫ h`. When `r` is relatively representable it has a *range* in the underlying
scheme of `c`, the image of the representing object of its base change along the identity. This
file proves that that subset descends to `a` as a *subset*: it is saturated for `q`, and its
image in `a` is closed, respectively locally closed, as soon as it is.

This is the part of the effective descent of Stacks 03I2 which is free of any quasi-coherent
input, and it is proved for an arbitrary descent datum, with no hypothesis on the property
carried by `r`. For an open immersion the descended subset determines the descended object; a
closed subscheme is instead determined by a quasi-coherent ideal, whose descent is Stacks 0247.

## Main results

* `IsOpenMap.isClosed_image_of_preimage_image_eq` and
  `IsOpenMap.isLocallyClosed_image_of_preimage_image_eq`: a continuous open surjection is a
  topological quotient map, so the image of a saturated closed set is closed; and, because a
  saturated set has saturated coborder, the image of a saturated locally closed set is locally
  closed.
* `AlgebraicGeometry.Space.preimage_image_range_eq_range`: **the range of a descent datum is
  saturated.** The preimage under the chart of the image of the range is the range again. No
  property of `r` is used: only that it is relatively representable, and that its two pullbacks
  to `c ×[a] c` have the same range, which is
  `AlgebraicGeometry.Space.preimage_range_eq_preimage_range`.
* `AlgebraicGeometry.Space.exists_isClosed_preimage_eq_range_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.exists_isLocallyClosed_preimage_eq_range_of_isImmersion`: **the
  underlying set of a closed-immersion, respectively immersion, descent datum descends.** There
  is a closed, respectively locally closed, subset of the base whose preimage under the chart is
  the range of the datum.

## Implementation notes

The saturation of the range combines `AlgebraicGeometry.Space.preimage_range_eq_preimage_range`
with `AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback`; the closed and locally closed
conclusions are then read off by point-set topology, through `IsOpenMap.isQuotientMap` and
`coborder_preimage`. `AlgebraicGeometry.Space.preimage_image_range_eq_range` needs the chart to be
surjective, and uses it only to cancel `pullback.snd q q` against its own preimage; étaleness
enters only through the openness of the chart in the two closed and locally closed statements.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Images of saturated sets under a continuous open surjection -/

/-- The image of a *saturated* closed set under a continuous open surjection is closed. Such a
map is a topological quotient map, so a set of the target is closed exactly when its preimage
is, and the preimage of the image of a saturated set is the set itself. -/
@[ega "II 8.11.1" "open case"]
theorem IsOpenMap.isClosed_image_of_preimage_image_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {φ : X → Y} (hopen : IsOpenMap φ) (hcont : Continuous φ)
    (hsurj : Function.Surjective φ) {T : Set X} (hsat : φ ⁻¹' (φ '' T) = T)
    (hT : IsClosed T) : IsClosed (φ '' T) :=
  (hopen.isQuotientMap hcont hsurj).isCoinducing.isClosed_preimage.1 (by rw [hsat]; exact hT)

/-- The image of a *saturated* locally closed set under a continuous open surjection is locally
closed. A set is locally closed exactly when its coborder is open, and the coborder of a
preimage is the preimage of the coborder for an open continuous map, so the coborder of a
saturated set is again saturated; quotient maps then transfer its openness. -/
theorem IsOpenMap.isLocallyClosed_image_of_preimage_image_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {φ : X → Y} (hopen : IsOpenMap φ) (hcont : Continuous φ)
    (hsurj : Function.Surjective φ) {T : Set X} (hsat : φ ⁻¹' (φ '' T) = T)
    (hT : IsLocallyClosed T) : IsLocallyClosed (φ '' T) := by
  rw [isLocallyClosed_iff_isOpen_coborder,
    ← (hopen.isQuotientMap hcont hsurj).isCoinducing.isOpen_preimage,
    ← coborder_preimage hopen hcont, hsat]
  exact hT.isOpen_coborder

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace Space

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-- **The subset of the chart cut out by a descent datum is saturated.** Let `(m, r)` present `A`
as the base change of `f` along `yoneda.map q ≫ h`, with `r` relatively representable and `q`
surjective on underlying schemes. Then the preimage under `q` of the image of the range of the
datum is the range again.

The two pullbacks of the datum to `c ×[a] c` have the same range, by
`AlgebraicGeometry.Space.preimage_range_eq_preimage_range`; the preimage under `q` of the image
of a set is the image under one projection of the preimage under the other, by
`AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback`; and the projection used to take the
image is surjective, being a base change of `q`. No property of `r` is involved. -/
theorem preimage_image_range_eq_range (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hrep : yoneda.relativelyRepresentable r)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q)) :
    ((BigFppfOver.toScheme B S hS).map q).base ⁻¹'
        (((BigFppfOver.toScheme B S hS).map q).base ''
          Set.range ((BigFppfOver.toScheme B S hS).map
            (hrep.snd (𝟙 (yoneda.obj c)))).base) =
      Set.range ((BigFppfOver.toScheme B S hS).map (hrep.snd (𝟙 (yoneda.obj c)))).base := by
  have sqD : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst q q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd q q))
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map q) :=
    (IsPullback.of_hasPullback q q).map (BigFppfOver.toScheme B S hS)
  have hsnd : Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd q q)) :=
    MorphismProperty.of_isPullback sqD hqs
  rw [← Scheme.image_preimage_eq_of_isPullback sqD,
    preimage_range_eq_preimage_range sq hrep, Set.image_preimage_eq _ hsnd.surj]

/-- **The underlying closed set of a closed-immersion descent datum descends.** Let `(m, r)`
present `A` as the base change of `f` along `yoneda.map q ≫ h`, with `q` surjective étale and `r`
relatively representable with closed-immersion represented base changes. Then there is a closed
subset of the underlying scheme of `a` whose preimage under `q` is the range of the datum. -/
theorem exists_isClosed_preimage_eq_range_of_isClosedImmersion
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    (hr : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj a), IsClosed V ∧
      ((BigFppfOver.toScheme B S hS).map q).base ⁻¹' V =
        Set.range ((BigFppfOver.toScheme B S hS).map
          (hr.rep.snd (𝟙 (yoneda.obj c)))).base := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hr.rep.snd (𝟙 (yoneda.obj c)))) :=
    hr.property_snd (𝟙 (yoneda.obj c))
  have := hqe
  have hsat := preimage_image_range_eq_range sq hr.rep hqs
  refine ⟨_, ?_, hsat⟩
  exact ((BigFppfOver.toScheme B S hS).map q).isOpenMap.isClosed_image_of_preimage_image_eq
    ((BigFppfOver.toScheme B S hS).map q).continuous hqs.surj hsat
    (((BigFppfOver.toScheme B S hS).map
      (hr.rep.snd (𝟙 (yoneda.obj c)))).isClosedEmbedding).isClosed_range

/-- **The underlying locally closed set of an immersion descent datum descends.** Let `(m, r)`
present `A` as the base change of `f` along `yoneda.map q ≫ h`, with `q` surjective étale and `r`
relatively representable with immersion represented base changes. Then there is a locally closed
subset of the underlying scheme of `a` whose preimage under `q` is the range of the datum. -/
theorem exists_isLocallyClosed_preimage_eq_range_of_isImmersion
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    (hr : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj a), IsLocallyClosed V ∧
      ((BigFppfOver.toScheme B S hS).map q).base ⁻¹' V =
        Set.range ((BigFppfOver.toScheme B S hS).map
          (hr.rep.snd (𝟙 (yoneda.obj c)))).base := by
  have himm : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hr.rep.snd (𝟙 (yoneda.obj c)))) :=
    hr.property_snd (𝟙 (yoneda.obj c))
  have := hqe
  have hsat := preimage_image_range_eq_range sq hr.rep hqs
  refine ⟨_, ?_, hsat⟩
  exact ((BigFppfOver.toScheme B S hS).map q).isOpenMap.isLocallyClosed_image_of_preimage_image_eq
    ((BigFppfOver.toScheme B S hS).map q).continuous hqs.surj hsat
    (((BigFppfOver.toScheme B S hS).map
      (hr.rep.snd (𝟙 (yoneda.obj c)))).isLocallyClosed_range)

end Space

end AlgebraicGeometry

end

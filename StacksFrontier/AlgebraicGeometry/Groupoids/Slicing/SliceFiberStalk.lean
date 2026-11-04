module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.RestrictedArrowStalk
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceFiberPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceStalkChart

/-!
# The slice, its point, and the local ring of the fibre of the base change

This file supplies the two ingredients clause (4) of Stacks 0461 needs beyond the keystone of
`SliceBaseChangeChart.lean`.

## The point of the slice

`exists_slice_of_mem_primeIdealOf` produces the slice `Spec(Γ(Y, V) ⧸ (b)) ⟶ Y` of an affine open
`V` cut by a section `b` vanishing at a point `y`, together with a point of the slice lying over
`y` — but only as an existential, and it also forgets which morphism the slice map is. Both are
needed: the morphism has to be the specific one the keystone computes with, and the point has to
be available as data, because the point of the fibre product `U' ×_{g,U,t} R` at which clause (4)
is asserted is produced from it.

`AlgebraicGeometry.IsAffineOpen.slicePoint` is that point, constructed rather than chosen: it is
the image `𝔭 ⧸ (b)` of the prime of `y` under the quotient map, which is prime precisely because
`b` lies in `𝔭`. Its image in `Y` is `y`, which is
`AlgebraicGeometry.IsAffineOpen.sliceMap_slicePoint`.

## The local ring of the fibre

Let `t : X ⟶ W` and `f : X ⟶ Y`, let `gL : Z ⟶ W`, and write `h = pr₂ ≫ f` for the composite
`Z ×_{gL, W, t} X ⟶ Y`. By `SliceFiberPullback.lean` the fibre `h⁻¹(y)` is the base change of
`gL` along `ι ≫ t`, where `ι : f⁻¹(y) ⟶ X` is the embedding of the fibre of `f`. That base change
is of exactly the shape `AlgebraicGeometry.quotientStalkEquivStalkPullbackSndOfSpan` computes, so
the local ring of `h⁻¹(y)` is the local ring of `f⁻¹(y)` modulo a single germ:

```
𝒪_{h⁻¹(y), ·} ≅ 𝒪_{f⁻¹(y), ·} ⧸ (germ of the cutting section).
```

For the slicing lemma `f` is the source map and `t` the target map of a groupoid scheme, so
`f⁻¹(y) = F_u` is the source fibre and the cutting section is the image `t(b)` of the slicing
parameter; this is the identification of the local ring of `h⁻¹(u)` that clause (4) asserts
Cohen-Macaulayness of.

## Main definitions

* `AlgebraicGeometry.IsAffineOpen.slicePoint`: the point of a slice over the point it is cut at.
* `AlgebraicGeometry.quotientStalkEquivFiberStalkPullbackSndComp`: the local ring of the fibre of
  `pr₂ ≫ f`, as a quotient of the local ring of the fibre of `f`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.sliceMap_slicePoint`: the point of the slice lies over the point
  the slice is cut at.
* `AlgebraicGeometry.quotientStalkEquivFiberStalkPullbackSndComp_mk_germ` pins the identification
  on germs of sections over the chart.
* `AlgebraicGeometry.fiberι_fiberBaseChangeIso_hom` pins the point of `h⁻¹(y)` the identification
  is read at, by its image in `Z ×_{gL, W, t} X`.

## Implementation notes

The point of the slice is built from `Ideal.map_isPrime_of_surjective`, and the computation of its
image is `Ideal.comap_map_of_surjective` together with `Ideal.mk_ker`: the contraction of the
extension of a prime containing the kernel is the prime again. No existential is involved, so the
slice map that the point belongs to is the specific composite
`Spec.map (Ideal.Quotient.mk (b)) ≫ hV.fromSpec` which the keystone is stated for.

The identification of local rings is the composite of the chart computation on the fibre with the
transport of local rings along the identification of schemes of `SliceFiberPullback.lean`, taken
in the direction `AlgebraicGeometry.stalkRingEquivOfSchemeIso` provides it and then inverted. The
point of `h⁻¹(y)` is the image of the point of the base change under that identification, so no
point of a fibre is ever transported along an equality of base points.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section SlicePoint

variable {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V)
  {b : Γ(Y, V)} (hb : b ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal)

include hb in
/-- The ideal `(b)` is contained in the prime of `y`, `b` vanishing at `y`. -/
private lemma span_singleton_le_primeIdealOf :
    Ideal.span {b} ≤ (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hb)

/-- **The point of a slice over the point it is cut at.** Let `V` be an affine open of a scheme
`Y`, let `y` be a point of `V`, and let `b` be a section over `V` vanishing at `y`. Then the
image of the prime of `y` under the quotient map is a point of the slice
`Spec(Γ(Y, V) ⧸ (b))`.

This is the point of the slice as *data*: the slicing lemma needs it to build the point of
`U' ×_{g,U,t} R` at which its clauses (4) and (5) are asserted, and an existentially bound point
cannot be used there, the slice morphism having to be the specific one the chart computation of
`SliceBaseChangeChart.lean` is about. -/
public noncomputable def IsAffineOpen.slicePoint :
    ↥(Spec (CommRingCat.of (↥Γ(Y, V) ⧸ Ideal.span {b}))) :=
  ⟨Ideal.map (Ideal.Quotient.mk (Ideal.span {b})) (hV.primeIdealOf ⟨y, hy⟩).asIdeal,
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact span_singleton_le_primeIdealOf hV hy hb)⟩

include hb in
/-- The point of the slice lies over the prime of `y` in `Spec Γ(Y, V)`. -/
public theorem IsAffineOpen.specMap_mk_slicePoint :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) (hV.slicePoint hy hb) =
      hV.primeIdealOf ⟨y, hy⟩ := by
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (Ideal.Quotient.mk (Ideal.span {b}))
      (Ideal.map (Ideal.Quotient.mk (Ideal.span {b}))
        (hV.primeIdealOf ⟨y, hy⟩).asIdeal) = _
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left]
  exact span_singleton_le_primeIdealOf hV hy hb

include hb in
/-- **The point of a slice lies over the point the slice is cut at.** -/
public theorem IsAffineOpen.sliceMap_slicePoint :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ hV.fromSpec)
        (hV.slicePoint hy hb) = y := by
  rw [Scheme.Hom.comp_apply, hV.specMap_mk_slicePoint hy hb]
  exact hV.fromSpec_primeIdealOf ⟨y, hy⟩

end SlicePoint

section FiberStalk

variable {T X Y Z : Scheme.{u}} (f : X ⟶ Y) (t : X ⟶ T) (gL : Z ⟶ T) (y : Y)
  {U : (f.fiber y).Opens} (hU : IsAffineOpen U)
  (hW : IsAffineOpen (pullback.snd gL (f.fiberι y ≫ t) ⁻¹ᵁ U))
  (hsurj : Function.Surjective ((pullback.snd gL (f.fiberι y ≫ t)).app U).hom)
  {w : Γ(f.fiber y, U)}
  (hker : RingHom.ker ((pullback.snd gL (f.fiberι y ≫ t)).app U).hom = Ideal.span {w})
  {z : ↥(pullback gL (f.fiberι y ≫ t))}
  (hz : pullback.snd gL (f.fiberι y ≫ t) z ∈ U)

/-- **The local ring of the fibre of a base change followed by a second morphism.** Let
`gL : Z ⟶ T` and `t : X ⟶ T`, let `f : X ⟶ Y`, and write `h = pr₂ ≫ f`. If the base change of
`gL` along the fibre embedding `ι : f⁻¹(y) ⟶ X` composed with `t` is, over an affine chart `U` of
`f⁻¹(y)` with affine preimage, cut out by a single section `w`, then the local ring of `h⁻¹(y)` at
the corresponding point is the local ring of `f⁻¹(y)` modulo the germ of `w`.

For the slicing lemma of Stacks 0461 the section `w` is the image `t(b)` of the slicing parameter
under the target map, read on the source fibre; so this computes the local ring of `h⁻¹(u)` as
`𝒪_{F_u, e(u)} ⧸ (t b)`, which is the ring whose Cohen-Macaulayness clause (4) asserts. -/
public noncomputable def quotientStalkEquivFiberStalkPullbackSndComp :
    ((f.fiber y).presheaf.stalk (pullback.snd gL (f.fiberι y ≫ t) z) ⧸
        Ideal.span {((f.fiber y).presheaf.germ U
          (pullback.snd gL (f.fiberι y ≫ t) z) hz).hom w}) ≃+*
      ((pullback.snd gL t ≫ f).fiber y).presheaf.stalk
        ((fiberBaseChangeIso f t gL y).hom z) :=
  (quotientStalkEquivStalkPullbackSndOfSpan (f.fiberι y ≫ t) hU gL hW hsurj hker hz).trans
    (stalkRingEquivOfSchemeIso (fiberBaseChangeIso f t gL y) z rfl).symm

include hU hW hsurj hker in
/-- The identification of `quotientStalkEquivFiberStalkPullbackSndComp` carries the class of the
germ of a section over the chart to the transport of the germ of its image. This pins it down,
the germs of sections over an affine open generating the local ring. -/
public theorem quotientStalkEquivFiberStalkPullbackSndComp_mk_germ (c : Γ(f.fiber y, U)) :
    quotientStalkEquivFiberStalkPullbackSndComp f t gL y hU hW hsurj hker hz
        (Ideal.Quotient.mk _ ((f.fiber y).presheaf.germ U
          (pullback.snd gL (f.fiberι y ≫ t) z) hz c)) =
      (stalkRingEquivOfSchemeIso (fiberBaseChangeIso f t gL y) z rfl).symm
        ((pullback gL (f.fiberι y ≫ t)).presheaf.germ
          (pullback.snd gL (f.fiberι y ≫ t) ⁻¹ᵁ U) z hz
          (((pullback.snd gL (f.fiberι y ≫ t)).app U) c)) := by
  rw [quotientStalkEquivFiberStalkPullbackSndComp, RingEquiv.trans_apply,
    quotientStalkEquivStalkPullbackSndOfSpan_mk_germ]

/-- The point of `h⁻¹(y)` at which the identification is read lies over the image of the point of
the base change in `Z ×_{gL, T, t} X`. This pins that point down, the embedding of a fibre being
injective. -/
public theorem fiberι_fiberBaseChangeIso_hom :
    (pullback.snd gL t ≫ f).fiberι y ((fiberBaseChangeIso f t gL y).hom z) =
      fiberBaseChangeToBaseChange f t gL y z := by
  rw [← Scheme.Hom.comp_apply, fiberBaseChangeIso_hom_fiberι]

end FiberStalk

end AlgebraicGeometry

end

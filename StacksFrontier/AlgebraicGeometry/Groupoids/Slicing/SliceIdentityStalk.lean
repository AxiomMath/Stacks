module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceFiberStalk

/-!
# The local rings of the sliced arrow scheme and of its fibre, at the identity arrow

Fix a groupoid scheme `(U, R, s, t, c, e, i)`, an affine open `A` of the object scheme containing
a point `u`, and a section `b` over `A` vanishing at `u`. Write

```
gL : U' = Spec(Γ(U, A) ⧸ (b)) ⟶ U
```

for the slice, `P = U' ×_{gL, U, t} R` for its base change along the target map, and
`h = pr₂ ≫ s : P ⟶ U` for the morphism of Stacks 0461. This file reads the chart computation of
`SliceBaseChangeChart.lean` twice — once on the arrow scheme and once on the source fibre
`F_u = s⁻¹(u)` — at the point of `P` determined by the slice point and the identity arrow, giving

```
𝒪_{P, (u', e(u))} ≅ 𝒪_{R, e(u)} ⧸ (t b)    and    𝒪_{h⁻¹(u), ·} ≅ 𝒪_{F_u, e(u)} ⧸ (t b).
```

These are the two local-ring computations clauses (4) and (5) of Stacks 0461 rest on. The first
is the keystone read directly; the second is the keystone read for the morphism
`AlgebraicGeometry.GroupoidScheme.targetOnSourceFiber`, which is the target map restricted to the
source fibre, together with the identification of `SliceFiberPullback.lean` of `h⁻¹(u)` with that
base change. The inputs the second needed — an affine chart of `F_u` around the identity arrow
carried into `A` by the target map, and the surjectivity and the kernel of the map on sections
over it — are supplied here.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.SliceFiberIdentityPoint` is the point of
  `U' ×_{gL, U, t|F_u} F_u` lying over the slice point and the identity arrow, pinned by its two
  projections, and `AlgebraicGeometry.GroupoidScheme.sliceFiberIdentityPoint` is that point.
* `AlgebraicGeometry.GroupoidScheme.quotientStalkEquivStalkSliceBaseChange` computes the local
  ring of `P` at the point determined by the slice point and the identity arrow.
* `AlgebraicGeometry.GroupoidScheme.quotientStalkEquivStalkSourceMapFiber` computes the local ring
  of `h⁻¹(u)` at the corresponding point.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_isAffineOpen_sourceFiber_mem_le_preimage`: the affine
  chart of the source fibre around the identity arrow carried into `A`.
* `AlgebraicGeometry.GroupoidScheme.surjective_and_ker_app_pullback_snd_slice_sourceFiber`: the
  surjectivity and the kernel of the map on sections over such a chart — the missing input of the
  fibre half.
* `AlgebraicGeometry.GroupoidScheme.isAffineOpen_preimage_pullback_snd_slice_sourceFiber`: the
  preimage of such a chart in the base change is affine.
* `AlgebraicGeometry.GroupoidScheme.sliceBaseChangeIdentityPoint_fst` and
  `_snd` pin the point of `P`, and
  `AlgebraicGeometry.GroupoidScheme.fiberι_sliceFiberIdentityFiberPoint` pins the point of
  `h⁻¹(u)`.

## Implementation notes

The point of the fibre product is produced from the surjectivity of the comparison of a fibre
square of schemes onto the fibre product of the underlying spaces, so it is available only through
its two projections; it is therefore recorded as a structure, in the same way as
`AlgebraicGeometry.SliceSituation.IdentityArrowPoint`. The point of `P` is then its image under
the comparison morphism of `SliceFiberPullback.lean`, whose two projection formulas compute the
projections of the image, so both points are pinned without any transport along an equality of
points.

The local rings are taken at `pullback.snd … P.point` rather than at `sourceFiberIdentity G u`,
and at `pullback.snd … (comparison P.point)` rather than at the identity arrow: the two agree, by
`SliceFiberIdentityPoint.point_snd` and
`AlgebraicGeometry.GroupoidScheme.sliceBaseChangeIdentityPoint_snd`, but stating the computations
at the projections keeps every germ and every stalk indexed by the point the chart argument
itself produces.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) (A : G.objects.left.affineOpens)
  {u : G.objects.left} (huA : u ∈ A.1) {b : Γ(G.objects.left, A.1)}
  (hb : b ∈ (A.2.primeIdealOf ⟨u, huA⟩).asIdeal)

/-- **The arrow-scheme half.** The local ring of `U' ×_{gL, U, t} R` at a point lying over the
chart `B` of the arrow scheme is the local ring of `R` there modulo the germ of `t(b)`.

This is `AlgebraicGeometry.quotientStalkEquivStalkPullbackSndOfSpan` fed with
`AlgebraicGeometry.GroupoidScheme.surjective_and_ker_app_pullback_snd_slice` and
`AlgebraicGeometry.isAffineOpen_preimage_pullback_snd_quotientSpan`. -/
public noncomputable def quotientStalkEquivStalkSliceBaseChange
    {B : G.arrows.left.Opens} (hB : IsAffineOpen B) (hBA : B ≤ G.target.left ⁻¹ᵁ A.1)
    {q : ↥(pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
      A.2.fromSpec) G.target.left)}
    (hq : pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
      A.2.fromSpec) G.target.left q ∈ B) :
    (G.arrows.left.presheaf.stalk
          (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
            A.2.fromSpec) G.target.left q) ⧸
        Ideal.span {(G.arrows.left.presheaf.germ B
          (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
            A.2.fromSpec) G.target.left q) hq).hom
          (G.target.left.appLE A.1 B hBA b)}) ≃+*
      (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
        A.2.fromSpec) G.target.left).presheaf.stalk q :=
  quotientStalkEquivStalkPullbackSndOfSpan G.target.left hB _
    (isAffineOpen_preimage_pullback_snd_quotientSpan G.target.left A.2 hB hBA b)
    (surjective_app_pullback_snd_quotientSpan G.target.left A.2 hB hBA b)
    (ker_app_pullback_snd_quotientSpan G.target.left A.2 hB hBA b) hq

include huA in
/-- **The affine chart of the source fibre.** Around the identity arrow, viewed as a point of the
source fibre `F_u`, there is an affine open of `F_u` carried into `A` by the target map read on
`F_u`.

This is the first of the inputs the fibre half of clause (4) was missing. -/
public theorem exists_isAffineOpen_sourceFiber_mem_le_preimage :
    ∃ W : (G.source.left.fiber u).Opens, IsAffineOpen W ∧ sourceFiberIdentity G u ∈ W ∧
      W ≤ targetOnSourceFiber G u ⁻¹ᵁ A.1 :=
  exists_isAffineOpen_mem_le_preimage (targetOnSourceFiber G u) (sourceFiberIdentity G u)
    (by rw [targetOnSourceFiber_sourceFiberIdentity]; exact huA)

/-- **The missing input of the fibre half.** Over an affine chart `W` of the source fibre carried
into `A` by the target map, the map on sections of the second projection of the base change of the
slice along the target map read on `F_u` is surjective with kernel generated by the image of the
parameter.

This is `AlgebraicGeometry.surjective_and_ker_app_pullback_snd_quotientSpan` for the morphism
`targetOnSourceFiber G u`, which is what the fibre half of clause (4) of Stacks 0461 needs:
together with the identification of the fibre of `h` of `SliceFiberPullback.lean`, it computes the
local ring of `h⁻¹(u)`. -/
public theorem surjective_and_ker_app_pullback_snd_slice_sourceFiber
    {W : (G.source.left.fiber u).Opens} (hW : IsAffineOpen W)
    (hWA : W ≤ targetOnSourceFiber G u ⁻¹ᵁ A.1) :
    Function.Surjective ((pullback.snd
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec)
          (targetOnSourceFiber G u)).app W).hom ∧
      RingHom.ker ((pullback.snd
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec)
          (targetOnSourceFiber G u)).app W).hom =
        Ideal.span {(targetOnSourceFiber G u).appLE A.1 W hWA b} :=
  surjective_and_ker_app_pullback_snd_quotientSpan (targetOnSourceFiber G u) A.2 hW hWA b

/-- The preimage of an affine chart of the source fibre in the base change of the slice is an
affine open. -/
public theorem isAffineOpen_preimage_pullback_snd_slice_sourceFiber
    {W : (G.source.left.fiber u).Opens} (hW : IsAffineOpen W)
    (hWA : W ≤ targetOnSourceFiber G u ⁻¹ᵁ A.1) :
    IsAffineOpen (pullback.snd
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec)
      (targetOnSourceFiber G u) ⁻¹ᵁ W) :=
  isAffineOpen_preimage_pullback_snd_quotientSpan (targetOnSourceFiber G u) A.2 hW hWA b

/-- The point of `U' ×_{gL, U, t|F_u} F_u` lying over the slice point and over the identity arrow,
pinned by its two projections.

The scheme is a fibre product, so the point is not available as a pair of points; it comes from
the surjectivity of the comparison of a fibre square of schemes onto the fibre product of the
underlying spaces, and the two projection equations are all that is known about it. -/
public structure SliceFiberIdentityPoint where
  /-- The point itself. -/
  point : ↥(pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
    A.2.fromSpec) (targetOnSourceFiber G u))
  /-- Its projection to the slice is the slice point. -/
  point_fst :
    pullback.fst (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
      A.2.fromSpec) (targetOnSourceFiber G u) point = A.2.slicePoint huA hb
  /-- Its projection to the source fibre is the identity arrow. -/
  point_snd :
    pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
      A.2.fromSpec) (targetOnSourceFiber G u) point = sourceFiberIdentity G u

/-- **The point of `U' ×_{gL, U, t|F_u} F_u` over the slice point and the identity arrow.** The
slice carries its point to `u` and the target map carries the identity arrow at `u` to `u`, so the
two points are compatible over the object scheme and the fibre product has a point above them. -/
public noncomputable def sliceFiberIdentityPoint : SliceFiberIdentityPoint G A huA hb :=
  Classical.choice (by
    obtain ⟨p, hp₁, hp₂⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec)
        (targetOnSourceFiber G u))
      (A.2.slicePoint huA hb) (sourceFiberIdentity G u)
      (by rw [A.2.sliceMap_slicePoint huA hb, targetOnSourceFiber_sourceFiberIdentity])
    exact ⟨p, hp₁, hp₂⟩)

/-- The point of `U' ×_{gL, U, t} R` determined by the slice point and the identity arrow: the
image of `SliceFiberIdentityPoint.point` under the comparison morphism of
`SliceFiberPullback.lean`. -/
public noncomputable def sliceBaseChangeIdentityPoint
    (P : SliceFiberIdentityPoint G A huA hb) :
    ↥(pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
      A.2.fromSpec) G.target.left) :=
  fiberBaseChangeToBaseChange G.source.left G.target.left
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec) u P.point

/-- The projection of the point of `U' ×_{gL, U, t} R` to the slice is the slice point. -/
public theorem sliceBaseChangeIdentityPoint_fst (P : SliceFiberIdentityPoint G A huA hb) :
    pullback.fst (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
        A.2.fromSpec) G.target.left (sliceBaseChangeIdentityPoint G A huA hb P) =
      A.2.slicePoint huA hb :=
  (fiberBaseChangeToBaseChange_fst_apply G.source.left G.target.left
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec) u
    P.point).trans P.point_fst

/-- The projection of the point of `U' ×_{gL, U, t} R` to the arrow scheme is the identity arrow
at `u`. Together with the previous lemma this is the statement that the point is `(u', e(u))`. -/
public theorem sliceBaseChangeIdentityPoint_snd (P : SliceFiberIdentityPoint G A huA hb) :
    pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
        A.2.fromSpec) G.target.left (sliceBaseChangeIdentityPoint G A huA hb P) =
      G.identity.left u :=
  (fiberBaseChangeToBaseChange_snd_apply G.source.left G.target.left
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec) u
      P.point).trans
    ((congrArg (fun x => G.source.left.fiberι u x) P.point_snd).trans
      (fiberι_sourceFiberIdentity G u))

/-- **The fibre half.** The local ring of the fibre `h⁻¹(u)` of `h = pr₂ ≫ s` at the point
determined by the slice point and the identity arrow is the local ring of the source fibre `F_u`
there modulo the germ of the image `t(b)` of the slicing parameter.

This is the second of the two local-ring computations clauses (4) and (5) of Stacks 0461 rest on;
the chart argument is `AlgebraicGeometry.quotientStalkEquivFiberStalkPullbackSndComp` for the
morphism `targetOnSourceFiber G u`, and its hypotheses are
`surjective_and_ker_app_pullback_snd_slice_sourceFiber` and
`isAffineOpen_preimage_pullback_snd_slice_sourceFiber`. -/
public noncomputable def quotientStalkEquivStalkSourceMapFiber
    {W : (G.source.left.fiber u).Opens} (hW : IsAffineOpen W)
    (hWA : W ≤ targetOnSourceFiber G u ⁻¹ᵁ A.1) (P : SliceFiberIdentityPoint G A huA hb)
    (hPW : pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
      A.2.fromSpec) (targetOnSourceFiber G u) P.point ∈ W) :
    ((G.source.left.fiber u).presheaf.stalk
          (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
            A.2.fromSpec) (targetOnSourceFiber G u) P.point) ⧸
        Ideal.span {((G.source.left.fiber u).presheaf.germ W
          (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
            A.2.fromSpec) (targetOnSourceFiber G u) P.point) hPW).hom
          ((targetOnSourceFiber G u).appLE A.1 W hWA b)}) ≃+*
      ((pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
            A.2.fromSpec) G.target.left ≫ G.source.left).fiber u).presheaf.stalk
        ((fiberBaseChangeIso G.source.left G.target.left
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec)
          u).hom P.point) :=
  quotientStalkEquivFiberStalkPullbackSndComp G.source.left G.target.left
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec) u hW
    (isAffineOpen_preimage_pullback_snd_slice_sourceFiber G A hW hWA)
    (surjective_and_ker_app_pullback_snd_slice_sourceFiber G A hW hWA).1
    (surjective_and_ker_app_pullback_snd_slice_sourceFiber G A hW hWA).2 hPW

/-- The point of `h⁻¹(u)` at which the fibre half is read lies over the point `(u', e(u))` of
`U' ×_{gL, U, t} R`. This pins it down, the embedding of a fibre being injective. -/
public theorem fiberι_sliceFiberIdentityFiberPoint (P : SliceFiberIdentityPoint G A huA hb) :
    (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫
          A.2.fromSpec) G.target.left ≫ G.source.left).fiberι u
        ((fiberBaseChangeIso G.source.left G.target.left
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec)
          u).hom P.point) =
      sliceBaseChangeIdentityPoint G A huA hb P :=
  fiberι_fiberBaseChangeIso_hom G.source.left G.target.left
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b}))) ≫ A.2.fromSpec) u

end AlgebraicGeometry.GroupoidScheme

end

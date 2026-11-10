module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreChartReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreResidueFieldSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions

/-!
# The fibre over a point of a decent space as a chart fibre, and its reducedness

Let `p : X ⟶ Y` be a relatively representable morphism of algebraic spaces over a scheme `S` of
a big fppf site `B` and let `ξ` be a point of the decent space `Y`. The fibre
`X ×_Y Spec κ(ξ)` is represented by `Functor.relativelyRepresentable.pullback` of `p` along
`AlgebraicGeometry.Space.residueFieldMorphism`, and that presentation has no affine open to work
in. This file gives it a second presentation, as a **fibre of a morphism of schemes**, and reads
reducedness off that.

Take an elementary étale neighborhood `(V, e)` of `ξ` in the sense of Stacks 0BGU — one exists at
every point of a decent algebraic space by Stacks 0BBP,
`AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'`, which also produces a
bijection `φ : κ(ξ) → κ(e)` and a morphism `g` of the site with `Spec φ` underlying it and with
`Spec κ(e) ⟶ Y` factoring as `Spec κ(e) ⟶ V ⟶ Y`. Since `φ` is bijective, `g` is an isomorphism,
so `Spec κ(e) ⟶ Y` *is* the residue field morphism at `ξ` up to that isomorphism, and

`X ×_Y Spec κ(ξ) ≅ X ×_Y Spec κ(e) = (X ×_Y V) ×_V Spec κ(e)`

is the scheme-theoretic fibre of the morphism of charts `X ×_Y V ⟶ V` over the single point `e`.
Reducedness is then free, by
`AlgebraicGeometry.isReduced_fiber_of_isField_stalk` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreChartReduced`: `X ×_Y V` is étale over `X`
hence reduced when `X` is, and `𝒪_{V, e}` is a field when the local ring of `Y` at `ξ` has
dimension zero. Nothing identifies the ring of the fibre with a total fraction ring, and nothing
needs an affine open of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldMapPoint`: the point `e` of the representing scheme of `V`,
  read as a field-valued point of `yoneda.obj V` whose site morphism is literally
  `AlgebraicGeometry.Space.residueFieldMap`.
* `AlgebraicGeometry.Space.chartFibreResidueFibreIso`: the comparison of the two presentations —
  the fibre product of the chart morphism `X ×_Y V ⟶ V` with `e`, formed in the site, is
  isomorphic to `Functor.relativelyRepresentable.pullback` of `p` along the residue field
  morphism at `ξ`.

## Main results

* `AlgebraicGeometry.Space.isPullback_residueFieldMorphism_chartFibre`: the square cutting out the
  chart fibre is cartesian over `p` and the residue field morphism at `ξ`. This is the pasting of
  `AlgebraicGeometry.Space.isPullback_yoneda_representedFibreProjection` on top of
  `Functor.relativelyRepresentable.isPullback` of `p` along `V ⟶ Y`, with the isomorphism `g`
  cancelled off the bottom edge.
* `AlgebraicGeometry.Space.isReduced_toScheme_obj_representedFibreObject_residueFieldMapPoint`:
  the chart fibre has reduced underlying scheme when the source chart does and the local ring of
  the target chart at `e` is a field.
* `AlgebraicGeometry.Space.isReduced_toScheme_obj_pullback_residueFieldMorphism`: **the fibre
  `X ×_Y Spec κ(ξ)` of a relatively representable morphism of reduced algebraic spaces over a
  point of local ring dimension zero is reduced**, with no chart data asked of the caller, and
  `AlgebraicGeometry.Space.isReduced_appTop_pullback_residueFieldMorphism` is the same read on the
  ring of global sections.
* `AlgebraicGeometry.Space.isReduced_toScheme_obj_pullback_residueFieldMorphism_genericPoint` and
  `AlgebraicGeometry.Space.isReduced_appTop_pullback_residueFieldMorphism_genericPoint`: **the
  generic fibre `X ×_Y Spec R(Y)` of a relatively representable morphism of integral algebraic
  spaces is reduced**, the local ring dimension at the generic point being zero by
  `AlgebraicGeometry.Space.localRingDimension_genericPoint_eq_zero`.

## Implementation notes

The field-valued point `AlgebraicGeometry.Space.residueFieldMapPoint` is used rather than
`AlgebraicGeometry.Space.schemePointRepresentative` or
`AlgebraicGeometry.Space.residueFieldValuedPoint`, which present the same point of `|V|`: those
two are built with `CategoryTheory.Functor.preimage` of `fromSpecResidueField`, so their object of
the site is only *propositionally* `AlgebraicGeometry.Space.residueFieldObject` — through
`CategoryTheory.Functor.map_preimage` — whereas the elementary étale neighborhood produces its
morphism `g` out of `AlgebraicGeometry.Space.residueFieldObject` on the nose. With
`AlgebraicGeometry.Space.residueFieldMapPoint` both the representing object and the site morphism
are those of the neighborhood by definition, so no transport along an equality of objects of the
site is needed anywhere below. A private copy of the same field-valued point appears inside
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood`.

`AlgebraicGeometry.Space.isReduced_toScheme_obj_representedFibreObject_residueFieldMapPoint` is
`AlgebraicGeometry.Space.isReduced_toScheme_representedFibreObject_of_isField_stalk` at this
field-valued point instead of at `AlgebraicGeometry.Space.schemePointRepresentative`; it is
reproved rather than transported for the reason just given, the proof being the same three lines
over `AlgebraicGeometry.Space.isPullback_toScheme_representedFibre`.

## References

* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The residue-field point of a scheme of the site -/

/-- The field-valued point of `yoneda.obj V` given by the residue field at a point `e` of the
representing scheme of `V`, presented on `AlgebraicGeometry.Space.residueFieldObject` by
`AlgebraicGeometry.Space.residueFieldMap`.

Its class as a point of `|yoneda.obj V|` is `AlgebraicGeometry.Space.presheafPoint`, and its
underlying morphism of schemes is `Scheme.fromSpecResidueField`, both by definition. -/
def residueFieldMapPoint (V : BigFppfOver B S hS) (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e)))) :
    FieldValuedPoint B S hS (yoneda.obj V) where
  carrier := V.left.1.residueField e
  contained := hu
  toBase := V.left.1.fromSpecResidueField e ≫ V.hom.1
  value := residueFieldMap B S hS V e hu

/-- The class of `AlgebraicGeometry.Space.residueFieldMapPoint` is the point of the represented
presheaf that `e` names. -/
theorem class_residueFieldMapPoint (V : BigFppfOver B S hS) (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e)))) :
    (residueFieldMapPoint B S hS V e hu).class B S hS (yoneda.obj V) =
      presheafPoint B S hS V e hu := rfl

/-- The point of the representing scheme underlying
`AlgebraicGeometry.Space.residueFieldMapPoint` is the point one started from. -/
theorem pointsToScheme_class_residueFieldMapPoint (V : BigFppfOver B S hS) (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e)))) :
    pointsToScheme B S hS V
        ((residueFieldMapPoint B S hS V e hu).class B S hS (yoneda.obj V)) = e := by
  change V.left.1.fromSpecResidueField e (IsLocalRing.closedPoint _) = e
  exact Scheme.fromSpecResidueField_apply e _

/-- A point of the representing scheme of an étale chart is a chart point above its image. -/
theorem chartPoint_residueFieldMapPoint {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : BigFppfOver B S hS) (c : yoneda.obj V ⟶ F) (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e))))
    {x : points B S hS F}
    (hx : pointsMap B S hS (yoneda.obj V) c (presheafPoint B S hS V e hu) = x) :
    ChartPoint B S hS V c e x := by
  have h := chartPoint_pointsToScheme B S hS V c (presheafPoint B S hS V e hu)
  rwa [← class_residueFieldMapPoint B S hS V e hu,
    pointsToScheme_class_residueFieldMapPoint B S hS V e hu,
    class_residueFieldMapPoint B S hS V e hu, hx] at h

/-! ### Reducedness of the fibre of a morphism of charts -/

/-- **The fibre of a morphism of the site over a point whose local ring is a field is reduced**,
as soon as the source chart is reduced.

The scheme underlying the fibre product `W ×_V Spec κ(e)` formed in the site is the
scheme-theoretic fibre of the underlying morphism of schemes over `e` — here literally, the
underlying morphism of `AlgebraicGeometry.Space.residueFieldMapPoint` being
`Scheme.fromSpecResidueField` by definition — and that fibre is reduced by
`AlgebraicGeometry.isReduced_fiber_of_isField_stalk`. -/
theorem isReduced_toScheme_obj_representedFibreObject_residueFieldMapPoint
    {W V : BigFppfOver B S hS} (α : W ⟶ V)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj W)] (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e))))
    (hv : IsField ((V.left.1).presheaf.stalk e)) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj
      (representedFibreObject B S hS α (residueFieldMapPoint B S hS V e hu))) := by
  have hsq : IsPullback
      ((BigFppfOver.toScheme B S hS).map
        (representedFibreProjection B S hS α (residueFieldMapPoint B S hS V e hu)))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd α (FieldValuedPoint.siteHom B S hS (residueFieldMapPoint B S hS V e hu))))
      ((BigFppfOver.toScheme B S hS).map α)
      ((V.left.1).fromSpecResidueField e) :=
    isPullback_toScheme_representedFibre B S hS α (residueFieldMapPoint B S hS V e hu)
  have key : IsReduced (((BigFppfOver.toScheme B S hS).map α).fiber e) :=
    isReduced_fiber_of_isField_stalk ((BigFppfOver.toScheme B S hS).map α) e hv
  have hfib : IsPullback (((BigFppfOver.toScheme B S hS).map α).fiberι e)
      (((BigFppfOver.toScheme B S hS).map α).fiberToSpecResidueField e)
      ((BigFppfOver.toScheme B S hS).map α)
      ((V.left.1).fromSpecResidueField e) := IsPullback.of_hasPullback _ _
  exact @isReduced_of_isOpenImmersion _ _ (hsq.isoIsPullback _ _ hfib).hom _ key

/-! ### The two presentations of the fibre -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The chart fibre is the fibre over the residue field point.** Let `p : X ⟶ Y` be a
relatively representable morphism, let `ξ` be a point of the decent space `Y`, let
`c : yoneda.obj V ⟶ Y` be a morphism of the site's Yoneda image and let `e` be a point of the
representing scheme of `V`. Suppose given an isomorphism `g` of the site from the residue-field
point of `V` at `e` to the chosen representative of `ξ`, under which `Spec κ(e) ⟶ V ⟶ Y` is the
residue field morphism at `ξ` — which is exactly the data
`AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'` produces at `ξ`. Then the
square

```
(X ×_Y V) ×_V Spec κ(e) ⟶ X
          ↓                ↓ p
     Spec κ(e) ⟶ Spec κ(ξ) ⟶ Y
```

is cartesian.

This is one pasting: stack `AlgebraicGeometry.Space.isPullback_yoneda_representedFibreProjection`
for the chart morphism `X ×_Y V ⟶ V` on top of `Functor.relativelyRepresentable.isPullback` of
`p` along `c`, which gives the same square with `Spec κ(e) ⟶ V ⟶ Y` along the bottom, and cancel
the isomorphism `g` off that bottom edge. No commutative algebra enters. -/
theorem isPullback_residueFieldMorphism_chartFibre {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hdecY : IsDecentSpace B S hS Y)
    (ξ : points B S hS Y) {V : BigFppfOver B S hS} (c : yoneda.obj V ⟶ Y) (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e))))
    (g : (residueFieldMapPoint B S hS V e hu).siteObject B S hS (yoneda.obj V) ⟶
      (residueFieldRepresentative B S hS Y hdecY ξ).1.siteObject B S hS Y)
    (hgiso : IsIso g)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY ξ =
      yoneda.map (residueFieldMap B S hS V e hu) ≫ c) :
    IsPullback
      (yoneda.map (representedFibreProjection B S hS (hrep.snd c)
          (residueFieldMapPoint B S hS V e hu)) ≫ hrep.fst c)
      (yoneda.map (pullback.snd (hrep.snd c)
        (FieldValuedPoint.siteHom B S hS (residueFieldMapPoint B S hS V e hu)) ≫ g))
      p (residueFieldMorphism B S hS Y hdecY ξ) := by
  have := hgiso
  have hpaste := (isPullback_yoneda_representedFibreProjection B S hS (hrep.snd c)
    (residueFieldMapPoint B S hS V e hu)).paste_horiz (hrep.isPullback c)
  have hbot : fieldMorphism B S hS (yoneda.obj V) (residueFieldMapPoint B S hS V e hu) ≫ c =
      yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY ξ :=
    (congrArg (· ≫ c)
      (fieldMorphism_yoneda B S hS (residueFieldMapPoint B S hS V e hu))).trans hg.symm
  rw [hbot] at hpaste
  refine hpaste.of_iso (Iso.refl _) (Iso.refl _)
    (yoneda.mapIso (asIso g)) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp only [Functor.mapIso_hom, asIso_hom, Iso.refl_hom, Category.id_comp]
    exact (yoneda.map_comp _ _).symm
  · simp
  · simp [Functor.mapIso_hom]

/-- **The comparison of the two presentations of the fibre over `ξ`.** The fibre product of the
chart morphism `X ×_Y V ⟶ V` with the residue-field point of `V` at `e`, formed in the site, is
isomorphic to `Functor.relativelyRepresentable.pullback` of `p` along the residue field morphism
at `ξ`: two cartesian squares over the same cospan have isomorphic apices, and Yoneda is fully
faithful, so the isomorphism is one of the site. -/
def chartFibreResidueFibreIso {p : X ⟶ Y} (hrep : yoneda.relativelyRepresentable p)
    (hdecY : IsDecentSpace B S hS Y) (ξ : points B S hS Y) {V : BigFppfOver B S hS}
    (c : yoneda.obj V ⟶ Y) (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e))))
    (g : (residueFieldMapPoint B S hS V e hu).siteObject B S hS (yoneda.obj V) ⟶
      (residueFieldRepresentative B S hS Y hdecY ξ).1.siteObject B S hS Y)
    (hgiso : IsIso g)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY ξ =
      yoneda.map (residueFieldMap B S hS V e hu) ≫ c) :
    representedFibreObject B S hS (hrep.snd c) (residueFieldMapPoint B S hS V e hu) ≅
      hrep.pullback (residueFieldMorphism B S hS Y hdecY ξ) :=
  yoneda.preimageIso
    ((isPullback_residueFieldMorphism_chartFibre B S hS hrep hdecY ξ c e hu g hgiso
        hg).isoIsPullback _ _
      (hrep.isPullback (residueFieldMorphism B S hS Y hdecY ξ)))

/-- **The fibre over `ξ` is reduced**, read through the chart presentation: the fibre
`X ×_Y Spec κ(ξ)` is reduced as soon as the chart `X ×_Y V` is reduced and the local ring of the
representing scheme of `V` at `e` is a field. -/
theorem isReduced_toScheme_obj_pullback_residueFieldMorphism_of_chart {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hdecY : IsDecentSpace B S hS Y)
    (ξ : points B S hS Y) {V : BigFppfOver B S hS} (c : yoneda.obj V ⟶ Y) (e : V.left.1)
    (hu : B.Contains (Spec (.of (V.left.1.residueField e))))
    (g : (residueFieldMapPoint B S hS V e hu).siteObject B S hS (yoneda.obj V) ⟶
      (residueFieldRepresentative B S hS Y hdecY ξ).1.siteObject B S hS Y)
    (hgiso : IsIso g)
    (hg : yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY ξ =
      yoneda.map (residueFieldMap B S hS V e hu) ≫ c)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj (hrep.pullback c))]
    (hv : IsField ((V.left.1).presheaf.stalk e)) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY ξ))) :=
  have := isReduced_toScheme_obj_representedFibreObject_residueFieldMapPoint B S hS
    (hrep.snd c) e hu hv
  isReduced_of_isOpenImmersion
    ((BigFppfOver.toScheme B S hS).mapIso
      (chartFibreResidueFibreIso B S hS hrep hdecY ξ c e hu g hgiso hg)).inv

/-! ### The fibre over a point of local ring dimension zero -/

/-- **The fibre `X ×_Y Spec κ(ξ)` of a relatively representable morphism of reduced algebraic
spaces over a point of local ring dimension zero has reduced underlying scheme.**

The chart `(V, e)` is an affine elementary étale neighborhood of `ξ` (Stacks 0BBP), which comes
with a bijection `φ : κ(ξ) → κ(e)`; so the morphism `g` of the site it also produces has
`Spec φ` underlying it and is therefore an isomorphism, by
`AlgebraicGeometry.Space.isIso_bigFppfOver_of_isIso_toScheme_map`. The chart `X ×_Y V` of `X` is
reduced because `X` is and `Functor.relativelyRepresentable.fst` of `p` along `V ⟶ Y` is étale,
and the local ring of `V` at `e` is a field by
`AlgebraicGeometry.Space.isField_stalk_chart_of_localRingDimension_eq_zero`. So
`AlgebraicGeometry.Space.isReduced_toScheme_obj_pullback_residueFieldMorphism_of_chart` applies.

At the generic point of an integral space the hypothesis on the local ring dimension holds by
`AlgebraicGeometry.Space.mem_genericPoints_iff_localRingDimension_eq_zero`, so this is
reducedness of the **generic fibre** — the half of the identification of the generic fibre of a
finite dominant morphism with `Spec R(X)` that the proof of Stacks 0EQ4 for algebraic spaces
needs and that was missing; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreResidueFieldSquare`. -/
theorem isReduced_toScheme_obj_pullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hdecY : IsDecentSpace B S hS Y)
    (hredX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hredY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    {ξ : points B S hS Y} (hξ : localRingDimension B S hS ξ = 0) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY ξ))) := by
  obtain ⟨E, -, -, φ, hφ, g, hgspec, hgsq⟩ :=
    exists_affine_elementaryEtaleNeighborhood' B S hS hY hdecY ξ
  have hofhom : IsIso (CommRingCat.ofHom φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hφ
  have hgi : IsIso g := by
    refine isIso_bigFppfOver_of_isIso_toScheme_map B S hS g ?_
    have h2 : IsIso (Spec.map (CommRingCat.ofHom φ)) :=
      inferInstanceAs (IsIso (Scheme.Spec.map (CommRingCat.ofHom φ).op))
    exact hgspec ▸ h2
  have hetfst : IsEtale B S hS (hrep.fst E.toSpace) :=
    isEtale_of_isPullback_yoneda B S hS (hrep.isPullback E.toSpace).flip E.etale_toSpace
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj (hrep.pullback E.toSpace)) :=
    (exists_atlas_iff_forall_etale B S hS X (fun T : Scheme.{u} => IsReduced T) hX).mp hredX
      (hrep.pullback E.toSpace) (hrep.fst E.toSpace)
      ((isEtale_iff_presheaf_of_yoneda B S hS _).mp hetfst)
  exact isReduced_toScheme_obj_pullback_residueFieldMorphism_of_chart B S hS hrep hdecY ξ
    E.toSpace E.point E.residueField_contained g hgi hgsq
    (isField_stalk_chart_of_localRingDimension_eq_zero B S hS hY hredY hξ E.etale_toSpace
      (chartPoint_residueFieldMapPoint B S hS E.scheme E.toSpace E.point
        E.residueField_contained E.map_point))

/-- **The generic point of an integral algebraic space has local ring dimension zero.** Its
closure is the whole point space, which is the unique irreducible component, so it is a point of
codimension zero in the sense of Stacks 0ABV. -/
theorem localRingDimension_genericPoint_eq_zero {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hint : IsIntegralSpace B S hS F) :
    localRingDimension B S hS (genericPoint B S hS hF hint) = 0 := by
  let : IrreducibleSpace (points B S hS F) := hint.2.2
  refine (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hF hint.2.1 _).1 ?_
  change closure {genericPoint B S hS hF hint} ∈ irreducibleComponents (points B S hS F)
  rw [isGenericPoint_genericPoint B S hS hF hint, irreducibleComponents_eq_singleton]
  exact rfl

/-- **The generic fibre `X ×_Y Spec R(Y)` of a relatively representable morphism of integral
algebraic spaces has reduced underlying scheme.**

This is `AlgebraicGeometry.Space.isReduced_toScheme_obj_pullback_residueFieldMorphism` at the
generic point of `Y`, whose local ring has dimension zero by
`AlgebraicGeometry.Space.localRingDimension_genericPoint_eq_zero`; the function field `R(Y)` is
the residue field there, by Stacks 0END and
`AlgebraicGeometry.Space.rationalFunctionsRingEquiv`.

Reducedness of the generic fibre is the half of the identification of the generic fibre of a
finite dominant morphism with `Spec R(X)` that the proof of Stacks 0EQ4 for algebraic spaces
needs; the other half, that the fibre of `|p|` over the generic point of `Y` is a single point,
is `AlgebraicGeometry.Space.fibre_genericPoint_eq_singleton`. -/
theorem isReduced_toScheme_obj_pullback_residueFieldMorphism_genericPoint {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hintY.2.1
        (genericPoint B S hS hY hintY)))) :=
  isReduced_toScheme_obj_pullback_residueFieldMorphism B S hS hrep hX hY hintY.2.1 hintX.1
    hintY.1 (localRingDimension_genericPoint_eq_zero B S hS hY hintY)

/-- **The ring of the generic fibre `X ×_Y Spec R(Y)` is reduced**, the reading of
`AlgebraicGeometry.Space.isReduced_toScheme_obj_pullback_residueFieldMorphism_genericPoint` on
global sections. For `p` finite the generic fibre is affine, `Spec D` with `D` a finite
`R(Y)`-algebra by `AlgebraicGeometry.Space.finite_appTop_pullback_fieldMorphism`, and this says
that `D` is reduced — hence, being Artinian and local, a field. -/
theorem isReduced_appTop_pullback_residueFieldMorphism_genericPoint {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) :
    _root_.IsReduced Γ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hintY.2.1
        (genericPoint B S hS hY hintY))), ⊤) :=
  have := isReduced_toScheme_obj_pullback_residueFieldMorphism_genericPoint B S hS hrep hX hY
    hintX hintY
  inferInstance

/-- **The ring of the fibre `X ×_Y Spec κ(ξ)` is reduced**, the reading of
`AlgebraicGeometry.Space.isReduced_toScheme_obj_pullback_residueFieldMorphism` on global
sections. This is the form a consumer presenting the fibre as the spectrum of a ring uses: for
`p` finite the fibre is affine, by
`AlgebraicGeometry.Space.isAffine_toScheme_obj_pullback_fieldMorphism`, and this says that the
finite `κ(ξ)`-algebra it is the spectrum of is reduced. -/
theorem isReduced_appTop_pullback_residueFieldMorphism {p : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable p) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hdecY : IsDecentSpace B S hS Y)
    (hredX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T))
    (hredY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    {ξ : points B S hS Y} (hξ : localRingDimension B S hS ξ = 0) :
    _root_.IsReduced Γ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback (residueFieldMorphism B S hS Y hdecY ξ)), ⊤) :=
  have := isReduced_toScheme_obj_pullback_residueFieldMorphism B S hS hrep hX hY hdecY
    hredX hredY hξ
  inferInstance

end AlgebraicGeometry.Space

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpacePoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiSeparatedMorphismComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionBaseChange

/-!
# Quasi-compactness of a morphism of formal algebraic spaces on reductions

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0AJB** lists four equivalent conditions on `f`, of
which condition (1) is that the induced morphism `f_red : X_red ⟶ Y_red` of reductions be a
quasi-compact morphism of algebraic spaces and condition (3) — the one taken as the definition
of a quasi-compact morphism, Stacks 0AJC — is that `X ×_Y T` be a quasi-compact formal algebraic
space for every affine scheme `T` over `S` in the site mapping to `Y`. This file proves the
implication (3) ⇒ (1), and with it the implication (2) ⇒ (1), condition (2) being the same
condition over the quasi-compact schemes of the site.

The argument is the one of **Stacks 03E4**, that quasi-compactness of an algebraic space is
quasi-compactness of its point space. Quasi-compactness of `f_red` is tested against the
quasi-compact algebraic spaces mapping to `Y_red`, and a quasi-compact algebraic space has, by
**Stacks 03H6**, a surjective étale chart by an affine scheme `U` of the site, along which the
test descends; so it suffices to see that `U ×_{Y_red} X_red` is quasi-compact for every affine
scheme `U` of the site mapping to `Y_red`. Now

* `U ×_{Y_red} X_red ⟶ U ×_Y X` is a representable thickening — it is the base change of
  `X_red ⟶ X` along `U ×_Y X ⟶ X`, which is
  `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_baseChange_of_isReduction`;
* `U ×_Y X` is a quasi-compact formal algebraic space by condition (3), hence receives from a
  represented presheaf with compact underlying scheme a morphism surjective on points,
  `AlgebraicGeometry.FormalSpace.exists_compact_pointsSurjection_of_isQuasiCompactSpace`;
* the base change of that morphism along the representable thickening is again represented, by
  an object of the site whose underlying scheme is a closed subscheme of a compact one and so
  is compact, and it is surjective on points.

So `U ×_{Y_red} X_red` receives a morphism surjective on points from a represented presheaf
with compact underlying scheme, and it is an algebraic space, being a fibre product of three
algebraic spaces. Stacks 03E4 in the value universe of the formal algebraic spaces,
`AlgebraicGeometry.Space.isQuasiCompactSpaceULift_iff_compactSpace_pointsULift`, finishes.

## Main results

* `AlgebraicGeometry.FormalSpace.IsQuasiCompact.isQuasiCompactOnReductions`: **Stacks 0AJB**,
  the implication condition (3) ⇒ condition (1).
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnSchemeBaseChanges.isQuasiCompactOnReductions`:
  **Stacks 0AJB**, the implication condition (2) ⇒ condition (1).

## What is assumed

Nothing. In particular Stacks 0AIN, the existence of the reduction of a formal algebraic space,
is not used: condition (1) of Stacks 0AJB is phrased in this library, in
`AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions`, with the two reductions, their
inclusions and the induced morphism quantified over, so the reductions against which the
conclusion is proved are given, not constructed.

The implications not proved here are proved, with the four conditions assembled into one
`List.TFAE`, in `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismTFAE`: condition
(4) implies condition (3) by refining the covering, along a point `T ⟶ Y` with `T` affine, to
finitely many *affine* objects of the site étale over `T` (Stacks 0AIG makes the base changes of
the members objects of the site), over each of which the fibre product has a single affine formal
chart by Stacks 0AN3 clause (1). No form of Stacks 0AJ3 or Stacks 0AIU is used: the fibre product
`X ×_Y T` is shown to be a formal algebraic space by exhibiting that chart, not by a colimit
argument. With (1) ⇒ (4) this gives (1) ⇒ (3), and (3) ⇒ (1) closes the cycle.

Condition (4) of Stacks 0AJB, the covering form, is not treated here: the implication (1) ⇒ (4)
is proved in `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismFormalAtlas` and the
implication (4) ⇒ (3) in `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismTFAE`.

## Implementation notes

The fibre products are the chosen `CategoryTheory.Limits.pullback`s here rather than arbitrary
cartesian squares, since condition (1) is a statement about `pullback g f_red` — that is the
shape of `AlgebraicGeometry.Space.IsQuasiCompactULift` — while condition (2) quantifies over
every cartesian square and so applies to the chosen one. The cartesian square of fppf sheaves
produced for condition (2) is carried to one of presheaves along the inclusion of sheaves into
presheaves, which preserves limits.

Descent of quasi-compactness of a fibre product along a surjective étale chart of the base is
`AlgebraicGeometry.Space.isQuasiCompactSpaceULift_pullback_of_chart`, which is stated for
arbitrary presheaves and so needs no algebraic-space hypothesis on the test object. The affine
chart of the test object is
`AlgebraicGeometry.Space.exists_affine_chart_of_isQuasiCompactSpaceULift`, Stacks 03H6 in the
value universe of the formal algebraic spaces.

## References

* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Xred Yred : FppfSheaf B S hS} {f : X ⟶ Y} {iX : Xred ⟶ X} {iY : Yred ⟶ Y}
  {fred : Xred ⟶ Yred}

/-- The fibre product of the reductions over an affine scheme of the site is a quasi-compact
algebraic space, under condition (3) of Stacks 0AJB.

The comparison morphism to the fibre product `U ×_Y X` is a representable thickening; that
fibre product is a quasi-compact formal algebraic space by hypothesis, so it receives a
morphism surjective on points from a represented presheaf with compact underlying scheme; and
the base change of that morphism along the representable thickening is again represented, by an
object of the site with compact underlying scheme, and surjective on points. -/
private theorem isQuasiCompactSpaceULift_pullback_of_affine
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    (hfred : fred ≫ iY = iX ≫ f)
    (hf : IsQuasiCompact B S hS f)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (η : (uliftYoneda.{u + 1}).obj U ⟶ Yred.obj) :
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS (pullback η fred.hom) := by
  -- the fibre product `U ×_Y X`, as a cartesian square of fppf sheaves and of presheaves
  let gs : yonedaSheaf B S hS U ⟶ Y := ⟨η ≫ iY.hom⟩
  have hWsheaf : IsPullback (pullback.fst gs f) (pullback.snd gs f) gs f :=
    IsPullback.of_hasPullback gs f
  have hWqc : IsQuasiCompactSpace B S hS (pullback gs f) :=
    hf U hU gs _ _ _ hWsheaf
  have hW : IsPullback (pullback.fst gs f).hom (pullback.snd gs f).hom (η ≫ iY.hom) f.hom :=
    hWsheaf.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  -- the comparison morphism from the fibre product of the reductions
  obtain ⟨c, -, -, hcthick⟩ :=
    exists_isRepresentableThickeningULift_baseChange_of_isReduction B S hS hiX hiY hfred
      (IsPullback.of_hasPullback η fred.hom) hW
  -- a represented presheaf with compact underlying scheme, surjective on points onto `U ×_Y X`
  obtain ⟨T, a, hT, ha⟩ :=
    exists_compact_pointsSurjection_of_isQuasiCompactSpace B S hS _ hWqc
  -- its base change along the comparison morphism
  have hsq : IsPullback (pullback.fst a c) (pullback.snd a c) a c :=
    IsPullback.of_hasPullback a c
  have hRthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS (pullback.fst a c) :=
    Space.relative_of_isPullback B S hS hsq hcthick
  obtain ⟨b, snd, fst, sqb⟩ := hRthick.rep (𝟙 ((uliftYoneda.{u + 1}).obj T))
  have hthick := hRthick.property (𝟙 ((uliftYoneda.{u + 1}).obj T)) fst snd sqb
  have _ : IsIso fst := sqb.isIso_fst_of_isIso
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := hT
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map snd) := hthick.1
  have hb : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
      ((BigFppfOver.toScheme B S hS).map snd)).compactSpace
  -- the composite is surjective on points
  have hsnd : Function.Surjective
      (Space.pointsMapULift.{u + 1} B S hS (pullback a c) (pullback.snd a c)) := by
    intro p
    obtain ⟨t, ht⟩ := ha (Space.pointsMapULift.{u + 1} B S hS (pullback η fred.hom) c p)
    obtain ⟨v, -, hv⟩ := Space.exists_point_of_isPullbackULift B S hS hsq t p ht
    exact ⟨v, hv⟩
  have hcomp : Function.Surjective (Space.pointsMapULift.{u + 1} B S hS
      ((uliftYoneda.{u + 1}).obj b) (fst ≫ pullback.snd a c)) := by
    rw [Space.pointsMapULift_comp]
    exact hsnd.comp (Space.bijective_pointsMapULift_of_iso.{u + 1} B S hS (asIso fst)).2
  -- Stacks 03E4 in the value universe of the formal algebraic spaces
  refine Space.isQuasiCompactSpaceULift_of_surjective_pointsMapULift.{u + 1} B S hS ?_
    (Space.compactSpace_pointsULift_uliftYoneda.{u + 1} B S hS b hb) _ hcomp
  exact Space.isAlgebraicSpaceULift_pullback B S hS η fred.hom
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U) hiX.algebraic hiY.algebraic

/-- **Stacks 0AJB, condition (3) implies condition (1).** Let `f : X ⟶ Y` be a morphism of
fppf sheaves on the big fppf site of `S` such that every fibre product of `f` with an affine
scheme over `S` in the site mapping to `Y` is a quasi-compact formal algebraic space — that is,
let `f` be quasi-compact in the sense of Stacks 0AJC. Then every morphism between reductions of
`X` and of `Y` compatible with `f` is a quasi-compact morphism of algebraic spaces.

Quasi-compactness of the morphism of reductions is tested against the quasi-compact algebraic
spaces mapping to the reduction of `Y`; such a space has, by Stacks 03H6, a surjective étale
chart by an *affine* scheme of the site, along which the test descends, so it suffices to treat
an affine scheme of the site, which is `isQuasiCompactSpaceULift_pullback_of_affine`. -/
@[stacks 0AJB "condition (3) implies condition (1), with the reductions quantified over in \
place of Stacks 0AIN"]
theorem IsQuasiCompact.isQuasiCompactOnReductions (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompactOnReductions B S hS f := by
  intro Xred Yred iX iY hiX hiY fred hfred Z hZalg hZqc g
  obtain ⟨U, cc, hU, hccSurj, hccEtale⟩ :=
    Space.exists_affine_chart_of_isQuasiCompactSpaceULift.{u + 1} B S hS hZalg hZqc
  refine Space.isQuasiCompactSpaceULift_pullback_of_chart.{u + 1} B S hS fred.hom g cc
    hccSurj hccEtale ?_
  exact isQuasiCompactSpaceULift_pullback_of_affine B S hS hiX hiY hfred hf U hU (cc ≫ g)

/-- **Stacks 0AJB, condition (2) implies condition (1).** The fibre product condition over the
quasi-compact schemes over `S` in the site restricts to the affine ones, which already implies
quasi-compactness of every induced morphism of reductions. -/
@[stacks 0AJB "condition (2) implies condition (1), with the reductions quantified over in \
place of Stacks 0AIN"]
theorem IsQuasiCompactOnSchemeBaseChanges.isQuasiCompactOnReductions
    (hf : IsQuasiCompactOnSchemeBaseChanges B S hS f) :
    IsQuasiCompactOnReductions B S hS f :=
  IsQuasiCompact.isQuasiCompactOnReductions B S hS (hf.isQuasiCompact B S hS)

end AlgebraicGeometry.FormalSpace

end

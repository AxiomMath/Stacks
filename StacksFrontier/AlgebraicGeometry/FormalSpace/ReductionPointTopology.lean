module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
import all StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSupplement

/-!
# The point space of a reduction

Let `S` be a scheme contained in a big fppf site `B` and let `i : X_red ⟶ X` be a reduction of
a formal algebraic space `X` over `S`. The inclusion of a reduction is bijective on points,
`AlgebraicGeometry.FormalSpace.IsReduction.bijective_pointsMapULift`; this file upgrades that
to a homeomorphism for the point topology
`AlgebraicGeometry.Space.pointTopologyULift`, so that a subset of `|X_red|` and its image in
`|X|` are closed together.

The inclusion is continuous, every morphism of presheaves being so, and the content is that it
is open. A scheme-valued point `a : U ⟶ X` of the target is tested against the image of an open
`W ⊆ |X_red|` by base change: `i` is representable, so `a` pulls back to `U' ⟶ U` with
`U' ⟶ X_red`, and the morphism of schemes `U' ⟶ U` is a thickening, hence a homeomorphism,
`Stacks.Thickenings.IsThickening.isHomeomorph`. The open subset of `U'` cutting out the inverse
image of `W` therefore transports to an open subset of `U`, and that subset cuts out the
inverse image of the image of `W`: a field-valued point of `U` lifts to `U'`, uniquely, because
the spectrum of a field is reduced.

## Main results

* `AlgebraicGeometry.FormalSpace.isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift`:
  a representable thickening of presheaves is a homeomorphism on points.
* `AlgebraicGeometry.FormalSpace.isOpenMap_pointsMapULift_of_isRepresentableThickeningULift`:
  a representable thickening of presheaves is open on points. Together these are the
  universal-homeomorphism statement for thickenings at the level of point spaces; the reduction
  statements below are corollaries of it, a reduction's inclusion being a representable
  thickening.
* `AlgebraicGeometry.FormalSpace.IsReduction.isOpenMap_pointsMapULift`: the inclusion of a
  reduction is open on points.
* `AlgebraicGeometry.FormalSpace.IsReduction.isHomeomorph_pointsMapULift`: it is therefore a
  homeomorphism on points.
* `AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift`: the image in `|X|`
  of a closed subset of `|X_red|` is closed, and
  `AlgebraicGeometry.FormalSpace.IsReduction.isCompact_compl_image_pointsMapULift`: its
  complement stays quasi-compact.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A representable thickening is open on points.** Let `W` be open in the point space of the
source and let `a : U ⟶ G` be a scheme-valued point of the target. Pulling the thickening back
along `a` gives `U' ⟶ U`, a thickening of schemes and hence a homeomorphism, together with
`U' ⟶ F`; the open subset of `U'` cutting out the inverse image of `W` transports along that
homeomorphism to an open subset of `U`. It cuts out the inverse image of the image of `W`,
because a field-valued point of `U` lifts to `U'` — the spectrum of a field being reduced, so
the base-changed thickening over it is an isomorphism — and the map is injective on points.

Nothing here uses a universal property: the lifting step is
`AlgebraicGeometry.FormalSpace.existsUnique_comp_eq_of_isRepresentableThickeningULift`. -/
theorem isOpenMap_pointsMapULift_of_isRepresentableThickeningULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (h : Space.IsRepresentableThickeningULift.{u + 1} B S hS a) :
    @IsOpenMap _ _ (Space.pointTopologyULift.{u + 1} B S hS F)
      (Space.pointTopologyULift.{u + 1} B S hS G)
      (Space.pointsMapULift.{u + 1} B S hS F a) := by
  let _instSource := Space.pointTopologyULift.{u + 1} B S hS F
  let _instTarget := Space.pointTopologyULift.{u + 1} B S hS G
  intro W hW
  rw [Space.isOpen_pointTopologyULift_iff] at hW ⊢
  intro U b
  obtain ⟨c, snd, fst, sq⟩ := h.1 b
  obtain ⟨V, hVopen, hVmem⟩ := hW c fst
  have hhomeo := (h.2 b fst snd sq).isHomeomorph
  refine ⟨⇑((BigFppfOver.toScheme B S hS).map snd) '' V, hhomeo.isOpenMap V hVopen, ?_⟩
  intro p
  have hred := IsReduction.isReduced_toScheme_obj_siteObject
    ((uliftYoneda.{u + 1}).obj U) p
  set T := p.siteObject B S hS ((uliftYoneda.{u + 1}).obj U) with hTdef
  set tU : (uliftYoneda.{u + 1}).obj T ⟶ (uliftYoneda.{u + 1}).obj U :=
    uliftYonedaEquiv.{u + 1}.symm p.value with htU
  obtain ⟨l, hl, -⟩ := existsUnique_comp_eq_of_isRepresentableThickeningULift h T hred
    (uliftYonedaEquiv.{u + 1} (tU ≫ b))
  rw [Equiv.symm_apply_apply] at hl
  have hvalue : ((uliftYoneda.{u + 1}).map snd).app (Opposite.op T)
      (uliftYonedaEquiv.{u + 1} (sq.lift l tU hl)) = p.value := by
    rw [← uliftYonedaEquiv_comp, sq.lift_snd l tU hl, htU, Equiv.apply_symm_apply]
  set q : Space.FieldValuedPointULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj c) :=
    { carrier := p.carrier, field := p.field, contained := p.contained, toBase := p.toBase,
      value := uliftYonedaEquiv.{u + 1} (sq.lift l tU hl) } with hq
  have hqmap : Space.FieldValuedPointULift.map B S hS ((uliftYoneda.{u + 1}).obj c)
      ((uliftYoneda.{u + 1}).map snd) q = p :=
    congrArg (fun v ↦ (⟨p.carrier, p.contained, p.toBase, v⟩ :
      Space.FieldValuedPointULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U))) hvalue
  have hscheme : Space.schemePointULift B S hS U p =
      ((BigFppfOver.toScheme B S hS).map snd) (Space.schemePointULift B S hS c q) := by
    conv_lhs => rw [← hqmap]
    exact Space.schemePointULift_map_uliftYoneda B S hS snd q
  have hkey : Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U) b
        (p.class B S hS ((uliftYoneda.{u + 1}).obj U)) =
      Space.pointsMapULift.{u + 1} B S hS F a
        (Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj c) fst
          (q.class B S hS ((uliftYoneda.{u + 1}).obj c))) := by
    have hpq : Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj c)
        ((uliftYoneda.{u + 1}).map snd) (q.class B S hS ((uliftYoneda.{u + 1}).obj c)) =
        p.class B S hS ((uliftYoneda.{u + 1}).obj U) := by
      rw [Space.pointsMapULift_class, hqmap]
    have hstep := congrFun (congrArg
      (Space.pointsMapULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj c)) sq.w.symm)
      (q.class B S hS ((uliftYoneda.{u + 1}).obj c))
    simp only [Space.pointsMapULift_comp, Function.comp_apply] at hstep
    simpa only [hpq] using hstep
  rw [Set.mem_preimage, hkey,
    (bijective_pointsMapULift_of_isRepresentableThickeningULift h).1.mem_set_image,
    hscheme, hhomeo.injective.mem_set_image]
  exact hVmem q

/-- **A representable thickening of presheaves is a homeomorphism on points.** It is continuous,
every morphism of presheaves being continuous on points, open by
`AlgebraicGeometry.FormalSpace.isOpenMap_pointsMapULift_of_isRepresentableThickeningULift`, and
bijective by
`AlgebraicGeometry.FormalSpace.bijective_pointsMapULift_of_isRepresentableThickeningULift`. -/
theorem isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (h : Space.IsRepresentableThickeningULift.{u + 1} B S hS a) :
    @IsHomeomorph _ _ (Space.pointTopologyULift.{u + 1} B S hS F)
      (Space.pointTopologyULift.{u + 1} B S hS G)
      (Space.pointsMapULift.{u + 1} B S hS F a) := by
  let _instSource := Space.pointTopologyULift.{u + 1} B S hS F
  let _instTarget := Space.pointTopologyULift.{u + 1} B S hS G
  exact ⟨Space.continuous_pointsMapULift.{u + 1} B S hS a,
    isOpenMap_pointsMapULift_of_isRepresentableThickeningULift h,
    bijective_pointsMapULift_of_isRepresentableThickeningULift h⟩

namespace IsReduction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}

/-- **The inclusion of a reduction is open on points.** Let `W ⊆ |X_red|` be open and let
`a : U ⟶ X` be a scheme-valued point of `X`. Pulling `i` back along `a` gives `U' ⟶ U`, a
thickening of schemes and hence a homeomorphism, together with `U' ⟶ X_red`; the open subset
of `U'` cutting out the inverse image of `W` transports along that homeomorphism to an open
subset of `U`. It cuts out the inverse image of the image of `W`, because a field-valued point
of `U` lifts to `U'` — the spectrum of a field being reduced — and `i` is injective on
points. -/
theorem isOpenMap_pointsMapULift (h : IsReduction B S hS X Xred i) :
    @IsOpenMap _ _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj)
      (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom) :=
  isOpenMap_pointsMapULift_of_isRepresentableThickeningULift h.isRepresentableThickening

/-- **The inclusion of a reduction is a homeomorphism on points.** It is continuous, every
morphism of presheaves being continuous on points, open by
`AlgebraicGeometry.FormalSpace.IsReduction.isOpenMap_pointsMapULift`, and bijective by
`AlgebraicGeometry.FormalSpace.IsReduction.bijective_pointsMapULift`. -/
theorem isHomeomorph_pointsMapULift (h : IsReduction B S hS X Xred i) :
    @IsHomeomorph _ _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj)
      (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom) :=
  isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift
    h.isRepresentableThickening

/-- The image in `|X|` of a closed subset of `|X_red|` along the inclusion of a reduction is
closed, the inclusion being a homeomorphism on points. -/
theorem isClosed_image_pointsMapULift (h : IsReduction B S hS X Xred i)
    {T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)}
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T) := by
  let _instSource := Space.pointTopologyULift.{u + 1} B S hS Xred.obj
  let _instTarget := Space.pointTopologyULift.{u + 1} B S hS X.obj
  exact h.isHomeomorph_pointsMapULift.isClosedMap T hT

/-- **The image in `|X|` of a subset of `|X_red|` with quasi-compact complement again has
quasi-compact complement.** The inclusion of a reduction is a homeomorphism on points, so it is
a bijection and the image of the complement is the complement of the image. This is the
companion of `AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift` that
clause (3) of Stacks 0GVV needs, its quasi-compactness hypothesis being on `|X_red| \ T`
while the completion is formed along the image of `T` in `|X|`. -/
theorem isCompact_compl_image_pointsMapULift (h : IsReduction B S hS X Xred i)
    {T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)}
    (hqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) Tᶜ) :
    @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T)ᶜ := by
  let _instSource := Space.pointTopologyULift.{u + 1} B S hS Xred.obj
  let _instTarget := Space.pointTopologyULift.{u + 1} B S hS X.obj
  rw [← Set.image_compl_eq h.bijective_pointsMapULift]
  exact hqc.image (Space.continuous_pointsMapULift.{u + 1} B S hS i.hom)

end IsReduction

end AlgebraicGeometry.FormalSpace

end

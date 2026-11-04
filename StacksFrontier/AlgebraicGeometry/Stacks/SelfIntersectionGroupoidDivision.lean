module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.DerealizationIdentityArrowDivision
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidDerealization
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidPreRelation

/-!
# Dividing the self-intersection groupoid of a field-valued point

Let `𝒳` be an algebraic stack over `S` and `ξ : Spec(k) ⟶ 𝒳` a 1-morphism out of the algebraic
stack of a field spectrum of the big fppf site of `S`. The groupoid in algebraic spaces of
**Stacks 04T4 (4)** that `ξ` carries is
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`, and
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoidScheme_fieldSpectrum` is its
de-realization — a groupoid scheme over `S`, when `𝒳` is quasi-DM over `S` and `ξ` is locally of
finite type.

This file runs the division of **Stacks 04S4** by the open and closed piece of the arrow scheme
through the identity on it. Of the hypotheses
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_division_identityArrowOpens_derealization`
asks of the pre-relation, unramifiedness and local quasi-finiteness are supplied by the join of
**Stacks 050H** to the groupoid's own pre-relation
(`StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidPreRelation`), and separatedness
comes from the zero-dimensionality of the arrow scheme instead: a zero-dimensional scheme is
discrete, hence separated, so every morphism out of the arrow space is separated. The hypotheses
asked of the source and the target are the finiteness properties of `ξ`, read on the representing
presheaves by **Stacks 06FM**; and the zero-dimensionality of the arrow scheme is the first
paragraph of the proof of **Stacks 06MF**, read through **Stacks 0ACA**.

So the division runs at a field spectrum of a DM stack with nothing left over: no separatedness
hypothesis on `𝒳` or on its relative diagonal enters.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.derealizationObjectsIsoSpec`: **the object scheme of
  the de-realization is the spectrum of the field** — the chosen representing scheme of the
  object space is isomorphic to it.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isFlat_source_pointGroupoid` and
  `...isLocallyOfFinitePresentation_source_pointGroupoid`: the source morphism of the groupoid is
  flat and locally of finite presentation as soon as `ξ` is.
* `AlgebraicGeometry.Stack.SelfIntersection.isLocallyArtinian_arrows_derealization_pointGroupoid`:
  the arrow scheme of the de-realization is zero-dimensional.
* `AlgebraicGeometry.Stack.SelfIntersection.isSeparated_prodLift_pointGroupoid_fieldSpectrum`:
  **the pre-relation is separated**, from that zero-dimensionality alone.
* `AlgebraicGeometry.Stack.SelfIntersection.exists_division_identityArrowOpens_pointGroupoid`:
  **the division of the de-realized self-intersection groupoid of a field spectrum by the piece
  through the identity, with the quotient the spectrum of a field.**
* `...exists_division_identityArrowOpens_etale_pointGroupoid`: the same division when `ξ` is in
  addition flat and locally of finite presentation, with the identity of the quotient groupoid an
  open immersion and its source and target maps étale.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (kObj : BigFppfOver B S hS)
  (ξ : schemeStack.{u, w} B S hS kObj ⟶ 𝒳)
  (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)

section Finiteness

variable (Usp : AlgebraicSpaces B S hS)
  (eU : StacksRepresentableCFG.EquivalenceOver
    (schemeStack.{u, w} B S hS kObj).val.val.p
    (presheafOfCategories (Usp.obj ⋙ typeToCat)).p)

/-- **The source morphism of a self-intersection groupoid is flat as soon as the point is.** The
second projection of the canonical 2-fibre product square of the cospan `(ξ, ξ)` is a base change
of `ξ`, hence flat by **Stacks 06PY**, and
`AlgebraicGeometry.Stack.isFlat_representingMap_of_isFlat` reads that on the morphism of
representing presheaves, which is
`AlgebraicGeometry.Stack.SelfIntersection.relationSource` by `rfl`. -/
theorem isFlat_relationSource (hξ : AlgebraicStacks.IsFlat B S hS ξ) :
    Space.IsFlat B S hS
      (relationSource (B := B) (S := S) (hS := hS)
        (𝒰 := (schemeStack.{u, w} B S hS kObj).val) (𝒳 := 𝒳.val) (f := ξ.hom.hom)
        (U := Usp) (R := Rsp) eU eR).hom :=
  isFlat_representingMap_of_isFlat B S hS Rsp.obj Usp.obj Rsp.property Usp.property eR eU
    (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ).snd
    (AlgebraicStacks.isFlat_baseChange B S hS ξ ξ
      (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ).swap
      (Bicategory.isTwoFibreProduct_swap
        (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS ξ ξ)) hξ)

/-- **The source morphism of a self-intersection groupoid is locally of finite presentation as
soon as the point is.** The argument of
`AlgebraicGeometry.Stack.SelfIntersection.isFlat_relationSource` at local finite presentation,
through **Stacks 06Q4**. -/
theorem isLocallyOfFinitePresentation_relationSource
    (hξ : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS ξ) :
    Space.IsLocallyOfFinitePresentation B S hS
      (relationSource (B := B) (S := S) (hS := hS)
        (𝒰 := (schemeStack.{u, w} B S hS kObj).val) (𝒳 := 𝒳.val) (f := ξ.hom.hom)
        (U := Usp) (R := Rsp) eU eR).hom :=
  isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation B S hS Rsp.obj
    Usp.obj Rsp.property Usp.property eR eU
    (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ).snd
    (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS ξ ξ
      (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ).swap
      (Bicategory.isTwoFibreProduct_swap
        (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS ξ ξ)) hξ)

end Finiteness

/-- `AlgebraicGeometry.Stack.SelfIntersection.isFlat_relationSource` at the canonical chart of the
object space, which is the source morphism of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`. -/
theorem isFlat_source_pointGroupoid (hξ : AlgebraicStacks.IsFlat B S hS ξ) :
    Space.IsFlat B S hS (pointGroupoid B S hS kObj ξ Rsp eR).source.hom :=
  isFlat_relationSource B S hS kObj ξ Rsp eR (AlgebraicGeometry.schemeSpace kObj)
    (representedChart B S hS kObj) hξ

/-- `AlgebraicGeometry.Stack.SelfIntersection.isLocallyOfFinitePresentation_relationSource` at the
canonical chart of the object space, which is the source morphism of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`. -/
theorem isLocallyOfFinitePresentation_source_pointGroupoid
    (hξ : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS ξ) :
    Space.IsLocallyOfFinitePresentation B S hS
      (pointGroupoid B S hS kObj ξ Rsp eR).source.hom :=
  isLocallyOfFinitePresentation_relationSource B S hS kObj ξ Rsp eR
    (AlgebraicGeometry.schemeSpace kObj) (representedChart B S hS kObj) hξ

end AlgebraicGeometry.Stack.SelfIntersection

namespace AlgebraicGeometry.Stack.SelfIntersection

/-! ### The division at the field spectrum that Stacks 06MP hands over -/

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : FieldSpectrum B S hS)
  {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (ξ : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
  (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)
  (hZ : B.Contains (⊤_ Scheme.{u}))
  (h𝒳 : IsQuasiDMOver B S hS 𝒳)
  (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ)

include eR in
/-- **The object scheme of the de-realization of the self-intersection groupoid of a field
spectrum is the spectrum of the field.** The object space is the presheaf of the spectrum's
object of the site on the nose, and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealizationObjectsIso` identifies the chosen
representing scheme with that object's underlying scheme; `AlgebraicGeometry.Stack.FieldSpectrum`
carries the isomorphism of the latter with the spectrum of the field. -/
def derealizationObjectsIsoSpec :
    haveI := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
    haveI := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
    (GroupoidInAlgebraicSpaces.derealization
        (pointGroupoid B S hS F.base ξ Rsp eR)).objects.left ≅
      Spec (CommRingCat.of F.carrier) :=
  haveI := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
  haveI := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
  ((Over.forget S).mapIso
    (GroupoidInAlgebraicSpaces.derealizationObjectsIso
      (pointGroupoid B S hS F.base ξ Rsp eR)
      (V := (Space.siteToOver B hS).obj F.base) F.base.left.property (Iso.refl _))).trans
    F.isSpec

include eR in
/-- **The arrow scheme of the de-realized self-intersection groupoid of a field spectrum is
zero-dimensional.** The dimension of the arrow space is at most zero by
`AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero_fieldSpectrum` — the first
paragraph of the proof of **Stacks 06MF** — and **Stacks 0ACA** turns that into local
quasi-finiteness of the source over the object space, which makes the arrow scheme locally
Artinian over the spectrum of the field. -/
theorem isLocallyArtinian_arrows_derealization_pointGroupoid :
    haveI := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
    haveI := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
    IsLocallyArtinian (GroupoidInAlgebraicSpaces.derealization
      (pointGroupoid B S hS F.base ξ Rsp eR)).arrows.left := by
  have : Subsingleton (Spec (CommRingCat.of F.carrier) : Type u) := inferInstance
  have := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
  have := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
  exact GroupoidInAlgebraicSpaces.isLocallyArtinian_derealization_arrows_of_dimension_le_zero
    (pointGroupoid B S hS F.base ξ Rsp eR) F.base (Iso.refl _)
    ⟨fun _ _ => (Scheme.homeoOfIso F.isSpec).injective (Subsingleton.elim _ _)⟩
    (isLocallyOfFiniteType_source_pointGroupoid B S hS F.base ξ Rsp eR hξ)
    (dimension_relation_le_zero_fieldSpectrum B S hS F ξ Rsp eR h𝒳 hξ)
    F.carrier (derealizationObjectsIsoSpec B S hS F ξ Rsp eR hZ h𝒳 hξ)

include eR hZ h𝒳 hξ in
/-- **The pre-relation of the de-realized self-intersection groupoid of a field spectrum is
separated.** The arrow scheme of the de-realization is zero-dimensional, hence discrete, hence a
separated scheme, so every morphism out of the arrow space is separated;
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSeparated_of_isLocallyArtinian_derealization_arrows`
is the statement, and the zero-dimensionality is
`AlgebraicGeometry.Stack.SelfIntersection.isLocallyArtinian_arrows_derealization_pointGroupoid`.

This is the form in which the division consumes separatedness of the pre-relation. Part (3) of
**Stacks 050H** reaches the same conclusion from separatedness of `Δ_{𝒳/S}`, as
`AlgebraicGeometry.Stack.SelfIntersection.isSeparated_prodLift_pointGroupoid`; here no condition
on `𝒳` beyond those already present enters, because at a field spectrum the arrow scheme is a
disjoint union of spectra of Artinian local rings and the pre-relation is separated
componentwise. -/
theorem isSeparated_prodLift_pointGroupoid_fieldSpectrum :
    Space.IsSeparated B S hS
      (prod.lift (pointGroupoid B S hS F.base ξ Rsp eR).target.hom
        (pointGroupoid B S hS F.base ξ Rsp eR).source.hom) := by
  have := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
  have := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
  exact GroupoidInAlgebraicSpaces.isSeparated_of_isLocallyArtinian_derealization_arrows
    (pointGroupoid B S hS F.base ξ Rsp eR) _
    (isLocallyArtinian_arrows_derealization_pointGroupoid B S hS F ξ Rsp eR hZ h𝒳 hξ)

include eR in
/-- **Stacks 04S4 at the de-realized self-intersection groupoid of a field spectrum.** Let `𝒳` be
an algebraic stack over `S` which is DM over `S` and let `ξ : Spec(k) ⟶ 𝒳` be a 1-morphism out of
the algebraic stack of a field spectrum of the site which is locally of finite type. Then the
groupoid scheme `AlgebraicGeometry.Stack.SelfIntersection.pointGroupoidScheme_fieldSpectrum` can
be divided by the open and closed piece of its arrow scheme through the identity at a point of
the object scheme, and the quotient is the spectrum of a field.

Every hypothesis of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_division_identityArrowOpens_derealization` is
discharged: unramifiedness and local quasi-finiteness of the pre-relation are the parts (4) and
(5) of **Stacks 050H** joined to the groupoid's own pre-relation, its separatedness comes from
the zero-dimensionality of the arrow scheme by
`AlgebraicGeometry.Stack.SelfIntersection.isSeparated_prodLift_pointGroupoid_fieldSpectrum`,
local finite type of the source and target is **Stacks 06FU** read on the representing
presheaves, zero-dimensionality of the arrow scheme is the first paragraph of the proof of
**Stacks 06MF**, and the object scheme is the spectrum of the field by
`AlgebraicGeometry.Stack.SelfIntersection.derealizationObjectsIsoSpec`. -/
theorem exists_division_identityArrowOpens_pointGroupoid
    (hDM : IsDMOver B S hS 𝒳)
    (u : (pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ).objects.left) :
    ∃ (P : _root_.Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid
        (pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ))
      (D : GroupoidScheme.Division
        (pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ)
        P.subgroupoid P.inclusion P.objects_eq),
      Set.range P.inclusion.mapArrows.left.base =
          {(pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ).identity.left.base u} ∧
        IsField Γ(D.quotient.left, ⊤) := by
  have := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
  have := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
  exact GroupoidInAlgebraicSpaces.exists_division_identityArrowOpens_derealization
    (pointGroupoid B S hS F.base ξ Rsp eR) F.carrier
    (derealizationObjectsIsoSpec B S hS F ξ Rsp eR hZ h𝒳 hξ)
    (isLocallyArtinian_arrows_derealization_pointGroupoid B S hS F ξ Rsp eR hZ h𝒳 hξ)
    (isLocallyOfFiniteType_source_pointGroupoid B S hS F.base ξ Rsp eR hξ)
    (isLocallyOfFiniteType_target_pointGroupoid B S hS F.base ξ Rsp eR hξ)
    (isUnramified_prodLift_pointGroupoid B S hS F.base ξ Rsp eR hDM)
    (isSeparated_prodLift_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ)
    (isLocallyQuasiFinite_prodLift_pointGroupoid B S hS F.base ξ Rsp eR h𝒳) u

include eR in
/-- **The division of the de-realized self-intersection groupoid of a field spectrum has étale
quotient groupoid.** If, on top of the hypotheses of
`AlgebraicGeometry.Stack.SelfIntersection.exists_division_identityArrowOpens_pointGroupoid`, the
1-morphism `ξ` is flat and locally of finite presentation, then the identity of the quotient
groupoid `(Ū, R̄)` is an open immersion and its source and target maps are étale. -/
theorem exists_division_identityArrowOpens_etale_pointGroupoid
    (hDM : IsDMOver B S hS 𝒳)
    (hflat : AlgebraicStacks.IsFlat B S hS ξ)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS ξ)
    (u : (pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ).objects.left) :
    ∃ (P : _root_.Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid
        (pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ))
      (D : GroupoidScheme.Division
        (pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ)
        P.subgroupoid P.inclusion P.objects_eq),
      Set.range P.inclusion.mapArrows.left.base =
          {(pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ).identity.left.base u} ∧
        IsField Γ(D.quotient.left, ⊤) ∧
          _root_.AlgebraicGeometry.IsOpenImmersion D.descended.identity.left ∧
          Etale D.descended.source.left ∧ Etale D.descended.target.left := by
  have := isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
  have := isRepresentable_arrows_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ
  exact GroupoidInAlgebraicSpaces.exists_division_identityArrowOpens_etale_derealization
    (pointGroupoid B S hS F.base ξ Rsp eR) F.carrier
    (derealizationObjectsIsoSpec B S hS F ξ Rsp eR hZ h𝒳 hξ)
    (isLocallyArtinian_arrows_derealization_pointGroupoid B S hS F ξ Rsp eR hZ h𝒳 hξ)
    (isLocallyOfFiniteType_source_pointGroupoid B S hS F.base ξ Rsp eR hξ)
    (isLocallyOfFiniteType_target_pointGroupoid B S hS F.base ξ Rsp eR hξ)
    (isFlat_source_pointGroupoid B S hS F.base ξ Rsp eR hflat)
    (isLocallyOfFinitePresentation_source_pointGroupoid B S hS F.base ξ Rsp eR hlfp)
    (isUnramified_prodLift_pointGroupoid B S hS F.base ξ Rsp eR hDM)
    (isSeparated_prodLift_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR hZ h𝒳 hξ)
    (isLocallyQuasiFinite_prodLift_pointGroupoid B S hS F.base ξ Rsp eR h𝒳) u

end AlgebraicGeometry.Stack.SelfIntersection

end

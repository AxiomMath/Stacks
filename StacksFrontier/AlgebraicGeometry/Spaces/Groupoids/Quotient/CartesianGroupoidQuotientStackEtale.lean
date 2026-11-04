module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStackEtale

/-!
# The quotient stack of a restriction is étale over the quotient stack

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces.
The étaleness argument of Stacks 0DU2 — Stacks 045D reduces étaleness of `[φ] : [U/R] ⟶ [U'/R']`
to its base change along the projection `S_{U'} ⟶ [U'/R']`, Stacks 04Y4 identifies that base
change with the quotient stack `[U''/R'']` of the auxiliary groupoid of Section 78.21, and
Stacks 0DU1 identifies `[U''/R'']` with an algebraic space étale over `U'` — uses only two facts
about the auxiliary groupoid: its structure morphism `U'' ⟶ U'` is flat and locally of finite
presentation, and its pre-relation `R'' ⟶ U'' ×_{U'} U''` is an open immersion.

This file runs that argument in that generality, and then verifies the two facts for a morphism
`φ` which is **fully faithful on generalized points** — every evaluation `G(T) ⥤ G'(T)` is fully
faithful, i.e. `R = (U ×_S U) ×_{U' ×_S U'} R'` — and whose map on objects is flat and locally of
finite presentation. This is the case of the restriction `R|_{U''}` of a groupoid to an étale
`U'' ⟶ U`, for which Stacks 0DU3 needs `[U''/R|_{U''}] ⟶ [U/R]` to be étale. There the auxiliary
pre-relation is even an isomorphism: a point `((u₁, r₁'), (u₂, r₂'))` of `U'' ×_{U'} U''` has a
unique preimage `(r, r₂')`, `r` being the unique arrow `u₂ ⟶ u₁` of `G` with
`φ(r) = r₁' ∘ r₂'⁻¹`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_etale_quotientStackMap_of_auxGroupoid`: the
  1-morphism `[φ]` of Stacks 046Q, once representable by algebraic spaces, is étale in the sense
  of Stacks 03YK as soon as the auxiliary structure morphism is flat and locally of finite
  presentation and the auxiliary pre-relation is an open immersion.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_auxGroupoidPreRelation_of_full_of_faithful`:
  the auxiliary pre-relation is an isomorphism when every evaluation of `φ` is fully faithful.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_auxToTargetObjects_of_isFlat` and
  `…isLocallyOfFinitePresentation_auxToTargetObjects_of_isLocallyOfFinitePresentation`: the
  auxiliary structure morphism is flat, respectively locally of finite presentation, when the map
  on objects and the source map of the target are.
* `AlgebraicGeometry.Stack.hasRelativeProperty_etale_quotientStackMap_of_full_of_faithful`: the
  1-morphism `[φ]` of a morphism of groupoids which is fully faithful on generalized points, with
  flat and locally finitely presented map on objects, is étale in the sense of Stacks 03YK.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
* [Stacks Project, Tag 0DU1](https://stacks.math.columbia.edu/tag/0DU1)
* [Stacks Project, Tag 0DU2](https://stacks.math.columbia.edu/tag/0DU2)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G G')

/-! ### The auxiliary structure morphism -/

/-- **Flatness of the auxiliary structure morphism `U'' ⟶ U'`.** It is the projection
`U'' = U ×_{U', t'} R' ⟶ R'`, a base change of the map on objects, followed by the source map of
the target, and flatness is stable under base change (Stacks 03MO) and composition
(Stacks 03MN). -/
theorem isFlat_auxToTargetObjects_of_isFlat
    (hobj : Space.IsFlat C S hS φ.toGroupoidHom.mapObjects)
    (hs : Space.IsFlat C S hS G'.source.hom) :
    Space.IsFlat C S hS (auxToTargetObjects φ).hom := by
  have := Space.isFlat_isStableUnderBaseChange C S hS
  have hsnd : Space.IsFlat C S hS (auxObjectsSnd φ).hom :=
    MorphismProperty.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces C S hS⦄ (f : F ⟶ G) => Space.IsFlat C S hS f.hom)
      (isPullback_auxObjects φ) (show Space.IsFlat C S hS φ.objectsMap.hom from hobj)
  exact Space.isFlat_comp C S hS (auxObjects φ).property G'.arrows.property
    G'.objects.property _ _ hsnd hs

/-- **Local finite presentation of the auxiliary structure morphism `U'' ⟶ U'`**, by base change
(Stacks 03XR) and composition (Stacks 03XQ), as for flatness. -/
theorem isLocallyOfFinitePresentation_auxToTargetObjects_of_isLocallyOfFinitePresentation
    (hobj : Space.IsLocallyOfFinitePresentation C S hS φ.toGroupoidHom.mapObjects)
    (hs : Space.IsLocallyOfFinitePresentation C S hS G'.source.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (auxToTargetObjects φ).hom := by
  have hsnd : Space.IsLocallyOfFinitePresentation C S hS (auxObjectsSnd φ).hom :=
    MorphismProperty.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces C S hS⦄ (f : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation C S hS f.hom)
      (isPullback_auxObjects φ)
      (show Space.IsLocallyOfFinitePresentation C S hS φ.objectsMap.hom from hobj)
  exact Space.isLocallyOfFinitePresentation_comp C S hS (auxObjects φ).property
    G'.arrows.property G'.objects.property _ _ hsnd hs

/-! ### The auxiliary pre-relation of a fully faithful morphism -/

/-- The source of the arrow of `G'` indexed by a point of `U''` is the image of that point in the
target object space. -/
theorem auxIndex_src (T : (BigFppfOver C S hS)ᵒᵖ) (P : (auxObjects φ).obj.obj T) :
    (auxIndex φ T P).src = (auxToTargetObjects φ).hom.app T P := rfl

/-- **The auxiliary pre-relation of a morphism of groupoids which is fully faithful on
generalized points is an isomorphism.** Over a test object, a point of `R''` with source `P` and
target `Q` is an arrow `r` of `G` with `P.arr ≫ φ(r) = Q.arr`; faithfulness makes it unique, and
fullness produces it as soon as `P` and `Q` have the same image in `U'`, which is what a point
of `U'' ×_{U'} U''` asks. -/
theorem isIso_auxGroupoidPreRelation_of_full_of_faithful
    (hfull : ∀ T, (φ.toGroupoidHom.evaluation T).Full)
    (hfaith : ∀ T, (φ.toGroupoidHom.evaluation T).Faithful) :
    IsIso (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ)).left := by
  let G'' := auxGroupoidOverTargetObjects φ
  let j := (Space.groupoidPreRelation G'').left
  have : ∀ T, IsIso (j.app T) := fun T => by
    rw [isIso_iff_bijective]
    have hpb := (Space.isPullback_groupoidRelativeSquare G'').map ((evaluation _ _).obj T)
    let pt := (prod.fst : Space.groupoidRelativeSquare G'' ⟶
      Over.mk G''.objectsToBase.hom).left.app T
    let ps := (prod.snd : Space.groupoidRelativeSquare G'' ⟶
      Over.mk G''.objectsToBase.hom).left.app T
    have et : ∀ x, pt (j.app T x) = (auxTarget φ).hom.app T x :=
      fun x => congrArg (fun k => k.app T x) (Space.target_hom_eq_groupoidPreRelation_comp G'').symm
    have es : ∀ x, ps (j.app T x) = (auxSource φ).hom.app T x :=
      fun x => congrArg (fun k => k.app T x) (Space.source_hom_eq_groupoidPreRelation_comp G'').symm
    have := hfull T
    have := hfaith T
    refine ⟨fun a b hab => ?_, fun z => ?_⟩
    · have ht : (auxTarget φ).hom.app T a = (auxTarget φ).hom.app T b := by
        rw [← et, ← et, hab]
      have hs : (auxSource φ).hom.app T a = (auxSource φ).hom.app T b := by
        rw [← es, ← es, hab]
      let P := (auxSource φ).hom.app T a
      let Q := (auxTarget φ).hom.app T a
      let m := (auxArrowEquiv φ T P Q).symm ⟨a, rfl, rfl⟩
      let n := (auxArrowEquiv φ T P Q).symm ⟨b, hs.symm, ht.symm⟩
      have hmn : m = n := by
        refine AuxHom.ext' ((auxEval φ T).map_injective ?_)
        rw [← cancel_epi (auxIndex φ T P).arr, m.w, n.w]
      have := congrArg (fun k => ((auxArrowEquiv φ T P Q) k).1) hmn
      simp only [m, n, Equiv.apply_symm_apply] at this
      exact this
    · let Q := pt z
      let P := ps z
      have hbase : (auxIndex φ T P).src = (auxIndex φ T Q).src :=
        (congrArg (fun k => k z) hpb.w).symm
      let F := auxEval φ T
      let m : auxIndex φ T P ⟶ auxIndex φ T Q :=
        { base := hbase
          arrow := F.preimage (inv (auxIndex φ T P).arr ≫ eqToHom hbase ≫ (auxIndex φ T Q).arr)
          w := by rw [F.map_preimage, IsIso.hom_inv_id_assoc] }
      exact ⟨(auxArrowEquiv φ T P Q m).1, Types.ext_of_isPullback hpb
        ((et _).trans (auxArrowEquiv φ T P Q m).2.2) ((es _).trans (auxArrowEquiv φ T P Q m).2.1)⟩
  exact NatIso.isIso_of_isIso_app j

/-- The auxiliary pre-relation of a morphism of groupoids which is fully faithful on generalized
points is an open immersion, which is the hypothesis Stacks 0DU1 consumes. -/
theorem isOpenImmersion_auxGroupoidPreRelation_of_full_of_faithful
    (hfull : ∀ T, (φ.toGroupoidHom.evaluation T).Full)
    (hfaith : ∀ T, (φ.toGroupoidHom.evaluation T).Faithful) :
    Space.IsOpenImmersion C S hS
      (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ)).left :=
  have := isIso_auxGroupoidPreRelation_of_full_of_faithful φ hfull hfaith
  Space.isOpenImmersion_of_isIso C S hS _

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G H : GroupoidInAlgebraicSpaces C S hS B}

/-- **The étaleness argument of Stacks 0DU2, in the generality of an arbitrary morphism of
groupoids.** Let `φ : G ⟶ H` be a morphism of groupoids in algebraic spaces whose auxiliary
groupoid of Section 78.21, read over the object space `U'` of `H`, has flat and locally finitely
presented structure morphism `U'' ⟶ U'` and open immersion as pre-relation. If the 1-morphism
`[φ]` of Stacks 046Q is representable by algebraic spaces, it is étale in the sense of
Stacks 03YK.

By Stacks 045D it suffices that the base change of `[φ]` along `π : S_{U'} ⟶ [U'/R']` be étale;
by Stacks 04Y4 that base change is `[U''/R''] ⟶ S_{U'}`, which by Stacks 0DU1 is the étale
structure morphism `U''/R'' ⟶ U'`. The representability hypothesis is what Stacks 03YK
presupposes in order to speak of the relative property. -/
theorem hasRelativeProperty_etale_quotientStackMap_of_auxGroupoid (φ : Hom G H)
    (hflat : Space.IsFlat C S hS (auxToTargetObjects φ).hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS (auxToTargetObjects φ).hom)
    (hopen : Space.IsOpenImmersion C S hS
      (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ)).left)
    (hrep : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMap φ)) :
    HasRelativeProperty.{u, u + 1, u + 1, u} C S hS (Space.etaleMorphisms C S hS)
      (quotientStackMapCFGHom φ) hrep := by
  let G'' := auxGroupoidOverTargetObjects φ
  let X : AlgebraicSpaces C S hS := quotientSheafSpace G'' hflat hlfp hopen
  let Q := auxQuotientSquareFibredSwap φ
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_auxQuotientSquareFibredSwap φ
  have hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} C S hS _ _ _
      (quotientStackMapCFGHom φ) (quotientStackProjectionHom H) Q hQ hrep
  let p : Q.pt.val ⥤ᵇ (fibredCategory C S hS X.obj).val :=
    quotientStackToQuotientSheaf G'' hflat hlfp hopen
  have : p.toFunctor.IsEquivalence :=
    isEquivalence_quotientStackToQuotientSheaf G'' hflat hlfp hopen
  let q : (liftedObjectSpace H).val ⥤ᵇ (fibredCategory C S hS H.objects.obj).val :=
    liftedFibredCategoryDown H.objects
  have : q.toFunctor.IsEquivalence := isEquivalence_liftedFibredCategoryDown H.objects
  let a := (associatedMap C S hS (quotientSheafToBaseSpace G'' hflat hlfp hopen).hom).1
  have α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q :=
    eqToIso (quotientStackToQuotientSheaf_comp_auxToTargetObjects φ hflat hlfp hopen)
  have hprop : Space.etaleMorphisms C S hS
      (ObjectProperty.homMk (representingMap C S hS (fibredCategory C S hS X.obj)
        (fibredCategory C S hS H.objects.obj) X.obj H.objects.obj
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) a) :
        (⟨X.obj, X.property⟩ : AlgebraicSpaces C S hS) ⟶ ⟨H.objects.obj, H.objects.property⟩) := by
    show Space.IsEtale C S hS (representingMap C S hS _ _ _ _ _ _ a)
    rw [representingMap_associatedMap]
    exact Space.isEtale_quotientSheafToBase_of_isOpenImmersion hflat hlfp hopen
  exact hasRelativeProperty_of_baseChange.{u, u + 1, u + 1, u} C S hS _ _ _
    (Space.etaleMorphisms C S hS) (quotientStackMapCFGHom φ) (quotientStackProjectionHom H)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
    hrep (localEssSurj_quotientStackProjectionHom H)
    (hasRelativeProperty_fst_of_isTwoFibreProduct_representingMap C S hS
      (Space.etaleMorphisms C S hS)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
      hQ _ hQfst a (isRepresentableByAlgebraicSpaces_associatedMap _) p q α X.obj H.objects.obj
      X.property H.objects.property (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) hprop)

/-- **The quotient stack of a restriction is étale over the quotient stack.** Let `φ : G ⟶ H` be a
morphism of groupoids in algebraic spaces which is fully faithful on generalized points — every
evaluation `G(T) ⥤ H(T)` is fully faithful, so that `G` is the restriction of `H` along the map
on objects — whose map on objects is flat and locally of finite presentation, and let the source
map of `H` be flat and locally of finite presentation. If the 1-morphism `[φ]` of Stacks 046Q is
representable by algebraic spaces, it is étale in the sense of Stacks 03YK.

This is the step `[U'/R|_{U'}] ⟶ [U/R]` for an étale `U' ⟶ U` in the proof of Stacks 0DU3; it is
`AlgebraicGeometry.Stack.hasRelativeProperty_etale_quotientStackMap_of_auxGroupoid`, whose
auxiliary pre-relation is here an isomorphism. -/
theorem hasRelativeProperty_etale_quotientStackMap_of_full_of_faithful (φ : Hom G H)
    (hfull : ∀ T, (φ.toGroupoidHom.evaluation T).Full)
    (hfaith : ∀ T, (φ.toGroupoidHom.evaluation T).Faithful)
    (hflat : Space.IsFlat C S hS φ.toGroupoidHom.mapObjects)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS φ.toGroupoidHom.mapObjects)
    (hsflat : Space.IsFlat C S hS H.source.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS H.source.hom)
    (hrep : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMap φ)) :
    HasRelativeProperty.{u, u + 1, u + 1, u} C S hS (Space.etaleMorphisms C S hS)
      (quotientStackMapCFGHom φ) hrep :=
  hasRelativeProperty_etale_quotientStackMap_of_auxGroupoid φ
    (isFlat_auxToTargetObjects_of_isFlat φ hflat hsflat)
    (isLocallyOfFinitePresentation_auxToTargetObjects_of_isLocallyOfFinitePresentation φ hlfp
      hslfp)
    (isOpenImmersion_auxGroupoidPreRelation_of_full_of_faithful φ hfull hfaith) hrep

end AlgebraicGeometry.Stack

end

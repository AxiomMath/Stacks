module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.DivisionSiteObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientProjectionEtaleGroupoidScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidDivision
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# A DM algebraic stack with a flat field-valued point has an étale one

Let `𝒵` be an algebraic stack over `S` which is DM over the base and whose terminal scheme the
site contains, and let `ξ : Spec k ⟶ 𝒵` be a 1-morphism out of the spectrum of a field which is
surjective, flat and locally of finite presentation.  Then there is a field `k₀` and an *étale*
1-morphism `Spec k₀ ⟶ 𝒵`.

This is the whole of the argument of **Stacks 06N0** after its first step: the groupoid
`(U, R, s, t, c)` of the flat presentation is divided by the open subgroupoid through the
identity, the quotient `U̅ = Spec k₀` is the spectrum of the field of invariants, and `U̅ ⟶ 𝒵` is
étale.

## Main definitions

* `AlgebraicGeometry.Stack.quotientProjectionSchemeStackMap`: the projection `S_U ⟶ [U/R]` of
  **Stacks 044R** at the realization of a groupoid scheme, read as a 1-morphism out of the
  algebraic stack of the object scheme and composed with an equivalence of the quotient stack
  with a given algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_comp_of_equivalence_target` and
  `…relativeProperty_comp_of_equivalence_source`: **Stacks 0457** at a square one of whose
  horizontal 1-morphisms is the identity.
* `AlgebraicGeometry.Stack.isEtale_quotientProjectionSchemeStackMap`: that 1-morphism is étale
  when the source map of the groupoid scheme is.
* `AlgebraicGeometry.Stack.exists_isEtale_fieldSpectrum_cover_of_division`: the conclusion of
  **Stacks 06N0** from a division of a groupoid scheme whose quotient stack is equivalent to `𝒵`.
* `AlgebraicGeometry.Stack.exists_isEtale_fieldSpectrum_cover_of_flat_fieldSpectrum_cover`: the
  statement at the head of this file.

## Implementation notes

Three equivalences over the site are composed to compare the quotient stack of the divided
groupoid with `𝒵`:

* `AlgebraicGeometry.Stack.SelfIntersection.nonempty_isEquivalenceOver_canonicalMap`
  (**Stacks 04WY**) for `[U/R] ⟶ 𝒵`, whose hypothesis is the relative-property reading of
  surjectivity, flatness and local finite presentation of `ξ`;
* `AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_quotientStackMap_of_iso` at
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.realizationIso`, which identifies the
  self-intersection groupoid with the realization of the groupoid *scheme* it de-realizes to;
* `Stacks.Groupoids.GroupoidScheme.nonempty_isEquivalenceOver_quotientStackMap_realizationHom`
  (**Stacks 046T**) for `[U/R] ⟶ [U̅/R̅]`, the descent morphism of the division being fully
  faithful on generalized points and its map on objects being finite locally free and surjective.

Étaleness of the projection `S_{U̅} ⟶ [U̅/R̅]` is
`Stacks.Groupoids.GroupoidScheme.isRelativelyEtale_quotientStackProjection_realization`, and it
is carried to `Spec k₀ ⟶ 𝒵` by two instances of **Stacks 0457**: one across the equivalence of
targets, with the identity on sources, and one across the universe lift
`AlgebraicGeometry.Stack.schemeStackLift` of sources, with the identity on targets.  Both
2-commutative squares are the identity, the 1-morphism out of the slice of the site being
*defined* as the composite; those two instances are stated separately below rather than inlined,
because the identity square is checked by a definitional comparison whose two sides would
otherwise be the whole composite of the three equivalences.

For the same reason each equivalence is produced as a based functor paired with the statement
that it is an equivalence, rather than as a term inside the proof of the last theorem: the
composite is passed to the next step as an opaque argument.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fppf
  AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange
  AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

namespace AlgebraicGeometry.Stack

universe u w v₁ v₂ v₃ w₁ w₂ w₃

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transport

variable {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒴' : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
  {𝒴 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}

/-- **Stacks 0457 across an equivalence of targets.** A 1-morphism composed with an equivalence
over the site has the relative property of **Stacks 03YK** at `P` as soon as the 1-morphism
does.

The square used is the one whose other horizontal 1-morphism is the identity on the source, so it
2-commutes on the nose. -/
theorem relativeProperty_comp_of_equivalence_target
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (f' : 𝒳.val ⥤ᵇ 𝒴'.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    [Functor.IsEquivalence b.toFunctor]
    (hP' : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴'.val.obj)
      (_hy : y ⋙ 𝒴'.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴'.val.p y f'.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (BasedFunctor.comp f' b).toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  relativeProperty_of_equivalences_symm B S hS P f' (BasedFunctor.comp f' b)
    (BasedFunctor.id 𝒳.val) b (Iso.refl _) hP'

variable {𝒳' : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}

/-- **Stacks 0457 across an equivalence of sources.** An equivalence over the site composed with
a 1-morphism has the relative property of **Stacks 03YK** at `P` as soon as the 1-morphism does.

The square used is `AlgebraicGeometry.Stack.compIdSquareIso`, whose other horizontal 1-morphism
is the identity on the target. -/
theorem relativeProperty_comp_of_equivalence_source
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    [Functor.IsEquivalence a.toFunctor]
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴.val.p y
          (BasedFunctor.comp a f).toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  relativeProperty_of_equivalences B S hS P (BasedFunctor.comp a f) f a
    (BasedFunctor.id 𝒴.val) (compIdSquareIso a f) hP

end Transport

section Projection

variable {G : Stacks.Groupoids.GroupoidScheme S}
  (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
  (hP : B.Contains (pullback G.source G.target).left)
  (𝒵 : AlgebraicStacks.{u, w} B S hS)
  (b : (quotientStack (G.realization B hS hU hR hP)) ⥤ᵇ 𝒵.val.val)

/-- **The chart of an algebraic stack presented by a groupoid scheme.** The projection
`S_U ⟶ [U/R]` of **Stacks 044R** at the realization of a groupoid scheme, read as a 1-morphism
out of the algebraic stack of the object scheme by the universe lift
`AlgebraicGeometry.Stack.schemeStackLift`, and composed with an equivalence of the quotient stack
with `𝒵`. -/
def quotientProjectionSchemeStackMap :
    schemeStack.{u, w} B S hS (Space.schemeSiteObject B hS hU) ⟶ 𝒵 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (schemeStackLift B S hS (Space.schemeSiteObject B hS hU))
      (BasedFunctor.comp
        (quotientStackProjectionHom (G.realization B hS hU hR hP)).hom b)))

/-- **The chart of an algebraic stack presented by a groupoid scheme with étale source map is
étale.** The projection of the quotient stack of the realization is étale in the sense of
**Stacks 04XB** by
`Stacks.Groupoids.GroupoidScheme.isRelativelyEtale_quotientStackProjection_realization`, and the
two transports of **Stacks 0457** carry that verdict across the equivalence with `𝒵` and down the
universe lift of the source; a 1-morphism of algebraic stacks representable by algebraic spaces
and étale in the sense of Stacks 04XB is étale in the sense of **Stacks 0CIL**. -/
theorem isEtale_quotientProjectionSchemeStackMap
    (hb : Functor.IsEquivalence b.toFunctor) (hs : Etale G.source.left) :
    IsEtale B S hS (quotientProjectionSchemeStackMap B S hS hU hR hP 𝒵 b) := by
  have := hb
  have hπ := Stacks.Groupoids.GroupoidScheme.isRelativelyEtale_quotientStackProjection_realization
    G B hS hU hR hP hs
  have hg := relativeProperty_comp_of_equivalence_target B S hS (Space.etaleMorphisms B S hS)
    (quotientStackProjectionHom (G.realization B hS hU hR hP)).hom b hπ
  have hf := relativeProperty_comp_of_equivalence_source B S hS (Space.etaleMorphisms B S hS)
    (schemeStackLift B S hS (Space.schemeSiteObject B hS hU))
    (BasedFunctor.comp
      (quotientStackProjectionHom (G.realization B hS hU hR hP)).hom b) hg
  refine AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS _ ⟨?_, hf⟩
  exact isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒵.property
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS
      (Space.schemeSiteObject B hS hU)) _

end Projection

section Division

variable {Gs Hsub : Stacks.Groupoids.GroupoidScheme S}
  {i : Stacks.Groupoids.GroupoidScheme.Hom Hsub Gs} {hobj : Hsub.objects = Gs.objects}
  (D : GroupoidScheme.Division Gs Hsub i hobj)
  (hU : B.Contains Gs.objects.left) (hR : B.Contains Gs.arrows.left)
  (hP : B.Contains (pullback Gs.source Gs.target).left)
  (𝒵 : AlgebraicStacks.{u, w} B S hS)
  (b : (quotientStack (Gs.realization B hS hU hR hP)) ⥤ᵇ 𝒵.val.val)

include b in
/-- **The quotient stack of the descended groupoid of a division is equivalent to the algebraic
stack the quotient stack of the divided groupoid is equivalent to.** The comparison is the
inverse of the equivalence of **Stacks 046T** supplied by
`Stacks.Groupoids.GroupoidScheme.nonempty_isEquivalenceOver_quotientStackMap_realizationHom`,
composed with the given equivalence. -/
theorem nonempty_basedFunctor_isEquivalence_descended_of_division
    (hb : Functor.IsEquivalence b.toFunctor) :
    Nonempty (Σ' c : (quotientStack
        (D.descended.realization B hS (D.contains_descended_objects B hU)
          (D.contains_descended_arrows B hR) (D.contains_descended_composablePairs B hR))) ⥤ᵇ
        𝒵.val.val,
      Functor.IsEquivalence c.toFunctor) := by
  have := hb
  obtain ⟨E⟩ :=
    Stacks.Groupoids.GroupoidScheme.nonempty_isEquivalenceOver_quotientStackMap_realizationHom
      D.descend B hS hU hR hP (D.contains_descended_objects B hU)
      (D.contains_descended_arrows B hR) (D.contains_descended_composablePairs B hR)
      D.descend_fullyFaithful D.flat_descend_mapObjects
      D.locallyOfFinitePresentation_descend_mapObjects D.surjective_descend_mapObjects
  have : Functor.IsEquivalence E.inv :=
    (CategoryTheory.Equivalence.mk _ E.inv E.unitIso.symm E.counitIso).isEquivalence_inverse
  exact ⟨⟨BasedFunctor.comp ⟨E.inv, E.inv_over⟩ b,
    Functor.isEquivalence_trans E.inv b.toFunctor⟩⟩

include b in
/-- **The conclusion of Stacks 06N0 from a division.** If the quotient stack of a groupoid scheme
is equivalent over the site to an algebraic stack `𝒵`, the ring of invariants of a division of
that groupoid scheme is a field and the source map of the descended groupoid is étale, then `𝒵`
admits an étale 1-morphism from the spectrum of a field.

The field spectrum is the quotient of the division, which is affine by the fourth conclusion of
**Stacks 04S4**, and the 1-morphism is
`AlgebraicGeometry.Stack.quotientProjectionSchemeStackMap` at the descended groupoid. -/
theorem exists_isEtale_fieldSpectrum_cover_of_division
    (hb : Functor.IsEquivalence b.toFunctor)
    (hfield : IsField Γ(D.quotient.left, ⊤))
    (hetS : Etale D.descended.source.left) :
    ∃ (F₀ : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F₀.base ⟶ 𝒵),
      IsEtale B S hS f := by
  classical
  obtain ⟨c, hc⟩ :=
    nonempty_basedFunctor_isEquivalence_descended_of_division B S hS D hU hR hP 𝒵 b hb
  have : IsAffine D.quotient.left := D.quotient_affine
  let : Field Γ(D.quotient.left, ⊤) := hfield.toField
  refine ⟨{ carrier := Γ(D.quotient.left, ⊤)
            base := Space.schemeSiteObject B hS (D.contains_descended_objects B hU)
            isSpec := (eqToIso (congrArg (fun T : Over S => T.left) D.descended_objects)).trans
              D.quotient.left.isoSpec },
    quotientProjectionSchemeStackMap B S hS (D.contains_descended_objects B hU)
      (D.contains_descended_arrows B hR) (D.contains_descended_composablePairs B hR) 𝒵 c, ?_⟩
  exact isEtale_quotientProjectionSchemeStackMap B S hS (D.contains_descended_objects B hU)
    (D.contains_descended_arrows B hR) (D.contains_descended_composablePairs B hR) 𝒵 c hc hetS

end Division

section Cover

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The hypothesis of Stacks 04WY at a field-valued point which is surjective, flat and locally
of finite presentation.** Every algebraic space representing a base change of `ξ` along a
scheme-valued point of `𝒵` has surjective, flat and locally finitely presented structural
morphism.

The three conjuncts are the relative-property readings of **Stacks 04XI** for surjectivity and of
**Stacks 06FM** for flatness and local finite presentation, the latter two from the smooth-diagram
conditions of **Stacks 06PW** and **Stacks 06Q2** part (1). -/
theorem relativeProperty_surjective_flat_locallyOfFinitePresentation_of_fieldSpectrumCover
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (W : BigFppfOver B S hS)
    (ξ : schemeStack.{u, w} B S hS W ⟶ 𝒵)
    (hsurj : IsSurjective B S hS ξ)
    (hflat : AlgebraicStacks.IsFlat B S hS ξ)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS ξ) :
    ∀ (T : BigFppfOver B S hS)
      (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒵.val.val.obj)
      (_hy : y ⋙ 𝒵.val.val.p = Over.map T.hom)
      (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B T.left.1 T.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map T.hom)
          (schemeStack.{u, w} B S hS W).val.val.p 𝒵.val.val.p y
          (CatFiberedInGroupoids.homFunctor ξ.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let a := algebraicSpaceMap B S hS T
        ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)
      Space.IsSurjective B S hS a.hom ∧ Space.IsFlat B S hS a.hom ∧
        Space.IsLocallyOfFinitePresentation B S hS a.hom) := by
  have hξrep : IsRepresentableByAlgebraicSpaces B S hS ξ.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒵.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) ξ.hom
  intro T y hy F hF hE
  refine ⟨?_, ?_, ?_⟩
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS ξ hξrep).mp hsurj
      T y hy F hF hE
  · exact hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) ξ.hom hξrep
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS ξ).1 hflat)
      T y hy F hF hE
  · exact hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) ξ.hom hξrep
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        (schemeStack.{u, w} B S hS W).property 𝒵.property ξ.hom).1 hlfp)
      T y hy F hF hE

/-- **The quotient stack of the realization of the de-realization of a groupoid in algebraic
spaces is equivalent to whatever the quotient stack of the groupoid is equivalent to.** The
comparison is the inverse of the equivalence induced by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.realizationIso`, composed with the given
equivalence. -/
theorem nonempty_basedFunctor_isEquivalence_realization_derealization
    (G : GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS))
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable]
    (hU : B.Contains (GroupoidInAlgebraicSpaces.derealization G).objects.left)
    (hR : B.Contains (GroupoidInAlgebraicSpaces.derealization G).arrows.left)
    (hP : B.Contains (pullback (GroupoidInAlgebraicSpaces.derealization G).source
      (GroupoidInAlgebraicSpaces.derealization G).target).left)
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (a : (quotientStack G) ⥤ᵇ 𝒵.val.val)
    (ha : Functor.IsEquivalence a.toFunctor) :
    Nonempty (Σ' c : (quotientStack
        ((GroupoidInAlgebraicSpaces.derealization G).realization B hS hU hR hP)) ⥤ᵇ 𝒵.val.val,
      Functor.IsEquivalence c.toFunctor) := by
  have := ha
  obtain ⟨E⟩ :=
    nonempty_isEquivalenceOver_quotientStackMap_of_iso
      (GroupoidInAlgebraicSpaces.realizationIso G hU hR hP)
  have : Functor.IsEquivalence E.inv :=
    (CategoryTheory.Equivalence.mk _ E.inv E.unitIso.symm E.counitIso).isEquivalence_inverse
  exact ⟨⟨BasedFunctor.comp ⟨E.inv, E.inv_over⟩ a,
    Functor.isEquivalence_trans E.inv a.toFunctor⟩⟩

/-- **The canonical 1-morphism out of the quotient stack of the self-intersection groupoid of a
surjective, flat, locally finitely presented field-valued point is an equivalence.** This is
**Stacks 04WY** at that point, with its hypothesis read off the three properties of the point by
`…relativeProperty_surjective_flat_locallyOfFinitePresentation_of_fieldSpectrumCover`. -/
theorem nonempty_basedFunctor_isEquivalence_canonicalMap_pointGroupoid
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (ξ : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (Rsp : AlgebraicSpaces B S hS)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
      (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)
    (hsurj : IsSurjective B S hS ξ)
    (hflat : AlgebraicStacks.IsFlat B S hS ξ)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS ξ) :
    Nonempty (Σ' a : (quotientStack
        (SelfIntersection.pointGroupoid B S hS F.base ξ Rsp eR)) ⥤ᵇ 𝒵.val.val,
      Functor.IsEquivalence a.toFunctor) := by
  obtain ⟨E⟩ :=
    SelfIntersection.nonempty_isEquivalenceOver_canonicalMap.{u, w}
      (B := B) (S := S) (hS := hS)
      (𝒰 := (schemeStack.{u, w} B S hS F.base).val) (𝒳 := 𝒵.val) (f := ξ.hom)
      (U := AlgebraicGeometry.schemeSpace F.base) (R := Rsp)
      (representedChart B S hS F.base) eR 𝒵.property
      (relativeProperty_surjective_flat_locallyOfFinitePresentation_of_fieldSpectrumCover
        B S hS F.base ξ hsurj hflat hlfp)
  exact ⟨⟨(SelfIntersection.selfIntersectionPresentation (B := B) (S := S) (hS := hS)
      (𝒰 := (schemeStack.{u, w} B S hS F.base).val) (𝒳 := 𝒵.val) (f := ξ.hom.hom)
      (U := AlgebraicGeometry.schemeSpace F.base) (R := Rsp)
      (representedChart B S hS F.base) eR 𝒵.property).canonicalMap,
    (CategoryTheory.Equivalence.mk _ E.inv E.unitIso.symm E.counitIso).isEquivalence_functor⟩⟩

include hZ in
/-- **A DM algebraic stack with a surjective, flat, locally finitely presented field-valued point
has an étale one.** This is the whole of **Stacks 06N0** after its first step: the groupoid of the
flat presentation is divided by the open subgroupoid through the identity, and the quotient, the
spectrum of the field of invariants, is étale over the stack. -/
theorem exists_isEtale_fieldSpectrum_cover_of_flat_fieldSpectrum_cover
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (hDM : IsDMOver B S hS 𝒵)
    (F : FieldSpectrum B S hS) (ξ : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (hsurj : IsSurjective B S hS ξ)
    (hflat : AlgebraicStacks.IsFlat B S hS ξ)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS ξ) :
    ∃ (F₀ : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F₀.base ⟶ 𝒵),
      IsEtale B S hS f := by
  classical
  -- an algebraic space representing the self-intersection of `ξ`
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS (schemeStack.{u, w} B S hS F.base).val 𝒵.val ξ.hom.hom 𝒵.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base)
  let Rsp : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
      (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p := eR₀
  -- the two auxiliary hypotheses of the division
  have hqDM : IsQuasiDMOver B S hS 𝒵 :=
    AlgebraicStacks.isQuasiDM_of_isDM B S hS (f := structureMorphism B S hS 𝒵) hDM
  have hlft : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp
  have := SelfIntersection.isRepresentable_objects_pointGroupoid_fieldSpectrum B S hS F ξ Rsp eR
  have := SelfIntersection.isRepresentable_arrows_pointGroupoid_fieldSpectrum
    B S hS F ξ Rsp eR hZ hqDM hlft
  -- the containments of the object and arrow schemes in the site
  have hU : B.Contains
      (SelfIntersection.pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ hqDM
        hlft).objects.left :=
    Space.contains_representingScheme B hS
      (SelfIntersection.pointGroupoid B S hS F.base ξ Rsp eR).objects.obj
  have hR : B.Contains
      (SelfIntersection.pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ hqDM
        hlft).arrows.left :=
    Space.contains_representingScheme B hS
      (SelfIntersection.pointGroupoid B S hS F.base ξ Rsp eR).arrows.obj
  have hP : B.Contains (pullback
      (SelfIntersection.pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ hqDM hlft).source
      (SelfIntersection.pointGroupoidScheme_fieldSpectrum B S hS F ξ Rsp eR hZ hqDM
        hlft).target).left :=
    B.contains_pullback_left _ _ hR hR
  -- the division of Stacks 04S4 by the open subgroupoid through the identity
  obtain ⟨P, D, -, hfield, -, hetS, -⟩ :=
    SelfIntersection.exists_division_identityArrowOpens_etale_pointGroupoid
      B S hS F ξ Rsp eR hZ hqDM hlft hDM hflat hlfp
      ((SelfIntersection.derealizationObjectsIsoSpec B S hS F ξ Rsp eR hZ hqDM hlft).inv.base
        (IsLocalRing.closedPoint F.carrier))
  -- the equivalence of the quotient stack of the groupoid scheme with `𝒵`
  obtain ⟨a, ha⟩ := nonempty_basedFunctor_isEquivalence_canonicalMap_pointGroupoid
    B S hS 𝒵 F ξ Rsp eR hsurj hflat hlfp
  obtain ⟨c, hc⟩ := nonempty_basedFunctor_isEquivalence_realization_derealization
    B S hS (SelfIntersection.pointGroupoid B S hS F.base ξ Rsp eR) hU hR hP a ha
  exact exists_isEtale_fieldSpectrum_cover_of_division B S hS D hU hR hP 𝒵 c hc hfield hetS

end Cover

end AlgebraicGeometry.Stack

end

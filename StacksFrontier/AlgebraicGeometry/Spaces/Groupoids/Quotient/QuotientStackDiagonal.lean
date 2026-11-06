module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquareDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFlatCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothQuotientStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal

/-!
# The atlas and the diagonal of a model of a quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, and let `𝒳` be an algebraic stack equivalent over the site to its
quotient stack `[U/R]` (Stacks 044Q), the atlas `U ⟶ [U/R] ≃ 𝒳` of Stacks 044R being
`AlgebraicGeometry.Stack.quotientStackModelProjection`. This file proves the two facts about that
atlas which the source draws from Criteria for Representability:

* **Stacks 04M9 on the model.** The self-intersection `U ×_𝒳 U` is represented by the arrow space
  `R`, its two projections inducing `s` and `t`.
* **Stacks 06FH on the model.** If `s` and `t` are flat and locally of finite presentation, the
  atlas is representable by algebraic spaces, surjective, flat and locally of finite
  presentation.

and, for a groupoid over `S` itself, the comparison of the diagonal of `𝒳` with the relation that
the proof of Stacks 0DTY makes: `Δ_𝒳` has a property of Properties of Stacks, Section 04XB exactly
when `(t, s) : R ⟶ U ×_S U` has it (Stacks 04M9 at the diagonal and Stacks 04XD).

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackModelArrowComparison`: the functor from the category of
  the arrow space to the 2-fibre product `U ×_𝒳 U` which sends an arrow to its source, its target
  and the isomorphism of Stacks 044S between their images.
* `AlgebraicGeometry.Stack.quotientStackModelArrowEquivalenceOver`: the resulting identification
  of `U ×_𝒳 U` with the category of the arrow space, over the site.

## Main results

* `AlgebraicGeometry.Stack.localEssSurj_quotientStackModelProjection`: the atlas is locally
  essentially surjective.
* `AlgebraicGeometry.Stack.isEquivalence_quotientStackModelArrowComparison`: **Stacks 04M9** on
  the model.
* `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackModelProjection`: every relative
  property of `s` passes to the atlas.
* `AlgebraicGeometry.Stack.quotientModelAtlasFppf`: **Stacks 06FH** on the model, in the form
  `AlgebraicGeometry.Stack.QuotientModelAtlasFppf`.
* `AlgebraicGeometry.Stack.isTerminal_of_equivalenceOver_terminalCFG`: a presheaf representing
  the final category fibred in groupoids is a final presheaf.
* `AlgebraicGeometry.Stack.hasRelativeProperty_diagonal_iff_sourceTarget`: the diagonal of the
  model has a property exactly when `(t, s)` has it.

## Implementation notes

The comparison functor is assembled from Stacks 04M9 as it is formalized,
`AlgebraicGeometry.Stack.arrowToRelativeProduct` together with
`AlgebraicGeometry.Stack.isEquivalence_arrowToRelativeProduct`, which compare the arrow space with
the 2-fibre product of the projection with itself *over the quotient stack and with the morphism
universe raised*. Lowering the universe of the two factors is
`CategoryTheory.TwoFibreProductOver.precomposeFst` and `precomposeSnd` along the universe lift,
and replacing the quotient stack by `𝒳` is `CategoryTheory.TwoFibreProductOver.mapBase` along the
fully faithful forward functor of the equivalence; each is an equivalence, and the composite sends
an arrow to its source and its target on the nose, so that the two projections of `U ×_𝒳 U`
induce `s` and `t` by `AlgebraicGeometry.Stack.representingMap_congr_obj`.

The atlas is locally essentially surjective with no hypothesis on the groupoid: this is part (1)
of Stacks 044X, `AlgebraicGeometry.Stack.localEssSurj_quotientStackProjectionHom`, carried
through the equivalence. That is all Stacks 045D needs, so the descent of a property from `s` to
the atlas, and from `(t, s)` to the diagonal, uses no flatness; flatness and local finite
presentation of `s` enter Stacks 06FH only as the properties being transported.

For the diagonal, the product `U × U` of the site is identified with `U ×_S U`: both are pullbacks
over a final presheaf, the representing presheaf of the final category fibred in groupoids being
final by `AlgebraicGeometry.Stack.isTerminal_of_equivalenceOver_terminalCFG`.

## References

* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

section RepresentingMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The induced morphism of representing presheaves only sees objects.** Two 1-morphisms of
categories fibred in groupoids which agree on objects induce the same morphism of representing
presheaves (Stacks 04SW): the latter is determined by the sections named by the images of
objects. -/
theorem representingMap_congr_obj
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    {a b : 𝒜 ⟶ 𝒞} (h : ∀ z, a.hom.obj z = b.hom.obj z) :
    representingMap B S hS 𝒜 𝒞 F H eF eH a = representingMap B S hS 𝒜 𝒞 F H eF eH b := by
  refine morphismSpaceEquiv_eq_of_sectionOfObj B S hS 𝒜 𝒞 F H eF eH _ _ (fun z W hz => ?_)
  rw [morphismSpaceEquiv_app_sectionOfObj]
  have key : ∀ (y y' : 𝒞.val.obj) (_ : y = y') (h₁ : 𝒞.val.p.obj y = W)
      (h₂ : 𝒞.val.p.obj y' = W),
      PresheafOfCategories.sectionOfObj eH y h₁ = PresheafOfCategories.sectionOfObj eH y' h₂ := by
    rintro y _ rfl _ _
    rfl
  exact key _ _ (h z).symm _ _

end RepresentingMap

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (e : StacksRepresentableCFG.EquivalenceOver (quotientStack G).p 𝒳.val.val.p)

attribute [local implicit_reducible] BasedFunctor.comp

/-- **The comparison functor of Stacks 04M9 on a model of `[U/R]`.** It sends an object of the
category of the arrow space over `T`, that is an arrow `r` of the groupoid over `T`, to the object
`(s r, t r, φ_r)` of the 2-fibre product `U ×_𝒳 U` of the atlas with itself, where `φ_r` is the
isomorphism of Stacks 044S between the images of `s r` and `t r`, carried to `𝒳`. -/
noncomputable def quotientStackModelArrowComparison :
    (fibredCategory B S hS G.arrows.obj).val.obj ⥤
      TwoFibreProductOver (fibredCategory B S hS G.objects.obj).val.p
        (fibredCategory B S hS G.objects.obj).val.p 𝒳.val.val.p
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom.toFunctor
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom.toFunctor :=
  (ULiftHom.up : _ ⥤ ULiftHom.{u + 1} _) ⋙ arrowToRelativeProduct G ⋙
    TwoFibreProductOver.precomposeSnd (pT := (liftedFibredCategory G.objects).p)
      (p𝒜' := (liftedFibredCategory G.objects).p)
      (p𝒜 := (fibredCategory B S hS G.objects.obj).val.p) (pℬ := (quotientStack G).p)
      (liftedQuotientStackProjection G).toFunctor (quotientStackProjection G).toFunctor
      (liftedFibredCategoryDown G.objects).toFunctor rfl ⋙
    TwoFibreProductOver.precomposeFst (liftedFibredCategory G.objects).p
      (fibredCategory B S hS G.objects.obj).val.p (fibredCategory B S hS G.objects.obj).val.p
      (quotientStack G).p (quotientStackProjection G).toFunctor
      (quotientStackProjection G).toFunctor (liftedFibredCategoryDown G.objects).toFunctor rfl ⋙
    TwoFibreProductOver.mapBase (pT := (fibredCategory B S hS G.objects.obj).val.p)
      (p𝒜 := (fibredCategory B S hS G.objects.obj).val.p)
      (quotientStackProjection G).toFunctor (quotientStackProjection G).toFunctor
      e.hom.functor e.hom.w

/-- The comparison functor lies strictly over the site. -/
theorem quotientStackModelArrowComparison_comp_structureFunctor :
    quotientStackModelArrowComparison G 𝒳 e ⋙ TwoFibreProductOver.structureFunctor _ _ _ _ _ =
      (fibredCategory B S hS G.arrows.obj).val.p :=
  rfl

/-- **Stacks 04M9 on a model of `[U/R]`.** The comparison functor from the category of the arrow
space to the 2-fibre product `U ×_𝒳 U` of the atlas with itself is an equivalence. -/
instance isEquivalence_quotientStackModelArrowComparison :
    (quotientStackModelArrowComparison G 𝒳 e).IsEquivalence := by
  have hlift : (liftedFibredCategory G.objects).p.IsFiberedInGroupoids :=
    isFiberedInGroupoids_uliftHom _ (fibredCategory B S hS G.objects.obj).property
  have hfib : (fibredCategory B S hS G.objects.obj).val.p.IsFiberedInGroupoids :=
    (fibredCategory B S hS G.objects.obj).property
  have h1 : (ULiftHom.up : (fibredCategory B S hS G.arrows.obj).val.obj ⥤
      ULiftHom.{u + 1} _).IsEquivalence := ULiftHom.equiv.isEquivalence_functor
  have h2 := isEquivalence_arrowToRelativeProduct G
  have h3 := TwoFibreProductOver.isEquivalence_precomposeSnd
    (pT := (liftedFibredCategory G.objects).p) (pℬ := (quotientStack G).p)
    (G := (liftedQuotientStackProjection G).toFunctor) (F := (quotientStackProjection G).toFunctor)
    (a := (liftedFibredCategoryDown G.objects).toFunctor) hlift hlift hfib rfl
    (quotientStackProjection G).w
  have h4 := TwoFibreProductOver.isEquivalence_precomposeFst (liftedFibredCategory G.objects).p
      (fibredCategory B S hS G.objects.obj).val.p (fibredCategory B S hS G.objects.obj).val.p
      (quotientStack G).p (quotientStackProjection G).toFunctor
      (quotientStackProjection G).toFunctor (liftedFibredCategoryDown G.objects).toFunctor rfl
      hfib hlift hfib inferInstance (quotientStackProjection G).w
  have : e.hom.functor.IsEquivalence := e.toEquivalence.isEquivalence_functor
  have h5 := TwoFibreProductOver.isEquivalence_mapBase
    (pT := (fibredCategory B S hS G.objects.obj).val.p)
    (p𝒜 := (fibredCategory B S hS G.objects.obj).val.p)
    (G := (quotientStackProjection G).toFunctor) (F := (quotientStackProjection G).toFunctor)
    e.hom.w
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h1
    (@Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h2
      (@Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h3
        (@Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h4 h5)))

/-- **The source component of the comparison** is the source map. -/
theorem quotientStackModelArrowComparison_obj_x
    (z : (fibredCategory B S hS G.arrows.obj).val.obj) :
    ((quotientStackModelArrowComparison G 𝒳 e).obj z).x =
      (associatedMap B S hS G.source.hom).1.hom.obj z :=
  rfl

/-- **The target component of the comparison** is the target map. -/
theorem quotientStackModelArrowComparison_obj_y
    (z : (fibredCategory B S hS G.arrows.obj).val.obj) :
    ((quotientStackModelArrowComparison G 𝒳 e).obj z).y =
      (associatedMap B S hS G.target.hom).1.hom.obj z :=
  rfl

/-- **The atlas of a model of the quotient stack is locally essentially surjective.** -/
theorem localEssSurj_quotientStackModelProjection (U : BigFppfOver B S hS)
    (q : 𝒳.val.val.p.Fiber U) :
    ∃ R ∈ BigFppfOver.topology B S hS U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ z : (fibredCategory B S hS G.objects.obj).val.obj,
          ∃ φ : (CatFiberedInGroupoids.homFunctor
              (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom).obj z ⟶ q.1,
            𝒳.val.val.p.IsHomLift k φ := by
  have hy : (quotientStack G).p.obj (e.inv.functor.obj q.1) = U :=
    (Functor.congr_obj e.inv.w q.1).trans q.2
  obtain ⟨R, hR, h⟩ := localEssSurj_quotientStackProjectionHom G U ⟨e.inv.functor.obj q.1, hy⟩
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨z, φ, hφ⟩ := h hk
  refine ⟨ULiftHom.objDown.{u + 1, u + 1} z, e.hom.functor.map φ ≫ e.counitIso.hom.app q.1, ?_⟩
  have h1 : 𝒳.val.val.p.IsHomLift k (e.hom.functor.map φ) :=
    Functor.isHomLift_map_of_comp_eq e.hom.w k φ
  have h2 : 𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj q.1)) (e.counitIso.hom.app q.1) :=
    e.isHomLift_counitIso_hom_app q.1
  exact IsHomLift.comp_lift_id_right' 𝒳.val.val.p k (e.hom.functor.map φ) (𝒳.val.val.p.obj q.1)
    (e.counitIso.hom.app q.1)

/-- The comparison functor is an equivalence over the site, in the sense of Stacks 003Z (2). -/
theorem nonempty_isEquivalenceOver_quotientStackModelArrowComparison :
    Nonempty (Functor.IsEquivalenceOver (fibredCategory B S hS G.arrows.obj).val.p
      (twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom).val.p
      (quotientStackModelArrowComparison G 𝒳 e)) := by
  obtain ⟨F, hF, eu, ec, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over _ _
    (fibredCategory B S hS G.arrows.obj).property
    (twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom).property
    _ (quotientStackModelArrowComparison_comp_structureFunctor G 𝒳 e)
    (isEquivalence_quotientStackModelArrowComparison G 𝒳 e)
  refine ⟨⟨F, hF, eu, ec, fun X => ?_, fun Y => ?_⟩⟩
  · have hx : (fibredCategory B S hS G.arrows.obj).val.p.obj
        ((quotientStackModelArrowComparison G 𝒳 e ⋙ F).obj X) =
          (fibredCategory B S hS G.arrows.obj).val.p.obj X :=
      (Functor.congr_obj hF _).trans
        (Functor.congr_obj (quotientStackModelArrowComparison_comp_structureFunctor G 𝒳 e) X)
    exact (congrArg (fun U => (fibredCategory B S hS G.arrows.obj).val.p.IsHomLift (𝟙 U)
      (eu.hom.app X)) hx).mpr (hη X)
  · have hy : (twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom).val.p.obj
          ((F ⋙ quotientStackModelArrowComparison G 𝒳 e).obj Y) =
        (twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom).val.p.obj Y :=
      (Functor.congr_obj (quotientStackModelArrowComparison_comp_structureFunctor G 𝒳 e)
        (F.obj Y)).trans (Functor.congr_obj hF Y)
    exact (congrArg (fun U => (twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom).val.p.IsHomLift (𝟙 U)
      (ec.hom.app Y)) hy).mpr (hε Y)

/-- **Stacks 04M9 on a model of the quotient stack.** The self-intersection
`U ×_𝒳 U` of the atlas of a model `𝒳` of `[U/R]` is represented by the arrow space `R`, through
an equivalence over the site whose backward functor is the comparison functor. -/
noncomputable def quotientStackModelArrowEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom).val.p
      (presheafOfCategories (G.arrows.obj ⋙ typeToCat)).p :=
  (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (quotientStackModelArrowComparison_comp_structureFunctor G 𝒳 e)
    (nonempty_isEquivalenceOver_quotientStackModelArrowComparison G 𝒳 e).some).symm

/-- The backward functor of `quotientStackModelArrowEquivalenceOver` is the comparison
functor. -/
theorem quotientStackModelArrowEquivalenceOver_inv_functor :
    (quotientStackModelArrowEquivalenceOver G 𝒳 e).inv.functor =
      quotientStackModelArrowComparison G 𝒳 e :=
  rfl

/-- A 1-morphism out of the self-intersection of the atlas which agrees on objects with the
comparison followed by `associatedMap f` induces `f`. -/
private theorem representingMap_eq_of_obj_eq
    (f : G.arrows.obj ⟶ G.objects.obj)
    (m : twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom ⟶
      fibredCategory B S hS G.objects.obj)
    (hm : ∀ z, m.hom.obj ((quotientStackModelArrowComparison G 𝒳 e).obj z) =
      (associatedMap B S hS f).1.hom.obj z) :
    representingMap B S hS _ _ G.arrows.obj G.objects.obj
      (quotientStackModelArrowEquivalenceOver G 𝒳 e)
      (StacksRepresentableCFG.EquivalenceOver.refl _) m = f := by
  have h₁ := representingMap_comp B S hS G.arrows.obj G.arrows.obj G.objects.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _) (quotientStackModelArrowEquivalenceOver G 𝒳 e)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (equivalenceOverInvMap B S hS G.arrows.obj (quotientStackModelArrowEquivalenceOver G 𝒳 e)) m
  rw [representingMap_equivalenceOverInvMap, Category.id_comp] at h₁
  rw [← h₁, ← representingMap_associatedMap B S hS G.arrows.obj G.objects.obj f]
  exact representingMap_congr_obj _ _ _ _ hm

/-- **A 1-morphism out of the self-intersection of the atlas which takes the first component
induces the source map** of the groupoid, the self-intersection being represented by `R` through
`quotientStackModelArrowEquivalenceOver`. -/
theorem representingMap_eq_source_of_obj_eq
    (m : twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom ⟶
      fibredCategory B S hS G.objects.obj)
    (hm : ∀ P, m.hom.obj P = P.x) :
    representingMap B S hS _ _ G.arrows.obj G.objects.obj
      (quotientStackModelArrowEquivalenceOver G 𝒳 e)
      (StacksRepresentableCFG.EquivalenceOver.refl _) m = G.source.hom :=
  representingMap_eq_of_obj_eq G 𝒳 e _ m fun _ => hm _

/-- **A 1-morphism out of the self-intersection of the atlas which takes the second component
induces the target map** of the groupoid. -/
theorem representingMap_eq_target_of_obj_eq
    (m : twoFibreProduct B S hS 𝒳.val (fibredCategory B S hS G.objects.obj)
        (fibredCategory B S hS G.objects.obj)
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom
        (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom ⟶
      fibredCategory B S hS G.objects.obj)
    (hm : ∀ P, m.hom.obj P = P.y) :
    representingMap B S hS _ _ G.arrows.obj G.objects.obj
      (quotientStackModelArrowEquivalenceOver G 𝒳 e)
      (StacksRepresentableCFG.EquivalenceOver.refl _) m = G.target.hom :=
  representingMap_eq_of_obj_eq G 𝒳 e _ m fun _ => hm _

/-- **The atlas of a model of `[U/R]` is representable by algebraic spaces**: its source is an
algebraic space and its target an algebraic stack. -/
theorem isRepresentableByAlgebraicSpaces_quotientStackModelProjection :
    IsRepresentableByAlgebraicSpaces B S hS
      (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS _ G.objects.property) _

/-- **Every relative property of the source map passes to the atlas of a model of `[U/R]`.** Let
`P` be a property of morphisms of algebraic spaces over `S` which is stable under base change and
local at the target for the fppf topology. If the source map `s : R ⟶ U` has `P`, then the atlas
`U ⟶ [U/R]`, read on an algebraic stack `𝒳` equivalent to `[U/R]`, has `P` in the sense of
Stacks 03YK.

The atlas is locally essentially surjective and its self-intersection is represented by `R` with
first projection `s` (Stacks 04M9), so Stacks 045D applies. -/
theorem hasRelativeProperty_quotientStackModelProjection
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hP : P G.source) :
    HasRelativeProperty B S hS P (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom
      (isRepresentableByAlgebraicSpaces_quotientStackModelProjection G 𝒳 e) := by
  refine hasRelativeProperty_of_prop_representingMap_of_localEssSurj B S hS P _ _ _ _ _ _
    (localEssSurj_quotientStackModelProjection G 𝒳 e)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom
      (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    G.arrows.obj G.objects.obj G.arrows.property G.objects.property
    (quotientStackModelArrowEquivalenceOver G 𝒳 e)
    (StacksRepresentableCFG.EquivalenceOver.refl _) ?_
  have h := representingMap_eq_source_of_obj_eq G 𝒳 e
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom
      (quotientStackModelProjection.{u, w} B S hS A G 𝒳 e).hom).fst (fun _ => rfl)
  have hP' : P (ObjectProperty.homMk G.source.hom :
      (⟨G.arrows.obj, G.arrows.property⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨G.objects.obj, G.objects.property⟩) := hP
  exact h ▸ hP'

/-- **Stacks 06FH on a model of `[U/R]`.** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces
over `S` whose source and target are flat and locally of finite presentation, and let `𝒳` be an
algebraic stack equivalent over the site to `[U/R]`. Then the atlas `U ⟶ [U/R] ≃ 𝒳` is
representable by algebraic spaces, surjective, flat and locally of finite presentation.

Surjectivity needs no hypothesis (the identity arrow at a point is a preimage under `s`), and
groupoid inversion identifies `s` with `t`, so only the hypotheses on `s` are used. -/
theorem quotientModelAtlasFppf
    (hsFlat : Space.IsFlat B S hS G.source.hom) (_htFlat : Space.IsFlat B S hS G.target.hom)
    (hsLfp : Space.IsLocallyOfFinitePresentation B S hS G.source.hom)
    (_htLfp : Space.IsLocallyOfFinitePresentation B S hS G.target.hom) :
    QuotientModelAtlasFppf.{u, w} B S hS A G 𝒳 e := by
  have hrep := isRepresentableByAlgebraicSpaces_quotientStackModelProjection G 𝒳 e
  have h𝒰 := isAlgebraicStack_fibredCategory.{u, w} B S hS _ G.objects.property
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  refine ⟨hrep, ?_, ?_, ?_⟩
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS _ hrep).2
      (hasRelativeProperty_quotientStackModelProjection G 𝒳 e _
        (QuotientAtlas.isSurjective_source G))
  · exact (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) h𝒰 𝒳.property _ hrep).2
      (hasRelativeProperty_quotientStackModelProjection G 𝒳 e _ hsFlat)
  · exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      h𝒰 𝒳.property _).2
      ((hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        h𝒰 𝒳.property _ hrep).2
        (hasRelativeProperty_quotientStackModelProjection G 𝒳 e _ hsLfp))

end Comparison

section Terminal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A presheaf representing the final object of the 2-category is a final presheaf.** Every
section over `V` is named by the unique object of the fibre of the final object over `V`. -/
noncomputable def isTerminal_of_equivalenceOver_terminalCFG
    (H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eH : StacksRepresentableCFG.EquivalenceOver (terminalCFG B S hS).val.p
      (presheafOfCategories (H ⋙ typeToCat)).p) :
    IsTerminal H := by
  have key : ∀ (V : BigFppfOver B S hS) (z : BigFppfOver B S hS)
      (hz : (terminalCFG B S hS).val.p.obj z = V),
      PresheafOfCategories.sectionOfObj eH z hz = PresheafOfCategories.sectionOfObj eH V rfl := by
    rintro V z rfl
    rfl
  have hsub : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (a b : H.obj V), a = b := by
    intro V a b
    have ha := PresheafOfCategories.sectionOfObj_inv_obj eH
      (⟨V.unop, Discrete.mk a⟩ : (presheafOfCategories (H ⋙ typeToCat)).obj)
    have hb := PresheafOfCategories.sectionOfObj_inv_obj eH
      (⟨V.unop, Discrete.mk b⟩ : (presheafOfCategories (H ⋙ typeToCat)).obj)
    exact (((key V.unop _ _).symm.trans ha).symm.trans ((key V.unop _ _).symm.trans hb))
  refine IsTerminal.ofUniqueHom
    (fun X => (Space.baseTerminal_yonedaIsTerminal B S hS).from X ≫
      yonedaEquiv.symm (PresheafOfCategories.sectionOfObj eH (Space.baseTerminal B S hS) rfl))
    (fun X m => ?_)
  ext V x
  exact hsub _ _ _

end Terminal

section Diagonal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (G : GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS))
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_QuotientStackDiagonal :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_QuotientStackDiagonal
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 04M9 and Stacks 04XD at the diagonal of `[U/R]`.** Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `S` and let `𝒳` be an algebraic stack equivalent over the site
to its quotient stack `[U/R]`. For a property `P` of morphisms of algebraic spaces over `S`
which is stable under base change and local at the target for the fppf topology, the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` has `P` in the sense of Properties of Stacks, Section 04XB exactly when
`(t, s) : R ⟶ U ×_S U` has `P`.

The base change of `Δ` along `U × U ⟶ 𝒳 × 𝒳` is `U ×_𝒳 U ⟶ U × U` (Stacks 02XE), which is
`(s, t) : R ⟶ U ×_S U` by Stacks 04M9; the atlas `U ⟶ 𝒳` is locally essentially surjective, so
Stacks 045D descends `P` along `U × U ⟶ 𝒳 × 𝒳`, and Stacks 045C carries it back. -/
theorem hasRelativeProperty_diagonal_iff_sourceTarget
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack G).p 𝒳.val.val.p)) :
    HasRelativeProperty B S hS P (diagonal.{u, u, u + 1} B S hS 𝒳.val)
        (isRepresentableByAlgebraicSpaces_diagonal_algebraicStack.{u, w} B S hS 𝒳) ↔
      P (GroupoidInAlgebraicSpaces.sourceTarget G) := by
  obtain ⟨e⟩ := hequiv
  have h𝒰 := isRepresentableByAlgebraicSpace_fibredCategory B S hS _ G.objects.property
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_product B S hS _ _ h𝒰 h𝒰
  obtain ⟨H, -, ⟨eH⟩⟩ := isRepresentableByAlgebraicSpace_terminalCFG B S hS
  let 𝒰 := fibredCategory B S hS G.objects.obj
  let π := (quotientStackModelProjection.{u, w} B S hS _ G 𝒳 e).hom
  let D := relativeDiagonalSquare.{u, u, u} B S hS 𝒰 𝒰 𝒳.val π π
  let t𝒰 : 𝒰 ⟶ terminalCFG B S hS := Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒰)
  let Q₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} t𝒰 t𝒰
  have : (twoFibreProductStructureFunctor B S hS 𝒰 𝒰 (terminalCFG B S hS) t𝒰 t𝒰).IsFibered :=
    Q₀.pt.property.isFibered
  have hpb := isPullback_representingMap_twoFibreProductSquare B S hS 𝒰 𝒰 (terminalCFG B S hS)
    G.objects.obj G.objects.obj H (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) eH t𝒰 t𝒰 W eW
  -- the two components of the representing morphism of `U ×_𝒳 U ⟶ U × U` are `s` and `t`
  let pr₁ : CatFiberedInGroupoids.product 𝒰 𝒰 ⟶ 𝒰 := Q₀.fst
  have hs := representingMap_comp B S hS G.arrows.obj W G.objects.obj
    (quotientStackModelArrowEquivalenceOver G 𝒳 e) eW
    (StacksRepresentableCFG.EquivalenceOver.refl _) D.fst pr₁
  rw [representingMap_eq_source_of_obj_eq G 𝒳 e (D.fst ≫ pr₁) (fun _ => rfl)] at hs
  let pr₂ : CatFiberedInGroupoids.product 𝒰 𝒰 ⟶ 𝒰 := Q₀.snd
  have ht := representingMap_comp B S hS G.arrows.obj W G.objects.obj
    (quotientStackModelArrowEquivalenceOver G 𝒳 e) eW
    (StacksRepresentableCFG.EquivalenceOver.refl _) D.fst pr₂
  rw [representingMap_eq_target_of_obj_eq G 𝒳 e (D.fst ≫ pr₂) (fun _ => rfl)] at ht
  -- `W` is the product `U ×_S U`, both being pullbacks over a final presheaf
  have hpb₂ : IsPullback
      (representingMap B S hS (CatFiberedInGroupoids.product 𝒰 𝒰) 𝒰 W G.objects.obj eW
        (StacksRepresentableCFG.EquivalenceOver.refl _) pr₁)
      (representingMap B S hS (CatFiberedInGroupoids.product 𝒰 𝒰) 𝒰 W G.objects.obj eW
        (StacksRepresentableCFG.EquivalenceOver.refl _) pr₂)
      G.objectsToBase.hom G.objectsToBase.hom := by
    have hT : IsTerminal H := isTerminal_of_equivalenceOver_terminalCFG H eH
    have tT := Space.baseTerminal_yonedaIsTerminal B S hS
    exact hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (hT.uniqueUpToIso tT)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (tT.hom_ext _ _) (tT.hom_ext _ _)
  let ι := hpb₂.isoIsPullback _ _
    (IsPullback.of_hasPullback G.objectsToBase.hom G.objectsToBase.hom).flip
  have hcomp : representingMap B S hS _ _ G.arrows.obj W
        (quotientStackModelArrowEquivalenceOver G 𝒳 e) eW D.fst ≫ ι.hom =
      (GroupoidInAlgebraicSpaces.sourceTarget G).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd, ← ht]
      exact (GroupoidInAlgebraicSpaces.sourceTarget_target_projection G).symm
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst, ← hs]
      exact (GroupoidInAlgebraicSpaces.sourceTarget_source_projection G).symm
  let ι' : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ≅ GroupoidInAlgebraicSpaces.objectPairs G :=
    ObjectProperty.isoMk _ ι
  have hcomp' : (ObjectProperty.homMk (representingMap B S hS _ _ G.arrows.obj W
      (quotientStackModelArrowEquivalenceOver G 𝒳 e) eW D.fst) :
        (⟨G.arrows.obj, G.arrows.property⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩) ≫ ι'.hom =
      GroupoidInAlgebraicSpaces.sourceTarget G :=
    ObjectProperty.hom_ext _ hcomp
  have key := MorphismProperty.cancel_right_of_respectsIso P (ObjectProperty.homMk
    (representingMap B S hS _ _ G.arrows.obj W
      (quotientStackModelArrowEquivalenceOver G 𝒳 e) eW D.fst) :
        (⟨G.arrows.obj, G.arrows.property⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩) ι'.hom
  rw [hcomp'] at key
  have hbridge := hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P D.fst
    (isRepresentableByAlgebraicSpaces_twoFibreProductProjection.{u, u, u} B S hS 𝒰 𝒰 𝒳.val π π
      (isRepresentableByAlgebraicSpaces_diagonal_algebraicStack.{u, w} B S hS 𝒳))
    G.arrows.obj W G.arrows.property hW (quotientStackModelArrowEquivalenceOver G 𝒳 e) eW
  exact ⟨fun hΔ => key.mpr (hbridge.mp (hasRelativeProperty_baseChange.{u, u, u} B S hS P 𝒳.val
      _ _ _ (CatFiberedInGroupoids.productMap π π) D
      (isTwoFibreProduct_relativeDiagonalSquare.{u, u, u} B S hS 𝒰 𝒰 𝒳.val π π) _ hΔ)),
    fun hP => hasRelativeProperty_diagonal_of_localEssSurj.{u, u} B S hS P 𝒰 𝒰 𝒳.val π π _
      (localEssSurj_quotientStackModelProjection G 𝒳 e)
      (localEssSurj_quotientStackModelProjection G 𝒳 e) (hbridge.mpr (key.mp hP))⟩

end Diagonal

end AlgebraicGeometry.Stack

end

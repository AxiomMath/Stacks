module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBigSitePullbackStack
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets

/-!
# Representability under an enlargement of the big fppf site (Stacks 04X2)

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and write `f`
for the morphism of sites that the localized inclusion determines. Stacks 04X2 says that a stack
over the localized big fppf site of `S` which is represented by an algebraic space `F` has inverse
image represented by `f⁻¹F`, and that one represented by a scheme `X` of the smaller site has
inverse image represented by the *same* scheme, read in the larger site.

Both come from Stacks 04WX. A category of elements is the quotient stack of the *identity*
groupoid on its object space, 04WX carries that quotient across the change of site, and the
inverse-image groupoid of an identity groupoid is again an identity groupoid — on the inverse image
of the object space. The scheme case is the algebraic-space case at the sheaf represented by the
scheme, together with Stacks 03FP, part (1) in its canonical form
`AlgebraicGeometry.changeBigSiteYonedaIso`.

## Main definitions

* `AlgebraicGeometry.Stack.identityGroupoid`: the identity groupoid on an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_quotientStack_of_discrete`: the quotient stack
  of a groupoid whose source and target agree and are isomorphisms is the category of elements of
  its object space.
* `AlgebraicGeometry.Stack.pullbackStack_equivalenceOfSpace`: **Stacks 04X2 for representability
  by an algebraic space.**
* `AlgebraicGeometry.Stack.pullbackStack_representableBy`: **Stacks 04X2 for representability by a
  scheme.**

## Implementation notes

The identity groupoid has the object and arrow space equal, both structure maps the identity, and
composition the first projection of the chosen fibre product; its pointwise groupoid is the
equality groupoid of the sections of the object space. Its quotient stack is the stackification of
the pointwise groupoid fibration, and the comparison with the category of elements is an
equivalence already before stackification — the fibres of both are discrete — so the quotient stack
is the stackification of the category of elements, which is itself a stack because an algebraic
space is an fppf sheaf (Stacks 0430, in the form
`AlgebraicGeometry.Stack.isStack_fibredCategory`).

The comparison of presentations is stated for a groupoid in presheaves whose source map is
pointwise injective and equal to its target, which is what the identity groupoid supplies and what
its inverse image supplies again: the inverse image of the identity of an algebraic space is the
identity of the inverse image, the inverse image being a functor.

## References

* [Stacks Project, Tag 0430](https://stacks.math.columbia.edu/tag/0430)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
* [Stacks Project, Tag 04X2](https://stacks.math.columbia.edu/tag/04X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] CategoryTheory.Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

/-- The groupoid structure on a type whose only arrows are the proofs of equality. -/
@[instance_reducible]
private def equalityGroupoid (α : Type u) : Groupoid.{u} α where
  Hom x y := ULift.{u} (PLift (x = y))
  id _ := ⟨⟨rfl⟩⟩
  comp f g := ⟨⟨f.down.down.trans g.down.down⟩⟩
  inv f := ⟨⟨f.down.down.symm⟩⟩

section Discrete

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **The identity groupoid on an algebraic space over `S`**: the object and arrow spaces are the
space itself, the source and target maps are the identity, and composition is the first projection
of the chosen fibre product. Its quotient stack is the category of elements of the space. -/
noncomputable def identityGroupoid (F : AlgebraicSpaces C S hS) :
    GroupoidInAlgebraicSpaces C S hS F where
  objects := F
  arrows := F
  objectsToBase := 𝟙 F
  arrowsToBase := 𝟙 F
  source := 𝟙 F
  target := 𝟙 F
  source_over := Category.id_comp _
  target_over := Category.id_comp _
  comp := ObjectProperty.homMk (pullback.fst (𝟙 F.obj) (𝟙 F.obj))
  comp_over := rfl
  pointwiseGroupoid T := by
    let E : ∀ x y : F.obj.obj T,
        (@Quiver.Hom _ (equalityGroupoid (F.obj.obj T)).toCategory.toQuiver x y) ≃
        {a : F.obj.obj T // a = x ∧ a = y} := fun x y =>
      { toFun := fun f => ⟨x, rfl, f.down.down⟩
        invFun := fun a => ⟨⟨a.property.1.symm.trans a.property.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun a => Subtype.ext a.property.1.symm }
    refine ⟨{ groupoid := equalityGroupoid (F.obj.obj T)
              arrowEquiv := E
              comp_eq := ?_ }⟩
    intro x y z g f
    change x = (composableToPullback (𝟙 F.obj) (𝟙 F.obj) ≫
      pullback.fst (𝟙 F.obj) (𝟙 F.obj)).app T _
    simp only [composableToPullback, pullback.lift_fst]
    exact g.down.down

/-- In a groupoid in presheaves whose source and target maps agree, every arrow of an evaluation
is an endomorphism. -/
private lemma evaluation_eq_of_hom {D : Type v} [Category.{w} D]
    (G : Deformation.GroupoidInFunctors.{v, w, u} D)
    (hst : G.source = G.target) (T : D) {x y : G.Evaluation T} (f : x ⟶ y) : x = y := by
  let a := G.evaluationArrowEquiv T x y f
  exact a.property.1.symm.trans ((congrArg (fun k => k.app T a.val) hst).trans a.property.2)

/-- In a groupoid in presheaves whose source map is pointwise injective, an evaluation has at most
one arrow between two objects. -/
private lemma evaluation_hom_ext {D : Type v} [Category.{w} D]
    (G : Deformation.GroupoidInFunctors.{v, w, u} D)
    (hs : ∀ T, Function.Injective (G.source.app T))
    (T : D) {x y : G.Evaluation T} (f g : x ⟶ y) : f = g :=
  (G.evaluationArrowEquiv T x y).injective <| Subtype.ext <| hs T <|
    (G.evaluationArrowEquiv T x y f).property.1.trans
      (G.evaluationArrowEquiv T x y g).property.1.symm

/-- The fibres of a category of elements are discrete, so two parallel arrows of a fibre agree. -/
private lemma discrete_fiber_hom_ext {D : Type v} [Category.{w} D] (F : Dᵒᵖ ⥤ Type u) (U : D)
    (x y : (F ⋙ typeToCat).toPseudofunctor'.obj ⟨op U⟩) (f g : x ⟶ y) : f = g :=
  @Subsingleton.elim (Discrete.mk x.as ⟶ Discrete.mk y.as) inferInstance f g

/-- The comparison from the pointwise groupoid fibration of a groupoid in presheaves whose source
and target agree to the category of elements of its object presheaf. -/
private noncomputable def presentationToElements {D : Type v} [Category.{w} D]
    (G : Deformation.GroupoidInFunctors.{v, w, u} Dᵒᵖ) (hst : G.source = G.target) :
    (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj ⥤
      (presheafOfCategories (G.objects ⋙ typeToCat)).obj where
  obj x := ⟨x.base, Discrete.mk x.fiber⟩
  map f := ⟨f.base, eqToHom (Discrete.ext (evaluation_eq_of_hom G hst _ f.fiber))⟩
  map_id _ := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl
    (discrete_fiber_hom_ext G.objects _ _ _ _ _)
  map_comp _ _ := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl
    (discrete_fiber_hom_ext G.objects _ _ _ _ _)

/-- The comparison back, available when the source map of the groupoid in presheaves is pointwise
injective. -/
private noncomputable def elementsToPresentation {D : Type v} [Category.{w} D]
    (G : Deformation.GroupoidInFunctors.{v, w, u} Dᵒᵖ)
    (hs : ∀ T, Function.Injective (G.source.app T)) :
    (presheafOfCategories (G.objects ⋙ typeToCat)).obj ⥤
      (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj where
  obj x := ⟨x.base, x.fiber.as⟩
  map f := ⟨f.base, eqToHom (Discrete.eq_of_hom f.fiber)⟩
  map_id _ := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl (evaluation_hom_ext G hs _ _ _)
  map_comp _ _ := Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl (evaluation_hom_ext G hs _ _ _)

/-- The comparison from the pointwise groupoid fibration to the category of elements is an
equivalence of categories, when the source map agrees with the target and is pointwise
injective: both categories have the same objects, and both have thin fibres. -/
private lemma isEquivalence_presentationToElements {D : Type v} [Category.{w} D]
    (G : Deformation.GroupoidInFunctors.{v, w, u} Dᵒᵖ) (hst : G.source = G.target)
    (hs : ∀ T, Function.Injective (G.source.app T)) :
    (presentationToElements G hst).IsEquivalence := by
  have hfaith : (presentationToElements G hst).Faithful := ⟨by
    intro x y f g hfg
    exact Pseudofunctor.CoGrothendieck.Hom.ext _ _ (congrArg (·.base) hfg)
      (evaluation_hom_ext G hs _ _ _)⟩
  have hfull : (presentationToElements G hst).Full :=
    ⟨fun k => ⟨(elementsToPresentation G hs).map k,
      Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl
        (discrete_fiber_hom_ext G.objects _ _ _ _ _)⟩⟩
  have hess : (presentationToElements G hst).EssSurj :=
    ⟨fun y => ⟨⟨y.base, y.fiber.as⟩, ⟨Iso.refl _⟩⟩⟩
  exact { }

/-- **The pointwise groupoid fibration of a groupoid in presheaves whose source and target agree
and whose source is pointwise injective is the category of elements of its object presheaf**, as
an equivalence over the base. -/
private theorem nonempty_presentationEquivalence {D : Type v} [Category.{w} D]
    (G : Deformation.GroupoidInFunctors.{v, w, u} Dᵒᵖ) (hst : G.source = G.target)
    (hs : ∀ T, Function.Injective (G.source.app T)) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (presheafOfGroupoids (evaluationGroupoidFunctor G)).p
      (presheafOfCategories (G.objects ⋙ typeToCat)).p) :=
  Functor.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_presheafOfGroupoids (evaluationGroupoidFunctor G)).isFibered
    (presentationToElements G hst) (isEquivalence_presentationToElements G hst hs) rfl

/-- **The quotient stack of a groupoid in algebraic spaces whose source and target agree and whose
source is an isomorphism is the category of elements of its object space**, as an equivalence over
the big fppf site of `S`.

The pointwise groupoid fibration is already the category of elements, and the category of elements
of an algebraic space is a stack, so stackifying changes nothing. -/
theorem nonempty_equivalenceOver_quotientStack_of_discrete {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) (hst : G.source = G.target) (hiso : IsIso G.source) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (quotientStack G).p
      (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p) := by
  let E0 : StacksRepresentableCFG.EquivalenceOver
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (quotientPrestack G).p :=
    { hom := ⟨(quotientPrestackEquivalence G).functor, quotientPrestackEquivalence_comp G⟩
      inv := ⟨(quotientPrestackEquivalence G).inverse, rfl⟩
      unitIso := (quotientPrestackEquivalence G).unitIso
      counitIso := (quotientPrestackEquivalence G).counitIso
      unit_over :=
        StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
      counit_over :=
        StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl }
  have hsinj : ∀ T, Function.Injective (G.toGroupoidInFunctors.source.app T) := by
    have hh : IsIso G.source.hom := (ObjectProperty.isIso_hom_iff G.source).2 hiso
    intro T
    exact (ConcreteCategory.bijective_of_isIso (G.source.hom.app T)).injective
  obtain ⟨E'⟩ := nonempty_presentationEquivalence G.toGroupoidInFunctors
    (congrArg (·.hom) hst) hsinj
  let EL : StacksRepresentableCFG.EquivalenceOver (liftedFibredCategory G.objects).p
      (fibredCategory C S hS G.objects.obj).val.p :=
    { hom := ⟨(liftedFibredCategoryDown G.objects).toFunctor,
        (liftedFibredCategoryDown G.objects).w⟩
      inv := ⟨(liftedFibredCategoryUp G.objects).toFunctor,
        (liftedFibredCategoryUp G.objects).w⟩
      unitIso := Iso.refl _
      counitIso := Iso.refl _
      unit_over :=
        StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
      counit_over :=
        StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl }
  exact ⟨(Functor.stageThreeEquivalenceOfEquivalence.{u, u + 1, u + 1, u + 1, u}
    (BigFppfOver.topology C S hS) (liftedFibredCategory_isStack G.objects)
    (E0.symm.trans (E'.trans EL.symm))).trans EL⟩

end Discrete

section ChangeOfSite

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B')

/-- **Stacks 04X2, representability by an algebraic space.** A stack over the localized big fppf
site of `S` represented by an algebraic space `F` has inverse image represented by the inverse
image of `F`, that is by `AlgebraicGeometry.changeBigSite` applied to `F`. -/
@[stacks 04X2 "representability by an algebraic space: the inverse image of a stack represented \
by an algebraic space is represented by the inverse image of that same algebraic space"]
theorem pullbackStack_equivalenceOfSpace (S : Scheme.{u}) (hS : B.Contains S)
    (F : AlgebraicSpaces B S hS) (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p
      (presheafOfCategories (F.obj ⋙ typeToCat)).p) :
    letI : 𝒳.p.IsFibered :=
      (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e
        (fibredCategory B S hS F.obj).property).isFibered
    Nonempty (StacksRepresentableCFG.EquivalenceOver (pullbackStack h S hS 𝒳).p
      (presheafOfCategories
        (((changeBigSite B B' h S hS).obj F).obj ⋙ typeToCat)).p) := by
  have hfib𝒳 : 𝒳.p.IsFibered :=
    (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e
      (fibredCategory B S hS F.obj).property).isFibered
  let G := identityGroupoid F
  obtain ⟨EQ⟩ := nonempty_equivalenceOver_quotientStack_of_discrete G rfl (IsIso.id F)
  obtain ⟨P⟩ := nonempty_equivalenceOver_pullbackStack_of_quotient h S hS
    (quotientStack G) 𝒳 (EQ.trans e.symm)
  obtain ⟨E04WX⟩ := isEquivalenceOver_changeBigSiteQuotientEquivalence B B' h S hS G
  have hiso' : IsIso (changeBigSiteGroupoid B B' h S hS G).source := by
    rw [show (changeBigSiteGroupoid B B' h S hS G).source =
      𝟙 ((changeBigSite B B' h S hS).obj F) from (changeBigSite B B' h S hS).map_id F]
    exact IsIso.id _
  obtain ⟨Q⟩ := nonempty_equivalenceOver_quotientStack_of_discrete
    (changeBigSiteGroupoid B B' h S hS G) rfl hiso'
  exact ⟨P.symm.trans
    ((StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (changeBigSiteQuotientEquivalenceFunctor_comp B B' h S hS G _) E04WX).symm.trans Q)⟩

/-- **Stacks 04X2, representability by a scheme.** A stack over the localized big fppf site of `S`
represented by a scheme `X` of the smaller site has inverse image represented by the *same*
scheme, read as an object of the larger localized site. -/
@[stacks 04X2 "representability by a scheme: the inverse image of a stack represented by a scheme \
of the smaller big fppf site is represented by that same scheme, read in the larger one"]
theorem pullbackStack_representableBy (S : Scheme.{u}) (hS : B.Contains S)
    (X : BigFppfOver B S hS) (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.RepresentableBy 𝒳.p X) :
    letI : 𝒳.p.IsFibered :=
      (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e
        (Functor.IsFiberedInGroupoids.over_forget X)).isFibered
    Nonempty (StacksRepresentableCFG.RepresentableBy (pullbackStack h S hS 𝒳).p
      ((inclusionOver h S hS).obj X : BigFppfOver B' S (largerContains h hS))) := by
  have hfib𝒳 : 𝒳.p.IsFibered :=
    (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e
      (Functor.IsFiberedInGroupoids.over_forget X)).isFibered
  obtain ⟨W⟩ := pullbackStack_equivalenceOfSpace h S hS ((schemeSpaceFunctor B S hS).obj X) 𝒳
    (e.trans (PresheafOfCategories.sliceElementsEquivalenceOver X))
  have EY : StacksRepresentableCFG.EquivalenceOver
      (Over.forget ((inclusionOver h S hS).obj X : BigFppfOver B' S (largerContains h hS)))
      (presheafOfCategories (yoneda.obj
        ((inclusionOver h S hS).obj X : BigFppfOver B' S (largerContains h hS)) ⋙
          typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver _
  have EI : StacksRepresentableCFG.EquivalenceOver
      (presheafOfCategories (yoneda.obj
        ((inclusionOver h S hS).obj X : BigFppfOver B' S (largerContains h hS)) ⋙
          typeToCat)).p
      (presheafOfCategories
        (((changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj X)).obj ⋙
          typeToCat)).p :=
    PresheafOfCategories.equivalenceOverOfIso (changeBigSiteYonedaIso B B' h S hS X)
  have EF : StacksRepresentableCFG.EquivalenceOver (pullbackStack h S hS 𝒳).p
      (Over.forget ((inclusionOver h S hS).obj X : BigFppfOver B' S (largerContains h hS))) :=
    W.trans (EI.symm.trans EY.symm)
  exact ⟨EF⟩

end ChangeOfSite

end AlgebraicGeometry.Stack

end

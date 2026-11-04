module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct

/-!
# Morphisms from a quotient stack to an algebraic space

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `Y` be an algebraic space over `S`. There is a 1-to-1
correspondence

    { 1-morphisms [U/R] ⟶ Y }  ≃  { R-invariant morphisms U ⟶ Y }

given by restricting along the projection `π : U ⟶ [U/R]` of Stacks 044R.

## Main definitions

* `AlgebraicGeometry.Stack.restrictedMorphism`: the `R`-invariant morphism `U ⟶ Y` attached to a
  1-morphism `[U/R] ⟶ Y`, namely the composite with the projection.
* `AlgebraicGeometry.Stack.quotientStackHomEquivInvariant`: the correspondence.

## Main results

* `AlgebraicGeometry.Stack.isInvariant_iff`: for the pre-equivalence relation that a groupoid in
  algebraic spaces cuts out, invariance is the equation `t ≫ φ = s ≫ φ`.
* `AlgebraicGeometry.Stack.restrictedMorphism_isInvariant`: the restriction of a 1-morphism is
  invariant.
* `AlgebraicGeometry.Stack.restrictedMorphism_spec`: a 1-morphism restricted along the projection
  is the 1-morphism attached to its restriction, on the nose.
* `AlgebraicGeometry.Stack.quotientStackHomEquivInvariant_spec`: the correspondence is restriction
  along the projection.

## References

* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 02Y2](https://stacks.math.columbia.edu/tag/02Y2)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The target map of the pre-equivalence relation a groupoid in algebraic spaces cuts out is the
target map of the groupoid. -/
theorem groupoidPreRelation_target_left (G : GroupoidInAlgebraicSpaces C S hS B) :
    (Space.groupoidPreRelation G).target.left = G.target.hom := by
  simp [Space.groupoidPreRelation]

/-- The source map of the pre-equivalence relation a groupoid in algebraic spaces cuts out is the
source map of the groupoid. -/
theorem groupoidPreRelation_source_left (G : GroupoidInAlgebraicSpaces C S hS B) :
    (Space.groupoidPreRelation G).source.left = G.source.hom := by
  simp [Space.groupoidPreRelation]

/-- A morphism out of the object space of a groupoid in algebraic spaces is invariant under the
pre-equivalence relation the groupoid cuts out exactly when it identifies the target and the source
maps. -/
theorem isInvariant_iff (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y) :
    Space.IsInvariant (Space.groupoidPreRelation G) φ.hom ↔ G.target ≫ φ = G.source ≫ φ := by
  rw [Space.IsInvariant, groupoidPreRelation_target_left, groupoidPreRelation_source_left]
  exact ⟨ObjectProperty.hom_ext _, congrArg (fun g : G.arrows ⟶ Y ↦ g.hom)⟩

section Restriction

variable (G : GroupoidInAlgebraicSpaces C S hS B) {Y : AlgebraicSpaces C S hS}
  (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)

/-- The composite of a 1-morphism `[U/R] ⟶ Y` with the projection `π : U ⟶ [U/R]` of Stacks 044R,
as a 1-morphism of the categories fibred in sets of two presheaves. -/
noncomputable abbrev restrictedBasedFunctor :
    (fibredCategory C S hS G.objects.obj).val ⥤ᵇ (fibredCategory C S hS Y.obj).val :=
  BasedFunctor.comp (quotientStackProjection G) f

/-- The restriction of a 1-morphism `[U/R] ⟶ Y` along the projection, as a morphism of algebraic
spaces `U ⟶ Y`: the morphism of presheaves
`CategoryTheory.PresheafOfCategories.natTransOfBasedFunctor` of the composite `U ⟶ [U/R] ⟶ Y`. -/
noncomputable def restrictedMorphism : G.objects ⟶ Y :=
  ObjectProperty.homMk
    (PresheafOfCategories.natTransOfBasedFunctor
      (restrictedBasedFunctor G f).toFunctor (restrictedBasedFunctor G f).w)

/-- The category fibred in sets of an algebraic space is fibred in sets. -/
private instance isFiberedInSets_fibredCategory_p (Y : AlgebraicSpaces C S hS) :
    (fibredCategory C S hS Y.obj).val.p.IsFiberedInSets :=
  inferInstanceAs (PresheafOfCategories.discreteProjection Y.obj).IsFiberedInSets

/-- A 1-morphism between the categories fibred in sets of two presheaves sends an object to the
pair of its base and the section that its morphism of presheaves names. -/
theorem obj_eq_mk_natTransOfBasedFunctor
    {F Y' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (θ : (fibredCategory C S hS F).val ⥤ᵇ (fibredCategory C S hS Y').val)
    (x : (fibredCategory C S hS F).val.obj) :
    θ.obj x =
      ⟨x.base, Discrete.mk ((PresheafOfCategories.natTransOfBasedFunctor
        θ.toFunctor θ.w).app (op x.base) (Discrete.as x.fiber))⟩ :=
  PresheafOfCategories.obj_eq_of_elementOf_eq (Functor.congr_obj θ.w x) rfl
    (PresheafOfCategories.elementOf_mk _ _ _).symm

/-- A 1-morphism `[U/R] ⟶ Y` composed with the projection is the 1-morphism attached by Stacks 0458
to its restriction, on the nose. -/
theorem restrictedMorphism_spec :
    BasedFunctor.comp (quotientStackProjection G) f =
      (associatedMap C S hS (restrictedMorphism G f).hom).1.hom := by
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq
    (fibredCategory C S hS G.objects.obj).val.p (fibredCategory C S hS Y.obj).val.p _ _
    (restrictedBasedFunctor G f).w (associatedMap C S hS (restrictedMorphism G f).hom).1.hom.w
    (fun x => ?_)
  exact (obj_eq_mk_natTransOfBasedFunctor (restrictedBasedFunctor G f) x).trans
    (associatedMap_obj C S hS (restrictedMorphism G f).hom x).symm

/-- The morphism of presheaves induced by the 1-morphism of Stacks 0458 attached to `a : F ⟶ Y'` is
`a` itself. -/
theorem natTransOfBasedFunctor_associatedMap
    {F Y' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ Y') :
    PresheafOfCategories.natTransOfBasedFunctor (associatedMap C S hS a).1.hom.toFunctor
      (associatedMap C S hS a).1.hom.w = a := by
  ext T g
  refine (PresheafOfCategories.elementOf_congr (F := Y') _ rfl
    (associatedMap_obj C S hS a
      (⟨T.unop, Discrete.mk g⟩ : (fibredCategory C S hS F).val.obj))).trans ?_
  exact PresheafOfCategories.elementOf_mk Y' T.unop (a.app T g)

/-- The restriction along the projection `π : U ⟶ [U/R]` of the 1-morphism `[U/R] ⟶ Y` which
`AlgebraicGeometry.Stack.quotientStackOfInvariant` attaches to an invariant `φ : U ⟶ Y` is `φ`. -/
theorem restrictedMorphism_quotientStackOfInvariant (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    restrictedMorphism G (quotientStackOfInvariant G φ hφ) = φ := by
  refine ObjectProperty.hom_ext _ ?_
  have h := congrArg
    (fun θ : (fibredCategory C S hS G.objects.obj).val ⥤ᵇ
        (fibredCategory C S hS Y.obj).val =>
      PresheafOfCategories.natTransOfBasedFunctor θ.toFunctor θ.w)
    (quotientStackProjection_comp_quotientStackOfInvariant G φ hφ)
  rwa [natTransOfBasedFunctor_associatedMap] at h

/-- The images under a 1-morphism `[U/R] ⟶ Y` of the projections of the source and the target of a
point of the arrow space agree. -/
theorem obj_quotientStackProjection_source_eq_target
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    f.obj ((BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
        (quotientStackProjection G)).obj x) =
      f.obj ((BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
        (quotientStackProjection G)).obj x) := by
  have := (quotientStackTwoArrow G).isHomLift' x
  have : (fibredCategory C S hS Y.obj).val.p.IsHomLift
      (𝟙 ((fibredCategory C S hS G.arrows.obj).val.p.obj x))
      (f.toFunctor.map ((quotientStackTwoArrow G).app x)) :=
    Functor.isHomLift_map_of_comp_eq f.w _ _
  have : (fibredCategory C S hS Y.obj).val.p.IsHomLift
      (𝟙 ((fibredCategory C S hS G.arrows.obj).val.p.obj x))
      (𝟙 (f.obj ((BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
        (quotientStackProjection G)).obj x))) :=
    IsHomLift.id (BasedFunctor.w_obj
      (BasedFunctor.comp
        (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
          (quotientStackProjection G)) f) x)
  exact (Functor.IsFiberedInSets.eq_of_isHomLift (fibredCategory C S hS Y.obj).val.p
    (𝟙 ((fibredCategory C S hS G.arrows.obj).val.p.obj x))
    (f.toFunctor.map ((quotientStackTwoArrow G).app x))
    (𝟙 (f.obj ((BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
      (quotientStackProjection G)).obj x)))).choose

/-- The restriction of a 1-morphism `[U/R] ⟶ Y` along the projection is `R`-invariant. -/
theorem restrictedMorphism_isInvariant :
    Space.IsInvariant (Space.groupoidPreRelation G) (restrictedMorphism G f).hom := by
  rw [isInvariant_iff]
  refine ObjectProperty.hom_ext _ ?_
  ext T a
  set x : (fibredCategory C S hS G.arrows.obj).val.obj := ⟨T.unop, Discrete.mk a⟩
  have hsrc : (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
      (quotientStackProjection G)).obj x =
      (quotientStackProjection G).obj
        (⟨T.unop, Discrete.mk (G.source.hom.app T a)⟩ :
          (fibredCategory C S hS G.objects.obj).val.obj) :=
    congrArg (quotientStackProjection G).obj (associatedMap_obj C S hS G.source.hom x)
  have htgt : (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
      (quotientStackProjection G)).obj x =
      (quotientStackProjection G).obj
        (⟨T.unop, Discrete.mk (G.target.hom.app T a)⟩ :
          (fibredCategory C S hS G.objects.obj).val.obj) :=
    congrArg (quotientStackProjection G).obj (associatedMap_obj C S hS G.target.hom x)
  refine PresheafOfCategories.elementOf_congr (F := Y.obj) _ _ ?_
  exact ((congrArg f.obj htgt).symm.trans
    (obj_quotientStackProjection_source_eq_target G f x).symm).trans (congrArg f.obj hsrc)

end Restriction

section Injective

variable (G : GroupoidInAlgebraicSpaces C S hS B) {Y : AlgebraicSpaces C S hS}

/-- The object of the fibre of the category fibred in sets of `Y` that a 1-morphism `[U/R] ⟶ Y`
attaches to an object of a fibre of `[U/R]`. -/
noncomputable abbrev fiberImage
    (L : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    (T : BigFppfOver C S hS) (x : (quotientStack G).p.Fiber T) :
    (fibredCategory C S hS Y.obj).val.p.Fiber T :=
  ⟨L.obj x.1, (Functor.congr_obj L.w x.1).trans x.2⟩

/-- The section of `Y` named by the image of an object of a fibre of `[U/R]` is compatible with
restriction: the image of a chosen pullback is a pullback of the image. -/
theorem discreteFiberEquiv_fiberImage_pullback
    (L : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    {T V : BigFppfOver C S hS} (x : (quotientStack G).p.Fiber T) (g : V ⟶ T) :
    PresheafOfCategories.discreteFiberEquiv Y.obj V
        (fiberImage G L V (Functor.pullbackFiber (quotientStack G).p x g)) =
      Y.obj.map g.op (PresheafOfCategories.discreteFiberEquiv Y.obj T (fiberImage G L T x)) :=
  PresheafOfCategories.discreteFiberEquiv_eq_map_of_isHomLift Y.obj g _ _
    (L.toFunctor.map (Functor.IsPreFibered.pullbackMap x.2 g))
    (Functor.isHomLift_map_of_comp_eq L.w g _)

/-- A morphism of a fibre of `[U/R]` is carried by a 1-morphism into `Y` to an equality. -/
theorem fiberImage_eq_of_hom
    (L : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    {T : BigFppfOver C S hS} {x y : (quotientStack G).p.Fiber T} (m : x ⟶ y) :
    fiberImage G L T x = fiberImage G L T y := by
  refine (PresheafOfCategories.isDiscrete_fiber_discreteProjection Y.obj T).eq_of_hom ?_
  refine ⟨L.toFunctor.map m.1, ?_⟩
  have := m.2
  exact Functor.isHomLift_map_of_comp_eq L.w (𝟙 T) m.1

/-- Two 1-morphisms `[U/R] ⟶ Y` which agree after composing with the projection `π : U ⟶ [U/R]` are
equal. -/
theorem restriction_injective
    (F K : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    (h : BasedFunctor.comp (quotientStackProjection G) F =
      BasedFunctor.comp (quotientStackProjection G) K) : F = K := by
  have hpre : ∀ (T : BigFppfOver C S hS) (a : (quotientPrestack G).p.Fiber T),
      fiberImage G F T
          ((Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_toQuotientStack G).comp_eq T).obj a) =
        fiberImage G K T
          ((Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_toQuotientStack G).comp_eq T).obj a) := by
    intro T a
    refine Subtype.ext ?_
    have he := congrArg
      (fun L : (fibredCategory C S hS G.objects.obj).val ⥤ᵇ
          (fibredCategory C S hS Y.obj).val =>
        L.obj ⟨((quotientPrestackEquivalence G).inverse.obj a.1).base,
          Discrete.mk ((quotientPrestackEquivalence G).inverse.obj a.1).fiber⟩) h
    change F.obj ((quotientStackProjection G).obj _) =
      K.obj ((quotientStackProjection G).obj _) at he
    have hp := quotientStackProjection_obj G
      (⟨((quotientPrestackEquivalence G).inverse.obj a.1).base,
        Discrete.mk ((quotientPrestackEquivalence G).inverse.obj a.1).fiber⟩ :
        (fibredCategory C S hS G.objects.obj).val.obj)
    exact (congrArg F.obj hp).symm.trans (he.trans (congrArg K.obj hp))
  have hfiber : ∀ (T : BigFppfOver C S hS) (x : (quotientStack G).p.Fiber T),
      fiberImage G F T x = fiberImage G K T x := by
    intro T x
    obtain ⟨R, hR, hr⟩ := essImage_toQuotientStack G T x
    refine (PresheafOfCategories.discreteFiberEquiv Y.obj T).injective ?_
    refine ((isSheaf_iff_isSheaf_of_type _ _).mp Y.property.isSheaf R hR).isSeparatedFor.ext
      fun V g hg ↦ ?_
    rw [← discreteFiberEquiv_fiberImage_pullback G F x g,
      ← discreteFiberEquiv_fiberImage_pullback G K x g]
    obtain ⟨a, ⟨i⟩⟩ := hr hg
    exact congrArg (PresheafOfCategories.discreteFiberEquiv Y.obj V) <|
      (fiberImage_eq_of_hom G F i.inv).trans ((hpre V a).trans (fiberImage_eq_of_hom G K i.hom))
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq
    (quotientStack G).p (fibredCategory C S hS Y.obj).val.p _ _ F.w K.w (fun x => ?_)
  exact congrArg Subtype.val (hfiber ((quotientStack G).p.obj x) ⟨x, rfl⟩)

end Injective

section Equivalence

variable (G : GroupoidInAlgebraicSpaces C S hS B) (Y : AlgebraicSpaces C S hS)

/-- For a groupoid in algebraic spaces `(U, R, s, t, c)` over an algebraic space `B` over a scheme
`S` of a big fppf site, and an algebraic space `Y` over `S`, the 1-morphisms `[U/R] ⟶ Y` of stacks
over the big fppf site are in 1-to-1 correspondence with the `R`-invariant morphisms `U ⟶ Y`, by
restriction along the projection `π : U ⟶ [U/R]` of Stacks 044R. -/
@[stacks 0DUH]
noncomputable def quotientStackHomEquivInvariant :
    (quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val) ≃
      {φ : G.objects ⟶ Y // Space.IsInvariant (Space.groupoidPreRelation G) φ.hom} :=
  Equiv.ofBijective
    (fun f => ⟨restrictedMorphism G f, restrictedMorphism_isInvariant G f⟩)
    ⟨by
      intro F K hFK
      refine restriction_injective G F K ?_
      rw [restrictedMorphism_spec, restrictedMorphism_spec]
      exact congrArg
        (fun ψ : {ψ : G.objects ⟶ Y //
            Space.IsInvariant (Space.groupoidPreRelation G) ψ.hom} =>
          (associatedMap C S hS ψ.val.hom).1.hom) hFK,
     by
      intro ψ
      refine ⟨quotientStackOfInvariant G ψ.val ((isInvariant_iff G ψ.val).1 ψ.property),
        Subtype.ext (ObjectProperty.hom_ext _ ?_)⟩
      exact (congrArg
        (fun θ : (fibredCategory C S hS G.objects.obj).val ⥤ᵇ
            (fibredCategory C S hS Y.obj).val =>
          PresheafOfCategories.natTransOfBasedFunctor θ.toFunctor θ.w)
        (quotientStackProjection_comp_quotientStackOfInvariant G ψ.val
          ((isInvariant_iff G ψ.val).1 ψ.property))).trans
        (natTransOfBasedFunctor_associatedMap ψ.val.hom)⟩

/-- The correspondence is restriction along the projection: the 1-morphism `[U/R] ⟶ Y`
corresponding to an `R`-invariant morphism `φ : U ⟶ Y` restricts along the projection
`π : U ⟶ [U/R]` to the 1-morphism attached to `φ` by Stacks 0458. -/
@[stacks 0DUH "the correspondence is restriction along the projection"]
theorem quotientStackHomEquivInvariant_spec
    (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val) :
    BasedFunctor.comp (quotientStackProjection G) f =
      (associatedMap C S hS (quotientStackHomEquivInvariant G Y f).val.hom).1.hom :=
  restrictedMorphism_spec G f

end Equivalence

end AlgebraicGeometry.Stack

end

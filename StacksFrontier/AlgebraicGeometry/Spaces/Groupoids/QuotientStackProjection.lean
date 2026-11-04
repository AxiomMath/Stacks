module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# The canonical arrow from the object space to the quotient stack

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, with object space `U` and arrow space `R`. There are two canonical 1-morphisms of
stacks over the big fppf site: the projection `U ⟶ [U/R]` from the object space to the quotient
stack, and the structure arrow `[U/R] ⟶ B` to the base; their composite is the 1-morphism
induced by the structure morphism `U ⟶ B`. The projection is described on objects and on arrows.

More generally, a morphism `φ : U ⟶ Y` to an algebraic space which identifies the source and the
target of every arrow of the groupoid, an `R`-invariant morphism, descends to a 1-morphism
`[U/R] ⟶ Y`, compatibly with the projection. The structure arrow is the case `φ = U ⟶ B`.

## Main definitions

* `AlgebraicGeometry.Stack.pointwiseObjectInclusion`: the inclusion of the discrete fibred
  category of the object space into the pointwise groupoid fibration, as the identity arrow in
  each fibre.
* `AlgebraicGeometry.Stack.quotientStackProjection`: the canonical projection `U ⟶ [U/R]`.
* `AlgebraicGeometry.Stack.pointwiseOfInvariant` and
  `AlgebraicGeometry.Stack.prestackOfInvariant`: an invariant morphism `U ⟶ Y`, read as a
  1-morphism out of the pointwise groupoid fibration and out of the presentation of the quotient
  stack.
* `AlgebraicGeometry.Stack.quotientStackOfInvariant`: the descent of an invariant morphism
  `U ⟶ Y` to a 1-morphism `[U/R] ⟶ Y`, with
  `AlgebraicGeometry.Stack.quotientStackOfInvariantUnit` the 2-isomorphism filling the triangle.
* `AlgebraicGeometry.Stack.quotientStackToBase`: the structure arrow `[U/R] ⟶ B`.

## Main results

* `AlgebraicGeometry.Stack.quotientStackProjection_obj`: the projection on objects — the image
  under `AlgebraicGeometry.Stack.pointwiseToQuotientStack` of the point read as an object of the
  pointwise groupoid.
* `AlgebraicGeometry.Stack.quotientStackProjection_map`: the projection on arrows — every arrow of
  the split fibration of `U` goes to the identity-in-the-fibre arrow of the pointwise groupoid,
  carried into the quotient.
* `AlgebraicGeometry.Stack.app_eq_of_evaluationHom`: an invariant morphism identifies the two
  ends of every arrow of an evaluated groupoid.
* `AlgebraicGeometry.Stack.quotientStackProjection_comp_quotientStackOfInvariant`: the descent of
  an invariant morphism restricts along the projection to the morphism itself.
* `AlgebraicGeometry.Stack.quotientStackProjection_comp_toBase`: the composite `U ⟶ [U/R] ⟶ B`
  is the arrow induced by the structure morphism `U ⟶ B`.

## Implementation notes

The descent `AlgebraicGeometry.Stack.quotientStackOfInvariant` is the universal property of the
stackification, `CategoryTheory.Functor.Stackification.extendGroupoid`, applied to
`AlgebraicGeometry.Stack.prestackOfInvariant`. That universal property asks for one hom universe
across its three total categories, while the quotient stack has its morphisms one universe above
those of the site; so the target is the universe-enlarged
`AlgebraicGeometry.Stack.liftedFibredCategory`, a stack by
`AlgebraicGeometry.Stack.liftedFibredCategory_isStack`, and the extension is composed back down
with `AlgebraicGeometry.Stack.liftedFibredCategoryDown`.

The universal property gives only a 2-isomorphism `π ≫ f ≅ φ`. The target is fibred in sets, so
a 2-morphism over the site between two 1-morphisms into it is an identity
(`CategoryTheory.Functor.IsFiberedInSets.eq_of_obj_eq`), and
`AlgebraicGeometry.Stack.quotientStackProjection_comp_quotientStackOfInvariant` is an equation of
1-morphisms.

## References

* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 02Y2](https://stacks.math.columbia.edu/tag/02Y2)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

/- The fibre components of `pointwiseObjectInclusion` are arrows of the evaluated groupoid
indexed through `Functor.toPseudofunctor'`, which `implicit` transparency does not unfold, so
without this attribute `Cat.eqToHom_app` is not found by `simp only` there. -/
attribute [local implicit_reducible] CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- An arrow of an evaluated groupoid obtained from an equality of its endpoints is represented by
the identity arrow of the groupoid in presheaves. -/
theorem evaluationArrow_eqToHom_identity
    {D : Type u} [Category.{v} D]
    (H : Deformation.GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : H.Evaluation T} (h : x = y) :
    (H.evaluationArrowEquiv T x y (eqToHom h)).1 = H.identity T x := by
  cases h
  rfl

/-- Include the discrete object points in the evaluated groupoid, using identity arrows. -/
noncomputable def pointwiseObjectInclusion
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (fibredCategory C S hS G.objects.obj).val.obj ⥤
      (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj where
  obj x := ⟨x.base, Discrete.as x.fiber⟩
  map {x y} f := ⟨f.base, eqToHom (Discrete.eq_of_hom f.fiber)⟩
  map_id x := by
    cases x with
    | mk U x =>
      let H := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor'
      let targetObj : H.CoGrothendieck := ⟨U, x.as⟩
      refine Pseudofunctor.CoGrothendieck.Hom.ext
        (F := H) _ (𝟙 targetObj) rfl ?_
      simp only [H, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber,
        Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app, eqToHom_trans]
  map_comp {x y z} f g := by
    cases f with
    | mk f₀ ff₀ =>
      cases g with
      | mk g₀ fg₀ =>
        let H := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor'
        let targetX : H.CoGrothendieck := ⟨x.base, x.fiber.as⟩
        let targetY : H.CoGrothendieck := ⟨y.base, y.fiber.as⟩
        let targetZ : H.CoGrothendieck := ⟨z.base, z.fiber.as⟩
        let mf : targetX ⟶ targetY := ⟨f₀, eqToHom (Discrete.eq_of_hom ff₀)⟩
        let mg : targetY ⟶ targetZ := ⟨g₀, eqToHom (Discrete.eq_of_hom fg₀)⟩
        refine Pseudofunctor.CoGrothendieck.Hom.ext
          (F := H) _ (mf ≫ mg) rfl ?_
        simp only [H, Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber,
          Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app,
          Category.assoc]
        simp only [mf, mg, eqToHom_map, eqToHom_trans]

/-- The canonical arrow from the object space of a groupoid in algebraic spaces
to its quotient stack, viewed as a functor over the big fppf site. -/
@[stacks 044R "the canonical projection"]
noncomputable def quotientStackProjection
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor
      (fibredCategory C S hS G.objects.obj).val
      (quotientStack G) where
  toFunctor := pointwiseObjectInclusion G ⋙ pointwiseToQuotientStack G
  w := by
    change pointwiseObjectInclusion G ⋙
      (pointwiseToQuotientStack G ⋙ (quotientStack G).p) = _
    rw [(isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq]
    rfl

/-- The projection sends a point of the object space to its image under the
canonical map from the pointwise groupoid to its stackification. -/
@[stacks 044R "pointwise description of the projection"]
theorem quotientStackProjection_obj
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.objects.obj).val.obj) :
    (quotientStackProjection G).obj x =
        (pointwiseToQuotientStack G).obj
        ⟨x.base, Discrete.as x.fiber⟩ := rfl

/-- The projection sends every arrow of the object-space fibration to the
corresponding identity-in-the-fibre arrow of the pointwise groupoid, followed by
stackification. -/
@[stacks 044R "pointwise description on morphisms"]
theorem quotientStackProjection_map
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : (fibredCategory C S hS G.objects.obj).val.obj}
    (f : x ⟶ y) :
    ∃ g : (⟨x.base, Discrete.as x.fiber⟩ :
        (presheafOfGroupoids
          (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
        ⟨y.base, Discrete.as y.fiber⟩,
      g.base = f.base ∧
      (G.toGroupoidInFunctors.evaluationArrowEquiv
        (Opposite.op x.base) _ _ g.fiber).1 =
          G.toGroupoidInFunctors.identity
            (Opposite.op x.base) (Discrete.as x.fiber) ∧
      (quotientStackProjection G).map f =
        eqToHom (quotientStackProjection_obj G x) ≫
          (pointwiseToQuotientStack G).map g ≫
            eqToHom (quotientStackProjection_obj G y).symm := by
  refine ⟨(pointwiseObjectInclusion G).map f, rfl, ?_, ?_⟩
  · exact evaluationArrow_eqToHom_identity G.toGroupoidInFunctors (Opposite.op x.base)
      (CategoryTheory.Discrete.eq_of_hom f.fiber)
  · exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-! ### Descending an invariant morphism to the quotient stack

A morphism `φ : U ⟶ Y` of algebraic spaces which identifies the source and the target of every
arrow of the groupoid descends to a 1-morphism `[U/R] ⟶ Y` of stacks over the site, compatibly
with the projection. The structure arrow to the base is the case `Y = B`,
`φ = G.objectsToBase`. -/

section Invariant

open CategoryTheory.Functor.Stackification

/-- **An invariant morphism identifies the two ends of every arrow of an evaluated groupoid.** If
`φ : U ⟶ Y` satisfies `t ≫ φ = s ≫ φ` then for every test object `T` and every arrow `x ⟶ y` of
the groupoid `G(T)` of Stacks 044P the sections `φ(x)` and `φ(y)` of `Y` over `T` agree. -/
theorem app_eq_of_evaluationHom (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {φ : G.objects.obj ⟶ Y}
    (hφ : G.target.hom ≫ φ = G.source.hom ≫ φ)
    {T : (BigFppfOver C S hS)ᵒᵖ}
    {x y : G.toGroupoidInFunctors.Evaluation T} (m : x ⟶ y) :
    φ.app T x = φ.app T y := by
  obtain ⟨a, hs, ht⟩ := G.toGroupoidInFunctors.evaluationArrowEquiv T x y m
  have hinv : φ.app T (G.target.hom.app T a) = φ.app T (G.source.hom.app T a) :=
    congrArg (fun n : G.arrows.obj ⟶ Y => n.app T a) hφ
  exact (congrArg (fun s => φ.app T s) hs).symm.trans
    (hinv.symm.trans (congrArg (fun s => φ.app T s) ht))

/-- **An invariant morphism on the pointwise groupoid fibration.** A morphism `φ : U ⟶ Y` of
presheaves with `t ≫ φ = s ≫ φ` sends the object `(T, x)` of the pointwise groupoid fibration of
Stacks 044Q to the object `(T, φ_T(x))` of the category fibred in sets of `Y`. -/
noncomputable def pointwiseOfInvariant (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (φ : G.objects.obj ⟶ Y)
    (hφ : G.target.hom ≫ φ = G.source.hom ≫ φ) :
    presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors) ⥤ᵇ
      (fibredCategory C S hS Y).val where
  toFunctor :=
    { obj x := ⟨x.base, Discrete.mk (φ.app (Opposite.op x.base) x.fiber)⟩
      map {x y} m :=
        { base := m.base
          fiber := Discrete.eqToHom (by
            have h := app_eq_of_evaluationHom G hφ m.fiber
            change φ.app (Opposite.op x.base) x.fiber =
              φ.app (Opposite.op x.base) (G.objects.obj.map m.base.op y.fiber) at h
            exact h.trans (NatTrans.naturality_apply φ m.base.op y.fiber)) }
      map_id X := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
        apply Discrete.hom_eq
      map_comp f g := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl) ?_
        apply Discrete.hom_eq }
  w := rfl

/-- The value of `AlgebraicGeometry.Stack.pointwiseOfInvariant` on an object. -/
@[simp]
theorem pointwiseOfInvariant_obj (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (φ : G.objects.obj ⟶ Y)
    (hφ : G.target.hom ≫ φ = G.source.hom ≫ φ)
    (x : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) :
    (pointwiseOfInvariant G φ hφ).obj x =
      ⟨x.base, Discrete.mk (φ.app (Opposite.op x.base) x.fiber)⟩ := rfl

/-- The universe lift of the pointwise groupoid fibration back down to the fibration itself, as a
1-morphism over the site. It is the inverse of
`AlgebraicGeometry.Stack.quotientPrestackEquivalence`, which is strictly over the site. -/
noncomputable def quotientPrestackDown (G : GroupoidInAlgebraicSpaces C S hS B) :
    quotientPrestack G ⥤ᵇ
      presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors) :=
  ⟨(quotientPrestackEquivalence G).inverse, rfl⟩

/-- A morphism of algebraic spaces out of the object space which identifies the source and the
target of every arrow, read on the underlying presheaves. -/
theorem hom_comp_eq_of_invariant (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} {φ : G.objects ⟶ Y}
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    G.target.hom ≫ φ.hom = G.source.hom ≫ φ.hom :=
  congrArg (fun f : G.arrows ⟶ Y => f.hom) hφ

/-- **An invariant morphism on the presentation of the quotient stack.** The 1-morphism
`AlgebraicGeometry.Stack.pointwiseOfInvariant` carried through the two universe comparisons, so
that its source is the presentation `AlgebraicGeometry.Stack.quotientPrestack` the quotient stack
is the stackification of, and its target the universe-enlarged fibred category of `Y`. -/
noncomputable def prestackOfInvariant (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    quotientPrestack G ⥤ᵇ liftedFibredCategory Y :=
  BasedFunctor.comp (quotientPrestackDown G)
    (BasedFunctor.comp (pointwiseOfInvariant G φ.hom (hom_comp_eq_of_invariant G hφ))
      (liftedFibredCategoryUp Y))

/-- The extension of `AlgebraicGeometry.Stack.prestackOfInvariant` along the stackification, as a
bare functor into the universe-enlarged fibred category of `Y`. -/
noncomputable def liftedQuotientStackOfInvariant
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    (quotientStack G).obj ⥤ (liftedFibredCategory Y).obj :=
  extendGroupoid
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G)
    (isStack_quotientStack G)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS Y.obj).property)
    (liftedFibredCategory_isStack Y)
    (isFibredOneMorphism_toQuotientStack G).comp_eq
    (prestackOfInvariant G φ hφ).w
    (isLocallyBijective_toQuotientStack G)
    (essImage_toQuotientStack G)

/-- **A morphism out of the object space which is invariant under the groupoid descends to the
quotient stack.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let
`φ : U ⟶ Y` be a morphism to an algebraic space with `t ≫ φ = s ≫ φ`. Then `φ` extends to a
1-morphism `[U/R] ⟶ Y` of stacks over the big fppf site. -/
noncomputable def quotientStackOfInvariant
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val :=
  BasedFunctor.comp
    (⟨liftedQuotientStackOfInvariant G φ hφ,
      extendGroupoid_comp_eq
        (isFiberedInGroupoids_quotientPrestack G)
        (isFiberedInGroupoids_quotientStack G)
        (isStack_quotientStack G)
        (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS Y.obj).property)
        (liftedFibredCategory_isStack Y)
        (isFibredOneMorphism_toQuotientStack G).comp_eq
        (prestackOfInvariant G φ hφ).w
        (isLocallyBijective_toQuotientStack G)
        (essImage_toQuotientStack G)⟩ :
      quotientStack G ⥤ᵇ liftedFibredCategory Y)
    (liftedFibredCategoryDown Y)

/-- The 2-isomorphism filling the triangle of the universal property of the stackification: the
descent of an invariant morphism restricted along the stackification is the morphism itself. -/
noncomputable def quotientStackOfInvariantUnit
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    toQuotientStack G ⋙ liftedQuotientStackOfInvariant G φ hφ ≅
      (prestackOfInvariant G φ hφ).toFunctor :=
  unitGroupoid
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G)
    (isStack_quotientStack G)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS Y.obj).property)
    (liftedFibredCategory_isStack Y)
    (isFibredOneMorphism_toQuotientStack G).comp_eq
    (prestackOfInvariant G φ hφ).w
    (isLocallyBijective_toQuotientStack G)
    (essImage_toQuotientStack G)

/-- Every component of `AlgebraicGeometry.Stack.quotientStackOfInvariantUnit` lies over an
identity of the site, so the triangle 2-commutes over the site and not merely in `Cat`. -/
theorem isHomLift_quotientStackOfInvariantUnit_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) (z : (quotientPrestack G).obj) :
    (liftedFibredCategory Y).p.IsHomLift (𝟙 ((quotientPrestack G).p.obj z))
      ((quotientStackOfInvariantUnit G φ hφ).hom.app z) :=
  isHomLift_unitGroupoid_app
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G)
    (isStack_quotientStack G)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS Y.obj).property)
    (liftedFibredCategory_isStack Y)
    (isFibredOneMorphism_toQuotientStack G).comp_eq
    (prestackOfInvariant G φ hφ).w
    (isLocallyBijective_toQuotientStack G)
    (essImage_toQuotientStack G) z

/-- The fibred category of a presheaf is fibred in sets over the site. -/
private instance isFiberedInSets_fibredCategory
    (Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    (fibredCategory C S hS Y).val.p.IsFiberedInSets :=
  inferInstanceAs (PresheafOfCategories.discreteProjection Y).IsFiberedInSets

/-- **On objects coming from the presentation, the descent of an invariant morphism is the
morphism itself.** -/
theorem quotientStackOfInvariant_obj_toQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) (z : (quotientPrestack G).obj) :
    (quotientStackOfInvariant G φ hφ).obj ((toQuotientStack G).obj z) =
      (pointwiseOfInvariant G φ.hom (hom_comp_eq_of_invariant G hφ)).obj
        ((quotientPrestackDown G).obj z) := by
  have := isHomLift_quotientStackOfInvariantUnit_app G φ hφ z
  have : (fibredCategory C S hS Y.obj).val.p.IsHomLift
      (𝟙 ((quotientPrestack G).p.obj z))
      ((liftedFibredCategoryDown Y).toFunctor.map
        ((quotientStackOfInvariantUnit G φ hφ).hom.app z)) :=
    Functor.isHomLift_map_of_comp_eq (liftedFibredCategoryDown Y).w _ _
  have : (fibredCategory C S hS Y.obj).val.p.IsHomLift
      (𝟙 ((quotientPrestack G).p.obj z))
      (𝟙 ((liftedFibredCategoryDown Y).obj ((prestackOfInvariant G φ hφ).obj z))) :=
    IsHomLift.id rfl
  exact (Functor.IsFiberedInSets.eq_of_isHomLift (fibredCategory C S hS Y.obj).val.p
    (𝟙 ((quotientPrestack G).p.obj z))
    ((liftedFibredCategoryDown Y).toFunctor.map
      ((quotientStackOfInvariantUnit G φ hφ).hom.app z))
    (𝟙 ((liftedFibredCategoryDown Y).obj ((prestackOfInvariant G φ hφ).obj z)))).choose

/-- **The descent of an invariant morphism restricts along the projection to the morphism
itself**, on the nose and not merely up to 2-isomorphism. -/
theorem quotientStackProjection_comp_quotientStackOfInvariant
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
    (hφ : G.target ≫ φ = G.source ≫ φ) :
    BasedFunctor.comp (quotientStackProjection G) (quotientStackOfInvariant G φ hφ) =
      (associatedMap C S hS φ.hom).1.hom := by
  refine BasedCategory.BasedFunctor.ext' ?_
  refine Functor.IsFiberedInSets.eq_of_obj_eq
    (fibredCategory C S hS G.objects.obj).val.p (fibredCategory C S hS Y.obj).val.p _ _
    (BasedFunctor.comp (quotientStackProjection G) (quotientStackOfInvariant G φ hφ)).w
    (associatedMap C S hS φ.hom).1.hom.w (fun x => ?_)
  refine (quotientStackOfInvariant_obj_toQuotientStack G φ hφ
    ((quotientPrestackEquivalence G).functor.obj ⟨x.base, Discrete.as x.fiber⟩)).trans ?_
  exact (associatedMap_obj C S hS φ.hom x).symm

/-- The second canonical 1-morphism, the structure arrow `[U/R] ⟶ B` from the
quotient stack to the base: the descent of the structure morphism `U ⟶ B` of the object space,
which is invariant because the source and the target of the groupoid are morphisms over `B`. -/
@[stacks 044R "the canonical map to the base"]
noncomputable def quotientStackToBase (G : GroupoidInAlgebraicSpaces C S hS B) :
    quotientStack G ⥤ᵇ (fibredCategory C S hS B.obj).val :=
  quotientStackOfInvariant G G.objectsToBase (G.target_over.trans G.source_over.symm)

/-- The composition `U ⟶ [U/R] ⟶ B` is the 1-morphism associated to the
structure morphism `U ⟶ B`. -/
@[stacks 044R "composition with the base map"]
theorem quotientStackProjection_comp_toBase (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor.comp (quotientStackProjection G) (quotientStackToBase G) =
      (associatedMap C S hS G.objectsToBase.hom).1.hom :=
  quotientStackProjection_comp_quotientStackOfInvariant G G.objectsToBase
    (G.target_over.trans G.source_over.symm)

end Invariant

end AlgebraicGeometry.Stack

end

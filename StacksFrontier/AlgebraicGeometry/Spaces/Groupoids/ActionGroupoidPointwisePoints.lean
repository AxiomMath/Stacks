module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackComparison
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensor

/-!
# Points and arrows of the pointwise action groupoid

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, acting on an algebraic space `X` over `B`. The quotient stack `[X/G]` is the stackification
of the pointwise groupoid fibration of the action groupoid `(X, G ×_B X, pr₁, a, m)` of Stacks
0444, so the comparison of `[X/G]` with the stack of torsors with an equivariant map (Stacks
04WM) has to be defined on that pointwise fibration. This file reads off its points and its
arrows: an object of the fibre over a test object `U` is an `X`-valued point `x : U ⟶ X`, and an
arrow `A ⟶ A'` is a pair `(f, g)` consisting of a morphism `f` of test objects and a `G`-point
`g` over `x ≫ X.hom`, subject to `g · x = x' ∘ f`.

## Main definitions

* `AlgebraicGeometry.Space.actionPointwiseCategory`: the pointwise groupoid fibration of the
  action groupoid.
* `AlgebraicGeometry.Space.actionPointwiseValue`: the `X`-valued point underlying an object of
  that fibration, and `AlgebraicGeometry.Space.actionPointwiseObject` the object it comes from.
* `AlgebraicGeometry.Space.actionPointwiseArrow` and
  `AlgebraicGeometry.Space.actionPointwiseGroupElement`: the point of `G ×_B X` underlying an
  arrow of that fibration, and its `G`-component.

## Main results

* `AlgebraicGeometry.Space.actionPointwiseArrow_source` and
  `AlgebraicGeometry.Space.actionPointwiseArrow_target`, with their natural-transformation forms
  `AlgebraicGeometry.Space.actionPointwiseArrow_source_natTrans` and
  `AlgebraicGeometry.Space.actionPointwiseArrow_target_natTrans`: the two endpoints of the point
  of `G ×_B X` underlying an arrow.
* `AlgebraicGeometry.Space.actionPointwise_base_compat`,
  `AlgebraicGeometry.Space.actionPointwise_group_compat` and
  `AlgebraicGeometry.Space.actionPointwise_action`: the three compatibilities satisfied by the
  pair `(f, g)`, the last of which is `g · x = x' ∘ f`.
* `AlgebraicGeometry.Space.actionPointwiseArrow_id`,
  `AlgebraicGeometry.Space.actionPointwiseGroupElement_id`,
  `AlgebraicGeometry.Space.actionPointwiseArrow_comp`,
  `AlgebraicGeometry.Space.actionPointwiseArrow_group_natTrans` and
  `AlgebraicGeometry.Space.actionPointwiseGroupElement_comp`: the identity and the composition
  of the fibration, read in terms of the unit and the multiplication of `G`.
* `AlgebraicGeometry.Space.actionPointwiseValue_actionPointwiseObject` and
  `AlgebraicGeometry.Space.actionPointwiseMorphism_ext`: the point of an object built from a
  point is that point, and an arrow is determined by its base and its `G`-component.

## Implementation notes

The action groupoid is `AlgebraicGeometry.Space.groupoidOfAction`, an
`AlgebraicGeometry.Space.ActionGroupoidConstruction`, whose object and arrow spaces are fields,
so the identification of them with `X` and `G ×_B X` is available through the equality fields
`AlgebraicGeometry.Space.ActionGroupoidConstruction.objects_eq` and
`AlgebraicGeometry.Space.ActionGroupoidConstruction.arrows_eq`. Every statement below therefore
transports a point along one of those equalities, and the resulting `cast`s are intrinsic to the
construction rather than an artefact of the formulation: the groupoid names the chosen spaces
instead of replacing them by isomorphic ones. Three private lemmas discharge the bookkeeping,
namely that applying a natural transformation, a function, or the composition law of a groupoid
in presheaves commutes with such a transport.

Those `cast`s are written with their equality proof spelled out rather than left as `_`. The
proofs are irrelevant to the elaborated term, but the placeholder is not inferable: the object
and arrow spaces of the action groupoid are definitionally the given ones, so the `cast`s reduce
away and leave the `change` no `cast` in the goal to read the proof off.

The pointwise fibration is the Grothendieck construction of the presheaf of groupoids obtained
by evaluating the action groupoid, so its identity and composition are those of
`CategoryTheory.presheafOfCategories`, read through
`CategoryTheory.PresheafOfCategories.comp_fiber` and, since the library has no identity
analogue of that lemma, through a private one mirroring it.

## References

* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

-- Reading the identity and the composition of the Grothendieck construction of a presheaf of
-- groupoids means seeing through the pseudofunctor it is presented by and through the
-- identification of the fibre of that pseudofunctor with the evaluated object presheaf. Both
-- chains are definitional, and these are the definitions along them.
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc CategoryTheory.Grpd.forgetToCat CategoryTheory.Grpd.of

section CastHelpers

universe u₁ v₁ v₂ u₂ w w'

/-- The strict compatibility `(𝟙 U)^* x = x` of the pullback functors of a presheaf of
categories, which is what makes the identity of `𝒮_F` type-check. -/
private lemma pullback_id_obj {𝒟 : Type u₁} [Category.{v₁} 𝒟] (F : 𝒟ᵒᵖ ⥤ Cat.{v₂, u₂})
    (A : F.toPseudofunctor'.CoGrothendieck) :
    A.fiber = (F.map (𝟙 A.base).op).toFunctor.obj A.fiber := by
  rw [op_id, F.map_id]
  rfl

/-- The identity of `𝒮_F` is the identity of the fibre, read through `pullback_id_obj`. This
is the identity analogue of `CategoryTheory.PresheafOfCategories.comp_fiber`. -/
private lemma coGrothendieck_id_fiber {𝒟 : Type u₁} [Category.{v₁} 𝒟]
    (F : 𝒟ᵒᵖ ⥤ Cat.{v₂, u₂}) (A : F.toPseudofunctor'.CoGrothendieck) :
    Pseudofunctor.CoGrothendieck.Hom.fiber (𝟙 A) = eqToHom (pullback_id_obj F A) := by
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber,
    CategoryTheory.Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]

/-- Applying a natural transformation commutes with transporting a point along an equality of
the functors involved. -/
private theorem app_cast_of_heq {D : Type u₁} [Category.{v₁} D]
    {F F' H H' : D ⥤ Type w} (hF : F = F') (hH : H = H')
    {φ : F ⟶ H} {φ' : F' ⟶ H'} (hφ : HEq φ φ') (T : D) (a : F.obj T) :
    φ'.app T (cast (congrArg (fun K : D ⥤ Type w => K.obj T) hF) a) =
      cast (congrArg (fun K : D ⥤ Type w => K.obj T) hH) (φ.app T a) := by
  subst F'
  subst H'
  cases eq_of_heq hφ
  rfl

/-- Applying a function commutes with transporting its argument along an equality of the types
involved. -/
private theorem apply_cast_of_heq {A A' : Type w} {E E' : Type w'}
    (hA : A = A') (hE : E = E') {f : A → E} {f' : A' → E'}
    (hf : HEq f f') (a : A) : f' (cast hA a) = cast hE (f a) := by
  subst A'
  subst E'
  cases eq_of_heq hf
  rfl

end CastHelpers

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)
  (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B) [ModObj G.obj.X X]
  (hX : IsAlgebraicSpace 𝒞 S hS X.left)

/-- Composing a composable pair of arrows commutes with transporting the pair along equalities
of the arrow and object presheaves and of the source, target and composition maps. -/
private theorem composableToPullback_comp_cast
    {O O' R R' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hO : O = O') (hR : R = R') {s t : R ⟶ O} {s' t' : R' ⟶ O'}
    (hs : HEq s s') (ht : HEq t t') {c : pullback s t ⟶ R}
    {c' : pullback s' t' ⟶ R'} (hc : HEq c c')
    (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a b : R.obj T) (h : s.app T a = t.app T b)
    (a' b' : R'.obj T)
    (ha : cast (congrArg (fun F => F.obj T) hR) a = a')
    (hb : cast (congrArg (fun F => F.obj T) hR) b = b')
    (h' : s'.app T a' = t'.app T b') :
    cast (congrArg (fun F => F.obj T) hR)
        ((composableToPullback s t ≫ c).app T ⟨(a, b), h⟩) =
      (composableToPullback s' t' ≫ c').app T ⟨(a', b'), h'⟩ := by
  subst O'
  subst R'
  cases eq_of_heq hs
  cases eq_of_heq ht
  cases eq_of_heq hc
  subst a'
  subst b'
  rfl

/-- The pointwise groupoid fibration of the action groupoid of an action of a group algebraic
space. -/
abbrev actionPointwiseCategory : BasedCategory (BigFppfOver 𝒞 S hS) :=
  presheafOfGroupoids
    (Stack.evaluationGroupoidFunctor
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid.toGroupoidInFunctors)

/-- The `X`-valued point underlying an object of the pointwise action groupoid. -/
def actionPointwiseValue (A : (actionPointwiseCategory hB G X hX).obj) :
    yoneda.obj A.base ⟶ X.left :=
  yonedaEquiv.symm
    (cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).objects_eq) A.fiber)

/-- The action-groupoid arrow encoded by a morphism in the Grothendieck construction of the
pointwise action groupoid, before taking its `G`-component. -/
def actionPointwiseArrow {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    (G.obj.X ⊗ X).left.obj (op A.base) :=
  let D := (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid.toGroupoidInFunctors
  let r := (D.evaluationArrowEquiv (op A.base) A.fiber
    ((D.objects.map (op f.base)) A'.fiber) f.fiber).1
  cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
    (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).arrows_eq) r

/-- The group element `g` in a pointwise arrow `(f, g)`. -/
def actionPointwiseGroupElement {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    yoneda.obj A.base ⟶ G.obj.X.left :=
  yonedaEquiv.symm
    ((pullback.fst G.obj.X.hom X.hom).app (op A.base) (actionPointwiseArrow hB G X hX f))

/-- The source of the action-groupoid arrow underlying a pointwise arrow is the point
underlying its domain. -/
theorem actionPointwiseArrow_source
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    (pullback.snd G.obj.X.hom X.hom).app (op A.base) (actionPointwiseArrow hB G X hX f) =
      yonedaEquiv (actionPointwiseValue hB G X hX A) := by
  let D := groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX
  let r := (D.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op A.base)
    A.fiber _ f.fiber)
  simp only [actionPointwiseValue, Equiv.apply_symm_apply]
  change _ = cast _ A.fiber
  change (pullback.snd G.obj.X.hom X.hom).app (op A.base)
    (cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.arrows_eq) r.val) = _
  exact (app_cast_of_heq (congrArg (fun Y => Y.obj) D.arrows_eq)
    (congrArg (fun Y => Y.obj) D.objects_eq) D.source_eq (op A.base) r.val).trans
      (congrArg (cast _) r.property.1)

/-- The target of the action-groupoid arrow underlying a pointwise arrow is the point
underlying its codomain, restricted along the base morphism. -/
theorem actionPointwiseArrow_target
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    (γ[G.obj.X, X]).left.app (op A.base) (actionPointwiseArrow hB G X hX f) =
      X.left.map f.base.op (yonedaEquiv (actionPointwiseValue hB G X hX A')) := by
  let D := groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX
  let r := (D.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op A.base)
    A.fiber _ f.fiber)
  simp only [actionPointwiseValue, Equiv.apply_symm_apply]
  change (γ[G.obj.X, X]).left.app (op A.base)
      (cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
        D.arrows_eq) r.val) =
    X.left.map _ (cast _ A'.fiber)
  exact (app_cast_of_heq (congrArg (fun Y => Y.obj) D.arrows_eq)
    (congrArg (fun Y => Y.obj) D.objects_eq) D.target_eq (op A.base) r.val).trans
      ((congrArg (cast _) r.property.2).trans
        (Deformation.cast_functor_map (congrArg (fun Y => Y.obj) D.objects_eq)
          f.base.op A'.fiber))

/-- `AlgebraicGeometry.Space.actionPointwiseArrow_source` as an equality of morphisms of
presheaves. -/
theorem actionPointwiseArrow_source_natTrans
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    yonedaEquiv.symm (actionPointwiseArrow hB G X hX f) ≫ pullback.snd G.obj.X.hom X.hom =
      actionPointwiseValue hB G X hX A := by
  apply yonedaEquiv.injective
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using
    actionPointwiseArrow_source hB G X hX f

/-- `AlgebraicGeometry.Space.actionPointwiseArrow_target` as an equality of morphisms of
presheaves. -/
theorem actionPointwiseArrow_target_natTrans
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    yonedaEquiv.symm (actionPointwiseArrow hB G X hX f) ≫ (γ[G.obj.X, X]).left =
      yoneda.map f.base ≫ actionPointwiseValue hB G X hX A' := by
  apply yonedaEquiv.injective
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_naturality] using
    actionPointwiseArrow_target hB G X hX f

/-- The points underlying the domain and the codomain of a pointwise arrow agree over `B`. -/
theorem actionPointwise_base_compat
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    actionPointwiseValue hB G X hX A ≫ X.hom =
      yoneda.map f.base ≫ actionPointwiseValue hB G X hX A' ≫ X.hom := by
  rw [← actionPointwiseArrow_source_natTrans hB G X hX f,
    ← Category.assoc, ← actionPointwiseArrow_target_natTrans hB G X hX f]
  simp only [Category.assoc, (γ[G.obj.X, X]).w]
  rw [← pullback.condition]
  rfl

/-- The group element of a pointwise arrow lies over the point underlying its domain. -/
theorem actionPointwise_group_compat
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    actionPointwiseGroupElement hB G X hX f ≫ G.obj.X.hom =
      actionPointwiseValue hB G X hX A ≫ X.hom := by
  have hg : actionPointwiseGroupElement hB G X hX f =
      yonedaEquiv.symm (actionPointwiseArrow hB G X hX f) ≫
        pullback.fst G.obj.X.hom X.hom := by
    apply yonedaEquiv.injective
    simp only [actionPointwiseGroupElement, yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [hg, ← actionPointwiseArrow_source_natTrans hB G X hX f]
  simp only [Category.assoc, pullback.condition]

/-- The group element of a pointwise arrow carries the point underlying its domain to the point
underlying its codomain. -/
theorem actionPointwise_action
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    pullback.lift (actionPointwiseGroupElement hB G X hX f)
        (actionPointwiseValue hB G X hX A) (actionPointwise_group_compat hB G X hX f) ≫
      (γ[G.obj.X, X]).left = yoneda.map f.base ≫ actionPointwiseValue hB G X hX A' := by
  have h : pullback.lift (actionPointwiseGroupElement hB G X hX f)
        (actionPointwiseValue hB G X hX A) (actionPointwise_group_compat hB G X hX f) =
      yonedaEquiv.symm (actionPointwiseArrow hB G X hX f) := by
    apply pullback.hom_ext
    · apply yonedaEquiv.injective
      simp only [pullback.lift_fst, actionPointwiseGroupElement,
        yonedaEquiv_comp, Equiv.apply_symm_apply]
    · rw [pullback.lift_snd, actionPointwiseArrow_source_natTrans]
  rw [h, actionPointwiseArrow_target_natTrans]

/-- The action-groupoid arrow underlying an identity is the unit arrow at the point. -/
theorem actionPointwiseArrow_id (A : (actionPointwiseCategory hB G X hX).obj) :
    actionPointwiseArrow hB G X hX (𝟙 A) =
      (Stacks.Groupoids.ActionGroupoid.identity G.obj.X X).left.app (op A.base)
        (yonedaEquiv (actionPointwiseValue hB G X hX A)) := by
  let D := groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX
  have hid : (D.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op A.base)
      A.fiber _ ((𝟙 A) : A ⟶ A).fiber).val =
      D.groupoid.toGroupoidInFunctors.identity (op A.base) A.fiber := by
    have hfib : ((𝟙 A) : A ⟶ A).fiber =
        eqToHom (pullback_id_obj (Stack.evaluationGroupoidFunctor
          D.groupoid.toGroupoidInFunctors ⋙ Grpd.forgetToCat) A) :=
      coGrothendieck_id_fiber _ A
    rw [hfib]
    exact Stack.evaluationArrow_eqToHom_identity _ (op A.base) _
  change cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.arrows_eq)
    ((D.groupoid.toGroupoidInFunctors.evaluationArrowEquiv _ _ _
      ((𝟙 A) : A ⟶ A).fiber).val) = _
  rw [hid]
  simp only [actionPointwiseValue, Equiv.apply_symm_apply]
  exact (apply_cast_of_heq
    (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.objects_eq)
    (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.arrows_eq) (D.identity_eq (op A.base)) A.fiber).symm

/-- The group element of an identity arrow is the unit of `G`. -/
theorem actionPointwiseGroupElement_id (A : (actionPointwiseCategory hB G X hX).obj) :
    actionPointwiseGroupElement hB G X hX (𝟙 A) =
      actionPointwiseValue hB G X hX A ≫ X.hom ≫ (η[G.obj.X]).left := by
  apply yonedaEquiv.injective
  simp only [actionPointwiseGroupElement, Equiv.apply_symm_apply, actionPointwiseArrow_id]
  rw [← yonedaEquiv_comp]
  change yonedaEquiv (actionPointwiseValue hB G X hX A ≫
      (Stacks.Groupoids.ActionGroupoid.identity G.obj.X X).left ≫
        pullback.fst G.obj.X.hom X.hom) = _
  congr 1
  simp only [Stacks.Groupoids.ActionGroupoid.identity, Over.lift_left, pullback.lift_fst,
    Over.comp_left, Over.toUnit_left]

-- The composition formula transports the chosen groupoid across slice pullbacks.
/-- The action-groupoid arrow underlying a composition is the composition of the action
groupoid. -/
theorem actionPointwiseArrow_comp
    {A A' A'' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') (g : A' ⟶ A'') :
    yonedaEquiv.symm (actionPointwiseArrow hB G X hX (f ≫ g)) =
      pullback.lift
        (yoneda.map f.base ≫ yonedaEquiv.symm (actionPointwiseArrow hB G X hX g))
        (yonedaEquiv.symm (actionPointwiseArrow hB G X hX f))
        (by
          change (yoneda.map f.base ≫ _) ≫ pullback.snd G.obj.X.hom X.hom = _
          rw [Category.assoc, actionPointwiseArrow_source_natTrans hB G X hX g,
            actionPointwiseArrow_target_natTrans hB G X hX f]) ≫
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).compositionDomainIso.hom ≫
        (Stacks.Groupoids.ActionGroupoid.composition G.obj.X X).left := by
  let D := groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX
  let E := D.groupoid.toGroupoidInFunctors
  let r := (E.evaluationArrowEquiv (op A.base) A.fiber _ f.fiber).val
  let q := (E.evaluationArrowEquiv (op A'.base) A'.fiber _ g.fiber).val
  have hst : E.source.app (op A.base) (E.arrows.map f.base.op q) = E.target.app (op A.base) r := by
    rw [NatTrans.naturality_apply]
    exact (congrArg (E.objects.map f.base.op)
      (E.evaluationArrowEquiv (op A'.base) A'.fiber _ g.fiber).property.1).trans
      (E.evaluationArrowEquiv (op A.base) A.fiber _ f.fiber).property.2.symm
  have hraw : (E.evaluationArrowEquiv (op A.base) A.fiber _ (f ≫ g).fiber).val =
      E.compose (op A.base) (E.arrows.map f.base.op q) r hst := by
    have hz := PresheafOfCategories.pullback_comp_obj
      (Stack.evaluationGroupoidFunctor E ⋙ Grpd.forgetToCat) f.base g.base A''.fiber
    have hcf : ((f ≫ g) : A ⟶ A'').fiber =
        (f.fiber ≫ (Deformation.evaluationMap E f.base.op).map g.fiber) ≫ eqToHom hz :=
      (PresheafOfCategories.comp_fiber _ f g).trans (Category.assoc _ _ _).symm
    -- `hcf` is applied by `congrArg` rather than by `rw`: the arrow it rewrites also fixes the
    -- target object of `evaluationArrowEquiv`, so the motive `rw` builds is dependent and deciding
    -- it type-correct is what exhausts the budget.  Both sides of `hcf` have the same type, so
    -- congruence in the arrow alone is enough.
    refine Eq.trans (congrArg
      (fun φ => (E.evaluationArrowEquiv (op A.base) A.fiber _ φ).val) hcf) ?_
    refine Eq.trans (Stack.evaluationArrowEquiv_comp_eqToHom E (op A.base)
      (f.fiber ≫ (Deformation.evaluationMap E f.base.op).map g.fiber) hz) ?_
    refine Eq.trans (E.evaluationArrowEquiv_comp (op A.base) f.fiber
      ((Deformation.evaluationMap E f.base.op).map g.fiber)) ?_
    exact congrArg (fun t => E.comp.app (op A.base) t)
      (Subtype.ext (Prod.ext (Deformation.evaluationMap_map_arrow E f.base.op g.fiber) rfl))
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.arrows_eq)
    ((E.evaluationArrowEquiv _ _ _ (f ≫ g).fiber).val) = _
  rw [hraw]
  let a := (G.obj.X ⊗ X).left.map f.base.op (actionPointwiseArrow hB G X hX g)
  let b := actionPointwiseArrow hB G X hX f
  have hab : (CartesianMonoidalCategory.snd G.obj.X X).left.app (op A.base) a =
      (γ[G.obj.X, X]).left.app (op A.base) b := by
    change (pullback.snd G.obj.X.hom X.hom).app _
      ((G.obj.X ⊗ X).left.map _ _) = _
    change (pullback.snd G.obj.X.hom X.hom).app _
      ((pullback G.obj.X.hom X.hom).map _ _) = _
    rw [NatTrans.naturality_apply, actionPointwiseArrow_source hB G X hX g,
      actionPointwiseArrow_target hB G X hX f]
  have hcast := composableToPullback_comp_cast
    (congrArg (fun Y => Y.obj) D.objects_eq)
    (congrArg (fun Y => Y.obj) D.arrows_eq) D.source_eq D.target_eq D.comp_eq
    (op A.base) (E.arrows.map f.base.op q) r hst a b
    (Deformation.cast_functor_map (congrArg (fun Y => Y.obj) D.arrows_eq) f.base.op q)
    rfl hab
  change cast _ ((composableToPullback _ _ ≫ _).app _ _) = _
  refine hcast.trans ?_
  have hp : yonedaEquiv.symm
      ((composableToPullback (CartesianMonoidalCategory.snd G.obj.X X).left
        (γ[G.obj.X, X]).left).app (op A.base) ⟨(a, b), hab⟩) =
      pullback.lift
        (yoneda.map f.base ≫ yonedaEquiv.symm (actionPointwiseArrow hB G X hX g))
        (yonedaEquiv.symm (actionPointwiseArrow hB G X hX f))
        (by
          change (yoneda.map f.base ≫ _) ≫ pullback.snd G.obj.X.hom X.hom = _
          rw [Category.assoc, actionPointwiseArrow_source_natTrans hB G X hX g,
            actionPointwiseArrow_target_natTrans hB G X hX f]) := by
    apply pullback.hom_ext
    · apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply, pullback.lift_fst]
      change ((composableToPullback _ _ ≫ pullback.fst _ _).app _ ⟨(a, b), hab⟩) = a
      simp only [composableToPullback, pullback.lift_fst]
      rfl
    · apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply, pullback.lift_snd]
      change ((composableToPullback _ _ ≫ pullback.snd _ _).app _ ⟨(a, b), hab⟩) = b
      simp only [composableToPullback, pullback.lift_snd]
      rfl
  rw [← hp]
  simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- `AlgebraicGeometry.Space.actionPointwiseGroupElement` as the first component of the
action-groupoid arrow. -/
theorem actionPointwiseArrow_group_natTrans
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') :
    yonedaEquiv.symm (actionPointwiseArrow hB G X hX f) ≫ pullback.fst G.obj.X.hom X.hom =
      actionPointwiseGroupElement hB G X hX f := by
  apply yonedaEquiv.injective
  simp only [yonedaEquiv_comp, Equiv.apply_symm_apply, actionPointwiseGroupElement]

/-- The group element of a composition is the product of the group elements of its factors. -/
theorem actionPointwiseGroupElement_comp
    {A A' A'' : (actionPointwiseCategory hB G X hX).obj} (f : A ⟶ A') (g : A' ⟶ A'') :
    actionPointwiseGroupElement hB G X hX (f ≫ g) =
      pullback.lift
        (yoneda.map f.base ≫ actionPointwiseGroupElement hB G X hX g)
        (actionPointwiseGroupElement hB G X hX f)
        (by rw [Category.assoc, actionPointwise_group_compat hB G X hX g,
          actionPointwise_group_compat hB G X hX f,
          actionPointwise_base_compat hB G X hX f]) ≫ (μ[G.obj.X]).left := by
  rw [← actionPointwiseArrow_group_natTrans, actionPointwiseArrow_comp]
  simp only [Stacks.Groupoids.ActionGroupoid.composition, Over.lift_left, Over.comp_left,
    Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [← Category.assoc _ _ (CartesianMonoidalCategory.fst G.obj.X X).left,
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).compositionDomainIso_fst]
    simp only [← Category.assoc, pullback.lift_fst]
    rw [Category.assoc]
    exact congrArg (fun t => yoneda.map f.base ≫ t)
      (actionPointwiseArrow_group_natTrans hB G X hX g)
  · simp only [Category.assoc, pullback.lift_snd]
    rw [← Category.assoc _ _ (CartesianMonoidalCategory.fst G.obj.X X).left,
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).compositionDomainIso_snd]
    simp only [← Category.assoc, pullback.lift_snd]
    exact actionPointwiseArrow_group_natTrans hB G X hX f

/-- The object of the pointwise action groupoid determined by an `X`-valued point. -/
def actionPointwiseObject (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    (actionPointwiseCategory hB G X hX).obj where
  base := U
  fiber := cast
    (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op U))
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).objects_eq).symm (yonedaEquiv x)

/-- The point underlying the object determined by a point is that point. -/
theorem actionPointwiseValue_actionPointwiseObject
    (U : BigFppfOver 𝒞 S hS) (x : yoneda.obj U ⟶ X.left) :
    actionPointwiseValue hB G X hX (actionPointwiseObject hB G X hX U x) = x := by
  have hc : cast
      (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op U))
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).objects_eq)
      (cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op U))
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).objects_eq).symm
        (yonedaEquiv x)) = yonedaEquiv x :=
    (cast_cast _ _ _).trans (cast_eq _ _)
  exact (congrArg yonedaEquiv.symm hc).trans (yonedaEquiv.symm_apply_apply x)

/-- An arrow of the pointwise action groupoid is determined by its base morphism and its group
element. -/
theorem actionPointwiseMorphism_ext
    {A A' : (actionPointwiseCategory hB G X hX).obj} (f g : A ⟶ A')
    (hb : f.base = g.base)
    (hg : actionPointwiseGroupElement hB G X hX f =
      actionPointwiseGroupElement hB G X hX g) : f = g := by
  have ha : actionPointwiseArrow hB G X hX f = actionPointwiseArrow hB G X hX g := by
    apply yonedaEquiv.symm.injective
    apply pullback.hom_ext
    · simpa only [actionPointwiseArrow_group_natTrans] using hg
    · rw [actionPointwiseArrow_source_natTrans, actionPointwiseArrow_source_natTrans]
  let D := (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid.toGroupoidInFunctors
  apply Pseudofunctor.CoGrothendieck.Hom.ext f g hb
  apply (D.evaluationArrowEquiv (op A.base) A.fiber _).injective
  apply Subtype.ext
  rw [Stack.evaluationArrowEquiv_comp_eqToHom]
  exact (Equiv.cast
    (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).arrows_eq)).injective ha

end AlgebraicGeometry.Space

end

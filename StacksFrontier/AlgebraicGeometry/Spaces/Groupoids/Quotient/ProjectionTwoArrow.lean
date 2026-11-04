module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection

/-!
# Two-commutativity of the quotient stack square (Stacks 044S)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `π : 𝒮_U ⟶ [U/R]` be the canonical projection of
Stacks 044R. The source and target maps of `G` give two arrows `𝒮_R ⟶ 𝒮_U`, and the square

    𝒮_R ---s---> 𝒮_U
     |            |
     t            π
     v            v
    𝒮_U ---π---> [U/R]

commutes only up to a 2-morphism. This file constructs that 2-morphism and identifies its
components: at a point of the arrow space it is the image under stackification of the arrow of
the pointwise groupoid named by that point.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackTwoArrow`: **Stacks 044S**, the canonical 2-morphism
  `π ∘ s ⟶ π ∘ t` making the square above 2-commutative. This also carries **Stacks 04M7**,
  which is the same square written in the abbreviated notation that drops `𝒮_(-)`, displaying
  it as `R ⇉ U → [U/R]`; the abbreviation changes the notation and not the mathematics.

## Main results

* `AlgebraicGeometry.Stack.quotientStackTwoArrow_app`: **Stacks 044S**, the pointwise
  description — each component of the 2-morphism is the image, under the map from the pointwise
  groupoid fibration to the quotient stack, of an arrow lying over the identity whose underlying
  element of the arrow space is the given point.
* `AlgebraicGeometry.Stack.quotientStackTwoArrow_app_compose`: **the 2-morphism is
  multiplicative** — its component at a composite of two composable arrows of the groupoid is the
  composite of its components at the two factors, after the transports identifying the endpoints.
  This is what identifies the composition law of the self-intersection groupoid of Stacks 04T4 (4)
  at the atlas of a presentation with the composition law of the presenting groupoid; it is read
  off the pointwise description through
  `AlgebraicGeometry.Stack.pointwiseHom_eq_comp_of_arrow_compose`, the same statement one level
  down, in the pointwise groupoid fibration.

## Implementation notes

Both legs of the square are functors over the big fppf site, so a `BasedNatTrans` carries both
the 2-commutativity and the compatibility with pullback; `isHomLift'` is exactly the statement
that every component lies over an identity of the site.

The construction factors through the *pointwise* groupoid fibration rather than its
stackification: at a point `x` of `𝒮_R` the arrow `directArrowAt` is the arrow of the evaluated
groupoid named by `x` itself, from `s(x)` to `t(x)`, and the component of the 2-morphism is its
image under `AlgebraicGeometry.Stack.pointwiseToQuotientStack`. The two `eqToHom`s in
`pointwiseArrowAt` reconcile that arrow with the endpoints `associatedMap` actually produces,
whose fibre components are only *heterogeneously* equal to `s(x)` and `t(x)`; `associatedMapObj_eq`
upgrades that to an equality of objects of the Grothendieck construction.

Naturality is checked on the two halves of an arrow of the Grothendieck construction separately,
through `pointwiseHom_ext`: the base components by `eqToHom` bookkeeping, and the fibre components
by transporting the underlying element of the arrow space along the base arrow. Because the fibres
of `AlgebraicGeometry.Stack.fibredCategory` are discrete, the arrows coming out of
`quotientStackProjection_map` are identities in their fibres, which is what
`pointwiseComp_arrow_of_left_identity` and `pointwiseComp_arrow_of_right_identity` exploit.

Both the 2-morphism and its pointwise description are extracted from one existence statement, so
that the description is available for the very arrow the definition chooses.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w u₁ v₁ u₂ v₂

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/- An object of the pointwise groupoid fibration is an object of a Grothendieck construction
indexed through `CategoryTheory.Functor.toPseudofunctor'`, reached through
`CategoryTheory.BasedCategory.ofFunctor`; neither is unfolded at `implicit` transparency, so a
goal naming both such an object and its `base` or `fiber` is not type-correct there and `rw` and
`simp` refuse it. Naming that chain — the same three definitions
`CategoryTheory.PresheafOfCategories` names, together with the two that present a based category
and the fibres of `fibredCategory` — is what lets the ordinary tactics see through it. -/
attribute [local implicit_reducible] Bicategory.InducedBicategory fibredCategory
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  BasedCategory.ofFunctor Grpd.forgetToCat Grpd.of

/-- Two arrows conjugated by transports, composed so that the transports at the shared end
cancel, give the transported composite. Stated in an abstract category because that is where
`eqToHom` bookkeeping is routine; in the quotient stack the category is a field of an opaque
definition and the associativity and `eqToHom` simp lemmas no longer key-match. -/
theorem eqToHom_comp_cancel_middle {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A A' M M' Z Z' : 𝒞}
    (h₁ : A = A') (h₂ : M' = M) (h₃ : Z = Z') (u : A' ⟶ M) (v : M ⟶ Z) :
    (eqToHom h₁ ≫ u ≫ eqToHom h₂.symm) ≫ eqToHom h₂ ≫ v ≫ eqToHom h₃ =
      eqToHom h₁ ≫ (u ≫ v) ≫ eqToHom h₃ := by
  subst h₁ h₂ h₃
  simp

/-- The image of an arrow conjugated by two transports is its image conjugated by the two
transported transports. Stated in abstract categories so that the `eqToHom` simp lemmas apply;
over the quotient stack they do not, because the projection is a field of an opaque
definition. -/
theorem map_eqToHom_comp_comp_eqToHom {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂}
    [Category.{v₂} 𝒟] (F : 𝒞 ⥤ 𝒟) {A A' Z Z' : 𝒞} (h₁ : A = A') (f : A' ⟶ Z) (h₂ : Z = Z') :
    F.map (eqToHom h₁ ≫ f ≫ eqToHom h₂) =
      eqToHom (congrArg F.obj h₁) ≫ F.map f ≫ eqToHom (congrArg F.obj h₂) := by
  subst h₁ h₂
  simp

/-- A four-fold composite of transports is the transport along the composite equality. Stated in
an abstract category for the same reason as `eqToHom_comp_cancel_middle`. -/
theorem eqToHom_comp_four {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A A' M M' Z : 𝒞}
    (h₁ : A = A') (h₂ : A' = M) (h₃ : M = M') (h₄ : M' = Z) (h : A = Z) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ eqToHom h₃) ≫ eqToHom h₄ = eqToHom h := by
  subst h₁ h₂ h₃ h₄
  simp

/-- A functor carries a two-factor composite conjugated by three transports to the composite of
the images conjugated by the transported transports. Stated in abstract categories for the same
reason as `eqToHom_comp_cancel_middle`. -/
theorem map_eqToHom_comp_two_comp_eqToHom {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂}
    [Category.{v₂} 𝒟] (F : 𝒞 ⥤ 𝒟) {A A' M M' Z Z' : 𝒞}
    (h₁ : A = A') (u : A' ⟶ M) (h₂ : M = M') (t : M' ⟶ Z) (h₃ : Z = Z') :
    F.map (eqToHom h₁ ≫ u ≫ eqToHom h₂ ≫ t ≫ eqToHom h₃) =
      eqToHom (congrArg F.obj h₁) ≫ F.map u ≫ eqToHom (congrArg F.obj h₂) ≫ F.map t ≫
        eqToHom (congrArg F.obj h₃) := by
  subst h₁ h₂ h₃
  simp

/-- A two-factor composite is the conjugate, by two transports and their inverses, of itself
followed by one of them. Stated in an abstract category for the same reason as
`eqToHom_comp_cancel_middle`. -/
theorem eqToHom_conj_cancel {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A B M N Z Zc : 𝒞}
    (h₁ : B = A) (h₂ : Z = Zc) (u : A ⟶ M) (w : M ⟶ N) (t : N ⟶ Z) :
    (u ≫ w) ≫ t =
      eqToHom h₁.symm ≫ (eqToHom h₁ ≫ u ≫ w ≫ t ≫ eqToHom h₂) ≫ eqToHom h₂.symm := by
  subst h₁ h₂
  simp

/-- Two isomorphisms between objects identified by equalities are heterogeneously equal as soon
as their inverses agree after conjugating by the two transports. Stated in an abstract category
for the same reason as `eqToHom_comp_cancel_middle`. -/
theorem heq_iso_of_inv_eq_conj {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X X' Y Y' : 𝒞}
    (hX : X = X') (hY : Y = Y') (i : X ≅ Y) (j : X' ≅ Y')
    (hij : i.inv = eqToHom hY ≫ j.inv ≫ eqToHom hX.symm) : HEq i j := by
  subst hX hY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hij
  exact heq_of_eq (Iso.ext ((Iso.inv_eq_inv i j).1 hij))

/-- Transporting a section along an equality of objects of the base, read in the opposite
category, returns the underlying element of a heterogeneously equal discrete point. -/
theorem map_eqToHom_of_heq {D : Type v} [Category.{u} D]
    {F : Dᵒᵖ ⥤ Type u} {X Y : D} (h : Y = X)
    {a : F.obj (Opposite.op X)} {b : Discrete (F.obj (Opposite.op Y))}
    (hab : HEq (Discrete.mk a) b) :
    F.map (eqToHom h).op a = b.as := by
  cases h
  show (F.map (𝟙 (Opposite.op X))) a = b.as
  rw [Functor.map_id_apply]
  exact congrArg Discrete.as (eq_of_heq hab)

/-- Transporting a section along an equality of objects of the base changes nothing, up to
heterogeneous equality. -/
theorem map_eqToHom_heq {D : Type v} [Category.{u} D]
    {F : Dᵒᵖ ⥤ Type u} {X Y : D} (h : Y = X)
    (a : F.obj (Opposite.op X)) :
    HEq (F.map (eqToHom h).op a) a := by
  cases h
  show (F.map (𝟙 (Opposite.op X))) a ≍ a
  rw [Functor.map_id_apply]

/-- The arrow of the pointwise groupoid fibration named by a point `x` of the arrow space: it
lies over the identity of the base and its underlying element of the arrow space is `x`
itself, so it runs from the source of `x` to the target of `x`. -/
noncomputable def directArrowAt
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    (⟨x.base, G.source.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ :
        (presheafOfGroupoids
          (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
      ⟨x.base, G.target.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ :=
  ⟨𝟙 x.base,
    (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op x.base) _ _).symm
      ⟨Discrete.as x.fiber, rfl, by
        change _ = (G.toGroupoidInFunctors.objects.map
          (𝟙 (Opposite.op x.base))) _
        exact (G.toGroupoidInFunctors.objects.map_id_apply
          (Opposite.op x.base) _).symm⟩⟩

/-- Postcomposing with an arrow coming from an equality of endpoints does not change the
underlying element of the arrow space. -/
theorem evaluationArrow_comp_eqToHom
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y z : G.Evaluation T} (a : x ⟶ y) (h : y = z) :
    (G.evaluationArrowEquiv T _ _ (a ≫ eqToHom h)).1 =
      (G.evaluationArrowEquiv T _ _ a).1 := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]

/-- Precomposing with an arrow coming from an equality of endpoints does not change the
underlying element of the arrow space. -/
theorem evaluationArrow_eqToHom_comp
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y z : G.Evaluation T} (h : x = y) (a : y ⟶ z) :
    (G.evaluationArrowEquiv T _ _ (eqToHom h ≫ a)).1 =
      (G.evaluationArrowEquiv T _ _ a).1 := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]

/-- Converse to `evaluationArrow_eqToHom_identity`: an arrow of an evaluated groupoid whose
underlying element of the arrow space is an identity has equal endpoints, and is the arrow that
equality induces. -/
theorem evaluationArrow_eqToHom_of_identity
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : G.Evaluation T} (a : x ⟶ y)
    (ha : (G.evaluationArrowEquiv T _ _ a).1 = G.identity T x) :
    ∃ h : x = y, a = eqToHom h := by
  have h : x = y := ((G.evaluationArrowEquiv T x x (𝟙 x)).2.2).symm.trans
    ((congrArg (G.target.app T) ha).symm.trans (G.evaluationArrowEquiv T _ _ a).2.2)
  refine ⟨h, ?_⟩
  subst y
  exact (G.evaluationArrowEquiv T _ _).injective (Subtype.ext ha)

/-- The 1-morphism induced by a map `a` of presheaves sends a point of the attached fibred
category to the point of the pointwise groupoid fibration with the same base and with fibre the
value of `a` there. -/
theorem associatedMapObj_eq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (a : G.arrows.obj ⟶ G.objects.obj)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    let y := (CatFiberedInGroupoids.homFunctor (associatedMap C S hS a).1).obj x
    (⟨y.base, y.fiber.as⟩ : (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) =
      ⟨x.base, a.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ := by
  let y := (CatFiberedInGroupoids.homFunctor (associatedMap C S hS a).1).obj x
  have hb : y.base = x.base := (associatedMap C S hS a).1.hom.w_obj x
  have hv := map_eqToHom_of_heq (F := G.toGroupoidInFunctors.objects) hb
    ((associatedMap C S hS a).2 x).symm
  have hm := map_eqToHom_heq (F := G.toGroupoidInFunctors.objects) hb
    (a.app (Opposite.op x.base) (Discrete.as x.fiber))
  apply (PresheafOfCategories.objEquiv
    (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat)).injective
  exact Sigma.ext hb ((heq_of_eq hv.symm).trans hm)

/-- The arrow `directArrowAt`, transported to run between the two points that the source and
target maps of `G` actually produce in the pointwise groupoid fibration. -/
noncomputable def pointwiseArrowAt
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    let xs := (CatFiberedInGroupoids.homFunctor
      (associatedMap C S hS G.source.hom).1).obj x
    let xt := (CatFiberedInGroupoids.homFunctor
      (associatedMap C S hS G.target.hom).1).obj x
    ((⟨xs.base, xs.fiber.as⟩ : (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶ ⟨xt.base, xt.fiber.as⟩) :=
  eqToHom (associatedMapObj_eq G G.source.hom x) ≫ directArrowAt G x ≫
    eqToHom (associatedMapObj_eq G G.target.hom x).symm

/-- The base component of an arrow of the pointwise groupoid fibration coming from an equality
of its endpoints. -/
theorem pointwiseEqToHom_base
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {X Y : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Pseudofunctor.CoGrothendieck.base h) := by
  cases h
  rfl

/-- Conjugating an arrow of the pointwise groupoid fibration by equalities of its endpoints
transports its underlying element of the arrow space along the induced base arrow. -/
theorem pointwiseConj_arrow
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {X X' Y Y' : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj}
    (hx : X = X') (hy : Y = Y') (f : X' ⟶ Y') :
    (G.evaluationArrowEquiv (Opposite.op X.base) _ _
      (eqToHom hx ≫ f ≫ eqToHom hy.symm).fiber).1 =
    G.arrows.map (eqToHom (congrArg Pseudofunctor.CoGrothendieck.base hx)).op
      (G.evaluationArrowEquiv (Opposite.op X'.base) _ _ f.fiber).1 := by
  cases hx
  cases hy
  simp only [eqToHom_refl, op_id, Functor.map_id_apply]
  exact congrArg (fun k : X ⟶ Y =>
    (G.evaluationArrowEquiv (Opposite.op X.base) _ _ k.fiber).1) (by simp)

/-- The underlying element of the arrow space of a composite in the pointwise groupoid
fibration, written inside the fibre over the source. -/
theorem pointwiseComp_arrow
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {X Y Z : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (G.evaluationArrowEquiv (Opposite.op X.base) _ _ (f ≫ g).fiber).1 =
      (G.evaluationArrowEquiv (Opposite.op X.base) _ _
        (f.fiber ≫ (Deformation.evaluationMap G f.base.op).map g.fiber)).1 := by
  rw [PresheafOfCategories.comp_fiber, ← Category.assoc]
  exact evaluationArrow_comp_eqToHom G _ _ _

/-- Composing with an arrow that is an identity in its fibre transports the other factor along
the base. -/
theorem pointwiseComp_arrow_of_left_identity
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {X Y Z : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (G.evaluationArrowEquiv (Opposite.op X.base) _ _ f.fiber).1 =
      G.identity (Opposite.op X.base) X.fiber) :
    (G.evaluationArrowEquiv (Opposite.op X.base) _ _ (f ≫ g).fiber).1 =
      G.arrows.map f.base.op (G.evaluationArrowEquiv (Opposite.op Y.base) _ _ g.fiber).1 := by
  obtain ⟨h, he⟩ := evaluationArrow_eqToHom_of_identity G _ f.fiber hf
  rw [pointwiseComp_arrow G, he]
  exact (evaluationArrow_eqToHom_comp G _ _ _).trans
    (Deformation.evaluationMap_map_arrow G _ _)

/-- Composing with an arrow that is an identity in its fibre leaves the other factor
unchanged. -/
theorem pointwiseComp_arrow_of_right_identity
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {X Y Z : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : (G.evaluationArrowEquiv (Opposite.op Y.base) _ _ g.fiber).1 =
      G.identity (Opposite.op Y.base) Y.fiber) :
    (G.evaluationArrowEquiv (Opposite.op X.base) _ _ (f ≫ g).fiber).1 =
      (G.evaluationArrowEquiv (Opposite.op X.base) _ _ f.fiber).1 := by
  obtain ⟨h, he⟩ := evaluationArrow_eqToHom_of_identity G _ g.fiber hg
  rw [pointwiseComp_arrow G, he, eqToHom_map]
  exact evaluationArrow_comp_eqToHom G _ _ _

/-- The source and the target of the underlying element of the arrow space of an arrow of the
pointwise groupoid fibration which lies over an identity of the base are its two endpoints. -/
theorem pointwiseArrow_endpoints_of_base_id
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {T : D} {x y : G.Evaluation (Opposite.op T)}
    (f : (⟨T, x⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj) ⟶ ⟨T, y⟩)
    (hf : f.base = 𝟙 T) :
    G.source.app (Opposite.op T)
          (G.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1 = x ∧
      G.target.app (Opposite.op T)
          (G.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1 = y := by
  have h := (G.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).2
  refine ⟨h.1, h.2.trans ?_⟩
  show G.objects.map f.base.op y = y
  rw [hf]
  exact G.objects.map_id_apply (Opposite.op T) y

/-- Composition in a groupoid in functors depends only on the two arrows, not on the proof that
they are composable. -/
private theorem compose_congr_of_eq {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ) {T : Dᵒᵖ}
    {a a' b b' : G.arrows.obj T} (ha : a = a') (hb : b = b')
    (h : G.source.app T a = G.target.app T b) (h' : G.source.app T a' = G.target.app T b') :
    G.compose T a b h = G.compose T a' b' h' := by
  subst ha hb
  rfl

/-- **The underlying element of the arrow space of a composite of two arrows of the pointwise
groupoid fibration lying over an identity of the base is the composite in the groupoid**, in the
order the composition law of a groupoid in functors uses. -/
theorem pointwiseComp_arrow_of_base_id
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {T : D} {x y z : G.Evaluation (Opposite.op T)}
    (f : (⟨T, x⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj) ⟶ ⟨T, y⟩)
    (g : (⟨T, y⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj) ⟶ ⟨T, z⟩)
    (hf : f.base = 𝟙 T)
    (hcomp : G.source.app (Opposite.op T)
          (G.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1 =
        G.target.app (Opposite.op T)
          (G.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1) :
    (G.evaluationArrowEquiv (Opposite.op T) _ _ (f ≫ g).fiber).1 =
      G.compose (Opposite.op T)
        (G.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1
        (G.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1 hcomp := by
  refine Eq.trans (pointwiseComp_arrow G f g) ?_
  refine Eq.trans (G.evaluationArrowEquiv_comp (Opposite.op T) f.fiber
    ((Deformation.evaluationMap G f.base.op).map g.fiber)) ?_
  have hv : (G.evaluationArrowEquiv (Opposite.op T) _ _
        ((Deformation.evaluationMap G f.base.op).map g.fiber)).1 =
      (G.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1 := by
    refine Eq.trans (Deformation.evaluationMap_map_arrow G f.base.op g.fiber) ?_
    rw [hf]
    exact G.arrows.map_id_apply (Opposite.op T) _
  exact compose_congr_of_eq G hv rfl _ _

/-- Two arrows of the pointwise groupoid fibration with the same base component and the same
underlying element of the arrow space are equal. -/
theorem pointwiseHom_ext
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {X Y : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj}
    {f g : X ⟶ Y} (hb : f.base = g.base)
    (ha : (G.evaluationArrowEquiv (Opposite.op X.base) _ _ f.fiber).1 =
      (G.evaluationArrowEquiv (Opposite.op X.base) _ _ g.fiber).1) : f = g := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext f g hb
  apply (G.evaluationArrowEquiv _ _ _).injective
  apply Subtype.ext
  exact ha.trans (evaluationArrow_comp_eqToHom G _ _ _).symm

/-- **Multiplicativity of the arrows of the pointwise groupoid fibration lying over an identity
of the base.** An arrow whose underlying element of the arrow space is the composite of those of
two others is their composite, after the transports identifying the three pairs of endpoints. -/
theorem pointwiseHom_eq_comp_of_arrow_compose
    {D : Type u} [Category.{v} D]
    (G : Deformation.GroupoidInFunctors.{u, v, w} Dᵒᵖ)
    {T : D} {xa ya xb yb xc yc : G.Evaluation (Opposite.op T)}
    (f : (⟨T, xb⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj) ⟶ ⟨T, yb⟩)
    (g : (⟨T, xa⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj) ⟶ ⟨T, ya⟩)
    (w : (⟨T, xc⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj) ⟶ ⟨T, yc⟩)
    (hf : f.base = 𝟙 T) (hg : g.base = 𝟙 T) (hw : w.base = 𝟙 T)
    (hm : yb = xa) (hx : xc = xb) (hy : ya = yc)
    (hcomp : G.source.app (Opposite.op T)
          (G.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1 =
        G.target.app (Opposite.op T)
          (G.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1)
    (harrow : (G.evaluationArrowEquiv (Opposite.op T) _ _ w.fiber).1 =
      G.compose (Opposite.op T)
        (G.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1
        (G.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1 hcomp) :
    w = eqToHom (congrArg
          (fun z => (⟨T, z⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj)) hx) ≫
        f ≫ eqToHom (congrArg
          (fun z => (⟨T, z⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj)) hm) ≫
        g ≫ eqToHom (congrArg
          (fun z => (⟨T, z⟩ : (presheafOfGroupoids (evaluationGroupoidFunctor G)).obj)) hy) := by
  subst hm hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine pointwiseHom_ext G ?_ ?_
  · show w.base = f.base ≫ g.base
    rw [hf, hg, hw, Category.id_comp]
  · exact harrow.trans (pointwiseComp_arrow_of_base_id G f g hf hcomp).symm

/-- The base component of `pointwiseArrowAt` is the comparison of the two bases, which both
agree with the base of the given point. -/
theorem pointwiseArrowAt_base
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    (pointwiseArrowAt G x).base =
      eqToHom (((associatedMap C S hS G.source.hom).1.hom.w_obj x).trans
        ((associatedMap C S hS G.target.hom).1.hom.w_obj x).symm) := by
  simp only [pointwiseArrowAt, Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
    pointwiseEqToHom_base G.toGroupoidInFunctors, directArrowAt, Category.id_comp,
    eqToHom_trans]
  rfl

/-- The underlying element of the arrow space of `directArrowAt` is the given point. -/
theorem directArrowAt_arrow
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op x.base) _ _
      (directArrowAt G x).fiber).1 = Discrete.as x.fiber :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The underlying element of the arrow space of `pointwiseArrowAt` is the given point, carried
along the comparison of bases. -/
theorem pointwiseArrowAt_arrow
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _ (pointwiseArrowAt G x).fiber).1 =
      G.toGroupoidInFunctors.arrows.map
        (eqToHom ((associatedMap C S hS G.source.hom).1.hom.w_obj x)).op x.fiber.as :=
  (pointwiseConj_arrow G.toGroupoidInFunctors (associatedMapObj_eq G G.source.hom x)
      (associatedMapObj_eq G G.target.hom x) (directArrowAt G x)).trans
    (congrArg (fun a => G.toGroupoidInFunctors.arrows.map
        (eqToHom ((associatedMap C S hS G.source.hom).1.hom.w_obj x)).op a)
      (directArrowAt_arrow G x))

/-- The projection of a quotient stack to the site sends a transport to a transport. This is
`CategoryTheory.eqToHom_map` with the functor fixed, so that it has a concrete head and the
rewriting tactics find it in a goal about the quotient stack. -/
theorem quotientStack_p_map_eqToHom (G : GroupoidInAlgebraicSpaces C S hS B)
    {X Y : (quotientStack G).obj} (h : X = Y) :
    (quotientStack G).p.map (eqToHom h) = eqToHom (congrArg (quotientStack G).p.obj h) :=
  eqToHom_map _ h

/-- The 2-morphism of Stacks 044S, constructed with its components. -/
noncomputable def constructedTwoArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
        (quotientStackProjection G) ⟶
      BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
        (quotientStackProjection G) := by
  let F := BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
    (quotientStackProjection G)
  let H := BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
    (quotientStackProjection G)
  let component : ∀ x : (fibredCategory C S hS G.arrows.obj).val.obj,
      F.obj x ⟶ H.obj x := fun x => by
        let xs := (CatFiberedInGroupoids.homFunctor
          (associatedMap C S hS G.source.hom).1).obj x
        let xt := (CatFiberedInGroupoids.homFunctor
          (associatedMap C S hS G.target.hom).1).obj x
        change (quotientStackProjection G).obj xs ⟶ (quotientStackProjection G).obj xt
        let hs := quotientStackProjection_obj G xs
        let ht := quotientStackProjection_obj G xt
        exact eqToHom hs ≫
          (pointwiseToQuotientStack G).map (pointwiseArrowAt G x) ≫ eqToHom ht.symm
  let η : F.toFunctor ⟶ H.toFunctor := {
    app := component
    naturality := by
      intro X Y f
      let sMap := (associatedMap C S hS G.source.hom).1
      let tMap := (associatedMap C S hS G.target.hom).1
      let fs := CatFiberedInGroupoids.homFunctor sMap
      let ft := CatFiberedInGroupoids.homFunctor tMap
      obtain ⟨gs, hgsBase, hgsArrow, hgsMap⟩ := quotientStackProjection_map G (fs.map f)
      obtain ⟨gt, hgtBase, hgtArrow, hgtMap⟩ := quotientStackProjection_map G (ft.map f)
      have hdata : X.fiber.as = G.toGroupoidInFunctors.arrows.map f.base.op Y.fiber.as := by
        have hf := f.fiber
        change X.fiber ⟶ Discrete.mk
          (G.toGroupoidInFunctors.arrows.map f.base.op Y.fiber.as) at hf
        exact Discrete.eq_of_hom hf
      have hfsbase : (fs.map f).base =
          eqToHom (BasedFunctor.w_obj sMap.hom X) ≫ f.base ≫
            eqToHom (BasedFunctor.w_obj sMap.hom Y).symm := by
        have hh := Functor.congr_hom sMap.hom.w f
        change (fs.map f).base = _ at hh
        exact hh
      have hftbase : (ft.map f).base =
          eqToHom (BasedFunctor.w_obj tMap.hom X) ≫ f.base ≫
            eqToHom (BasedFunctor.w_obj tMap.hom Y).symm := by
        have hh := Functor.congr_hom tMap.hom.w f
        change (ft.map f).base = _ at hh
        exact hh
      change (quotientStackProjection G).map (fs.map f) ≫ component Y =
        component X ≫ (quotientStackProjection G).map (ft.map f)
      rw [hgsMap, hgtMap]
      have hpoint : gs ≫ pointwiseArrowAt G Y = pointwiseArrowAt G X ≫ gt := by
        have hsX : (fs.obj X).base = X.base := sMap.hom.w_obj X
        have hsY : (fs.obj Y).base = Y.base := sMap.hom.w_obj Y
        have htX : (ft.obj X).base = X.base := tMap.hom.w_obj X
        have htY : (ft.obj Y).base = Y.base := tMap.hom.w_obj Y
        have htransport : G.toGroupoidInFunctors.arrows.map (eqToHom hsX).op X.fiber.as =
            G.toGroupoidInFunctors.arrows.map (eqToHom hsX ≫ f.base).op Y.fiber.as := by
          rw [hdata]
          simpa only [← op_comp] using
            (G.toGroupoidInFunctors.arrows.map_comp_apply
              f.base.op (eqToHom hsX).op Y.fiber.as).symm
        apply pointwiseHom_ext G.toGroupoidInFunctors
        · change gs.base ≫ (pointwiseArrowAt G Y).base =
            (pointwiseArrowAt G X).base ≫ gt.base
          rw [hgsBase, hgtBase, hfsbase, hftbase, pointwiseArrowAt_base G Y,
            pointwiseArrowAt_base G X]
          change (eqToHom hsX ≫ f.base ≫ eqToHom hsY.symm) ≫ eqToHom (hsY.trans htY.symm) =
            eqToHom (hsX.trans htX.symm) ≫ eqToHom htX ≫ f.base ≫ eqToHom htY.symm
          simp [eqToHom_trans, Category.assoc]
        · refine (pointwiseComp_arrow_of_left_identity G.toGroupoidInFunctors
            gs (pointwiseArrowAt G Y) hgsArrow).trans (Eq.trans ?_
              (pointwiseComp_arrow_of_right_identity G.toGroupoidInFunctors
                (pointwiseArrowAt G X) gt hgtArrow).symm)
          rw [pointwiseArrowAt_arrow G Y, pointwiseArrowAt_arrow G X, hgsBase, hfsbase]
          refine (G.toGroupoidInFunctors.arrows.map_comp_apply (eqToHom hsY).op
            (eqToHom hsX ≫ f.base ≫ eqToHom hsY.symm).op Y.fiber.as).symm.trans ?_
          simp only [← op_comp, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          exact htransport.symm
      have hmapped := congrArg (fun k => (pointwiseToQuotientStack G).map k) hpoint
      have hmapped' :
          (pointwiseToQuotientStack G).map gs ≫
              (pointwiseToQuotientStack G).map (pointwiseArrowAt G Y) =
            (pointwiseToQuotientStack G).map (pointwiseArrowAt G X) ≫
              (pointwiseToQuotientStack G).map gt :=
        ((pointwiseToQuotientStack G).map_comp gs (pointwiseArrowAt G Y)).symm.trans <|
          hmapped.trans ((pointwiseToQuotientStack G).map_comp (pointwiseArrowAt G X) gt)
      exact (eqToHom_comp_cancel_middle (quotientStackProjection_obj G (fs.obj X))
          (quotientStackProjection_obj G (fs.obj Y))
          (quotientStackProjection_obj G (ft.obj Y)).symm
          ((pointwiseToQuotientStack G).map gs)
          ((pointwiseToQuotientStack G).map (pointwiseArrowAt G Y))).trans
        ((congrArg (fun m => eqToHom (quotientStackProjection_obj G (fs.obj X)) ≫ m ≫
            eqToHom (quotientStackProjection_obj G (ft.obj Y)).symm) hmapped').trans
          (eqToHom_comp_cancel_middle (quotientStackProjection_obj G (fs.obj X))
            (quotientStackProjection_obj G (ft.obj X))
            (quotientStackProjection_obj G (ft.obj Y)).symm
            ((pointwiseToQuotientStack G).map (pointwiseArrowAt G X))
            ((pointwiseToQuotientStack G).map gt)).symm)
  }
  refine { toNatTrans := η, isHomLift' := ?_ }
  intro a
  apply IsHomLift.of_fac' (quotientStack G).p
    (𝟙 ((fibredCategory C S hS G.arrows.obj).val.p.obj a))
    (component a) (BasedFunctor.w_obj F a) (BasedFunctor.w_obj H a)
  change (quotientStack G).p.map
      (eqToHom _ ≫ (pointwiseToQuotientStack G).map (pointwiseArrowAt G a) ≫ eqToHom _) = _
  refine Eq.trans (map_eqToHom_comp_comp_eqToHom (quotientStack G).p _ _ _) ?_
  have hcomp := Functor.congr_hom
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq (pointwiseArrowAt G a)
  have hbase : (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.map (pointwiseArrowAt G a) =
        (pointwiseArrowAt G a).base := rfl
  change (quotientStack G).p.map
      ((pointwiseToQuotientStack G).map (pointwiseArrowAt G a)) = _ at hcomp
  rw [hcomp]
  rw [hbase]
  simp only [Bicategory.InducedBicategory.bicategory_Hom, Lean.Elab.WF.paramLet,
    Functor.comp_obj, pointwiseArrowAt_base, Category.assoc, eqToHom_trans_assoc,
    BasedFunctor.w_obj, eqToHom_naturality, Category.comp_id, eqToHom_trans]
  exact eqToHom_comp_four _ _ _ _ _

/-- Each component of `constructedTwoArrow` is the image of `directArrowAt`, up to the
transports that reconcile the endpoints. -/
theorem constructedTwoArrow_app_heq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    HEq ((constructedTwoArrow G).app x)
      ((pointwiseToQuotientStack G).map (directArrowAt G x)) := by
  show HEq (eqToHom _ ≫ (pointwiseToQuotientStack G).map
    (pointwiseArrowAt G x) ≫ eqToHom _) _
  rw [pointwiseArrowAt]
  simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- The pointwise description of `constructedTwoArrow`. -/
theorem constructedTwoArrow_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    ∃ g : (⟨x.base, G.source.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
        ⟨x.base, G.target.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩,
      g.base = 𝟙 x.base ∧
      (G.toGroupoidInFunctors.evaluationArrowEquiv
        (Opposite.op x.base) _ _ g.fiber).1 = Discrete.as x.fiber ∧
      HEq ((constructedTwoArrow G).app x) ((pointwiseToQuotientStack G).map g) :=
  ⟨directArrowAt G x, rfl, directArrowAt_arrow G x, constructedTwoArrow_app_heq G x⟩

/-- Existence of a 2-morphism with the pointwise description of Stacks 044S. Extracting both
the 2-morphism and its description from one statement is what makes the description apply to
the 2-morphism the definition below chooses. -/
theorem exists_quotientStackTwoArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    ∃ η : BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
        (quotientStackProjection G) ⟶
      BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
        (quotientStackProjection G),
    ∀ x : (fibredCategory C S hS G.arrows.obj).val.obj,
    ∃ g : (⟨x.base, G.source.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
        ⟨x.base, G.target.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩,
      g.base = 𝟙 x.base ∧
      (G.toGroupoidInFunctors.evaluationArrowEquiv
        (Opposite.op x.base) _ _ g.fiber).1 = Discrete.as x.fiber ∧
      HEq (η.app x) ((pointwiseToQuotientStack G).map g) :=
  ⟨constructedTwoArrow G, constructedTwoArrow_app G⟩

/-- **Stacks 044S.** The canonical 2-morphism between the source and target maps to a quotient
stack, making the square of Stacks 044R 2-commutative. Its components are the images of the
groupoid arrows. -/
@[stacks 044S,
  stacks 04M7 "remark restating the 2-commutative square in the X-for-S_X notation"]
noncomputable def quotientStackTwoArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
        (quotientStackProjection G) ⟶
      BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
        (quotientStackProjection G) :=
  Classical.choose (exists_quotientStackTwoArrow G)

/-- **Stacks 044S.** At a point of the arrow space, the canonical 2-morphism is the image of
that groupoid arrow under the pointwise-groupoid map to the quotient stack. -/
@[stacks 044S "pointwise description"]
theorem quotientStackTwoArrow_app
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    ∃ g : (⟨x.base, G.source.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶
        ⟨x.base, G.target.hom.app (Opposite.op x.base) (Discrete.as x.fiber)⟩,
      g.base = 𝟙 x.base ∧
      (G.toGroupoidInFunctors.evaluationArrowEquiv
        (Opposite.op x.base) _ _ g.fiber).1 = Discrete.as x.fiber ∧
      HEq ((quotientStackTwoArrow G).app x) ((pointwiseToQuotientStack G).map g) :=
  Classical.choose_spec (exists_quotientStackTwoArrow G) x

/-- **The canonical 2-morphism of Stacks 044S is multiplicative.** At a composite of two
composable arrows of the groupoid it is the composite of the 2-morphism at the two factors, after
the transports identifying the endpoints: the source of the composite is the source of the second
factor, the target of the second factor is the source of the first, and the target of the
composite is the target of the first. -/
theorem quotientStackTwoArrow_app_compose
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : BigFppfOver C S hS}
    (a b : G.arrows.obj.obj (Opposite.op T))
    (h : G.source.hom.app (Opposite.op T) a = G.target.hom.app (Opposite.op T) b)
    (hs : (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
            (quotientStackProjection G)).toFunctor.obj
          ⟨T, Discrete.mk (G.toGroupoidInFunctors.compose (Opposite.op T) a b h)⟩ =
        (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
            (quotientStackProjection G)).toFunctor.obj ⟨T, Discrete.mk b⟩)
    (hm : (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
            (quotientStackProjection G)).toFunctor.obj ⟨T, Discrete.mk b⟩ =
        (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
            (quotientStackProjection G)).toFunctor.obj ⟨T, Discrete.mk a⟩)
    (ht : (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
            (quotientStackProjection G)).toFunctor.obj ⟨T, Discrete.mk a⟩ =
        (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
            (quotientStackProjection G)).toFunctor.obj
          ⟨T, Discrete.mk (G.toGroupoidInFunctors.compose (Opposite.op T) a b h)⟩) :
    (quotientStackTwoArrow G).app
        ⟨T, Discrete.mk (G.toGroupoidInFunctors.compose (Opposite.op T) a b h)⟩ =
      eqToHom hs ≫ (quotientStackTwoArrow G).app ⟨T, Discrete.mk b⟩ ≫ eqToHom hm ≫
        (quotientStackTwoArrow G).app ⟨T, Discrete.mk a⟩ ≫ eqToHom ht := by
  obtain ⟨gc, hgcb, hgca, hgch⟩ := quotientStackTwoArrow_app G
    ⟨T, Discrete.mk (G.toGroupoidInFunctors.compose (Opposite.op T) a b h)⟩
  obtain ⟨gb, hgbb, hgba, hgbh⟩ := quotientStackTwoArrow_app G ⟨T, Discrete.mk b⟩
  obtain ⟨ga, hgab, hgaa, hgah⟩ := quotientStackTwoArrow_app G ⟨T, Discrete.mk a⟩
  have hcomp : G.toGroupoidInFunctors.source.app (Opposite.op T)
        (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ ga.fiber).1 =
      G.toGroupoidInFunctors.target.app (Opposite.op T)
        (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ gb.fiber).1 := by
    rwa [hgaa, hgba]
  have hmul := pointwiseHom_eq_comp_of_arrow_compose G.toGroupoidInFunctors gb ga gc
    hgbb hgab hgcb h.symm
    ((G.toGroupoidInFunctors.pointwiseData (Opposite.op T)).source_comp a b h)
    (((G.toGroupoidInFunctors.pointwiseData (Opposite.op T)).target_comp a b h).symm)
    hcomp (hgca.trans (compose_congr_of_eq G.toGroupoidInFunctors hgaa hgba _ _).symm)
  have hc : (quotientStackTwoArrow G).app
        ⟨T, Discrete.mk (G.toGroupoidInFunctors.compose (Opposite.op T) a b h)⟩ =
      (pointwiseToQuotientStack G).map gc := eq_of_heq hgch
  have hb : (quotientStackTwoArrow G).app ⟨T, Discrete.mk b⟩ =
      (pointwiseToQuotientStack G).map gb := eq_of_heq hgbh
  have ha : (quotientStackTwoArrow G).app ⟨T, Discrete.mk a⟩ =
      (pointwiseToQuotientStack G).map ga := eq_of_heq hgah
  rw [hc, hb, ha, hmul]
  simp only [Functor.map_comp, eqToHom_map]
  rfl

add_to_stacks 04M7 "the two-commutative square of Stacks 044S, in the abbreviated notation \
that writes U for the stack in sets associated to U" quotientStackTwoArrow

end AlgebraicGeometry.Stack

end

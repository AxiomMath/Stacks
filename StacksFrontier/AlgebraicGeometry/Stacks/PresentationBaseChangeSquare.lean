module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackCell
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationBaseChangeRelation

/-!
# The square of the base-changed presentation 2-commutes (Stacks 04Y6, assertion (4))

Let `S` be a scheme of a big fppf site, let `g : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over
`S` representable by algebraic spaces and let `P = ((U, R, s, t, c), ε : [U/R] ≃ 𝒳)` be a
presentation of `𝒳`. The base-changed presentation `ε' : [U'/R'] ≃ 𝒳'` of
`StacksFrontier/AlgebraicGeometry/Stacks/PresentationBaseChangePresentation.lean` and the morphism
of groupoids `pr` of
`StacksFrontier/AlgebraicGeometry/Stacks/PresentationBaseChangeProjection.lean` fit into a square

```
[U'/R'] ---ε'---> 𝒳'
   |               |
  [pr]             g
   v               v
 [U/R] ----ε----> 𝒳
```

and this module builds the 2-isomorphism filling it, which is **Stacks 04Y6, assertion (4)**,
together with the conjunction of all four assertions of the tag.

## The mathematical content

On the pointwise groupoid presentation of `[U'/R']` a point over a test object is a section of
`U'`, and the chosen representative of that section is an object `z = (u, x, ψ)` of
`U' = U ×_𝒳 𝒳'`, so it *carries* the comparison `ψ : a(u) ≅ g(x)` the square needs — the lower
leg lands on `a(u)` and the upper one on `g(x)`. Naturality in an arrow of `R'` is then the
description of `pr` on arrows: the image of `(z₁, z₂, φ)` is `(u₁, u₂, ψ₁ ≫ g(φ) ≫ ψ₂⁻¹)`, so
cancelling the two comparisons leaves the compatibility square of a morphism of
`U' = U ×_𝒳 𝒳'`, which is one field of a morphism of a 2-fibre product.

Reading the lower leg off takes one new ingredient, the arrow part of `ε` on the pointwise
groupoid fibration of `P`'s own groupoid
(`AlgebraicGeometry.Stack.GroupoidPresentation.basedFunctor_map_pointwiseToQuotientStack`): an
arrow factors as one lying over the identity of the site, named by a point of `R`, followed by one
with an identity arrow of the groupoid, and the two factors are the inverse of the comparison
isomorphism of Stacks 04M9 at that point and the canonical restriction of the atlas.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.bcPointwiseUpper` and `...bcPointwiseLower`: the
  two legs of the square, read on the pointwise groupoid presentation of `[U'/R']`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.bcComparisonArrow`: the arrow comparing them at a
  point of `U'`, namely the comparison isomorphism of the chosen representative of that point.
* `AlgebraicGeometry.Stack.GroupoidPresentation.bcSquareUpperCan` and `...bcSquareLower`: the two
  legs of the square themselves.
* `AlgebraicGeometry.Stack.GroupoidPresentation.bcSquareIsoCan`: the 2-isomorphism filling the
  square, produced from the comparison on the presentation by Stacks 04W9.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.basedFunctor_map_pointwiseToQuotientStack`: the
  arrow part of the presenting 1-morphism on the pointwise groupoid fibration.
* `AlgebraicGeometry.Stack.GroupoidPresentation.bcPointwiseUpper_map` and
  `...bcPointwiseLower_map`: the arrow part of each leg.
* `AlgebraicGeometry.Stack.GroupoidPresentation.bcComparisonArrow_naturality` and
  `...bcPointwiseBasedIso`: the two legs agree on the pointwise groupoid presentation of
  `[U'/R']`, through a 2-isomorphism over the big fppf site.
* `AlgebraicGeometry.Stack.GroupoidPresentation.nonempty_bcSquareIso`: **Stacks 04Y6,
  assertion (4)** — the square 2-commutes.
* `AlgebraicGeometry.Stack.GroupoidPresentation.exists_baseChangedPresentationSquare`:
  **Stacks 04Y6, the whole statement** — the four assertions conjoined.

## Implementation notes

Every cancellation and transport identity here is stated in an abstract category or for an
abstract functor (`AlgebraicGeometry.Stack.GroupoidPresentation.naturality_with_transport` and the
six lemmas beside it): the composites they regroup live in `𝒳`, where a goal naming them is not
type-correct at `implicit` transparency — the coercion of a category fibred in groupoids to a
based category is not unfolded there — and `rw` and `simp` therefore refuse to fire on a pattern
that is visibly present. This is the same provision
`StacksFrontier/AlgebraicGeometry/Stacks/PresentationBaseChangeProjection.lean` makes for
`AlgebraicGeometry.Stack.GroupoidPresentation.comp_regroup_middle`.

The two transports of
`AlgebraicGeometry.Stack.GroupoidPresentation.basedFunctor_map_pointwiseToQuotientStack` are
hypotheses rather than terms, so that a caller may supply whichever proofs its own goal carries;
this is the shape
`AlgebraicGeometry.Stack.GroupoidPresentation.arrowToAtlasRelationBase_iso_hom_compose` already
uses.

**Why the filler is produced in the universe lift of `𝒳`.** Stacks 04W9,
`CategoryTheory.Functor.Stackification.restrict_full`, asks its three categories to share a
morphism universe. The presentation and the quotient stack live at morphism universe `u + 1`,
`𝒳` at `u`, so the restriction functor at the target `𝒳` is not the one that lemma speaks about.
Both legs are therefore followed into `AlgebraicGeometry.Stack.SelfIntersection.stackUlift 𝒳`,
which is a stack by Stacks 026F
(`AlgebraicGeometry.Stack.SelfIntersection.isStack_stackUlift`), the filler is produced there, and
the universe lift is undone by its own comparison — lifting and then forgetting being the identity
on the nose. This is the same detour
`StacksFrontier/AlgebraicGeometry/Stacks/SelfIntersectionQuotientMap.lean` makes for Stacks 0436.

## References

* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04W9](https://stacks.math.columbia.edu/tag/04W9)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u w u₁ v₁ u₂ v₂

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

attribute [local implicit_reducible] liftedObjectSpace liftedSpace liftedFibredCategory

/-- Reading a commuting square of transports as a conjugation. Stated in an abstract category:
see the implementation notes. -/
theorem eq_conj_eqToHom_of_comp_eq {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X Y X' Y' : 𝒞}
    (hx : X = X') (hy : Y = Y') (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : eqToHom hx ≫ f' = f ≫ eqToHom hy) :
    f = eqToHom hx ≫ f' ≫ eqToHom hy.symm := by
  subst hx
  subst hy
  simpa using h.symm

/-- The inverse of an isomorphism identified with a conjugate of another. Stated in an abstract
category: see the implementation notes. -/
theorem iso_inv_conj {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A Bb A' B' : 𝒞} (hx : A = A') (hy : Bb = B')
    (i : A ≅ Bb) (i' : A' ≅ B')
    (h : i.hom = eqToHom hx ≫ i'.hom ≫ eqToHom hy.symm) :
    eqToHom hy ≫ i'.inv ≫ eqToHom hx.symm = i.inv := by
  subst hx
  subst hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  exact congrArg Iso.inv (Iso.ext h).symm

/-- Regrouping a composite of three morphisms conjugated by four transports. Stated in an abstract
category: see the implementation notes. -/
theorem eqToHom_conj_regroup {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : 𝒞}
    (h₁ : A₀ = A₁) (h₂ : A₁ = A₂) (h₃ : A₄ = A₃) (h₄ : A₄ = A₅)
    (t : A₂ ⟶ A₃) (u : A₅ ⟶ A₆)
    {v : A₁ ⟶ A₄} (hv : eqToHom h₂ ≫ t ≫ eqToHom h₃.symm = v)
    {ww : A₄ ⟶ A₆} (hw : eqToHom h₄ ≫ u = ww) :
    eqToHom (h₁.trans h₂) ≫ t ≫ eqToHom (h₃.symm.trans h₄) ≫ u =
      eqToHom h₁ ≫ v ≫ ww := by
  subst hv
  subst hw
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  simp

/-- The image of a morphism conjugated by two transports, with the first transport cancelled.
Stated for an abstract functor: see the implementation notes. -/
theorem map_conj_eqToHom {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    (F : 𝒞 ⥤ 𝒟) {A₀ A₁ A₂ A₃ : 𝒞} (h₁ : A₀ = A₁) (h₂ : A₂ = A₃) (ψ : A₁ ⟶ A₂)
    {φ : A₀ ⟶ A₃} (hφ : φ = eqToHom h₁ ≫ ψ ≫ eqToHom h₂) :
    eqToHom (congrArg F.obj h₁).symm ≫ F.map φ =
      F.map ψ ≫ eqToHom (congrArg F.obj h₂) := by
  subst hφ
  cases h₁
  cases h₂
  simp

/-- **The naturality square of the comparison of the two legs**, with the transports identifying
the endpoints carried along: after cancelling the two comparison isomorphisms of the points of
`U'` the square is the compatibility square of a morphism of `U' = U ×_𝒳 𝒳'`. Stated in an
abstract category: see the implementation notes. -/
theorem naturality_with_transport {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {LX LY A₁ A₂ A₃ Bb₁ Bb₂ Bb₃ : 𝒞} (hLX : LX = A₂) (hLY : LY = A₃)
    (p₁ : A₁ ≅ Bb₁) (p₂ : A₂ ≅ Bb₂) (p₃ : A₃ ≅ Bb₃) (e : Bb₁ ≅ Bb₂)
    (ka : A₁ ⟶ A₃) (kb : Bb₁ ⟶ Bb₃) (hw : ka ≫ p₃.hom = p₁.hom ≫ kb) :
    (eqToHom hLX ≫ (p₁ ≪≫ e ≪≫ p₂.symm).inv ≫ ka ≫ eqToHom hLY.symm) ≫
        (eqToHom hLY ≫ p₃.hom) =
      (eqToHom hLX ≫ p₂.hom) ≫ e.inv ≫ kb := by
  subst hLX
  subst hLY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Iso.trans_inv, Iso.symm_inv,
    Category.assoc]
  rw [hw]
  simp

/-- The image of a transport is the transport between the images. Stated for an abstract functor:
see the implementation notes. -/
theorem map_eqToHom_eq_eqToHom {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞} (h : X = Y) (E : F.obj X = F.obj Y) :
    F.map (eqToHom h) = eqToHom E := by
  cases h
  simp

/-- The image of a four-factor composite bracketed on the left, with the images of the first three
factors identified. Stated for an abstract functor: see the implementation notes. -/
theorem map_comp_eq_three {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    (F : 𝒞 ⥤ 𝒟) {X Y Z T V : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (i : T ⟶ V)
    {f' : F.obj X ⟶ F.obj Y} {g' : F.obj Y ⟶ F.obj Z} {h' : F.obj Z ⟶ F.obj T}
    (hf : F.map f = f') (hg : F.map g = g') (hh : F.map h = h') :
    F.map ((f ≫ g ≫ h) ≫ i) = f' ≫ g' ≫ h' ≫ F.map i := by
  subst hf
  subst hg
  subst hh
  rw [F.map_comp, F.map_comp, F.map_comp]
  simp

/-! ### The arrow part of the presenting 1-morphism on the pointwise groupoid fibration -/

section Atlas

variable (P : GroupoidPresentation B S hS 𝒳.val)
variable {W W₂ : BigFppfOver B S hS}

/-- An object of the object-space fibration of a presentation is the pair of the test object it
lies over and the section it names. -/
theorem obj_eq_of_sectionOfObj (v : (objectStack P).val.obj)
    (h : (objectStack P).val.p.obj v = W) :
    (⟨W, Discrete.mk (PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P) v h)⟩ :
        (objectStack P).val.obj) = v := by
  obtain rfl := h
  rfl

/-- **Two morphisms of the object-space fibration over one morphism of the site with the same
endpoints are equal**: the object-space fibration is fibred in setoids, so its fibres are thin. -/
theorem objectStack_hom_unique {v v' : (objectStack P).val.obj} (k : W ⟶ W₂)
    (φ φ' : v ⟶ v') (hφ : (objectStack P).val.p.IsHomLift k φ)
    (hφ' : (objectStack P).val.p.IsHomLift k φ') : φ = φ' :=
  have : (objectStack P).val.p.IsFibered :=
    (isFiberedInSetoids_objectStack P).isFiberedInGroupoids.isFibered
  CategoryTheory.Functor.hom_unique_of_fiber_isThin (objectStack P).val.p k
    ((isFiberedInSetoids_objectStack P).fiber_isThin W) φ φ' hφ hφ'

/-- A morphism of the object-space fibration over a morphism of the site is the conjugate by the
transports of any other such morphism between the identified endpoints. -/
theorem objectStack_hom_eq_conj {v v' u u' : (objectStack P).val.obj} (k : W ⟶ W₂)
    (e₁ : v = u) (e₂ : v' = u') (φ : v ⟶ v') (ψ : u ⟶ u')
    (hφ : (objectStack P).val.p.IsHomLift k φ)
    (hψ : (objectStack P).val.p.IsHomLift k ψ) :
    φ = eqToHom e₁ ≫ ψ ≫ eqToHom e₂.symm := by
  subst e₁
  subst e₂
  simpa using objectStack_hom_unique P k φ ψ hφ hψ

/-- The atlas on arrows, read through the pointwise groupoid fibration. -/
theorem basedFunctor_map_pointwiseObjectInclusion {v v' : (objectStack P).val.obj} (φ : v ⟶ v') :
    (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor).map
        ((pointwiseObjectInclusion P.groupoid).map φ) =
      (atlasMap P).hom.toFunctor.map φ := rfl

/-- **Two objects of one fibre of the self-intersection of the atlas naming the same section of
the arrow space, with the same two components, have the same comparison isomorphism.** The fibre
isomorphism between them has vertical components, which are therefore the transports. -/
theorem relation_iso_hom_eq_of_sectionOfObj_eq
    {ρ ρ' : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj}
    (hρ : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p.obj ρ = W)
    (hρ' : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p.obj ρ' = W)
    (hs : PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P) ρ hρ =
      PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P) ρ' hρ')
    (hx : ρ.x = ρ'.x) (hy : ρ.y = ρ'.y) :
    ρ.iso.hom = eqToHom (congrArg (atlasMap P).hom.toFunctor.obj hx) ≫ ρ'.iso.hom ≫
      eqToHom (congrArg (atlasMap P).hom.toFunctor.obj hy).symm := by
  have i := PresheafOfCategories.fiberIsoOfSectionOfObj_eq (atlasRelationEquivalence P) hρ hρ' hs
  have hlift : (SelfIntersection.relation B S hS (objectStack P) 𝒳
      (atlasMap P).hom).val.p.IsHomLift (𝟙 W) (Functor.Fiber.fiberInclusion.map i.hom) := i.hom.2
  have key : ∀ {v v' : (objectStack P).val.obj} (φ : v ⟶ v') (h : v = v'),
      (objectStack P).val.p.obj v' = W → (objectStack P).val.p.IsHomLift (𝟙 W) φ →
        φ = eqToHom h := fun φ h hW hφ =>
    objectStack_hom_unique P (𝟙 W) _ _ hφ
      (by rw [← hW]; exact Functor.isHomLift_id_eqToHom (objectStack P).val.p h)
  have hax := key _ hx (ρ'.hx.trans hρ') (TwoFibreProductOver.isHomLift_a _ (𝟙 W) hlift)
  have hby := key _ hy (ρ'.hy.trans hρ') (TwoFibreProductOver.isHomLift_b _ (𝟙 W) hlift)
  have hw : (atlasMap P).hom.toFunctor.map (eqToHom hx : ρ.x ⟶ ρ'.x) ≫ ρ'.iso.hom =
      ρ.iso.hom ≫ (atlasMap P).hom.toFunctor.map (eqToHom hy : ρ.y ⟶ ρ'.y) := by
    rw [← hax, ← hby]
    exact (Functor.Fiber.fiberInclusion.map i.hom).w
  rw [CategoryTheory.eqToHom_map (atlasMap P).hom.toFunctor hx,
    CategoryTheory.eqToHom_map (atlasMap P).hom.toFunctor hy] at hw
  exact eq_conj_eqToHom_of_comp_eq _ _ _ _ hw

/-- **The arrow part of the presenting 1-morphism at an arrow of the pointwise groupoid fibration
lying over the identity of the site**: the inverse of the comparison isomorphism of Stacks 04M9 at
the point of the arrow space it names. -/
theorem basedFunctor_map_pointwiseToQuotientStack_of_base_id
    (r : P.groupoid.arrows.obj.obj (op W))
    (n : (⟨W, P.groupoid.source.hom.app (op W) r⟩ :
          (presheafOfGroupoids
            (evaluationGroupoidFunctor P.groupoid.toGroupoidInFunctors)).obj) ⟶
        ⟨W, P.groupoid.target.hom.app (op W) r⟩)
    (hb : n.base = 𝟙 W)
    (ha : (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op W) _ _ n.fiber).1 = r) :
    P.basedFunctor.toFunctor.map ((pointwiseToQuotientStack P.groupoid).map n) =
      (atlasRelationTriple P r).iso.inv := by
  obtain ⟨gg, hgb, hga, hgh⟩ := quotientStackTwoArrow_app P.groupoid ⟨W, Discrete.mk r⟩
  have hn : n = gg :=
    pointwiseHom_ext P.groupoid.toGroupoidInFunctors (hb.trans hgb.symm) (ha.trans hga.symm)
  rw [hn]
  exact (congrArg P.basedFunctor.toFunctor.map (eq_of_heq hgh)).symm

/-- The canonical restriction morphism of the object-space fibration, read in the pointwise
groupoid fibration, has an identity arrow of the groupoid. -/
theorem evaluationArrow_pointwiseObjectInclusion_splitRestrict
    (bb : P.groupoid.objects.obj.obj (op W₂)) (k : W ⟶ W₂) :
    (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op W) _ _
        ((pointwiseObjectInclusion P.groupoid).map
          (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)).fiber).1 =
      P.groupoid.toGroupoidInFunctors.identity (op W)
        (P.groupoid.objects.obj.map k.op bb) := by
  obtain ⟨h, he⟩ : ∃ h, ((pointwiseObjectInclusion P.groupoid).map
      (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)).fiber = eqToHom h :=
    ⟨Discrete.eq_of_hom
      (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb).fiber, rfl⟩
  rw [he]
  exact evaluationArrow_eqToHom_identity P.groupoid.toGroupoidInFunctors (op W) h

variable (a : P.groupoid.objects.obj.obj (op W)) (bb : P.groupoid.objects.obj.obj (op W₂))
  (k : W ⟶ W₂) (r : P.groupoid.arrows.obj.obj (op W))

section Factorisation

variable
  (n : (⟨W, a⟩ : (presheafOfGroupoids
    (evaluationGroupoidFunctor P.groupoid.toGroupoidInFunctors)).obj) ⟶ ⟨W₂, bb⟩)
  (ea : (⟨W, a⟩ : (presheafOfGroupoids
      (evaluationGroupoidFunctor P.groupoid.toGroupoidInFunctors)).obj) =
    ⟨W, P.groupoid.source.hom.app (op W) r⟩)
  (ety : (⟨W, P.groupoid.objects.obj.map k.op bb⟩ : (presheafOfGroupoids
      (evaluationGroupoidFunctor P.groupoid.toGroupoidInFunctors)).obj) =
    ⟨W, P.groupoid.target.hom.app (op W) r⟩)

/-- The base component of the factorisation of an arrow of the pointwise groupoid fibration: the
transports and the arrow named by a point of the arrow space are all over the identity. -/
theorem pointwiseFactorisation_base (hk : n.base = k) :
    n.base =
      ((eqToHom ea ≫ directArrowAt P.groupoid ⟨W, Discrete.mk r⟩ ≫ eqToHom ety.symm) ≫
        (pointwiseObjectInclusion P.groupoid).map
          (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)).base := by
  refine hk.trans (Eq.symm ?_)
  have hd : (directArrowAt P.groupoid
      (⟨W, Discrete.mk r⟩ :
        (fibredCategory B S hS P.groupoid.arrows.obj).val.obj)).base = 𝟙 W := rfl
  have hi : ((pointwiseObjectInclusion P.groupoid).map
      (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)).base = k := rfl
  have hea : (eqToHom ea).base = 𝟙 W :=
    (pointwiseEqToHom_base P.groupoid.toGroupoidInFunctors ea).trans (eqToHom_refl W _)
  have hety : (eqToHom ety.symm).base = 𝟙 W :=
    (pointwiseEqToHom_base P.groupoid.toGroupoidInFunctors ety.symm).trans (eqToHom_refl W _)
  show ((eqToHom ea).base ≫ (directArrowAt P.groupoid
      (⟨W, Discrete.mk r⟩ :
        (fibredCategory B S hS P.groupoid.arrows.obj).val.obj)).base ≫
      (eqToHom ety.symm).base) ≫ ((pointwiseObjectInclusion P.groupoid).map
        (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)).base = k
  rw [hea, hety, hd, hi]
  exact Category.id_comp k

/-- The arrow component of the factorisation of an arrow of the pointwise groupoid fibration: the
canonical restriction contributes an identity and the transports leave the point of the arrow
space alone. -/
theorem pointwiseFactorisation_arrow
    (ha : (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op W) _ _ n.fiber).1 = r) :
    (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op W) _ _ n.fiber).1 =
      (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op W) _ _
        ((eqToHom ea ≫ directArrowAt P.groupoid ⟨W, Discrete.mk r⟩ ≫ eqToHom ety.symm) ≫
          (pointwiseObjectInclusion P.groupoid).map
            (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)).fiber).1 := by
  have h1 := pointwiseComp_arrow_of_right_identity P.groupoid.toGroupoidInFunctors
    (eqToHom ea ≫ directArrowAt P.groupoid ⟨W, Discrete.mk r⟩ ≫ eqToHom ety.symm)
    ((pointwiseObjectInclusion P.groupoid).map
      (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb))
    (evaluationArrow_pointwiseObjectInclusion_splitRestrict P bb k)
  have h2 := pointwiseConj_arrow P.groupoid.toGroupoidInFunctors ea ety
    (directArrowAt P.groupoid ⟨W, Discrete.mk r⟩)
  have h3 := directArrowAt_arrow P.groupoid ⟨W, Discrete.mk r⟩
  have he : (eqToHom (congrArg Pseudofunctor.CoGrothendieck.base ea) : W ⟶ W) = 𝟙 W :=
    eqToHom_refl W _
  have h4 : P.groupoid.toGroupoidInFunctors.arrows.map
      (eqToHom (congrArg Pseudofunctor.CoGrothendieck.base ea)).op r = r := by
    rw [he, op_id]
    exact P.groupoid.toGroupoidInFunctors.arrows.map_id_apply (op W) r
  exact ha.trans (h1.trans (h2.trans ((congrArg
    (fun z => P.groupoid.toGroupoidInFunctors.arrows.map
      (eqToHom (congrArg Pseudofunctor.CoGrothendieck.base ea)).op z) h3).trans h4))).symm

/-- **The factorisation of an arrow of the pointwise groupoid fibration**: the arrow named by the
point `r` of the arrow space it names, which lies over the identity of the site, followed by the
canonical restriction along the morphism of the site. -/
theorem pointwiseFactorisation (hk : n.base = k)
    (ha : (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op W) _ _ n.fiber).1 = r) :
    n = (eqToHom ea ≫ directArrowAt P.groupoid ⟨W, Discrete.mk r⟩ ≫ eqToHom ety.symm) ≫
      (pointwiseObjectInclusion P.groupoid).map
        (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb) :=
  pointwiseHom_ext P.groupoid.toGroupoidInFunctors
    (pointwiseFactorisation_base P a bb k r n ea ety hk)
    (pointwiseFactorisation_arrow P a bb k r n ea ety ha)

include ea ety in
/-- The image of the factorisation under the presenting 1-morphism, read on the pointwise
groupoid fibration. The two transports are hypotheses rather than terms, so that a caller may
supply whichever proofs its own goal carries. -/
theorem basedFunctor_map_factorisation
    (E1 : (atlasMap P).hom.toFunctor.obj (⟨W, Discrete.mk a⟩ : (objectStack P).val.obj) =
      (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.source.hom.app (op W) r)⟩)
    (E2 : (atlasMap P).hom.toFunctor.obj
        (⟨W, Discrete.mk (P.groupoid.target.hom.app (op W) r)⟩ : (objectStack P).val.obj) =
      (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.objects.obj.map k.op bb)⟩) :
    (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor).map
        ((eqToHom ea ≫ directArrowAt P.groupoid ⟨W, Discrete.mk r⟩ ≫ eqToHom ety.symm) ≫
          (pointwiseObjectInclusion P.groupoid).map
            (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)) =
      eqToHom E1 ≫ (atlasRelationTriple P r).iso.inv ≫ eqToHom E2 ≫
        (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor).map
          ((pointwiseObjectInclusion P.groupoid).map
            (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)) :=
  map_comp_eq_three (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor)
    (eqToHom ea) (directArrowAt P.groupoid ⟨W, Discrete.mk r⟩) (eqToHom ety.symm)
    ((pointwiseObjectInclusion P.groupoid).map
      (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb))
    (map_eqToHom_eq_eqToHom
      (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor) ea E1)
    (basedFunctor_map_pointwiseToQuotientStack_of_base_id P r
      (directArrowAt P.groupoid ⟨W, Discrete.mk r⟩) rfl
      (directArrowAt_arrow P.groupoid ⟨W, Discrete.mk r⟩))
    (map_eqToHom_eq_eqToHom
      (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor) ety.symm E2)

include ea ety in
/-- **The arrow part of the presenting 1-morphism on the pointwise groupoid fibration of the
presenting groupoid.** The first factor of the factorisation goes to the inverse of the comparison
isomorphism of Stacks 04M9 at `r` and the second to the canonical restriction of the atlas. -/
theorem basedFunctor_map_pointwiseToQuotientStack (hk : n.base = k)
    (ha : (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op W) _ _ n.fiber).1 = r)
    (E1 : (atlasMap P).hom.toFunctor.obj (⟨W, Discrete.mk a⟩ : (objectStack P).val.obj) =
      (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.source.hom.app (op W) r)⟩)
    (E2 : (atlasMap P).hom.toFunctor.obj
        (⟨W, Discrete.mk (P.groupoid.target.hom.app (op W) r)⟩ : (objectStack P).val.obj) =
      (atlasMap P).hom.toFunctor.obj
        ⟨W, Discrete.mk (P.groupoid.objects.obj.map k.op bb)⟩) :
    (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor).map n =
      eqToHom E1 ≫ (atlasRelationTriple P r).iso.inv ≫ eqToHom E2 ≫
        (pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor).map
          ((pointwiseObjectInclusion P.groupoid).map
            (SelfIntersection.splitRestrict (U := P.groupoid.objects) k bb)) :=
  (congrArg (fun m => (pointwiseToQuotientStack P.groupoid ⋙
        P.basedFunctor.toFunctor).map m)
      (pointwiseFactorisation P a bb k r n ea ety hk ha)).trans
    (basedFunctor_map_factorisation P a bb k r ea ety E1 E2)

end Factorisation

end Atlas

/-! ### The comparison on the pointwise groupoid presentation of `[U'/R']` -/

section BaseChange

variable (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)
variable {W : BigFppfOver B S hS}
variable {U' R' : AlgebraicSpaces B S hS}
variable
  (eU' : StacksRepresentableCFG.EquivalenceOver
    (baseChangedAtlasSquare P g).pt.val.p (presheafOfCategories (U'.obj ⋙ typeToCat)).p)
  (eR' : StacksRepresentableCFG.EquivalenceOver
    (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.p
    (presheafOfCategories (R'.obj ⋙ typeToCat)).p)

/-- **The image under `pr` of a section of `U'` names the projection of the chosen representative
of that section.** This is what makes the two legs of the square comparable. -/
theorem prObjects_app_eq (c : U'.obj.obj (op W)) :
    (⟨W, Discrete.mk ((prObjects P g eU').app (op W) c)⟩ : (objectStack P).val.obj) =
      (baseChangedAtlasSquare P g).fst.hom.toFunctor.obj
        (SelfIntersection.representingObj eU' c) := by
  have h1 : (prObjects P g eU').app (op W) c =
      PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P)
        ((baseChangedAtlasSquare P g).fst.hom.toFunctor.obj
          (SelfIntersection.representingObj eU' c))
        ((Functor.congr_obj (baseChangedAtlasSquare P g).fst.hom.w
            (SelfIntersection.representingObj eU' c)).trans
          (SelfIntersection.representingObj_over eU' c)) :=
    (congrArg (fun y => (prObjects P g eU').app (op W) y)
      (SelfIntersection.sectionOfObj_representingObj eU' c)).symm.trans
      (prObjects_app_sectionOfObj P g eU' (SelfIntersection.representingObj eU' c)
        (SelfIntersection.representingObj_over eU' c))
  exact (congrArg (fun z => (⟨W, Discrete.mk z⟩ : (objectStack P).val.obj)) h1).trans
    (obj_eq_of_sectionOfObj P _ _)

variable (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
variable (h𝒳' : IsAlgebraicStack.{u, w} B S hS 𝒳'.val)

/-- The pointwise groupoid presentation of the quotient stack of the base-changed groupoid. -/
noncomputable abbrev bcPointwise : BasedCategory (BigFppfOver B S hS) :=
  presheafOfGroupoids (evaluationGroupoidFunctor
    (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.toGroupoidInFunctors)

/-- The upper and right legs of the square of Stacks 04Y6, read on the pointwise groupoid
presentation of `[U'/R']`: the 1-morphism of Stacks 04T4 (4) of the base-changed atlas, followed
by `g`. -/
noncomputable def bcPointwiseUpper : bcPointwise P g eU' eR' h𝒳 h𝒳' ⥤ᵇ 𝒳.val :=
  BasedFunctor.comp
    (SelfIntersection.toStackOfPointwiseGroupoid eU' eR'
      (SelfIntersection.isFiberedInSetoids_source eU')) g.hom

/-- The left and lower legs of the square of Stacks 04Y6, read on the pointwise groupoid
presentation of `[U'/R']`: the pointwise map of `pr`, followed by the canonical arrow to `[U/R]`
and by the presenting 1-morphism of `P`. -/
noncomputable def bcPointwiseLower : bcPointwise P g eU' eR' h𝒳 h𝒳' ⥤ᵇ 𝒳.val :=
  BasedFunctor.comp (quotientPointwiseMap (pr P g eU' eR' h𝒳 h𝒳'))
    (BasedFunctor.comp (pointwiseToQuotientStackBased P.groupoid) P.basedFunctor)

/-- The upper leg lands on the image under `g` of the second component of the chosen
representative. -/
theorem bcPointwiseUpper_obj (X : (bcPointwise P g eU' eR' h𝒳 h𝒳').obj) :
    (bcPointwiseUpper P g eU' eR' h𝒳 h𝒳').toFunctor.obj X =
      g.hom.toFunctor.obj ((baseChangedAtlas P g).hom.toFunctor.obj
        (SelfIntersection.representingObj eU' X.fiber)) := rfl

/-- The lower leg lands on the image under the atlas of the first component of the chosen
representative. -/
theorem bcPointwiseLower_obj (X : (bcPointwise P g eU' eR' h𝒳 h𝒳').obj) :
    (bcPointwiseLower P g eU' eR' h𝒳 h𝒳').toFunctor.obj X =
      (atlasMap P).hom.toFunctor.obj
        ((baseChangedAtlasSquare P g).fst.hom.toFunctor.obj
          (SelfIntersection.representingObj eU' X.fiber)) :=
  congrArg (atlasMap P).hom.toFunctor.obj (prObjects_app_eq P g eU' X.fiber)

/-- **The arrow comparing the two legs on the pointwise groupoid presentation of `[U'/R']`**: at a
point of `U'` it is the comparison isomorphism `ψ : a(u) ≅ g(x)` carried by the chosen
representative `(u, x, ψ)` of that point. -/
noncomputable def bcComparisonArrow (X : (bcPointwise P g eU' eR' h𝒳 h𝒳').obj) :
    (bcPointwiseLower P g eU' eR' h𝒳 h𝒳').toFunctor.obj X ⟶
      (bcPointwiseUpper P g eU' eR' h𝒳 h𝒳').toFunctor.obj X :=
  eqToHom (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' X) ≫
    (SelfIntersection.representingObj eU' X.fiber).iso.hom

section Naturality

variable {X Y : (bcPointwise P g eU' eR' h𝒳 h𝒳').obj} (m : X ⟶ Y)

/-- **The arrow part of the upper leg on the pointwise groupoid presentation**: the inverse of the
comparison isomorphism of the arrow of `U' ×_{𝒳'} U'` the arrow names, followed by the image of
the canonical restriction, both carried into `𝒳` by `g`. -/
theorem bcPointwiseUpper_map :
    (bcPointwiseUpper P g eU' eR' h𝒳 h𝒳').toFunctor.map m =
      g.hom.toFunctor.map (SelfIntersection.relationOfFiberHom eU' X.fiber
            (U'.obj.map m.base.op Y.fiber)
            (SelfIntersection.pointwiseFiberHom eU' eR'
              (SelfIntersection.isFiberedInSetoids_source eU') m)).iso.inv ≫
        g.hom.toFunctor.map ((baseChangedAtlas P g).hom.toFunctor.map
          (SelfIntersection.representingObjRestrict eU' m.base Y.fiber)) :=
  (congrArg g.hom.toFunctor.map (SelfIntersection.toStackOfPointwiseGroupoidMap_def eU' eR'
      (SelfIntersection.isFiberedInSetoids_source eU') m)).trans
    (g.hom.toFunctor.map_comp _ _)

/-- The source of the point of `R` named by the image under `pr` of the arrow of `R'` an arrow of
the pointwise groupoid fibration names. -/
theorem prArrows_source_pointwiseSection :
    P.groupoid.source.hom.app (op X.base) ((prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m)) =
      (prObjects P g eU').app (op X.base) X.fiber :=
  (prArrows_source P g eU' eR' _).trans
    (congrArg ((prObjects P g eU').app (op X.base))
      (SelfIntersection.relationSourceMap_pointwiseSection eU' eR'
        (SelfIntersection.isFiberedInSetoids_source eU') m))

/-- The target of the point of `R` named by the image under `pr` of the arrow of `R'` an arrow of
the pointwise groupoid fibration names. -/
theorem prArrows_target_pointwiseSection :
    P.groupoid.target.hom.app (op X.base) ((prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m)) =
      (prObjects P g eU').app (op X.base) (U'.obj.map m.base.op Y.fiber) :=
  (prArrows_target P g eU' eR' _).trans
    (congrArg ((prObjects P g eU').app (op X.base))
      (SelfIntersection.relationTargetMap_pointwiseSection eU' eR'
        (SelfIntersection.isFiberedInSetoids_source eU') m))

/-- The image under `pr` of a restricted section of `U'` is the restriction of its image. -/
theorem prObjects_app_map :
    P.groupoid.objects.obj.map m.base.op ((prObjects P g eU').app (op Y.base) Y.fiber) =
      (prObjects P g eU').app (op X.base) (U'.obj.map m.base.op Y.fiber) :=
  (NatTrans.naturality_apply (prObjects P g eU') m.base.op Y.fiber).symm

/-- The point of `R` named by the image under `pr` of the arrow of `R'` an arrow of the pointwise
groupoid fibration names, read through the arrow part of the pointwise map of `pr`. -/
theorem quotientPointwiseMap_pr_arrow :
    (P.groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op X.base) _ _
        ((quotientPointwiseMap (pr P g eU' eR' h𝒳 h𝒳')).toFunctor.map m).fiber).1 =
      (prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m) :=
  quotientPointwiseMap_arrow (pr P g eU' eR' h𝒳 h𝒳') m

/-- The arrow of `U' ×_{𝒳'} U'` that an arrow of the pointwise groupoid presentation names: the
triple of the chosen representatives of its two endpoints and of the comparison isomorphism of
`𝒳'` between their images. -/
noncomputable abbrev bcRelationArrow : (SelfIntersection.relation B S hS
    (baseChangedAtlasSquare P g).pt 𝒳' (baseChangedAtlas P g).hom).val.obj :=
  SelfIntersection.relationOfFiberHom eU' X.fiber (U'.obj.map m.base.op Y.fiber)
    (SelfIntersection.pointwiseFiberHom eU' eR'
      (SelfIntersection.isFiberedInSetoids_source eU') m)

/-- The image under `pr` of the arrow of `U' ×_{𝒳'} U'` names the point of `R` the image arrow
names. -/
theorem sectionOfObj_bcRelationFunctor :
    PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P)
        ((bcRelationFunctor P g).obj (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m)) rfl =
      (prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m) :=
  (prArrows_app_sectionOfObj P g eR' (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m) rfl).symm.trans
    (congrArg ((prArrows P g eR').app (op X.base))
      (SelfIntersection.arrowOfFiberHom_pointwiseFiberHom eU' eR'
        (SelfIntersection.isFiberedInSetoids_source eU') m))

/-- The target of the image arrow is the target of the explicit triple of the point of `R` it
names. -/
theorem bcRelationFunctor_obj_x_eq :
    ((bcRelationFunctor P g).obj (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m)).x =
      (atlasRelationTriple P ((prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m))).x :=
  (prObjects_app_eq P g eU' (U'.obj.map m.base.op Y.fiber)).symm.trans
    (congrArg (fun z => (⟨X.base, Discrete.mk z⟩ : (objectStack P).val.obj))
      (prArrows_target_pointwiseSection P g eU' eR' h𝒳 h𝒳' m).symm)

/-- The source of the image arrow is the source of the explicit triple of the point of `R` it
names. -/
theorem bcRelationFunctor_obj_y_eq :
    ((bcRelationFunctor P g).obj (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m)).y =
      (atlasRelationTriple P ((prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m))).y :=
  (prObjects_app_eq P g eU' X.fiber).symm.trans
    (congrArg (fun z => (⟨X.base, Discrete.mk z⟩ : (objectStack P).val.obj))
      (prArrows_source_pointwiseSection P g eU' eR' h𝒳 h𝒳' m).symm)

/-- **The inverse of the comparison isomorphism of the image arrow is the inverse of the
comparison isomorphism of Stacks 04M9 at the point of `R` it names**, conjugated by the
transports identifying the two pairs of endpoints. -/
theorem bcRelationFunctor_obj_iso_inv :
    eqToHom (congrArg (atlasMap P).hom.toFunctor.obj
          (bcRelationFunctor_obj_y_eq P g eU' eR' h𝒳 h𝒳' m)) ≫
        (atlasRelationTriple P ((prArrows P g eR').app (op X.base)
          (SelfIntersection.pointwiseSection eU' eR'
            (SelfIntersection.isFiberedInSetoids_source eU') m))).iso.inv ≫
        eqToHom (congrArg (atlasMap P).hom.toFunctor.obj
          (bcRelationFunctor_obj_x_eq P g eU' eR' h𝒳 h𝒳' m)).symm =
      ((bcRelationFunctor P g).obj (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m)).iso.inv :=
  iso_inv_conj
    (congrArg (atlasMap P).hom.toFunctor.obj
      (bcRelationFunctor_obj_x_eq P g eU' eR' h𝒳 h𝒳' m))
    (congrArg (atlasMap P).hom.toFunctor.obj
      (bcRelationFunctor_obj_y_eq P g eU' eR' h𝒳 h𝒳' m))
    ((bcRelationFunctor P g).obj (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m)).iso
    (atlasRelationTriple P ((prArrows P g eR').app (op X.base)
      (SelfIntersection.pointwiseSection eU' eR'
        (SelfIntersection.isFiberedInSetoids_source eU') m))).iso
    (relation_iso_hom_eq_of_sectionOfObj_eq P (W := X.base) rfl rfl
      ((sectionOfObj_bcRelationFunctor P g eU' eR' h𝒳 h𝒳' m).trans
        (sectionOfObj_atlasRelationTriple P ((prArrows P g eR').app (op X.base)
          (SelfIntersection.pointwiseSection eU' eR'
            (SelfIntersection.isFiberedInSetoids_source eU') m))).symm)
      (bcRelationFunctor_obj_x_eq P g eU' eR' h𝒳 h𝒳' m)
      (bcRelationFunctor_obj_y_eq P g eU' eR' h𝒳 h𝒳' m))

/-- The source of the canonical restriction of the object space is the first component of the
chosen representative of the restricted section. -/
theorem splitRestrict_source_eq :
    (⟨X.base, Discrete.mk (P.groupoid.objects.obj.map m.base.op
        ((prObjects P g eU').app (op Y.base) Y.fiber))⟩ : (objectStack P).val.obj) =
      ((bcRelationFunctor P g).obj (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m)).x :=
  (congrArg (fun z => (⟨X.base, Discrete.mk z⟩ : (objectStack P).val.obj))
      (prObjects_app_map P g eU' eR' h𝒳 h𝒳' m)).trans
    (prObjects_app_eq P g eU' (U'.obj.map m.base.op Y.fiber))

/-- **The canonical restriction of the object space is the first component of the canonical
restriction of the chosen representatives**, conjugated by the transports: the object-space
fibration is fibred in setoids, so a morphism of it over one morphism of the site is unique. -/
theorem splitRestrict_eq_fst_map :
    SelfIntersection.splitRestrict (U := P.groupoid.objects) m.base
        ((prObjects P g eU').app (op Y.base) Y.fiber) =
      eqToHom (splitRestrict_source_eq P g eU' eR' h𝒳 h𝒳' m) ≫
        (baseChangedAtlasSquare P g).fst.hom.toFunctor.map
          (SelfIntersection.representingObjRestrict eU' m.base Y.fiber) ≫
        eqToHom (prObjects_app_eq P g eU' Y.fiber).symm :=
  objectStack_hom_eq_conj P m.base
    (splitRestrict_source_eq P g eU' eR' h𝒳 h𝒳' m) (prObjects_app_eq P g eU' Y.fiber)
    (SelfIntersection.splitRestrict (U := P.groupoid.objects) m.base
      ((prObjects P g eU').app (op Y.base) Y.fiber))
    ((baseChangedAtlasSquare P g).fst.hom.toFunctor.map
      (SelfIntersection.representingObjRestrict eU' m.base Y.fiber))
    (SelfIntersection.isHomLift_splitRestrict (U := P.groupoid.objects) m.base _)
    (CategoryTheory.Functor.isHomLift_map_of_comp_eq_general
      (baseChangedAtlasSquare P g).fst.hom.w m.base _
      (SelfIntersection.isHomLift_representingObjRestrict eU' m.base Y.fiber))

/-- **The arrow part of the lower leg on the pointwise groupoid presentation**: the inverse of the
comparison isomorphism of the image under `pr` of the arrow of `U' ×_{𝒳'} U'`, followed by the
image under the atlas of the first component of the canonical restriction. -/
theorem bcPointwiseLower_map :
    (bcPointwiseLower P g eU' eR' h𝒳 h𝒳').toFunctor.map m =
      eqToHom (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' X) ≫
        ((bcRelationFunctor P g).obj (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m)).iso.inv ≫
        (atlasMap P).hom.toFunctor.map
          ((baseChangedAtlasSquare P g).fst.hom.toFunctor.map
            (SelfIntersection.representingObjRestrict eU' m.base Y.fiber)) ≫
        eqToHom (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' Y).symm :=
  (basedFunctor_map_pointwiseToQuotientStack P
      ((prObjects P g eU').app (op X.base) X.fiber)
      ((prObjects P g eU').app (op Y.base) Y.fiber) m.base
      ((prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m))
      ((quotientPointwiseMap (pr P g eU' eR' h𝒳 h𝒳')).toFunctor.map m)
      (congrArg (fun z => (⟨X.base, z⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor P.groupoid.toGroupoidInFunctors)).obj))
        (prArrows_source_pointwiseSection P g eU' eR' h𝒳 h𝒳' m).symm)
      (congrArg (fun z => (⟨X.base, z⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor P.groupoid.toGroupoidInFunctors)).obj))
        ((prObjects_app_map P g eU' eR' h𝒳 h𝒳' m).trans
          (prArrows_target_pointwiseSection P g eU' eR' h𝒳 h𝒳' m).symm))
      rfl (quotientPointwiseMap_pr_arrow P g eU' eR' h𝒳 h𝒳' m)
      ((bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' X).trans
        (congrArg (atlasMap P).hom.toFunctor.obj
          (bcRelationFunctor_obj_y_eq P g eU' eR' h𝒳 h𝒳' m)))
      ((congrArg (atlasMap P).hom.toFunctor.obj
          (bcRelationFunctor_obj_x_eq P g eU' eR' h𝒳 h𝒳' m)).symm.trans
        (congrArg (atlasMap P).hom.toFunctor.obj
          (splitRestrict_source_eq P g eU' eR' h𝒳 h𝒳' m).symm))).trans
    (eqToHom_conj_regroup (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' X)
      (congrArg (atlasMap P).hom.toFunctor.obj
        (bcRelationFunctor_obj_y_eq P g eU' eR' h𝒳 h𝒳' m))
      (congrArg (atlasMap P).hom.toFunctor.obj
        (bcRelationFunctor_obj_x_eq P g eU' eR' h𝒳 h𝒳' m))
      (congrArg (atlasMap P).hom.toFunctor.obj
        (splitRestrict_source_eq P g eU' eR' h𝒳 h𝒳' m).symm)
      (atlasRelationTriple P ((prArrows P g eR').app (op X.base)
        (SelfIntersection.pointwiseSection eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') m))).iso.inv
      ((pointwiseToQuotientStack P.groupoid ⋙ P.basedFunctor.toFunctor).map
        ((pointwiseObjectInclusion P.groupoid).map
          (SelfIntersection.splitRestrict (U := P.groupoid.objects) m.base
            ((prObjects P g eU').app (op Y.base) Y.fiber))))
      (bcRelationFunctor_obj_iso_inv P g eU' eR' h𝒳 h𝒳' m)
      (map_conj_eqToHom (atlasMap P).hom.toFunctor
        (splitRestrict_source_eq P g eU' eR' h𝒳 h𝒳' m)
        (prObjects_app_eq P g eU' Y.fiber).symm
        ((baseChangedAtlasSquare P g).fst.hom.toFunctor.map
          (SelfIntersection.representingObjRestrict eU' m.base Y.fiber))
        (splitRestrict_eq_fst_map P g eU' eR' h𝒳 h𝒳' m)))

/-- **The comparison arrows are natural.** After cancelling the two comparison isomorphisms of the
points of `U'`, the naturality square is the compatibility square of the canonical restriction of
the chosen representatives, a morphism of `U' = U ×_𝒳 𝒳'`. -/
theorem bcComparisonArrow_naturality :
    (bcPointwiseLower P g eU' eR' h𝒳 h𝒳').toFunctor.map m ≫
        bcComparisonArrow P g eU' eR' h𝒳 h𝒳' Y =
      bcComparisonArrow P g eU' eR' h𝒳 h𝒳' X ≫
        (bcPointwiseUpper P g eU' eR' h𝒳 h𝒳').toFunctor.map m :=
  (congrArg (fun z => z ≫ bcComparisonArrow P g eU' eR' h𝒳 h𝒳' Y)
      (bcPointwiseLower_map P g eU' eR' h𝒳 h𝒳' m)).trans
    ((naturality_with_transport (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' X)
        (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' Y)
        (SelfIntersection.representingObj eU' (U'.obj.map m.base.op Y.fiber)).iso
        (SelfIntersection.representingObj eU' X.fiber).iso
        (SelfIntersection.representingObj eU' Y.fiber).iso
        (g.hom.toFunctor.mapIso (bcRelationArrow P g eU' eR' h𝒳 h𝒳' m).iso)
        ((atlasMap P).hom.toFunctor.map
          ((baseChangedAtlasSquare P g).fst.hom.toFunctor.map
            (SelfIntersection.representingObjRestrict eU' m.base Y.fiber)))
        (g.hom.toFunctor.map ((baseChangedAtlas P g).hom.toFunctor.map
          (SelfIntersection.representingObjRestrict eU' m.base Y.fiber)))
        (SelfIntersection.representingObjRestrict eU' m.base Y.fiber).w).trans
      (congrArg (fun z => bcComparisonArrow P g eU' eR' h𝒳 h𝒳' X ≫ z)
        (bcPointwiseUpper_map P g eU' eR' h𝒳 h𝒳' m).symm))

end Naturality

/-- The comparison arrow at a point of `U'`, as an isomorphism. -/
noncomputable def bcComparisonIso (X : (bcPointwise P g eU' eR' h𝒳 h𝒳').obj) :
    (bcPointwiseLower P g eU' eR' h𝒳 h𝒳').toFunctor.obj X ≅
      (bcPointwiseUpper P g eU' eR' h𝒳 h𝒳').toFunctor.obj X :=
  eqToIso (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' X) ≪≫
    (SelfIntersection.representingObj eU' X.fiber).iso

/-- Each comparison arrow is vertical over the big fppf site: the comparison isomorphism of a
point of `U' = U ×_𝒳 𝒳'` is. -/
theorem isHomLift_bcComparisonArrow (X : (bcPointwise P g eU' eR' h𝒳 h𝒳').obj) :
    𝒳.val.p.IsHomLift (𝟙 ((bcPointwise P g eU' eR' h𝒳 h𝒳').p.obj X))
      (bcComparisonArrow P g eU' eR' h𝒳 h𝒳' X) := by
  have he : (SelfIntersection.representingObj eU' X.fiber).base = X.base :=
    SelfIntersection.representingObj_over eU' X.fiber
  have hz := (SelfIntersection.representingObj eU' X.fiber).vertical
  rw [he] at hz
  have hb : 𝒳.val.p.obj ((atlasMap P).hom.toFunctor.obj
      ((baseChangedAtlasSquare P g).fst.hom.toFunctor.obj
        (SelfIntersection.representingObj eU' X.fiber))) = X.base :=
    ((atlasMap P).hom.w_obj _).trans
      (((baseChangedAtlasSquare P g).fst.hom.w_obj _).trans
        (SelfIntersection.representingObj_over eU' X.fiber))
  have h0 := CategoryTheory.Functor.isHomLift_id_eqToHom 𝒳.val.p
    (bcPointwiseLower_obj P g eU' eR' h𝒳 h𝒳' X)
  rw [hb] at h0
  exact CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ (𝟙 X.base) h0 hz

/-- **The two legs of the square of Stacks 04Y6 agree on the pointwise groupoid presentation of
`[U'/R']`**, through the comparison isomorphism carried by the chosen representative of a point of
`U'`. -/
noncomputable def bcPointwiseIso :
    (bcPointwiseLower P g eU' eR' h𝒳 h𝒳').toFunctor ≅
      (bcPointwiseUpper P g eU' eR' h𝒳 h𝒳').toFunctor :=
  NatIso.ofComponents (fun X => bcComparisonIso P g eU' eR' h𝒳 h𝒳' X)
    (fun m => bcComparisonArrow_naturality P g eU' eR' h𝒳 h𝒳' m)

/-- `AlgebraicGeometry.Stack.GroupoidPresentation.bcPointwiseIso` as a 2-isomorphism over the big
fppf site. -/
noncomputable def bcPointwiseBasedIso :
    bcPointwiseLower P g eU' eR' h𝒳 h𝒳' ≅ bcPointwiseUpper P g eU' eR' h𝒳 h𝒳' :=
  BasedNatIso.mkNatIso (bcPointwiseIso P g eU' eR' h𝒳 h𝒳')
    (fun X => isHomLift_bcComparisonArrow P g eU' eR' h𝒳 h𝒳' X)

/-! ### The 2-isomorphism filling the square -/

section Square

/-- The universe lift of a category fibred in groupoids, as a 1-morphism over the big fppf site:
the target of Stacks 0436 at the universes the stackification works at. -/
noncomputable abbrev stackUliftUp
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    𝒴.val ⥤ᵇ SelfIntersection.stackUlift 𝒴 :=
  ⟨BasedCategory.uliftUp 𝒴.val, BasedCategory.uliftUp_comp 𝒴.val⟩

/-- The comparison bringing the universe lift of a category fibred in groupoids back down to it,
as a 1-morphism over the big fppf site. -/
noncomputable abbrev stackUliftDown
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    SelfIntersection.stackUlift 𝒴 ⥤ᵇ 𝒴.val :=
  ⟨BasedCategory.uliftDown 𝒴.val, BasedCategory.uliftDown_comp 𝒴.val⟩

/-- **The upper and right legs of the square of Stacks 04Y6**, with the presenting 1-morphism of
the base-changed presentation written as the canonical morphism of Stacks 04T4 (5), which it is. -/
noncomputable def bcSquareUpperCan :
    quotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid ⥤ᵇ 𝒳.val :=
  BasedFunctor.comp (SelfIntersection.canonicalMapToStack eU' eR'
    (SelfIntersection.isFiberedInSetoids_source eU') h𝒳') g.hom

/-- **The left and lower legs of the square of Stacks 04Y6.** -/
noncomputable def bcSquareLower :
    quotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid ⥤ᵇ 𝒳.val :=
  BasedFunctor.comp (quotientStackPr P g eU' eR' h𝒳 h𝒳') P.basedFunctor

/-- **The upper and right legs, restricted to the pointwise groupoid presentation of `[U'/R']`**:
the unit of Stacks 0436 identifies the restriction of the canonical morphism of Stacks 04T4 (5)
with the 1-morphism out of the pointwise groupoid fibration it extends. -/
noncomputable def bcRestrictedUpperIso :
    BasedFunctor.comp
        (toQuotientStackBased (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (bcSquareUpperCan P g eU' eR' h𝒳 h𝒳') ≅
      BasedFunctor.comp
        (quotientPrestackDown (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (bcPointwiseUpper P g eU' eR' h𝒳 h𝒳') :=
  have hdown : (BasedCategory.uliftDown 𝒳'.val ⋙ 𝒳'.val.p :
      (SelfIntersection.stackUlift 𝒳').obj ⥤ BigFppfOver B S hS) =
      (SelfIntersection.stackUlift 𝒳').p := BasedCategory.uliftDown_comp 𝒳'.val
  let unitU : BasedFunctor.comp
        (toQuotientStackBased (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (SelfIntersection.canonicalMapToStack eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') h𝒳') ≅
      BasedFunctor.comp
        (quotientPrestackDown (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (SelfIntersection.toStackOfPointwiseGroupoid eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU')) :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight
        (SelfIntersection.unitCanonicalMapUlift eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') h𝒳')
        (BasedCategory.uliftDown 𝒳'.val))
      (fun A => CategoryTheory.Functor.isHomLift_map_of_comp_eq_general hdown
        (𝟙 ((quotientPrestack
          (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid).p.obj A))
        ((SelfIntersection.unitCanonicalMapUlift eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') h𝒳').hom.app A)
        (SelfIntersection.isHomLift_unitCanonicalMapUlift_app eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU') h𝒳' A))
  BasedCategory.whiskerRightIso unitU g.hom

/-- **The left and lower legs, restricted to the pointwise groupoid presentation of `[U'/R']`**:
the unit of Stacks 046Q identifies the restriction of `[pr]` with the pointwise map of `pr`
followed by the canonical arrow to `[U/R]`. -/
noncomputable def bcRestrictedLowerIso :
    BasedFunctor.comp
        (toQuotientStackBased (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (bcSquareLower P g eU' eR' h𝒳 h𝒳') ≅
      BasedFunctor.comp
        (quotientPrestackDown (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (bcPointwiseLower P g eU' eR' h𝒳 h𝒳') :=
  let unitL : BasedFunctor.comp
        (toQuotientStackBased (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (quotientStackPr P g eU' eR' h𝒳 h𝒳') ≅
      (⟨quotientMapUnderlying (pr P g eU' eR' h𝒳 h𝒳'),
        quotientMapUnderlying_comp (pr P g eU' eR' h𝒳 h𝒳')⟩ :
          quotientPrestack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid ⥤ᵇ
            quotientStack P.groupoid) :=
    BasedNatIso.mkNatIso (quotientMapExtensionUnit (pr P g eU' eR' h𝒳 h𝒳'))
      (quotientMapExtensionUnit_hom_isHomLift (pr P g eU' eR' h𝒳 h𝒳'))
  BasedCategory.whiskerRightIso unitL P.basedFunctor

/-- **The square of Stacks 04Y6 2-commutes after restriction to the pointwise groupoid
presentation of `[U'/R']`**: there the comparison is the comparison isomorphism of the chosen
representative of a point of `U'`. -/
noncomputable def bcRestrictedSquare :
    BasedFunctor.comp
        (toQuotientStackBased (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (bcSquareUpperCan P g eU' eR' h𝒳 h𝒳') ≅
      BasedFunctor.comp
        (toQuotientStackBased (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (bcSquareLower P g eU' eR' h𝒳 h𝒳') :=
  ((bcRestrictedUpperIso P g eU' eR' h𝒳 h𝒳').trans
      (BasedCategory.whiskerLeftIso
        (quotientPrestackDown (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
        (bcPointwiseBasedIso P g eU' eR' h𝒳 h𝒳').symm)).trans
    (bcRestrictedLowerIso P g eU' eR' h𝒳 h𝒳').symm

/-- The upper and right legs, lifted to the universe at which the stackification works, as an
object of the morphism category of Stacks 02ZG. -/
noncomputable def bcUpperFibredMor :
    Functor.FibredMor
      (quotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid).p
      (SelfIntersection.stackUlift 𝒳).p :=
  ⟨(BasedFunctor.comp (bcSquareUpperCan P g eU' eR' h𝒳 h𝒳')
      (stackUliftUp 𝒳)).toFunctor,
    (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibredOneMorphism
      (BasedFunctor.comp (bcSquareUpperCan P g eU' eR' h𝒳 h𝒳') (stackUliftUp 𝒳)).w⟩

/-- The left and lower legs, lifted to the universe at which the stackification works, as an
object of the morphism category of Stacks 02ZG. -/
noncomputable def bcLowerFibredMor :
    Functor.FibredMor
      (quotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid).p
      (SelfIntersection.stackUlift 𝒳).p :=
  ⟨(BasedFunctor.comp (bcSquareLower P g eU' eR' h𝒳 h𝒳')
      (stackUliftUp 𝒳)).toFunctor,
    (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibredOneMorphism
      (BasedFunctor.comp (bcSquareLower P g eU' eR' h𝒳 h𝒳') (stackUliftUp 𝒳)).w⟩

/-- Restriction of 1-morphisms into the universe lift of `𝒳` along the stackification map of the
pointwise groupoid presentation of `[U'/R']`, the functor of Stacks 04W9 through which the filler
of the square is produced. -/
noncomputable abbrev bcRestrictMor :
    Functor.FibredMor
        (quotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid).p
        (SelfIntersection.stackUlift 𝒳).p ⥤
      Functor.FibredMor
        (quotientPrestack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid).p
        (SelfIntersection.stackUlift 𝒳).p :=
  Functor.restrictMor (q := (SelfIntersection.stackUlift 𝒳).p)
    (isFibredOneMorphism_toQuotientStack
      (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)

/-- **Stacks 04W9**: restriction along the stackification map of the pointwise groupoid
presentation of `[U'/R']` is full on 1-morphisms into the universe lift of `𝒳`, which is a stack
by Stacks 026F. -/
theorem full_bcRestrictMor : (bcRestrictMor P g eU' eR' h𝒳 h𝒳').Full :=
  have : (SelfIntersection.stackUlift 𝒳).p.IsFibered :=
    (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibered
  Functor.Stackification.restrict_full
    (isFibredOneMorphism_toQuotientStack
      (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
    (isLocallyBijective_toQuotientStack
      (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
    (SelfIntersection.isStack_stackUlift h𝒳).isMorSheaf
    (essImage_toQuotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)

/-- **Stacks 04W9**: that restriction is faithful. -/
theorem faithful_bcRestrictMor : (bcRestrictMor P g eU' eR' h𝒳 h𝒳').Faithful :=
  have : (SelfIntersection.stackUlift 𝒳).p.IsFibered :=
    (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids).isFibered
  Functor.Stackification.restrict_faithful
    (isFibredOneMorphism_toQuotientStack
      (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
    (SelfIntersection.isStack_stackUlift h𝒳).isMorSheaf
    (essImage_toQuotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)

/-- The restricted square, lifted to the universe at which the stackification works, as an
isomorphism in the morphism category of Stacks 02ZG. -/
noncomputable def bcRestrictedSquareMor :
    (bcRestrictMor P g eU' eR' h𝒳 h𝒳').obj
        (bcUpperFibredMor P g eU' eR' h𝒳 h𝒳') ≅
      (bcRestrictMor P g eU' eR' h𝒳 h𝒳').obj
        (bcLowerFibredMor P g eU' eR' h𝒳 h𝒳') :=
  let α := BasedCategory.whiskerRightIso (bcRestrictedSquare P g eU' eR' h𝒳 h𝒳')
    (stackUliftUp 𝒳)
  Functor.FibredMor.isoMk
    ((BasedNatTrans.forgetful
      (quotientPrestack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
      (SelfIntersection.stackUlift 𝒳)).mapIso α)
    (fun A => α.hom.isHomLift' A)

/-- The filler of the lifted square, as an isomorphism in the morphism category of Stacks 02ZG:
the preimage of the restricted square under the fully faithful restriction functor. -/
noncomputable def bcSquareFibredMorIso :
    bcUpperFibredMor P g eU' eR' h𝒳 h𝒳' ≅
      bcLowerFibredMor P g eU' eR' h𝒳 h𝒳' :=
  haveI := full_bcRestrictMor P g eU' eR' h𝒳 h𝒳'
  haveI := faithful_bcRestrictMor P g eU' eR' h𝒳 h𝒳'
  (bcRestrictMor P g eU' eR' h𝒳 h𝒳').preimageIso
    (bcRestrictedSquareMor P g eU' eR' h𝒳 h𝒳')

/-- **Stacks 04Y6, assertion (4), with the presenting 1-morphism written as the canonical morphism
of Stacks 04T4 (5).** The square 2-commutes: the two legs into the universe lift of `𝒳` are
2-isomorphic by Stacks 04W9, and the universe lift is undone by its own comparison. -/
noncomputable def bcSquareIsoCan :
    bcSquareUpperCan P g eU' eR' h𝒳 h𝒳' ≅ bcSquareLower P g eU' eR' h𝒳 h𝒳' :=
  BasedCategory.whiskerRightIso
    (BasedNatIso.mkNatIso
      (Functor.fibredMorNatIso (bcSquareFibredMorIso P g eU' eR' h𝒳 h𝒳'))
      (fun A => (bcSquareFibredMorIso P g eU' eR' h𝒳 h𝒳').hom.isHomLift A))
    (stackUliftDown 𝒳)

/-- The presenting 1-morphism of the base-changed presentation is the canonical morphism of
Stacks 04T4 (5): that is the defining property of the equivalence Stacks 04T5 (2) produces. -/
theorem basedFunctor_baseChangedPresentation :
    (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').basedFunctor =
      SelfIntersection.canonicalMapToStack eU' eR'
        (SelfIntersection.isFiberedInSetoids_source eU') h𝒳' := by
  have h : (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').basedFunctor.toFunctor =
      (SelfIntersection.canonicalMapToStack eU' eR'
        (SelfIntersection.isFiberedInSetoids_source eU') h𝒳').toFunctor :=
    (SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
      (𝒰 := (baseChangedAtlasSquare P g).pt) (𝒳 := 𝒳') (f := baseChangedAtlas P g)
      (U := U') (R := R') eU' eR' h𝒳'
      (isRelativelySmooth_baseChangedAtlas P g h𝒳).2
      (isRelativelySurjective_baseChangedAtlas P g h𝒳)).choose_spec
  cases hb : (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').basedFunctor
  rw [hb] at h
  cases h
  rfl

/-- **Stacks 04Y6, assertion (4).** The square

```
[U'/R'] ---ε'---> 𝒳'
   |               |
  [pr]             g
   v               v
 [U/R] ----ε----> 𝒳
```

2-commutes: the presenting 1-morphism of the base-changed presentation followed by `g` is
2-isomorphic, over the big fppf site, to the morphism `[pr]` of quotient stacks induced by `pr`
followed by the presenting 1-morphism of `P`. -/
@[stacks 04Y6 "assertion (4): the square [U'/R'] -> X' -> X and [U'/R'] -> [U/R] -> X 2-commutes"]
theorem nonempty_bcSquareIso :
    Nonempty (BasedFunctor.comp
        (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').basedFunctor g.hom ≅
      BasedFunctor.comp (quotientStackPr P g eU' eR' h𝒳 h𝒳') P.basedFunctor) := by
  rw [basedFunctor_baseChangedPresentation P g eU' eR' h𝒳 h𝒳']
  exact ⟨bcSquareIsoCan P g eU' eR' h𝒳 h𝒳'⟩

end Square

/-! ### The whole statement of Stacks 04Y6 -/

/-- **Stacks 04Y6, the whole statement.** Let `g : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks
over `S` representable by algebraic spaces and let `[U/R] ⟶ 𝒳` be a presentation. Then there are a
presentation `[U'/R'] ⟶ 𝒳'` of the form `(U', R', s', t', c')` — its object space representing
`U' = U ×_𝒳 𝒳'` and its arrow space representing `R' = R ×_𝒳 𝒳'` — and a morphism of groupoids
`pr : (U', R', s', t', c') ⟶ (U, R, s, t, c)` for which the square

```
[U'/R'] ---ε'---> 𝒳'
   |               |
  [pr]             g
   v               v
 [U/R] ----ε----> 𝒳
```

2-commutes.

The four assertions are
`AlgebraicGeometry.Stack.GroupoidPresentation.exists_baseChangedPresentation`,
`...pr`, `...quotientStackPr` and
`AlgebraicGeometry.Stack.GroupoidPresentation.nonempty_bcSquareIso`; this is their conjunction.
The 2-commutativity is a `Nonempty` of an isomorphism of 1-morphisms over the site, an
isomorphism being data while a conjunct must be a proposition — and asserting that a square
2-commutes *is* asserting that such an isomorphism exists. -/
@[stacks 04Y6 "the whole statement: assertions (1), (2), (3) and (4) conjoined"]
theorem exists_baseChangedPresentationSquare
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒳' : IsAlgebraicStack.{u, w} B S hS 𝒳'.val)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    ∃ P' : GroupoidPresentation B S hS 𝒳'.val,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (baseChangedAtlasSquare P g).pt.val.p
        (presheafOfCategories (P'.groupoid.objects.obj ⋙ typeToCat)).p) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (atlasRelationBaseChangeSquare P g).pt.val.p
        (presheafOfCategories (P'.groupoid.arrows.obj ⋙ typeToCat)).p) ∧
      ∃ pr' : GroupoidInAlgebraicSpaces.Hom P'.groupoid P.groupoid,
        Nonempty (BasedFunctor.comp P'.basedFunctor g.hom ≅
          BasedFunctor.comp (quotientStackMap pr') P.basedFunctor) := by
  obtain ⟨FU, hFU, ⟨eU'⟩⟩ := isRepresentableByAlgebraicSpace_baseChangedAtlas P g hg
  obtain ⟨FR, hFR, ⟨eR'⟩⟩ := isRepresentableByAlgebraicSpace_baseChangedRelation P g h𝒳' hg
  exact ⟨baseChangedPresentation (U' := ⟨FU, hFU⟩) (R' := ⟨FR, hFR⟩) P g h𝒳 h𝒳' eU' eR',
    nonempty_equivalenceOver_objects_baseChangedPresentation
      (U' := ⟨FU, hFU⟩) (R' := ⟨FR, hFR⟩) P g h𝒳 h𝒳' eU' eR',
    nonempty_equivalenceOver_arrows_baseChangedPresentation
      (U' := ⟨FU, hFU⟩) (R' := ⟨FR, hFR⟩) P g h𝒳 h𝒳' eU' eR',
    pr (U' := ⟨FU, hFU⟩) (R' := ⟨FR, hFR⟩) P g eU' eR' h𝒳 h𝒳',
    nonempty_bcSquareIso (U' := ⟨FU, hFU⟩) (R' := ⟨FR, hFR⟩) P g eU' eR' h𝒳 h𝒳'⟩

end BaseChange

end AlgebraicGeometry.Stack.GroupoidPresentation

end

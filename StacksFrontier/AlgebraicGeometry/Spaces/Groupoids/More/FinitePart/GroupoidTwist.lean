module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces

/-!
# Twisting the fibre product of the source of a groupoid in algebraic spaces by an arrow

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S`, let `T` be an algebraic space and let `z : T ⟶ R` be a section of the arrow space.
Composing an arrow with the inverse of `z` is an isomorphism
`c(-, i ∘ z) : R ×_{s, U, s ∘ z} T → R ×_{s, U, t ∘ z} T` over `T`, whose inverse is composition
with `z` itself. This file builds that isomorphism. It is the map used in Stacks 04RT to carry
the open subspace of a pair along an arrow, and so is what the target morphism of the finite
part of a groupoid is built from.

## Main definitions

* `AlgebraicGeometry.Space.inverseHom`: the inverse morphism `i : R ⟶ R` of a groupoid in
  algebraic spaces.
* `AlgebraicGeometry.Space.twistMap` and `AlgebraicGeometry.Space.untwistMap`: composition with
  the inverse of a fixed arrow `z`, and composition with `z` itself, as morphisms of the ambient
  fibre products over `T`.
* `AlgebraicGeometry.Space.twistIso`: the isomorphism `c(-, i ∘ z)` over `T` which those two
  morphisms constitute.

## Main results

* `AlgebraicGeometry.Space.twistMap_untwistMap` and
  `AlgebraicGeometry.Space.untwistMap_twistMap`: the two morphisms are mutually inverse; on
  sections these are the cancellation laws `c(c(r, i ∘ z), z) = r` and `c(c(r, z), i ∘ z) = r`.
* `AlgebraicGeometry.Space.twistIso_hom_fst` and `AlgebraicGeometry.Space.twistIso_inv_fst`: the
  isomorphism and its inverse are morphisms over `T`.
* `AlgebraicGeometry.Space.comp_hom_app`: the composition morphism of a groupoid in algebraic
  spaces, read on a section of the fibre product of its source and target, is the composition of
  the underlying groupoid in presheaves.
* `AlgebraicGeometry.Space.inverseHom_comp_source` and
  `AlgebraicGeometry.Space.inverseHom_comp_target`: the inverse morphism exchanges source and
  target.

## Implementation notes

No hypothesis on the groupoid is carried: the twist exists for any groupoid in algebraic spaces
over any base and any section of its arrow space, and separatedness or finite type of the source
and the target plays no part here.

The inverse is not a field of `AlgebraicGeometry.GroupoidInAlgebraicSpaces`. It is the unique
natural transformation of the arrow space inverting every arrow at every test scheme, which
exists by Stacks 06K5 (`Deformation.existsUnique_inverse`), and `inverseHom` is that unique
morphism; nothing is chosen, since the morphism is unique.

The composition of the groupoid has to be read through the evaluated groupoids of the underlying
groupoid in presheaves, the composition being given only by the pointwise groupoid condition.
The helpers `evalMor`, `compose_eq_evalMor` and `inverseArrow_eq_evalMor` translate
between a section of the arrow space with prescribed source and target and the corresponding
arrow of the evaluated groupoid, in which the two cancellation laws are the groupoid identities
`ζ ≫ (ζ⁻¹ ≫ ρ) = ρ` and `ζ⁻¹ ≫ (ζ ≫ ρ) = ρ`. Those helpers are stated for a general groupoid in
presheaves; the `*_app` lemmas restate their consequences for the groupoid in algebraic spaces,
with the source and target written as `G.source.hom.app` rather than through
`toGroupoidInFunctors`, so that rewriting with them is syntactic.

The source and target of the twist are explicit parameters `u` and `a` carrying hypotheses
`z ≫ s = u` and `z ≫ t = a`, rather than being the composites `z ≫ s` and `z ≫ t`, so that a
caller holding these morphisms in another form need not transport the ambient fibre products
along an equality of morphisms.

Composability of two sections of the arrow space is a proposition which the composite depends
on, so the rewriting tactics cannot rewrite the entries of a composite;
`AlgebraicGeometry.Space.compose_congr` is what replaces them instead.

`AlgebraicGeometry.Space.pullbackAtEquiv` repeats, for a pullback of presheaves, what
`AlgebraicGeometry.Space.fiberProductAtEquiv` says for the chosen fibre product of algebraic
spaces. The two differ by the semireducible definition of that chosen fibre product, which the
rewriting tactics will not unfold, so the version stated directly for the presheaf pullback is
the one usable here.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-! ### Arrows of an evaluated groupoid in functors

Composing an arrow with the inverse of another and then with that other arrow returns the
first arrow. These are the two cancellation laws used to see that composing with a fixed arrow
is invertible, and they are proved by translating the composition of the groupoid in functors
into the categorical composition of its evaluated groupoid.
-/

/-- The arrow of an evaluated groupoid determined by an element of the arrow functor whose
source and target are the prescribed objects. -/
public def evalMor {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a : H.arrows.obj T) (x y : H.Evaluation T)
    (hs : H.source.app T a = x) (ht : H.target.app T a = y) : x ⟶ y :=
  (H.evaluationArrowEquiv T x y).symm ⟨a, hs, ht⟩

/-- The arrow element underlying `evalMor` is the given one. -/
public theorem evalMor_val {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a : H.arrows.obj T) (x y : H.Evaluation T)
    (hs : H.source.app T a = x) (ht : H.target.app T a = y) :
    (H.evaluationArrowEquiv T x y (evalMor H T a x y hs ht)).1 = a :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- An arrow of an evaluated groupoid is recognised from the element of the arrow functor
underlying it. -/
public theorem evalMor_eq {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a : H.arrows.obj T) (x y : H.Evaluation T)
    (hs : H.source.app T a = x) (ht : H.target.app T a = y) (f : x ⟶ y)
    (hf : a = (H.evaluationArrowEquiv T x y f).1) :
    evalMor H T a x y hs ht = f := by
  unfold evalMor
  rw [show (⟨a, hs, ht⟩ : {b : H.arrows.obj T //
      H.source.app T b = x ∧ H.target.app T b = y}) =
    H.evaluationArrowEquiv T x y f from Subtype.ext hf, Equiv.symm_apply_apply]

/-- The composition of a groupoid in functors is the categorical composition of its evaluated
groupoid: the composite of `a` and `b` is the arrow of `b` followed by the arrow of `a`. -/
public theorem compose_eq_evalMor {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a b : H.arrows.obj T) {x y z : H.Evaluation T}
    (hsb : H.source.app T b = x) (htb : H.target.app T b = y)
    (hsa : H.source.app T a = y) (hta : H.target.app T a = z)
    (h : H.source.app T a = H.target.app T b) :
    H.compose T a b h =
      (H.evaluationArrowEquiv T x z
        (evalMor H T b x y hsb htb ≫ evalMor H T a y z hsa hta)).1 := by
  rw [H.evaluationArrowEquiv_comp T (evalMor H T b x y hsb htb) (evalMor H T a y z hsa hta)]
  exact congrArg (H.comp.app T) (Subtype.ext (Prod.ext
    (evalMor_val H T a y z hsa hta).symm (evalMor_val H T b x y hsb htb).symm))

/-- The inverse of an arrow element is the element underlying the categorical inverse. -/
private theorem inverseArrow_eq_evalMor {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a : H.arrows.obj T) (x y : H.Evaluation T)
    (hs : H.source.app T a = x) (ht : H.target.app T a = y) :
    Deformation.inverseArrow H T a =
      (H.evaluationArrowEquiv T y x (Groupoid.inv (evalMor H T a x y hs ht))).1 := by
  subst hs
  subst ht
  rfl

/-- The arrow of an evaluated groupoid underlying the inverse of an arrow element is the
categorical inverse. -/
private theorem evalMor_inverseArrow {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a : H.arrows.obj T) (x y : H.Evaluation T)
    (hs : H.source.app T a = x) (ht : H.target.app T a = y)
    (hs' : H.source.app T (Deformation.inverseArrow H T a) = y)
    (ht' : H.target.app T (Deformation.inverseArrow H T a) = x) :
    evalMor H T (Deformation.inverseArrow H T a) y x hs' ht' =
      Groupoid.inv (evalMor H T a x y hs ht) :=
  evalMor_eq H T _ y x hs' ht' _ (inverseArrow_eq_evalMor H T a x y hs ht)

/-- First cancellation law: composing an arrow with the inverse of `z` and then with `z`
returns the arrow. -/
private theorem compose_compose_inverseArrow {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (r z : H.arrows.obj T)
    (h₁ : H.source.app T r = H.target.app T (Deformation.inverseArrow H T z))
    (h₂ : H.source.app T (H.compose T r (Deformation.inverseArrow H T z) h₁) =
      H.target.app T z) :
    H.compose T (H.compose T r (Deformation.inverseArrow H T z) h₁) z h₂ = r := by
  have hsz : H.source.app T z = H.source.app T z := rfl
  have htz : H.target.app T z = H.target.app T z := rfl
  have hiz₁ : H.source.app T (Deformation.inverseArrow H T z) = H.target.app T z :=
    Deformation.inverseArrow_source H T z
  have hiz₂ : H.target.app T (Deformation.inverseArrow H T z) = H.source.app T z :=
    Deformation.inverseArrow_target H T z
  have hr : H.source.app T r = H.source.app T z := h₁.trans hiz₂
  set ζ := evalMor H T z (H.source.app T z) (H.target.app T z) hsz htz with hζ
  set ρ := evalMor H T r (H.source.app T z) (H.target.app T r) hr rfl with hρ
  have hinner : H.compose T r (Deformation.inverseArrow H T z) h₁ =
      (H.evaluationArrowEquiv T (H.target.app T z) (H.target.app T r)
        (Groupoid.inv ζ ≫ ρ)).1 := by
    rw [compose_eq_evalMor H T r (Deformation.inverseArrow H T z) hiz₁ hiz₂ hr rfl h₁]
    exact congrArg (fun k => (H.evaluationArrowEquiv T (H.target.app T z)
      (H.target.app T r) (k ≫ ρ)).1)
      (evalMor_inverseArrow H T z (H.source.app T z) (H.target.app T z) hsz htz hiz₁ hiz₂)
  have hinnerTarget : H.target.app T (H.compose T r
      (Deformation.inverseArrow H T z) h₁) = H.target.app T r := by
    rw [hinner]
    exact (H.evaluationArrowEquiv T _ _ (Groupoid.inv ζ ≫ ρ)).2.2
  rw [compose_eq_evalMor H T (H.compose T r (Deformation.inverseArrow H T z) h₁) z
    hsz htz h₂ hinnerTarget h₂,
    evalMor_eq H T _ (H.target.app T z) (H.target.app T r) h₂ hinnerTarget
      (Groupoid.inv ζ ≫ ρ) hinner]
  rw [← Category.assoc, Groupoid.comp_inv, Category.id_comp]
  exact evalMor_val H T r (H.source.app T z) (H.target.app T r) hr rfl

/-- Second cancellation law: composing an arrow with `z` and then with the inverse of `z`
returns the arrow. -/
private theorem compose_compose_self {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (r z : H.arrows.obj T)
    (h₁ : H.source.app T r = H.target.app T z)
    (h₂ : H.source.app T (H.compose T r z h₁) =
      H.target.app T (Deformation.inverseArrow H T z)) :
    H.compose T (H.compose T r z h₁) (Deformation.inverseArrow H T z) h₂ = r := by
  have hiz₁ : H.source.app T (Deformation.inverseArrow H T z) = H.target.app T z :=
    Deformation.inverseArrow_source H T z
  have hiz₂ : H.target.app T (Deformation.inverseArrow H T z) = H.source.app T z :=
    Deformation.inverseArrow_target H T z
  set ζ := evalMor H T z (H.source.app T z) (H.target.app T z) rfl rfl with hζ
  set ρ := evalMor H T r (H.target.app T z) (H.target.app T r) h₁ rfl with hρ
  have hinner : H.compose T r z h₁ =
      (H.evaluationArrowEquiv T (H.source.app T z) (H.target.app T r) (ζ ≫ ρ)).1 :=
    compose_eq_evalMor H T r z rfl rfl h₁ rfl h₁
  have hinnerSource : H.source.app T (H.compose T r z h₁) = H.source.app T z := by
    rw [hinner]
    exact (H.evaluationArrowEquiv T _ _ (ζ ≫ ρ)).2.1
  have hinnerTarget : H.target.app T (H.compose T r z h₁) = H.target.app T r := by
    rw [hinner]
    exact (H.evaluationArrowEquiv T _ _ (ζ ≫ ρ)).2.2
  rw [compose_eq_evalMor H T (H.compose T r z h₁) (Deformation.inverseArrow H T z)
    hiz₁ hiz₂ hinnerSource hinnerTarget h₂,
    evalMor_eq H T _ (H.source.app T z) (H.target.app T r) hinnerSource hinnerTarget
      (ζ ≫ ρ) hinner,
    evalMor_inverseArrow H T z (H.source.app T z) (H.target.app T z) rfl rfl hiz₁ hiz₂]
  rw [← Category.assoc, Groupoid.inv_comp, Category.id_comp]
  exact evalMor_val H T r (H.target.app T z) (H.target.app T r) h₁ rfl

/-- Composing an arrow with the identity arrow at its target returns the arrow. -/
private theorem compose_identity_left {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D) (b : H.arrows.obj T)
    (h : H.source.app T (H.identity T (H.target.app T b)) = H.target.app T b) :
    H.compose T (H.identity T (H.target.app T b)) b h = b := by
  have hid : H.identity T (H.target.app T b) =
      (H.evaluationArrowEquiv T (H.target.app T b) (H.target.app T b) (𝟙 _)).1 := rfl
  have hidt : H.target.app T (H.identity T (H.target.app T b)) = H.target.app T b := by
    rw [hid]
    exact (H.evaluationArrowEquiv T (H.target.app T b) (H.target.app T b) (𝟙 _)).2.2
  rw [compose_eq_evalMor H T (H.identity T (H.target.app T b)) b rfl rfl h hidt h,
    evalMor_eq H T (H.identity T (H.target.app T b)) (H.target.app T b) (H.target.app T b)
      h hidt (𝟙 _) hid, Category.comp_id]
  exact evalMor_val H T b (H.source.app T b) (H.target.app T b) rfl rfl

/-- The source of a composite is the source of its second entry. -/
private theorem source_compose {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D) (a b : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T b) :
    H.source.app T (H.compose T a b h) = H.source.app T b :=
  (H.pointwiseData T).source_comp a b h

/-- The target of a composite is the target of its first entry. -/
private theorem target_compose {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D) (a b : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T b) :
    H.target.app T (H.compose T a b h) = H.target.app T a :=
  (H.pointwiseData T).target_comp a b h

/-! ### Twisting the fibre product of the source along an arrow

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces, let `T` be an algebraic space and
let `z : T ⟶ R`. Composing with the inverse of `z` is an isomorphism
`c(-, i ∘ z) : R ×_{s, U, s ∘ z} T → R ×_{s, U, t ∘ z} T` over `T`, with inverse composition
with `z`. This is the isomorphism which transports the open subspace of a pair along an arrow,
and so is what the target morphism of the finite part is built from.
-/

section Twist

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B)

/-- The sections of a pullback of presheaves over a test object are the pairs of sections with
the same image, limits of presheaves being computed pointwise. -/
public def pullbackAtEquiv {F₁ F₂ F₃ : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F₁ ⟶ F₃) (g : F₂ ⟶ F₃) (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) :
    (pullback f g).obj T ≃ FiberBaseChange.Obj (f.app T) (g.app T) :=
  (pullbackObjIso f g T).toEquiv.trans
    (Types.pullbackIsoPullback (f.app T) (g.app T)).toEquiv

/-- The first component of a section of a pullback of presheaves is its first projection. -/
public theorem pullbackAtEquiv_fst
    {F₁ F₂ F₃ : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F₁ ⟶ F₃) (g : F₂ ⟶ F₃) (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (x : (pullback f g).obj T) :
    (pullbackAtEquiv f g T x).val.1 = (pullback.fst f g).app T x := by
  simp only [pullbackAtEquiv]
  exact congrArg (fun k => k x) (pullbackObjIso_hom_comp_fst f g T)

/-- The second component of a section of a pullback of presheaves is its second projection. -/
public theorem pullbackAtEquiv_snd
    {F₁ F₂ F₃ : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F₁ ⟶ F₃) (g : F₂ ⟶ F₃) (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (x : (pullback f g).obj T) :
    (pullbackAtEquiv f g T x).val.2 = (pullback.snd f g).app T x := by
  simp only [pullbackAtEquiv]
  exact congrArg (fun k => k x) (pullbackObjIso_hom_comp_snd f g T)

/-- Two sections of a pullback of presheaves with the same two projections are equal. -/
public theorem pullback_obj_ext
    {F₁ F₂ F₃ : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F₁ ⟶ F₃) (g : F₂ ⟶ F₃) (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (x y : (pullback f g).obj T)
    (h₁ : (pullback.fst f g).app T x = (pullback.fst f g).app T y)
    (h₂ : (pullback.snd f g).app T x = (pullback.snd f g).app T y) : x = y := by
  refine (pullbackAtEquiv f g T).injective (Subtype.ext (Prod.ext ?_ ?_))
  · rwa [pullbackAtEquiv_fst, pullbackAtEquiv_fst]
  · rwa [pullbackAtEquiv_snd, pullbackAtEquiv_snd]

/-- The inverse morphism `i : R ⟶ R` of a groupoid in algebraic spaces: the unique natural
transformation of the arrow space inverting every arrow at every test scheme, which exists by
Stacks 06K5. -/
public def inverseHom : G.arrows.obj ⟶ G.arrows.obj :=
  (Deformation.existsUnique_inverse G.toGroupoidInFunctors).choose

/-- The inverse morphism inverts every arrow at every test scheme. -/
public theorem inverseHom_app (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : G.arrows.obj.obj T) :
    (inverseHom G).app T a = Deformation.inverseArrow G.toGroupoidInFunctors T a :=
  (Deformation.existsUnique_inverse G.toGroupoidInFunctors).choose_spec.1 T a

/-- The source of the inverse of an arrow is the target of that arrow. -/
public theorem inverseHom_comp_source : inverseHom G ≫ G.source.hom = G.target.hom := by
  ext T a
  change G.source.hom.app T ((inverseHom G).app T a) = G.target.hom.app T a
  rw [inverseHom_app]
  exact Deformation.inverseArrow_source G.toGroupoidInFunctors T a

/-- The target of the inverse of an arrow is the source of that arrow. -/
public theorem inverseHom_comp_target : inverseHom G ≫ G.target.hom = G.source.hom := by
  ext T a
  change G.target.hom.app T ((inverseHom G).app T a) = G.source.hom.app T a
  rw [inverseHom_app]
  exact Deformation.inverseArrow_target G.toGroupoidInFunctors T a

/-- The composition of a groupoid in algebraic spaces, read on a section of the fibre product
of the source and the target, is the composition of the underlying groupoid in functors. -/
public theorem comp_hom_app (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (y : (pullback G.source.hom G.target.hom).obj T)
    (h : G.source.hom.app T ((pullback.fst G.source.hom G.target.hom).app T y) =
      G.target.hom.app T ((pullback.snd G.source.hom G.target.hom).app T y)) :
    G.comp.hom.app T y = G.toGroupoidInFunctors.compose T
      ((pullback.fst G.source.hom G.target.hom).app T y)
      ((pullback.snd G.source.hom G.target.hom).app T y) h := by
  have hback : (AlgebraicGeometry.composableToPullback G.source.hom G.target.hom).app T
      ⟨((pullback.fst G.source.hom G.target.hom).app T y,
        (pullback.snd G.source.hom G.target.hom).app T y), h⟩ = y := by
    refine pullback_obj_ext G.source.hom G.target.hom T _ y ?_ ?_
    · change ((AlgebraicGeometry.composableToPullback G.source.hom G.target.hom ≫
        pullback.fst G.source.hom G.target.hom).app T) _ = _
      rw [AlgebraicGeometry.composableToPullback, pullback.lift_fst]
      rfl
    · change ((AlgebraicGeometry.composableToPullback G.source.hom G.target.hom ≫
        pullback.snd G.source.hom G.target.hom).app T) _ = _
      rw [AlgebraicGeometry.composableToPullback, pullback.lift_snd]
      rfl
  exact congrArg (fun z => G.comp.hom.app T z) hback.symm

/-- The source of a composite of sections of the arrow space is the source of its second
entry. -/
public theorem source_comp_hom_app (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : G.arrows.obj.obj T) (h : G.source.hom.app T a = G.target.hom.app T b) :
    G.source.hom.app T (G.toGroupoidInFunctors.compose T a b h) = G.source.hom.app T b :=
  source_compose G.toGroupoidInFunctors T a b h

/-- The target of a composite of sections of the arrow space is the target of its first
entry. -/
public theorem target_comp_hom_app (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : G.arrows.obj.obj T) (h : G.source.hom.app T a = G.target.hom.app T b) :
    G.target.hom.app T (G.toGroupoidInFunctors.compose T a b h) = G.target.hom.app T a :=
  target_compose G.toGroupoidInFunctors T a b h

/-- The source of the inverse of a section of the arrow space is its target. -/
public theorem inverseHom_app_source (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : G.arrows.obj.obj T) :
    G.source.hom.app T ((inverseHom G).app T a) = G.target.hom.app T a :=
  congrArg (fun k => k.app T a) (inverseHom_comp_source G)

/-- The target of the inverse of a section of the arrow space is its source. -/
public theorem inverseHom_app_target (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : G.arrows.obj.obj T) :
    G.target.hom.app T ((inverseHom G).app T a) = G.source.hom.app T a :=
  congrArg (fun k => k.app T a) (inverseHom_comp_target G)

/-- Composing a section of the arrow space with the inverse of another and then with that
other returns the first section. -/
private theorem compose_compose_inverseHom_app
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (r b : G.arrows.obj.obj T)
    (h₁ : G.source.hom.app T r =
      G.target.hom.app T (Deformation.inverseArrow G.toGroupoidInFunctors T b))
    (h₂ : G.source.hom.app T (G.toGroupoidInFunctors.compose T r
      (Deformation.inverseArrow G.toGroupoidInFunctors T b) h₁) = G.target.hom.app T b) :
    G.toGroupoidInFunctors.compose T (G.toGroupoidInFunctors.compose T r
      (Deformation.inverseArrow G.toGroupoidInFunctors T b) h₁) b h₂ = r :=
  compose_compose_inverseArrow G.toGroupoidInFunctors T r b h₁ h₂

/-- Composing a section of the arrow space with another and then with the inverse of that
other returns the first section. -/
private theorem compose_compose_self_app
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (r b : G.arrows.obj.obj T)
    (h₁ : G.source.hom.app T r = G.target.hom.app T b)
    (h₂ : G.source.hom.app T (G.toGroupoidInFunctors.compose T r b h₁) =
      G.target.hom.app T (Deformation.inverseArrow G.toGroupoidInFunctors T b)) :
    G.toGroupoidInFunctors.compose T (G.toGroupoidInFunctors.compose T r b h₁)
      (Deformation.inverseArrow G.toGroupoidInFunctors T b) h₂ = r :=
  compose_compose_self G.toGroupoidInFunctors T r b h₁ h₂

/-- The source of the inverse of a section of the arrow space is its target. -/
public theorem inverseArrow_app_source (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : G.arrows.obj.obj T) :
    G.source.hom.app T (Deformation.inverseArrow G.toGroupoidInFunctors T a) =
      G.target.hom.app T a :=
  Deformation.inverseArrow_source G.toGroupoidInFunctors T a

/-- The target of the inverse of a section of the arrow space is its source. -/
public theorem inverseArrow_app_target (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : G.arrows.obj.obj T) :
    G.target.hom.app T (Deformation.inverseArrow G.toGroupoidInFunctors T a) =
      G.source.hom.app T a :=
  Deformation.inverseArrow_target G.toGroupoidInFunctors T a

/-- The composite of two sections of the arrow space depends only on those two sections, the
composability hypothesis being a proposition. -/
public theorem compose_congr (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b a' b' : G.arrows.obj.obj T)
    (h : G.source.hom.app T a = G.target.hom.app T b)
    (h' : G.source.hom.app T a' = G.target.hom.app T b')
    (ha : a = a') (hb : b = b') :
    G.toGroupoidInFunctors.compose T a b h = G.toGroupoidInFunctors.compose T a' b' h' := by
  subst ha
  subst hb
  rfl

/-- Composing a section of the arrow space with the identity at its target returns it. -/
public theorem compose_identity_app (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (b : G.arrows.obj.obj T)
    (h : G.source.hom.app T
      (G.toGroupoidInFunctors.identity T (G.target.hom.app T b)) =
      G.target.hom.app T b) :
    G.toGroupoidInFunctors.compose T
      (G.toGroupoidInFunctors.identity T (G.target.hom.app T b)) b h = b :=
  compose_identity_left G.toGroupoidInFunctors T b h

/-- The two projections of a section of a pullback of presheaves have the same image. -/
public theorem pullback_condition_app
    {F₁ F₂ F₃ : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F₁ ⟶ F₃) (g : F₂ ⟶ F₃) (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (x : (pullback f g).obj T) :
    f.app T ((pullback.fst f g).app T x) = g.app T ((pullback.snd f g).app T x) :=
  congrArg (fun k => k.app T x) (pullback.condition (f := f) (g := g))

/-- The composition of the groupoid on a section of the fibre product whose entries are `r` and
`q` is the composite of `r` and `q`. -/
private theorem comp_hom_app_eq_compose (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (w : (pullback G.source.hom G.target.hom).obj T) (r q : G.arrows.obj.obj T)
    (hr : (pullback.fst G.source.hom G.target.hom).app T w = r)
    (hq : (pullback.snd G.source.hom G.target.hom).app T w = q)
    (h : G.source.hom.app T r = G.target.hom.app T q) :
    G.comp.hom.app T w = G.toGroupoidInFunctors.compose T r q h :=
  (comp_hom_app G T w (pullback_condition_app G.source.hom G.target.hom T w)).trans
    (compose_congr G T _ _ _ _ _ h hr hq)

variable {T : AlgebraicGeometry.AlgebraicSpaces C S hS}

/-- The composable pair `(r, i ∘ z ∘ pr₁)` of arrows on the fibre product `T ×_{s ∘ z, U, s} R`,
whose composite is the twist of a section by the inverse of `z`. -/
public def twistPair (z : T ⟶ G.arrows) (u : T ⟶ G.objects) (hu : z ≫ G.source = u) :
    pullback u.hom G.source.hom ⟶ pullback G.source.hom G.target.hom :=
  pullback.lift (pullback.snd u.hom G.source.hom)
    (pullback.fst u.hom G.source.hom ≫ z.hom ≫ inverseHom G) (by
      have hu' : z.hom ≫ G.source.hom = u.hom :=
        congrArg (fun k : T ⟶ G.objects => k.hom) hu
      calc
        pullback.snd u.hom G.source.hom ≫ G.source.hom =
            pullback.fst u.hom G.source.hom ≫ u.hom := pullback.condition.symm
        _ = pullback.fst u.hom G.source.hom ≫ z.hom ≫ G.source.hom :=
            congrArg (fun k => pullback.fst u.hom G.source.hom ≫ k) hu'.symm
        _ = (pullback.fst u.hom G.source.hom ≫ z.hom ≫ inverseHom G) ≫ G.target.hom := by
            simp only [Category.assoc, inverseHom_comp_target])

/-- The first entry of the twisting pair is the given section of `R`. -/
public theorem twistPair_fst (z : T ⟶ G.arrows) (u : T ⟶ G.objects) (hu : z ≫ G.source = u) :
    twistPair G z u hu ≫ pullback.fst G.source.hom G.target.hom =
      pullback.snd u.hom G.source.hom :=
  pullback.lift_fst _ _ _

/-- The second entry of the twisting pair is the inverse of the given arrow. -/
public theorem twistPair_snd (z : T ⟶ G.arrows) (u : T ⟶ G.objects) (hu : z ≫ G.source = u) :
    twistPair G z u hu ≫ pullback.snd G.source.hom G.target.hom =
      pullback.fst u.hom G.source.hom ≫ z.hom ≫ inverseHom G :=
  pullback.lift_snd _ _ _

/-- The composable pair `(r, z ∘ pr₁)` of arrows on the fibre product `T ×_{t ∘ z, U, s} R`,
whose composite is the twist of a section by `z` itself. -/
public def untwistPair (z : T ⟶ G.arrows) (a : T ⟶ G.objects) (ha : z ≫ G.target = a) :
    pullback a.hom G.source.hom ⟶ pullback G.source.hom G.target.hom :=
  pullback.lift (pullback.snd a.hom G.source.hom)
    (pullback.fst a.hom G.source.hom ≫ z.hom) (by
      have ha' : z.hom ≫ G.target.hom = a.hom :=
        congrArg (fun k : T ⟶ G.objects => k.hom) ha
      calc
        pullback.snd a.hom G.source.hom ≫ G.source.hom =
            pullback.fst a.hom G.source.hom ≫ a.hom := pullback.condition.symm
        _ = pullback.fst a.hom G.source.hom ≫ z.hom ≫ G.target.hom :=
            congrArg (fun k => pullback.fst a.hom G.source.hom ≫ k) ha'.symm
        _ = (pullback.fst a.hom G.source.hom ≫ z.hom) ≫ G.target.hom := (Category.assoc _ _ _).symm)

/-- The first entry of the untwisting pair is the given section of `R`. -/
public theorem untwistPair_fst (z : T ⟶ G.arrows) (a : T ⟶ G.objects)
    (ha : z ≫ G.target = a) :
    untwistPair G z a ha ≫ pullback.fst G.source.hom G.target.hom =
      pullback.snd a.hom G.source.hom :=
  pullback.lift_fst _ _ _

/-- The second entry of the untwisting pair is the given arrow. -/
public theorem untwistPair_snd (z : T ⟶ G.arrows) (a : T ⟶ G.objects)
    (ha : z ≫ G.target = a) :
    untwistPair G z a ha ≫ pullback.snd G.source.hom G.target.hom =
      pullback.fst a.hom G.source.hom ≫ z.hom :=
  pullback.lift_snd _ _ _

/-- Composing with the inverse of a fixed arrow `z : T ⟶ R`, as a morphism
`T ×_{s ∘ z, U, s} R ⟶ T ×_{t ∘ z, U, s} R` over `T`: on sections it sends `(pt, r)` to
`(pt, c(r, i ∘ z(pt)))`. -/
public def twistMap (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    pullback u.hom G.source.hom ⟶ pullback a.hom G.source.hom :=
  pullback.lift (pullback.fst u.hom G.source.hom) (twistPair G z u hu ≫ G.comp.hom) (by
    have ha' : z.hom ≫ G.target.hom = a.hom :=
      congrArg (fun k : T ⟶ G.objects => k.hom) ha
    ext T' y
    have hsnd : (pullback.snd G.source.hom G.target.hom).app T'
        ((twistPair G z u hu).app T' y) =
        (inverseHom G).app T' (z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y)) :=
      congrArg (fun k => k.app T' y) (twistPair_snd G z u hu)
    have hcond := pullback_condition_app G.source.hom G.target.hom T'
      ((twistPair G z u hu).app T' y)
    change a.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y) =
      G.source.hom.app T' (G.comp.hom.app T' ((twistPair G z u hu).app T' y))
    rw [comp_hom_app G T' _ hcond, source_comp_hom_app, hsnd, inverseHom_app_source]
    exact (congrArg (fun k => k.app T' ((pullback.fst u.hom G.source.hom).app T' y)) ha').symm)

/-- The twist is a morphism over `T`. -/
public theorem twistMap_fst (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    twistMap G z u a hu ha ≫ pullback.fst a.hom G.source.hom =
      pullback.fst u.hom G.source.hom :=
  pullback.lift_fst _ _ _

/-- The section of `R` underlying the twist of a section is the composite of that section
with the inverse of the fixed arrow. -/
public theorem twistMap_snd (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    twistMap G z u a hu ha ≫ pullback.snd a.hom G.source.hom =
      twistPair G z u hu ≫ G.comp.hom :=
  pullback.lift_snd _ _ _

/-- Composing with a fixed arrow `z : T ⟶ R`, as a morphism
`T ×_{t ∘ z, U, s} R ⟶ T ×_{s ∘ z, U, s} R` over `T`: on sections it sends `(pt, r)` to
`(pt, c(r, z(pt)))`. This is the inverse of `twistMap`. -/
public def untwistMap (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    pullback a.hom G.source.hom ⟶ pullback u.hom G.source.hom :=
  pullback.lift (pullback.fst a.hom G.source.hom) (untwistPair G z a ha ≫ G.comp.hom) (by
    have hu' : z.hom ≫ G.source.hom = u.hom :=
      congrArg (fun k : T ⟶ G.objects => k.hom) hu
    ext T' y
    have hsnd : (pullback.snd G.source.hom G.target.hom).app T'
        ((untwistPair G z a ha).app T' y) =
        z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y) :=
      congrArg (fun k => k.app T' y) (untwistPair_snd G z a ha)
    have hcond := pullback_condition_app G.source.hom G.target.hom T'
      ((untwistPair G z a ha).app T' y)
    change u.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y) =
      G.source.hom.app T' (G.comp.hom.app T' ((untwistPair G z a ha).app T' y))
    rw [comp_hom_app G T' _ hcond, source_comp_hom_app, hsnd]
    exact (congrArg (fun k => k.app T' ((pullback.fst a.hom G.source.hom).app T' y)) hu').symm)

/-- The untwist is a morphism over `T`. -/
public theorem untwistMap_fst (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    untwistMap G z u a hu ha ≫ pullback.fst u.hom G.source.hom =
      pullback.fst a.hom G.source.hom :=
  pullback.lift_fst _ _ _

/-- The section of `R` underlying the untwist of a section is the composite of that section
with the fixed arrow. -/
public theorem untwistMap_snd (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    untwistMap G z u a hu ha ≫ pullback.snd u.hom G.source.hom =
      untwistPair G z a ha ≫ G.comp.hom :=
  pullback.lift_snd _ _ _

/-- Twisting by the inverse of `z` and then by `z` is the identity: on sections this is the
cancellation `c(c(r, i ∘ z), z) = r`. -/
public theorem twistMap_untwistMap (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    twistMap G z u a hu ha ≫ untwistMap G z u a hu ha = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, untwistMap_fst, twistMap_fst, Category.id_comp]
  · rw [Category.assoc, untwistMap_snd, Category.id_comp]
    ext T' y
    have hfstTw : (pullback.fst a.hom G.source.hom).app T'
        ((twistMap G z u a hu ha).app T' y) =
        (pullback.fst u.hom G.source.hom).app T' y :=
      congrArg (fun k => k.app T' y) (twistMap_fst G z u a hu ha)
    have hsndTw : (pullback.snd a.hom G.source.hom).app T'
        ((twistMap G z u a hu ha).app T' y) =
        G.comp.hom.app T' ((twistPair G z u hu).app T' y) :=
      congrArg (fun k => k.app T' y) (twistMap_snd G z u a hu ha)
    have hfstTp : (pullback.fst G.source.hom G.target.hom).app T'
        ((twistPair G z u hu).app T' y) = (pullback.snd u.hom G.source.hom).app T' y :=
      congrArg (fun k => k.app T' y) (twistPair_fst G z u hu)
    have hsndTp : (pullback.snd G.source.hom G.target.hom).app T'
        ((twistPair G z u hu).app T' y) =
        Deformation.inverseArrow G.toGroupoidInFunctors T'
          (z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y)) :=
      (congrArg (fun k => k.app T' y) (twistPair_snd G z u hu)).trans
        (inverseHom_app G T' _)
    have h₁ : G.source.hom.app T' ((pullback.snd u.hom G.source.hom).app T' y) =
        G.target.hom.app T' (Deformation.inverseArrow G.toGroupoidInFunctors T'
          (z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y))) := by
      rw [← hfstTp, ← hsndTp]
      exact pullback_condition_app G.source.hom G.target.hom T' _
    have h₂ : G.source.hom.app T' (G.toGroupoidInFunctors.compose T'
          ((pullback.snd u.hom G.source.hom).app T' y)
          (Deformation.inverseArrow G.toGroupoidInFunctors T'
            (z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y))) h₁) =
        G.target.hom.app T'
          (z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y)) :=
      (source_comp_hom_app G T' _ _ h₁).trans (inverseArrow_app_source G T' _)
    have hinner : G.comp.hom.app T' ((twistPair G z u hu).app T' y) =
        G.toGroupoidInFunctors.compose T'
          ((pullback.snd u.hom G.source.hom).app T' y)
          (Deformation.inverseArrow G.toGroupoidInFunctors T'
            (z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y))) h₁ :=
      comp_hom_app_eq_compose G T' _ _ _ hfstTp hsndTp h₁
    have hfstUp : (pullback.fst G.source.hom G.target.hom).app T'
        ((untwistPair G z a ha).app T' ((twistMap G z u a hu ha).app T' y)) =
        G.toGroupoidInFunctors.compose T'
          ((pullback.snd u.hom G.source.hom).app T' y)
          (Deformation.inverseArrow G.toGroupoidInFunctors T'
            (z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y))) h₁ :=
      ((congrArg (fun k => k.app T' ((twistMap G z u a hu ha).app T' y))
        (untwistPair_fst G z a ha)).trans hsndTw).trans hinner
    have hsndUp : (pullback.snd G.source.hom G.target.hom).app T'
        ((untwistPair G z a ha).app T' ((twistMap G z u a hu ha).app T' y)) =
        z.hom.app T' ((pullback.fst u.hom G.source.hom).app T' y) :=
      (congrArg (fun k => k.app T' ((twistMap G z u a hu ha).app T' y))
        (untwistPair_snd G z a ha)).trans (congrArg (fun q => z.hom.app T' q) hfstTw)
    change G.comp.hom.app T'
        ((untwistPair G z a ha).app T' ((twistMap G z u a hu ha).app T' y)) =
      (pullback.snd u.hom G.source.hom).app T' y
    exact (comp_hom_app_eq_compose G T' _ _ _ hfstUp hsndUp h₂).trans
      (compose_compose_inverseHom_app G T' _ _ h₁ h₂)

/-- Twisting by `z` and then by the inverse of `z` is the identity: on sections this is the
cancellation `c(c(r, z), i ∘ z) = r`. -/
public theorem untwistMap_twistMap (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    untwistMap G z u a hu ha ≫ twistMap G z u a hu ha = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, twistMap_fst, untwistMap_fst, Category.id_comp]
  · rw [Category.assoc, twistMap_snd, Category.id_comp]
    ext T' y
    have hfstUw : (pullback.fst u.hom G.source.hom).app T'
        ((untwistMap G z u a hu ha).app T' y) =
        (pullback.fst a.hom G.source.hom).app T' y :=
      congrArg (fun k => k.app T' y) (untwistMap_fst G z u a hu ha)
    have hsndUw : (pullback.snd u.hom G.source.hom).app T'
        ((untwistMap G z u a hu ha).app T' y) =
        G.comp.hom.app T' ((untwistPair G z a ha).app T' y) :=
      congrArg (fun k => k.app T' y) (untwistMap_snd G z u a hu ha)
    have hfstUp : (pullback.fst G.source.hom G.target.hom).app T'
        ((untwistPair G z a ha).app T' y) = (pullback.snd a.hom G.source.hom).app T' y :=
      congrArg (fun k => k.app T' y) (untwistPair_fst G z a ha)
    have hsndUp : (pullback.snd G.source.hom G.target.hom).app T'
        ((untwistPair G z a ha).app T' y) =
        z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y) :=
      congrArg (fun k => k.app T' y) (untwistPair_snd G z a ha)
    have h₁ : G.source.hom.app T' ((pullback.snd a.hom G.source.hom).app T' y) =
        G.target.hom.app T' (z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y)) := by
      rw [← hfstUp, ← hsndUp]
      exact pullback_condition_app G.source.hom G.target.hom T' _
    have h₂ : G.source.hom.app T' (G.toGroupoidInFunctors.compose T'
          ((pullback.snd a.hom G.source.hom).app T' y)
          (z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y)) h₁) =
        G.target.hom.app T' (Deformation.inverseArrow G.toGroupoidInFunctors T'
          (z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y))) :=
      (source_comp_hom_app G T' _ _ h₁).trans
        (inverseArrow_app_target G T' _).symm
    have hinner : G.comp.hom.app T' ((untwistPair G z a ha).app T' y) =
        G.toGroupoidInFunctors.compose T'
          ((pullback.snd a.hom G.source.hom).app T' y)
          (z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y)) h₁ :=
      comp_hom_app_eq_compose G T' _ _ _ hfstUp hsndUp h₁
    have hfstTp : (pullback.fst G.source.hom G.target.hom).app T'
        ((twistPair G z u hu).app T' ((untwistMap G z u a hu ha).app T' y)) =
        G.toGroupoidInFunctors.compose T'
          ((pullback.snd a.hom G.source.hom).app T' y)
          (z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y)) h₁ :=
      ((congrArg (fun k => k.app T' ((untwistMap G z u a hu ha).app T' y))
        (twistPair_fst G z u hu)).trans hsndUw).trans hinner
    have hsndTp : (pullback.snd G.source.hom G.target.hom).app T'
        ((twistPair G z u hu).app T' ((untwistMap G z u a hu ha).app T' y)) =
        Deformation.inverseArrow G.toGroupoidInFunctors T'
          (z.hom.app T' ((pullback.fst a.hom G.source.hom).app T' y)) :=
      ((congrArg (fun k => k.app T' ((untwistMap G z u a hu ha).app T' y))
        (twistPair_snd G z u hu)).trans (inverseHom_app G T' _)).trans
        (congrArg (fun q => Deformation.inverseArrow G.toGroupoidInFunctors T'
          (z.hom.app T' q)) hfstUw)
    change G.comp.hom.app T'
        ((twistPair G z u hu).app T' ((untwistMap G z u a hu ha).app T' y)) =
      (pullback.snd a.hom G.source.hom).app T' y
    exact (comp_hom_app_eq_compose G T' _ _ _ hfstTp hsndTp h₂).trans
      (compose_compose_self_app G T' _ _ h₁ h₂)

/-- **The twisting isomorphism.** For an algebraic space `T` and a section `z : T ⟶ R` of the
arrow space, composition with the inverse of `z` is an isomorphism
`T ×_{s ∘ z, U, s} R ≅ T ×_{t ∘ z, U, s} R` over `T`, with inverse composition with `z`. This
is the isomorphism `c(-, i ∘ z)` of Stacks 04RT used to define the target morphism of the
finite part. -/
public def twistIso (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    pullback u.hom G.source.hom ≅ pullback a.hom G.source.hom where
  hom := twistMap G z u a hu ha
  inv := untwistMap G z u a hu ha
  hom_inv_id := twistMap_untwistMap G z u a hu ha
  inv_hom_id := untwistMap_twistMap G z u a hu ha

/-- The twisting isomorphism is a morphism over `T`. -/
public theorem twistIso_hom_fst (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    (twistIso G z u a hu ha).hom ≫ pullback.fst a.hom G.source.hom =
      pullback.fst u.hom G.source.hom :=
  twistMap_fst G z u a hu ha

/-- The inverse of the twisting isomorphism is a morphism over `T`. -/
public theorem twistIso_inv_fst (z : T ⟶ G.arrows) (u a : T ⟶ G.objects)
    (hu : z ≫ G.source = u) (ha : z ≫ G.target = a) :
    (twistIso G z u a hu ha).inv ≫ pullback.fst u.hom G.source.hom =
      pullback.fst a.hom G.source.hom :=
  untwistMap_fst G z u a hu ha

end Twist

end AlgebraicGeometry.Space

end

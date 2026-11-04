module

public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension

/-!
# Automorphism groups at a point through the automorphism group algebraic space

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and let `x : Spec k → 𝒳` be a field-valued
point. Stacks 0DTW says that `f` induces an isomorphism between automorphism groups at the point
of `|𝒳|` represented by `x` when the map `G_x ⟶ G_{f ∘ x}` of automorphism group algebraic
spaces is an isomorphism. This library spells the condition in two ways:

* `AlgebraicGeometry.Stack.InducesIsomorphismAt`, on the sections: at every object lying above
  every representative, `f` is bijective on the vertical automorphism groups;
* `CategoryTheory.IsIso (AlgebraicGeometry.Stack.pointAutomorphismSpaceMap f x)`, on the
  automorphism group algebraic spaces themselves.

This file proves that they agree, and so with **Stacks 0DTV**
(`AlgebraicGeometry.Stack.exists_isIso_pointAutomorphismSpaceMap_iff_forall`) that a single
field-valued representative decides `InducesIsomorphismAt`.

## Main results

* `CategoryTheory.Functor.verticalAutConj`: conjugation by an *arbitrary* isomorphism identifies
  the automorphism groups of its source and target. Unlike
  `CategoryTheory.Functor.verticalAutCongr`, the isomorphism need not lie over an identity.
* `CategoryTheory.Functor.bijective_verticalAutMap_of_iso'`: hence bijectivity of
  `CategoryTheory.Functor.verticalAutMap` is invariant under arbitrary isomorphisms.
* `CategoryTheory.Functor.fiberIsoEndEquiv`: the automorphisms of an object of a fibre category
  are the vertical automorphisms of the underlying object.
* `AlgebraicGeometry.Stack.bijective_isomSpaceMap_app_iff_bijective_automorphismGroupMap`:
  `Isom_𝒳(x, x) ⟶ Isom_𝒴(f x, f x)` is bijective on the sections over `V` exactly when `f` is
  bijective on the vertical automorphism group of the chosen pullback of `x` to `V`.
* `AlgebraicGeometry.Stack.inducesIsomorphismAtObject_of_isIso_pointAutomorphismSpaceMap` and
  `AlgebraicGeometry.Stack.isIso_pointAutomorphismSpaceMap_of_inducesIsomorphismAtObject`: the
  map of automorphism group algebraic spaces at `x` is an isomorphism exactly when `f` induces
  isomorphisms between automorphism groups at every object above `x`.
* `AlgebraicGeometry.Stack.inducesIsomorphismAt_of_isIso_pointAutomorphismSpaceMap` and
  `AlgebraicGeometry.Stack.inducesIsomorphismAt_iff_isIso_pointAutomorphismSpaceMap`:
  **Stacks 0DTW through one representative.**

## References

* [Stacks Project, Tag 0DTV](https://stacks.math.columbia.edu/tag/0DTV)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe uC vC uX vX uY vY

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y]

/-- Conjugation by an isomorphism `e : a ≅ b` identifies the automorphism groups of `a` and `b`
for any isomorphism `e`: the conjugate of an automorphism lying over an identity lies over an
identity, because `p` sends `e⁻¹ ≫ α ≫ e` to `p e⁻¹ ≫ p e = 𝟙`. -/
def verticalAutConj (p : X ⥤ C) {a b : X} (e : a ≅ b) :
    p.verticalAut a ≃* p.verticalAut b where
  toFun α := ⟨Aut.autMulEquivOfIso e α, by
    simp only [mem_verticalAut_iff]
    change p.map (e.inv ≫ (α : Aut a).hom ≫ e.hom) = _
    rw [p.map_comp, p.map_comp, verticalAut.cond α, Category.id_comp, ← p.map_comp,
      e.inv_hom_id, p.map_id]⟩
  invFun β := ⟨(Aut.autMulEquivOfIso e).symm β, by
    simp only [mem_verticalAut_iff]
    change p.map (e.hom ≫ (β : Aut b).hom ≫ e.inv) = _
    rw [p.map_comp, p.map_comp, verticalAut.cond β, Category.id_comp, ← p.map_comp,
      e.hom_inv_id, p.map_id]⟩
  left_inv α := Subtype.ext ((Aut.autMulEquivOfIso e).symm_apply_apply _)
  right_inv β := Subtype.ext ((Aut.autMulEquivOfIso e).apply_symm_apply _)
  map_mul' α β := Subtype.ext (map_mul (Aut.autMulEquivOfIso e) _ _)

variable {pX : X ⥤ C} {pY : Y ⥤ C}

/-- Whether a functor over `C` induces an isomorphism between the automorphism groups at an
object only depends on the object up to an *arbitrary* isomorphism. -/
theorem bijective_verticalAutMap_of_iso' (F : X ⥤ Y) (hF : F ⋙ pY = pX) {a b : X} (e : a ≅ b)
    (hb : Function.Bijective (verticalAutMap F hF b)) :
    Function.Bijective (verticalAutMap F hF a) := by
  have key : (verticalAutMap F hF a : pX.verticalAut a → _) =
      (verticalAutConj pY (F.mapIso e)).symm ∘ (verticalAutMap F hF b) ∘
        (verticalAutConj pX e) := by
    funext α
    apply (verticalAutConj pY (F.mapIso e)).injective
    simp only [Function.comp_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Aut.ext
    show F.map e.inv ≫ F.map (α : Aut a).hom ≫ F.map e.hom =
      F.map (e.inv ≫ (α : Aut a).hom ≫ e.hom)
    simp
  rw [key]
  exact (verticalAutConj pY (F.mapIso e)).symm.bijective.comp
    (hb.comp (verticalAutConj pX e).bijective)

/-- An endomorphism in a fibre lying over an identity: `p` sends it to an identity. -/
lemma map_fiberInclusion_map_eq_id (p : X ⥤ C) {c : C} {A : p.Fiber c} (m : A ⟶ A) :
    p.map (Fiber.fiberInclusion.map m) = 𝟙 (p.obj A.1) := by
  have h := IsHomLift.fac' p (𝟙 c) (Fiber.fiberInclusion.map m)
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl] at h
  exact h

/-- The automorphisms of an object `A` of the fibre category of `p` over `c` are the vertical
automorphisms of the underlying object of `A`. -/
noncomputable def fiberIsoEndEquiv (p : X ⥤ C) {c : C} (A : p.Fiber c) :
    {m : A ⟶ A // IsIso m} ≃ p.verticalAut A.1 where
  toFun m := haveI := m.2
    ⟨Fiber.fiberInclusion.mapIso (asIso m.1),
      (mem_verticalAut_iff p _).mpr (map_fiberInclusion_map_eq_id p m.1)⟩
  invFun α :=
    haveI : IsHomLift p (𝟙 c) (α : Aut A.1).hom :=
      IsHomLift.of_fac' p _ _ A.2 A.2 (by simp [verticalAut.cond α])
    haveI : IsHomLift p (𝟙 c) (α : Aut A.1).inv :=
      IsHomLift.of_fac' p _ _ A.2 A.2 (by
        have h0 : p.map ((α : Aut A.1).hom ≫ (α : Aut A.1).inv) = p.map (𝟙 _) :=
          congrArg p.map (α : Aut A.1).hom_inv_id
        rw [p.map_comp, verticalAut.cond α, Category.id_comp, p.map_id] at h0
        simp [h0])
    ⟨Fiber.homMk p c (α : Aut A.1).hom,
      ⟨Fiber.homMk p c (α : Aut A.1).inv,
        Fiber.hom_ext (α : Aut A.1).hom_inv_id, Fiber.hom_ext (α : Aut A.1).inv_hom_id⟩⟩
  left_inv m := Subtype.ext (Fiber.hom_ext rfl)
  right_inv α := Subtype.ext (Aut.ext rfl)

/-- **Bijectivity on fibre automorphisms is bijectivity on vertical automorphisms.** Let
`F : X ⥤ Y` be a functor strictly over `C`, let `A` be an object of the fibre of `pX` over `c` and
let `ψ : B' ≅ F A` be an isomorphism in the fibre of `pY` over `c`. Then `F`, conjugated by `ψ`,
is bijective from the automorphisms of `A` in its fibre to those of `B'` exactly when `F` is
bijective on the vertical automorphism groups at `A`. -/
theorem bijective_fiberConj_iff (F : X ⥤ Y) (hF : F ⋙ pY = pX) {c : C} (A : pX.Fiber c)
    (B' : pY.Fiber c) (ψ : B' ≅ (fiberFunctorOfCompEq hF c).obj A) :
    Function.Bijective (fun m : {m : A ⟶ A // IsIso m} =>
      (⟨ψ.hom ≫ (fiberFunctorOfCompEq hF c).map m.1 ≫ ψ.inv,
        by have := m.2; infer_instance⟩ : {m : B' ⟶ B' // IsIso m})) ↔
      Function.Bijective (verticalAutMap F hF A.1) := by
  let e : F.obj A.1 ≅ B'.1 := (Fiber.fiberInclusion.mapIso ψ).symm
  have key : (fun m : {m : A ⟶ A // IsIso m} =>
      (⟨ψ.hom ≫ (fiberFunctorOfCompEq hF c).map m.1 ≫ ψ.inv,
        by have := m.2; infer_instance⟩ : {m : B' ⟶ B' // IsIso m})) =
      (fiberIsoEndEquiv pY B').symm ∘ (verticalAutConj pY e) ∘ (verticalAutMap F hF A.1) ∘
        (fiberIsoEndEquiv pX A) := by
    funext m
    apply (fiberIsoEndEquiv pY B').injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Aut.ext
    simp [fiberIsoEndEquiv, verticalAutConj, verticalAutMap, Aut.autMulEquivOfIso, e]
    rfl
  rw [key]
  exact (EquivLike.comp_bijective _ (fiberIsoEndEquiv pY B').symm).trans
    ((EquivLike.comp_bijective _ (verticalAutConj pY e)).trans
      (EquivLike.bijective_comp (fiberIsoEndEquiv pX A) _))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The map of Isom sheaves on sections is the map of vertical automorphism groups.** For a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, an object `x` of the fibre of `𝒳` over `U` and an
object `V` of the big fppf site of `U`, the map `Isom_𝒳(x, x) ⟶ Isom_𝒴(f x, f x)` is bijective on
`V`-sections exactly when `f` is bijective on the vertical automorphism group of the chosen
pullback of `x` to `V`. -/
theorem bijective_isomSpaceMap_app_iff_bijective_automorphismGroupMap (f : 𝒳 ⟶ 𝒴)
    (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U) (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Function.Bijective ((isomSpaceMap B S hS 𝒳.val 𝒴.val f.hom.hom U x x).app W) ↔
      Function.Bijective (automorphismGroupMap B S hS f
        (Functor.pullbackFiber 𝒳.val.val.p x (sliceObj B S hS U W).hom).1) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  exact Functor.bijective_fiberConj_iff (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) _ _
    ((isFibredOneMorphism_basedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).mapPullbackFiberIso x
      (sliceObj B S hS U W).hom)

/-- The map of automorphism group algebraic spaces at a field-valued point `p` is an isomorphism
exactly when `f` is bijective on the vertical automorphism groups of all the chosen pullbacks of
`p` to the objects of the big fppf site of its field spectrum. -/
theorem isIso_pointAutomorphismSpaceMap_iff_forall (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    IsIso (pointAutomorphismSpaceMap B S hS f p) ↔
      ∀ W : (BigFppfOver B p.base.left.1 p.base.left.2)ᵒᵖ,
        Function.Bijective (automorphismGroupMap B S hS f
          (Functor.pullbackFiber 𝒳.val.val.p (Functor.Fiber.mk p.over)
            (sliceObj B S hS p.base W).hom).1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  refine forall_congr' fun W => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_isomSpaceMap_app_iff_bijective_automorphismGroupMap B S hS f p.base _ W

/-- **An isomorphism of automorphism group algebraic spaces at `p` gives the condition of
Stacks 0DTW at every object above `p`.** Any object `b` with a morphism `m : b ⟶ p` is
isomorphic to the chosen pullback of `p` along the morphism of the site underlying `m`, read as
an object of the site of the field spectrum, and bijectivity on vertical automorphism groups is
invariant under isomorphism. -/
theorem inducesIsomorphismAtObject_of_isIso_pointAutomorphismSpaceMap (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (h : IsIso (pointAutomorphismSpaceMap B S hS f p)) :
    InducesIsomorphismAtObject B S hS f p.obj := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have hall := (isIso_pointAutomorphismSpaceMap_iff_forall B S hS f p).1 h
  intro b m
  let t : 𝒳.val.val.p.obj b ⟶ p.base := 𝒳.val.val.p.map m ≫ eqToHom p.over
  have hm : 𝒳.val.val.p.IsHomLift t m := IsHomLift.of_fac' 𝒳.val.val.p t m rfl p.over (by simp [t])
  let W : (BigFppfOver B p.base.left.1 p.base.left.2)ᵒᵖ := Opposite.op (Over.mk t.left)
  let g := sliceObj B S hS p.base W
  let i : 𝒳.val.val.p.obj b ≅ g.left := Over.isoMk (Iso.refl _) (by
    show 𝟙 _ ≫ t.left ≫ p.base.hom = (𝒳.val.val.p.obj b).hom
    rw [Category.id_comp]
    exact Over.w t)
  have hfac : t = i.hom ≫ g.hom := by
    apply Over.OverMorphism.ext
    simp only [i, g, W, sliceObj, Over.comp_left]
    exact (Category.id_comp _).symm
  let c'' := Functor.IsPreFibered.pullbackMap (Functor.Fiber.mk p.over).2 g.hom
  have : 𝒳.val.val.p.IsStronglyCartesian g.hom c'' :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift g.hom c''
  let φ := @Functor.IsStronglyCartesian.map _ _ _ _ 𝒳.val.val.p _ _ _ _ g.hom c'' _ _ _ _ _
    hfac m hm
  have : 𝒳.val.val.p.IsHomLift i.hom φ :=
    @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ 𝒳.val.val.p _ _ _ _ g.hom c'' _ _ _ _ _
      hfac m hm
  have : 𝒳.val.val.p.IsStronglyCartesian i.hom φ :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift i.hom φ
  have : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p i.hom φ
  exact Functor.bijective_verticalAutMap_of_iso' _ _ (asIso φ) (hall W)

/-- **Stacks 0DTW through one representative.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
induces an isomorphism between automorphism groups at a point `q ∈ |𝒳|` as soon as the map
`G_x ⟶ G_{f ∘ x}` of automorphism group algebraic spaces is an isomorphism for one field-valued
representative `x` of `q`: by **Stacks 0DTV** it is then an isomorphism for every representative,
and at every representative it gives bijectivity on the vertical automorphism groups of every
object lying above it. -/
theorem inducesIsomorphismAt_of_isIso_pointAutomorphismSpaceMap (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (h : IsIso (pointAutomorphismSpaceMap B S hS f p)) :
    InducesIsomorphismAt B S hS f (pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p) :=
  (inducesIsomorphismAt_iff_forall_representatives B S hS f _).2 fun r hr =>
    inducesIsomorphismAtObject_of_isIso_pointAutomorphismSpaceMap B S hS f r
      ((exists_isIso_pointAutomorphismSpaceMap_iff_forall B S hS f _).1 ⟨p, rfl, h⟩ r hr)

/-- Conversely, the condition of Stacks 0DTW at every object above `p` makes the map of
automorphism group algebraic spaces at `p` an isomorphism: the chosen pullbacks of `p` lie above
`p`. -/
theorem isIso_pointAutomorphismSpaceMap_of_inducesIsomorphismAtObject (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val) (h : InducesIsomorphismAtObject B S hS f p.obj) :
    IsIso (pointAutomorphismSpaceMap B S hS f p) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  exact (isIso_pointAutomorphismSpaceMap_iff_forall B S hS f p).2 fun W =>
    h _ (Functor.IsPreFibered.pullbackMap (Functor.Fiber.mk p.over).2 _)

/-- **Stacks 0DTW at a representative.** A 1-morphism of algebraic stacks induces an isomorphism
between automorphism groups at the point of `|𝒳|` represented by `p` exactly when the map of
automorphism group algebraic spaces at `p` is an isomorphism. -/
theorem inducesIsomorphismAt_iff_isIso_pointAutomorphismSpaceMap (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    InducesIsomorphismAt B S hS f (pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p) ↔
      IsIso (pointAutomorphismSpaceMap B S hS f p) :=
  ⟨fun h => isIso_pointAutomorphismSpaceMap_of_inducesIsomorphismAtObject B S hS f p
      ((inducesIsomorphismAt_iff_forall_representatives B S hS f _).1 h p rfl),
    inducesIsomorphismAt_of_isIso_pointAutomorphismSpaceMap B S hS f p⟩

end AlgebraicGeometry.Stack

end

module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# 2-fibre products of algebraic spaces over an algebraic stack

Let `𝒳` be an algebraic stack over `S` and let `x : U ⟶ 𝒳`, `y : V ⟶ 𝒳` be 1-morphisms from
(the stacks attached to) algebraic spaces `U` and `V`. The 2-fibre product `U ×_{x, 𝒳, y} V` is an
algebraic space, and this file realizes it as a 2-commutative square of algebraic stacks whose
apex is the stack of an algebraic space `I` and whose legs are the stacks of morphisms of algebraic
spaces `p : I ⟶ U`, `q : I ⟶ V`, together with the universal property of that square read in the
category of algebraic spaces. This is the algebraic space `I' = U' ×_{x', 𝒳', x'} U'` used in the
proofs of Stacks 0CJW and 0CKG.

What makes the universal property readable on algebraic spaces is that the stacks of algebraic
spaces form a *locally discrete* full sub-2-category of the algebraic stacks: a 1-morphism between
two of them is the stack of a unique morphism of algebraic spaces
(`AlgebraicGeometry.Stack.algebraicSpaceStackFunctor_map_homMk_representingMap`,
`AlgebraicGeometry.Stack.algebraicSpaceStackFunctor_map_injective`), and two 1-morphisms into the
stack of an algebraic space joined by a 2-morphism are equal, the 2-morphism being unique
(`AlgebraicGeometry.Stack.eq_of_hom₂_algebraicSpaceStackFunctor_obj`,
`AlgebraicGeometry.Stack.subsingleton_hom₂_algebraicSpaceStackFunctor_obj`).

## Main results

* `AlgebraicGeometry.Stack.exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj`: a 2-fibre
  product of algebraic stacks which is representable by an algebraic space has a model in the
  2-category of algebraic stacks whose apex is the stack of that space.
* `AlgebraicGeometry.Stack.exists_isTwoFibreProduct_algebraicSpaceStackFunctor`: the 2-fibre
  product of two algebraic spaces over an algebraic stack is an algebraic space, with legs
  morphisms of algebraic spaces. The input is condition (8) of Stacks 045G for an algebraic stack.
* `AlgebraicGeometry.Stack.exists_lift_of_isTwoFibreProduct_algebraicSpaceStackFunctor` and
  `AlgebraicGeometry.Stack.hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor`: the
  existence and uniqueness halves of its universal property, for test objects that are algebraic
  spaces, with the filler compared along equalities of 1-morphisms.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.iso_hom_eq_eqToHom` and
  `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofEqToHom`: the bookkeeping, in an arbitrary strict
  bicategory, of pre-morphisms of 2-commutative squares whose comparison 2-cells are identities
  read along equalities.

## Implementation notes

The 2-cell computations are done in an arbitrary strict bicategory, where `rw` and `simp` apply,
and only instantiated in `AlgebraicGeometry.Stack.AlgebraicStacks`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory` for why rewriting fails there. The
equalities along which the fillers are compared are arguments (or universally quantified) rather
than built in the statements, so that no statement relies on the definitional unfolding of
`(algebraicSpaceStackFunctor B S hS).map (h ≫ p)`, which holds by `rfl` but is expensive to check.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0CJW](https://stacks.math.columbia.edu/tag/0CJW)
* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Bicategory

universe w₀ v₀ u₀

variable {𝔅 : Type u₀} [Bicategory.{w₀, v₀} 𝔅] {x y z : 𝔅} {f : x ⟶ z} {g : y ⟶ z}

/-- **A 2-commutative square transported along a 1-morphism into the apex.** Given a
2-commutative square `P`, a 1-morphism `k : t ⟶ P.pt` and two 1-morphisms `a : t ⟶ x`,
`b : t ⟶ y` identified with `k ≫ P.fst` and `k ≫ P.snd`, the square with apex `t`, legs `a`, `b`
and the filler of `P` carried along the two identifications. -/
def TwoCommSq.ofComparison (P : TwoCommSq f g) {t : 𝔅} (k : t ⟶ P.pt) {a : t ⟶ x}
    {b : t ⟶ y} (ea : a ≅ k ≫ P.fst) (eb : b ≅ k ≫ P.snd) : TwoCommSq f g where
  pt := t
  fst := a
  snd := b
  iso := whiskerRightIso ea f ≪≫ α_ k P.fst f ≪≫ whiskerLeftIso k P.iso ≪≫
    (α_ k P.snd g).symm ≪≫ whiskerRightIso eb.symm g

/-- The pre-morphism of squares from `TwoCommSq.ofComparison` to the square it was transported
from, on the 1-morphism `k`. -/
def TwoCommSq.PreHom.ofComparison (P : TwoCommSq f g) {t : 𝔅} (k : t ⟶ P.pt) {a : t ⟶ x}
    {b : t ⟶ y} (ea : a ≅ k ≫ P.fst) (eb : b ≅ k ≫ P.snd) :
    TwoCommSq.PreHom (P.ofComparison k ea eb) P where
  hom := k
  isoFst := ea
  isoSnd := eb
  compat := by
    change (ea.hom ▷ f ≫ (α_ k P.fst f).hom ≫ k ◁ P.iso.hom ≫ (α_ k P.snd g).inv ≫
      eb.inv ▷ g) ≫ eb.hom ▷ g ≫ (α_ k P.snd g).hom =
        ea.hom ▷ f ≫ (α_ k P.fst f).hom ≫ k ◁ P.iso.hom
    simp only [Category.assoc, inv_hom_whiskerRight_assoc, Iso.inv_hom_id, Category.comp_id]

section Strict

variable [Bicategory.Strict 𝔅]

/-- **The filler of a square mapping to another by eqToHom comparisons, in a strict bicategory.**
If the comparison 2-cells of a pre-morphism of squares `m : T ⟶ P` are identities read along
equalities `T.fst = m.hom ≫ P.fst` and `T.snd = m.hom ≫ P.snd`, then the filler of `T` is the
filler of `P` whiskered by `m.hom`, read along those equalities. -/
theorem TwoCommSq.PreHom.iso_hom_eq_eqToHom {T P : TwoCommSq f g} (m : TwoCommSq.PreHom T P)
    (ha : T.fst = m.hom ≫ P.fst) (hb : T.snd = m.hom ≫ P.snd)
    (hfst : m.isoFst.hom = eqToHom ha) (hsnd : m.isoSnd.hom = eqToHom hb) :
    T.iso.hom = eqToHom (by rw [ha, Strict.assoc]) ≫ (m.hom ◁ P.iso.hom) ≫
      eqToHom (by rw [hb, Strict.assoc]) := by
  have e₁ : m.isoFst = eqToIso ha := Iso.ext hfst
  have e₂ : m.isoSnd = eqToIso hb := Iso.ext hsnd
  have h := m.iso_hom_eq
  rw [e₁, e₂] at h
  simp only [eqToIso.inv, eqToHom_whiskerRight, Strict.associator_eqToIso, eqToIso.hom] at h
  rw [eqToHom_comp_iff] at h
  rw [h]
  simp only [eqToHom_trans, eqToHom_trans_assoc]

/-- **A pre-morphism of squares with eqToHom comparisons.** For two 1-morphisms `k, k'` into the
apex of a square `P` with `k ≫ P.fst = k' ≫ P.fst` and `k ≫ P.snd = k' ≫ P.snd`, and with the
filler of `P` whiskered by `k` equal to the one whiskered by `k'` along those equalities, `k'`
underlies a pre-morphism from the square `P` transported along `k`, with eqToHom comparisons. -/
def TwoCommSq.PreHom.ofEqToHom (P : TwoCommSq f g) {t : 𝔅} {k k' : t ⟶ P.pt}
    (hfst : k ≫ P.fst = k' ≫ P.fst) (hsnd : k ≫ P.snd = k' ≫ P.snd)
    (h : k ◁ P.iso.hom = eqToHom (by rw [← Strict.assoc, hfst, Strict.assoc]) ≫
      (k' ◁ P.iso.hom) ≫ eqToHom (by rw [← Strict.assoc, ← hsnd, Strict.assoc])) :
    TwoCommSq.PreHom (P.ofComparison k (Iso.refl _) (Iso.refl _)) P where
  hom := k'
  isoFst := eqToIso hfst
  isoSnd := eqToIso hsnd
  compat := by
    change ((Iso.refl (k ≫ P.fst)).hom ▷ f ≫ (α_ k P.fst f).hom ≫ k ◁ P.iso.hom ≫
      (α_ k P.snd g).inv ≫ (Iso.refl (k ≫ P.snd)).symm.hom ▷ g) ≫ (eqToIso hsnd).hom ▷ g ≫
        (α_ k' P.snd g).hom = (eqToIso hfst).hom ▷ f ≫ (α_ k' P.fst f).hom ≫ k' ◁ P.iso.hom
    simp only [Iso.refl_hom, Iso.refl_symm, id_whiskerRight, Category.id_comp, eqToIso.hom,
      eqToHom_whiskerRight, Strict.associator_eqToIso, eqToIso.inv, h, Category.assoc,
      eqToHom_trans, eqToHom_trans_assoc]
    simp

end Strict

end CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The functor from algebraic spaces to algebraic stacks is faithful.** -/
theorem algebraicSpaceStackFunctor_map_injective {X Y : AlgebraicSpaces B S hS} {f g : X ⟶ Y}
    (h : (algebraicSpaceStackFunctor.{u, w} B S hS).map f =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map g) : f = g := by
  have e := congrArg (fun φ => representingMap B S hS _ _ X.obj Y.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) φ.hom) h
  exact ObjectProperty.hom_ext _
    ((representingMap_associatedMap B S hS X.obj Y.obj f.hom).symm.trans
      (e.trans (representingMap_associatedMap B S hS X.obj Y.obj g.hom)))

/-- **Two 1-morphisms into the stack of an algebraic space joined by a 2-morphism are equal.** -/
theorem eq_of_hom₂_algebraicSpaceStackFunctor_obj {𝒯 : AlgebraicStacks.{u, w} B S hS}
    {Y : AlgebraicSpaces B S hS} {φ ψ : 𝒯 ⟶ (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y}
    (η : φ ⟶ ψ) : φ = ψ :=
  Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS η.hom)

/-- **A 2-morphism between two 1-morphisms into the stack of an algebraic space is unique.** -/
theorem subsingleton_hom₂_algebraicSpaceStackFunctor_obj {𝒯 : AlgebraicStacks.{u, w} B S hS}
    {Y : AlgebraicSpaces B S hS} (φ ψ : 𝒯 ⟶ (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y) :
    Subsingleton (φ ⟶ ψ) :=
  ⟨fun a b => Bicategory.InducedBicategory.hom₂_ext
    ((subsingleton_hom₂ B S hS φ.hom ψ.hom).elim a.hom b.hom)⟩

/-- **The functor from algebraic spaces to algebraic stacks is full**: a 1-morphism between the
stacks of two algebraic spaces is the image of the morphism of representing presheaves it
induces (Stacks 04SW). -/
theorem algebraicSpaceStackFunctor_map_homMk_representingMap {X Y : AlgebraicSpaces B S hS}
    (φ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map (ObjectProperty.homMk
      (representingMap B S hS _ _ X.obj Y.obj (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) φ.hom)) = φ := by
  let m : X.obj ⟶ Y.obj := representingMap B S hS _ _ X.obj Y.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) φ.hom
  obtain ⟨e⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS X.obj) (fibredCategory B S hS Y.obj) X.obj Y.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (f := (associatedMap B S hS m).1) (g := φ.hom)
    (representingMap_associatedMap B S hS X.obj Y.obj m)
  exact Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS e.default.hom)

/-- Every 1-morphism between the stacks of two algebraic spaces is the image of a morphism. -/
private theorem exists_map_eq {X Y : AlgebraicSpaces B S hS}
    (φ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).obj Y) :
    ∃ f : X ⟶ Y, (algebraicSpaceStackFunctor.{u, w} B S hS).map f = φ :=
  ⟨_, algebraicSpaceStackFunctor_map_homMk_representingMap φ⟩

/-- **A 2-fibre product of algebraic stacks represented by an algebraic space has a model with
the stack of that space as apex.** If the canonical 2-fibre product `𝒰 ×_{x, 𝒳, y} 𝒱` of a cospan
of algebraic stacks is representable by an algebraic space, then there are an algebraic space `I`,
1-morphisms `a : I ⟶ 𝒰`, `b : I ⟶ 𝒱` and a 2-isomorphism `γ : x ∘ a ≅ y ∘ b` exhibiting the stack
of `I` as a 2-fibre product of `x` and `y` in the 2-category of algebraic stacks. -/
theorem exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj
    {𝒰 𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (x : 𝒰 ⟶ 𝒳) (y : 𝒱 ⟶ 𝒳)
    (h : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} x.hom y.hom).pt) :
    ∃ (I : AlgebraicSpaces B S hS) (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj I ⟶ 𝒰)
      (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj I ⟶ 𝒱) (γ : a ≫ x ≅ b ≫ y),
      Nonempty (Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y)) := by
  let P0 := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} x.hom y.hom
  obtain ⟨F, hF, ⟨e⟩⟩ := h
  let I : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let k : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj I).val ⟶ P0.pt :=
    Bicategory.InducedBicategory.mkHom ⟨e.inv.functor, e.inv.w⟩
  let Q0 := P0.ofComparison k (Iso.refl (k ≫ P0.fst)) (Iso.refl (k ≫ P0.snd))
  let a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj I ⟶ 𝒰 :=
    Bicategory.InducedBicategory.mkHom (k ≫ P0.fst)
  let b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj I ⟶ 𝒱 :=
    Bicategory.InducedBicategory.mkHom (k ≫ P0.snd)
  let γ : a ≫ x ≅ b ≫ y := Bicategory.InducedBicategory.isoMk Q0.iso
  have hQ : Bicategory.IsTwoFibreProduct
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS ⟨_, _, _, γ⟩) :=
    Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        x.hom y.hom)
      (Bicategory.TwoCommSq.PreHom.ofComparison P0 k _ _)
      (inferInstanceAs e.toEquivalence.inverse.IsEquivalence)
  exact ⟨I, a, b, γ, ⟨AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids B S hS _ hQ⟩⟩

/-- **A 2-fibre product of two algebraic spaces over an algebraic stack is an algebraic space.**
For 1-morphisms `x : U ⟶ 𝒳` and `y : V ⟶ 𝒳` from algebraic spaces to an algebraic stack there
are an algebraic space `I`, morphisms `p : I ⟶ U`, `q : I ⟶ V` and a 2-isomorphism
`γ : x ∘ p ≅ y ∘ q` exhibiting `I` as the 2-fibre product `U ×_{x, 𝒳, y} V` in the 2-category of
algebraic stacks. The diagonal of `𝒳` is representable by algebraic spaces, so condition (8) of
Stacks 045G makes the canonical 2-fibre product representable by an algebraic space; the two legs
are then morphisms of algebraic spaces by
`AlgebraicGeometry.Stack.algebraicSpaceStackFunctor_map_homMk_representingMap`. -/
theorem exists_isTwoFibreProduct_algebraicSpaceStackFunctor
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V : AlgebraicSpaces B S hS}
    (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
    (y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒳) :
    ∃ (I : AlgebraicSpaces B S hS) (p : I ⟶ U) (q : I ⟶ V)
      (γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x ≅
        (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ y),
      Nonempty (Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y)) := by
  obtain ⟨I, a, b, γ, hγ⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj x y
    (hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal.{u, u, u + 1, u, u, u, u} B S hS 𝒳.val
      (SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj U).val
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj V).val
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U.obj U.property)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V.obj V.property)
      x.hom.hom y.hom.hom)
  obtain ⟨p, rfl⟩ := exists_map_eq a
  obtain ⟨q, rfl⟩ := exists_map_eq b
  exact ⟨I, p, q, γ, hγ⟩

section UniversalProperty

open Bicategory

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V I : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳}
  {y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒳} {p : I ⟶ U} {q : I ⟶ V}
  {γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x ≅
    (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ y}

/-- **The existence half of the universal property of a 2-fibre product of algebraic spaces.**
Let `I` with `p`, `q`, `γ` be a 2-fibre product of `x : U ⟶ 𝒳` and `y : V ⟶ 𝒳`. For morphisms
`a : T ⟶ U`, `b : T ⟶ V` of algebraic spaces and a 2-isomorphism `η : x ∘ a ≅ y ∘ b` there is a
morphism `h : T ⟶ I` with `p ∘ h = a`, `q ∘ h = b` and `η = h^*γ`, read along these equalities. -/
theorem exists_lift_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    (hP : Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y))
    {T : AlgebraicSpaces B S hS} (a : T ⟶ U) (b : T ⟶ V)
    (η : (algebraicSpaceStackFunctor.{u, w} B S hS).map a ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map b ≫ y) :
    ∃ h : T ⟶ I, h ≫ p = a ∧ h ≫ q = b ∧
      ∀ (e₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).map a ≫ x =
          (algebraicSpaceStackFunctor.{u, w} B S hS).map h ≫
            (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x)
        (e₂ : (algebraicSpaceStackFunctor.{u, w} B S hS).map h ≫
            (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ y =
          (algebraicSpaceStackFunctor.{u, w} B S hS).map b ≫ y),
        η.hom = eqToHom e₁ ≫ ((algebraicSpaceStackFunctor.{u, w} B S hS).map h ◁ γ.hom) ≫
          eqToHom e₂ := by
  obtain ⟨hom, isoFst, isoSnd, compat⟩ :=
    Bicategory.twoFibreProductPreHom hP ⟨_, _, _, η⟩
  obtain ⟨h, rfl⟩ := exists_map_eq hom
  have ha := eq_of_hom₂_algebraicSpaceStackFunctor_obj isoFst.hom
  have hb := eq_of_hom₂_algebraicSpaceStackFunctor_obj isoSnd.hom
  have key := Bicategory.TwoCommSq.PreHom.iso_hom_eq_eqToHom ⟨_, isoFst, isoSnd, compat⟩ ha hb
    ((subsingleton_hom₂_algebraicSpaceStackFunctor_obj _ _).elim _ _)
    ((subsingleton_hom₂_algebraicSpaceStackFunctor_obj _ _).elim _ _)
  exact ⟨h, algebraicSpaceStackFunctor_map_injective
      (((algebraicSpaceStackFunctor.{u, w} B S hS).map_comp h p).trans ha.symm),
    algebraicSpaceStackFunctor_map_injective
      (((algebraicSpaceStackFunctor.{u, w} B S hS).map_comp h q).trans hb.symm),
    fun _ _ => key⟩

/-- **The uniqueness half of the universal property of a 2-fibre product of algebraic spaces.**
Two morphisms `h, h' : T ⟶ I` into a 2-fibre product of algebraic spaces with `p ∘ h = p ∘ h'`,
`q ∘ h = q ∘ h'` and `h^*γ = h'^*γ` along these equalities are equal. -/
theorem hom_ext_of_isTwoFibreProduct_algebraicSpaceStackFunctor
    (hP : Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y))
    {T : AlgebraicSpaces B S hS} {h h' : T ⟶ I} (hp : h ≫ p = h' ≫ p) (hq : h ≫ q = h' ≫ q)
    (e₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).map h ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map h' ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x)
    (e₂ : (algebraicSpaceStackFunctor.{u, w} B S hS).map h' ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ y =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map h ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ y)
    (hγ : (algebraicSpaceStackFunctor.{u, w} B S hS).map h ◁ γ.hom =
      eqToHom e₁ ≫ ((algebraicSpaceStackFunctor.{u, w} B S hS).map h' ◁ γ.hom) ≫ eqToHom e₂) :
    h = h' := by
  let P : Bicategory.TwoCommSq x y := ⟨_, _, _, γ⟩
  have map_eq : ∀ {W : AlgebraicSpaces B S hS} (r : I ⟶ W), h ≫ r = h' ≫ r →
      (algebraicSpaceStackFunctor.{u, w} B S hS).map h ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map r =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map h' ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map r :=
    fun r e => by rw [← Functor.map_comp, ← Functor.map_comp, e]
  let m₂ := Bicategory.TwoCommSq.PreHom.ofEqToHom P (map_eq p hp) (map_eq q hq) hγ
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hP
    (Bicategory.TwoCommSq.PreHom.ofComparison P _ (Iso.refl _) (Iso.refl _)) m₂
  exact algebraicSpaceStackFunctor_map_injective (eq_of_hom₂_algebraicSpaceStackFunctor_obj
    (θ.hom : (algebraicSpaceStackFunctor.{u, w} B S hS).map h ⟶
      (algebraicSpaceStackFunctor.{u, w} B S hS).map h'))

end UniversalProperty

end AlgebraicGeometry.Stack

end

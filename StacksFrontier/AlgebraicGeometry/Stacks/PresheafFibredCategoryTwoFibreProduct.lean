module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# A cartesian square of presheaves gives a 2-cartesian square of the attached categories

Let `S` be a scheme of a big fppf site `B`. A set-valued presheaf on the big fppf site of `S`
has an attached category fibred in groupoids with discrete fibres,
`AlgebraicGeometry.Stack.fibredCategory`, and a map of presheaves has an attached 1-morphism,
`AlgebraicGeometry.Stack.associatedMap`. The attached construction carries a pullback square of
presheaves to a 2-fibre product square in the 2-category of categories fibred in groupoids over
the site.

## Main definitions

* `AlgebraicGeometry.Stack.basedFunctorOfSections`: the 1-morphism into the attached category
  named by a compatible family of elements.
* `AlgebraicGeometry.Stack.pullbackElement`: the element of the apex of a pullback square of
  presheaves determined by a compatible pair of elements of the two other corners.
* `AlgebraicGeometry.Stack.fibredCategorySquare`: the 2-commutative square attached to a
  commuting square of presheaves.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_fibredCategorySquare`: the attached square of a
  pullback square of presheaves is a 2-fibre product.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The universal property of the category attached to a presheaf -/

section Sections

variable {B S hS}
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The 1-morphism into the category attached to a presheaf `T` named by a compatible family `s`
of elements: an object `x` of `𝒳` goes to the pair of its base and the element `s x`, and a
morphism goes to the morphism of the site it lies over. -/
def basedFunctorOfSections
    (s : ∀ x : 𝒳.val.obj, T.obj (op (𝒳.val.p.obj x)))
    (hs : ∀ {x y : 𝒳.val.obj} (u : x ⟶ y), T.map (𝒳.val.p.map u).op (s y) = s x) :
    𝒳 ⟶ fibredCategory B S hS T := by
  let f : 𝒳.val.obj ⥤ (fibredCategory B S hS T).val.obj :=
    { obj x := ⟨𝒳.val.p.obj x, Discrete.mk (s x)⟩
      map {x y} u := { base := 𝒳.val.p.map u, fiber := Discrete.eqToHom (hs u).symm }
      map_id x := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
        · exact 𝒳.val.p.map_id x
        · apply Discrete.hom_eq
      map_comp u v := by
        refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
        · exact 𝒳.val.p.map_comp u v
        · apply Discrete.hom_eq }
  exact (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm ⟨f, rfl⟩

/-- The 1-morphism named by a compatible family of elements sends `x` to the pair of its base and
the element named there. -/
theorem basedFunctorOfSections_obj
    (s : ∀ x : 𝒳.val.obj, T.obj (op (𝒳.val.p.obj x)))
    (hs : ∀ {x y : 𝒳.val.obj} (u : x ⟶ y), T.map (𝒳.val.p.map u).op (s y) = s x)
    (x : 𝒳.val.obj) :
    (basedFunctorOfSections s hs).hom.obj x = ⟨𝒳.val.p.obj x, Discrete.mk (s x)⟩ :=
  rfl

/-- The family of elements named by the 1-morphism
`AlgebraicGeometry.Stack.basedFunctorOfSections s hs` is `s`. -/
theorem section_basedFunctorOfSections
    (s : ∀ x : 𝒳.val.obj, T.obj (op (𝒳.val.p.obj x)))
    (hs : ∀ {x y : 𝒳.val.obj} (u : x ⟶ y), T.map (𝒳.val.p.map u).op (s y) = s x)
    (x : 𝒳.val.obj) :
    sectionOfBasedFunctor (basedFunctorOfSections s hs).hom.toFunctor
      (basedFunctorOfSections s hs).hom.w x = s x :=
  rfl

/-- Postcomposing a 1-morphism into `fibredCategory F` with the 1-morphism attached to a map
`a : F ⟶ G'` of presheaves applies `a` to each element named. -/
theorem section_comp_associatedMap {F G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G')
    (f : 𝒳 ⟶ fibredCategory B S hS F) (x : 𝒳.val.obj) :
    sectionOfBasedFunctor (f ≫ (associatedMap B S hS a).1).hom.toFunctor
        (f ≫ (associatedMap B S hS a).1).hom.w x =
      a.app (op (𝒳.val.p.obj x)) (sectionOfBasedFunctor f.hom.toFunctor f.hom.w x) := by
  have h1 : (f ≫ (associatedMap B S hS a).1).hom.obj x =
      (⟨𝒳.val.p.obj x, Discrete.mk (a.app (op (𝒳.val.p.obj x))
        (sectionOfBasedFunctor f.hom.toFunctor f.hom.w x))⟩ :
        (fibredCategory B S hS G').val.obj) := by
    show (associatedMap B S hS a).1.hom.obj (f.hom.obj x) = _
    rw [associatedMap_obj, obj_eq_mk_section B S hS f x]
  exact (elementOf_congr _ rfl h1).trans (elementOf_mk G' _ _)

end Sections

/-! ### Elements of the apex of a pullback square of presheaves -/

section Elements

variable {B S hS}
variable {F G H T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {p : T ⟶ F} {q : T ⟶ G} {a : F ⟶ H} {b : G ⟶ H}

/-- A pullback square of presheaves is a pullback square of sets over every object of the
site. -/
theorem isPullback_app (h : IsPullback p q a b) (U : (BigFppfOver B S hS)ᵒᵖ) :
    IsPullback (p.app U) (q.app U) (a.app U) (b.app U) :=
  h.map ((evaluation _ _).obj U)

/-- The element of the apex of a pullback square of presheaves determined by a compatible pair of
elements `f` and `g` of the two other corners. -/
noncomputable def pullbackElement (h : IsPullback p q a b) {U : (BigFppfOver B S hS)ᵒᵖ}
    (f : F.obj U) (g : G.obj U) (hfg : a.app U f = b.app U g) : T.obj U :=
  (isPullback_app h U).lift (↾fun _ : PUnit.{u + 1} => f) (↾fun _ => g)
    (by ext _; exact hfg) PUnit.unit

/-- Two elements of a type are equal if the constant maps from `PUnit` they define are equal. -/
private theorem eq_of_ofHom_const_eq {X : Type u} {x y : X}
    (h : (↾fun _ : PUnit.{u + 1} => x : PUnit.{u + 1} ⟶ X) =
      ↾fun _ => y) : x = y := by
  simpa only [TypeCat.homEquiv_apply, TypeCat.ofHom_apply, TypeCat.Fun.toFun_apply] using
    congrFun (congrArg (fun z => TypeCat.homEquiv z) h) PUnit.unit

/-- The first coordinate of `AlgebraicGeometry.Stack.pullbackElement` is the element it was built
from. -/
theorem pullbackElement_fst (h : IsPullback p q a b) {U : (BigFppfOver B S hS)ᵒᵖ}
    (f : F.obj U) (g : G.obj U) (hfg : a.app U f = b.app U g) :
    p.app U (pullbackElement h f g hfg) = f := by
  exact eq_of_ofHom_const_eq ((isPullback_app h U).lift_fst _ _ (by ext _; exact hfg))

/-- The second coordinate of `AlgebraicGeometry.Stack.pullbackElement` is the element it was built
from. -/
theorem pullbackElement_snd (h : IsPullback p q a b) {U : (BigFppfOver B S hS)ᵒᵖ}
    (f : F.obj U) (g : G.obj U) (hfg : a.app U f = b.app U g) :
    q.app U (pullbackElement h f g hfg) = g := by
  exact eq_of_ofHom_const_eq ((isPullback_app h U).lift_snd _ _ (by ext _; exact hfg))

/-- An element of the apex of a pullback square of presheaves is determined by its two
coordinates. -/
theorem element_ext (h : IsPullback p q a b) {U : (BigFppfOver B S hS)ᵒᵖ} {t t' : T.obj U}
    (h₁ : p.app U t = p.app U t') (h₂ : q.app U t = q.app U t') : t = t' := by
  exact eq_of_ofHom_const_eq
    ((isPullback_app h U).hom_ext (by ext _; exact h₁) (by ext _; exact h₂))

end Elements

/-! ### The attached square -/

section Square

variable {B S hS}
variable {F G H T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {p : T ⟶ F} {q : T ⟶ G} {a : F ⟶ H} {b : G ⟶ H}

/-- The 2-commutative square attached to a commuting square of presheaves: its apex is the
category attached to the apex presheaf, its two legs are the 1-morphisms attached to the two
projections, and its filler is an `eqToIso`. -/
def fibredCategorySquare (hcomm : p ≫ a = q ≫ b) :
    Bicategory.TwoCommSq (associatedMap B S hS a).1 (associatedMap B S hS b).1 where
  pt := fibredCategory B S hS T
  fst := (associatedMap B S hS p).1
  snd := (associatedMap B S hS q).1
  iso := eqToIso (by rw [← associatedMap_comp, ← associatedMap_comp, hcomm])

/-- The square attached to a pullback square of presheaves is a 2-fibre product, that is, a
terminal object of the category of 2-commutative squares over the attached cospan. -/
noncomputable def isTwoFibreProduct_fibredCategorySquare (h : IsPullback p q a b) :
    Bicategory.IsTwoFibreProduct (fibredCategorySquare h.w) := by
  have mk : ∀ P : Bicategory.TwoCommSq (associatedMap B S hS a).1 (associatedMap B S hS b).1,
      Bicategory.TwoCommSq.PreHom P (fibredCategorySquare h.w) := by
    intro P
    have hP : P.fst ≫ (associatedMap B S hS a).1 = P.snd ≫ (associatedMap B S hS b).1 :=
      hom_eq_of_hom₂ B S hS P.iso.hom
    have key : ∀ x : P.pt.val.obj,
        a.app (op (P.pt.val.p.obj x))
            (sectionOfBasedFunctor P.fst.hom.toFunctor P.fst.hom.w x) =
          b.app (op (P.pt.val.p.obj x))
            (sectionOfBasedFunctor P.snd.hom.toFunctor P.snd.hom.w x) := by
      intro x
      rw [← section_comp_associatedMap a P.fst x, ← section_comp_associatedMap b P.snd x]
      exact sectionOfBasedFunctor_congr
        (P.fst ≫ (associatedMap B S hS a).1).hom.toFunctor
        (P.snd ≫ (associatedMap B S hS b).1).hom.toFunctor
        (P.fst ≫ (associatedMap B S hS a).1).hom.w
        (P.snd ≫ (associatedMap B S hS b).1).hom.w (by rw [hP])
    have hpT : ∀ x : P.pt.val.obj, p.app (op (P.pt.val.p.obj x))
        (pullbackElement h _ _ (key x)) =
          sectionOfBasedFunctor P.fst.hom.toFunctor P.fst.hom.w x := fun x =>
      pullbackElement_fst h _ _ (key x)
    have hqT : ∀ x : P.pt.val.obj, q.app (op (P.pt.val.p.obj x))
        (pullbackElement h _ _ (key x)) =
          sectionOfBasedFunctor P.snd.hom.toFunctor P.snd.hom.w x := fun x =>
      pullbackElement_snd h _ _ (key x)
    have hsTmap : ∀ {x y : P.pt.val.obj} (u : x ⟶ y),
        T.map (P.pt.val.p.map u).op (pullbackElement h _ _ (key y)) =
          pullbackElement h _ _ (key x) := by
      intro x y u
      refine element_ext h ?_ ?_
      · rw [NatTrans.naturality_apply p (P.pt.val.p.map u).op (pullbackElement h _ _ (key y)),
          hpT, hpT]
        exact sectionOfBasedFunctor_map P.fst.hom.toFunctor P.fst.hom.w u
      · rw [NatTrans.naturality_apply q (P.pt.val.p.map u).op (pullbackElement h _ _ (key y)),
          hqT, hqT]
        exact sectionOfBasedFunctor_map P.snd.hom.toFunctor P.snd.hom.w u
    refine ⟨basedFunctorOfSections (fun x => pullbackElement h _ _ (key x)) hsTmap,
      eqToIso ?_, eqToIso ?_, (subsingleton_hom₂ B S hS _ _).elim _ _⟩
    · refine hom_ext_of_section B S hS P.fst
        (basedFunctorOfSections (fun x => pullbackElement h _ _ (key x)) hsTmap ≫
          (associatedMap B S hS p).1) fun x => ?_
      rw [section_comp_associatedMap p
        (basedFunctorOfSections (fun x => pullbackElement h _ _ (key x)) hsTmap) x,
        section_basedFunctorOfSections]
      exact (hpT x).symm
    · refine hom_ext_of_section B S hS P.snd
        (basedFunctorOfSections (fun x => pullbackElement h _ _ (key x)) hsTmap ≫
          (associatedMap B S hS q).1) fun x => ?_
      rw [section_comp_associatedMap q
        (basedFunctorOfSections (fun x => pullbackElement h _ _ (key x)) hsTmap) x,
        section_basedFunctorOfSections]
      exact (hqT x).symm
  refine IsTerminal.ofUniqueHom (fun P => Quotient.mk _ (mk P)) fun P A => ?_
  induction A using Quotient.inductionOn with
  | h A =>
    refine (Quotient.sound ?_).symm
    have h₁ : (mk P).hom ≫ (associatedMap B S hS p).1 = A.hom ≫ (associatedMap B S hS p).1 :=
      (hom_eq_of_hom₂ B S hS (mk P).isoFst.hom).symm.trans (hom_eq_of_hom₂ B S hS A.isoFst.hom)
    have h₂ : (mk P).hom ≫ (associatedMap B S hS q).1 = A.hom ≫ (associatedMap B S hS q).1 :=
      (hom_eq_of_hom₂ B S hS (mk P).isoSnd.hom).symm.trans (hom_eq_of_hom₂ B S hS A.isoSnd.hom)
    have hhom : (mk P).hom = A.hom := by
      refine hom_ext_of_section B S hS _ _ fun x => ?_
      refine element_ext h ?_ ?_
      · rw [← section_comp_associatedMap p (mk P).hom x, ← section_comp_associatedMap p A.hom x]
        exact sectionOfBasedFunctor_congr
          ((mk P).hom ≫ (associatedMap B S hS p).1).hom.toFunctor
          (A.hom ≫ (associatedMap B S hS p).1).hom.toFunctor
          ((mk P).hom ≫ (associatedMap B S hS p).1).hom.w
          (A.hom ≫ (associatedMap B S hS p).1).hom.w (by rw [h₁])
      · rw [← section_comp_associatedMap q (mk P).hom x, ← section_comp_associatedMap q A.hom x]
        exact sectionOfBasedFunctor_congr
          ((mk P).hom ≫ (associatedMap B S hS q).1).hom.toFunctor
          (A.hom ≫ (associatedMap B S hS q).1).hom.toFunctor
          ((mk P).hom ≫ (associatedMap B S hS q).1).hom.w
          (A.hom ≫ (associatedMap B S hS q).1).hom.w (by rw [h₂])
    exact ⟨eqToIso hhom, (subsingleton_hom₂ B S hS _ _).elim _ _,
      (subsingleton_hom₂ B S hS _ _).elim _ _⟩

end Square

end AlgebraicGeometry.Stack

end

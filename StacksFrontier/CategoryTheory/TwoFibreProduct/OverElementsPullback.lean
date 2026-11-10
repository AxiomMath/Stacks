module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of elements of a fibre product of presheaves of sets

For a presheaf of sets `F` on a category `C`, the category `𝒮_F` of Stacks 04TM has objects the
pairs `(U, x)` with `x ∈ F(U)`; it is `(F.Elements)ᵒᵖ`, with structure functor
`(Functor.Elements.π F).leftOp` to `C`, and a map of presheaves `α : F ⟶ H` induces the
1-morphism `(NatTrans.mapElements α).op` over `C`.

This file shows that `F ↦ 𝒮_F` turns fibre products of presheaves into 2-fibre products over `C`
(Stacks 0040, `CategoryTheory.TwoFibreProductOver`):

* for a pullback square `P = F ×_H G` of presheaves, the comparison functor
  `𝒮_P ⥤ 𝒮_F ×_{𝒮_H} 𝒮_G` is an equivalence, strictly over `C` and strictly compatible with
  the two projections;
* for a product `P = F × G` of presheaves, the comparison functor `𝒮_P ⥤ 𝒮_F ×_C 𝒮_G`, the
  2-fibre product over `C` taken along the two structure functors and the identity of `C`, is
  an equivalence, with the same compatibilities.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.ElementsPullback`: the 2-fibre product `𝒮_F ×_{𝒮_H} 𝒮_G`.
* `CategoryTheory.TwoFibreProductOver.elementsPullback`: the comparison functor out of `𝒮_P`.
* `CategoryTheory.TwoFibreProductOver.ElementsProd`: the 2-fibre product `𝒮_F ×_C 𝒮_G`.
* `CategoryTheory.TwoFibreProductOver.elementsProd`: the comparison functor out of `𝒮_P`.

## Main results

* `CategoryTheory.TwoFibreProductOver.instIsEquivalenceElementsPullback` and
  `CategoryTheory.TwoFibreProductOver.isEquivalence_elementsProd`: the two comparison
  functors are equivalences.

## Implementation notes

The fibre categories of `𝒮_F`, `𝒮_G` and `𝒮_H` have only identity morphisms, so a morphism of
`𝒮_H` is determined by the morphism of `C` underneath it (`Functor.Elements.hom_ext`); the
comparison isomorphism of an object of the 2-fibre product, being vertical, lies over an
identity and is therefore forced. That is why the comparison functor can put the element
isomorphism over `Iso.refl` in that field, and why essential surjectivity needs nothing beyond
the pointwise description of a pullback of sets
(`CategoryTheory.Limits.Types.exists_of_isPullback`).
As in `CategoryTheory.TwoFibreProductOver.instIsEquivalenceSlicePullback`, equivalence is proved by
fully faithful plus essentially surjective.

## References

* [Stacks Project, Tag 04SU](https://stacks.math.columbia.edu/tag/04SU)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver

universe w v u

attribute [local implicit_reducible] fst snd structureFunctor

variable {C : Type u} [Category.{v} C] {F G H P : Cᵒᵖ ⥤ Type w}

section Pullback

variable (α : F ⟶ H) (β : G ⟶ H)

/-- The 2-fibre product `𝒮_F ×_{𝒮_H} 𝒮_G` over `C` of the categories of elements of two
presheaves of sets over a third one, along the 1-morphisms induced by `α` and `β`. -/
abbrev ElementsPullback : Type _ :=
  TwoFibreProductOver (Functor.Elements.π F).leftOp (Functor.Elements.π G).leftOp
    (Functor.Elements.π H).leftOp (NatTrans.mapElements α).op (NatTrans.mapElements β).op

variable {α β} {pF : P ⟶ F} {pG : P ⟶ G}

/-- The comparison isomorphism of the image of `z ∈ P(U)` in `𝒮_F ×_{𝒮_H} 𝒮_G`: the element
isomorphism over the identity of `U` between `β(pG z)` and `α(pF z)`, which agree because the
square commutes. -/
def elementsPullbackIso (w : pF ≫ α = pG ≫ β) (X : P.Elementsᵒᵖ) :
    (NatTrans.mapElements α).op.obj ((NatTrans.mapElements pF).op.obj X) ≅
      (NatTrans.mapElements β).op.obj ((NatTrans.mapElements pG).op.obj X) :=
  (Functor.Elements.isoMk
    (x := (NatTrans.mapElements β).obj ((NatTrans.mapElements pG).obj X.unop))
    (y := (NatTrans.mapElements α).obj ((NatTrans.mapElements pF).obj X.unop)) (Iso.refl _) (by
      simpa using (ConcreteCategory.congr_hom (NatTrans.congr_app w X.unop.1) X.unop.2).symm)).op

variable (h : IsPullback pF pG α β)

/-- The comparison functor `𝒮_P ⥤ 𝒮_F ×_{𝒮_H} 𝒮_G` attached to a pullback square of presheaves
of sets: an element `z ∈ P(U)` goes to the pair of its two images, with the identity of `U` as
comparison isomorphism. -/
@[simps! obj_base obj_x obj_y map_hbase map_a map_b]
def elementsPullback : P.Elementsᵒᵖ ⥤ ElementsPullback α β where
  obj X :=
    { base := X.unop.1.unop
      x := (NatTrans.mapElements pF).op.obj X
      y := (NatTrans.mapElements pG).op.obj X
      hx := rfl
      hy := rfl
      iso := elementsPullbackIso h.w X
      vertical := IsHomLift.of_fac' _ _ _ rfl rfl (by simp [elementsPullbackIso]) }
  map {X Y} f :=
    { hbase := (Functor.Elements.π P).leftOp.map f
      a := (NatTrans.mapElements pF).op.map f
      b := (NatTrans.mapElements pG).op.map f
      ha := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      hb := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      w := by
        apply Quiver.Hom.unop_inj
        ext
        simp [elementsPullbackIso] }
  map_id X := by
    refine Hom.ext' ?_ ?_ <;> rfl
  map_comp f g := by
    refine Hom.ext' ?_ ?_ <;> rfl

/-- The comparison functor is strictly a 1-morphism of categories over `C`. -/
theorem elementsPullback_comp_structureFunctor :
    elementsPullback h ⋙ structureFunctor _ _ _ _ _ = (Functor.Elements.π P).leftOp := rfl

/-- The comparison functor followed by the first projection is the 1-morphism induced by the
first projection of the pullback. -/
theorem elementsPullback_comp_fst :
    elementsPullback h ⋙ fst _ _ _ _ _ = (NatTrans.mapElements pF).op := rfl

/-- The comparison functor followed by the second projection is the 1-morphism induced by the
second projection of the pullback. -/
theorem elementsPullback_comp_snd :
    elementsPullback h ⋙ snd _ _ _ _ _ = (NatTrans.mapElements pG).op := rfl

/-- The comparison functor out of the category of elements of a pullback is faithful. -/
instance : (elementsPullback h).Faithful where
  map_injective {X Y} {f g} hfg := by
    have hb : ((elementsPullback h).map f).hbase = ((elementsPullback h).map g).hbase := by
      rw [hfg]
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op hb

/-- The comparison functor out of the category of elements of a pullback is full. -/
instance : (elementsPullback h).Full where
  map_surjective {X Y} φ := by
    have ha : φ.a.unop.1 = φ.hbase.op := congrArg Quiver.Hom.op
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (Functor.Elements.π F).leftOp
        ((NatTrans.mapElements pF).op.obj X) ((NatTrans.mapElements pF).op.obj Y)
        φ.hbase φ.a φ.ha).symm
    have hb : φ.b.unop.1 = φ.hbase.op := congrArg Quiver.Hom.op
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (Functor.Elements.π G).leftOp
        ((NatTrans.mapElements pG).op.obj X) ((NatTrans.mapElements pG).op.obj Y)
        φ.hbase φ.b φ.hb).symm
    have hu : P.map φ.hbase.op Y.unop.2 = X.unop.2 := by
      refine Types.ext_of_isPullback (h.app X.unop.1) ?_ ?_
      · refine (NatTrans.naturality_apply pF φ.hbase.op Y.unop.2).trans ?_
        rw [← ha]
        exact φ.a.unop.2
      · refine (NatTrans.naturality_apply pG φ.hbase.op Y.unop.2).trans ?_
        rw [← hb]
        exact φ.b.unop.2
    refine ⟨Quiver.Hom.op ⟨φ.hbase.op, hu⟩, ?_⟩
    refine Hom.ext' ?_ ?_ <;> apply Quiver.Hom.unop_inj <;> apply Functor.Elements.hom_ext
    · exact ha.symm
    · exact hb.symm

/-- The comparison functor out of the category of elements of a pullback is essentially
surjective. -/
instance : (elementsPullback h).EssSurj where
  mem_essImage Q := by
    obtain ⟨base, ⟨x⟩, ⟨y⟩, hx, hy, i, hi⟩ := Q
    obtain @⟨c, s⟩ := x
    obtain @⟨c', t⟩ := y
    obtain ⟨U⟩ := c
    obtain ⟨U'⟩ := c'
    change U = base at hx
    subst hx
    change U' = U at hy
    subst hy
    have hval : i.hom.unop.1 = 𝟙 (op U') := congrArg Quiver.Hom.op
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (Functor.Elements.π H).leftOp
        ((NatTrans.mapElements α).op.obj (op (Functor.elementsMk _ (op U') s)))
        ((NatTrans.mapElements β).op.obj (op (Functor.elementsMk _ (op U') t))) (𝟙 U') i.hom
        hi).symm
    have hst : α.app (op U') s = β.app (op U') t := by
      have h₂ : H.map i.hom.unop.1 (β.app (op U') t) = α.app (op U') s := i.hom.unop.2
      rw [hval] at h₂
      simpa using h₂.symm
    obtain ⟨z, rfl, rfl⟩ := Types.exists_of_isPullback (h.app (op U')) s t hst
    refine ⟨op (Functor.elementsMk _ (op U') z), ⟨isoMkVertical (U := U') (Iso.refl _) (Iso.refl _)
      (IsHomLift.id rfl) (IsHomLift.id rfl) ?_⟩⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    change i.hom.unop.1 ≫ 𝟙 (op U') = 𝟙 (op U') ≫ 𝟙 (op U')
    rw [hval]

/-- **The category of elements of a fibre product of presheaves of sets is the 2-fibre product
of the categories of elements.** -/
instance instIsEquivalenceElementsPullback : (elementsPullback h).IsEquivalence :=
  Functor.IsEquivalence.mk

end Pullback

section Product

variable (F G) in
/-- The 2-fibre product `𝒮_F ×_C 𝒮_G` over `C` of the categories of elements of two presheaves of
sets, taken along their two structure functors and the identity of `C`. -/
abbrev ElementsProd : Type _ :=
  TwoFibreProductOver (Functor.Elements.π F).leftOp (Functor.Elements.π G).leftOp (𝟭 C)
    (Functor.Elements.π F).leftOp (Functor.Elements.π G).leftOp

variable {pF : P ⟶ F} {pG : P ⟶ G}

/-- At every object of `C`, a product of presheaves of sets is a product of sets, written as a
pullback over the terminal set. -/
@[sga "3 I 1.2" "partial, special case"]
theorem isPullback_app_of_isLimit_binaryFan (h : IsLimit (BinaryFan.mk pF pG)) (U : Cᵒᵖ) :
    IsPullback (pF.app U) (pG.app U) (Limits.Types.isTerminalPUnit.from _)
      (Limits.Types.isTerminalPUnit.from _) :=
  IsPullback.of_is_product'
    (mapIsLimitOfPreservesOfIsLimit ((evaluation Cᵒᵖ (Type w)).obj U) pF pG h)
    Limits.Types.isTerminalPUnit

variable (pF pG) in
/-- The comparison functor `𝒮_P ⥤ 𝒮_F ×_C 𝒮_G` attached to a product of presheaves of sets: an
element `z ∈ P(U)` goes to the pair of its two components, with the identity of `U` as
comparison isomorphism. -/
@[simps! obj_base obj_x obj_y map_hbase map_a map_b]
def elementsProd : P.Elementsᵒᵖ ⥤ ElementsProd F G where
  obj X :=
    { base := X.unop.1.unop
      x := (NatTrans.mapElements pF).op.obj X
      y := (NatTrans.mapElements pG).op.obj X
      hx := rfl
      hy := rfl
      iso := Iso.refl _
      vertical := IsHomLift.id rfl }
  map {X Y} f :=
    { hbase := (Functor.Elements.π P).leftOp.map f
      a := (NatTrans.mapElements pF).op.map f
      b := (NatTrans.mapElements pG).op.map f
      ha := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      hb := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      w := (Category.comp_id _).trans (Category.id_comp _).symm }
  map_id X := by
    refine Hom.ext' ?_ ?_ <;> rfl
  map_comp f g := by
    refine Hom.ext' ?_ ?_ <;> rfl

/-- The comparison functor is strictly a 1-morphism of categories over `C`. -/
theorem elementsProd_comp_structureFunctor :
    elementsProd pF pG ⋙ structureFunctor _ _ _ _ _ = (Functor.Elements.π P).leftOp := rfl

/-- The comparison functor followed by the first projection is the 1-morphism induced by the
first projection of the product. -/
theorem elementsProd_comp_fst :
    elementsProd pF pG ⋙ fst _ _ _ _ _ = (NatTrans.mapElements pF).op := rfl

/-- The comparison functor followed by the second projection is the 1-morphism induced by the
second projection of the product. -/
theorem elementsProd_comp_snd :
    elementsProd pF pG ⋙ snd _ _ _ _ _ = (NatTrans.mapElements pG).op := rfl

/-- The comparison functor out of the category of elements of a product is faithful. -/
instance : (elementsProd pF pG).Faithful where
  map_injective {X Y} {f g} hfg := by
    have hb : ((elementsProd pF pG).map f).hbase = ((elementsProd pF pG).map g).hbase := by
      rw [hfg]
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op hb

variable (h : IsLimit (BinaryFan.mk pF pG))
include h

/-- The comparison functor out of the category of elements of a product is full. -/
theorem full_elementsProd : (elementsProd pF pG).Full where
  map_surjective {X Y} φ := by
    have ha : φ.a.unop.1 = φ.hbase.op := congrArg Quiver.Hom.op
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (Functor.Elements.π F).leftOp
        ((NatTrans.mapElements pF).op.obj X) ((NatTrans.mapElements pF).op.obj Y)
        φ.hbase φ.a φ.ha).symm
    have hb : φ.b.unop.1 = φ.hbase.op := congrArg Quiver.Hom.op
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (Functor.Elements.π G).leftOp
        ((NatTrans.mapElements pG).op.obj X) ((NatTrans.mapElements pG).op.obj Y)
        φ.hbase φ.b φ.hb).symm
    have hu : P.map φ.hbase.op Y.unop.2 = X.unop.2 := by
      refine Types.ext_of_isPullback (isPullback_app_of_isLimit_binaryFan h X.unop.1) ?_ ?_
      · refine (NatTrans.naturality_apply pF φ.hbase.op Y.unop.2).trans ?_
        rw [← ha]
        exact φ.a.unop.2
      · refine (NatTrans.naturality_apply pG φ.hbase.op Y.unop.2).trans ?_
        rw [← hb]
        exact φ.b.unop.2
    refine ⟨Quiver.Hom.op ⟨φ.hbase.op, hu⟩, ?_⟩
    refine Hom.ext' ?_ ?_ <;> apply Quiver.Hom.unop_inj <;> apply Functor.Elements.hom_ext
    · exact ha.symm
    · exact hb.symm

/-- The comparison functor out of the category of elements of a product is essentially
surjective. -/
theorem essSurj_elementsProd : (elementsProd pF pG).EssSurj where
  mem_essImage Q := by
    obtain ⟨base, ⟨x⟩, ⟨y⟩, hx, hy, i, hi⟩ := Q
    obtain @⟨c, s⟩ := x
    obtain @⟨c', t⟩ := y
    obtain ⟨U⟩ := c
    obtain ⟨U'⟩ := c'
    change U = base at hx
    subst hx
    change U' = U at hy
    subst hy
    have hval : 𝟙 U' = i.hom :=
      @IsHomLift.eq_of_isHomLift _ _ _ _ (𝟭 C) U' U' (𝟙 U') i.hom hi
    obtain ⟨z, rfl, rfl⟩ :=
      Types.exists_of_isPullback (isPullback_app_of_isLimit_binaryFan h (op U')) s t rfl
    refine ⟨op (Functor.elementsMk _ (op U') z), ⟨isoMkVertical (U := U') (Iso.refl _) (Iso.refl _)
      (IsHomLift.id rfl) (IsHomLift.id rfl) ?_⟩⟩
    change 𝟙 U' ≫ i.hom = 𝟙 U' ≫ 𝟙 U'
    rw [← hval]

/-- **The category of elements of a product of presheaves of sets is the product over `C` of the
categories of elements.** -/
theorem isEquivalence_elementsProd : (elementsProd pF pG).IsEquivalence :=
  have := full_elementsProd h
  have := essSurj_elementsProd h
  Functor.IsEquivalence.mk

end Product

end CategoryTheory.TwoFibreProductOver

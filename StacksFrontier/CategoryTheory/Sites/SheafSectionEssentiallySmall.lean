module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local sections as morphisms out of a sheafified representable, on an essentially small site

A section over `U` of a sheaf of sets `M` is the same thing as a morphism `h_U^# ⟶ M` out of the
sheafification of the presheaf represented by `U`: Yoneda's lemma composed with the universal
property of sheafification. The usual statement of this identification,
`Stacks.Sheaves.GradedAlgebraPushforward.sheafSectionEquiv`, asks for a site
`C : Type u` with `Category.{u} C` — objects *and* morphisms in one and the same universe — and
for `M : Sheaf J (Type u)`. The small étale site of an algebraic space has objects in
`Type (u + 1)` and morphisms in `Type u`, and `AlgebraicGeometry.Space.smallEtaleRingedTopos` is
accordingly a `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, whose topos of sheaves of sets is
`Sheaf J (Type u)`.

This file states the identification at `C : Type u₁` with `Category.{v} C` and
`M : Sheaf J (Type v)`, which covers that site. Two separate facts make the restriction
unnecessary.

* `CategoryTheory.yonedaEquiv` itself places no relation between the two universes: a morphism
  `yoneda.obj U ⟶ F` for `F : Cᵒᵖ ⥤ Type v` is a `Type v`-valued datum however large the objects
  of `C` are.
* What genuinely fails is the *existence of sheafification* at the smaller universe. Mathlib's
  instance is `HasSheafify J (Type (max u₁ v))`, which at `u₁ = v` is the needed
  `HasSheafify J (Type v)` and at `u₁ = v + 1` is not. Essential smallness of the site supplies
  it: `Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall`, from Mathlib's
  `CategoryTheory.hasSheafifyEssentiallySmallSite`.

So the hypothesis is exactly `HasWeakSheafify J (Type v)`, which is a prerequisite for the
statement to be well formed at all — `presheafToSheaf` does not exist without it — and essential
smallness is what discharges it.

A second form is given for a sheaf universe `m` unrelated to the universe `v` of the morphisms of
the site. There `yoneda.obj U` is not a `Type m`-valued presheaf and cannot be sheafified into
`Sheaf J (Type m)`; what replaces it is `Stacks.Sites.SheafSection.smallYoneda`, the sectionwise
`m`-small model `Y ↦ Shrink.{m} (Y ⟶ U)` of the representable presheaf, which exists precisely
because an essentially `m`-small site is locally `m`-small.

## Main definitions

* `Stacks.Sites.SheafSection.sectionEquiv`: the identification
  `M.obj.obj U ≃ ((presheafToSheaf J (Type v)).obj (yoneda.obj U.unop) ⟶ M)` for
  `C : Type u₁` with `Category.{v} C`, with no relation between `u₁` and `v`.
* `Stacks.Sites.SheafSection.OfEssentiallySmall.sheafSectionEquiv`: the same identification with
  the sheafification hypothesis discharged by `EssentiallySmall.{v} C`.
* `Stacks.Sites.SheafSection.smallYoneda` and
  `Stacks.Sites.SheafSection.smallYonedaEquiv`: the sectionwise `m`-small model of a
  representable presheaf on a locally `m`-small site, and Yoneda's lemma for it.
* `Stacks.Sites.SheafSection.sectionEquivSmall` and
  `Stacks.Sites.SheafSection.OfEssentiallySmall.sheafSectionEquivSmall`: the identification at a
  sheaf universe `m` unrelated to the universes of the site.

## Main results

* `Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall`: an essentially `m`-small site
  has sheafification of presheaves of sets with sections in `Type m`. This is the whole content;
  the identification itself is Yoneda's lemma composed with an adjunction.
* `Stacks.Sites.SheafSection.sectionEquiv_comp` and
  `Stacks.Sites.SheafSection.sectionEquiv_map`: the identification is natural in the sheaf and in
  the object, and likewise `Stacks.Sites.SheafSection.sectionEquivSmall_comp`.

## Implementation notes

`hasSheafify_type_of_essentiallySmall` is a theorem and not an instance, following Mathlib's
`CategoryTheory.hasSheafifyEssentiallySmallSite`: its own hypothesis is a `HasSheafify` for the
induced topology on the small model, so as an instance it would be searched recursively against
itself. The `OfEssentiallySmall` namespace carries it as a `scoped instance` of low priority
instead, so that the statements there can mention `presheafToSheaf`. Since `HasSheafify` is a
`Prop`, proof irrelevance makes any two instances of it definitionally equal, and the sheafified
representable appearing in those statements is the same object as the one obtained from Mathlib's
instance wherever that also applies.

`smallYoneda` carries `attribute [local implicit_reducible]`: its sections over `Y` are
`Shrink.{m} (Y.unop ⟶ U)` by definition, but `rw` and `simp` match at a transparency that does not
unfold a plain `def`, so without it every rewrite under `(smallYoneda U).obj Y` is rejected as
ill-typed. `symm_smallYoneda_map` reads a section of the small model back as a morphism of the
site.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe m v u₁

namespace Stacks.Sites.SheafSection

variable {C : Type u₁} [Category.{v} C]

/-! ### Sheafification at the universe of the morphisms of the site -/

/-- **An essentially `m`-small site has sheafification of presheaves of sets with sections in
`Type m`.** -/
theorem hasSheafify_type_of_essentiallySmall (J : GrothendieckTopology C)
    [EssentiallySmall.{m} C] : HasSheafify J (Type m) :=
  hasSheafifyEssentiallySmallSite J (Type m)

variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]

/-- **Local sections of a sheaf of sets are morphisms out of a sheafified representable**, with
the universe of the objects of the site unrelated to the universe of its morphisms. A section
over `U` of a sheaf of sets with sections in `Type v` is the same thing as a morphism to it from
the sheafification of the presheaf represented by `U`. -/
def sectionEquiv (U : Cᵒᵖ) (M : Sheaf J (Type v)) :
    M.obj.obj U ≃ ((presheafToSheaf J (Type v)).obj (yoneda.obj U.unop) ⟶ M) :=
  yonedaEquiv.symm.trans ((sheafificationAdjunction J (Type v)).homEquiv _ _).symm

/-- The identification of local sections with morphisms out of a sheafified representable is
natural in the sheaf. -/
theorem sectionEquiv_comp (U : Cᵒᵖ) {M N : Sheaf J (Type v)} (morphism : M ⟶ N)
    (element : M.obj.obj U) :
    sectionEquiv J U N (morphism.hom.app U element) =
      sectionEquiv J U M element ≫ morphism := by
  dsimp [sectionEquiv]
  rw [← yonedaEquiv_symm_naturality_right]
  exact (sheafificationAdjunction J (Type v)).homEquiv_naturality_right_symm _ _

/-- The identification of local sections with morphisms out of a sheafified representable is
natural in the object: restricting a section corresponds to precomposing with the induced
morphism of sheafified representables. -/
theorem sectionEquiv_map {U V : Cᵒᵖ} (f : U ⟶ V) (M : Sheaf J (Type v))
    (element : M.obj.obj U) :
    sectionEquiv J V M (M.obj.map f element) =
      (presheafToSheaf J (Type v)).map (yoneda.map f.unop) ≫ sectionEquiv J U M element := by
  dsimp [sectionEquiv]
  rw [yonedaEquiv_symm_map]
  exact (sheafificationAdjunction J (Type v)).homEquiv_naturality_left_symm _ _

/-! ### The small model of a representable presheaf -/

/-- The sectionwise `m`-small model `Y ↦ Shrink (Y ⟶ U)` of the presheaf represented by `U` on a
locally `m`-small category. Unlike `CategoryTheory.yoneda.obj U`, whose sections live in the
universe of the morphisms of the site, this is a presheaf of sets with sections in `Type m`, so it
can be sheafified into `Sheaf J (Type m)` for an `m` unrelated to the site. -/
@[sga "4 I 1.3"]
def smallYoneda [LocallySmall.{m} C] (U : C) : Cᵒᵖ ⥤ Type m where
  obj Y := Shrink.{m} (Y.unop ⟶ U)
  map {Y _} f := ↾fun x => equivShrink _ (f.unop ≫ (equivShrink (Y.unop ⟶ U)).symm x)
  map_id Y := by ext x; simp
  map_comp f g := by ext x; simp

attribute [local implicit_reducible] smallYoneda

/-- Restriction in `Stacks.Sites.SheafSection.smallYoneda`, read back as composition of morphisms
of the site. -/
@[simp]
theorem symm_smallYoneda_map [LocallySmall.{m} C] {U : C} {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
    (x : (smallYoneda.{m} U).obj Y) :
    (equivShrink (Z.unop ⟶ U)).symm ((smallYoneda.{m} U).map f x) =
      f.unop ≫ (equivShrink (Y.unop ⟶ U)).symm x :=
  (equivShrink (Z.unop ⟶ U)).symm_apply_apply _

/-- **Yoneda's lemma for the small model of a representable presheaf**: morphisms from
`smallYoneda U` to a presheaf of sets with sections in `Type m` are the sections over `U`. -/
@[sga "3 I 1.1"]
def smallYonedaEquiv [LocallySmall.{m} C] {U : C} {F : Cᵒᵖ ⥤ Type m} :
    (smallYoneda.{m} U ⟶ F) ≃ F.obj (op U) where
  toFun η := η.app (op U) (equivShrink (U ⟶ U) (𝟙 U))
  invFun ξ :=
    { app Y := ↾fun x => F.map ((equivShrink (Y.unop ⟶ U)).symm x).op ξ
      naturality := fun Y Z f => by
        ext x
        change F.map ((equivShrink (Z.unop ⟶ U)).symm ((smallYoneda.{m} U).map f x)).op ξ
          = F.map f (F.map ((equivShrink (Y.unop ⟶ U)).symm x).op ξ)
        rw [symm_smallYoneda_map, op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] }
  left_inv η := by
    ext Y x
    change F.map ((equivShrink (Y.unop ⟶ U)).symm x).op
        (η.app (op U) (equivShrink (U ⟶ U) (𝟙 U))) = η.app Y x
    have h := NatTrans.naturality_apply η ((equivShrink (Y.unop ⟶ U)).symm x).op
      (show (smallYoneda.{m} U).obj (op U) from equivShrink (U ⟶ U) (𝟙 U))
    rw [show (smallYoneda.{m} U).map ((equivShrink (Y.unop ⟶ U)).symm x).op
        (equivShrink (U ⟶ U) (𝟙 U)) = x from
      (equivShrink (Y.unop ⟶ U)).symm.injective (by
        rw [symm_smallYoneda_map, Equiv.symm_apply_apply, Quiver.Hom.unop_op,
          Category.comp_id])] at h
    exact h.symm
  right_inv ξ := by simp

/-- Yoneda's lemma for the small model is compatible with postcomposition. -/
theorem smallYonedaEquiv_comp [LocallySmall.{m} C] {U : C} {F G : Cᵒᵖ ⥤ Type m}
    (α : smallYoneda.{m} U ⟶ F) (β : F ⟶ G) :
    smallYonedaEquiv (α ≫ β) = β.app (op U) (smallYonedaEquiv α) :=
  rfl

/-- The inverse direction of Yoneda's lemma for the small model is compatible with
postcomposition. -/
theorem smallYonedaEquiv_symm_naturality_right [LocallySmall.{m} C] (U : C)
    {F G : Cᵒᵖ ⥤ Type m} (β : F ⟶ G) (x : F.obj (op U)) :
    (smallYonedaEquiv (U := U) (F := F)).symm x ≫ β =
      (smallYonedaEquiv (U := U) (F := G)).symm (β.app (op U) x) :=
  (smallYonedaEquiv (U := U) (F := G)).injective <| by
    rw [smallYonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ### The identification at a sheaf universe unrelated to the site -/

/-- **Local sections of a sheaf of sets are morphisms out of a sheafified small representable.**
This is `Stacks.Sites.SheafSection.sectionEquiv` for a universe `m` of sections unrelated to the
universes of the site: the representable presheaf is replaced by its sectionwise `m`-small model,
which is what can be sheafified into `Sheaf J (Type m)`. -/
def sectionEquivSmall (J : GrothendieckTopology C) [LocallySmall.{m} C]
    [HasWeakSheafify J (Type m)] (U : Cᵒᵖ) (M : Sheaf J (Type m)) :
    M.obj.obj U ≃ ((presheafToSheaf J (Type m)).obj (smallYoneda.{m} U.unop) ⟶ M) :=
  smallYonedaEquiv.symm.trans ((sheafificationAdjunction J (Type m)).homEquiv _ _).symm

/-- The identification of local sections with morphisms out of a sheafified small representable
is natural in the sheaf. -/
theorem sectionEquivSmall_comp (J : GrothendieckTopology C) [LocallySmall.{m} C]
    [HasWeakSheafify J (Type m)] (U : Cᵒᵖ) {M N : Sheaf J (Type m)} (morphism : M ⟶ N)
    (element : M.obj.obj U) :
    sectionEquivSmall J U N (morphism.hom.app U element) =
      sectionEquivSmall J U M element ≫ morphism := by
  dsimp [sectionEquivSmall]
  rw [← smallYonedaEquiv_symm_naturality_right]
  exact (sheafificationAdjunction J (Type m)).homEquiv_naturality_right_symm _ _

/-! ### The forms stated on an essentially small site -/

namespace OfEssentiallySmall

/-- Sheafification of presheaves of sets with sections in `Type m` on an essentially `m`-small
site, as a low-priority instance scoped to this namespace. -/
scoped instance (priority := low) hasSheafify (J : GrothendieckTopology C)
    [EssentiallySmall.{m} C] : HasSheafify J (Type m) :=
  hasSheafify_type_of_essentiallySmall J

/-- **Local sections of a sheaf of sets on an essentially small site are morphisms out of a
sheafified representable.** This is `Stacks.Sites.SheafSection.sectionEquiv` with its
sheafification hypothesis discharged by essential smallness. -/
def sheafSectionEquiv (J : GrothendieckTopology C) [EssentiallySmall.{v} C] (U : Cᵒᵖ)
    (M : Sheaf J (Type v)) :
    M.obj.obj U ≃ ((presheafToSheaf J (Type v)).obj (yoneda.obj U.unop) ⟶ M) :=
  sectionEquiv J U M

/-- `Stacks.Sites.SheafSection.OfEssentiallySmall.sheafSectionEquiv` is natural in the sheaf. -/
theorem sheafSectionEquiv_comp (J : GrothendieckTopology C) [EssentiallySmall.{v} C] (U : Cᵒᵖ)
    {M N : Sheaf J (Type v)} (morphism : M ⟶ N) (element : M.obj.obj U) :
    sheafSectionEquiv J U N (morphism.hom.app U element) =
      sheafSectionEquiv J U M element ≫ morphism :=
  sectionEquiv_comp J U morphism element

/-- **Local sections of a sheaf of sets with sections in a universe unrelated to the site.** This
is `Stacks.Sites.SheafSection.sectionEquivSmall` with its sheafification hypothesis discharged by
essential smallness. -/
def sheafSectionEquivSmall (J : GrothendieckTopology C) [EssentiallySmall.{m} C] (U : Cᵒᵖ)
    (M : Sheaf J (Type m)) :
    M.obj.obj U ≃ ((presheafToSheaf J (Type m)).obj (smallYoneda.{m} U.unop) ⟶ M) :=
  sectionEquivSmall J U M

/-- `Stacks.Sites.SheafSection.OfEssentiallySmall.sheafSectionEquivSmall` is natural in the
sheaf. -/
theorem sheafSectionEquivSmall_comp (J : GrothendieckTopology C) [EssentiallySmall.{m} C]
    (U : Cᵒᵖ) {M N : Sheaf J (Type m)} (morphism : M ⟶ N) (element : M.obj.obj U) :
    sheafSectionEquivSmall J U N (morphism.hom.app U element) =
      sheafSectionEquivSmall J U M element ≫ morphism :=
  sectionEquivSmall_comp J U morphism element

end OfEssentiallySmall

end Stacks.Sites.SheafSection

end

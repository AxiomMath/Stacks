module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaGroupLaw
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The group-object axioms of the relative inertia

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks. The relative inertia
`I_{𝒳/𝒴}` has as objects the pairs `(x, α)` with `x` an object of `𝒳` and `α` an automorphism of
`x` in the fibre category of `𝒳` that `x` lives in, subject to `f(α) = id`; its projection
`π : I_{𝒳/𝒴} ⟶ 𝒳` is representable by algebraic spaces, so `I_{𝒳/𝒴}` is an object of the
2-category `Spaces/𝒳`. On it there is a *composition law*

`c : I_{𝒳/𝒴} ×_𝒳 I_{𝒳/𝒴} ⟶ I_{𝒳/𝒴}`,
`((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`,

which makes sense because `β : x ⟶ x'` is an isomorphism of the fibre category, together with a
*neutral element* `e : 𝒳 ⟶ I_{𝒳/𝒴}`, `x ↦ (x, id_x)` and an *inverse* `i : I_{𝒳/𝒴} ⟶ I_{𝒳/𝒴}`,
`(x, α) ↦ (x, α⁻¹)`. All three are morphisms over `𝒳`: `c` composed with `π` is the first
projection composed with `π`, `e` composed with `π` is the identity, and `i` composed with `π` is
`π`.

This data makes `I_{𝒳/𝒴}` a group object. This file proves the group-object axioms as
*equalities of 1-morphisms over the source*: associativity on the threefold 2-fibre product, the
two unit laws, and the two inverse laws. The products involved are the 2-fibre products of
`I_{𝒳/𝒴}` with itself over `𝒳`, in the (2,1)-category of categories over the base
(`CategoryTheory.TwoFibreProductOver.lift`). The axioms hold *strictly*, not merely up to
2-isomorphism.

## Main definitions

* `CategoryTheory.RelativeInertia.inverse`: the inverse `i`.
* `CategoryTheory.RelativeInertia.Pair` and `CategoryTheory.RelativeInertia.Triple`: the twofold
  and threefold 2-fibre products of `I_{S/S'}` over `S`, with their projections.
* `CategoryTheory.RelativeInertia.pairIdNeutral`, `pairNeutralId`, `pairIdInverse`,
  `pairInverseId`, `compFstPair`, `midPair`, `idCompPair`: the 1-morphisms into those products
  on which the group-object axioms are stated.
* `AlgebraicGeometry.Stack.relativeInertiaPairOverStack`: the twofold product of the relative
  inertia over `𝒳`, as an object of the 2-category of morphisms to `𝒳` representable by algebraic
  spaces.
* `AlgebraicGeometry.Stack.relativeInertiaCompositionHom`,
  `AlgebraicGeometry.Stack.relativeInertiaInverseHom`,
  `AlgebraicGeometry.Stack.relativeInertiaNeutralHom`: `c`, `i` and `e` in that 2-category.

## Main results

* `CategoryTheory.RelativeInertia.composition_assoc`: the associativity axiom.
* `CategoryTheory.RelativeInertia.composition_pairIdNeutral` and
  `CategoryTheory.RelativeInertia.composition_pairNeutralId`: the two unit axioms.
* `CategoryTheory.RelativeInertia.composition_pairIdInverse` and
  `CategoryTheory.RelativeInertia.composition_pairInverseId`: the two inverse axioms.
* `CategoryTheory.RelativeInertia.inverse_comp_π` and
  `AlgebraicGeometry.Stack.relativeInertiaNeutralHom_comp_map`: the inverse and the neutral
  element are morphisms over the source.
* `CategoryTheory.RelativeInertia.conjugateAuto_assoc`: the two bracketings of the threefold
  conjugation formula agree.

## Implementation notes

The composition law, the inverse and the axioms are stated for an arbitrary functor
`F : S ⥤ S'` and an arbitrary structure functor `p : S ⥤ C`, and specialised to algebraic stacks
only where `Spaces/𝒳` enters.

## References

* [Stacks Project, Tag 04ZQ](https://stacks.math.columbia.edu/tag/04ZQ)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.RelativeInertia

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
  {S' : Type u₃} [Category.{v₃} S']
/-! ### The inverse -/

/-- A morphism intertwining two automorphisms intertwines their inverses as well. -/
theorem comm_symm {X Y : S} (a : X ≅ X) (b : Y ≅ Y) (f : X ⟶ Y)
    (h : f ≫ b.hom = a.hom ≫ f) : f ≫ b.symm.hom = a.symm.hom ≫ f := by
  simp only [Iso.symm_hom]
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- The inverse of the group law: the 1-morphism `i : I_{S/S'} ⟶ I_{S/S'}`,
`(x, α) ↦ (x, α⁻¹)`, acting on morphisms by the identity. -/
@[stacks 050R "the inverse"]
def inverse (F : S ⥤ S') : RelativeInertia F ⥤ RelativeInertia F where
  obj A := { obj := A.obj, auto := .of A.auto.asIso.symm, cond := A.cond_inv }
  map {A B} φ := { hom := φ.hom, comm := comm_symm A.auto.asIso B.auto.asIso φ.hom φ.comm }
  map_id _ := RelativeInertiaHom.ext rfl
  map_comp _ _ := RelativeInertiaHom.ext rfl

/-- The inverse leaves the underlying object unchanged. -/
@[simp]
theorem inverse_obj_obj (F : S ⥤ S') (A : RelativeInertia F) :
    ((inverse F).obj A).obj = A.obj := rfl

/-- The automorphism attached by the inverse to `(x, α)` is `α⁻¹`. -/
@[simp]
theorem inverse_obj_auto_hom (F : S ⥤ S') (A : RelativeInertia F) :
    ((inverse F).obj A).auto.asIso.hom = A.auto.asIso.inv := rfl

/-- On morphisms the inverse is the identity. -/
@[simp]
theorem inverse_map_hom (F : S ⥤ S') {A B : RelativeInertia F} (φ : A ⟶ B) :
    ((inverse F).map φ).hom = φ.hom := rfl

/-- **The inverse is a morphism over the source**: followed by the projection to `S` it is that
projection again. -/
@[stacks 050R "the inverse is a morphism over the source"]
theorem inverse_comp_π (F : S ⥤ S') :
    inverse F ⋙ RelativeInertia.π F = RelativeInertia.π F := rfl

/-! ### The products `I ×_S I` and `(I ×_S I) ×_S I`

The twofold and threefold 2-fibre products of `I_{S/S'}` over `S`, in the (2,1)-category of
categories over `C`. Every 1-morphism into them below is built with
`CategoryTheory.TwoFibreProductOver.lift`, and its projections are recorded as `rfl`-lemmas. -/

/-- The 2-fibre product `I_{S/S'} ×_S I_{S/S'}`, the source of the composition law: an object is
a triple `((x, α), (x', α'), β)` with `β : x ≅ x'` vertical. -/
abbrev Pair (F : S ⥤ S') (p : S ⥤ C) :=
  TwoFibreProductOver (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F)

/-- The first projection `I_{S/S'} ×_S I_{S/S'} ⟶ I_{S/S'}`. -/
abbrev Pair.fst (F : S ⥤ S') (p : S ⥤ C) : Pair F p ⥤ RelativeInertia F :=
  TwoFibreProductOver.fst (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F)

/-- The second projection `I_{S/S'} ×_S I_{S/S'} ⟶ I_{S/S'}`. -/
abbrev Pair.snd (F : S ⥤ S') (p : S ⥤ C) : Pair F p ⥤ RelativeInertia F :=
  TwoFibreProductOver.snd (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F)

/-- The structure functor of `I_{S/S'} ×_S I_{S/S'}` as a category over `C`. -/
abbrev Pair.struct (F : S ⥤ S') (p : S ⥤ C) : Pair F p ⥤ C :=
  TwoFibreProductOver.structureFunctor (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F)

/-- The threefold 2-fibre product `(I_{S/S'} ×_S I_{S/S'}) ×_S I_{S/S'}`: an object is a pair
`((x, α), (x', α'), β)` together with `(x'', α'')` and a vertical `δ : x ≅ x''`. -/
abbrev Triple (F : S ⥤ S') (p : S ⥤ C) :=
  TwoFibreProductOver (Pair.struct F p) (RelativeInertia.π F ⋙ p) p
    (Pair.fst F p ⋙ RelativeInertia.π F) (RelativeInertia.π F)

/-- The projection of the threefold product onto its first two factors. -/
abbrev Triple.pairFst (F : S ⥤ S') (p : S ⥤ C) : Triple F p ⥤ Pair F p :=
  TwoFibreProductOver.fst (Pair.struct F p) (RelativeInertia.π F ⋙ p) p
    (Pair.fst F p ⋙ RelativeInertia.π F) (RelativeInertia.π F)

/-- The projection of the threefold product onto its third factor. -/
abbrev Triple.thd (F : S ⥤ S') (p : S ⥤ C) : Triple F p ⥤ RelativeInertia F :=
  TwoFibreProductOver.snd (Pair.struct F p) (RelativeInertia.π F ⋙ p) p
    (Pair.fst F p ⋙ RelativeInertia.π F) (RelativeInertia.π F)

/-- The structure functor of the threefold product as a category over `C`. -/
abbrev Triple.struct (F : S ⥤ S') (p : S ⥤ C) : Triple F p ⥤ C :=
  TwoFibreProductOver.structureFunctor (Pair.struct F p) (RelativeInertia.π F ⋙ p) p
    (Pair.fst F p ⋙ RelativeInertia.π F) (RelativeInertia.π F)

/-! ### The unit and inverse axioms -/

/-- Two functors into `RelativeInertia F` that agree on objects and on underlying morphisms are
equal. -/
private theorem functor_ext_of_hom_eq {T : Type*} [Category T] {F : S ⥤ S'}
    {G H : T ⥤ RelativeInertia F} (hobj : ∀ A, G.obj A = H.obj A)
    (hmap : ∀ {A B : T} (φ : A ⟶ B), HEq (G.map φ).hom (H.map φ).hom) : G = H :=
  Functor.ext hobj fun A B φ => RelativeInertiaHom.ext (by
    rw [RelativeInertia.comp_hom, RelativeInertia.comp_hom, RelativeInertiaHom.eqToHom_hom,
      RelativeInertiaHom.eqToHom_hom]
    exact eq_of_heq ((hmap φ).trans (by simp)))

section Units

variable (F : S ⥤ S') (p : S ⥤ C)

/-- The 1-morphism `⟨id, e ∘ π⟩ : I_{S/S'} ⟶ I_{S/S'} ×_S I_{S/S'}` over `S`, on objects
`(x, α) ↦ ((x, α), (x, id), id)`. -/
def pairIdNeutral : RelativeInertia F ⥤ Pair F p :=
  TwoFibreProductOver.lift (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F) (RelativeInertia.π F ⋙ p)
    (𝟭 (RelativeInertia F)) (RelativeInertia.π F ⋙ RelativeInertia.neutralSection F)
    rfl rfl (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- The 1-morphism `⟨e ∘ π, id⟩ : I_{S/S'} ⟶ I_{S/S'} ×_S I_{S/S'}` over `S`, on objects
`(x, α) ↦ ((x, id), (x, α), id)`. -/
def pairNeutralId : RelativeInertia F ⥤ Pair F p :=
  TwoFibreProductOver.lift (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F) (RelativeInertia.π F ⋙ p)
    (RelativeInertia.π F ⋙ RelativeInertia.neutralSection F) (𝟭 (RelativeInertia F))
    rfl rfl (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- The 1-morphism `⟨id, i⟩ : I_{S/S'} ⟶ I_{S/S'} ×_S I_{S/S'}` over `S`, on objects
`(x, α) ↦ ((x, α), (x, α⁻¹), id)`. -/
def pairIdInverse : RelativeInertia F ⥤ Pair F p :=
  TwoFibreProductOver.lift (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F) (RelativeInertia.π F ⋙ p)
    (𝟭 (RelativeInertia F)) (inverse F) rfl rfl (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- The 1-morphism `⟨i, id⟩ : I_{S/S'} ⟶ I_{S/S'} ×_S I_{S/S'}` over `S`, on objects
`(x, α) ↦ ((x, α⁻¹), (x, α), id)`. -/
def pairInverseId : RelativeInertia F ⥤ Pair F p :=
  TwoFibreProductOver.lift (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F) (RelativeInertia.π F ⋙ p)
    (inverse F) (𝟭 (RelativeInertia F)) rfl rfl (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- `⟨id, e ∘ π⟩` has first projection the identity. -/
theorem pairIdNeutral_comp_fst : pairIdNeutral F p ⋙ Pair.fst F p = 𝟭 (RelativeInertia F) := rfl

/-- `⟨id, e ∘ π⟩` has second projection the neutral section. -/
theorem pairIdNeutral_comp_snd :
    pairIdNeutral F p ⋙ Pair.snd F p =
      RelativeInertia.π F ⋙ RelativeInertia.neutralSection F := rfl

/-- `⟨e ∘ π, id⟩` has first projection the neutral section. -/
theorem pairNeutralId_comp_fst :
    pairNeutralId F p ⋙ Pair.fst F p =
      RelativeInertia.π F ⋙ RelativeInertia.neutralSection F := rfl

/-- `⟨e ∘ π, id⟩` has second projection the identity. -/
theorem pairNeutralId_comp_snd : pairNeutralId F p ⋙ Pair.snd F p = 𝟭 (RelativeInertia F) := rfl

/-- `⟨id, i⟩` has first projection the identity. -/
theorem pairIdInverse_comp_fst : pairIdInverse F p ⋙ Pair.fst F p = 𝟭 (RelativeInertia F) := rfl

/-- `⟨id, i⟩` has second projection the inverse. -/
theorem pairIdInverse_comp_snd : pairIdInverse F p ⋙ Pair.snd F p = inverse F := rfl

/-- `⟨i, id⟩` has first projection the inverse. -/
theorem pairInverseId_comp_fst : pairInverseId F p ⋙ Pair.fst F p = inverse F := rfl

/-- `⟨i, id⟩` has second projection the identity. -/
theorem pairInverseId_comp_snd : pairInverseId F p ⋙ Pair.snd F p = 𝟭 (RelativeInertia F) := rfl

/-- The right unit axiom: `c ∘ ⟨id, e ∘ π⟩ = id`. -/
@[stacks 050R "the right unit axiom"]
theorem composition_pairIdNeutral :
    pairIdNeutral F p ⋙ composition F p = 𝟭 (RelativeInertia F) := by
  have hobj : ∀ A : RelativeInertia F,
      (pairIdNeutral F p ⋙ composition F p).obj A = (𝟭 (RelativeInertia F)).obj A := fun A =>
    RelativeInertia.obj_ext rfl (by
      simp only [pairIdNeutral, TwoFibreProductOver.lift, Functor.comp_obj, π_obj, Functor.id_obj,
        neutralSection, Iso.app, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv, Functor.comp_map,
        π_map, Functor.id_map, composition_obj_obj, composition_obj_auto_hom, Category.id_comp]
      exact ((Category.id_comp (A.auto.asIso.hom ≫ 𝟙 A.obj)).trans
        (Category.comp_id A.auto.asIso.hom)).symm)
  exact functor_ext_of_hom_eq hobj fun _ => HEq.rfl

/-- The left unit axiom: `c ∘ ⟨e ∘ π, id⟩ = id`. -/
@[stacks 050R "the left unit axiom"]
theorem composition_pairNeutralId :
    pairNeutralId F p ⋙ composition F p = 𝟭 (RelativeInertia F) := by
  have hobj : ∀ A : RelativeInertia F,
      (pairNeutralId F p ⋙ composition F p).obj A = (𝟭 (RelativeInertia F)).obj A := fun A =>
    RelativeInertia.obj_ext rfl (by
      simp only [pairNeutralId, TwoFibreProductOver.lift, Functor.comp_obj, π_obj, neutralSection,
        Functor.id_obj, Iso.app, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv, Functor.comp_map,
        π_map, Functor.id_map, composition_obj_obj, composition_obj_auto_hom, Category.comp_id,
        Category.id_comp]
      exact ((Category.id_comp (A.auto.asIso.hom ≫ 𝟙 A.obj)).trans
        (Category.comp_id A.auto.asIso.hom)).symm)
  exact functor_ext_of_hom_eq hobj fun _ => HEq.rfl

/-- The right inverse axiom: `c ∘ ⟨id, i⟩ = e ∘ π`. -/
@[stacks 050R "the right inverse axiom"]
theorem composition_pairIdInverse :
    pairIdInverse F p ⋙ composition F p =
      RelativeInertia.π F ⋙ RelativeInertia.neutralSection F := by
  have hobj : ∀ A : RelativeInertia F,
      (pairIdInverse F p ⋙ composition F p).obj A =
        (RelativeInertia.π F ⋙ RelativeInertia.neutralSection F).obj A := fun A =>
    RelativeInertia.obj_ext rfl (by
      simp only [pairIdInverse, TwoFibreProductOver.lift, Functor.comp_obj, π_obj, Functor.id_obj,
        Iso.app, inverse_obj_obj, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv, Functor.comp_map,
        π_map, Functor.id_map, composition_obj_obj, composition_obj_auto_hom, inverse_obj_auto_hom,
        Category.id_comp, neutralSection, eqToHom_naturality, eqToHom_refl, Category.comp_id]
      exact A.auto.asIso.inv_hom_id)
  exact functor_ext_of_hom_eq hobj fun _ => HEq.rfl

/-- The left inverse axiom: `c ∘ ⟨i, id⟩ = e ∘ π`. -/
@[stacks 050R "the left inverse axiom"]
theorem composition_pairInverseId :
    pairInverseId F p ⋙ composition F p =
      RelativeInertia.π F ⋙ RelativeInertia.neutralSection F := by
  have hobj : ∀ A : RelativeInertia F,
      (pairInverseId F p ⋙ composition F p).obj A =
        (RelativeInertia.π F ⋙ RelativeInertia.neutralSection F).obj A := fun A =>
    RelativeInertia.obj_ext rfl (by
      simp only [pairInverseId, TwoFibreProductOver.lift, Functor.comp_obj, π_obj, Functor.id_obj,
        Iso.app, inverse_obj_obj, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv, Functor.comp_map,
        π_map, Functor.id_map, composition_obj_obj, composition_obj_auto_hom, inverse_obj_auto_hom,
        Category.id_comp, neutralSection, eqToHom_naturality, eqToHom_refl, Category.comp_id]
      exact A.auto.asIso.hom_inv_id)
  exact functor_ext_of_hom_eq hobj fun _ => HEq.rfl

end Units

/-! ### The associativity axiom -/

section Assoc

variable (F : S ⥤ S') (p : S ⥤ C)

/-- The composition law is a 1-morphism over `C`: its composite with the structure functor of
`I_{S/S'}` is the structure functor of `I_{S/S'} ×_S I_{S/S'}`. -/
theorem composition_comp_struct :
    composition F p ⋙ (RelativeInertia.π F ⋙ p) = Pair.struct F p :=
  TwoFibreProductOver.fst_comp_eq

/-- The comparison isomorphism of an object of the threefold product is vertical. -/
theorem triple_iso_x_isHomLift (A : Triple F p) : p.IsHomLift (𝟙 A.base) A.x.iso.hom := by
  have hb : A.x.base = A.base := A.hx
  rw [← hb]
  exact A.x.vertical

/-- The composite of two morphisms vertical over the same object of `C` is vertical. -/
theorem isHomLift_comp_of_vertical {U : C} {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : p.IsHomLift (𝟙 U) f) (hg : p.IsHomLift (𝟙 U) g) : p.IsHomLift (𝟙 U) (f ≫ g) := by
  have h : p.IsHomLift (𝟙 U ≫ 𝟙 U) (f ≫ g) := inferInstance
  rwa [Category.id_comp] at h

/-- Naturality of the comparison isomorphism `δ ∘ β⁻¹`, for bare isomorphisms of `S`: a pair of
morphisms compatible with `β` and with `δ` is compatible with `δ ∘ β⁻¹`. -/
theorem midIso_naturality {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : S} (β₁ : X₁ ≅ Y₁) (δ₁ : X₁ ≅ Z₁)
    (β₂ : X₂ ≅ Y₂) (δ₂ : X₂ ≅ Z₂) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (c : Z₁ ⟶ Z₂)
    (h1 : a ≫ β₂.hom = β₁.hom ≫ b) (h2 : a ≫ δ₂.hom = δ₁.hom ≫ c) :
    b ≫ β₂.inv ≫ δ₂.hom = (β₁.inv ≫ δ₁.hom) ≫ c := by
  have h3 : b ≫ β₂.inv = β₁.inv ≫ a := by
    rw [Iso.comp_inv_eq, Category.assoc, h1, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h3, Category.assoc, h2, Category.assoc]

/-- The comparison isomorphism `δ ∘ β⁻¹ : x' ≅ x''` between the second and the third factor of
an object `(((x, α), (x', α'), β), (x'', α''), δ)` of the threefold product. -/
def tripleMidIso : (Triple.pairFst F p ⋙ Pair.snd F p) ⋙ RelativeInertia.π F ≅
    Triple.thd F p ⋙ RelativeInertia.π F :=
  NatIso.ofComponents (fun A => A.x.iso.symm ≪≫ A.iso)
    (fun {A D} φ => midIso_naturality A.x.iso A.iso D.x.iso D.iso φ.a.a.hom φ.a.b.hom φ.b.hom
      φ.a.w φ.w)

/-- The comparison isomorphism `δ ∘ β⁻¹` is vertical. -/
theorem tripleMidIso_hom_app_isHomLift (A : Triple F p) :
    p.IsHomLift (𝟙 ((Triple.struct F p).obj A)) ((tripleMidIso F p).hom.app A) :=
  have : p.IsHomLift (𝟙 A.base) A.x.iso.hom := triple_iso_x_isHomLift F p A
  have h2 : p.IsHomLift (𝟙 A.base) A.x.iso.inv := inferInstance
  isHomLift_comp_of_vertical p A.x.iso.inv A.iso.hom h2 A.vertical

/-- The two bracketings of the threefold conjugation formula agree:
`(α β⁻¹ α' β) δ⁻¹ α'' δ = α β⁻¹ (α' (δβ⁻¹)⁻¹ α'' (δβ⁻¹)) β`, as an identity between morphisms
of `S`. -/
theorem conjugateAuto_assoc {X Y Z : S} (β : X ≅ Y) (δ : X ≅ Z)
    (α : X ⟶ X) (α' : Y ⟶ Y) (α'' : Z ⟶ Z) :
    δ.hom ≫ α'' ≫ δ.inv ≫ β.hom ≫ α' ≫ β.inv ≫ α =
      𝟙 X ≫ (β.hom ≫ ((β.inv ≫ δ.hom) ≫ α'' ≫ (δ.inv ≫ β.hom) ≫ α') ≫ β.inv ≫ α) ≫ 𝟙 X := by
  simp

/-- The 1-morphism `c × id : (I ×_S I) ×_S I ⟶ I ×_S I` over `S`, on objects
`(((x, α), (x', α'), β), (x'', α''), δ) ↦ ((x, α ∘ β⁻¹ ∘ α' ∘ β), (x'', α''), δ)`. -/
def compFstPair : Triple F p ⥤ Pair F p :=
  TwoFibreProductOver.lift (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F) (Triple.struct F p)
    (Triple.pairFst F p ⋙ composition F p) (Triple.thd F p)
    (by
      have h : Triple.pairFst F p ⋙ (composition F p ⋙ (RelativeInertia.π F ⋙ p)) =
          Triple.struct F p := by
        rw [composition_comp_struct]
        exact TwoFibreProductOver.fst_comp_eq
      exact h)
    TwoFibreProductOver.snd_comp_eq
    (TwoFibreProductOver.psiIso (Pair.struct F p) (RelativeInertia.π F ⋙ p) p
      (Pair.fst F p ⋙ RelativeInertia.π F) (RelativeInertia.π F))
    (fun A => A.vertical)

/-- The 1-morphism `(pr₂, pr₃) : (I ×_S I) ×_S I ⟶ I ×_S I` over `S`, on objects
`(((x, α), (x', α'), β), (x'', α''), δ) ↦ ((x', α'), (x'', α''), δ ∘ β⁻¹)`. -/
def midPair : Triple F p ⥤ Pair F p :=
  TwoFibreProductOver.lift (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F) (Triple.struct F p)
    (Triple.pairFst F p ⋙ Pair.snd F p) (Triple.thd F p)
    (by
      have h : Triple.pairFst F p ⋙ (Pair.snd F p ⋙ (RelativeInertia.π F ⋙ p)) =
          Triple.struct F p := by
        rw [TwoFibreProductOver.snd_comp_eq]
        exact TwoFibreProductOver.fst_comp_eq
      exact h)
    TwoFibreProductOver.snd_comp_eq (tripleMidIso F p) (tripleMidIso_hom_app_isHomLift F p)

/-- `(pr₂, pr₃)` is a 1-morphism over `C`. -/
theorem midPair_comp_struct : midPair F p ⋙ Pair.struct F p = Triple.struct F p :=
  TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _

/-- The 1-morphism `(id × c) ∘ assoc : (I ×_S I) ×_S I ⟶ I ×_S I` over `S`, on objects
`(((x, α), (x', α'), β), (x'', α''), δ) ↦ ((x, α), (x', α' ∘ (δβ⁻¹)⁻¹ ∘ α'' ∘ δβ⁻¹), β)`. -/
def idCompPair : Triple F p ⥤ Pair F p :=
  TwoFibreProductOver.lift (RelativeInertia.π F ⋙ p) (RelativeInertia.π F ⋙ p) p
    (RelativeInertia.π F) (RelativeInertia.π F) (Triple.struct F p)
    (Triple.pairFst F p ⋙ Pair.fst F p) (midPair F p ⋙ composition F p)
    (by
      have h : Triple.pairFst F p ⋙ (Pair.fst F p ⋙ (RelativeInertia.π F ⋙ p)) =
          Triple.struct F p := by
        rw [TwoFibreProductOver.fst_comp_eq]
        exact TwoFibreProductOver.fst_comp_eq
      exact h)
    (by
      have h : midPair F p ⋙ (composition F p ⋙ (RelativeInertia.π F ⋙ p)) =
          Triple.struct F p := by
        rw [composition_comp_struct]
        exact midPair_comp_struct F p
      exact h)
    (NatIso.ofComponents (fun A => A.x.iso) (fun φ => φ.a.w))
    (fun A => triple_iso_x_isHomLift F p A)

/-- `c × id` has first projection `c` on the first two factors. -/
theorem compFstPair_comp_fst :
    compFstPair F p ⋙ Pair.fst F p = Triple.pairFst F p ⋙ composition F p := rfl

/-- `c × id` has second projection the third factor. -/
theorem compFstPair_comp_snd : compFstPair F p ⋙ Pair.snd F p = Triple.thd F p := rfl

/-- `(pr₂, pr₃)` has first projection the second factor. -/
theorem midPair_comp_fst :
    midPair F p ⋙ Pair.fst F p = Triple.pairFst F p ⋙ Pair.snd F p := rfl

/-- `(pr₂, pr₃)` has second projection the third factor. -/
theorem midPair_comp_snd : midPair F p ⋙ Pair.snd F p = Triple.thd F p := rfl

/-- `(id × c) ∘ assoc` has first projection the first factor. -/
theorem idCompPair_comp_fst :
    idCompPair F p ⋙ Pair.fst F p = Triple.pairFst F p ⋙ Pair.fst F p := rfl

/-- `(id × c) ∘ assoc` has second projection `c` on the last two factors. -/
theorem idCompPair_comp_snd :
    idCompPair F p ⋙ Pair.snd F p = midPair F p ⋙ composition F p := rfl

/-- The associativity axiom: `c ∘ (c × id) = c ∘ (id × c) ∘ assoc` as
1-morphisms `(I_{S/S'} ×_S I_{S/S'}) ×_S I_{S/S'} ⟶ I_{S/S'}` over `S`: both send
`(((x, α), (x', α'), β), (x'', α''), δ)` to `(x, α ∘ β⁻¹ ∘ α' ∘ β ∘ δ⁻¹ ∘ α'' ∘ δ)`. -/
@[stacks 050R "the associativity axiom"]
theorem composition_assoc :
    compFstPair F p ⋙ composition F p = idCompPair F p ⋙ composition F p := by
  have hobj : ∀ A : Triple F p, (compFstPair F p ⋙ composition F p).obj A =
      (idCompPair F p ⋙ composition F p).obj A := fun A =>
    RelativeInertia.obj_ext rfl
      (conjugateAuto_assoc A.x.iso A.iso A.x.x.auto.asIso.hom A.x.y.auto.asIso.hom
        A.y.auto.asIso.hom)
  exact functor_ext_of_hom_eq hobj fun _ => HEq.rfl

end Assoc

end CategoryTheory.RelativeInertia

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- `I_{𝒳/𝒴} ×_𝒳 I_{𝒳/𝒴}` as an object of `Spaces/𝒳`: the 2-fibre product of the projection
with itself, with structure 1-morphism to `𝒳` the first projection followed by `π`. -/
@[stacks 050R "the twofold product of the relative inertia in the 2-category of morphisms to the
  source representable by algebraic spaces"]
noncomputable def relativeInertiaPairOverStack (f : 𝒳 ⟶ 𝒴) : SpacesOverStack B S hS 𝒳 where
  source := (AlgebraicStacks.twoFibreProductSquare B S hS
    (relativeInertiaOverStack B S hS f).map (relativeInertiaOverStack B S hS f).map).pt
  map := (AlgebraicStacks.twoFibreProductSquare B S hS
      (relativeInertiaOverStack B S hS f).map (relativeInertiaOverStack B S hS f).map).fst ≫
    (relativeInertiaOverStack B S hS f).map
  representable :=
    isRepresentableByAlgebraicSpaces_comp B S hS
      (AlgebraicStacks.twoFibreProductSquare B S hS
        (relativeInertiaOverStack B S hS f).map (relativeInertiaOverStack B S hS f).map).fst.hom
      (relativeInertiaOverStack B S hS f).map.hom
      (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳.val
        (relativeInertiaOverStack B S hS f).source.val
        (relativeInertiaOverStack B S hS f).source.val
        (relativeInertiaOverStack B S hS f).map.hom.hom
        (relativeInertiaOverStack B S hS f).map.hom.hom
        (relativeInertiaOverStack B S hS f).representable)
      (relativeInertiaOverStack B S hS f).representable

/-- The composition law as a 1-morphism of `Spaces/𝒳`: the functor
`c : I_{𝒳/𝒴} ×_𝒳 I_{𝒳/𝒴} ⟶ I_{𝒳/𝒴}`, `((x, α), (x', α'), β) ↦ (x, α ∘ β⁻¹ ∘ α' ∘ β)`, with
the identity as comparison 2-morphism. -/
@[stacks 050R "the composition law as a 1-morphism of the 2-category of morphisms to the source
  representable by algebraic spaces"]
noncomputable def relativeInertiaCompositionHom (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaPairOverStack B S hS f ⟶ relativeInertiaOverStack B S hS f where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.composition f.hom.hom.toFunctor 𝒳.val.val.p
      w := RelativeInertia.composition_comp_struct f.hom.hom.toFunctor 𝒳.val.val.p })
  comm := 𝟙 _

/-- The inverse as a 1-morphism of `Spaces/𝒳`: the functor `i : I_{𝒳/𝒴} ⟶ I_{𝒳/𝒴}`,
`(x, α) ↦ (x, α⁻¹)`, with the identity as comparison 2-morphism. -/
@[stacks 050R "the inverse as a 1-morphism of the 2-category of morphisms to the source
  representable by algebraic spaces"]
noncomputable def relativeInertiaInverseHom (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaOverStack B S hS f ⟶ relativeInertiaOverStack B S hS f where
  map := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.inverse f.hom.hom.toFunctor, w := rfl })
  comm := 𝟙 _

/-- The neutral element as a 1-morphism of algebraic stacks: `e : 𝒳 ⟶ I_{𝒳/𝒴}`,
`x ↦ (x, id_x)`. -/
@[stacks 050R "the neutral element as a 1-morphism of algebraic stacks"]
noncomputable def relativeInertiaNeutralHom (f : 𝒳 ⟶ 𝒴) :
    𝒳 ⟶ (relativeInertiaOverStack B S hS f).source :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := RelativeInertia.neutralSection f.hom.hom.toFunctor, w := rfl })

/-- The neutral element is a section of the projection: `e ≫ π = 𝟙 𝒳`, an equality of
1-morphisms of algebraic stacks. -/
@[stacks 050R "the neutral element is a section of the projection"]
theorem relativeInertiaNeutralHom_comp_map (f : 𝒳 ⟶ 𝒴) :
    relativeInertiaNeutralHom B S hS f ≫ (relativeInertiaOverStack B S hS f).map = 𝟙 𝒳 := rfl

end AlgebraicGeometry.Stack

end

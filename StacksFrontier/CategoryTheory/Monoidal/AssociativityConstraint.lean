module

public import StacksFrontier.CategoryTheory.Monoidal.UnitOfAssociativityConstraint
public import Mathlib.CategoryTheory.Monoidal.Free.Coherence
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Units of an associativity constraint

Let `C` be a category with a functor `⊗ = T : C × C ⥤ C` and an associativity constraint `φ`
(`CategoryTheory.AssociativityConstraint`). By Stacks Lemma 0HAW
(`CategoryTheory.AssociativityConstraint.unitEquivUnitPair`) a unit is the same as a pair
`(𝟏, 1)` of an object `𝟏` and an isomorphism `1 : 𝟏 ⊗ 𝟏 ≅ 𝟏` such that `X ↦ 𝟏 ⊗ X` and
`X ↦ X ⊗ 𝟏` are equivalences (`CategoryTheory.AssociativityConstraint.UnitPair`), with unit
constraints `l` and `r` (`UnitPair.l`, `UnitPair.r`) characterized by
`id_𝟏 ⊗ l_X = (1 ⊗ id_X) ∘ φ` and `r_X ⊗ id_𝟏 = (id_X ⊗ 1) ∘ φ⁻¹`. This file proves Stacks
Lemmas 0HAX and 0HAY about such a pair.

## Main results

* Lemma 0HAX: `CategoryTheory.AssociativityConstraint.UnitPair.assoc_hom_comp_tensorMap_iso_id`,
  `CategoryTheory.AssociativityConstraint.UnitPair.comp_comm`,
  `CategoryTheory.AssociativityConstraint.UnitPair.endCommMonoid`,
  `CategoryTheory.AssociativityConstraint.UnitPair.eq_iso_inv_comp_tensorMap_comp_iso`,
  `CategoryTheory.AssociativityConstraint.UnitPair.existsUnique_iso`.
* Lemma 0HAY: `CategoryTheory.AssociativityConstraint.UnitPair.l_self_eq_iso`,
  `CategoryTheory.AssociativityConstraint.UnitPair.r_self_eq_iso`,
  `CategoryTheory.AssociativityConstraint.UnitPair.assoc_hom_comp_tensorMap_l_id`,
  `CategoryTheory.AssociativityConstraint.UnitPair.tensorMap_id_r_eq`; its final statement, that
  a monoidal category satisfies the assumptions of Mac Lane's coherence theorem, is
  `CategoryTheory.AssociativityConstraint.UnitPair.monoidalCategory`, and the conclusion of that
  theorem is `CategoryTheory.AssociativityConstraint.UnitPair.coherence`.

## Implementation notes

The Stacks project suppresses the associativity constraint once the pentagon is known to hold;
the statements below write it out wherever the two sides have the same source and target up to
reassociation.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category

universe v u

namespace AssociativityConstraint

namespace UnitPair

variable {C : Type u} [Category.{v} C] {T : C × C ⥤ C} (φ : AssociativityConstraint T)
  (p : UnitPair T)

/-- Stacks Lemma 0HAY (1), for `r`: `r_𝟏 = 1 : 𝟏 ⊗ 𝟏 ≅ 𝟏`. -/
@[stacks 0HAY "(1) the arrows `1` and `r_𝟏` agree"]
theorem r_self_eq_iso : p.r φ p.obj = p.iso := by
  ext
  refine p.tensorMap_r_injective ((cancel_epi (φ.iso p.obj p.obj p.obj).hom).1 ?_)
  rw [p.triangle φ, p.tensorMap_l φ]

/-- Stacks Lemma 0HAY (1), for `l`: `l_𝟏 = 1 : 𝟏 ⊗ 𝟏 ≅ 𝟏`. -/
@[stacks 0HAY "(1) the arrows `1` and `l_𝟏` agree"]
theorem l_self_eq_iso : p.l φ p.obj = p.iso := by
  ext
  rw [← p.r_self_eq_iso φ]
  exact (p.toUnit φ).l_obj_eq_r_obj

/-- The monoidal category structure on `C` with tensor product `T`, unit `𝟏`, associator `φ⁻¹`
and unitors `l`, `r` attached to the pair `(𝟏, 1)`. This is the final statement of Stacks
Lemma 0HAY: `(C, ⊗, φ, 𝟏, 1)` satisfies the assumptions of Mac Lane's coherence theorem
(Natural associativity and commutativity, Theorem 5.2), namely the axioms of a monoidal
category. -/
@[stacks 0HAY "final statement: `(C, ⊗, φ, 𝟏, 1)` with `l`, `r` satisfies the assumptions of \
Mac Lane's coherence theorem, i.e. is a monoidal category", implicit_reducible]
def monoidalCategory : MonoidalCategory C :=
  (p.toUnit φ).monoidalCategory

/-- Mac Lane's coherence theorem for `(C, ⊗, φ, 𝟏, 1)`, the conclusion of the theorem whose
assumptions the final statement of Stacks Lemma 0HAY verifies: any two morphisms between
the same objects of the free monoidal category on the objects of `C`, that is any two composites
of tensor products of the constraints `φ`, `l`, `r` and their inverses with the same source and
target, are sent to the same morphism of `C`. -/
@[stacks 0HAY "final statement: Mac Lane's coherence theorem for `(C, ⊗, φ, 𝟏, 1)`, every \
diagram built from `φ`, `l`, `r` commutes"]
theorem coherence {X Y : FreeMonoidalCategory C} (f g : X ⟶ Y) :
    letI := p.monoidalCategory φ
    FreeMonoidalCategory.projectMap id X Y f = FreeMonoidalCategory.projectMap id X Y g := by
  rw [Subsingleton.elim f g]

/-- Stacks Lemma 0HAY (2): `(l_X ⊗ id_Y) ∘ φ_{𝟏,X,Y} = l_{X ⊗ Y} : 𝟏 ⊗ (X ⊗ Y) ⟶ X ⊗ Y`. -/
@[stacks 0HAY "(2) `l_X ⊗ id_Y = l_{X ⊗ Y}`, with the associativity constraint written out"]
theorem assoc_hom_comp_tensorMap_l_id (X Y : C) :
    (φ.iso p.obj X Y).hom ≫ tensorMap T (p.l φ X).hom (𝟙 Y) = (p.l φ (T.obj (X, Y))).hom := by
  let := p.monoidalCategory φ
  exact (MonoidalCategory.leftUnitor_tensor_hom X Y).symm

/-- Stacks Lemma 0HAY (3): `id_X ⊗ r_Y = r_{X ⊗ Y} ∘ φ_{X,Y,𝟏} : X ⊗ (Y ⊗ 𝟏) ⟶ X ⊗ Y`. -/
@[stacks 0HAY "(3) `id_X ⊗ r_Y = r_{X ⊗ Y}`, with the associativity constraint written out"]
theorem tensorMap_id_r_eq (X Y : C) :
    tensorMap T (𝟙 X) (p.r φ Y).hom = (φ.iso X Y p.obj).hom ≫ (p.r φ (T.obj (X, Y))).hom := by
  let := p.monoidalCategory φ
  have h := MonoidalCategory.rightUnitor_tensor_hom X Y
  change (p.r φ (T.obj (X, Y))).hom = (φ.iso X Y p.obj).inv ≫ tensorMap T (𝟙 X) (p.r φ Y).hom
    at h
  rw [h, Iso.hom_inv_id_assoc]

/-- Stacks Lemma 0HAX (1): `1 ⊗ id_𝟏 = id_𝟏 ⊗ 1`, as arrows `𝟏 ⊗ (𝟏 ⊗ 𝟏) ⟶ 𝟏 ⊗ 𝟏` once the
associativity constraint is written out. -/
@[stacks 0HAX "(1) `1 ⊗ id_𝟏 = id_𝟏 ⊗ 1`, with the associativity constraint written out"]
theorem assoc_hom_comp_tensorMap_iso_id :
    (φ.iso p.obj p.obj p.obj).hom ≫ tensorMap T p.iso.hom (𝟙 p.obj) =
      tensorMap T (𝟙 p.obj) p.iso.hom := by
  rw [← p.tensorMap_l φ, p.l_self_eq_iso φ]

section

include φ

@[reassoc]
lemma tensorMap_id_left_comp_iso (a : p.obj ⟶ p.obj) :
    tensorMap T (𝟙 p.obj) a ≫ p.iso.hom = p.iso.hom ≫ a := by
  have h := p.l_naturality φ a
  rwa [p.l_self_eq_iso φ] at h

@[reassoc]
lemma tensorMap_id_right_comp_iso (a : p.obj ⟶ p.obj) :
    tensorMap T a (𝟙 p.obj) ≫ p.iso.hom = p.iso.hom ≫ a := by
  have h := p.r_naturality φ a
  rwa [p.r_self_eq_iso φ] at h

/-- Stacks Lemma 0HAX (3): `a = 1 ∘ (a ⊗ id_𝟏) ∘ 1⁻¹ = 1 ∘ (id_𝟏 ⊗ a) ∘ 1⁻¹` for every
`a ∈ Γ = Mor(𝟏, 𝟏)`. -/
@[stacks 0HAX "(3) `a = 1 ∘ (a ⊗ id_𝟏) ∘ 1⁻¹ = 1 ∘ (id_𝟏 ⊗ a) ∘ 1⁻¹` for `a ∈ Mor(𝟏, 𝟏)`"]
theorem eq_iso_inv_comp_tensorMap_comp_iso (a : p.obj ⟶ p.obj) :
    a = p.iso.inv ≫ tensorMap T a (𝟙 p.obj) ≫ p.iso.hom ∧
      a = p.iso.inv ≫ tensorMap T (𝟙 p.obj) a ≫ p.iso.hom := by
  rw [p.tensorMap_id_right_comp_iso φ, p.tensorMap_id_left_comp_iso φ, Iso.inv_hom_id_assoc]
  exact ⟨rfl, rfl⟩

/-- `1 ∘ (a ⊗ a) = a² ∘ 1` for `a ∈ Mor(𝟏, 𝟏)`. -/
@[reassoc]
lemma tensorMap_self_comp_iso (a : p.obj ⟶ p.obj) :
    tensorMap T a a ≫ p.iso.hom = p.iso.hom ≫ a ≫ a := by
  rw [show tensorMap T a a = tensorMap T a (𝟙 p.obj) ≫ tensorMap T (𝟙 p.obj) a by simp, assoc,
    p.tensorMap_id_left_comp_iso φ, p.tensorMap_id_right_comp_iso_assoc φ]

/-- Stacks Lemma 0HAX (2): composition of endomorphisms of `𝟏` is commutative. -/
@[stacks 0HAX "(2) the monoid `Γ = Mor(𝟏, 𝟏)` is commutative"]
theorem comp_comm (a b : p.obj ⟶ p.obj) : a ≫ b = b ≫ a := by
  have h₁ : p.iso.hom ≫ a ≫ b = tensorMap T a b ≫ p.iso.hom := by
    rw [← p.tensorMap_id_right_comp_iso_assoc φ a b, ← p.tensorMap_id_left_comp_iso φ b,
      tensorMap_comp_tensorMap_assoc]
    simp
  have h₂ : p.iso.hom ≫ b ≫ a = tensorMap T a b ≫ p.iso.hom := by
    rw [← p.tensorMap_id_left_comp_iso_assoc φ b a, ← p.tensorMap_id_right_comp_iso φ a,
      tensorMap_comp_tensorMap_assoc]
    simp
  rw [← cancel_epi p.iso.hom, h₁, h₂]

/-- Stacks Lemma 0HAX (2): `Γ = Mor(𝟏, 𝟏)` is a commutative monoid under composition. -/
@[stacks 0HAX "(2) `Γ = Mor(𝟏, 𝟏)` is a commutative monoid", implicit_reducible]
def endCommMonoid : CommMonoid (End p.obj) where
  __ := End.monoid
  mul_comm a b := End.ext (p.comp_comm φ b.asHom a.asHom)

/-- Two isomorphisms of pairs `(𝟏', 1') ≅ (𝟏, 1)` agree. -/
private lemma iso_eq_of_comm {p' : UnitPair T} (s t : p'.obj ≅ p.obj)
    (hs : p'.iso.hom ≫ s.hom = tensorMap T s.hom s.hom ≫ p.iso.hom)
    (ht : p'.iso.hom ≫ t.hom = tensorMap T t.hom t.hom ≫ p.iso.hom) : s = t := by
  let c : p.obj ≅ p.obj := t.symm ≪≫ s
  have hst : s.hom = t.hom ≫ c.hom := by simp [c]
  rw [hst, ← tensorMap_comp_tensorMap, assoc, p.tensorMap_self_comp_iso φ, ← reassoc_of% ht,
    cancel_epi, cancel_epi] at hs
  have hc : c.hom = 𝟙 _ := by
    rw [← cancel_epi c.hom, comp_id]
    exact hs.symm
  ext
  rw [hst, hc, comp_id]

/-- Stacks Lemma 0HAX (4): any other pair `(𝟏', 1')` is isomorphic to `(𝟏, 1)` by a unique
isomorphism, that is a unique `t : 𝟏' ≅ 𝟏` with `t ∘ 1' = 1 ∘ (t ⊗ t)`. -/
@[stacks 0HAX "(4) any other unit is isomorphic to `(𝟏, 1)` by a unique isomorphism"]
theorem existsUnique_iso (p' : UnitPair T) :
    ∃! t : p'.obj ≅ p.obj, p'.iso.hom ≫ t.hom = tensorMap T t.hom t.hom ≫ p.iso.hom := by
  let t₀ : p'.obj ≅ p.obj := (p.r φ p'.obj).symm ≪≫ p'.l φ p.obj
  let b : p.obj ≅ p.obj := t₀.symm ≪≫ p'.iso.symm ≪≫ tensorIso T t₀ t₀ ≪≫ p.iso
  have hb : tensorMap T t₀.hom t₀.hom ≫ p.iso.hom = p'.iso.hom ≫ t₀.hom ≫ b.hom := by
    simp [b]
  have ht : p'.iso.hom ≫ (t₀ ≪≫ b.symm).hom =
      tensorMap T (t₀ ≪≫ b.symm).hom (t₀ ≪≫ b.symm).hom ≫ p.iso.hom := by
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    rw [← tensorMap_comp_tensorMap, assoc, p.tensorMap_self_comp_iso φ, reassoc_of% hb]
    simp
  exact ⟨t₀ ≪≫ b.symm, ht, fun s hs => p.iso_eq_of_comm φ s _ hs ht⟩

end

end UnitPair

end AssociativityConstraint

end CategoryTheory

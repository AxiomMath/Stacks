module

public import StacksFrontier.CategoryTheory.Monoidal.AssociativityConstraint
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Commutativity constraints

Following the Stacks project (Categories, Section 0FFJ), a *commutativity constraint* for a
functor `⊗ : C × C ⥤ C` is a functorial isomorphism `ψ : X ⊗ Y ≅ Y ⊗ X` with `ψ ∘ ψ = id`. It is
*compatible* with an associativity constraint `φ` if the hexagon
`φ ∘ ψ ∘ φ = (ψ ⊗ id) ∘ φ ∘ (id ⊗ ψ) : X ⊗ (Y ⊗ Z) ⟶ (Z ⊗ X) ⊗ Y` commutes. A symmetric
monoidal category is a quadruple `(C, ⊗, φ, ψ)` with `ψ` compatible with `φ` for which a unit
exists; Lemma 0HB0 computes `ψ` on the unit.

## Main definitions

* `CategoryTheory.CommutativityConstraint T`: a commutativity constraint for `T : C × C ⥤ C`.
* `CategoryTheory.CommutativityConstraint.Compatible`: the hexagon axiom.
* `CategoryTheory.CommutativityConstraint.braidedCategory`: the Mathlib braided structure on the
  monoidal category `CategoryTheory.AssociativityConstraint.UnitPair.monoidalCategory`.
* `CategoryTheory.CommutativityConstraint.symmetricCategory`: the Mathlib symmetric structure on
  it.

## Main results

* Lemma 0HB0: `CategoryTheory.CommutativityConstraint.hom_comp_one` and
  `CategoryTheory.CommutativityConstraint.tensorMap_id_l_eq`; its final statement, that a
  symmetric monoidal category satisfies the assumptions of Mac Lane's coherence theorem, is
  `CategoryTheory.CommutativityConstraint.symmetricCategory`.
-/

@[expose] public section

namespace CategoryTheory

open Category AssociativityConstraint

universe v u

variable {C : Type u} [Category.{v} C]

/-- A *commutativity constraint* for a functor `T : C × C ⥤ C`, written `(X, Y) ↦ X ⊗ Y`: a
functorial isomorphism `ψ : X ⊗ Y ≅ Y ⊗ X` such that `ψ ∘ ψ : X ⊗ Y ⟶ X ⊗ Y` is the
identity. -/
structure CommutativityConstraint (T : C × C ⥤ C) where
  /-- The isomorphism `ψ_{X,Y} : X ⊗ Y ≅ Y ⊗ X`. -/
  iso (X Y : C) : T.obj (X, Y) ≅ T.obj (Y, X)
  /-- `ψ` is functorial in `X` and `Y`. -/
  naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorMap T f g ≫ (iso X' Y').hom = (iso X Y).hom ≫ tensorMap T g f
  /-- `ψ ∘ ψ = id`. -/
  hom_comp_hom (X Y : C) : (iso X Y).hom ≫ (iso Y X).hom = 𝟙 _

namespace CommutativityConstraint

variable {T : C × C ⥤ C} (ψ : CommutativityConstraint T)

/-- A commutativity constraint `ψ` is *compatible* with an associativity constraint `φ` if for
all `X`, `Y`, `Z` the hexagon
`φ_{Z,X,Y} ∘ ψ_{X ⊗ Y, Z} ∘ φ_{X,Y,Z} = (ψ_{X,Z} ⊗ id_Y) ∘ φ_{X,Z,Y} ∘ (id_X ⊗ ψ_{Y,Z})`
commutes. -/
def Compatible (φ : AssociativityConstraint T) : Prop :=
  ∀ X Y Z : C, (φ.iso X Y Z).hom ≫ (ψ.iso (T.obj (X, Y)) Z).hom ≫ (φ.iso Z X Y).hom =
    tensorMap T (𝟙 X) (ψ.iso Y Z).hom ≫ (φ.iso X Z Y).hom ≫ tensorMap T (ψ.iso X Z).hom (𝟙 Y)

lemma inv_eq (X Y : C) : (ψ.iso X Y).inv = (ψ.iso Y X).hom :=
  Iso.inv_ext (ψ.hom_comp_hom X Y)

variable {ψ} {φ : AssociativityConstraint T} (h : ψ.Compatible φ) (p : UnitPair T)

include h in
/-- The hexagon for `φ⁻¹`, obtained by inverting the hexagon of `ψ.Compatible φ`. -/
lemma hexagon_inv (X Y Z : C) :
    (φ.iso X Y Z).inv ≫ (ψ.iso X (T.obj (Y, Z))).hom ≫ (φ.iso Y Z X).inv =
      tensorMap T (ψ.iso X Y).hom (𝟙 Z) ≫ (φ.iso Y X Z).inv ≫
        tensorMap T (𝟙 Y) (ψ.iso X Z).hom := by
  have e : φ.iso Y Z X ≪≫ ψ.iso (T.obj (Y, Z)) X ≪≫ φ.iso X Y Z =
      tensorIso T (Iso.refl Y) (ψ.iso Z X) ≪≫ φ.iso Y X Z ≪≫
        tensorIso T (ψ.iso Y X) (Iso.refl Z) :=
    Iso.ext (h Y Z X)
  have h' := congrArg Iso.inv e
  simp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv, assoc, inv_eq] at h'
  exact h'

/-- The Mathlib braided structure with braiding `ψ` on the monoidal category
`AssociativityConstraint.UnitPair.monoidalCategory`. -/
@[implicit_reducible]
noncomputable def braidedCategory : letI := p.monoidalCategory φ; BraidedCategory C :=
  letI := p.monoidalCategory φ
  { braiding := ψ.iso
    braiding_naturality_right := fun X _ _ f => ψ.naturality (𝟙 X) f
    braiding_naturality_left := fun f Z => ψ.naturality f (𝟙 Z)
    hexagon_forward := fun X Y Z => hexagon_inv h X Y Z
    hexagon_reverse := fun X Y Z => h X Y Z }

/-- The Mathlib symmetric monoidal structure with braiding `ψ` on the monoidal category
`AssociativityConstraint.UnitPair.monoidalCategory`. This is the final statement of Stacks
Lemma 0HB0: `(C, ⊗, φ, ψ, 𝟏)` satisfies the assumptions of Mac Lane's coherence theorem
(Natural associativity and commutativity, Theorem 5.1). -/
@[stacks 0HB0 "final statement: `(C, ⊗, φ, ψ, 𝟏)` with `l`, `r` satisfies the assumptions of \
Mac Lane's coherence theorem, i.e. is a symmetric monoidal category", implicit_reducible]
noncomputable def symmetricCategory : letI := p.monoidalCategory φ; SymmetricCategory C :=
  letI := p.monoidalCategory φ
  { braidedCategory h p with
    symmetry := ψ.hom_comp_hom }

include h in
/-- `l_X ∘ ψ_{X,𝟏} = r_X : X ⊗ 𝟏 ⟶ X`. -/
lemma hom_comp_l (X : C) :
    (ψ.iso X p.obj).hom ≫ (p.l φ X).hom = (p.r φ X).hom := by
  let := p.monoidalCategory φ
  let := braidedCategory h p
  exact braiding_leftUnitor X

include h in
/-- Stacks Lemma 0HB0 (1): `1 ∘ ψ = 1 : 𝟏 ⊗ 𝟏 ⟶ 𝟏`. -/
@[stacks 0HB0 "(1) `1 ∘ ψ = 1 : 𝟏 ⊗ 𝟏 ⟶ 𝟏`"]
theorem hom_comp_one : (ψ.iso p.obj p.obj).hom ≫ p.iso.hom = p.iso.hom := by
  have h₁ := hom_comp_l h p p.obj
  rwa [p.l_self_eq_iso φ, p.r_self_eq_iso φ] at h₁

include h in
/-- Stacks Lemma 0HB0 (2): `id_X ⊗ l_Y = (l_X ⊗ id_Y) ∘ (ψ_{X,𝟏} ⊗ id_Y)` as arrows
`X ⊗ 𝟏 ⊗ Y ⟶ X ⊗ Y`, with the associativity constraint `φ_{X,𝟏,Y}` written out. -/
@[stacks 0HB0 "(2) `id_X ⊗ l_Y = (l_X ⊗ id) ∘ (ψ ⊗ id_Y)`, with the associativity constraint \
written out"]
theorem tensorMap_id_l_eq (X Y : C) :
    tensorMap T (𝟙 X) (p.l φ Y).hom =
      (φ.iso X p.obj Y).hom ≫ tensorMap T (ψ.iso X p.obj).hom (𝟙 Y) ≫
        tensorMap T (p.l φ X).hom (𝟙 Y) := by
  rw [tensorMap_comp_tensorMap, comp_id, hom_comp_l h p X, p.triangle φ]

end CommutativityConstraint

end CategoryTheory

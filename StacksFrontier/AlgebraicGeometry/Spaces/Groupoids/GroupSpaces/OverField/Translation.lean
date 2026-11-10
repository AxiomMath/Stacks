module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Basic

/-!
# Translations of a group algebraic space

Let `G` be a group algebraic space over the terminal presheaf of the big fppf site of `S`, that
is a group object of the slice over that terminal presheaf whose underlying presheaf is an
algebraic space. The morphisms of presheaves `P ⟶ G` form a group, multiplicative in `P`, and a
section `t : h_A ⟶ G` over an object `A` of the site gives the right and left translations of
the base change `h_A × G`, which are isomorphisms of presheaves.

## Main definitions

* `AlgebraicGeometry.Space.GroupOverField.homGroup`: the group of morphisms `P ⟶ G`.
* `AlgebraicGeometry.Space.GroupOverField.rightTrans` and
  `AlgebraicGeometry.Space.GroupOverField.leftTrans`: the translations `(φ, x) ↦ (φ, x · t(φ))`
  and `(φ, x) ↦ (φ, t(φ) · x)` of `h_A × G`.

## Main results

* `AlgebraicGeometry.Space.GroupOverField.comp_mul'`: precomposition is multiplicative.
* `AlgebraicGeometry.Space.GroupOverField.comp_rightTrans_hom` and
  `AlgebraicGeometry.Space.GroupOverField.comp_leftTrans_hom`: the translations on generalized
  points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space.GroupOverField

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- The terminal presheaf on the big fppf site of `S`, represented by the terminal object. -/
noncomputable def isTerminalTop : IsTerminal (yoneda.obj (⊤_ (BigFppfOver C S hS))) :=
  terminalIsTerminal.isTerminalObj yoneda _

variable (G : GroupAlgebraicSpace C S hS (yoneda.obj (⊤_ (BigFppfOver C S hS)))
  (isAlgebraicSpace_yoneda C S hS _))

/-- A morphism of presheaves into a group algebraic space over the terminal presheaf, read as a
morphism of the slice over the terminal presheaf. -/
noncomputable def toOver {P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (u : P ⟶ G.obj.X.left) :
    Over.mk (isTerminalTop.from P) ⟶ G.obj.X :=
  Over.homMk u (isTerminalTop.hom_ext _ _)

/-- Morphisms of presheaves into a group algebraic space over the terminal presheaf are the
morphisms of the slice. -/
noncomputable def homEquiv (P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    (P ⟶ G.obj.X.left) ≃ (Over.mk (isTerminalTop.from P) ⟶ G.obj.X) where
  toFun := toOver G
  invFun f := f.left
  left_inv _ := rfl
  right_inv _ := Over.OverMorphism.ext rfl

/-- The group of morphisms of presheaves into a group algebraic space over the terminal
presheaf. -/
noncomputable instance homGroup (P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    Group (P ⟶ G.obj.X.left) :=
  letI : GrpObj G.obj.X := G.obj.grp
  (homEquiv G P).group

/-- `toOver` sends a product of morphisms into `G` to the product of their images in the slice. -/
theorem toOver_mul {P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (u v : P ⟶ G.obj.X.left) :
    letI : GrpObj G.obj.X := G.obj.grp
    toOver G (u * v) = toOver G u * toOver G v :=
  let : GrpObj G.obj.X := G.obj.grp
  (homEquiv G P).apply_symm_apply (toOver G u * toOver G v)

/-- Precomposition with `f` corresponds to composition in the slice with `Over.homMk f`. -/
private theorem homMk_comp_toOver {P P' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : P' ⟶ P)
    (u : P ⟶ G.obj.X.left) :
    (Over.homMk f (isTerminalTop.hom_ext _ _) :
      Over.mk (isTerminalTop.from P') ⟶ Over.mk (isTerminalTop.from P)) ≫ toOver G u =
      toOver G (f ≫ u) := Over.OverMorphism.ext rfl

/-- Precomposition is multiplicative. -/
theorem comp_mul' {P P' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : P' ⟶ P)
    (u v : P ⟶ G.obj.X.left) : f ≫ (u * v) = (f ≫ u) * (f ≫ v) := by
  let : GrpObj G.obj.X := G.obj.grp
  apply (homEquiv G P').injective
  change toOver G (f ≫ (u * v)) = toOver G ((f ≫ u) * (f ≫ v))
  rw [toOver_mul, ← homMk_comp_toOver G f u, ← homMk_comp_toOver G f v, ← MonObj.comp_mul,
    ← toOver_mul]
  rfl

/-- Precomposition commutes with inversion. -/
theorem comp_inv' {P P' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : P' ⟶ P)
    (u : P ⟶ G.obj.X.left) : f ≫ u⁻¹ = (f ≫ u)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← comp_mul', inv_mul_cancel]
  let : GrpObj G.obj.X := G.obj.grp
  apply (homEquiv G P').injective
  change toOver G (f ≫ 1) = toOver G 1
  have h1 : toOver G (1 : P ⟶ G.obj.X.left) = 1 := (homEquiv G P).apply_symm_apply 1
  have h1' : toOver G (1 : P' ⟶ G.obj.X.left) = 1 := (homEquiv G P').apply_symm_apply 1
  rw [← homMk_comp_toOver G f 1, h1, h1', MonObj.comp_one]

/-- Precomposition sends the identity element to the identity element. -/
theorem comp_one' {P P' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : P' ⟶ P) :
    f ≫ (1 : P ⟶ G.obj.X.left) = 1 := by
  have h := comp_mul' G f 1 1
  rw [mul_one] at h
  exact left_eq_mul.mp h |>.symm ▸ rfl

/-- Right translation `(φ, x) ↦ (φ, x · t(φ))` of `h_A × G` by a section `t` of `G` over `A`. -/
noncomputable def rightTrans {A : BigFppfOver C S hS} (t : yoneda.obj A ⟶ G.obj.X.left) :
    (yoneda.obj A ⨯ G.obj.X.left) ≅ (yoneda.obj A ⨯ G.obj.X.left) where
  hom := prod.lift prod.fst (prod.snd * (prod.fst ≫ t))
  inv := prod.lift prod.fst (prod.snd * (prod.fst ≫ t⁻¹))
  hom_inv_id := by
    apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, prod.lift_fst_assoc, Category.id_comp, comp_mul']
      rw [mul_assoc, ← comp_mul', mul_inv_cancel, comp_one', mul_one]
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, prod.lift_fst_assoc, Category.id_comp, comp_mul']
      rw [mul_assoc, ← comp_mul', inv_mul_cancel, comp_one', mul_one]

/-- Left translation `(φ, x) ↦ (φ, t(φ) · x)` of `h_A × G` by a section `t` of `G` over `A`. -/
noncomputable def leftTrans {A : BigFppfOver C S hS} (t : yoneda.obj A ⟶ G.obj.X.left) :
    (yoneda.obj A ⨯ G.obj.X.left) ≅ (yoneda.obj A ⨯ G.obj.X.left) where
  hom := prod.lift prod.fst ((prod.fst ≫ t) * prod.snd)
  inv := prod.lift prod.fst ((prod.fst ≫ t⁻¹) * prod.snd)
  hom_inv_id := by
    apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, prod.lift_fst_assoc, Category.id_comp, comp_mul']
      rw [← mul_assoc, ← comp_mul', inv_mul_cancel, comp_one', one_mul]
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, prod.lift_fst_assoc, Category.id_comp, comp_mul']
      rw [← mul_assoc, ← comp_mul', mul_inv_cancel, comp_one', one_mul]

/-- On a generalized point `a = (φ, x)` of `h_A × G`, right translation by `t` is
`(φ, x · t(φ))`. -/
theorem comp_rightTrans_hom {A : BigFppfOver C S hS} (t : yoneda.obj A ⟶ G.obj.X.left)
    {P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : P ⟶ yoneda.obj A ⨯ G.obj.X.left) :
    a ≫ (rightTrans G t).hom =
      prod.lift (a ≫ prod.fst) ((a ≫ prod.snd) * (a ≫ prod.fst ≫ t)) := by
  apply prod.hom_ext <;> simp [rightTrans, comp_mul']

/-- On a generalized point `a = (φ, x)` of `h_A × G`, left translation by `t` is
`(φ, t(φ) · x)`. -/
theorem comp_leftTrans_hom {A : BigFppfOver C S hS} (t : yoneda.obj A ⟶ G.obj.X.left)
    {P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : P ⟶ yoneda.obj A ⨯ G.obj.X.left) :
    a ≫ (leftTrans G t).hom =
      prod.lift (a ≫ prod.fst) ((a ≫ prod.fst ≫ t) * (a ≫ prod.snd)) := by
  apply prod.hom_ext <;> simp [leftTrans, comp_mul']

end AlgebraicGeometry.Space.GroupOverField

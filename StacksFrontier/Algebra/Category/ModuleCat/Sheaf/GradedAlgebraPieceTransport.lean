module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# Transport of a sheaf of graded algebras along a degreewise isomorphism

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of `ℤ`-graded `R`-algebras and let
`p : ℤ → SheafOfModules R` be a family of sheaves of modules identified degreewise with the
pieces of `A` by isomorphisms `e n : p n ≅ A.piece n`. Then `p` carries a graded algebra
structure, obtained by conjugating the multiplication and the unit of `A` through `e`.

## Main definitions

* `SheafOfModules.GradedAlgebra.transportMul`, `SheafOfModules.GradedAlgebra.transportOne`: the
  conjugated multiplication and unit.
* `SheafOfModules.GradedAlgebra.ofPieceIso`: **the transported graded algebra**, whose pieces
  are `p` by definition.
* `SheafOfModules.GradedAlgebra.ofPieceIsoUnitalHom`: **the transport is an isomorphism of
  sheaves of graded algebras**, given by the comparisons themselves.

## Main results

* `SheafOfModules.GradedAlgebra.ofPieceIso_mul_app`,
  `SheafOfModules.GradedAlgebra.ofPieceIso_one_eval`: the multiplication and the unit of the
  transported algebra, on local sections.
* `SheafOfModules.GradedAlgebra.isIso_ofPieceIsoUnitalHom_app`: that homomorphism is an
  isomorphism in every degree.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u t a

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

section IsoSections

variable {M N : SheafOfModules.{a} R}

/-- An isomorphism of sheaves of modules cancels its inverse, on local sections. -/
theorem iso_hom_val_app_inv_val_app (f : M ≅ N) (U : Cᵒᵖ) (x : N.val.obj U) :
    f.hom.val.app U (f.inv.val.app U x) = x :=
  congrFun (congrArg (fun g : N ⟶ N => ⇑(ConcreteCategory.hom ((Hom.val g).app U)))
    f.inv_hom_id) x

/-- An isomorphism of sheaves of modules is cancelled by its inverse, on local sections. -/
theorem iso_inv_val_app_hom_val_app (f : M ≅ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    f.inv.val.app U (f.hom.val.app U x) = x :=
  iso_hom_val_app_inv_val_app f.symm U x

end IsoSections

namespace GradedAlgebra

variable (A : GradedAlgebra.{t, a} R) {p : ℤ → SheafOfModules.{a} R}
  (e : ∀ n, p n ≅ A.piece n)

/-- Applying the inverse comparisons to the two sides of an `HEq` between sections of two
pieces of `A` in equal degrees gives an `HEq` between their images in the corresponding pieces
of `p`. -/
theorem heq_inv_val_app (U : Cᵒᵖ) {m n : ℤ} (hmn : m = n)
    {x : (A.piece m).val.obj U} {y : (A.piece n).val.obj U} (h : HEq x y) :
    HEq ((e m).inv.val.app U x) ((e n).inv.val.app U y) := by
  subst hmn
  rw [eq_of_heq h]

/-- The multiplication of `A`, conjugated onto the pieces `p`. -/
def transportMul (i j : ℤ) : BilinearMap (p i) (p j) (p (i + j)) :=
  (((A.mul i j).compLeft (e i).hom.val).compRight (e j).hom.val).postcomp (e (i + j)).inv.val

/-- The value of `transportMul A e i j` on a pair of local sections. -/
@[simp]
theorem transportMul_app (i j : ℤ) (U : Cᵒᵖ) (x : (p i).val.obj U) (y : (p j).val.obj U) :
    (transportMul A e i j).app U x y =
      (e (i + j)).inv.val.app U
        ((A.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y)) :=
  rfl

/-- The unit of `A`, carried to a global section of `p 0`. -/
def transportOne : (p 0).sections :=
  SheafOfModules.sectionsMap (e 0).inv A.one

/-- The value of `transportOne A e` on an object `U`. -/
@[simp]
theorem transportOne_eval (U : Cᵒᵖ) :
    (transportOne A e).eval U = (e 0).inv.val.app U (A.one.eval U) :=
  rfl

/-- **A sheaf of graded algebras transported along a degreewise isomorphism of its pieces.**
The pieces are the given family `p`, by definition; the multiplication and the unit are those of
`A` conjugated through the comparisons. -/
def ofPieceIso : GradedAlgebra.{t, a} R where
  piece := p
  mul := transportMul A e
  one := transportOne A e
  mul_assoc i j k U x y z := by
    simp only [transportMul_app, iso_hom_val_app_inv_val_app]
    exact heq_inv_val_app A e U (add_assoc i j k) (A.mul_assoc i j k U _ _ _)
  one_mul i U x := by
    simp only [transportMul_app, transportOne_eval, iso_hom_val_app_inv_val_app]
    exact (heq_inv_val_app A e U (zero_add i)
        (A.one_mul i U ((e i).hom.val.app U x))).trans
      (heq_of_eq (iso_inv_val_app_hom_val_app (e i) U x))
  mul_one i U x := by
    simp only [transportMul_app, transportOne_eval, iso_hom_val_app_inv_val_app]
    exact (heq_inv_val_app A e U (add_zero i)
        (A.mul_one i U ((e i).hom.val.app U x))).trans
      (heq_of_eq (iso_inv_val_app_hom_val_app (e i) U x))

/-- The pieces of `ofPieceIso A e` are the family `p`. -/
theorem ofPieceIso_piece (n : ℤ) : (ofPieceIso A e).piece n = p n := rfl

/-- The multiplication of `ofPieceIso A e` on local sections is that of `A`, conjugated through
`e`. -/
theorem ofPieceIso_mul_app (i j : ℤ) (U : Cᵒᵖ) (x : (p i).val.obj U) (y : (p j).val.obj U) :
    ((ofPieceIso A e).mul i j).app U x y =
      (e (i + j)).inv.val.app U
        ((A.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y)) :=
  rfl

/-- The unit of `ofPieceIso A e` on an object `U` is the image of the unit of `A` under the
inverse comparison in degree `0`. -/
theorem ofPieceIso_one_eval (U : Cᵒᵖ) :
    (ofPieceIso A e).one.eval U = (e 0).inv.val.app U (A.one.eval U) :=
  rfl

/-- **The transport is an isomorphism of sheaves of graded algebras**: the comparisons
themselves are a unital homomorphism `ofPieceIso A e ⟶ A`. -/
def ofPieceIsoUnitalHom : UnitalHom (ofPieceIso A e) A where
  app n := (e n).hom
  map_mul i j U x y :=
    iso_hom_val_app_inv_val_app (e (i + j)) U
      ((A.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y))
  map_one U := iso_hom_val_app_inv_val_app (e 0) U (A.one.eval U)

/-- The degree-`n` component of `ofPieceIsoUnitalHom A e` is `(e n).hom`. -/
@[simp] theorem ofPieceIsoUnitalHom_app (n : ℤ) :
    (ofPieceIsoUnitalHom A e).app n = (e n).hom :=
  rfl

/-- Every homogeneous component of `ofPieceIsoUnitalHom` is an isomorphism. -/
instance isIso_ofPieceIsoUnitalHom_app (n : ℤ) : IsIso ((ofPieceIsoUnitalHom A e).app n) :=
  (e n).isIso_hom

end GradedAlgebra

end SheafOfModules

end

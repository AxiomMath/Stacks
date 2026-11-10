module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Group and module objects built from a group structure on the points

In a cartesian monoidal category a monoid object `G` is the same thing as a monoid structure on
each set `Q ⟶ G` of points of `G`, compatible with precomposition: the structure morphisms are
recovered by evaluating the point-level operations on the projections out of `G ⊗ G`, and
conversely `g * h = lift g h ≫ μ`.

This file provides the passage from the points to the structure morphisms.
`CategoryTheory.monObjOfHoms`, `CategoryTheory.grpObjOfHoms` and
`CategoryTheory.modObjOfHoms` build a monoid, a group and a module object out of operations on
points, and the `_hom_` lemmas say that the operations the resulting objects induce on points
are the given ones. The unitors and the associator of the ambient category are discharged once
here, so a consumer never mentions them.

## Main definitions

* `CategoryTheory.monObjOfHoms`: a monoid object from a monoid structure on points.
* `CategoryTheory.grpObjOfHoms`: a group object from a group structure on points.
* `CategoryTheory.modObjOfHoms`: an action of a monoid object from an action on points.

## Main results

* `CategoryTheory.monObjOfHoms_hom_one`, `CategoryTheory.monObjOfHoms_hom_mul` and
  `CategoryTheory.grpObjOfHoms_hom_inv`: the operations induced on the points of the resulting
  object are the given ones.
* `CategoryTheory.modObjOfHoms_hom_smul`: the same for the action.
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory MonoidalCategory
open scoped MonObj ModObj

namespace CategoryTheory

universe v u

/-- The first projection out of `𝟙_ C ⊗ P`, composed with the unit of a monoid object `G`, is
the unit of the monoid of points of `G` over `𝟙_ C ⊗ P`. -/
private theorem fst_comp_one {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G P : C) [MonObj G] :
    fst (𝟙_ C) P ≫ (MonObj.one : 𝟙_ C ⟶ G) = (1 : 𝟙_ C ⊗ P ⟶ G) := by
  rw [toUnit_unique (fst (𝟙_ C) P) (toUnit (𝟙_ C ⊗ P))]
  rfl

/-- The first projection out of `(G ⊗ G) ⊗ P`, composed with the multiplication of a monoid
object `G`, is the product of its two components in the monoid of points. -/
private theorem fst_comp_mul {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G P : C) [MonObj G] :
    fst (G ⊗ G) P ≫ (MonObj.mul : G ⊗ G ⟶ G) =
      (fst (G ⊗ G) P ≫ fst G G) * (fst (G ⊗ G) P ≫ snd G G) := by
  change _ = lift _ _ ≫ (MonObj.mul : G ⊗ G ⟶ G)
  rw [← comp_lift, lift_fst_snd, Category.comp_id]

/-- **A monoid object from a monoid structure on its points.** Given a unit and a
multiplication on every set of points `Q ⟶ G`, both compatible with precomposition, and the
monoid axioms at every `Q`, the multiplication of `G` is the point-level multiplication of the
two projections out of `G ⊗ G`. -/
@[instance_reducible]
def monObjOfHoms {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C)
    (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k)) :
    MonObj G where
  one := one (𝟙_ C)
  mul := mul (G ⊗ G) (fst G G) (snd G G)
  one_mul := by
    rw [mul_comp, whiskerRight_fst, whiskerRight_snd, one_comp, one_mul, leftUnitor_hom]
  mul_one := by
    rw [mul_comp, whiskerLeft_fst, whiskerLeft_snd, one_comp, mul_one, rightUnitor_hom]
  mul_assoc := by
    rw [mul_comp, whiskerRight_fst, whiskerRight_snd, mul_comp, mul_comp, whiskerLeft_fst,
      whiskerLeft_snd, mul_comp, mul_comp, mul_comp, associator_hom_fst,
      associator_hom_snd_fst, associator_hom_snd_snd, mul_assoc]

/-- The multiplication of `CategoryTheory.monObjOfHoms` read on a pair of points: this is the
form in which the group axioms of `CategoryTheory.grpObjOfHoms` are discharged. -/
private theorem monObjOfHoms_lift_comp_mul {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] (G : C)
    (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k))
    (Q : C) (g h : Q ⟶ G) :
    lift g h ≫
        (monObjOfHoms G one mul one_comp mul_comp one_mul mul_one mul_assoc).mul =
      mul Q g h := by
  change lift g h ≫ mul (G ⊗ G) (fst G G) (snd G G) = _
  rw [mul_comp, lift_fst, lift_snd]

/-- The unit on the points of `CategoryTheory.monObjOfHoms` is the given one. -/
theorem monObjOfHoms_hom_one {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k))
    (Q : C) :
    letI : MonObj G := monObjOfHoms G one mul one_comp mul_comp one_mul mul_one mul_assoc
    (1 : Q ⟶ G) = one Q :=
  one_comp (toUnit Q)

/-- The multiplication on the points of `CategoryTheory.monObjOfHoms` is the given one. -/
theorem monObjOfHoms_hom_mul {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k))
    (Q : C) (g h : Q ⟶ G) :
    letI : MonObj G := monObjOfHoms G one mul one_comp mul_comp one_mul mul_one mul_assoc
    (g * h : Q ⟶ G) = mul Q g h :=
  monObjOfHoms_lift_comp_mul G one mul one_comp mul_comp one_mul mul_one mul_assoc Q g h

/-- **A group object from a group structure on its points.** The inverse of `G` is the
point-level inverse of its identity. -/
@[instance_reducible, sga "3 I 2.1.2" "partial"]
def grpObjOfHoms {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C)
    (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (inv : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k))
    (inv_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (inv Q g) g = one Q)
    (mul_inv : ∀ (Q : C) (g : Q ⟶ G), mul Q g (inv Q g) = one Q) :
    GrpObj G :=
  letI : MonObj G := monObjOfHoms G one mul one_comp mul_comp one_mul mul_one mul_assoc
  { inv := inv G (𝟙 G)
    left_inv := by
      rw [monObjOfHoms_lift_comp_mul G one mul one_comp mul_comp one_mul mul_one mul_assoc,
        show (MonObj.one : 𝟙_ C ⟶ G) = one (𝟙_ C) from rfl, one_comp]
      exact inv_mul G (𝟙 G)
    right_inv := by
      rw [monObjOfHoms_lift_comp_mul G one mul one_comp mul_comp one_mul mul_one mul_assoc,
        show (MonObj.one : 𝟙_ C ⟶ G) = one (𝟙_ C) from rfl, one_comp]
      exact mul_inv G (𝟙 G) }

/-- The unit on the points of `CategoryTheory.grpObjOfHoms` is the given one. -/
theorem grpObjOfHoms_hom_one {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (inv : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k))
    (inv_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (inv Q g) g = one Q)
    (mul_inv : ∀ (Q : C) (g : Q ⟶ G), mul Q g (inv Q g) = one Q)
    (Q : C) :
    letI : GrpObj G :=
      grpObjOfHoms G one mul inv one_comp mul_comp one_mul mul_one mul_assoc inv_mul mul_inv
    (1 : Q ⟶ G) = one Q :=
  one_comp (toUnit Q)

/-- The multiplication on the points of `CategoryTheory.grpObjOfHoms` is the given one. -/
theorem grpObjOfHoms_hom_mul {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (inv : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k))
    (inv_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (inv Q g) g = one Q)
    (mul_inv : ∀ (Q : C) (g : Q ⟶ G), mul Q g (inv Q g) = one Q)
    (Q : C) (g h : Q ⟶ G) :
    letI : GrpObj G :=
      grpObjOfHoms G one mul inv one_comp mul_comp one_mul mul_one mul_assoc inv_mul mul_inv
    (g * h : Q ⟶ G) = mul Q g h :=
  monObjOfHoms_lift_comp_mul G one mul one_comp mul_comp one_mul mul_one mul_assoc Q g h

/-- The inverse on the points of `CategoryTheory.grpObjOfHoms` is the given one, provided the
point-level inverse is compatible with precomposition. -/
theorem grpObjOfHoms_hom_inv {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) (one : ∀ Q : C, Q ⟶ G) (mul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G) → (Q ⟶ G))
    (inv : ∀ Q : C, (Q ⟶ G) → (Q ⟶ G))
    (one_comp : ∀ {Q R : C} (r : R ⟶ Q), r ≫ one Q = one R)
    (mul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ G),
      r ≫ mul Q g h = mul R (r ≫ g) (r ≫ h))
    (one_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (one Q) g = g)
    (mul_one : ∀ (Q : C) (g : Q ⟶ G), mul Q g (one Q) = g)
    (mul_assoc : ∀ (Q : C) (g h k : Q ⟶ G),
      mul Q (mul Q g h) k = mul Q g (mul Q h k))
    (inv_mul : ∀ (Q : C) (g : Q ⟶ G), mul Q (inv Q g) g = one Q)
    (mul_inv : ∀ (Q : C) (g : Q ⟶ G), mul Q g (inv Q g) = one Q)
    (inv_comp : ∀ {Q R : C} (r : R ⟶ Q) (g : Q ⟶ G), r ≫ inv Q g = inv R (r ≫ g))
    (Q : C) (g : Q ⟶ G) :
    letI : GrpObj G :=
      grpObjOfHoms G one mul inv one_comp mul_comp one_mul mul_one mul_assoc inv_mul mul_inv
    g ≫ GrpObj.inv = inv Q g := by
  change g ≫ inv G (𝟙 G) = inv Q g
  rw [inv_comp, Category.comp_id]

/-- **An action of a monoid object from an action on its points.** An action of `G` on `P` is
an action of the points of `G` on the points of `P`, compatible with precomposition; the action
morphism is obtained by acting with the first projection out of `G ⊗ P` on the second. -/
@[instance_reducible]
def modObjOfHoms {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {G : C} [MonObj G]
    (P : C) (smul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ P) → (Q ⟶ P))
    (smul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g : Q ⟶ G) (p : Q ⟶ P),
      r ≫ smul Q g p = smul R (r ≫ g) (r ≫ p))
    (one_smul : ∀ (Q : C) (p : Q ⟶ P), smul Q 1 p = p)
    (mul_smul : ∀ (Q : C) (g h : Q ⟶ G) (p : Q ⟶ P),
      smul Q (g * h) p = smul Q g (smul Q h p)) :
    ModObj G P where
  smul := smul (G ⊗ P) (fst G P) (snd G P)
  one_smul := by
    change (MonObj.one : 𝟙_ C ⟶ G) ▷ P ≫ smul (G ⊗ P) (fst G P) (snd G P) = (λ_ P).hom
    rw [smul_comp, whiskerRight_fst, whiskerRight_snd, leftUnitor_hom, fst_comp_one G P,
      one_smul]
  mul_smul := by
    change (MonObj.mul : G ⊗ G ⟶ G) ▷ P ≫ smul (G ⊗ P) (fst G P) (snd G P) =
      (α_ G G P).hom ≫ G ◁ smul (G ⊗ P) (fst G P) (snd G P) ≫
        smul (G ⊗ P) (fst G P) (snd G P)
    simpa only [smul_comp, whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst,
      whiskerLeft_snd, associator_hom_fst, associator_hom_snd_fst, associator_hom_snd_snd,
      fst_comp_mul G P] using
      mul_smul ((G ⊗ G) ⊗ P) (fst (G ⊗ G) P ≫ fst G G) (fst (G ⊗ G) P ≫ snd G G)
        (snd (G ⊗ G) P)

/-- The action on the points of `CategoryTheory.modObjOfHoms` is the given one. -/
theorem modObjOfHoms_hom_smul {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {G : C} [MonObj G] (P : C) (smul : ∀ Q : C, (Q ⟶ G) → (Q ⟶ P) → (Q ⟶ P))
    (smul_comp : ∀ {Q R : C} (r : R ⟶ Q) (g : Q ⟶ G) (p : Q ⟶ P),
      r ≫ smul Q g p = smul R (r ≫ g) (r ≫ p))
    (one_smul : ∀ (Q : C) (p : Q ⟶ P), smul Q 1 p = p)
    (mul_smul : ∀ (Q : C) (g h : Q ⟶ G) (p : Q ⟶ P),
      smul Q (g * h) p = smul Q g (smul Q h p))
    (Q : C) (g : Q ⟶ G) (p : Q ⟶ P) :
    letI : ModObj G P := modObjOfHoms P smul smul_comp one_smul mul_smul
    g • p = smul Q g p := by
  let : ModObj G P := modObjOfHoms P smul smul_comp one_smul mul_smul
  rw [show (g • p) = lift g p ≫ ModObj.smul (M := G) (X := P) from rfl]
  change lift g p ≫ smul (G ⊗ P) (fst G P) (snd G P) = _
  rw [smul_comp, lift_fst, lift_snd]

/-- **A morphism of monoid objects whose point-level monoid structures are given is a
homomorphism as soon as it is one on points.** -/
theorem isMonHom_of_homs {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X Y : C}
    (oneX : ∀ Q : C, Q ⟶ X) (mulX : ∀ Q : C, (Q ⟶ X) → (Q ⟶ X) → (Q ⟶ X))
    (one_compX : ∀ {Q R : C} (r : R ⟶ Q), r ≫ oneX Q = oneX R)
    (mul_compX : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ X),
      r ≫ mulX Q g h = mulX R (r ≫ g) (r ≫ h))
    (one_mulX : ∀ (Q : C) (g : Q ⟶ X), mulX Q (oneX Q) g = g)
    (mul_oneX : ∀ (Q : C) (g : Q ⟶ X), mulX Q g (oneX Q) = g)
    (mul_assocX : ∀ (Q : C) (g h k : Q ⟶ X),
      mulX Q (mulX Q g h) k = mulX Q g (mulX Q h k))
    (oneY : ∀ Q : C, Q ⟶ Y) (mulY : ∀ Q : C, (Q ⟶ Y) → (Q ⟶ Y) → (Q ⟶ Y))
    (one_compY : ∀ {Q R : C} (r : R ⟶ Q), r ≫ oneY Q = oneY R)
    (mul_compY : ∀ {Q R : C} (r : R ⟶ Q) (g h : Q ⟶ Y),
      r ≫ mulY Q g h = mulY R (r ≫ g) (r ≫ h))
    (one_mulY : ∀ (Q : C) (g : Q ⟶ Y), mulY Q (oneY Q) g = g)
    (mul_oneY : ∀ (Q : C) (g : Q ⟶ Y), mulY Q g (oneY Q) = g)
    (mul_assocY : ∀ (Q : C) (g h k : Q ⟶ Y),
      mulY Q (mulY Q g h) k = mulY Q g (mulY Q h k))
    (k : X ⟶ Y) (hone : ∀ Q : C, oneX Q ≫ k = oneY Q)
    (hmul : ∀ (Q : C) (g h : Q ⟶ X), mulX Q g h ≫ k = mulY Q (g ≫ k) (h ≫ k)) :
    letI : MonObj X := monObjOfHoms X oneX mulX one_compX mul_compX one_mulX mul_oneX mul_assocX
    letI : MonObj Y := monObjOfHoms Y oneY mulY one_compY mul_compY one_mulY mul_oneY mul_assocY
    IsMonHom k := by
  let : MonObj X := monObjOfHoms X oneX mulX one_compX mul_compX one_mulX mul_oneX mul_assocX
  let : MonObj Y := monObjOfHoms Y oneY mulY one_compY mul_compY one_mulY mul_oneY mul_assocY
  constructor
  · exact hone (𝟙_ C)
  · change mulX (X ⊗ X) (fst X X) (snd X X) ≫ k =
      (k ⊗ₘ k) ≫ mulY (Y ⊗ Y) (fst Y Y) (snd Y Y)
    rw [hmul, mul_compY, tensorHom_fst, tensorHom_snd]

end CategoryTheory

end

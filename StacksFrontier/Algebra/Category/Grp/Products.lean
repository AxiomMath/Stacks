module

public import Mathlib.Algebra.Category.Grp.Limits

/-!
# The categorical product of abelian groups is the group of functions on the index set

The categorical product `∏ᶜ G` of a family `G` of abelian groups in `AddCommGrpCat` is isomorphic
to the group `∀ b, G b` of all functions on the index set, in analogy with `ModuleCat.piIsoPi`
for modules.

## Main definitions

* `AddCommGrpCat.toPi` and `AddCommGrpCat.ofPi` — the two comparison maps: the first reads off
  the components with `CategoryTheory.Limits.Pi.π`, the second is the universal map whose
  component at `b` is evaluation at `b`.
* `AddCommGrpCat.piIsoPi` — **the categorical product of a family of abelian groups is the group
  of functions on the index set**, the `AddCommGrpCat` analogue of `ModuleCat.piIsoPi`.

## Implementation notes

The family is indexed by a `Type v` and takes its values in `AddCommGrpCat.{max v w}`.  This is
forced rather than a restriction: the group of functions on a `Type v` of indices with values in
`AddCommGrpCat.{w'}` lives in `Type (max v w')`, so it is an object of the same category as
`∏ᶜ` only when `v ≤ w'`, and `w' = max v w` says exactly that.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w

noncomputable section

namespace AddCommGrpCat

variable {β : Type v} (G : β → AddCommGrpCat.{max v w}) [HasProduct G]

/-- **Reading an element of the categorical product as a function on the index set**: its value
at `b` is the projection `CategoryTheory.Limits.Pi.π` onto the factor `G b`. -/
def toPi : ∏ᶜ G ⟶ AddCommGrpCat.of (∀ b, (G b : Type (max v w))) :=
  AddCommGrpCat.ofHom
    { toFun := fun s b => (Pi.π G b).hom s
      map_zero' := by funext b; exact (Pi.π G b).hom.map_zero
      map_add' := fun x y => by funext b; exact (Pi.π G b).hom.map_add x y }

/-- **Reading a function on the index set as an element of the categorical product**: the
universal map whose component at `b` is evaluation at `b`. -/
def ofPi : AddCommGrpCat.of (∀ b, (G b : Type (max v w))) ⟶ ∏ᶜ G :=
  Pi.lift fun b => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ b)

/-- The component of `ofPi G` at `b` is evaluation at `b`. -/
@[reassoc]
theorem ofPi_comp_π (b : β) :
    ofPi G ≫ Pi.π G b = AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ b) :=
  Pi.lift_comp_π _ b

/-- Reading an element of the product off as a function and back into the product is the
identity. -/
theorem toPi_comp_ofPi : toPi G ≫ ofPi G = 𝟙 _ :=
  Pi.hom_ext _ _ fun b => by rw [Category.assoc, ofPi_comp_π, Category.id_comp]; rfl

/-- Reading a function into the product and back off it is the identity. -/
theorem ofPi_comp_toPi : ofPi G ≫ toPi G = 𝟙 _ := by
  ext s b
  show (ofPi G ≫ Pi.π G b).hom s = s b
  rw [ofPi_comp_π]
  rfl

/-- **The categorical product of a family of abelian groups is the group of functions on the
index set.**  The `AddCommGrpCat` analogue of `ModuleCat.piIsoPi`. -/
def piIsoPi : ∏ᶜ G ≅ AddCommGrpCat.of (∀ b, (G b : Type (max v w))) where
  hom := toPi G
  inv := ofPi G
  hom_inv_id := toPi_comp_ofPi G
  inv_hom_id := ofPi_comp_toPi G

/-- The component at `b` of the inverse of `piIsoPi G` is evaluation at `b`. -/
@[reassoc (attr := simp)]
theorem piIsoPi_inv_comp_π (b : β) :
    (piIsoPi G).inv ≫ Pi.π G b = AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ b) :=
  ofPi_comp_π G b

/-- The value at `b` of the function `(piIsoPi G).hom s` is the projection of `s` onto `G b`. -/
@[simp]
theorem piIsoPi_hom_apply (s : (∏ᶜ G : AddCommGrpCat.{max v w})) (b : β) :
    (piIsoPi G).hom.hom s b = (Pi.π G b).hom s :=
  rfl

end AddCommGrpCat

end

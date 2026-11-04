module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.CategoryTheory.Shift.Quotient
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory

/-!
# The additive and shifted structure of the homotopy category of differential graded modules

The homotopy category of right differential graded `A`-modules is the quotient of the category
of such modules by the homotopy relation.  This file equips it with the structure a
pretriangulated category is required to carry: it is preadditive, it has a zero object, and it
is acted on by the additive monoid `ℤ` through additive shift functors.

## Main definitions

* `DifferentialGradedModule.Homotopy.add` adds two homotopies, witnessing that the homotopy
  relation is compatible with addition of homomorphisms.
* `DifferentialGradedModule.Homotopy.shift` shifts a homotopy, witnessing that the homotopy
  relation is compatible with the shift.

## Main results

* `DifferentialGradedModule.instPreadditiveHomotopyCategory` and
  `DifferentialGradedModule.instQuotientAdditive`: the homotopy category is preadditive and
  the quotient functor is additive.
* `DifferentialGradedModule.instHasZeroObject` and
  `DifferentialGradedModule.instHasZeroObjectHomotopyCategory`: both the category of
  differential graded modules and its homotopy category have a zero object.
* `DifferentialGradedModule.instHasShiftIntHomotopyCategory` and
  `DifferentialGradedModule.instShiftFunctorHomotopyCategoryAdditive`: the homotopy category
  carries a shift by `ℤ` whose shift functors are additive, and
  `DifferentialGradedModule.quotient_obj_shift` says that the shift of the class of a module
  is the class of its shift.

## Implementation notes

Both compatibilities of the homotopy relation are witnessed by an operation on homotopies
themselves: homotopies are added by adding the underlying right `A`-linear maps, and a
homotopy is shifted by multiplying its underlying map by the sign of the shift.  The sign is
forced: shifting multiplies the differential by that sign, so it enters the homotopy identity
twice, and only a homotopy carrying the sign once makes the two cancel.

Preadditivity, the shift, and the additivity of the shift functors are then the generic
constructions `CategoryTheory.Quotient.preadditive`, `CategoryTheory.HasShift.quotient` and
`CategoryTheory.Functor.additive_of_full_essSurj_comp` applied to the quotient functor, which
is full and essentially surjective.

The zero object of the category of differential graded modules is obtained from the terminal
object: the category has all small products, hence a terminal object, and in a preadditive
category the only endomorphism of a terminal object is zero, so a terminal object is a zero
object.  The zero object of the homotopy category is the class of that one, the quotient
functor being additive.

## References

* [Stacks Project, Tag 09JQ](https://stacks.math.columbia.edu/tag/09JQ)
-/

@[expose] public section

open CategoryTheory Limits

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

section Homotopies

variable {M N : DifferentialGradedModule.{u, v, w} A}

/-- The sum of two homotopies: if `f₁` is homotopic to `f₂` and `g₁` to `g₂`, then `f₁ + g₁` is
homotopic to `f₂ + g₂` by the sum of the two underlying maps. -/
def Homotopy.add {f₁ f₂ g₁ g₂ : Hom M N} (h : Homotopy f₁ f₂) (h' : Homotopy g₁ g₂) :
    Homotopy (f₁ + g₁) (f₂ + g₂) where
  toLinearMap := h.toLinearMap + h'.toLinearMap
  map_grading n x hx :=
    (N.grading (n - 1)).add_mem (h.map_grading n x hx) (h'.map_grading n x hx)
  homotopy_eq x := by
    have hx := h.homotopy_eq x
    have hx' := h'.homotopy_eq x
    simp only [Hom.hom_add_toFun, LinearMap.add_apply, map_add]
    rw [show f₁.toFun x + g₁.toFun x - (f₂.toFun x + g₂.toFun x) =
      (f₁.toFun x - f₂.toFun x) + (g₁.toFun x - g₂.toFun x) by abel, hx, hx']
    abel

/-- The underlying map of the shift of a homotopy: the original map multiplied by the sign of
the shift. -/
def Homotopy.shiftLinearMap {f g : Hom M N} (h : Homotopy f g) (k : ℤ) :
    M.M →ₗ[MulOpposite A.A] N.M where
  toFun x := (k.negOnePow : ℤ) • h.toLinearMap x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' a x := by
    rw [RingHom.id_apply, h.toLinearMap.map_smul]
    exact (map_zsmul (DistribSMul.toAddMonoidHom N.M a) (k.negOnePow : ℤ)
      (h.toLinearMap x)).symm

/-- The underlying map of the shift of a homotopy by `k` sends `x` to `(-1)^k • h x`. -/
@[simp] theorem Homotopy.shiftLinearMap_apply {f g : Hom M N} (h : Homotopy f g) (k : ℤ)
    (x : M.M) : h.shiftLinearMap k x = (k.negOnePow : ℤ) • h.toLinearMap x := rfl

/-- The shift of a homotopy by an integer `k`.  Shifting multiplies the differential by
`(-1)^k`, so the underlying map of the homotopy is multiplied by `(-1)^k` as well: the sign
then occurs twice in the homotopy identity and cancels. -/
def Homotopy.shift {f g : Hom M N} (h : Homotopy f g) (k : ℤ) :
    Homotopy (shiftMap f k) (shiftMap g k) where
  toLinearMap := h.shiftLinearMap k
  map_grading n x hx := by
    have hx' : h.toLinearMap x ∈ N.grading (n + k - 1) := h.map_grading (n + k) x hx
    change (k.negOnePow : ℤ) • h.toLinearMap x ∈ N.grading (n - 1 + k)
    rw [show n - 1 + k = n + k - 1 by ring]
    exact zsmul_mem hx' _
  homotopy_eq x := by
    have hsq : ((k.negOnePow : ℤ) * (k.negOnePow : ℤ)) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
    simp only [shiftMap_toFun, shift_d, Homotopy.shiftLinearMap_apply, LinearMap.smul_apply,
      Units.smul_def, map_zsmul, smul_smul, hsq, one_smul]
    exact h.homotopy_eq x

end Homotopies

/-- Homotopy of homomorphisms of differential graded modules is compatible with addition. -/
theorem homotopyRel_add {M N : DifferentialGradedModule.{u, v, w} A}
    (f₁ f₂ g₁ g₂ : M ⟶ N) (hf : homotopyRel.{u, v, w} A f₁ f₂)
    (hg : homotopyRel.{u, v, w} A g₁ g₂) :
    homotopyRel.{u, v, w} A (f₁ + g₁) (f₂ + g₂) :=
  ⟨hf.some.add hg.some⟩

/-- The homotopy category of differential graded modules is preadditive: homotopy is compatible
with addition of homomorphisms. -/
instance instPreadditiveHomotopyCategory :
    Preadditive (HomotopyCategory.{u, v, w} A) :=
  Quotient.preadditive _ (by
    rintro _ _ f₁ f₂ g₁ g₂ hf hg
    exact homotopyRel_add f₁ f₂ g₁ g₂ hf hg)

/-- The quotient functor to the homotopy category is additive. -/
instance instQuotientAdditive : (toHomotopyCategory.{u, v, w} A).Additive :=
  Quotient.functor_additive _ (by
    rintro _ _ f₁ f₂ g₁ g₂ hf hg
    exact homotopyRel_add f₁ f₂ g₁ g₂ hf hg)

/-- Right differential graded `A`-modules have a zero object: the category has all small
products, hence a terminal object, and in a preadditive category a terminal object is a zero
object. -/
instance instHasZeroObject : HasZeroObject (DifferentialGradedModule.{u, v, w} A) := by
  have : HasFiniteProducts (DifferentialGradedModule.{u, v, w} A) :=
    hasFiniteProducts_of_hasProducts.{w} _
  refine IsZero.hasZeroObject (X := ⊤_ (DifferentialGradedModule.{u, v, w} A)) ?_
  rw [IsZero.iff_id_eq_zero]
  exact terminalIsTerminal.hom_ext _ _

open ZeroObject in
/-- The homotopy category of differential graded modules has a zero object, the class of a zero
module. -/
instance instHasZeroObjectHomotopyCategory :
    HasZeroObject (HomotopyCategory.{u, v, w} A) :=
  ⟨(toHomotopyCategory.{u, v, w} A).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (toHomotopyCategory.{u, v, w} A).map_id, id_zero,
      Functor.map_zero]⟩

/-- Homotopy of homomorphisms of differential graded modules is compatible with the shift. -/
instance instIsCompatibleWithShift :
    (homotopyRel.{u, v, w} A).IsCompatibleWithShift ℤ :=
  ⟨fun k _ _ _ _ h => ⟨h.some.shift k⟩⟩

/-- The shift by the additive monoid `ℤ` on the homotopy category of differential graded
modules, induced by the shift on differential graded modules. -/
noncomputable instance instHasShiftIntHomotopyCategory :
    HasShift (HomotopyCategory.{u, v, w} A) ℤ :=
  inferInstanceAs (HasShift (CategoryTheory.Quotient (homotopyRel.{u, v, w} A)) ℤ)

/-- The quotient functor to the homotopy category commutes with the shift. -/
noncomputable instance instQuotientCommShift :
    (toHomotopyCategory.{u, v, w} A).CommShift ℤ :=
  Quotient.functor_commShift (homotopyRel.{u, v, w} A) ℤ

/-- The shift of the class of a differential graded module is the class of its shift. -/
theorem quotient_obj_shift (M : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    ((toHomotopyCategory.{u, v, w} A).obj M)⟦k⟧ = (toHomotopyCategory.{u, v, w} A).obj (M⟦k⟧) :=
  Quotient.functor_obj_shift ..

/-- The class of the shift of a differential graded module, identified with the shift of its
class.  The two objects are equal, by `DifferentialGradedModule.quotient_obj_shift`, but this
isomorphism is natural in the module, which the equality is not: it is the isomorphism witnessing
that the quotient functor commutes with the shift. -/
noncomputable def quotientShiftIso (M : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    (toHomotopyCategory.{u, v, w} A).obj (shift M k) ≅
      ((toHomotopyCategory.{u, v, w} A).obj M)⟦k⟧ :=
  ((toHomotopyCategory.{u, v, w} A).commShiftIso k).app M

section EqToHomSpelling

/- `CategoryTheory.HasShift.quotient` and `CategoryTheory.Quotient.functor_commShift` are marked
irreducible in Mathlib, which is what hides the identification below; the two declarations are
restored to their default reducibility for this one lemma only. -/
attribute [local semireducible] CategoryTheory.HasShift.quotient
  CategoryTheory.Quotient.functor_commShift

/-- The natural comparison isomorphism of `DifferentialGradedModule.quotientShiftIso` is the
transport along the equality `DifferentialGradedModule.quotient_obj_shift` of its two objects.

This identifies the two spellings of the comparison map that the differential graded theory uses:
the triangles built from mapping cones in this chapter use the natural isomorphism, because their
rotation and shift comparisons need its naturality, while the triangle of an admissible short
exact sequence uses the transport.  Being natural, `quotientShiftIso` is the better-shaped of the
two; this lemma routes the transport spelling onto it. -/
theorem quotientShiftIso_hom_eq_eqToHom (M : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    (quotientShiftIso M k).hom =
      eqToHom (quotient_obj_shift.{u, v, w} (A := A) M k).symm :=
  rfl

/-- The inverse form of `DifferentialGradedModule.quotientShiftIso_hom_eq_eqToHom`. -/
theorem quotientShiftIso_inv_eq_eqToHom (M : DifferentialGradedModule.{u, v, w} A) (k : ℤ) :
    (quotientShiftIso M k).inv = eqToHom (quotient_obj_shift.{u, v, w} (A := A) M k) :=
  rfl

end EqToHomSpelling

/-- Naturality of the comparison between the class of a shift and the shift of a class. -/
theorem quotient_map_shiftMap_comp_quotientShiftIso
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) (k : ℤ) :
    (toHomotopyCategory.{u, v, w} A).map (shiftMap f k) ≫ (quotientShiftIso N k).hom =
      (quotientShiftIso M k).hom ≫ ((toHomotopyCategory.{u, v, w} A).map f)⟦k⟧' :=
  ((toHomotopyCategory.{u, v, w} A).commShiftIso k).hom.naturality f

/-- Every shift functor on the homotopy category of differential graded modules is additive:
it becomes additive after composition with the quotient functor, which is full and essentially
surjective. -/
instance instShiftFunctorHomotopyCategoryAdditive (k : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) k).Additive := by
  have : (toHomotopyCategory.{u, v, w} A ⋙
      CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) k).Additive :=
    Functor.additive_of_iso ((toHomotopyCategory.{u, v, w} A).commShiftIso k)
  exact Functor.additive_of_full_essSurj_comp (toHomotopyCategory.{u, v, w} A) _

end DifferentialGradedModule

end

module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback

/-!
# The ring of all local sections of a sheaf of graded algebras

Let `A` be a sheaf of `ℤ`-graded algebras over a sheaf of rings and let `U` be an object of the
site. The local sections of the homogeneous pieces of `A` over `U` form a graded ring in the sense
of `DirectSum.GRing`, and their direct sum

`Tot(A)(U) = ⨁_{n : ℤ} A_n(U)`

is an honest associative unital ring. This is the device that removes the degree transports from
computations in `A`: the associativity and unit laws of a sheaf of graded algebras are stated with
`HEq`, because the two sides of `(x · y) · z = x · (y · z)` live in the pieces of degree `(i + j)
+ k` and `i + (j + k)`, whereas in `Tot(A)(U)` the degree is carried by the element and the two
sides are equal on the nose. A homogeneous identity is proved in `Tot(A)(U)` and transferred back
along the injectivity of `DirectSum.of`.

For an exterior algebra the degree-one generator extends to a ring homomorphism out of the
ordinary exterior algebra of the module of sections, and Mathlib's
`ExteriorAlgebra.ι_mul_prod_list` then gives the vanishing of an ordered product of degree-one
generators with a repeated factor.

## Main definitions

* `SheafOfModules.GradedAlgebra.sectionsPiece`: the local sections over `U` of the degree-`n`
  piece, as the graded family.
* `SheafOfModules.GradedAlgebra.sectionsGRing`: the graded-ring structure on that family.
* `SheafOfModules.GradedAlgebra.totalSections`: the ring `⨁_n A_n(U)` of all local sections.
* `SheafOfModules.GradedAlgebra.totalSectionsOfExterior`: for an exterior algebra with
  degree-one generator `ι`, the ring homomorphism from `ExteriorAlgebra ℤ (M(U))` to
  `Tot(A)(U)` sending a generator to the corresponding degree-one section.

## Main results

* `SheafOfModules.GradedAlgebra.of_mul_of_eq`: the product of two homogeneous summands is the
  summand of the graded product, which is `DirectSum.of_mul_of` in the vocabulary of `A`.
* `SheafOfModules.GradedAlgebra.of_generator_mul_listProd_eq_zero`: **an ordered product of
  degree-one generators with a repeated factor vanishes.** This is the exterior-algebra identity
  `x ∧ y₁ ∧ ⋯ ∧ y_c = 0` for `x` one of the `y_j`, read in `Tot(A)(U)`.

## Implementation notes

The graded-ring structure needs the three structural laws of a sheaf of graded algebras and
nothing else. `DirectSum.GMonoid` wants its laws as equalities of elements of the sigma type
`GradedMonoid`, and `Sigma.ext` turns each of them into the equality of degrees together with the
`HEq` the sheaf-level law supplies.

The integer and natural-number casts are the multiples of the unit, which is forced: in a graded
ring they must land in degree zero and extend the semiring cast.

`totalSectionsOfExterior` only uses that the degree-one generator has square zero, not the
initiality half of `SheafOfModules.GradedAlgebra.IsExteriorAlgebra`; it is therefore stated for a
`SheafOfModules.GradedAlgebra.SquareZero` generator.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

open CategoryTheory

universe t a v₁ u₁

namespace SheafOfModules.GradedAlgebra

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The local sections over `U` of the homogeneous pieces of a sheaf of graded algebras, as a
family of abelian groups indexed by the degree. -/
abbrev sectionsPiece (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ) (n : ℤ) : Type a :=
  (A.piece n).val.obj U

/-- The unit of the graded ring of local sections: the local section over `U` of the global unit
of the algebra. -/
@[instance_reducible]
def sectionsGOne (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    GradedMonoid.GOne (A.sectionsPiece U) :=
  ⟨A.one.eval U⟩

attribute [local instance] sectionsGOne

/-- The multiplication of the graded ring of local sections: the graded multiplication of the
algebra, read on sections over `U`. -/
@[instance_reducible]
def sectionsGMul (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    GradedMonoid.GMul (A.sectionsPiece U) :=
  ⟨fun {i j} x y => (A.mul i j).app U x y⟩

attribute [local instance] sectionsGMul

/-- **The local sections of a sheaf of graded algebras form a graded ring.** The multiplication,
unit, associativity and unit laws are those of the algebra, read on sections over `U`; the
integer casts are the multiples of the unit. -/
@[instance_reducible]
def sectionsGRing (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    DirectSum.GRing (A.sectionsPiece U) where
  mul {i j} x y := (A.mul i j).app U x y
  one := A.one.eval U
  mul_zero x := map_zero _
  zero_mul y := by
    change (A.mul _ _).app U 0 y = 0
    rw [map_zero]
    rfl
  mul_add x y z := map_add _ _ _
  add_mul x y z := by
    change (A.mul _ _).app U (x + y) z = (A.mul _ _).app U x z + (A.mul _ _).app U y z
    rw [map_add]
    rfl
  one_mul := fun ⟨i, x⟩ => Sigma.ext (zero_add i) (A.one_mul i U x)
  mul_one := fun ⟨i, x⟩ => Sigma.ext (add_zero i) (A.mul_one i U x)
  mul_assoc := fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ =>
    Sigma.ext (add_assoc i j k) (A.mul_assoc i j k U x y z)
  natCast n := n • A.one.eval U
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast n := n • A.one.eval U
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc_ofNat n := negSucc_zsmul _ _

attribute [local instance] sectionsGRing

/-- **The ring of all local sections over `U`** of a sheaf of graded algebras: the direct sum of
the sections of the homogeneous pieces, with the graded multiplication. -/
abbrev totalSections (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ) : Type a :=
  DirectSum ℤ (A.sectionsPiece U)

/-- The product of two homogeneous summands of the ring of local sections is the summand of their
graded product. -/
theorem of_mul_of_eq (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ) (i j : ℤ)
    (x : A.sectionsPiece U i) (y : A.sectionsPiece U j) :
    DirectSum.of (A.sectionsPiece U) i x * DirectSum.of (A.sectionsPiece U) j y =
      DirectSum.of (A.sectionsPiece U) (i + j) ((A.mul i j).app U x y) :=
  DirectSum.of_mul_of x y

variable {M : SheafOfModules.{a} R}

/-- **The exterior algebra of the sections maps to the ring of local sections.** For a degree-one
generator of square zero, the ring homomorphism out of the ordinary exterior algebra of the
`ℤ`-module `M(U)` sending a generator to its image in degree one. -/
def totalSectionsOfExterior {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
    (hι : SquareZero ι) (U : Cᵒᵖ) :
    ExteriorAlgebra ℤ (M.val.obj U) →+* A.totalSections U :=
  (ExteriorAlgebra.lift ℤ
    ⟨((DirectSum.of (A.sectionsPiece U) 1).comp
        (ι.val.app U).hom.toAddMonoidHom).toIntLinearMap,
      fun x => by
        change DirectSum.of (A.sectionsPiece U) 1 _ * DirectSum.of (A.sectionsPiece U) 1 _ = 0
        rw [of_mul_of_eq]
        exact (congrArg (DirectSum.of (A.sectionsPiece U) (1 + 1)) (hι U x)).trans
          (map_zero _)⟩).toRingHom

/-- The ring homomorphism out of the exterior algebra of the sections sends a generator to the
corresponding summand in degree one. -/
@[simp]
theorem totalSectionsOfExterior_ι {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
    (hι : SquareZero ι) (U : Cᵒᵖ) (x : M.val.obj U) :
    totalSectionsOfExterior hι U (ExteriorAlgebra.ι ℤ x) =
      DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U x) := by
  show (ExteriorAlgebra.lift ℤ _) (ExteriorAlgebra.ι ℤ x) = _
  rw [ExteriorAlgebra.lift_ι_apply]
  rfl

/-- **An ordered product of degree-one generators with a repeated factor vanishes.** In the ring
of local sections, the product of the image of `g i` with the ordered product of the images of
all the `g j` is zero. -/
theorem of_generator_mul_listProd_eq_zero {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
    (hι : SquareZero ι) (U : Cᵒᵖ) {c : ℕ} (g : Fin c → M.val.obj U) (i : Fin c) :
    DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U (g i)) *
        (List.ofFn fun j => DirectSum.of (A.sectionsPiece U) 1 (ι.val.app U (g j))).prod = 0 := by
  have h := congrArg (totalSectionsOfExterior hι U)
    (ExteriorAlgebra.ι_mul_prod_list (R := ℤ) g i)
  rw [map_mul, map_list_prod, map_zero, List.map_ofFn] at h
  simpa only [Function.comp_def, totalSectionsOfExterior_ι] using h

end SheafOfModules.GradedAlgebra

end

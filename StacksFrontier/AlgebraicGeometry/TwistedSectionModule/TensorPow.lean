module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Functoriality

/-!
# The twisted object as a tensor product: `F ⊙ m ≅ F ⊗ L ^⊗ m`

`Stacks.TwistedSections.twistPow F L` is defined by the recursion `F ⊙ 0 = F`,
`F ⊙ (m + 1) = (F ⊙ m) ⊗ L`, so the object `F ⊙ m` is the left-nested product
`(⋯ ((F ⊗ L) ⊗ L) ⋯) ⊗ L`. This file constructs an isomorphism `F ⊙ m ≅ F ⊗ L ^⊗ m` with the
grouped tensor product, together with an isomorphism `(F ⊙ m) ⊗ L ^⊗ d ≅ F ⊙ (m + d)`. Both use
only the monoidal structure: no invertibility of `L`, no braiding and no additivity. The first is
given by the recursion
`F ⊙ (m + 1) = (F ⊙ m) ⊗ L ≅ (F ⊗ L ^⊗ m) ⊗ L ≅ F ⊗ (L ^⊗ m ⊗ L) = F ⊗ L ^⊗ (m + 1)`,
whiskering the previous step and then reassociating; the base case is the right unitor.

## Main definitions

* `Stacks.TwistedSections.twistPowTensorIso`: the isomorphism `F ⊙ m ≅ F ⊗ L ^⊗ m`.
* `Stacks.TwistedSections.twistPowTensorPowIso`: the isomorphism
  `(F ⊙ m) ⊗ L ^⊗ d ≅ F ⊙ (m + d)`.

## Main results

* `Stacks.TwistedSections.twistPowTensorIso_hom_naturality`: `twistPowTensorIso` is natural in
  `F`, against `Stacks.TwistedSections.twistPowMap` on the left and whiskering by `L ^⊗ m` on
  the right.
* `Stacks.TwistedSections.twistPowTensorPowIso_hom_naturality`: `twistPowTensorPowIso` is
  natural in `F`.

## Implementation notes

The object `Stacks.TwistedSections.twistPow F L m` is not definitionally equal to
`F ⊗ Stacks.TensorPowers.natTensorPow L m`: the two sides differ by one unitor and `m`
associators, so the comparison is an isomorphism rather than an equality of objects.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open Stacks.TensorPowers (natTensorPow)

universe v u

namespace Stacks.TwistedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {F G : C}

/-- The isomorphism `F ⊙ m ≅ F ⊗ L ^⊗ m` between the left-nested product
`Stacks.TwistedSections.twistPow F L m` and the tensor product of `F` with the tensor power
`Stacks.TensorPowers.natTensorPow L m`, built from the right unitor and associators. -/
def twistPowTensorIso (F L : C) : (m : ℕ) → (twistPow F L m ≅ F ⊗ natTensorPow L m)
  | 0 => (ρ_ F).symm
  | m + 1 => whiskerRightIso (twistPowTensorIso F L m) L ≪≫ α_ F (natTensorPow L m) L

/-- In degree `0`, `twistPowTensorIso F L` is the inverse of the right unitor of `F`. -/
@[simp] theorem twistPowTensorIso_zero (F L : C) :
    twistPowTensorIso F L 0 = (ρ_ F).symm := rfl

/-- In degree `m + 1`, `twistPowTensorIso F L` is the degree-`m` isomorphism whiskered by `L`,
followed by the associator. -/
theorem twistPowTensorIso_succ (F L : C) (m : ℕ) :
    twistPowTensorIso F L (m + 1) =
      whiskerRightIso (twistPowTensorIso F L m) L ≪≫ α_ F (natTensorPow L m) L := rfl

/-- `twistPowTensorIso` is natural in `F`: for `φ : F ⟶ G`,
`twistPowMap L φ m ≫ (twistPowTensorIso G L m).hom` equals
`(twistPowTensorIso F L m).hom ≫ φ ▷ natTensorPow L m`. -/
theorem twistPowTensorIso_hom_naturality (L : C) (φ : F ⟶ G) (m : ℕ) :
    twistPowMap L φ m ≫ (twistPowTensorIso G L m).hom =
      (twistPowTensorIso F L m).hom ≫ φ ▷ natTensorPow L m := by
  induction m with
  | zero =>
      have hL : twistPowMap L φ 0 ≫ (twistPowTensorIso G L 0).hom = φ ≫ (ρ_ G).inv := rfl
      have hR : (twistPowTensorIso F L 0).hom ≫ φ ▷ natTensorPow L 0 =
          (ρ_ F).inv ≫ φ ▷ 𝟙_ C := rfl
      rw [hL, hR]
      exact rightUnitor_inv_naturality φ
  | succ m ih =>
      have hL : twistPowMap L φ (m + 1) ≫ (twistPowTensorIso G L (m + 1)).hom =
          twistPowMap L φ m ▷ L ≫ ((twistPowTensorIso G L m).hom ▷ L ≫
            (α_ G (natTensorPow L m) L).hom) := rfl
      have hR : (twistPowTensorIso F L (m + 1)).hom ≫ φ ▷ natTensorPow L (m + 1) =
          ((twistPowTensorIso F L m).hom ▷ L ≫ (α_ F (natTensorPow L m) L).hom) ≫
            φ ▷ (natTensorPow L m ⊗ L) := rfl
      rw [hL, hR, ← Category.assoc, ← comp_whiskerRight, ih, comp_whiskerRight,
        Category.assoc, associator_naturality_left, Category.assoc]

/-- The isomorphism `(F ⊙ m) ⊗ L ^⊗ d ≅ F ⊙ (m + d)`, built from the right unitor and
associators. -/
def twistPowTensorPowIso (F L : C) (m : ℕ) :
    (d : ℕ) → ((twistPow F L m ⊗ natTensorPow L d : C) ≅ twistPow F L (m + d))
  | 0 => ρ_ (twistPow F L m)
  | d + 1 => (α_ (twistPow F L m) (natTensorPow L d) L).symm ≪≫
      whiskerRightIso (twistPowTensorPowIso F L m d) L

/-- In degree `0`, `twistPowTensorPowIso F L m` is the right unitor of `F ⊙ m`. -/
@[simp] theorem twistPowTensorPowIso_zero (F L : C) (m : ℕ) :
    twistPowTensorPowIso F L m 0 = ρ_ (twistPow F L m) := rfl

/-- In degree `d + 1`, `twistPowTensorPowIso F L m` is the inverse associator followed by the
degree-`d` isomorphism whiskered by `L`. -/
theorem twistPowTensorPowIso_succ (F L : C) (m d : ℕ) :
    twistPowTensorPowIso F L m (d + 1) =
      (α_ (twistPow F L m) (natTensorPow L d) L).symm ≪≫
        whiskerRightIso (twistPowTensorPowIso F L m d) L := rfl

/-- `twistPowTensorPowIso` is natural in `F`: for `φ : F ⟶ G`,
`twistPowMap L φ m ▷ natTensorPow L d ≫ (twistPowTensorPowIso G L m d).hom` equals
`(twistPowTensorPowIso F L m d).hom ≫ twistPowMap L φ (m + d)`. -/
theorem twistPowTensorPowIso_hom_naturality (L : C) (φ : F ⟶ G) (m d : ℕ) :
    twistPowMap L φ m ▷ natTensorPow L d ≫ (twistPowTensorPowIso G L m d).hom =
      (twistPowTensorPowIso F L m d).hom ≫ twistPowMap L φ (m + d) := by
  induction d with
  | zero =>
      have hL : twistPowMap L φ m ▷ natTensorPow L 0 ≫ (twistPowTensorPowIso G L m 0).hom =
          twistPowMap L φ m ▷ 𝟙_ C ≫ (ρ_ (twistPow G L m)).hom := rfl
      have hR : (twistPowTensorPowIso F L m 0).hom ≫ twistPowMap L φ (m + 0) =
          (ρ_ (twistPow F L m)).hom ≫ twistPowMap L φ m := rfl
      rw [hL, hR]
      exact rightUnitor_naturality (twistPowMap L φ m)
  | succ d ih =>
      have hL : twistPowMap L φ m ▷ natTensorPow L (d + 1) ≫
            (twistPowTensorPowIso G L m (d + 1)).hom =
          twistPowMap L φ m ▷ (natTensorPow L d ⊗ L) ≫
            ((α_ (twistPow G L m) (natTensorPow L d) L).inv ≫
              (twistPowTensorPowIso G L m d).hom ▷ L) := rfl
      have hR : (twistPowTensorPowIso F L m (d + 1)).hom ≫ twistPowMap L φ (m + (d + 1)) =
          ((α_ (twistPow F L m) (natTensorPow L d) L).inv ≫
            (twistPowTensorPowIso F L m d).hom ▷ L) ≫ twistPowMap L φ (m + d) ▷ L := rfl
      rw [hL, hR, ← Category.assoc, associator_inv_naturality_left, Category.assoc,
        ← comp_whiskerRight, ih, comp_whiskerRight, Category.assoc]

end Stacks.TwistedSections

end

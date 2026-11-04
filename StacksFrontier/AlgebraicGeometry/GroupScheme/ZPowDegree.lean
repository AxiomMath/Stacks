module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by an integer on an abelian variety

Multiplication by an integer `d` on a group scheme `A` is the `d`-th power of the identity in
the group `A ⟶ A` of morphisms into the group object. On an abelian variety, finite local
freeness of multiplication by every nonzero `d`, of degree `|d| ^ (2 * dim A)`, follows from the
case of the natural numbers `n ≥ 2`.

## Main definitions

* `Stacks.Groupoids.invIsoLeft`: inversion on a group object, as an isomorphism of the
  underlying schemes.

## Main results

* `CategoryTheory.GrpObj.inv_comp_zpow_id`: precomposing multiplication by `d` with inversion
  is multiplication by `-d`.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_neg`: multiplication by `-d` is finite
  locally free of the same rank as multiplication by `d`.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_one` and
  `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_neg_one`: multiplication by `1` and by
  `-1` is finite locally free of rank `1`, unconditionally.
* `Stacks.Groupoids.smooth_hom` and `Stacks.Groupoids.isSmoothVariety_hom`: an abelian variety
  is smooth over its ground field.
* `Stacks.Groupoids.isLocallyNoetherian_left`: the underlying scheme of an abelian variety is
  locally Noetherian.
* `Stacks.Groupoids.isFiniteLocallyFree_of_isFinite_of_flat`: a finite flat morphism to the
  underlying scheme of an abelian variety is finite locally free.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_of_two_le`: if multiplication by each
  natural number `n ≥ 2` is finite locally free of rank `n ^ (2 * dim A)`, then multiplication by
  each nonzero integer `d` is finite locally free of rank `|d| ^ (2 * dim A)`.

## Implementation notes

The group structure on `A ⟶ A` is `CategoryTheory.GrpObj.Hom.group`, so multiplication by `d`
is `(𝟙 A) ^ d`. Precomposition with a morphism is a group homomorphism on `- ⟶ A`
(`CategoryTheory.GrpObj.comp_zpow`), so inversion precomposed with multiplication by `d` is
multiplication by `-d`, and precomposition with an isomorphism of the source does not change the
rank of a finite locally free morphism.

Over a locally Noetherian target, finite local freeness is finiteness and flatness (Tag 02KB);
the underlying scheme of an abelian variety is locally Noetherian because its structure morphism
is locally of finite type over the spectrum of a field.

Smoothness is `AlgebraicGeometry.smooth_of_grpObj`, which needs the group-object structure on
`CategoryTheory.Over.mk A.hom` rather than on `A`; the structure is transported by
`inferInstanceAs`.

## References

* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
* [Stacks Project, Tag 0BFC](https://stacks.math.columbia.edu/tag/0BFC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

/-- Inversion precomposed with the `d`-th power of the identity is the `(-d)`-th power of the
identity. -/
theorem inv_comp_zpow_id (d : ℤ) : (ι : G ⟶ G) ≫ (𝟙 G) ^ d = (𝟙 G) ^ (-d) := by
  rw [GrpObj.comp_zpow, Category.comp_id, GrpObj.inv_eq_inv, inv_zpow, ← zpow_neg]

/-- The `(-1)`-st power of the identity of a group object is inversion. -/
theorem zpow_id_neg_one : (𝟙 G) ^ (-1 : ℤ) = (ι : G ⟶ G) := by
  rw [zpow_neg, zpow_one, GrpObj.inv_eq_inv]

end CategoryTheory.GrpObj

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Inversion on a group scheme, as an isomorphism of the underlying schemes. -/
noncomputable def invIsoLeft : A.left ≅ A.left :=
  (Over.forget (Spec (.of k))).mapIso (asIso (ι : A ⟶ A))

/-- The forward morphism of `Stacks.Groupoids.invIsoLeft A` is inversion on the underlying
scheme. -/
theorem invIsoLeft_hom : (invIsoLeft A).hom = (ι : A ⟶ A).left := rfl

/-- Multiplication by `-d` on the underlying scheme is inversion followed by multiplication
by `d`. -/
theorem zpow_id_left_neg (d : ℤ) :
    ((𝟙 A : A ⟶ A) ^ (-d)).left = (invIsoLeft A).hom ≫ ((𝟙 A : A ⟶ A) ^ d).left := by
  rw [← GrpObj.inv_comp_zpow_id, Over.comp_left, invIsoLeft_hom]

/-- Multiplication by `-d` on a group scheme is finite locally free of the same rank as
multiplication by `d`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_neg (d : ℤ) (r : ℕ)
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left r) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ (-d)).left r := by
  rw [zpow_id_left_neg]
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp (invIsoLeft A) _ h

/-- Multiplication by `1` on a group scheme is finite locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_one :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ (1 : ℤ)).left 1 := by
  rw [zpow_one, Over.id_left]
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso (𝟙 A.left)

/-- Multiplication by `-1` on a group scheme, namely inversion, is finite locally free of
rank `1`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_neg_one :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ (-1 : ℤ)).left 1 := by
  exact isFiniteLocallyFreeOfRank_zpow_id_neg A 1 1 (isFiniteLocallyFreeOfRank_zpow_id_one A)

/-- An abelian variety is smooth over its ground field. -/
@[ega "IV 15.6.10" "(iii), special case",
  sga "3 VIB 7.8" "special case",
  sga "7 VIII 4.1" "special case"]
theorem smooth_hom [AlgebraicGeometry.IsAbelianVariety k A] : Smooth A.hom :=
  have : GrpObj (Over.mk A.hom) := inferInstanceAs (GrpObj A)
  AlgebraicGeometry.smooth_of_grpObj A.hom

/-- An abelian variety is a smooth variety. -/
theorem isSmoothVariety_hom [AlgebraicGeometry.IsAbelianVariety k A] :
    IsSmoothVariety k A.hom :=
  have := smooth_hom A
  .mk

/-- The underlying scheme of an abelian variety is locally Noetherian. -/
theorem isLocallyNoetherian_left [AlgebraicGeometry.IsAbelianVariety k A] :
    IsLocallyNoetherian A.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.hom

/-- A finite flat morphism to the underlying scheme of an abelian variety is finite locally
free. -/
theorem isFiniteLocallyFree_of_isFinite_of_flat [AlgebraicGeometry.IsAbelianVariety k A]
    {X : Scheme.{u}} (f : X ⟶ A.left) [IsFinite f] [Flat f] :
    Stacks.Morphisms.IsFiniteLocallyFree f :=
  have := isLocallyNoetherian_left A
  (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian f).mpr
    ⟨‹_›, ‹_›⟩

/-- Multiplication by a nonzero natural number `n` on a group scheme is finite locally free of
rank `n ^ (2 * dim A)` as soon as this holds for every `n ≥ 2`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_natCast
    (hnat : ∀ n : ℕ, 2 ≤ n → Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left (n ^ (2 * abelianVarietyDimension A)))
    (n : ℕ) (hn : n ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left
      (n ^ (2 * abelianVarietyDimension A)) := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h2
  · rw [← h1]
    simpa using isFiniteLocallyFreeOfRank_zpow_id_one A
  · exact hnat n h2

/-- Multiplication by a nonzero integer `d` on a group scheme is finite locally free of degree
`|d| ^ (2 * dim A)`, given that multiplication by every natural number `n ≥ 2` is finite locally
free of degree `n ^ (2 * dim A)`. -/
theorem isFiniteLocallyFreeOfRank_zpow_id_of_two_le
    (hnat : ∀ n : ℕ, 2 ≤ n → Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left (n ^ (2 * abelianVarietyDimension A)))
    (d : ℤ) (hd : d ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left
      (d.natAbs ^ (2 * abelianVarietyDimension A)) := by
  have key := isFiniteLocallyFreeOfRank_zpow_id_natCast A hnat d.natAbs
    (Int.natAbs_ne_zero.mpr hd)
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · rw [show ((d.natAbs : ℤ)) = -d by omega] at key
    simpa using isFiniteLocallyFreeOfRank_zpow_id_neg A (-d) _ key
  · rwa [show ((d.natAbs : ℤ)) = d by omega] at key

end Stacks.Groupoids

end

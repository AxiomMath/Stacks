module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowDegree

/-!
# Multiplication by an integer on an abelian variety

Multiplication by an integer `d` on a group scheme `A` is the `d`-th power of the identity in
the group `A ⟶ A` of morphisms into the group object. On an abelian variety it is proper, locally
of finite presentation and quasi-compact for every `d`, and its finite local freeness is
characterised by conditions on the morphism itself.

## Main results

* `CategoryTheory.GrpObj.zpow_id_comp_zpow_id` and
  `Stacks.Groupoids.zpow_id_left_comp`: multiplication by `e` followed by multiplication by `d`
  is multiplication by `e * d`.
* `Stacks.Groupoids.isProper_zpow_id_left`: multiplication by `d` on an abelian variety is a
  proper morphism, for every `d`.
* `Stacks.Groupoids.locallyOfFinitePresentation_zpow_id_left`: multiplication by `d` is locally
  of finite presentation, for every `d`.
* `Stacks.Groupoids.quasiCompact_zpow_id_left`: multiplication by `d` is quasi-compact, for
  every `d`.
* `Stacks.Groupoids.isFinite_zpow_id_left_iff_isAffineHom` and
  `Stacks.Groupoids.isFinite_zpow_id_left_iff_locallyQuasiFinite`: multiplication by `d` is
  finite if and only if it is affine, and if and only if it is locally quasi-finite.
* `Stacks.Groupoids.isFinite_zpow_id_left_iff_finite_preimage`: multiplication by `d` is finite
  if and only if each of its set-theoretic fibres is a finite set.
* `Stacks.Groupoids.isFiniteLocallyFree_zpow_id_left_iff` and
  `Stacks.Groupoids.isFiniteLocallyFree_zpow_id_left_iff_flat_and_finite_preimage`:
  multiplication by `d` is finite locally free if and only if it is affine and flat, and if and
  only if it is flat with finite fibres.
* `Stacks.Groupoids.isFiniteLocallyFree_zpow_id_left_mul`: if multiplication by `d` and
  multiplication by `e` are finite locally free, so is multiplication by `e * d`.
* `Stacks.Morphisms.isFiniteLocallyFree_of_isIso`: an isomorphism of schemes is finite locally
  free.
* `Stacks.Groupoids.isFiniteLocallyFree_zpow_id_one` and
  `Stacks.Groupoids.isFiniteLocallyFree_zpow_id_left_neg`: multiplication by `1` is finite
  locally free, and multiplication by `-d` is whenever multiplication by `d` is.
* `Stacks.Groupoids.isFiniteLocallyFree_zpow_id_left_iff_forall_prime`: multiplication by every
  nonzero integer is finite locally free if and only if multiplication by every prime is.

## Implementation notes

Multiplication by `d` is a morphism over the ground field, so composing it with the structure
morphism returns the structure morphism (`CategoryTheory.Over.w`). The structure morphism of an
abelian variety is proper, hence separated and quasi-separated, so properness and
quasi-compactness of multiplication by `d` follow by right cancellation
(`AlgebraicGeometry.IsProper.of_comp`, Tag 01W6).

Finiteness is properness together with affineness
(`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`), and also properness together with
local quasi-finiteness by Zariski's main theorem
(`AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite`, Tag 02LS). For a
quasi-compact morphism locally of finite type, local quasi-finiteness is the finiteness of each
set-theoretic fibre.

The composition law holds for a general group object in a cartesian monoidal category:
precomposition with a morphism is a group homomorphism on morphisms into a group object
(`CategoryTheory.GrpObj.comp_zpow`).

## References

* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02KC](https://stacks.math.columbia.edu/tag/02KC)
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

/-- The `e`-th power of the identity of a group object followed by the `d`-th power of the
identity is the `(e * d)`-th power of the identity. -/
theorem zpow_id_comp_zpow_id (d e : ℤ) :
    ((𝟙 G) ^ e) ≫ ((𝟙 G) ^ d) = (𝟙 G) ^ (e * d) := by
  rw [GrpObj.comp_zpow, Category.comp_id, zpow_mul]

end CategoryTheory.GrpObj

namespace Stacks.Morphisms

/-- An isomorphism of schemes is finite locally free. -/
theorem isFiniteLocallyFree_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsFiniteLocallyFree f :=
  have := isFiniteLocallyFreeOfRank_one_of_isIso f
  IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f 1

end Stacks.Morphisms

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Multiplication by `e` followed by multiplication by `d` is multiplication by `e * d`, on the
underlying schemes. -/
theorem zpow_id_left_comp (d e : ℤ) :
    ((𝟙 A : A ⟶ A) ^ e).left ≫ ((𝟙 A : A ⟶ A) ^ d).left =
      ((𝟙 A : A ⟶ A) ^ (e * d)).left := by
  rw [← Over.comp_left, GrpObj.zpow_id_comp_zpow_id]

/-- Multiplication by `d` followed by the structure morphism is the structure morphism. -/
theorem zpow_id_left_comp_hom (d : ℤ) :
    ((𝟙 A : A ⟶ A) ^ d).left ≫ A.hom = A.hom :=
  Over.w _

/-- Multiplication by an integer `d` on an abelian variety is a proper morphism. -/
theorem isProper_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    IsProper ((𝟙 A : A ⟶ A) ^ d).left := by
  have : IsProper (((𝟙 A : A ⟶ A) ^ d).left ≫ A.hom) := by
    rw [zpow_id_left_comp_hom]
    infer_instance
  exact IsProper.of_comp _ A.hom

/-- Multiplication by an integer `d` on an abelian variety is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_zpow_id_left
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ d).left :=
  have := isProper_zpow_id_left A d
  have := isLocallyNoetherian_left A
  inferInstance

/-- Multiplication by an integer `d` on an abelian variety is finite if and only if it is
affine. -/
theorem isFinite_zpow_id_left_iff_isAffineHom
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    IsFinite ((𝟙 A : A ⟶ A) ^ d).left ↔ IsAffineHom ((𝟙 A : A ⟶ A) ^ d).left := by
  rw [AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom]
  exact and_iff_right (isProper_zpow_id_left A d)

/-- Multiplication by an integer `d` on an abelian variety is quasi-compact. -/
theorem quasiCompact_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    QuasiCompact ((𝟙 A : A ⟶ A) ^ d).left := by
  have : QuasiCompact (((𝟙 A : A ⟶ A) ^ d).left ≫ A.hom) := by
    rw [zpow_id_left_comp_hom]
    infer_instance
  exact QuasiCompact.of_comp _ A.hom

/-- Multiplication by an integer `d` on an abelian variety is finite if and only if it is
locally quasi-finite. -/
theorem isFinite_zpow_id_left_iff_locallyQuasiFinite
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    IsFinite ((𝟙 A : A ⟶ A) ^ d).left ↔ LocallyQuasiFinite ((𝟙 A : A ⟶ A) ^ d).left := by
  rw [AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite]
  exact and_iff_right (isProper_zpow_id_left A d)

/-- Multiplication by an integer `d` on an abelian variety is finite if and only if each of its
set-theoretic fibres is a finite set. -/
theorem isFinite_zpow_id_left_iff_finite_preimage
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    IsFinite ((𝟙 A : A ⟶ A) ^ d).left ↔
      ∀ x : A.left, (((𝟙 A : A ⟶ A) ^ d).left ⁻¹' {x}).Finite := by
  have := isProper_zpow_id_left A d
  have := quasiCompact_zpow_id_left A d
  rw [isFinite_zpow_id_left_iff_locallyQuasiFinite A d,
    AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton]

/-- Multiplication by an integer `d` on an abelian variety is finite locally free if and only if
it is affine and flat. -/
theorem isFiniteLocallyFree_zpow_id_left_iff
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left ↔
      IsAffineHom ((𝟙 A : A ⟶ A) ^ d).left ∧ Flat ((𝟙 A : A ⟶ A) ^ d).left := by
  refine ⟨fun h ↦ ⟨h.toIsAffineHom, Stacks.Morphisms.IsFiniteLocallyFree.flat _⟩,
    fun ⟨haff, hflat⟩ ↦ ?_⟩
  have : IsFinite ((𝟙 A : A ⟶ A) ^ d).left :=
    (isFinite_zpow_id_left_iff_isAffineHom A d).mpr haff
  exact isFiniteLocallyFree_of_isFinite_of_flat A _

/-- Multiplication by an integer `d` on an abelian variety is finite locally free if and only if
it is flat and each of its set-theoretic fibres is a finite set. -/
theorem isFiniteLocallyFree_zpow_id_left_iff_flat_and_finite_preimage
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left ↔
      Flat ((𝟙 A : A ⟶ A) ^ d).left ∧
        ∀ x : A.left, (((𝟙 A : A ⟶ A) ^ d).left ⁻¹' {x}).Finite := by
  rw [isFiniteLocallyFree_zpow_id_left_iff A d, and_comm,
    ← isFinite_zpow_id_left_iff_isAffineHom A d, isFinite_zpow_id_left_iff_finite_preimage A d]

/-- If multiplication by `d` and multiplication by `e` are finite locally free, then so is
multiplication by `e * d`. -/
theorem isFiniteLocallyFree_zpow_id_left_mul (d e : ℤ)
    [Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left]
    [Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ e).left] :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ (e * d)).left := by
  rw [← zpow_id_left_comp]
  infer_instance

/-- Multiplication by `1` on a group scheme is finite locally free. -/
theorem isFiniteLocallyFree_zpow_id_one :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ (1 : ℤ)).left :=
  have := isFiniteLocallyFreeOfRank_zpow_id_one A
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

/-- Multiplication by `-d` on a group scheme is finite locally free as soon as multiplication
by `d` is. -/
theorem isFiniteLocallyFree_zpow_id_left_neg (d : ℤ)
    [Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left] :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ (-d)).left := by
  rw [zpow_id_left_neg]
  have : IsIso (invIsoLeft A).hom := (invIsoLeft A).isIso_hom
  have := Stacks.Morphisms.isFiniteLocallyFree_of_isIso (invIsoLeft A).hom
  infer_instance

/-- Multiplication by a nonzero natural number is finite locally free as soon as multiplication
by every prime is. -/
theorem isFiniteLocallyFree_zpow_id_left_natCast_of_forall_prime
    (hp : ∀ p : ℕ, p.Prime →
      Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ (p : ℤ)).left)
    (n : ℕ) (hn : n ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h2
    · rw [← h1, Nat.cast_one]
      exact isFiniteLocallyFree_zpow_id_one A
    · obtain ⟨q, hq, m, rfl⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
      have hm : m ≠ 0 := by rintro rfl; omega
      have hmlt : m < q * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hq.one_lt
      have := ih m hmlt hm
      have := hp q hq
      have key := isFiniteLocallyFree_zpow_id_left_mul A (m : ℤ) (q : ℤ)
      rwa [← Nat.cast_mul] at key

/-- Multiplication by every nonzero integer on a group scheme is finite locally free if and
only if multiplication by every prime number is. -/
theorem isFiniteLocallyFree_zpow_id_left_iff_forall_prime :
    (∀ d : ℤ, d ≠ 0 →
        Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left) ↔
      ∀ p : ℕ, p.Prime →
        Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ (p : ℤ)).left := by
  refine ⟨fun h p hp ↦ h p (by exact_mod_cast hp.ne_zero), fun hp d hd ↦ ?_⟩
  have key := isFiniteLocallyFree_zpow_id_left_natCast_of_forall_prime A hp d.natAbs
    (Int.natAbs_ne_zero.mpr hd)
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · rw [show ((d.natAbs : ℤ)) = -d by omega] at key
    simpa using isFiniteLocallyFree_zpow_id_left_neg A (-d)
  · rwa [show ((d.natAbs : ℤ)) = d by omega] at key

end Stacks.Groupoids

end

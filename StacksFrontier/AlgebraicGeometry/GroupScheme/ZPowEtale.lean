module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs

/-!
# Étaleness of multiplication by an integer on an abelian variety

Multiplication by an integer `d` on an abelian variety over `k` is étale exactly when `d` is
invertible in `k`.  This file proves the cases `|d| ≤ 1` unconditionally and reduces the
statement for a general `d` to the case of a natural number `n ≥ 2`.

## Main results

* `Stacks.Groupoids.etale_zpow_id_one` and `Stacks.Groupoids.etale_zpow_id_neg_one`:
  multiplication by `1` and by `-1` is étale, unconditionally.
* `Stacks.Groupoids.etale_zpow_id_neg_iff`: multiplication by `-d` is étale if and only if
  multiplication by `d` is.
* `Stacks.Groupoids.isClosedImmersion_unit_left`: the unit section of a group scheme over a
  field is a closed immersion.
* `Stacks.Groupoids.not_etale_zpow_id_zero`: multiplication by `0` on a positive-dimensional
  abelian variety is not étale.
* `Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast_of_natAbs_le_one`: **the statement of
  Stacks Tag 0BFH for `|d| ≤ 1`**, unconditionally.
* `Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast_iff_forall_two_le`: **Stacks Tag 0BFH is
  equivalent to its own special case `d = n` a natural number with `n ≥ 2`.**
* `Stacks.Groupoids.etaleAt_identity_zpow_id_iff_isUnit_intCast_of_natAbs_eq_one`: the
  identity-point form of Tag 0BFH for `|d| = 1`, unconditionally.

## Implementation notes

Multiplication by `d` is the `d`-th power of the identity in the group `A ⟶ A` of morphisms into
the group object, as in `StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowDegree`.  The sign of `d`
is removed by precomposition with inversion, `Stacks.Groupoids.zpow_id_left_neg`, because
precomposition with an isomorphism of the source is the only direction in which a morphism
property can be cancelled without a statement about the target.

Multiplication by `0` is the composite of the structure morphism with the unit section, so its
set-theoretic image is the image of the unit section.  That image is closed because the unit
section is a closed immersion — it is a section of a morphism whose target is a one-point space,
which is `AlgebraicGeometry.isClosedImmersion_of_comp_eq_id`, so no separatedness hypothesis is
needed — and it is open because an étale morphism is flat and locally of finite presentation,
hence universally open.  The underlying scheme of an abelian variety is integral, hence
preconnected, so a nonempty clopen subset is everything; that forces the underlying space to be
a single point and the topological Krull dimension to be at most `0`.

The remaining case `|d| ≥ 2` is the content of the source proof: the derivative of `[d]` at the
identity is multiplication by `d` on the tangent space (Tag 0BF5), so étaleness at the identity
is the invertibility of `d`, and the étale locus of a homomorphism of group schemes is empty or
everything.  That case is settled in
`StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleCriterion`, which proves Tag 0BFH for every
integer and with no hypothesis beyond the source's; the equivalences recorded here are
independent of it, and
`Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast_iff_forall_two_le` says in particular that the
reduction to `n ≥ 2` was an equivalence rather than a weakening.

## References

* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Multiplication by `0` on the underlying scheme of a group scheme over a field is the
structure morphism followed by the unit section. -/
theorem zpow_id_left_zero :
    ((𝟙 A : A ⟶ A) ^ (0 : ℤ)).left = A.hom ≫ (η[A]).left := by
  rw [zpow_zero, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]

/-- Multiplication by `1` on a group scheme is étale: it is the identity. -/
theorem etale_zpow_id_one : Etale ((𝟙 A : A ⟶ A) ^ (1 : ℤ)).left := by
  rw [zpow_one, Over.id_left]
  infer_instance

/-- Multiplication by `-1` on a group scheme, namely inversion, is étale: it is an
isomorphism. -/
theorem etale_zpow_id_neg_one : Etale ((𝟙 A : A ⟶ A) ^ (-1 : ℤ)).left := by
  have : IsIso ((𝟙 A : A ⟶ A) ^ (-1 : ℤ)).left := by
    rw [GrpObj.zpow_id_neg_one]
    exact ((Over.forget (Spec (.of k))).mapIso (asIso (ι : A ⟶ A))).isIso_hom
  infer_instance

/-- Multiplication by `-d` on a group scheme is étale if and only if multiplication by `d` is:
the two differ by precomposition with inversion, which is an isomorphism. -/
theorem etale_zpow_id_neg_iff (d : ℤ) :
    Etale ((𝟙 A : A ⟶ A) ^ (-d)).left ↔ Etale ((𝟙 A : A ⟶ A) ^ d).left := by
  rw [zpow_id_left_neg]
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have h : Etale ((invIsoLeft A).inv ≫ (invIsoLeft A).hom ≫ ((𝟙 A : A ⟶ A) ^ d).left) :=
    inferInstance
  rwa [Iso.inv_hom_id_assoc] at h

/-- An integer is invertible in a commutative ring if and only if its negative is. -/
theorem isUnit_intCast_neg_iff (d : ℤ) : IsUnit ((-d : ℤ) : k) ↔ IsUnit ((d : ℤ) : k) := by
  rw [Int.cast_neg, IsUnit.neg_iff]

/-- The unit section of a group scheme over a field is a closed immersion: it is a section of
the structure morphism, whose target is a one-point space. -/
theorem isClosedImmersion_unit_left : IsClosedImmersion (η[A]).left :=
  AlgebraicGeometry.isClosedImmersion_of_comp_eq_id A.hom (η[A]).left (by simp)

/-- Multiplication by `0` on an abelian variety of positive dimension is not étale: its image
is the image of the unit section, which would then be a nonempty clopen subset of an integral,
hence preconnected, space, forcing the dimension to be at most `0`. -/
theorem not_etale_zpow_id_zero [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : 0 < topologicalKrullDim A.left) :
    ¬ Etale ((𝟙 A : A ⟶ A) ^ (0 : ℤ)).left := by
  intro h
  have hss : Subsingleton ↥((𝟙_ (Over (Spec (CommRingCat.of k)))).left) :=
    inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of k)))
  have hsn : Nonempty ↥((𝟙_ (Over (Spec (CommRingCat.of k)))).left) :=
    inferInstanceAs (Nonempty ↥(Spec (CommRingCat.of k)))
  obtain ⟨hflat, -, hfp⟩ := Etale.iff_flat_and_formallyUnramified.mp h
  have hopen : IsOpenMap ((𝟙 A : A ⟶ A) ^ (0 : ℤ)).left := Scheme.Hom.isOpenMap _
  have hcomp : ∀ y : A.left, ((𝟙 A : A ⟶ A) ^ (0 : ℤ)).left y = (η[A]).left (A.hom y) := by
    intro y
    rw [zpow_id_left_zero]
    rfl
  have hr : Set.range ⇑((𝟙 A : A ⟶ A) ^ (0 : ℤ)).left = Set.range ⇑(η[A]).left := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      exact ⟨A.hom y, (hcomp y).symm⟩
    · rintro x ⟨a, rfl⟩
      refine ⟨Nonempty.some inferInstance, ?_⟩
      rw [hcomp, Subsingleton.elim (A.hom (Nonempty.some inferInstance)) a]
  have hclopen : IsClopen (Set.range ⇑(η[A]).left) :=
    ⟨(isClosedImmersion_unit_left A).isClosedEmbedding.isClosed_range,
      hr ▸ hopen.isOpen_range⟩
  have huniv : Set.range ⇑(η[A]).left = Set.univ := hclopen.eq_univ (Set.range_nonempty _)
  have : Subsingleton A.left := (Set.range_eq_univ.mp huniv).subsingleton
  exact absurd hA (not_lt.mpr (topologicalKrullDim_zero_of_discreteTopology A.left))

/-- **Stacks Project, Tag 0BFH for `|d| ≤ 1`.** Multiplication by an integer `d` with
`|d| ≤ 1` on an abelian variety of positive dimension is étale if and only if `d` is
invertible in the ground field: for `d = ±1` both sides hold, and for `d = 0` both fail. -/
theorem etale_zpow_id_iff_isUnit_intCast_of_natAbs_le_one
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : 0 < topologicalKrullDim A.left)
    (d : ℤ) (hd : d.natAbs ≤ 1) :
    Etale ((𝟙 A : A ⟶ A) ^ d).left ↔ IsUnit ((d : ℤ) : k) := by
  obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = -1 := by omega
  · exact iff_of_false (not_etale_zpow_id_zero A hA) (by simp)
  · exact iff_of_true (etale_zpow_id_one A) (by simp)
  · exact iff_of_true (etale_zpow_id_neg_one A) (by simp)

/-- **Stacks Project, Tag 0BFH, reduced to the case of a natural number `n ≥ 2` — and the
reduction is an equivalence.** Multiplication by an integer `d` on an abelian variety of
positive dimension is étale if and only if `d` is invertible in the ground field, for every
`d`, exactly when this holds for every natural number `n ≥ 2`.

The forward implication is trivial — the hypothesis is an instance of the conclusion — so no
generality is lost: the cases `|d| ≤ 1` are proved outright by
`Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast_of_natAbs_le_one`, and the sign of `d` is
removed by `Stacks.Groupoids.etale_zpow_id_neg_iff`. -/
theorem etale_zpow_id_iff_isUnit_intCast_iff_forall_two_le
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : 0 < topologicalKrullDim A.left) :
    (∀ d : ℤ, Etale ((𝟙 A : A ⟶ A) ^ d).left ↔ IsUnit ((d : ℤ) : k)) ↔
      ∀ n : ℕ, 2 ≤ n → (Etale ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left ↔ IsUnit ((n : ℤ) : k)) := by
  refine ⟨fun h n _ ↦ h n, fun hnat d ↦ ?_⟩
  rcases le_or_gt d.natAbs 1 with hle | hlt
  · exact etale_zpow_id_iff_isUnit_intCast_of_natAbs_le_one A hA d hle
  · have key := hnat d.natAbs hlt
    rcases lt_or_gt_of_ne (show d ≠ 0 by omega) with hneg | hpos
    · rwa [show ((d.natAbs : ℤ)) = -d by omega, etale_zpow_id_neg_iff,
        isUnit_intCast_neg_iff] at key
    · rwa [show ((d.natAbs : ℤ)) = d by omega] at key

/-- Multiplication by `1` is étale at every point of a group scheme. -/
theorem etaleAt_zpow_id_one (x : A.left) :
    AlgebraicGeometry.EtaleAt ((𝟙 A : A ⟶ A) ^ (1 : ℤ)).left x :=
  (AlgebraicGeometry.etale_iff_forall_etaleAt _).mp (etale_zpow_id_one A) x

/-- Multiplication by `-1` is étale at every point of a group scheme. -/
theorem etaleAt_zpow_id_neg_one (x : A.left) :
    AlgebraicGeometry.EtaleAt ((𝟙 A : A ⟶ A) ^ (-1 : ℤ)).left x :=
  (AlgebraicGeometry.etale_iff_forall_etaleAt _).mp (etale_zpow_id_neg_one A) x

/-- If multiplication by `d` is étale then it is étale at the identity point.  This is the
direction in which the identity-point form of Tag 0BFH follows from the global form; the
converse direction is the local content of the source proof. -/
theorem etaleAt_identity_of_etale (d : ℤ) (h : Etale ((𝟙 A : A ⟶ A) ^ d).left) :
    AlgebraicGeometry.EtaleAt ((𝟙 A : A ⟶ A) ^ d).left
      ((η[A]).left (IsLocalRing.closedPoint k)) :=
  (AlgebraicGeometry.etale_iff_forall_etaleAt _).mp h _

/-- **Stacks Project, Tag 0BFH at the identity point, for `|d| = 1`.** Multiplication by an
integer `d` with `|d| = 1` is étale at the identity point of a group scheme over a field if and
only if `d` is invertible in the ground field; both sides hold. -/
theorem etaleAt_identity_zpow_id_iff_isUnit_intCast_of_natAbs_eq_one
    (d : ℤ) (hd : d.natAbs = 1) :
    AlgebraicGeometry.EtaleAt ((𝟙 A : A ⟶ A) ^ d).left
        ((η[A]).left (IsLocalRing.closedPoint k)) ↔ IsUnit ((d : ℤ) : k) := by
  obtain rfl | rfl : d = 1 ∨ d = -1 := by omega
  · exact iff_of_true (etaleAt_zpow_id_one A _) (by simp)
  · exact iff_of_true (etaleAt_zpow_id_neg_one A _) (by simp)

end Stacks.Groupoids

end

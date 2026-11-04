module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.CategoryTheory.GrpObjTorsionPoints
public import StacksFrontier.GroupTheory.TorsionCardinalityZMod

/-!
# The `n`-torsion of an abelian variety over an algebraically closed field

Let `k` be an algebraically closed field, let `A` be an abelian variety over `k` of dimension
`g`, and let `n ≥ 1` be invertible in `k`.  The group of `k`-points of the `n`-torsion of `A` is
isomorphic to `(ℤ/nℤ)^{2g}`.  This is Groupoids, Proposition 39.9.11, Stacks Tag 03RP, in the
clause about prime-to-characteristic torsion.

The unit `𝟙_ (Over (Spec (.of k)))` is `Spec k` over itself, so `𝟙_ (Over (Spec (.of k))) ⟶ A` is
the group of `k`-points of `A`; it is commutative by the commutativity clause of Tag 03RP, and
`Additive` of it carries the `n`-torsion subgroup `Submodule.torsionBy ℤ _ (n : ℤ)`.  The
`k`-points of the `n`-torsion of `A` are the `k`-points that multiplication by `n` carries to
the unit section, which is the subtype appearing in the hypothesis below.

## The hypothesis `hdeg`, and what it would take to discharge it

The theorem here is **conditional**: it assumes that for every divisor `d` of `n` the number of
`k`-points killed by `[d]` is `d ^ (2 * dim A)`.  That count is the content of Stacks Tag
**0BFG** — multiplication by `d` is finite locally free of degree `|d| ^ (2 * dim A)` — together
with Tag **0BFH** — `[d]` is étale when `d` is invertible in `k` — which over an algebraically
closed field turns the degree into a count of rational points.  Neither is available in this
library:

* The two forms of 0BFG inside the library take the degree as an explicit hypothesis `hnat`:
  `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_natCast`
  (`StacksFrontier/AlgebraicGeometry/GroupScheme/ZPowDegree.lean:179`) and
  `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_of_two_le` (same file, line 197).
* Tag 0BFH is only *reduced* to the case of a natural number `n ≥ 2`, by
  `Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast_iff_forall_two_le`
  (`StacksFrontier/AlgebraicGeometry/GroupScheme/ZPowEtale.lean:182`).
* The source's route to 0BFG runs through Tag 0BFF, which in this library is itself conditional
  on the theorem of the cube for `A`: `Stacks.Groupoids.nonempty_zpowId_pullback_iso`
  (`StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianVariety/ZPowPullback.lean:421`) takes
  `Stacks.Groupoids.HasTheoremOfTheCube A`
  (`StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianVariety/CubeRelation.lean:194`), and Tag
  0BF4 itself is registered conditionally on Tags 0BDP, 0BF0 and 0BF3 at
  `StacksFrontier/AlgebraicGeometry/Descent/TheoremOfTheCube.lean:283`.  Beyond that, 0BFG needs the
  degree of an invertible module on a proper curve (Tags 0B5X, 0BEV), Euler characteristics
  (Tag 02OG) and multiplicativity of degrees (Tag 0BEX).

So discharging `hdeg` is a separate development, not a missing step of this one.  Everything
*else* in Proposition 39.9.11's prime-to-characteristic clause is unconditional and proved: the
reduction of the point count to the torsion subgroup of the group of points
(`StacksFrontier/CategoryTheory/GrpObjTorsionPoints.lean`) and the structure theory that turns the
counts into `(ℤ/nℤ)^{2g}` (`StacksFrontier/GroupTheory/TorsionCardinalityZMod.lean`).

No tag is registered here: Tag 03RP's attribute is carried elsewhere in the library, by
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, registered at
`StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/AbelianVariety.lean:98`.

## Main results

* `AlgebraicGeometry.IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod`: the
  `n`-torsion of the group of `k`-points is `(ℤ/nℤ)^{2 dim A}`, given the point counts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.IsAbelianVariety

universe u

/-- **The `n`-torsion of an abelian variety over an algebraically closed field**, Stacks Tag
03RP's prime-to-characteristic clause, conditional on the degree of multiplication by `d`.

Let `k` be algebraically closed, let `A` be an abelian variety over `k`, and let `n ≥ 1` be
invertible in `k`.  Assuming that for every divisor `d` of `n` the `k`-points killed by `[d]`
number `d ^ (2 * dim A)` — Stacks Tag 0BFG together with Tag 0BFH, neither of which this
library has; see the module documentation for the file:line evidence and for what discharging it
would take — the `n`-torsion of the group of `k`-points of `A` is isomorphic to
`(ℤ/nℤ)^{2 dim A}`.

Nothing else is assumed: the passage from the point count to the torsion subgroup and the
structure theory that pins the group down are both proved outright. -/
theorem nonempty_torsionBy_points_addEquiv_pi_zmod {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (n : ℕ) (hn : 1 ≤ n) (_hnk : IsUnit (n : k))
    (hdeg : ∀ d : ℕ, d ∣ n →
      Nat.card {p : 𝟙_ (Over (Spec (.of k))) ⟶ A // p ≫ (𝟙 A : A ⟶ A) ^ (d : ℤ) = η[A]}
        = d ^ (2 * Stacks.Groupoids.abelianVarietyDimension A)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin (2 * Stacks.Groupoids.abelianVarietyDimension A) → ZMod n)) := by
  let _inst : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  refine AddCommGroup.nonempty_torsionBy_addEquiv_pi_zmod (by omega) fun d hd => ?_
  rw [CategoryTheory.GrpObj.card_torsionBy_additive_points A d]
  exact hdeg d hd

end AlgebraicGeometry.IsAbelianVariety

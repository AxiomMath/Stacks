module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Torsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleCriterion
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsion of an abelian variety

Let `A` be an abelian variety over a field `k`.  This file proves the parts of Stacks Tag 03RP
about the `n`-torsion group scheme `A[n] = Ker([n] : A → A)`, the kernel of multiplication by an
integer `n` (`CategoryTheory.GrpObj.torsion`).

## Main results

* `Stacks.Groupoids.isCommMonObj_of_isAbelianVariety`: an abelian variety is commutative, as an
  instance (part (2) of Tag 03RP; this is Mathlib's
  `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`); it is what makes `[n]` a
  homomorphism and `A[n]` a group scheme.
* `Stacks.Groupoids.isIso_hom_of_topologicalKrullDim_eq_zero`: a zero-dimensional abelian variety
  is the spectrum of its ground field.
* `Stacks.Groupoids.etale_torsion_iff`: **Tag 03RP, part (6)**, with the zero-dimensional case
  that the source omits.

## Implementation notes

Part (6) follows the source proof.  If `n` is invertible then `[n]` is étale (Tag 0BFH, in the
form `Stacks.Groupoids.etale_zpow_id_of_isUnit`, which does not use Tag 0BFG), and `A[n]` is a
base change of `[n]`.  Conversely, if `A[n]` is étale then it is unramified at its identity, so
`[n]` is unramified at the identity of `A` (Tag 0475), and the derivative of `[n]` there is
multiplication by `n` on a tangent space which is nonzero when `A` has positive dimension;
`Stacks.Groupoids.unramifiedAt_zpow_id_identity_iff_isUnit` packages that computation.

The source states part (6) for every abelian variety, which is false for the zero abelian
variety `Spec k`: there `A[n] = Spec k` is étale for every `n`.  The statement here adds that
case as an alternative, and proves it: in dimension zero the structure morphism of `A` is an
isomorphism, hence so is `[n]`, and `A[n]` is a base change of it.

## References

* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- An abelian variety is commutative (Tag 03RP, part (2)), as an instance. -/
instance isCommMonObj_of_isAbelianVariety [AlgebraicGeometry.IsAbelianVariety k A] :
    IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A

/-- A zero-dimensional abelian variety is the spectrum of its ground field: its structure
morphism is an isomorphism.  The underlying space is irreducible of dimension `0`, hence a point,
so the identity section is a surjective closed immersion into a reduced scheme. -/
theorem isIso_hom_of_topologicalKrullDim_eq_zero [AlgebraicGeometry.IsAbelianVariety k A]
    (h : topologicalKrullDim A.left = 0) : IsIso A.hom := by
  have hsub : Subsingleton A.left := ⟨fun x y =>
    (Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero h.le
      (genericPoint_specializes x)).symm.trans
      (Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero h.le
        (genericPoint_specializes y))⟩
  have : Surjective (η[A]).left := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (η[A]).left
  have hη : (η[A]).left ≫ A.hom = 𝟙 _ := Over.w η[A]
  rw [IsIso.eq_inv_of_hom_inv_id hη]
  infer_instance

/-- **Stacks Project, Tag 03RP, part (6).** Let `A` be an abelian variety over a field `k` and
`n` an integer.  The `n`-torsion group scheme `A[n] = Ker([n] : A → A)` is étale over `k` if and
only if `n` is invertible in `k`, or `A` is zero-dimensional.

The second alternative is a correction of the source, which omits it: for the zero abelian
variety `A = Spec k`, every `A[n]` is `Spec k`, hence étale, also when `n = 0` in `k`.  For a
nonzero abelian variety the statement is the source's. -/
@[stacks 03RP "part (6), with the zero-dimensional case added", sga "3 XII 4.4.2" "partial"]
theorem etale_torsion_iff (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (n : ℤ) :
    Etale (GrpObj.torsion A n).X.hom ↔ topologicalKrullDim A.left = 0 ∨ IsUnit (n : k) := by
  have := locallyOfFinitePresentation_zpow_id_left A n
  constructor
  · intro h
    by_cases hpos : 0 < topologicalKrullDim A.left
    · right
      let s : Spec (.of k) := IsLocalRing.closedPoint k
      refine (unramifiedAt_zpow_id_identity_iff_isUnit k A hpos s n).mp ?_
      rw [← torsionι_left_unit_apply A n s,
        unramifiedAt_iff_of_isPullback (isPullback_torsion_left A n)]
      exact ((AlgebraicGeometry.etaleAt_iff_smoothAt_and_unramifiedAt _ _).mp
        ((AlgebraicGeometry.etale_iff_forall_etaleAt _).mp h _)).2
    · left
      have : Nonempty (TopologicalSpace.IrreducibleCloseds A.left) :=
        ⟨⟨_, (isIrreducible_singleton (x := (η[A]).left (IsLocalRing.closedPoint k))).closure,
          isClosed_closure⟩⟩
      exact le_antisymm (not_lt.mp hpos) Order.krullDim_nonneg
  · rintro (h0 | hu)
    · have := isIso_hom_of_topologicalKrullDim_eq_zero A h0
      have : IsIso (η[A]).left :=
        ⟨⟨A.hom, Over.w η[A], by rw [← cancel_mono A.hom, Category.assoc, Over.w η[A]]; simp⟩⟩
      have : IsIso (GrpObj.torsionι A n).left :=
        (isPullback_torsion_left A n).isIso_fst_of_isIso
      rw [← Over.w (GrpObj.torsionι A n)]
      infer_instance
    · have := etale_zpow_id_of_isUnit k A n hu
      exact etale_torsion_hom A n

end Stacks.Groupoids

end

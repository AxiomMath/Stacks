module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.FibreSubgroup
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace

/-!
# A set of rational points closed under the group law and containing an open set is everything

Let `k` be an algebraically closed field and `A` an abelian variety over `k`. Then:

* every nonempty open subset of `A` contains a `k`-point;
* an open subset of `A` containing every `k`-point is all of `A`;
* a set `S` of `k`-points closed under the group law and containing every `k`-point of an open
  neighbourhood `U` of the unit is the set of all `k`-points.

## Main results

* `Stacks.Groupoids.exists_comp_mem_of_nonempty`: a nonempty open contains a `k`-point.
* `Stacks.Groupoids.eq_top_of_forall_comp_mem`: an open containing every `k`-point is `⊤`.
* `Stacks.Groupoids.forall_of_mul_of_isOpen`: a set of `k`-points closed under the group law and
  containing the `k`-points of an open neighbourhood of the unit is everything.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Over (Spec (.of k))}

/-- **A nonempty open subset of a scheme locally of finite type over an algebraically closed field
contains a `k`-point**. -/
theorem exists_comp_mem_of_nonempty [LocallyOfFiniteType A.hom] (U : A.left.Opens)
    (hU : (U : Set A.left).Nonempty) :
    ∃ a : 𝟙_ (Over (Spec (.of k))) ⟶ A, a.left (IsLocalRing.closedPoint k) ∈ U := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨x, hxU, hxc⟩ := nonempty_inter_closedPoints hU U.2.isLocallyClosed
  let q := (pointEquivClosedPoint A.hom).symm ⟨x, hxc⟩
  refine ⟨Over.homMk q.1 q.2, ?_⟩
  have hqx : q.1 (IsLocalRing.closedPoint k) = x := by
    simpa [q, pointEquivClosedPoint] using
      congrArg Subtype.val ((pointEquivClosedPoint A.hom).apply_symm_apply ⟨x, hxc⟩)
  change q.1 (IsLocalRing.closedPoint k) ∈ U
  rwa [hqx]

/-- **An open subset of a scheme locally of finite type over an algebraically closed field
containing every `k`-point is everything.** -/
theorem eq_top_of_forall_comp_mem [LocallyOfFiniteType A.hom] (O : A.left.Opens)
    (hO : ∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ A, a.left (IsLocalRing.closedPoint k) ∈ O) :
    O = ⊤ := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  by_contra hne
  have hc : ((O : Set A.left)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hne (TopologicalSpace.Opens.ext (by simpa using h))
  obtain ⟨x, hxO, hxc⟩ := nonempty_inter_closedPoints hc O.2.isClosed_compl.isLocallyClosed
  let q := (pointEquivClosedPoint A.hom).symm ⟨x, hxc⟩
  have hqx : q.1 (IsLocalRing.closedPoint k) = x := by
    simpa [q, pointEquivClosedPoint] using
      congrArg Subtype.val ((pointEquivClosedPoint A.hom).apply_symm_apply ⟨x, hxc⟩)
  have h := hO (Over.homMk q.1 q.2)
  change q.1 (IsLocalRing.closedPoint k) ∈ O at h
  rw [hqx] at h
  exact hxO h

variable [GrpObj A]

/-- Let `S` be a set of `k`-points of an abelian variety, closed
under the group law, and containing every `k`-point of an open neighbourhood `U` of the unit.
Then every `k`-point lies in `S`. -/
theorem forall_of_mul_of_isOpen [AlgebraicGeometry.IsAbelianVariety k A]
    (S : (𝟙_ (Over (Spec (.of k))) ⟶ A) → Prop) (hmul : ∀ a b, S a → S b → S (a * b))
    (U : A.left.Opens) (he : η[A].left (IsLocalRing.closedPoint k) ∈ U)
    (hU : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ A, b.left (IsLocalRing.closedPoint k) ∈ U → S b)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : S a := by
  let s : A ⟶ A := (toUnit A ≫ a) * (𝟙 A)⁻¹
  have hs : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ≫ s = a * b⁻¹ := by
    intro b
    rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ← Category.assoc,
      Subsingleton.elim (b ≫ toUnit A) (𝟙 _), Category.id_comp]
  have hpt : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ A,
      s.left (b.left (IsLocalRing.closedPoint k)) =
        (a * b⁻¹).left (IsLocalRing.closedPoint k) := by
    intro b
    rw [← hs b]; rfl
  let V : A.left.Opens := s.left ⁻¹ᵁ U
  have haV : a.left (IsLocalRing.closedPoint k) ∈ V := by
    change s.left (a.left (IsLocalRing.closedPoint k)) ∈ U
    rw [hpt, mul_inv_cancel, Hom.one_def, Subsingleton.elim (toUnit _) (𝟙 _), Category.id_comp]
    exact he
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.2 V.2 ⟨_, he⟩ ⟨_, haV⟩
  obtain ⟨b, hb⟩ := exists_comp_mem_of_nonempty (U ⊓ V) ⟨x, hxU, hxV⟩
  have hbS : S b := hU b hb.1
  have hab : S (a * b⁻¹) := hU _ (by rw [← hpt]; exact hb.2)
  simpa using hmul _ _ hab hbS

end Stacks.Groupoids

end

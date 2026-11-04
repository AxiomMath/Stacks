module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataCoordinates
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ZeroCycleTraceDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of the class of the point `∞` of `𝐏¹_k`

The point `∞` of the projective line `𝐏¹_k` is closed, with residue field `k`
(`Stacks.Chow.residueDegree_eq_one_of_lineConstantSection`), so by Stacks 0FHR its class
`[∞] ∈ CH¹(𝐏¹_k)` has trace `∫_{𝐏¹} γ([∞]) = 1` for every datum (D0)–(D3) satisfying (A), (B),
(C) (`Stacks.WeilCohomology.WeilData.traceCoord_cycleClassCoord_infinityClass`).

## Main definitions

* `Stacks.WeilCohomology.infinityPoint`: the point `∞` of `𝐏¹_k`.
* `Stacks.WeilCohomology.infinityClass`: its class in `CH¹(𝐏¹_k)`.

## References

* [Stacks Project, Tag 0FHR](https://stacks.math.columbia.edu/tag/0FHR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- The point `∞` of `𝐏¹_k`. -/
def infinityPoint : (projectiveLineObj k).obj.left :=
  (WeilData.pointInfinity k).base (IsLocalRing.closedPoint k)

/-- The point `∞` of `𝐏¹_k` is closed. -/
@[ega "II 7.4.14" "partial"]
theorem isClosed_infinityPoint :
    IsClosed ({infinityPoint k} : Set (projectiveLineObj k).obj.left) := by
  have h := (WeilData.pointInfinity k).isClosedEmbedding.isClosedMap _
    (isClosed_singleton (x := IsLocalRing.closedPoint k))
  have he : ({infinityPoint k} : Set (projectiveLineObj k).obj.left) =
      (WeilData.pointInfinity k) '' {IsLocalRing.closedPoint k} :=
    Set.image_singleton.symm
  rw [he]
  exact h

/-- The residue field of `𝐏¹_k` at `∞` has degree `1` over `k`. -/
theorem residueDegree_infinityPoint :
    (projectiveLineObj k).obj.hom.residueDegree (infinityPoint k) = 1 :=
  residueDegree_eq_one_of_lineConstantSection (Spec (.of k)) _ _

/-- The residue field of `𝐏¹_k` at `∞` is separable over `k`. -/
theorem hasSeparableResidueField_infinityPoint :
    HasSeparableResidueField k (projectiveLineObj k).obj.hom (infinityPoint k) := by
  let := residueFieldAlgebra (Y := projectiveLineObj k) (infinityPoint k)
  have h :
      Module.finrank k ((projectiveLineObj k).obj.left.residueField (infinityPoint k)) = 1 := by
    rw [finrank_residueField_eq_residueDegree, residueDegree_infinityPoint]
  have hbot := Subalgebra.bot_eq_top_of_finrank_eq_one h
  refine ⟨fun x ↦ ?_⟩
  have hx : x ∈ (⊥ : Subalgebra k _) := hbot ▸ Algebra.mem_top
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hx
  exact isSeparable_algebraMap a

/-- The class `[∞] ∈ CH¹(𝐏¹_k)` of the point `∞`. -/
def infinityClass : codimensionChowGroup k (projectiveLineObj k).obj.hom 1 :=
  closedSubschemeClass (projectiveLineObj k).obj.hom
    (closedPointHom (isClosed_infinityPoint k) (hasSeparableResidueField_infinityPoint k)).hom.left
    ((1 : ℕ) : ℤ)

namespace WeilData

variable {k} {F : Type w} [Field F] [CharZero F] {W : WeilData k F}

/-- **`∫_{𝐏¹} γ([∞]) = 1`**, in coordinates of the Tate line. -/
theorem traceCoord_cycleClassCoord_infinityClass (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) :
    W.traceCoord (projectiveLineObj k) 1 (isNonemptyEquidimensional_projectiveLineObj k)
      (W.cycleClassCoord (projectiveLineObj k) ((1 : ℕ) : ℤ) (infinityClass k)) = 1 := by
  have h := trace_cycleClass_closedPoint hA hB hC (isNonemptyEquidimensional_projectiveLineObj k)
    (isClosed_infinityPoint k) (hasSeparableResidueField_infinityPoint k)
  rw [residueDegree_infinityPoint] at h
  rw [cycleClassCoord_apply, ← trace_eq_traceCoord]
  exact h.trans Nat.cast_one

end WeilData

end Stacks.WeilCohomology

end

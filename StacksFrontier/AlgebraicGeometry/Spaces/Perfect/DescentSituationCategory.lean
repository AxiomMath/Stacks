module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Reindexing a descent situation

A situation can be reindexed along an order isomorphism of its index set,
`AlgebraicGeometry.Space.DescentSituation.reindex`, and an index set whose cardinality is below a
cardinal of the universe of the site is order isomorphic to one in that universe,
`AlgebraicGeometry.Space.DescentSituation.exists_orderIso_of_lift_mk_lt`. Together they move a
statement about situations indexed in the universe of the site to an arbitrary index universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Reindexing a descent situation along an order isomorphism.** The stages, transition
morphisms and limit of the reindexed situation are those of `D` read through `e`, and its chosen
index is the preimage of the chosen index of `D`. -/
def reindex {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)] (e : J ≃o I) :
    DescentSituation B S hS hZ J where
  system := e.equivalence.functor.op ⋙ D.system
  algebraicSpace j := D.algebraicSpace (e j)
  transition_affine _ := D.transition_affine _
  quasiCompact j := D.quasiCompact (e j)
  quasiSeparated j := D.quasiSeparated (e j)
  limitCone := D.limitCone.whisker e.equivalence.functor.op
  isLimit := D.isLimit.whiskerEquivalence e.equivalence.op
  limitAlgebraicSpace := D.limitAlgebraicSpace
  base := e.symm D.base

/-- A stage of the reindexed situation is the stage of `D` at the image index. -/
theorem reindex_system_obj {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)] (e : J ≃o I)
    (j : J) : (D.reindex e).system.obj (op j) = D.system.obj (op (e j)) :=
  rfl

/-- The limit of the reindexed situation is the limit of `D`. -/
theorem reindex_limitCone_pt {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)] (e : J ≃o I) :
    (D.reindex e).limitCone.pt = D.limitCone.pt :=
  rfl

/-- The chosen index of the reindexed situation lies below `j` exactly when the chosen index of
`D` lies below the image of `j`. -/
theorem reindex_base_le_iff {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)] (e : J ≃o I)
    (j : J) : (D.reindex e).base ≤ j ↔ D.base ≤ e j := by
  exact e.symm_apply_le

omit [IsDirected I (· ≤ ·)] in
/-- **An index set of small cardinality has a model in the universe of the site.** If the
cardinality of a preorder `I`, lifted, is below that of a cardinal `c` of universe `u`, then `I`
is order isomorphic to a preorder in `Type u` of cardinality below `c`, which is directed when
`I` is. -/
theorem exists_orderIso_of_lift_mk_lt {c : Cardinal.{u}}
    (hI : Cardinal.lift.{u} (Cardinal.mk I) < Cardinal.lift.{v} c) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty (J ≃o I)), Cardinal.mk J < c ∧
      (IsDirected I (· ≤ ·) → IsDirected J (· ≤ ·)) := by
  obtain ⟨a, hac, ha⟩ := Cardinal.lt_lift_iff.1 hI
  have hmk : Cardinal.lift.{v} (Cardinal.mk a.out) = Cardinal.lift.{u} (Cardinal.mk I) := by
    rw [Cardinal.mk_out, ha]
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 hmk
  let : Preorder a.out := Preorder.lift e
  let o : a.out ≃o I := ⟨e, Iff.rfl⟩
  refine ⟨a.out, inferInstance, ⟨o⟩, by rw [Cardinal.mk_out]; exact hac, fun hdir => ⟨?_⟩⟩
  intro x y
  obtain ⟨z, hxz, hyz⟩ := hdir.directed (o x) (o y)
  exact ⟨o.symm z, o.le_symm_apply.2 hxz, o.le_symm_apply.2 hyz⟩

end DescentSituation

end AlgebraicGeometry.Space

end

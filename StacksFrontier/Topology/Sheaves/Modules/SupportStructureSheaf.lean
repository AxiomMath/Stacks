module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Topology.Sheaves.Stalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of a sheaf of rings is closed

Let `X` be a topological space and `O` a sheaf of commutative rings on `X`. The support of `O` is
the set of points `x` at which the stalk `O_x` is not the zero ring, that is, at which `1 ≠ 0` in
`O_x`. This file shows that the support is a closed subset of `X`.

## Main definitions

* `StalkIsZero`: the proposition that the stalk of `F` at `x` is the zero ring.
* `sheafRingSupport`: the set of points at which the stalk of `F` is not the zero ring.

## Main results

* `isOpen_compl_sheafRingSupport`: the set of points at which the stalk is the zero ring is open.
* `isClosed_sheafRingSupport`: the support of a sheaf of commutative rings is closed.
-/

@[expose] public section

/-- The stalk of the sheaf of commutative rings `F` at `x` is the zero ring, that is, `1 = 0` in
it. -/
def StalkIsZero {X : TopCat} (F : TopCat.Sheaf CommRingCat X) (x : X) : Prop :=
  (1 : F.presheaf.stalk x) = 0

/-- The support of a sheaf of commutative rings `F` on `X`: the set of points `x` at which the
stalk of `F` is not the zero ring, that is, at which `1 ≠ 0` in the stalk. -/
@[ega "0 3.1.6"]
def sheafRingSupport {X : TopCat} (F : TopCat.Sheaf CommRingCat X) : Set X :=
  {x | (1 : F.presheaf.stalk x) ≠ 0}

/-- A point lies in the support of `F` if and only if the stalk of `F` at it is not the zero
ring. -/
theorem mem_sheafRingSupport_iff {X : TopCat} (F : TopCat.Sheaf CommRingCat X)
    (x : X) :
    x ∈ sheafRingSupport F ↔ ¬ StalkIsZero F x := by
  rfl

/-- The set of points at which the stalk of a sheaf of commutative rings is the zero ring is
open. -/
@[ega "IV 19.1.7" "closed support of O_X/J", sga "3 VIA 2.1.3" "more general"]
theorem isOpen_compl_sheafRingSupport {X : TopCat}
    (F : TopCat.Sheaf CommRingCat X) :
    IsOpen {x : X | (1 : F.presheaf.stalk x) = 0} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  have hgerm : (F.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom 1
      = (F.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x)).hom 0 := by
    rw [map_one, map_zero]; exact hx
  obtain ⟨W, hxW, iU, iV, hW⟩ :=
    F.presheaf.germ_eq x (TopologicalSpace.Opens.mem_top x)
      (TopologicalSpace.Opens.mem_top x)
      (1 : F.presheaf.obj (Opposite.op ⊤)) 0 hgerm
  have hW1 : (1 : F.presheaf.obj (Opposite.op W)) = 0 := by
    have e1 : (F.presheaf.map iU.op).hom (1 : F.presheaf.obj (Opposite.op ⊤)) = 1 :=
      map_one _
    have e2 : (F.presheaf.map iV.op).hom (0 : F.presheaf.obj (Opposite.op ⊤)) = 0 :=
      map_zero _
    rw [e1, e2] at hW
    exact hW
  refine ⟨(W : Set X), ?_, W.isOpen, hxW⟩
  intro y hy
  simp only [Set.mem_ofPred_eq]
  calc (1 : F.presheaf.stalk y) = (F.presheaf.germ W y hy).hom 1 := (map_one _).symm
    _ = (F.presheaf.germ W y hy).hom 0 := by rw [hW1]
    _ = 0 := map_zero _

/-- The support of a sheaf of commutative rings on `X` is a closed subset of `X`. -/
@[stacks 01AV,
  ega "0 5.2.2" "special case",
  ega "I 4.1.2" "more general",
  ega "IV 19.1.7" "closed support of O_X/J", sga "3 VIA 2.1.3" "more general"]
theorem isClosed_sheafRingSupport {X : TopCat} (F : TopCat.Sheaf CommRingCat X) :
    IsClosed (sheafRingSupport F) := by
  rw [← isOpen_compl_iff]
  have hcompl : (sheafRingSupport F)ᶜ = {x : X | (1 : F.presheaf.stalk x) = 0} := by
    ext x
    simp only [sheafRingSupport, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
  rw [hcompl]
  exact isOpen_compl_sheafRingSupport F

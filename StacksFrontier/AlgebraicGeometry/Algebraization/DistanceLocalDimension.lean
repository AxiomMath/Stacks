module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Distance bounded by the local dimension of a point closure

For a point `y` of a Noetherian scheme and a specialization `z` of `y` in a closed
subset `Z`, the distance from `y` to `Z` is at most the dimension of the local ring
of the closure of `y` at `z`.

## Main results

* `Stacks.Algebraization.distanceFunction_le_closureLocalDimension` bounds the
  distance by this local dimension.

## Implementation notes

The local-ring dimension is expressed as the coheight of `z` in the subspace
`closure {y}`. By the stalk-dimension formula (Stacks 02IZ), this is the dimension
of the local ring of the reduced closed subscheme supported on `closure {y}`. The bound
comes from the one-leg system `closure {z} ⊆ closure {y}`, whose weight is the codimension
of the lower endpoint in the upper one.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- The codimension of `A` in `B` is at most the coheight of `A` in the down-set of `B`:
a chain from `A` to `B` is in particular a chain in that down-set. -/
private theorem topCodim_le_coheight_Iic {X : Type u} [TopologicalSpace X]
    (A B : IrreducibleCloseds X) (hAB : A ≤ B) :
    IrreducibleClosedsCodim.topCodim A B ≤ Order.coheight (⟨A, hAB⟩ : Set.Iic B) := by
  rw [IrreducibleClosedsCodim.topCodim_le_iff]
  intro p hh hl
  have hmono (i) : p i ≤ B := by rw [← hl]; exact p.monotone (Fin.le_last i)
  let q : LTSeries (Set.Iic B) := ⟨p.length, fun i => ⟨p i, hmono i⟩, p.step⟩
  exact (Subtype.ext hh : q.head = ⟨A, hAB⟩) ▸ Order.length_le_coheight_head (p := q)

/-- The points of the closure of `y` correspond, order-reversingly in the sense of taking
closures, to the irreducible closed subsets contained in the closure of `y`. -/
private def closurePointOrderIso (Y : Scheme.{u}) (y : Y) :
    {x : Y // x ∈ closure ({y} : Set Y)} ≃o
      {C : IrreducibleCloseds Y // C ≤ IrreducibleCloseds.closureSingleton y} := by
  classical
  let e := irreducibleSetEquivPoints (α := Y)
  refine
    { toFun := fun x => ⟨e.symm x.1, ?_⟩
      invFun := fun C => ⟨e C.1, ?_⟩
      left_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      right_inv := fun C => Subtype.ext (e.symm_apply_apply C.1)
      map_rel_iff' := ?_ }
  · exact isClosed_closure.mem_iff_closure_subset.1 x.2
  · have hm : e C.1 ∈ (C.1 : Set Y) :=
      (C.1.isIrreducible.isGenericPoint_genericPoint C.1.isClosed).mem
    exact C.2 hm
  · intro x x'
    change e.symm x.1 ≤ e.symm x'.1 ↔ x.1 ≤ x'.1
    exact e.symm.map_rel_iff

/-- **Stacks Project, Tag 0EIY.** The distance to `Z` is at most the local dimension of the
closure of `y` at any specialization `z` lying in `Z`. -/
@[stacks 0EIY "le_local_dimension"]
public theorem distanceFunction_le_closureLocalDimension
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y)
    (y z : Y) (hzy : z ∈ closure {y}) (hzZ : z ∈ (Z : Set Y)) :
    (distanceFunction Y Z y : WithBot ℕ∞) ≤
      Order.coheight (⟨z, hzy⟩ : (closure {y} : Set Y)) := by
  classical
  let V := IrreducibleCloseds.closureSingleton z
  let W := IrreducibleCloseds.closureSingleton y
  have hVW : V ≤ W := by
    exact isClosed_closure.mem_iff_closure_subset.1 hzy
  let s : DistanceSystem Y Z y :=
    { k := 0
      V := fun _ => V
      W := fun _ => W
      V_le_W := fun _ => hVW
      V_next_le_W := fun i => Fin.elim0 i
      V_zero_subset := by
        intro x hx
        exact (Z.2.mem_iff_closure_subset.1 hzZ) hx
      W_last_eq_closure := by
        simp [W] }
  have hcomponent : (connectedComponent y ∩ (Z : Set Y)).Nonempty :=
    ⟨z, isClosed_connectedComponent.mem_iff_closure_subset.1 mem_connectedComponent hzy, hzZ⟩
  have hweight : s.weight = (IrreducibleClosedsCodim.topCodim V W).toNat := by
    simp [s, DistanceSystem.weight, DistanceSystem.upCodimension,
      DistanceSystem.downCodimension]
  rw [distanceFunction_eq_iInf_of_nonempty Y Z y hcomponent]
  apply WithBot.coe_le_coe.mpr
  calc
    (⨅ t : DistanceSystem Y Z y, (t.weight : ℕ∞)) ≤ s.weight := iInf_le _ s
    _ = (IrreducibleClosedsCodim.topCodim V W).toNat := by exact_mod_cast hweight
    _ ≤ IrreducibleClosedsCodim.topCodim V W := ENat.natCast_toNat_le_self _
    _ ≤ Order.coheight (⟨V, hVW⟩ : Set.Iic W) := topCodim_le_coheight_Iic V W hVW
    _ = Order.coheight (⟨z, hzy⟩ : (closure {y} : Set Y)) := by
      change Order.coheight ((closurePointOrderIso Y y) ⟨z, hzy⟩) = _
      exact Order.coheight_orderIso (closurePointOrderIso Y y) ⟨z, hzy⟩

end Stacks.Algebraization

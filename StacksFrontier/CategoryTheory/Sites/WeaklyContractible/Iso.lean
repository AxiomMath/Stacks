module

public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Weak contractibility is invariant under isomorphism

Weak contractibility of an object of a site is a statement about the sections of sheaves of sets
over it, so it only depends on the object up to isomorphism.

## Main results

* `CategoryTheory.GrothendieckTopology.IsWeaklyContractible.of_iso`
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

universe v u

variable {C : Type u} [Category.{v} C] [Small.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J (Type v)]

omit [Small.{v} C] [HasSheafify J (Type v)] in
/-- **Weak contractibility is invariant under isomorphism.** A section over the second object is
transported to the first, lifted there, and the lift transported back. -/
theorem IsWeaklyContractible.of_iso {X Y : C} (e : X ≅ Y) (h : J.IsWeaklyContractible X) :
    J.IsWeaklyContractible Y := by
  intro F G φ hφ s
  obtain ⟨t, ht⟩ := h F G φ hφ (G.obj.map e.hom.op s)
  have ht' : φ.hom.app (op X) t = G.obj.map e.hom.op s := ht
  refine ⟨F.obj.map e.inv.op t, ?_⟩
  change φ.hom.app (op Y) (F.obj.map e.inv.op t) = s
  rw [NatTrans.naturality_apply φ.hom e.inv.op t]
  change G.obj.map e.inv.op (φ.hom.app (op X) t) = s
  rw [ht', ← types_comp_apply (G.obj.map e.hom.op) (G.obj.map e.inv.op), ← G.obj.map_comp,
    ← op_comp, e.inv_hom_id, op_id, G.obj.map_id, types_id_apply]

end CategoryTheory.GrothendieckTopology

end

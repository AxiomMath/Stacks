module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.AlgebraicClosureFibreOrbit

/-!
# Condition (1) of Tag 0C4D implies condition (3) over an arbitrary field

A closed point of a scheme locally of finite type over a field is a node exactly when *some*
point of the base change to the algebraic closure above it is an ordinary double point, and the
geometric form of the condition asks that *every* such point be one.  The two agree, over any
base field, because the automorphisms of the algebraic closure act transitively on the points
of the base change above a fixed point.

## Main results

* `Stacks.Curves.exists_isIso_base_eq_of_mem_fibre` — the transitivity statement, in the form
  `Stacks.Curves.forall_isOrdinaryDoublePoint_of_isNode_of_fibre_transitive` consumes.
* `Stacks.Curves.forall_isOrdinaryDoublePoint_of_isNode` — condition (1) of Tag 0C4D implies
  condition (3), over an arbitrary field.

## Implementation notes

The witnessing isomorphism is `AlgebraicGeometry.galoisBaseChangeMap`, the self-map of the base
change induced by a `k`-automorphism of the algebraic closure; it is an isomorphism by
`AlgebraicGeometry.isIso_galoisBaseChangeMap` and it lies over `X`, although the consumer does
not need that.  Transitivity is
`AlgebraicGeometry.exists_galoisBaseChangeMap_base_eq_of_isAlgClosure`, which assumes no
separability — the separable case alone would leave Tag 0C4D open over an imperfect field.

Closedness of the second point of the fibre is not an extra obligation: the consumer transports
it along the underlying homeomorphism of the isomorphism.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 04KP](https://stacks.math.columbia.edu/tag/04KP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.Curves

/-- **The automorphisms of the algebraic closure act transitively on the points of the base
change above a fixed point.**  Stated in the form the fibre-transitivity hypothesis of
`Stacks.Curves.forall_isOrdinaryDoublePoint_of_isNode_of_fibre_transitive` asks for: the
isomorphism is not required to lie over `X`, although the one produced here does. -/
theorem exists_isIso_base_eq_of_mem_fibre
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))] (x : X) :
    let K := AlgebraicClosure k
    let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
    ∀ xbar xbar' : Y, p.base xbar = x → p.base xbar' = x →
      ∃ h : Y ⟶ Y, IsIso h ∧ h.base xbar = xbar' := by
  intro K g Y p xbar xbar' h1 h2
  obtain ⟨σ, hσ⟩ := AlgebraicGeometry.exists_galoisBaseChangeMap_base_eq_of_isAlgClosure
    k K X (X ↘ AlgebraicGeometry.Spec (.of k)) xbar xbar' (h1.trans h2.symm)
  exact ⟨_, AlgebraicGeometry.isIso_galoisBaseChangeMap k K X
    (X ↘ AlgebraicGeometry.Spec (.of k)) σ, hσ⟩

/-- **Condition (1) of Stacks 0C4D implies condition (3), over an arbitrary field.**  If some
point of the base change to the algebraic closure above `x` is an ordinary double point, then
every such point is. -/
theorem forall_isOrdinaryDoublePoint_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X)
    (hnode : IsNode k X x) :
    let K := AlgebraicClosure k
    let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k)) g
    let q : Y ⟶ AlgebraicGeometry.Spec (.of K) :=
      pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g
    letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
    ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar :=
  forall_isOrdinaryDoublePoint_of_isNode_of_fibre_transitive k X x
    (exists_isIso_base_eq_of_mem_fibre k X x) hnode

end Stacks.Curves

end

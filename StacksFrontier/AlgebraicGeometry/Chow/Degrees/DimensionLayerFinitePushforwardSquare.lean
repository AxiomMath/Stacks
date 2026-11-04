module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerFinitePushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# The left-hand square of the finite pushforward diagram on dimension layers

Let `(S, δ)` be a base situation with a dimension function and let `π : X ⟶ Y` be a finite
morphism of schemes locally of finite type over `S`. Tag 0FDR asserts that the two maps of
Tag 02S9,

`Z_k ⟶ K₀(Coh_{≤k}/Coh_{≤k-1})` and `K₀(Coh_{≤k}/Coh_{≤k-1}) ⟶ Z_k`,

commute with proper pushforward of `k`-cycles and direct image along `π` on the Grothendieck
groups of the layers. The right-hand square is
`Stacks.Chow.properPushforwardHom_comp_dimensionLayerCycleHom`. This file proves the left-hand
square at exactly the hypotheses of the tag: `Y` is locally of finite type over the locally
Noetherian base, hence locally Noetherian, and nothing more is asked of it.

## Main results

* `Stacks.Chow.cycleDimensionLayerHom_comp_properPushforwardHom` — the left-hand square.
* `Stacks.Chow.cycleDimensionLayerHom_properPushforwardHom` — the left-hand square read on a
  cycle.
* `Stacks.Chow.finitePushforward_dimensionLayer_diagram_commutes` — both squares of the diagram
  of Tag 0FDR at once.

## Implementation notes

The source deduces the left-hand square from the right-hand one: the horizontal arrows are
bijections. Concretely, for a `k`-cycle `c` on `X`, the composite
`Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ Z_k(X)` is the identity, so `π_* c` is the
pushforward of the cycle class of the element `x` of the layer attached to `c`; the right-hand
square identifies that with the cycle class of `π_* x`; and the composite
`K₀(Coh_{≤k}(Y)/Coh_{≤k-1}(Y)) ⟶ Z_k(Y) ⟶ K₀(Coh_{≤k}(Y)/Coh_{≤k-1}(Y))` is the identity, which
is `Stacks.Chow.cycleDimensionLayerHom_comp_dimensionLayerCycleHom_eq_id`, Tag 02S9 for a scheme
merely locally of finite type over the base.

## References

* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (π : X ⟶ Y) [IsFinite π] (hπ : π ≫ sY = sX) (k : ℤ)

/-- **Stacks 0FDR**, the left-hand square of the diagram. The homomorphism
`Z_k ⟶ K₀(Coh_{≤k}/Coh_{≤k-1})` of Stacks 02S9 commutes with proper pushforward of `k`-cycles on
the source and direct image along the finite morphism `π` on the target.

As in the source, it follows from the right-hand square
`Stacks.Chow.properPushforwardHom_comp_dimensionLayerCycleHom` because the two maps of Tag 02S9
are mutually inverse, over `X` and over `Y`, each being merely locally of finite type over the
base. -/
@[stacks 0FDR "commutativity of the left-hand square of the diagram"]
theorem cycleDimensionLayerHom_comp_properPushforwardHom :
    (cycleDimensionLayerHom C sY k).comp (properPushforwardHom C sX sY π hπ k) =
      (dimensionLayerFinitePushforwardHom C sX sY π hπ k).comp
        (cycleDimensionLayerHom C sX k) := by
  refine AddMonoidHom.ext fun c => ?_
  have hsq := DFunLike.congr_fun
    (properPushforwardHom_comp_dimensionLayerCycleHom C sX sY π hπ k)
    (cycleDimensionLayerHom C sX k c)
  have hid := DFunLike.congr_fun (cycleDimensionLayerHom_comp_dimensionLayerCycleHom_eq_id C sY k)
    (dimensionLayerFinitePushforwardHom C sX sY π hπ k (cycleDimensionLayerHom C sX k c))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hsq hid ⊢
  rw [← hid, ← hsq, dimensionLayerCycleHom_cycleDimensionLayerHom]

/-- **Stacks 0FDR**, the left-hand square read on a cycle. The element of the Grothendieck group
of the layer over `Y` attached to the proper pushforward of a `k`-cycle `c` on `X` is the direct
image along `π` of the element attached to `c`. -/
@[stacks 0FDR "the left-hand square of the diagram on a cycle"]
theorem cycleDimensionLayerHom_properPushforwardHom (c : CycleGroup C sX k) :
    cycleDimensionLayerHom C sY k (properPushforwardHom C sX sY π hπ k c) =
      dimensionLayerFinitePushforwardHom C sX sY π hπ k (cycleDimensionLayerHom C sX k c) :=
  DFunLike.congr_fun (cycleDimensionLayerHom_comp_properPushforwardHom C sX sY π hπ k) c

/-- **Stacks 0FDR**, the diagram. The maps of Stacks 02S9,
`Z_k ⟶ K₀(Coh_{≤k}/Coh_{≤k-1}) ⟶ Z_k`, over `X` and over `Y`, together with proper pushforward
of `k`-cycles on the two outer columns and direct image along `π` on the middle column, form a
commutative diagram: both the left-hand and the right-hand square commute. -/
@[stacks 0FDR "the maps of Tag 02S9 fit into a commutative diagram with `π_*`"]
theorem finitePushforward_dimensionLayer_diagram_commutes :
    (cycleDimensionLayerHom C sY k).comp (properPushforwardHom C sX sY π hπ k) =
        (dimensionLayerFinitePushforwardHom C sX sY π hπ k).comp
          (cycleDimensionLayerHom C sX k) ∧
      (properPushforwardHom C sX sY π hπ k).comp (dimensionLayerCycleHom C sX k) =
        (dimensionLayerCycleHom C sY k).comp
          (dimensionLayerFinitePushforwardHom C sX sY π hπ k) :=
  ⟨cycleDimensionLayerHom_comp_properPushforwardHom C sX sY π hπ k,
    properPushforwardHom_comp_dimensionLayerCycleHom C sX sY π hπ k⟩

end Stacks.Chow

end

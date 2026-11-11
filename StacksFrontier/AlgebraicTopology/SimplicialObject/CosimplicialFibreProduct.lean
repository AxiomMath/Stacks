module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Limits
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoveringAndHomotopies.FibreProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms into the degreewise fibre product of cosimplicial objects

Let `C` be a category, let `U`, `V`, `W` be cosimplicial objects of `C` and let `a : V ⟶ U`,
`b : W ⟶ U` be morphisms such that every fibre product `V_n ×_{U_n} W_n` exists in `C`, so that
the degreewise fibre product `V ×_U W` of [Stacks, Tag 0172], `Limits.pointwisePullback a b`,
exists. Then for every cosimplicial object `T` the Hom-set `Mor(T, V ×_U W)` is the fibre product
of `Mor(T, V)` and `Mor(T, W)` over `Mor(T, U)`, through the degreewise projections.

## Main results

* `CategoryTheory.CosimplicialObject.isBijective_canonicalMap_pointwisePullback`: for the
  degreewise fibre product `V ×_U W`, with its degreewise projections `p`, `q`, the comparison
  map `Mor(T, V ×_U W) → Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`, `f ↦ (f ≫ p, f ≫ q)`, is a
  bijection.

## Implementation notes

The degreewise fibre product is a fibre product in the category of cosimplicial objects
(`Limits.isPullback_pointwisePullback`), and the bijection is then
`CosimplicialObject.isBijective_canonicalMap`.

## References

* [Stacks, Tag 0172](https://stacks.math.columbia.edu/tag/0172)
* [Stacks, Tag 0173](https://stacks.math.columbia.edu/tag/0173)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CosimplicialObject

/-- **Stacks 0173**.
Let `C` be a category, `U V W` cosimplicial objects of `C`, and `a : V ⟶ U`, `b : W ⟶ U`
morphisms of cosimplicial objects such that every fibre product `V_n ×_{U_n} W_n` exists in `C`,
and let `V ×_U W = Limits.pointwisePullback a b` be the degreewise fibre product of Tag 0172,
with its degreewise projections `p`, `q`. Then for every cosimplicial object `T` the map
`Mor(T, V ×_U W) → Mor(T, V) ×_{Mor(T, U)} Mor(T, W)`, `f ↦ (f ≫ p, f ≫ q)`, is a bijection. -/
@[stacks 0173 "the fibre product of sets `Mor(T, V) ×_{Mor(T, U)} Mor(T, W)` is \
  `Types.PullbackObj`, the set of pairs `(f, g)` with `f ≫ a = g ≫ b`, and the identification \
  is composition with the degreewise projections of `V ×_U W`"]
theorem isBijective_canonicalMap_pointwisePullback
    {C : Type u} [Category.{v} C] {U V W : CosimplicialObject C}
    (a : V ⟶ U) (b : W ⟶ U) [∀ n, HasPullback (a.app n) (b.app n)]
    (T : CosimplicialObject C) :
    Function.Bijective
      (PullbackCone.canonicalMap a b (isPullback_pointwisePullback a b).cone (T := T)) :=
  isBijective_canonicalMap (isPullback_pointwisePullback a b) T

end CategoryTheory.CosimplicialObject

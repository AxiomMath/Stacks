module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback

/-!
# Quasi-coherent modules on the quotient stack of a groupoid in algebraic spaces

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `𝒳 = [U/R]` be its quotient stack (Stacks 044Q).
Stacks 06WT asserts that `QCoh(𝒪_𝒳)` is equivalent to the category `QCoh(U, R, s, t, c)` of
quasi-coherent modules on the groupoid (Stacks 0441,
`AlgebraicGeometry.Space.QuasicoherentModule`), by the equivalence whose forward functor sends
`ℱ` to the pair `(x^*ℱ|_{U_étale}, α)`, where `x : 𝒮_U ⟶ [U/R]` is the canonical projection of
Stacks 044R and `α : t_{small}^*(x^*ℱ|_{U_étale}) ⟶ s_{small}^*(x^*ℱ|_{U_étale})` is the
transport of the canonical 2-morphism of Stacks 044S.

This file defines two functors of that construction: the inverse image along `x`, and the
restriction of quasi-coherent modules along the stackification map `[U/_pR] ⟶ [U/R]`.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackModulePullback` is `ℱ ↦ x^*ℱ`, the inverse image of
  sheaves of modules of Stacks 06WE along the canonical projection `x : 𝒮_U ⟶ [U/R]` of
  Stacks 044R, the first step of the forward functor of Stacks 06WT.
* `AlgebraicGeometry.Stack.quotientPrestackQuasicoherentPullback` is the restriction of
  quasi-coherent modules along the stackification map `[U/_pR] ⟶ [U/R]`.

## Implementation notes

The module universe is `u + 1` throughout, the universe of the objects and of the morphisms of
the quotient stack. On the quasi-coherent side this is forced: Stacks 06WH,
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback`, preserves quasi-coherence of a
module whose universe is `max u v w m` for object universe `v` and morphism universe `w`, which
for the quotient stack is `max u (u + 1) (u + 1) m = max (u + 1) m`.

The reduction functor is formed along `AlgebraicGeometry.Stack.toQuotientStack`, whose source is
the universe-lifted pointwise groupoid fibration `AlgebraicGeometry.Stack.quotientPrestack`
rather than the unlifted one: Stacks 06WH asks the two fibred categories to have objects and
morphisms in a common pair of universes, which holds for the lifted presentation and the quotient
stack — both `Type (u + 1)` with morphisms in `Type (u + 1)` — and fails for the unlifted
pointwise fibration, whose morphisms lie in `Type u`. The universe lift is an equivalence
commuting strictly with the projection to the site
(`AlgebraicGeometry.Stack.quotientPrestackEquivalence`), so nothing of the pointwise quotient is
changed by using it.

`AlgebraicGeometry.Stack.quotientStackModulePullback` is stated on all sheaves of modules rather
than on `QCoh`, for the same universe reason read the other way: the object space fibration
`AlgebraicGeometry.Stack.fibredCategory` has morphisms in `Type u` while the quotient stack has
morphisms in `Type (u + 1)`, so Stacks 06WH does not apply to `x` and quasi-coherence of `x^*ℱ`
is not available here. The inverse image of modules itself, Stacks 06WE, is universe-general, and
so is `x^*`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044T](https://stacks.math.columbia.edu/tag/044T)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 06TM](https://stacks.math.columbia.edu/tag/06TM)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
-/


@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The functor `ℱ ↦ x^*ℱ`, the inverse image of sheaves of modules of Stacks 06WE along the
canonical projection `x : 𝒮_U ⟶ [U/R]` of Stacks 044R. -/
@[stacks 06WT "the inverse image of modules along the canonical map from the object space, \
the first step of the forward functor"]
def quotientStackModulePullback (G : GroupoidInAlgebraicSpaces C S hS B) :
    SheafOfModules.{u + 1}
        (ringStructureSheafCore C S hS (quotientStack G).p
          (isFiberedInGroupoids_quotientStack G) C.topology le_rfl) ⥤
      SheafOfModules.{u + 1}
        (ringStructureSheafCore C S hS (fibredCategory C S hS G.objects.obj).val.p
          (fibredCategory C S hS G.objects.obj).property C.topology le_rfl) :=
  modulePullback.{u, u + 1, u, u + 1, u + 1, u + 1} C S hS
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS G.objects.obj).property (isFiberedInGroupoids_quotientStack G)
    (quotientStackProjection G).toFunctor (quotientStackProjection G).w C.topology le_rfl

/-- The restriction of quasi-coherent modules along the stackification map `[U/_pR] ⟶ [U/R]`: the
inverse image of modules of Stacks 06WE, which preserves quasi-coherence by Stacks 06WH. -/
@[stacks 06WT "the restriction of quasi-coherent modules along the stackification map of the \
pointwise quotient"]
def quotientPrestackQuasicoherentPullback (G : GroupoidInAlgebraicSpaces C S hS B) :
    FibredSite.quasicoherentModules.{u, u + 1, u + 1, u + 1} C S hS (quotientStack G).p
        (isFiberedInGroupoids_quotientStack G) ⥤
      FibredSite.quasicoherentModules.{u, u + 1, u + 1, u + 1} C S hS (quotientPrestack G).p
        (isFiberedInGroupoids_quotientPrestack G) :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherentOnSite _).ι ⋙
      modulePullback.{u, u + 1, u + 1, u + 1, u + 1, u + 1} C S hS (quotientPrestack G).p
        (quotientStack G).p (isFiberedInGroupoids_quotientPrestack G)
        (isFiberedInGroupoids_quotientStack G) (toQuotientStack G)
        (isFibredOneMorphism_toQuotientStack G).comp_eq C.topology le_rfl)
    fun M => @isQuasicoherentOnSite_modulePullback.{u, u + 1, u + 1, u + 1} C S hS _ _ _ _ _ _ _ _
      _ (isFibredOneMorphism_toQuotientStack G).comp_eq M.obj M.property

end AlgebraicGeometry.Stack

end

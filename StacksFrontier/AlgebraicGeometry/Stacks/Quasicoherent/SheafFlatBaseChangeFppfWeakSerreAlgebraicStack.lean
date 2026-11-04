module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineVanishing

/-!
# `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)` for an algebraic stack

For an algebraic stack `𝒳`, the modules on `𝒳_fppf` which are locally quasi-coherent
(**Stacks 06WJ**) and have the flat base change property of **Stacks 0762**, read with the
pullback of sheaves, form a weak Serre subcategory of `Mod(𝒪_𝒳)`: this is **Stacks 0771** (2)
for the fppf site.

Closure under kernels, cokernels and isomorphisms, and the reduction of closure under
extensions to the vanishing of `H^1_{fppf}(x, ℱ)` over the objects `x` lying over affine schemes,
are `isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_rightDerived_vanishing`;
the vanishing is `isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`. Both
lie in the namespace `AlgebraicGeometry.Stack`. This file puts the two together as an instance.

## Main results

* `AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModules`:
  the instance.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] hasSheafify_associatedTopology_algebraicStack
  wEqualsLocallyBijective_associatedTopology_algebraicStack enoughInjectives_fppfModules
  Stacks.Cohomology.AcyclicCover.evaluation_additive

/-- For an algebraic stack `𝒳`, the locally quasi-coherent modules on `𝒳_fppf` with the flat base
change property, read with the pullback of sheaves, form a weak Serre subcategory of
`Mod(𝒪_𝒳)`: Stacks 0771 (2) for the fppf site. -/
instance isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModules :
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳).IsWeakSerreClass :=
  isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppf_of_rightDerived_vanishing
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (fun F hF x hx ↦ isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack
      B E h S hS 𝒳 F hF x hx 1 Nat.one_pos)

end AlgebraicGeometry.Stack

end

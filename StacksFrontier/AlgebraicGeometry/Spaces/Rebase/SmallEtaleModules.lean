module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite

/-!
# Exactness of the transport of modules to the lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site and let `F` be an algebraic space over `W`,
with lower-shriek extension `Λ_h F`.  The equivalence
`AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE : Mod(𝒪_F) ≌ Mod(𝒪_{Λ_h F})`
is additive in both directions and its inverse is exact.

## Main results

* `AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE_inverse_additive` and
  `AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE_functor_additive`.
* `AlgebraicGeometry.Space.preservesFiniteLimits_relocalizeModulesEquivalenceSE_inverse`
  and `AlgebraicGeometry.Space.preservesFiniteColimits_relocalizeModulesEquivalenceSE_inverse`.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}

variable (hF : IsAlgebraicSpace B W hW F)
  (hF' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))

/-- The inverse of `relocalizeModulesEquivalenceSE` is additive. -/
instance relocalizeModulesEquivalenceSE_inverse_additive :
    (relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor of `relocalizeModulesEquivalenceSE` is additive. -/
instance relocalizeModulesEquivalenceSE_functor_additive :
    (relocalizeModulesEquivalenceSE B W S hW hS h hF hF').functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of `relocalizeModulesEquivalenceSE` preserves finite limits. -/
instance preservesFiniteLimits_relocalizeModulesEquivalenceSE_inverse :
    PreservesFiniteLimits (relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse :=
  inferInstance

/-- The inverse of `relocalizeModulesEquivalenceSE` preserves finite colimits. -/
instance preservesFiniteColimits_relocalizeModulesEquivalenceSE_inverse :
    PreservesFiniteColimits (relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse :=
  inferInstance

end AlgebraicGeometry.Space

end

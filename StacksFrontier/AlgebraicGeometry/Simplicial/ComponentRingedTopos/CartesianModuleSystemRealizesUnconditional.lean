module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleSystemRealizes
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationLeftDerivedComponent

/-!
# Stacks 0D9T without the flatness hypothesis

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. Every cartesian simplicial system of the derived category of modules whose positively
shifted self-maps vanish is the simplicial system of a cartesian object of `D(O)`
(`CategoryTheory.SimplicialSiteSituation.CartesianModuleSystemRealizes`), with no flatness
assumption on the transitions.

## Main results

* `CategoryTheory.SimplicialSiteSituation.cartesianModuleSystemRealizes_unconditional`: Stacks
  0D9T without the flatness hypothesis.

## References

* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- In a simplicial-site situation with a sheaf of rings `O` on the total site, every cartesian
simplicial system of the derived category of modules whose positively shifted self-maps vanish is
the simplicial system of a cartesian object of `D(O)`; no flatness of the transitions is
assumed. -/
theorem cartesianModuleSystemRealizes_unconditional : S.CartesianModuleSystemRealizes O :=
  exists_isCartesianDerivedModule_realizing_moduleSystem

end CategoryTheory.SimplicialSiteSituation

end

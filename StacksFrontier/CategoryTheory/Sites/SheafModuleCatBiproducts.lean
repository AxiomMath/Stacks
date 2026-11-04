module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Finite biproducts of sheaves of modules

Sheaves of `R`-modules on any site form a preadditive category with finite products, hence have
finite biproducts. Instance search does not find this on its own, and without it a finite direct
sum `⨁` of sheaves of modules does not elaborate.

## Main results

* `CategoryTheory.Sheaf.hasFiniteBiproducts_moduleCat`: the instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Sheaf

/-- Sheaves of `R`-modules on a site have finite biproducts: they are preadditive and have
finite products. -/
instance hasFiniteBiproducts_moduleCat {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type w) [Ring R] : HasFiniteBiproducts (Sheaf J (ModuleCat.{w} R)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end CategoryTheory.Sheaf

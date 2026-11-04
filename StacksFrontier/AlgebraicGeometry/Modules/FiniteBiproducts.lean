module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finite biproducts of modules on a scheme

The category `X.Modules` of `𝒪_X`-modules on a scheme is preadditive with finite products, hence
has finite biproducts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The category of `𝒪_X`-modules has finite biproducts. -/
instance schemeModulesHasFiniteBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

end AlgebraicGeometry.Scheme.Modules

end

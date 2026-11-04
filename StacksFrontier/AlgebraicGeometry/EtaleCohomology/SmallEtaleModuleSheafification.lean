module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass

/-!
# Sheafification of presheaves of modules on a slice of the small étale site

Let `B` be a big étale site, `T` one of its schemes, `V` an object of the small étale site of
`T` and `Λ` a commutative ring. On the slice of that small étale site at `V`, a morphism of
presheaves of `Λ`-modules becomes an isomorphism after sheafification exactly when it is locally
injective and locally surjective.

## Main results

* `AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_over_moduleCat` — the class `J.W` of the
  slice topology is local bijectivity, at the coefficient universe `u + 1`.
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- Sheafification of presheaves of `Λ`-modules on a slice of the small étale site inverts
exactly the locally bijective morphisms, at the coefficient universe `u + 1`. This is
`Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat` with its universes fixed; instance
search cannot fix them itself, the general statement being at `ModuleCat.{max u v w}`. -/
public instance SmallEtale.wEqualsLocallyBijective_over_moduleCat (B : BigEtaleSite.{u})
    (T : B.Scheme) (V : SmallEtale B T.obj T.property) (Λ : Type (u + 1)) [CommRing Λ] :
    ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
      (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, u + 1}
    ((SmallEtale.topology B T.obj T.property).over V) Λ

end AlgebraicGeometry

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleRestrictUnitAnyUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image of a ring sheaf viewed as a module over another

Let `φ : O ⟶ O'` be a morphism of sheaves of commutative rings on a site, and read `O'` as a
sheaf of `O`-modules by restriction of scalars along `φ`. Its inverse image along a
finite-product-preserving functor `Φ` of sheaves of sets is then `Φ O'` read as a sheaf of
`Φ O`-modules by restriction of scalars along `Φ φ`.

This is the comparison that turns the Stacks 05VD statement about *modules* into the statement
about *morphisms of sheaves of rings*: flatness of `φ` is flatness of `O'` as an `O`-module, so
transporting it along `Φ` needs exactly the identification above.

The two sides have the same underlying sheaf of sets on the nose — restriction of scalars does
not change it, and by construction of Stacks 03D2 the inverse image of a sheaf of modules has
`Φ` of the underlying sheaf as its own. So the comparison is the identity there, and what has to
be checked is that the two addition maps and the two scalar actions agree.

## Main results

* `Stacks.Sheaves.ToposPullback.isFlatMap_pullbackCommRingSheafMap`: **the inverse image of a
  flat morphism of sheaves of commutative rings is flat**, which is Stacks 05VD read at a
  morphism of sheaves of rings rather than at a module. The identification of the two module
  structures it rests on is `Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso`.

## Implementation notes

`isFlatMap_pullbackCommRingSheafMap` asks `Φ` to be a left adjoint rather than carrying
preservation of epimorphisms and of the coproducts of
`Stacks.Sheaves.ToposPullback.factorizationSheaf` as separate hypotheses, which is how
`AlgebraicGeometry.RingedToposSiteHom.isFlat_inverseImageModules` supplies them too. At the
inverse image of a morphism of topoi, which is the case this is for, that hypothesis is free.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (Φ : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [PreservesFiniteProducts Φ]
  {O O' : Sheaf K CommRingCat.{u}} (φ : O ⟶ O')

section Flat

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]

/-- **Inverse image preserves flatness of a morphism of sheaves of commutative rings.** If `O'`
is flat over `O` then `Φ O'` is flat over `Φ O`.

This is the ring-map form of Stacks 05VD. The module form,
`Stacks.Sheaves.ToposPullback.isFlat_pullbackModuleObj_of_isFlat`, applies to `O'` read as an
`O`-module; `AnyUniverse.pullbackRestrictUnitIso` identifies its conclusion with the assertion
that `Φ O'` is flat over `Φ O`. Preservation of epimorphisms and of the coproducts the module
form asks for come from `Φ` being a left adjoint. -/
@[sga "4 VI 8.6.4" "special case"]
theorem isFlatMap_pullbackCommRingSheafMap [Φ.IsLeftAdjoint] [PreservesFiniteLimits Φ]
    (hφ : AlgebraicGeometry.SheafOfModules.IsFlatMap φ) :
    AlgebraicGeometry.SheafOfModules.IsFlatMap ((pullbackCommRingSheafFunctor J Φ).map φ) := by
  have : Φ.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_isLeftAdjoint _
  exact AlgebraicGeometry.SheafOfModules.isFlat_of_iso (AnyUniverse.pullbackRestrictUnitIso Φ φ)
    (isFlat_pullbackModuleObj_of_isFlat Φ O _ hφ)

end Flat

end Stacks.Sheaves.ToposPullback

end

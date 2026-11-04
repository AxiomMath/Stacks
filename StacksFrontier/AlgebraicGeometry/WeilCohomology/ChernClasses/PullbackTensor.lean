module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup

/-!
# The pullback of a tensor product, at the spelling `K₀(Vect(X))` is built over

Tag 01CD says that the pullback of a tensor product of sheaves of modules is the tensor product
of the pullbacks. The comparison morphism it asserts to be an isomorphism is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison`, whose source and target are spelled
through the monoidal product of Tag 01CA; that product is, for a morphism of schemes, exactly
`AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace`, the tensor product the Grothendieck ring
of Tag 0FDK multiplies with. This file records the resulting isomorphism in that spelling.

## Main definitions

* `Stacks.WeilCohomology.pullbackTensorObjRingedSpaceIso`: **Tag 01CD at that spelling.**

## Implementation notes

The `IsIso` instance has to be supplied explicitly rather than found by instance search, the
morphism of schemes having to be read as a morphism of ringed spaces first.

This is in a module of its own because importing
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` disturbs the instances by
which the group structure of `Pic(X)` is found, and
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleTensor` needs that
structure.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.WeilCohomology

/-- **Stacks Tag 01CD, the pullback of a tensor product is the tensor product of the
pullbacks**, at the spelling of the tensor product that `K₀(Vect(X))` multiplies with. The
comparison morphism of Tag 01CD is an isomorphism, and its source and target are the two sides
spelled through the monoidal product of Tag 01CA, which is that spelling. -/
@[stacks 01CD "the pullback of a tensor product of sheaves of modules on a scheme, read at the \
  spelling of the tensor product that the Grothendieck ring of Tag 0FDK multiplies with"]
def pullbackTensorObjRingedSpaceIso {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.tensorObjRingedSpace Y A B) ≅
      Scheme.Modules.tensorObjRingedSpace X ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B) :=
  @asIso _ _ _ _
    (Stacks.PullbackTensorCoherence.pullbackTensorComparison f.toLRSHom.toShHom A B)
    (Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison f.toLRSHom.toShHom A B)

end Stacks.WeilCohomology

end

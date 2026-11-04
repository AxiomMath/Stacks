module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.InvertibleTwistDerived

/-!
# The derived twist by an invertible module, as a single isomorphism

`Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleIso` identifies
`K ⊗^𝐋_{𝒪_X} L[0]` with the class of the total tensor complex `Tot(K ⊗ L[0])`, and
`Stacks.AmpleNonvanishing.totalTensorSingleIso` identifies that total complex with the termwise
twist `p ↦ K^p ⊗_{𝒪_X} L`. This file names the termwise twist and composes the two, identifying
the derived twist `K ⊗^𝐋_{𝒪_X} L[0]` with the complex whose degree-`p` term is `K^p ⊗ L`.

## Main definitions

* `Stacks.AmpleNonvanishing.termwiseTwist`: the complex `p ↦ K^p ⊗_{𝒪_X} L`.
* `Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleTermwiseIso`:
  `K ⊗^𝐋_{𝒪_X} L[0] ≅ Q(p ↦ K^p ⊗_{𝒪_X} L)` for an arbitrary complex `K` and an invertible `L`,
  with **no flatness hypothesis on `K`**.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample

universe u

namespace Stacks.AmpleNonvanishing

/-- **The termwise twist of a complex by a module**, the complex `p ↦ K^p ⊗_{𝒪_X} L` with the
differentials of `K` tensored with the identity. No hypothesis on `L`. -/
def termwiseTwist (X : Scheme.{u}) (L : X.Modules) (K : Stacks.Duality.TensorComplex X) :
    Stacks.Duality.TensorComplex X :=
  CochainComplex.KFlatBifunctor.rowComplex
    (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) K L

/-- **The total tensor complex against a module in degree zero is the termwise twist**, at the
name `Stacks.AmpleNonvanishing.termwiseTwist`. -/
def totalTensorSingleTermwiseIso (X : Scheme.{u}) (L : X.Modules)
    (K : Stacks.Duality.TensorComplex X) :
    Stacks.Duality.totalTensorComplex K
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L) ≅ termwiseTwist X L K :=
  totalTensorSingleIso X L K

/-- **The derived twist by an invertible module is the termwise twist.** For every complex `K` of
`𝒪_X`-modules and every invertible `𝒪_X`-module `L`,

`K ⊗^𝐋_{𝒪_X} L[0] ≅ Q(p ↦ K^p ⊗_{𝒪_X} L)`,

with no flatness hypothesis on `K`. It is the composite of
`Stacks.AmpleNonvanishing.derivedTensorSingleInvertibleIso` with
`Stacks.AmpleNonvanishing.totalTensorSingleIso`. -/
def derivedTensorSingleInvertibleTermwiseIso (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (K : Stacks.Duality.TensorComplex X) :
    ((Stacks.Duality.derivedTensor X).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj L)) ≅
      DerivedCategory.Q.obj (termwiseTwist X L K) :=
  derivedTensorSingleInvertibleIso X L K ≪≫
    DerivedCategory.Q.mapIso (totalTensorSingleTermwiseIso X L K)

end Stacks.AmpleNonvanishing

end

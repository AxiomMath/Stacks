module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 01O4's statement carries no hypothesis but the graded algebra

The statement of Tag 01O4 in `StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Representation` is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation A TA ι D`, with three parameters
beyond the quasi-coherent graded algebra `A`: a choice `TA` of tensor algebras, a degreewise
comparison `ι` of the pullback of a tensor algebra with the tensor algebra of the pullback, and a
twist datum `D` of Tag 01NR. **All three are constructible**, so a representation of Tag 01O4's
functor is a term of a single type depending on `A` alone.

* `ι` is `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorAlgebraPullbackIsos`, built in
  `StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos` from Tag 01CD.
* `D` is `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, Tag 01NR's
  existence assertion, which needs nothing beyond the graded algebra.
* `TA` is `canonicalTensorAlgebras` below: `SheafOfModules.algebras` constructs the package for
  an arbitrary sheaf of modules, realizing each of the three algebras as the degreewise
  sheafification of its sectionwise counterpart and transporting along the counit isomorphism of
  the sheafification adjunction, and `canonicalTensorAlgebras` instantiates it at the site of
  open subsets of a scheme.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.canonicalTensorAlgebras`: **the canonical choice of
  tensor algebras**, for every scheme and every sheaf of modules on it.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1RepresentationOf`: **the type of representations
  of Tag 01O4's functor**, with every constructible parameter supplied: the representing
  bijections of the functor `F1` of the canonical tensor algebras, normalised at the twist datum
  that Tag 01NR produces from `A` itself.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.canonicalTensorAlgebras_apply`: the canonical choice
  is `SheafOfModules.algebras` at the site of open subsets of the scheme, on the nose.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

/-- **The canonical tensor algebras of Tag 01O4's functor.** For every scheme `T` and every sheaf
of `𝒪_T`-modules `L`, the tensor algebra of `L` with its exterior and symmetric quotients, as
constructed by `SheafOfModules.algebras`: each of the three is the degreewise sheafification of
its sectionwise counterpart. -/
@[ega "II 1.7.4" "special case"]
public def canonicalTensorAlgebras : TensorAlgebras.{u} :=
  fun T L => SheafOfModules.algebras (Opens.grothendieckTopology ↥T) L

/-- The canonical choice is `SheafOfModules.algebras` at the site of open subsets of the scheme,
with no transport. -/
public theorem canonicalTensorAlgebras_apply (T : Scheme.{u}) (L : T.Modules) :
    canonicalTensorAlgebras T L = SheafOfModules.algebras (Opens.grothendieckTopology ↥T) L :=
  rfl

/-- **Representations of Tag 01O4's functor for a graded algebra alone**: the type of
representations of the functor `F1` of invertible degree-one quotients by the relative
homogeneous spectrum, with the choice of tensor algebras, the pullback comparison and the twist
datum all supplied canonically. -/
public abbrev F1RepresentationOf {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) : Type (u + 1) :=
  F1Representation A canonicalTensorAlgebras
    (tensorAlgebraPullbackIsos canonicalTensorAlgebras)
    (GluedTwistAlgebra.twistDataOfGradedAlgebra A)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end

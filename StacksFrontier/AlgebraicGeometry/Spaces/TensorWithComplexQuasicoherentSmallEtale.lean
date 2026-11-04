module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleExtensionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleKernelQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherentAdjoint
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 09MA for the small étale site of an algebraic space

`AlgebraicGeometry.RingedSite.derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsum` is the
dévissage of Stacks 09MA for an arbitrary ringed site, where it takes the two clauses of
Stacks 03M1 it uses as inputs: quasi-coherence is a weak Serre class, and `hqcsum`, closure
under direct sums.  For a *variable* ringed site neither is available.

For the small étale site of an algebraic space both are theorems of this development, and this
module supplies them, which makes the statement below **Stacks 09MA itself**, with the source's
own hypothesis on `K` and nothing else.

The point is a universe count.  The ambient category in which the tensor products of
Stacks 09LX are formed, `AlgebraicGeometry.RingedSite.TensorModO`, has its sections in
`max u v w t s`; for `AlgebraicGeometry.Space.smallEtaleRingedSite`, a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, that is `max (u + 1) t s`, strictly above the
universe `u` of the structure rings.  All six clauses of Stacks 03M1 that enter are available
there:

* the **kernel**, **cokernel**, **colimit** and **direct-sum** clauses are
  `AlgebraicGeometry.Space.isClosedUnderKernels`,
  `AlgebraicGeometry.Space.isClosedUnderCokernels`,
  `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape` and
  `AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent`;
* the **extension** clause is `AlgebraicGeometry.Space.isClosedUnderExtensions` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleExtensionQuasicoherent.lean`.

So setting `m := max t s` discharges `hqcsum` and all three inputs of the weak Serre class.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryB_tensorWithComplexDerived_obj_smallEtale`:
  **Stacks 09MA**, for the small étale site of an algebraic space.

## Implementation notes

**The universes of the clause theorems are passed explicitly, enlargement first.**  Each of
`isClosedUnderKernels`, `isClosedUnderCokernels`, `isClosedUnderExtensions` and
`isClosedUnderDirectSumsQuasicoherent` takes its module-universe enlargement before the universe
of the schemes; written the other way round the big fppf site is asked to live in
`Type (max t s + 2)`.

**The weak Serre class is assembled from the three closure clauses.**  The tensor products live
at the module universe `max (u + 1) t s`, not at the universe `u` of the schemes; what is used
here is the conditional instance
`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass` with its three binders supplied
at `max (u + 1) t s`.

## References

* [Stacks Project, Tag 09MA](https://stacks.math.columbia.edu/tag/09MA)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u t s

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.RingedSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 09MA.**  Let `S` be a scheme, let `F` be an algebraic space over `S`, let `K` be a
complex of `𝒪_F`-modules whose cohomology sheaves are quasi-coherent and let `(E, d) = Hom(K, K)`
be the endomorphism differential graded algebra.  Then the functor
`- ⊗_E^𝐋 K : D(E, d) ⟶ D(𝒪_F)` of Stacks 09LX has image contained in `D_QCoh(𝒪_F)`.

The hypothesis `hK` is the source's, that the cohomology sheaves of `K` be quasi-coherent, stated
for the complex `liftComplex F K` that the functor tensors with.  Nothing else is assumed: the
weak Serre class that the dévissage
`AlgebraicGeometry.RingedSite.derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsum` uses comes
from `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass` together with
`AlgebraicGeometry.Space.isClosedUnderKernels`,
`AlgebraicGeometry.Space.isClosedUnderCokernels` and
`AlgebraicGeometry.Space.isClosedUnderExtensions` at the module universe in which the tensor
products are formed, and its `hqcsum` is
`AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent`; the exactness of the functor and
its preservation of direct sums are instances of this development. -/
@[stacks 09MA]
public theorem derivedCategoryB_tensorWithComplexDerived_obj_smallEtale
    (K : CochainComplex (ModO.{u + 1, u, u, t} (smallEtaleRingedSite B S hS F hF)) ℤ)
    (hK : tensorModOQuasicoherentDerived.{u + 1, u, u, t, s}
      (smallEtaleRingedSite B S hS F hF)
      (DerivedCategory.Q.obj (liftComplex.{u + 1, u, u, t, s}
        (smallEtaleRingedSite B S hS F hF) K)))
    (M : DifferentialGradedModule.derivedCategory.{0, max (u + 1) t s, max (u + 1) t s}
      (RingedSite.Rep.{u + 1, u, u, t, s, 0} (smallEtaleRingedSite B S hS F hF) ℤ K).algebra) :
    tensorModOQuasicoherentDerived.{u + 1, u, u, t, s} (smallEtaleRingedSite B S hS F hF)
      ((tensorWithComplexDerived.{u + 1, u, u, t, s, 0}
        (smallEtaleRingedSite B S hS F hF) ℤ K).obj M) :=
  let := isClosedUnderKernels.{max t s, u} B S hS F hF
  let := isClosedUnderCokernels.{max t s, u} B S hS F hF
  let := isClosedUnderExtensions.{max t s, u} B S hS F hF
  derivedCategoryB_tensorWithComplexDerived_obj_of_hqcsum.{u + 1, u, u, t, s} _ K
    (fun Mf c hc hMf =>
      isClosedUnderDirectSumsQuasicoherent.{max t s, u} B S hS F hF _ Mf c hc hMf)
    hK M

end AlgebraicGeometry.Space

end

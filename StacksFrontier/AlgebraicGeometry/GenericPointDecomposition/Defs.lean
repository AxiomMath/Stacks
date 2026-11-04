module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# The generic-point decomposition vocabulary

This file introduces the `𝒪_X`-modules which the generic-point decomposition of the sheaf of
meromorphic functions compares: the sheaf of meromorphic functions itself, the sheaf of
meromorphic sections of a module, and the contribution of a single generic point.

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointDecomposition.totalQuotientRingCatSheaf` and
  `toTotalQuotientRingCatSheaf`: the sheaf of total quotient rings and the canonical map to it,
  both regarded as `RingCat`-valued, which is the form in which sheaves of modules are taken.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.meromorphicFunctions`: the sheaf of total
  quotient rings regarded as an `𝒪_X`-module.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.genericPointStalkModule`: the structure
  sheaf of the spectrum of the local ring at a generic point, pushed forward to `X`.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.genericPointStalkModuleOf`: the
  corresponding contribution of an arbitrary `𝒪_X`-module at a generic point.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.meromorphicSections`: the sheaf of
  meromorphic sections of an `𝒪_X`-module, regarded again as an `𝒪_X`-module.

## Implementation notes

A sheaf of modules is taken over a `RingCat`-valued sheaf of rings, whereas the structure sheaf
and the sheaf of total quotient rings are `CommRingCat`-valued; the two are related by
`CategoryTheory.sheafCompose` along `forget₂ CommRingCat RingCat`, which is exactly how
`AlgebraicGeometry.Scheme.ringCatSheaf` is built from `AlgebraicGeometry.Scheme.sheaf`. The
module of meromorphic functions is the free module of rank one over the sheaf of total quotient
rings, with its scalars restricted along the canonical map from the structure sheaf; since the
canonical map is a map of sheaves of rings, this is the same thing as the sheaf of total
quotient rings together with its `𝒪_X`-algebra structure.

The direct sum appearing in the decomposition is the coproduct in `X.Modules`, so it includes
sheafification and is not the objectwise coproduct of presheaves.

`genericPointStalkModule` is stated with the free module of rank one on the spectrum of the
stalk, rather than as the pullback of the structure sheaf of `X` along
`AlgebraicGeometry.Scheme.fromSpecStalk`; `genericPointStalkModuleOf` is the version for a
general module, and takes the pullback. The two agree on the structure sheaf up to the canonical
comparison map `SheafOfModules.pullbackObjUnitToUnit`.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointDecomposition

variable (X : Scheme.{u})

/-- The sheaf of total quotient rings of a scheme, regarded as a sheaf of `RingCat`-valued
rings. This is the form over which sheaves of modules are taken, exactly as
`AlgebraicGeometry.Scheme.ringCatSheaf` is for the structure sheaf. -/
noncomputable abbrev totalQuotientRingCatSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat.{u})).obj X.totalQuotientSheaf

/-- The canonical morphism from the structure sheaf of a scheme to its sheaf of total quotient
rings, regarded as a morphism of `RingCat`-valued sheaves of rings. -/
noncomputable abbrev toTotalQuotientRingCatSheaf :
    X.ringCatSheaf ⟶ totalQuotientRingCatSheaf X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat.{u})).map X.toTotalQuotientSheaf

/-- The sheaf of meromorphic functions on `X`, regarded as an `𝒪_X`-module: the free module of
rank one over the sheaf of total quotient rings, with scalars restricted along the canonical
morphism from the structure sheaf. -/
noncomputable abbrev meromorphicFunctions : X.Modules :=
  (SheafOfModules.restrictScalars (toTotalQuotientRingCatSheaf X)).obj
    (SheafOfModules.unit (totalQuotientRingCatSheaf X))

/-- The contribution of a generic point `η` to the sheaf of meromorphic functions: the structure
sheaf of the spectrum of the local ring `𝒪_{X, η}`, pushed forward to `X` along the canonical
morphism `Spec 𝒪_{X, η} ⟶ X`. -/
noncomputable abbrev genericPointStalkModule (η : genericPoints X) : X.Modules :=
  (Scheme.Modules.pushforward (X.fromSpecStalk η.1)).obj
    (SheafOfModules.unit (Spec (X.presheaf.stalk η.1)).ringCatSheaf)

/-- The contribution of a generic point `η` to the sheaf of meromorphic sections of an
`𝒪_X`-module `F`: the pullback of `F` to the spectrum of the local ring at `η`, pushed forward
again to `X`. This is the summand `j_{η,*} F_η` that the displayed decompositions of Stacks
02OW (2) are stated with; `genericPointStalkModule` above is the structure-sheaf case
`j_{η,*} κ(η)`, the corresponding summand of the decomposition of `𝒦_X` itself. -/
noncomputable abbrev genericPointStalkModuleOf (F : X.Modules) (η : genericPoints X) :
    X.Modules :=
  (Scheme.Modules.pushforward (X.fromSpecStalk η.1)).obj
    ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F)

/-- The sheaf of meromorphic sections of an `𝒪_X`-module `F`, regarded again as an
`𝒪_X`-module by restricting its scalars along the canonical morphism from the structure sheaf
to the sheaf of total quotient rings. This is the form in which the displayed decompositions of
Stacks 02OW (2) are stated. -/
noncomputable abbrev meromorphicSections (F : X.Modules) : X.Modules :=
  (SheafOfModules.restrictScalars (toTotalQuotientRingCatSheaf X)).obj
    (meromorphicSectionSheaf X.sheaf F)

end Stacks.AlgebraicGeometry.GenericPointDecomposition

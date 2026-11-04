module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreStalkFreeness

/-!
# The stalk criterion for flatness of a module on an algebraic space over itself

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `F` be a
quasi-coherent `𝒪_X`-module.  Flatness of `F` over `X` itself — `AlgebraicGeometry.Space`'s
`IsFlatOver` of Stacks 05VV along the identity of `X`, which is what "`F` is a flat
`𝒪_X`-module" means — is a condition on the restrictions of `F` to the étale scheme charts of
`X`.  This file records that it is equivalently the pointwise condition that every geometric
stalk `F_{x̄}` of Stacks 05VQ be a flat `𝒪_{X, x̄}`-module over the étale local ring of
Stacks 04NG.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_id_iff_forall_flat_geometricModuleStalk`: **the stalk
  criterion.**  A quasi-coherent `𝒪_X`-module is flat over `X` exactly when all of its
  geometric stalks are flat.
* `AlgebraicGeometry.Space.isFlatOver_id_of_forall_free_geometricModuleStalk`: free geometric
  stalks make a quasi-coherent module flat over `X`.

## Implementation notes

Both halves are already in the tree and this file only composes them: the geometric-stalk form
of Stacks 05VV is `AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint`
of `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleGeometricPointCriterion.lean`, which is
where quasi-coherence is used, and the identification of relative flatness at a geometric point
over the source itself with flatness of the geometric stalk is
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_id_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricFibreStalkFreeness.lean`.

The composite is worth stating because it is the form a consumer of plain flatness of an
`𝒪_X`-module tests, and because the analogous criterion for the *tensor-exactness* predicate
`AlgebraicGeometry.SheafOfModules.IsFlat` is **not** available on the small étale site: Stacks
05NE, `AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat` of
`StacksFrontier/Topology/Sheaves/Modules/Flat/Stalk.lean`, is proved only for
`Opens.grothendieckTopology`.  The two predicates are not compared anywhere in this
development, so neither criterion substitutes for the other; what this file gives is the
criterion for the predicate Stacks 05VV defines, which is the one the module-flatness results
of this development are stated with.

No declaration here carries a `stacks` tag: Stacks 05VV is tagged at its definition
`AlgebraicGeometry.Space.IsFlatOver` and Stacks 05VQ at `geometricModuleStalk`, and the
geometric-stalk form of 05VV is already carried by the criterion this composes.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The stalk criterion for flatness of a module over its own algebraic space.**  A
quasi-coherent `𝒪_X`-module is flat over `X` in the chartwise sense of Stacks 05VV, read along
the identity of `X`, exactly when its geometric stalk at every geometric point `x̄` is a flat
module over the étale local ring `𝒪_{X, x̄}`. -/
theorem isFlatOver_id_iff_forall_flat_geometricModuleStalk {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] :
    IsFlatOver B S hS X.2 (𝟙 X : X ⟶ X).hom F ↔
      ∀ xbar : GeometricPoint B S hS X.1,
        Module.Flat (etaleLocalRing B S hS X.1 xbar)
          (geometricModuleStalk B S hS X xbar F) :=
  (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (𝟙 X) F).trans
    (forall_congr' fun xbar => isFlatOverAtGeometricPoint_id_iff B S hS F xbar)

/-- A quasi-coherent `𝒪_X`-module whose geometric stalks are all free is flat over `X`. -/
theorem isFlatOver_id_of_forall_free_geometricModuleStalk {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hfree : ∀ xbar : GeometricPoint B S hS X.1,
      Module.Free (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar F)) :
    IsFlatOver B S hS X.2 (𝟙 X : X ⟶ X).hom F :=
  (isFlatOver_id_iff_forall_flat_geometricModuleStalk B S hS F).2 fun xbar =>
    let := hfree xbar
    Module.Flat.of_free

end AlgebraicGeometry.Space

end

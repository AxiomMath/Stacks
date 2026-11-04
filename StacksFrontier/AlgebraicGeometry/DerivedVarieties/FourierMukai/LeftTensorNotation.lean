module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative

/-!
# The derived tensor product on the left, and the derived pullback of the structure sheaf

This file provides, on the derived categories `D(𝒪_W)` of modules over schemes `W` (spelled with
the category `W.Modules`), the derived tensor product with a fixed complex on the left, the
projection-formula transformation read in the target complex ([Stacks, Tag 0B53]), the
commutativity isomorphism `- ⊗^𝐋 A ≅ A ⊗^𝐋 -` given by the symmetric monoidal structure of
[Stacks, Tag 0FPB] on `D(𝒪_W)`, and the identification `L p^*(𝒪_W[0]) ≅ 𝒪_V[0]`.

## Main definitions

* `dtenLeft W A` (scoped notation in `AlgebraicGeometry`): `A ⊗^𝐋_{𝒪_W} -`.
* `AlgebraicGeometry.dprojectionFormulaRight`: the projection-formula transformation
  `(R p_* E) ⊗^𝐋 - ⟶ L p^* ⋙ (E ⊗^𝐋 -) ⋙ R p_*`.
* `AlgebraicGeometry.dtenRSwapIso`: commutativity of the derived tensor product,
  `- ⊗^𝐋 A ≅ A ⊗^𝐋 -`.
* `AlgebraicGeometry.dpullStructureSheafIso`: `L p^*(𝒪_W[0]) ≅ 𝒪_V[0]`.

## Implementation notes

`dtenLeft` is notation rather than a definition: `dtenLeft W A` elaborates to
`(AlgebraicGeometry.TorFormula.derivedTensor W).obj A`, the base derived tensor bifunctor at the
scheme spelling of `D(𝒪_W)`, and `dtenLeft W` alone to the partially applied `.obj`. The
symmetric monoidal structure of [Stacks, Tag 0FPB] on `D(𝒪_W)` is used as
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` and `canonicalDerivedSymmetric`
directly, ascribed the scheme-spelled type. The remaining operations are definitions directly in
terms of the public library constructions (`derivedTensorProductFunctor`,
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap`,
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`,
`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso`).

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Notation

variable {V W : Scheme.{u}}

/-- `dtenLeft W A` is `A ⊗^𝐋_{𝒪_W} -`, the derived tensor product with a fixed complex `A` on
the left; `dtenLeft W` is the partially applied form. -/
scoped syntax (name := dtenLeftStx) "dtenLeft " term:max (ppSpace term:max)? : term

macro_rules (kind := dtenLeftStx)
  | `(dtenLeft $W $A) => `((AlgebraicGeometry.TorFormula.derivedTensor $W).obj $A)
  | `(dtenLeft $W) => `((AlgebraicGeometry.TorFormula.derivedTensor $W).obj)

/-- The projection-formula transformation of [Stacks, Tag 0B53] read in the target complex:
`(R p_* E) ⊗^𝐋 - ⟶ L p^* ⋙ (E ⊗^𝐋 -) ⋙ R p_*`. -/
def dprojectionFormulaRight (p : V ⟶ W) (E : DerivedCategory V.Modules) :
    dtenLeft W ((dpush p).obj E) ⟶ dpull p ⋙ dtenLeft V E ⋙ dpush p where
  app A := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
    p.toLRSHom.toShHom E A
  naturality _ _ a :=
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
      p.toLRSHom.toShHom E a

/-- **The derived pullback of the structure sheaf is the structure sheaf**, both placed in
degree zero: `𝒪_W` is a flat `𝒪_W`-module, so `L p^*` of it is the ordinary pullback. -/
def dpullStructureSheafIso (p : V ⟶ W) :
    (dpull p).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        (SheafOfModules.unit W.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor V.Modules 0).obj (SheafOfModules.unit V.ringCatSheaf) :=
  Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso p.toLRSHom.toShHom _
      (Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_structureSheafModule
        W.toRingedSpace) ≪≫
    (DerivedCategory.singleFunctor V.Modules 0).mapIso
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso p.toLRSHom.toShHom)

end Notation

section Monoidal

variable (W : Scheme.{u})

/-- **Commutativity of the derived tensor product**, as an isomorphism of functors
`- ⊗^𝐋 A ≅ A ⊗^𝐋 -`. -/
def dtenRSwapIso (A : DerivedCategory W.Modules) : dtenR W A ≅ dtenLeft W A :=
  letI : MonoidalCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal W.toRingedSpace.sheaf
  letI : SymmetricCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric W.toRingedSpace.sheaf
  (BraidedCategory.tensorLeftIsoTensorRight A).symm

end Monoidal

end AlgebraicGeometry

end

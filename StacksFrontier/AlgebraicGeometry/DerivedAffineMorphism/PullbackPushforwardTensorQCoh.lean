module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08I9]: `Rf_*Lf^*E` is `E ⊗^𝐋 f_*𝒪_X` for an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes and let `E` be an object of `D_QCoh(𝒪_S)`.
[Stacks, Tag 08I9] identifies

`Rf_*Lf^*E ≅ E ⊗^𝐋_{𝒪_S} f_*𝒪_X`.

## Main results

* `isDQCoh_singleUnit`: the structure sheaf of a scheme placed in degree zero lies in
  `D_QCoh(𝒪_X)`.
* `isIso_projectionFormulaMap_singleUnit`: the projection-formula morphism of
  [Stacks, Tag 0B53] is invertible at the source complex `𝒪_X[0]`, for a quasi-compact and
  quasi-separated morphism of schemes and every `K` in `D_QCoh(𝒪_S)`.
* `derivedPushforwardDerivedPullbackIso`: `Rf_*𝒪_X ⊗^𝐋_{𝒪_S} K ≅ Rf_*Lf^*K`, for a
  quasi-compact and quasi-separated `f`.
* `derivedPushforwardDerivedPullbackTensorIso`: **[Stacks, Tag 08I9]**, the same with the
  *ordinary* direct image `f_*𝒪_X` placed in degree zero on the left, for `f` affine.

## How the tag is obtained

`Stacks.Cohomology.DerivedProjectionFormula.derivedPushforwardDerivedPullbackIsoOfIsIso`
already builds the isomorphism from one input: invertibility of the projection-formula morphism
of [Stacks, Tag 0B53] at the source complex `𝒪_X[0]` and an arbitrary target complex.  That is
[Stacks, Tag 08EU] at `E = 𝒪_X[0]`, and [Stacks, Tag 08EU] is proved unconditionally as
`Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh`.  So the two
restrictions that
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/PullbackPushforwardTensor.lean` carries —
the ordinary tensor product in place of `⊗^𝐋`, and `E` concentrated in degree zero — are both
lifted here, and no hypothesis beyond the source's is used.

The passage from the derived direct image `Rf_*(𝒪_X[0])` to the ordinary one `(f_*𝒪_X)[0]` is
[Stacks, Tag 01XC] for an affine morphism, available as
`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso`.

*The order of the tensor factors.*  The source writes `E ⊗^𝐋_{𝒪_S} f_*𝒪_X`; the
projection-formula morphism of [Stacks, Tag 0B53] produces the direct image as the left factor,
so the statements below read `f_*𝒪_X ⊗^𝐋_{𝒪_S} E`.  The derived tensor product of a ringed
space is symmetric, so this is the same statement.

*The model of the derived category.*  `CategoryTheory.HasDerivedCategory.standard`, at priority
`10000`, which is the model of both inputs; the category of modules is spelled
`SheafOfModules (structureSheafRing X.toRingedSpace)` for the same reason.

## References

* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.AlgebraicGeometry.AffinePullbackPushforwardTensor

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}}

/-- **The structure sheaf in degree zero lies in `D_QCoh`.**  Every term of the complex
`𝒪_X[0]` is quasi-coherent — the term in degree `0` is `𝒪_X` and the others vanish — so its
cohomology sheaves are. -/
theorem isDQCoh_singleUnit (Z : Scheme.{u}) :
    Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Z.toRingedSpace)
      (singleUnit Z.toRingedSpace) := by
  have : (_root_.SheafOfModules.isQuasicoherent
      (structureSheafRing Z.toRingedSpace)).IsClosedUnderKernels :=
    AlgebraicGeometry.isClosedUnderKernels_isQuasicoherent Z
  have : (_root_.SheafOfModules.isQuasicoherent
      (structureSheafRing Z.toRingedSpace)).IsClosedUnderCokernels :=
    AlgebraicGeometry.isClosedUnderCokernels_isQuasicoherent Z
  have hunit : (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.toRingedSpace.sheaf)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z
  have hQ : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Z.toRingedSpace)
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).obj
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.toRingedSpace.sheaf)))) :=
    Stacks.DerivedQCoh.isDQCoh_Q_obj (R := structureSheafRing Z.toRingedSpace)
      ((CochainComplex.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).obj
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.toRingedSpace.sheaf)))
      (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_singleFunctor_obj_X
        (W := Z) 0 _ hunit)
  exact Stacks.DerivedQCoh.isDQCoh_of_iso (R := structureSheafRing Z.toRingedSpace)
    (((DerivedCategory.singleFunctorIsoCompQ
      (_root_.SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).app
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.toRingedSpace.sheaf))).symm) hQ

/-- **[Stacks, Tag 08EU] at the source complex `𝒪_X[0]`.**  For a quasi-compact and
quasi-separated morphism of schemes `f : X ⟶ S` and every `K` in `D_QCoh(𝒪_S)`, the
projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*𝒪_X ⊗^𝐋_{𝒪_S} K ⟶ Rf_*(𝒪_X ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism.  This is the one input that [Stacks, Tag 08I9] needs. -/
theorem isIso_projectionFormulaMap_singleUnit (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing S.toRingedSpace) K) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom (singleUnit X.toRingedSpace) K) :=
  Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f
    (singleUnit X.toRingedSpace) K (isDQCoh_singleUnit X) hK

/-- **[Stacks, Tag 08I9] with the derived direct image of the structure sheaf**, and for a
quasi-compact and quasi-separated morphism rather than only an affine one:

`Rf_*𝒪_X ⊗^𝐋_{𝒪_S} K ≅ Rf_*Lf^*K`

for every `K` in `D_QCoh(𝒪_S)`.  The underlying morphism is the canonical one — the
projection-formula morphism of [Stacks, Tag 0B53] at `𝒪_X[0]` followed by `Rf_*` of the left
unit law — by construction of
`Stacks.Cohomology.DerivedProjectionFormula.pullbackPushforwardTensorMap`. -/
def derivedPushforwardDerivedPullbackIso (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing S.toRingedSpace) K) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj (singleUnit X.toRingedSpace))).obj K ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((derivedPullback f.toLRSHom.toShHom).obj K) :=
  derivedPushforwardDerivedPullbackIsoOfIsIso f.toLRSHom.toShHom
    (Stacks.RingedSpace.derivedTensorLeftUnitIso (Z := X.toRingedSpace)) K
    (isIso_projectionFormulaMap_singleUnit f K hK)

/-- **[Stacks, Tag 08I9].**  Let `f : X ⟶ S` be an affine morphism of schemes.  For every `K`
in `D_QCoh(𝒪_S)`,

`f_*𝒪_X ⊗^𝐋_{𝒪_S} K ≅ Rf_*Lf^*K`,

with the *ordinary* direct image of the structure sheaf placed in degree zero on the left and
the *derived* tensor product.  The left-hand factor is `(f_*𝒪_X)[0]` rather than `Rf_*(𝒪_X[0])`
by [Stacks, Tag 01XC] for an affine morphism, which is the first step of the source's proof. -/
@[stacks 08I9 "the whole lemma: for an affine morphism of schemes f : X ⟶ S and every K in \
D_QCoh(𝒪_S), the canonical map f_*𝒪_X ⊗ᴸ K ⟶ Rf_*Lf^*K is invertible. The tensor factors are \
written in the opposite order from the source, the derived tensor product of a ringed space \
being symmetric"]
def derivedPushforwardDerivedPullbackTensorIso (f : X ⟶ S) [IsAffineHom f]
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing S.toRingedSpace) K) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj
          ((modulePushforward f.toLRSHom.toShHom).obj
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf))))).obj K ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((derivedPullback f.toLRSHom.toShHom).obj K) :=
  haveI : IsSeparated f := IsSeparated.of_isAffineHom f
  ((derivedTensorProductFunctor S.toRingedSpace.sheaf).mapIso
      (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.derivedPushforwardSingleIso f 0
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf))
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X))).app K ≪≫
    derivedPushforwardDerivedPullbackIso f K hK

end Stacks.AlgebraicGeometry.AffinePullbackPushforwardTensor

end

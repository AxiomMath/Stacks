module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionComponent
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineHomRecovery
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# The canonical map `f^*ℳ_k ⟶ h^*(ℳ(k)~)` over an affine base

Situation 01NN fixes a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜`, and [Stacks, Tag
01O7] attaches to a quasi-coherent graded `𝒜`-module `ℳ` an `𝒪_{Proj_S(𝒜)}`-module `ℳ̃` whose
property (1) is a canonical isomorphism `ℳ̃_T ≅ h^*ℳ̃` for the morphism `h` a quadruple
classifies, `ℳ̃_T` being the module of [Stacks, Tag 01O6].

Over an **affine** base `S` the comparison is assembled summand by summand. The degree-`n`
summand of `ℳ̃_T` is `f^*ℳ_{nd} ⊗ L^{⊗(-n)}`, and
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedContractIso` already supplies

`φ^*(ℳ(dn)~) ⊗ L^{⊗(-n)} ≅ φ^*ℳ̃`

with the tensor product and the right-hand factor agreeing with [Stacks, Tag 01O6]'s on the nose.
The one map still missing was the **left** factor, `f^*ℳ_{nd} ⟶ φ^*(ℳ(nd)~)`. This file builds
it, in every degree `k : ℤ` and along an arbitrary morphism `h : Y ⟶ Proj Γ(S, 𝒜)` — no
quadruple, no twisting `ψ` and no invertible module are needed to state or prove it.

## The construction

`S` being affine and every homogeneous piece of `ℳ` quasi-coherent,
`Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv` identifies the morphisms
`f^*ℳ_k ⟶ h^*(ℳ(k)~)` with the `Γ(S, 𝒪_S)`-**linear** maps on global sections

`Γ(S, ℳ_k) ⟶ Γ(Y, h^*(ℳ(k)~))`,

the scalars acting on the target through `f^♯`. The linear map is prescribed: a homogeneous
global section of `ℳ_k` is a degree-`k` element of the graded module of sections
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.sectionModule`, hence names a
global section of `ℳ(k)~` on `Proj Γ(S, 𝒜)`, which the unit of `h^* ⊣ h_*` carries to `Y`. That
composite is `Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeN`, and its linearity is
`Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeN_smul_appTop` — the four steps

`Γ(S, 𝒪_S)`-action, degree-zero action, multiplication by `π^♯(a)`, `h^♯(π^♯(a)) = f^♯ r`,

the first of which is `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.strHom_smul_of`, applied
here through `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.coe_gradeZeroHom`.

The morphism `f : Y ⟶ S` is the one the degree-zero part recovers, `baseHom` below; by
`Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.comp_eq_of_appTop_eq` it is exactly the
`f` of a quadruple whose triple classifies `h`, so nothing is lost by building the arrow over
this `f`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.baseHom`: the morphism
  `f : Y ⟶ S` recovered from the degree-zero part, `h ≫ π ≫ Spec.map c ≫ (Spec Γ(S, 𝒪_S) ≅ S)`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.pullbackShifted`: the module
  `h^*(ℳ(k)~)` on `Y`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.sectionsLinearMap`: the
  degreewise `Γ(S, 𝒪_S)`-linear map on global sections.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.arrow`: **the canonical map
  `f^*ℳ_k ⟶ h^*(ℳ(k)~)`.**

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow.arrow_pullbackUnit`: **the
  arrow has the prescribed effect on the pullback-unit image of a homogeneous global section**,
  which is what characterises it.

## Scope

The arrow is not the isomorphism of property (1) of [Stacks, Tag 01O7]. On the route through it,
the balancing relations of the comparison are reduced by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.relation_of_intertwines` to
the one identity
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreewiseFamily.Intertwines`, which is a
hypothesis there; of this arrow's own contribution to it, `arrow_pullbackUnit` is the
evaluation on sections.

The comparison `ℳ̃_T ≅ h^*ℳ̃` of property (1) of [Stacks, Tag 01O7] is built by another route,
in `StacksFrontier/AlgebraicGeometry/RelativeProjQuadrupleTilde/`, which uses nothing from this file:
on a chart datum (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`) the
degreewise maps send `x ⊗ l` to `g^*(x / c^m) · (l · w^m)`, their balancing relations are
verified directly (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.bmap_balanced`), and the
inverse is written down.

## Implementation notes

`DirectSum.Decomposition` of `sectionModuleGrading` is a `def` rather than a global instance in
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionModule`, so it is taken as a local
instance here; it is named, not anonymous, which keeps the two spellings of the associated module
sheaf from diverging.

`ofPiece` is `AddMonoidHom.rangeRestrict` of the summand inclusion, and `sectionModuleGrading` is
*defined* as that inclusion's range, so the membership proof is `rfl` and `coe_ofPiece` records
that the underlying element is the summand inclusion itself. This is the module-side analogue of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.ofGrading`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (pullbackDegreeN pullbackDegreeN_add pullbackDegreeN_smul_appTop structureCompositeSharp)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.GradedModule (shiftedGrading)
open Stacks.RingedSpace (pullbackFunctor pullbackUnit)
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow

attribute [local instance] SheafGradedModule.sectionModuleDecomposition

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}}

/-- **The structure map `Γ(S, 𝒪_S) ⟶ A_0` of the graded `Γ(S, 𝒪_S)`-algebra `A = Γ(S, 𝒜)`**, as a
morphism of `CommRingCat`. It is the degree-zero corestriction of the structure map of the graded
ring of sections, the same datum as
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.structureRingHom`. -/
def structureRingHom (A : SheafGradedAlgebra S) :
    Γ(S, ⊤) ⟶ CommRingCat.of (A.grading (⊤ : S.Opens) 0) :=
  CommRingCat.ofHom (A.gradeZeroHom ⊤)

variable {A : SheafGradedAlgebra S} (𝔐 : SheafGradedModule A)
  {Y : Scheme.{u}} (h : Y ⟶ AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens)))

/-- **The morphism `f : Y ⟶ S` recovered from the degree-zero part.** For a morphism
`h : Y ⟶ Proj A`, `A = Γ(S, 𝒜)`, it is `h` followed by `Proj A ⟶ Spec A_0 ⟶ Spec Γ(S, 𝒪_S) ≅ S`.

By `Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.comp_eq_of_appTop_eq` this is the
morphism `T ⟶ S` that a quadruple whose triple classifies `h` carries, so the arrow built over it
is the arrow a quadruple asks for. -/
def baseHom (A : SheafGradedAlgebra S) [IsAffine S]
    (h : Y ⟶ AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens))) : Y ⟶ S :=
  h ≫ AlgebraicGeometry.Proj.toSpecZero (A.grading (⊤ : S.Opens)) ≫
    Spec.map (structureRingHom A) ≫ S.isoSpec.inv

/-- **The module `h^*(ℳ(k)~)` on `Y`**: the pullback along `h` of the sheaf associated to the
degree-`k` shift of the graded module of global sections of `ℳ`. -/
def pullbackShifted (k : ℤ) : Y.Modules :=
  (pullbackFunctor h.toLRSHom.toShHom).obj
    (associatedModuleSheaf (A.grading (⊤ : S.Opens))
      (shiftedGrading (𝔐.sectionModuleGrading (⊤ : S.Opens)) k))

/-- **The degree-`k` homogeneous element of the graded module of global sections of `ℳ` named by
a global section of `ℳ_k`**: the inclusion of the degree-`k` summand, corestricted to its range,
which is by definition the degree-`k` part of the grading. -/
def ofPiece (k : ℤ) :
    Γ(𝔐.piece k, ⊤) →+ 𝔐.sectionModuleGrading (⊤ : S.Opens) k :=
  (DirectSum.of (𝔐.sectionModulePieces (⊤ : S.Opens)) k).rangeRestrict

/-- The element of the module of sections underlying `ofPiece` is the summand inclusion. -/
theorem coe_ofPiece (k : ℤ) (x : Γ(𝔐.piece k, ⊤)) :
    ((ofPiece 𝔐 k x : 𝔐.sectionModuleGrading (⊤ : S.Opens) k) : 𝔐.sectionModule (⊤ : S.Opens))
      = DirectSum.of (𝔐.sectionModulePieces (⊤ : S.Opens)) k x := rfl

/-- **The degreewise `Γ(S, 𝒪_S)`-linear map on global sections** that the arrow is recovered
from: a global section of `ℳ_k` is read as a degree-`k` element of the graded module of global
sections, which names a global section of `ℳ(k)~` on `Proj A`, pulled back to `Y` along `h`.

Linearity is the four-step chain of
`Stacks.AlgebraicGeometry.ProjShiftedSections.pullbackDegreeN_smul_appTop`, whose first step —
that a function on `S` acts on homogeneous sections as the degree-zero scalar it names — is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.strHom_smul_of`. The scalars act on the target
through `f^♯` for `f = baseHom`, which is what the target's module structure, the sections of
`f_*h^*(ℳ(k)~)` over `⊤`, already says; that is why the last step of the chain closes the
`map_smul'` field by `rfl`. -/
def sectionsLinearMap [IsAffine S] (k : ℤ) :
    Γ(𝔐.piece k, ⊤) →ₗ[Γ(S, ⊤)]
      Γ(AffineHomRecovery.pushforward (baseHom A h) (pullbackShifted 𝔐 h k), ⊤) where
  toFun x :=
    pullbackDegreeN (A.grading (⊤ : S.Opens)) (𝔐.sectionModuleGrading (⊤ : S.Opens)) h k
      (ofPiece 𝔐 k x)
  map_add' x y := by
    change pullbackDegreeN _ _ h k (ofPiece 𝔐 k (x + y)) = _
    rw [map_add (ofPiece 𝔐 k), pullbackDegreeN_add]
    rfl
  map_smul' r x := by
    change pullbackDegreeN _ _ h k (ofPiece 𝔐 k (r • x)) = _
    rw [pullbackDegreeN_smul_appTop (A.grading (⊤ : S.Opens)) (structureRingHom A)
      (𝔐.sectionModuleGrading (⊤ : S.Opens)) h k r (ofPiece 𝔐 k x) (ofPiece 𝔐 k (r • x))
      (strHom_smul_of 𝔐 ⊤ r x).symm]
    rfl

/-- **The canonical map** `f^*ℳ_k ⟶ h^*(ℳ(k)~)`

over an affine base `S`, for an arbitrary morphism `h : Y ⟶ Proj Γ(S, 𝒜)` and `f` the morphism
`Y ⟶ S` the degree-zero part recovers: the morphism out of the pullback that
`Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv` recovers from `sectionsLinearMap`.

This is the left factor of the degree-`n` component of the comparison `ℳ̃_T ≅ h^*ℳ̃` of property
(1) of [Stacks, Tag 01O7] on the route whose right factor is
`Stacks.AlgebraicGeometry.PullbackTwistPower.pullbackShiftedContractIso`. It is not itself a
clause of that tag, and the comparison of property (1) is built by another route, without this
arrow: see the module docstring. -/
def arrow [IsAffine S] (k : ℤ) :
    (pullbackFunctor (baseHom A h).toLRSHom.toShHom).obj (𝔐.piece k) ⟶ pullbackShifted 𝔐 h k :=
  (AffineHomRecovery.homEquiv (baseHom A h) (𝔐.piece k) (pullbackShifted 𝔐 h k)).symm
    (sectionsLinearMap 𝔐 h k)

/-- **The arrow has the prescribed effect on the pullback-unit image of a homogeneous global
section**, which is what characterises it: a morphism out of `f^*ℳ_k` over an affine base is
determined by its values there. -/
theorem arrow_pullbackUnit [IsAffine S] (k : ℤ) (x : Γ(𝔐.piece k, ⊤)) :
    (arrow 𝔐 h k).val.app ((opensMap (baseHom A h).toLRSHom.toShHom).op.obj (op ⊤))
        (pullbackUnit (baseHom A h).toLRSHom.toShHom (𝔐.piece k) (op ⊤) x)
      = pullbackDegreeN (A.grading (⊤ : S.Opens)) (𝔐.sectionModuleGrading (⊤ : S.Opens)) h k
          (ofPiece 𝔐 k x) := by
  have hh : AffineHomRecovery.sectionsMap (baseHom A h) (𝔐.piece k) (pullbackShifted 𝔐 h k)
      (arrow 𝔐 h k) = sectionsLinearMap 𝔐 h k :=
    (AffineHomRecovery.homEquiv (baseHom A h) (𝔐.piece k)
      (pullbackShifted 𝔐 h k)).apply_symm_apply _
  exact (Stacks.RingedSpace.homEquiv_val_app (baseHom A h).toLRSHom.toShHom
    (𝔐.piece k) (pullbackShifted 𝔐 h k) (arrow 𝔐 h k) (op ⊤) x).symm.trans
    (DFunLike.congr_fun hh x)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ChartShiftedArrow

end

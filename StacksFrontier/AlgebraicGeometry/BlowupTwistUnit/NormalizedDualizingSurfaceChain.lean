module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.TopFormsNormalizedDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedModelOnAffineLocalBase
public import StacksFrontier.AlgebraicGeometry.Duality.SurfaceDualizingDegree.NormalizedUpperShriek
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMapsUnconditional
public import StacksFrontier.RingTheory.Dualizing.RegularLocalNormalizedShift

/-!
# `ω_W = h^!ω_S^•` is normalized relative to `ω_S` along a sequence of point blowups

Let `S` be affine with `A = Γ(S, ⊤)` a regular local ring of dimension two, let `ω_S^•` be an
object of `D_QCoh(𝒪_S)` modelled on `S` by a normalized dualizing complex `ω_A^•` over `A`, and
let `h : W ⟶ S` be a sequence of blowups in closed points. Writing `ω_W = H^{-2}(h^!ω_S^•)` for
the relative dualizing module of [Stacks, Tag 0AWI], this file proves

`h^×(ω_S[0]) ≅ ω_W[0]`   in `D_QCoh(𝒪_W)`,

the *normalization* of `ω_W` relative to `ω_S` in the sense of [Stacks, Remark 0B4R] and the
shape of the field `Stacks.BlowupTwistUnit.NormalizedTopFormData.normalized`.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `baseDualizingShiftIso`: the base presentation `ω_S^• ≅ ω_S[0]⟦2⟧`.
* `relativeDualizingModuleIdIso`: the value of the family at the bottom stage is the dualizing
  module `H^{-2}(ω_S^•)` of `S` itself.
* `normalizedIsoOfIsNormalSurface`: `h^×(ω_S[0]) ≅ ω_W[0]` for a proper morphism from a connected
  normal scheme of dimension two.
* `chainDualizingModule`: the family `ω W h = H^{-2}(h^!ω_S^•)`, as a total function of the stage.
* `normalizedChainDualizingModule`: the same isomorphism in the shape of the field
  `NormalizedTopFormData.normalized` for that family.

## Main results

* `exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top_of_isRegularLocalRing`: the
  input pair `(ω_S^•, ω_A^•)` exists as soon as `Γ(S, ⊤)` is regular local, with nothing assumed
  about dualizing complexes.
* `normalizedIsoOfPointBlowupChain`: the normalization at every stage of a sequence of blowups in
  closed points of an integral Noetherian surface regular of dimension two.
* `isQuasicoherent_chainDualizingModule`: the family is quasi-coherent.

## Implementation notes

The field `NormalizedTopFormData.ω` is a total function of the pair `(W, h)`, but
`Stacks.Duality.relativeDualizingModule h _ ω_S^•` is formed only when `h` is quasi-compact and
quasi-separated with a right adjoint available for `Rh_*`, which a sequence of blowups supplies.
So `chainDualizingModule` branches on the sequence and takes the value `𝒪_W` off it, and
`chainDualizingModule_eq` describes it on the sequence.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Remark 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Duality
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.BlowupTwistUnit

variable {S : Scheme.{u}} [IsAffine S] [AlgebraicGeometry.IsNoetherian S]
  [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]

/-! ### The base presentation `ω_S^• ≅ ω_S[0]⟦2⟧` -/

/-- **`ω_S^• ≅ ω_S[0]⟦2⟧` on a normal surface base**, the presentation of the dualizing complex
of the base in terms of its own dualizing module. -/
def baseDualizingShiftIso [ConnectedSpace S] (hnormal : IsNormal S)
    (hdim : topologicalKrullDim S = 2)
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    ωS.obj ≅ ((DerivedCategory.singleFunctor S.Modules 0).obj
        (relativeDualizingModule (𝟙 S)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S)) ωS))⟦(2 : ℤ)⟧ :=
  ((ObjectProperty.ι _).mapIso
      ((twistedInverseImageIdIso S
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).app ωS)).symm ≪≫
    relativeDualizingComplexIsoShiftTwoOfIsNormalSurface (𝟙 S) hnormal hdim ωS ω hω hmodel

/-- **`ω_S^•` carries the dualizing module of `S` in degree `-2`**: the value of the family
`ω W h = H^{-2}(h^!ω_S^•)` at the bottom stage `h = 𝟙 S` is the dualizing module `H^{-2}(ω_S^•)`
of `S` itself. -/
def relativeDualizingModuleIdIso (hdim : topologicalKrullDim S = 2)
    (ωS : quasiCoherentDerivedCategory S) :
    relativeDualizingModule (𝟙 S)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S)) ωS ≅
      (DerivedCategory.homologyFunctor S.Modules (-2 : ℤ)).obj ωS.obj :=
  eqToIso (by rw [relativeDualizingModule, show
      (-(ENat.toNat ((topologicalKrullDim S).getD 0) : ℤ)) = (-2 : ℤ) by rw [hdim]; rfl]; rfl) ≪≫
    (DerivedCategory.homologyFunctor S.Modules (-2 : ℤ)).mapIso ((ObjectProperty.ι _).mapIso
      ((twistedInverseImageIdIso S
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S))).app ωS))

/-! ### The normalization `h^×(ω_S[0]) ≅ ω_W[0]` -/

/-- **`h^×(ω_S[0]) ≅ ω_W[0]`**: the relative dualizing module of a proper morphism from a
connected normal scheme of dimension two to a normal surface base is normalized relative to the
dualizing module of the base. -/
def normalizedIsoOfIsNormalSurface [ConnectedSpace S] (hnormal : IsNormal S)
    (hdim : topologicalKrullDim S = 2)
    {W : Scheme.{u}} (h : W ⟶ S) [IsProper h] [ConnectedSpace W]
    (hWnormal : IsNormal W) (hWdim : topologicalKrullDim W = 2)
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj
        (singleQuasiCoherent (relativeDualizingModule (𝟙 S)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S)) ωS)
          (isQuasicoherent_relativeDualizingModule _ _ ωS) 0)).obj ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj (relativeDualizingModule h
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h) ωS) :=
  letI := (twistedInverseImageAdjunction h
    (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).rightAdjointCommShift ℤ
  let A : quasiCoherentDerivedCategory S :=
    singleQuasiCoherent (relativeDualizingModule (𝟙 S)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S)) ωS)
      (isQuasicoherent_relativeDualizingModule _ _ ωS) 0
  let B : quasiCoherentDerivedCategory W :=
    singleQuasiCoherent (relativeDualizingModule h
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h) ωS)
      (isQuasicoherent_relativeDualizingModule _ _ ωS) 0
  let eS : ωS ≅ (shiftFunctor (quasiCoherentDerivedCategory S) (2 : ℤ)).obj A :=
    ObjectProperty.isoMk _ (baseDualizingShiftIso hnormal hdim ωS ω hω hmodel ≪≫
      (((ObjectProperty.ι _).commShiftIso (2 : ℤ)).app A).symm)
  let eW : (twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj ωS ≅
        (shiftFunctor (quasiCoherentDerivedCategory W) (2 : ℤ)).obj B :=
    ObjectProperty.isoMk _
      (relativeDualizingComplexIsoShiftTwoOfIsNormalSurface h hWnormal hWdim ωS ω hω hmodel ≪≫
        (((ObjectProperty.ι _).commShiftIso (2 : ℤ)).app B).symm)
  (ObjectProperty.ι _).mapIso
    ((shiftFunctor (quasiCoherentDerivedCategory W) (2 : ℤ)).preimageIso
      ((((twistedInverseImage h
            (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).commShiftIso
          (2 : ℤ)).app A).symm ≪≫
        (twistedInverseImage h
          (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).mapIso eS.symm ≪≫ eW))

/-! ### The input pair on a regular local base -/

section Regular

variable {S : Scheme.{u}} [IsAffine S] [AlgebraicGeometry.IsNoetherian S]
  [IsRegularLocalRing Γ(S, ⊤)]

/-- **A regular local ring of global sections supplies the pair `(ω_S^•, ω_A^•)`.** If
`Γ(S, ⊤)` is a regular local ring, there are a normalized dualizing complex `ω` over `Γ(S, ⊤)`
and an object `ω_S^•` of `D_QCoh(𝒪_S)` modelled on `S` by `ω`. -/
theorem exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top_of_isRegularLocalRing :
    ∃ (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤))),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω ∧
        IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω := by
  obtain ⟨d, -, hd⟩ :=
    Dualizing.exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift
      Γ(S, ⊤)
  exact exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top _ hd.1

end Regular

/-! ### Along a sequence of blowups in closed points -/

/-- **The normalization at every stage of a sequence of blowups in closed points.** For `S` an
integral Noetherian surface regular of dimension two and `h : W ⟶ S` a sequence of blowups in
closed points, `h^×(ω_S[0]) ≅ ω_W[0]`. -/
def normalizedIsoOfPointBlowupChain (hS : IsIntegralRegularSurface S) {T : Set S}
    {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    haveI := compactSpace_of_pointBlowupChain hc
    haveI := quasiSeparatedSpace_of_pointBlowupChain hc
    haveI := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).2
    ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj
        (singleQuasiCoherent (relativeDualizingModule (𝟙 S)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 S)) ωS)
          (isQuasicoherent_relativeDualizingModule _ _ ωS) 0)).obj ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj (relativeDualizingModule h
        (isQuasicoherent_homology_derivedPushforward_of_qcqs h) ωS) :=
  haveI := compactSpace_of_pointBlowupChain hc
  haveI := quasiSeparatedSpace_of_pointBlowupChain hc
  haveI := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).2
  haveI := hS.isIntegral
  haveI := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).1.1
  normalizedIsoOfIsNormalSurface (isNormal_of_isRegular S hS.isRegular)
    hS.topologicalKrullDim_eq h
    (isNormal_of_isRegular W
      (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).1.isRegular)
    (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional
      hc hS).1.topologicalKrullDim_eq
    ωS ω hω hmodel

/-- **The family `ω_W = H^{-2}(h^!ω_S^•)` of dualizing modules along the sequence**, as a total
function of the stage; off the sequence its value is `𝒪_W`. -/
def chainDualizingModule (hS : IsIntegralRegularSurface S) (T : Set S)
    (ωS : quasiCoherentDerivedCategory S) (W : Scheme.{u}) (h : W ⟶ S) : W.Modules :=
  letI := Classical.propDecidable (PointBlowupChain S T W h)
  if hc : PointBlowupChain S T W h then
    haveI := compactSpace_of_pointBlowupChain hc
    haveI := quasiSeparatedSpace_of_pointBlowupChain hc
    haveI := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).2
    relativeDualizingModule h (isQuasicoherent_homology_derivedPushforward_of_qcqs h) ωS
  else SheafOfModules.unit W.ringCatSheaf

omit [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)] in
/-- **At a stage of the sequence the family is the relative dualizing module.** -/
theorem chainDualizingModule_eq (hS : IsIntegralRegularSurface S) {T : Set S}
    (ωS : quasiCoherentDerivedCategory S) {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) :
    chainDualizingModule hS T ωS W h =
      haveI := compactSpace_of_pointBlowupChain hc
      haveI := quasiSeparatedSpace_of_pointBlowupChain hc
      haveI := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).2
      relativeDualizingModule h (isQuasicoherent_homology_derivedPushforward_of_qcqs h) ωS :=
  dite_eq_left hc

omit [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)] in
/-- **Each dualizing module of the family is quasi-coherent.** -/
theorem isQuasicoherent_chainDualizingModule (hS : IsIntegralRegularSurface S) {T : Set S}
    (ωS : quasiCoherentDerivedCategory S) {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) :
    (chainDualizingModule hS T ωS W h).IsQuasicoherent := by
  rw [chainDualizingModule_eq hS ωS hc]
  have := compactSpace_of_pointBlowupChain hc
  have := quasiSeparatedSpace_of_pointBlowupChain hc
  have := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).2
  exact isQuasicoherent_relativeDualizingModule _ _ ωS

/-- **`h^×(ω_S[0]) ≅ ω_W[0]` for the family `ω_W = H^{-2}(h^!ω_S^•)`** at every stage of a
sequence of blowups in closed points, with both sides written through
`Stacks.BlowupTwistUnit.chainDualizingModule`, in the shape of the field
`NormalizedTopFormData.normalized`. -/
def normalizedChainDualizingModule (hS : IsIntegralRegularSurface S) {T : Set S}
    (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω)
    {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h) :
    haveI := compactSpace_of_pointBlowupChain hc
    haveI := quasiSeparatedSpace_of_pointBlowupChain hc
    ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj
        (singleQuasiCoherent (chainDualizingModule hS T ωS S (𝟙 S))
          (isQuasicoherent_chainDualizingModule hS ωS PointBlowupChain.refl) 0)).obj ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj (chainDualizingModule hS T ωS W h) := by
  haveI := compactSpace_of_pointBlowupChain hc
  haveI := quasiSeparatedSpace_of_pointBlowupChain hc
  haveI := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc hS).2
  refine ?_ ≪≫ normalizedIsoOfPointBlowupChain hS hc ωS ω hω hmodel ≪≫
    (DerivedCategory.singleFunctor W.Modules 0).mapIso
      (eqToIso (chainDualizingModule_eq hS ωS hc)).symm
  exact (ObjectProperty.ι _).mapIso ((twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).mapIso
    (ObjectProperty.isoMk _ ((DerivedCategory.singleFunctor S.Modules 0).mapIso
      (eqToIso (chainDualizingModule_eq hS ωS PointBlowupChain.refl)))))

end Stacks.BlowupTwistUnit

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneralRegistration
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.ConnectedLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.LocalStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.StructureMapBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneral

/-!
# The Stein factorization of a flat proper morphism with reduced fibres is finite étale

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` and `X ⟶ Y' ⟶ Y` its Stein
factorization (Stacks 0A1C), the factorization through the normalization `Y'` of `Y` in `X`
(`AlgebraicGeometry.Space.normalizationInQcqs`).  Stacks 0E0D: if `f` is of finite presentation,
flat, with geometrically reduced fibres (Stacks 0E08), then `Y' ⟶ Y` is finite étale.

This module proves the statement from three inputs, stated in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiInputs` (Stacks 0E0R (1), (2) and
Stacks 0E0S); `StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFlatProperFiniteEtale`
discharges them and records the tag.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.isFinite_and_isEtale_normalizationInQcqsHom_of_inputs`:
  Stacks 0E0D, for the Stein factorization of the library, from the three inputs.

## References

* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0E0S](https://stacks.math.columbia.edu/tag/0E0S)
* [Stacks Project, Tag 0E1E](https://stacks.math.columbia.edu/tag/0E1E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0E0S, read on global functions over an affine base.**  For `g : P ⟶ h_U` proper, flat,
finitely presented, with geometrically reduced and connected geometric fibres, pulling back along
`g` identifies the regular functions on `U` with the global functions on `P`. -/
theorem bijective_pullbackToGlobalFunctions_of_properFlatStructureSharp
    (hpush : StructureSharpOfGeometricFibresInput B S hS)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (U : BigFppfOver B S hS) (_hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : P ⟶ yoneda.obj U) (hgp : IsProper B S hS g) (hgfl : IsFlat B S hS g)
    (hgfp : IsFinitePresentation B S hS g)
    (hgred : ∀ z, IsGeometricallyReducedFibreAt B S hS g hP (isAlgebraicSpace_yoneda B S hS U) z)
    (hgconn : ∀ t : GeometricPoint B S hS (yoneda.obj U),
      ConnectedPullback B S hS g (yonedaEquiv.symm t.val.value)) :
    Function.Bijective (pullbackToGlobalFunctions B S hS ⟨P, hP⟩ U
      (ObjectProperty.homMk g)) := by
  have hU := isAlgebraicSpace_yoneda B S hS U
  let G : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace U := ObjectProperty.homMk g
  have hred' : ∀ y : GeometricPoint B S hS (yoneda.obj U),
      HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS g y.1)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T) := fun y =>
    (isGeometricallyReducedFibreAt_iff_forall_isReduced B S hS g hP hU y.image).1 (hgred _) y.1
      rfl
  have hconn' : ∀ y : GeometricPoint B S hS (yoneda.obj U),
      ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS g y.1) := fun y =>
    (connectedPoints_fibreOverFieldValuedPoint_iff B S hS hP hU g y.1).2 (hgconn y)
  have hid : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U)) := by
    have := isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.id_mem _ _
  exact bijective_pullbackToGlobalFunctions_of_isIso_structureSharp B S hS G
    (hpush G hgp hgfl hgfp hred' hconn').1 U (𝟙 (yoneda.obj U)) hid hP (𝟙 P) g
    IsPullback.of_id_fst

/-- **Stacks 0E0D, from the three inputs.**  Let `f : X ⟶ Y` be a proper morphism of algebraic
spaces over `S`, with Stein factorization `X ⟶ Y' ⟶ Y` (Stacks 0A1C: `Y'` is the normalization of
`Y` in `X`, `AlgebraicGeometry.Space.normalizationInQcqs`).  If `f` is of finite presentation,
flat, with geometrically reduced fibres (Stacks 0E08), then `Y' ⟶ Y` is finite and étale. -/
theorem isFinite_and_isEtale_normalizationInQcqsHom_of_inputs
    (hBC : FibreBettiBaseChangeInput B S hS) (hUSC : UpperSemicontinuousFibreBettiInput B S hS)
    (h0E0S : StructureSharpOfGeometricFibresInput B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS f.hom X.2 Y.2 y) :
    let h := isQuasiCompact_isQuasiSeparated_of_isProper B S hS f hf
    IsFinite B S hS (normalizationInQcqsHom B S hS f h.1 h.2).hom ∧
      IsEtale B S hS (normalizationInQcqsHom B S hS f h.1 h.2).hom := by
  intro h
  have hfqc := h.1
  have hfqs := h.2
  have hsharp := isIso_fSharp_toNormalizationInQcqs f hfqc hfqs hf.2.2
  have hconn := connectedPullback_of_isProper_of_isIso_fSharp_unconditional
    (toNormalizationInQcqs f hfqc hfqs) (isProper_toNormalizationInQcqs B S hS f hfqc hfqs hf)
    (isSurjective_toNormalizationInQcqs B S hS f hfqc hfqs hf.2.2) hsharp
  rw [← toNormalizationInQcqs_comp_hom B S hS f hfqc hfqs] at hf hfl hfp hred
  exact isFinite_and_isEtale_of_stein_of_inputs B S hS X.2 Y.2
    (normalizationInQcqs B S hS f hfqc hfqs).2 (toNormalizationInQcqs f hfqc hfqs).hom
    (normalizationInQcqsHom B S hS f hfqc hfqs).hom
    (isAffineHom_normalizationInQcqsHom B S hS f hfqc hfqs)
    (isIntegralHom_normalizationInQcqsHom f hfqc hfqs) hf hfl hfp hred hconn
    (fun V _ c hc _ hP a b sq =>
      bijective_pullbackToGlobalFunctions_of_isIso_fSharp B S hS _ hsharp V c hc hP a b sq)
    (bijective_pullbackToGlobalFunctions_of_properFlatStructureSharp B S hS h0E0S)
    (fun hP Z g hgp hgfl hgfp hgred =>
      isOpen_setOf_numberGeometricConnectedComponents_eq_one
        (ObjectProperty.homMk g : (⟨_, hP⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩) hBC hUSC h0E0S hgp hgfl hgfp hgred)

end AlgebraicGeometry.Space.ProperFlatStein

end

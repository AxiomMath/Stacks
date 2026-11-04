module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeSectionMap
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackUnitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsFlatBaseChangeSpan
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic

/-!
# Sections of the tensor powers of an invertible module on an algebraic space over an affine
scheme, at a point of a flat scheme chart

Let `Z` be an algebraic space over an affine scheme `T₀` of the big fppf site, with
quasi-compact and quasi-separated structure morphism `π`, let `𝓛` be an invertible
`𝒪_Z`-module, and let

```
h_U --w--> Z
 |         |π
 v         v
h_T' --u--> h_T₀
```

be a cartesian square with `T'` affine and `u` flat, in which `Z ×_{T₀} T'` is the scheme `U`.
If the base change of `𝓛` to `U` is ample, then every point `x` of `U` lies off the support of
the cokernel of the map of `𝒪_U`-modules corresponding to `w^*(𝒪_Z ⟶ 𝓛^{⊗ n})` for some `n ≥ 1`
and some global section of `𝓛^{⊗ n}` on `Z`. This is the step of Stacks 0D3C in which the
sections of the base change are written in terms of sections on `Z`: global sections commute
with flat base change (Stacks 073K), so the sections over `U` are linear combinations of
pullbacks of sections over `Z`, and a sum is a generator at `x` only if a summand is.

## Main results

* `AlgebraicGeometry.Space.exists_notMem_supp_cokernel_chartPullbackSchemeMap`: the statement
  above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

/-- **A point of a flat scheme chart lies in the surjectivity locus of the map named by some
global section of some tensor power.** See the module docstring. -/
theorem exists_notMem_supp_cokernel_chartPullbackSchemeMap {Z : AlgebraicSpaces B S hS}
    {T₀ T' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (π : Z ⟶ (⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩ : AlgebraicSpaces B S hS))
    (hqc : IsQuasiCompact B S hS π.hom) (hqs : IsQuasiSeparated B S hS π.hom)
    (u : T' ⟶ T₀) (hu : Flat ((BigFppfOver.toScheme B S hS).map u)) (q : U ⟶ T')
    (w : yoneda.obj U ⟶ Z.1) (hsq : IsPullback w (yoneda.map q) π.hom (yoneda.map u))
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS Z.1 Z.2).obj
      (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      ((modulePullback B S hS (chartSpaceMap w)).obj L)]
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U w)]
    (hamp : Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U w))
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : (natTensorPow (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)))
        L n).sections,
      x ∉ _root_.SheafOfModules.supp (cokernel (chartPullbackSchemeMap
        (h𝓖 := SheafOfModules.isQuasicoherentOnSite_unit _)
        (h𝓕 := isQuasicoherentOnSite_natTensorPow_of_isInvertible L n)
        ((SheafOfModules.unitHomEquiv _).symm σ) w)) := by
  obtain ⟨n, hn, s, O, hO, hxO, -⟩ := hamp.2 x
  refine ⟨n, hn, ?_⟩
  have hFq := isQuasicoherentOnSite_natTensorPow_of_isInvertible L n
  let Ln := natTensorPow (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)))
        L n
  -- the tensor power, read on the scheme
  let θ := natTensorPowIsoChartSchemeTarget L w n
  let 𝓖q : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
    @chartPullbackQcoh B S hS Z U w Ln hFq
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (chartScheme (idEtaleChart B S hS U)).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme
            (idEtaleChart B S hS U)))))
        (baseChangeModule B S hS L U w) n) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ (baseChangeModule B S hS L U w) (n : ℤ)
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj 𝓖q).obj :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ θ
  -- the map named by the section `s`, carried to the module corresponding to `w^*𝓛^{⊗ n}`
  let φ₀ : ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj
      (chartUnitQcoh U)).obj ⟶
        ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj 𝓖q).obj :=
    (chartSchemeUnitIso U).inv ≫ Stacks.SheafOfModules.unitHom _ s ≫ θ.hom
  have hφ₀ : x ∉ _root_.SheafOfModules.supp (cokernel φ₀) :=
    (Stacks.CokernelSupport.notMem_supp_cokernel_iso_comp_iff (chartSchemeUnitIso U).symm _ x).mpr
      ((Stacks.CokernelSupport.notMem_supp_cokernel_comp_iso_iff _ θ x).mpr
        (Stacks.CokernelSupport.notMem_supp_cokernel_unitHom s x (hO ▸ hxO)))
  obtain ⟨ψ₀, hψ₀⟩ := exists_chartSectionMap_eq (𝓐 := chartUnitQcoh U) (𝓖 := 𝓖q) φ₀
  -- the flat base change square, as a diagram of algebraic spaces
  have hsq' : IsPullback (chartSpaceMap w) (representedSpaceMap B S hS q) π
      (representedSpaceMap B S hS u) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) hsq
  have : IsIso (idEtaleChart B S hS T₀).obj.hom := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso (idEtaleChart B S hS T').obj.hom := inferInstanceAs (IsIso (𝟙 _))
  have : IsAffine (chartScheme (idEtaleChart B S hS T₀)) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
  have : IsAffine (chartScheme (idEtaleChart B S hS T')) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
  have hflat : IsFlat B S hS (representedSpaceMap B S hS u).hom :=
    holdsOnEveryEtaleChart_yoneda_map B S hS Flat.isEtaleLocalOnSourceAndTarget u hu
  have hspan := mem_span_range_pullbackSection hsq' Ln
    (hF := hFq) (idEtaleChart B S hS T₀) (idEtaleChart B S hS T') hflat hqc hqs
    (SheafOfModules.unitHomEquiv 𝓖q.obj ψ₀)
  obtain ⟨σ, hσ⟩ := exists_notMem_supp_cokernel_of_mem_span 𝓖q x _ _ hspan
    (((congrArg chartSectionMap ((SheafOfModules.unitHomEquiv 𝓖q.obj).symm_apply_apply ψ₀)).trans
      hψ₀) ▸ hφ₀)
  have hP := unitHomEquiv_symm_globalSectionsPullbackMap (chartSpaceMap w) Ln σ
  have h₁ := (congrArg (chartSectionMap (𝓐 := chartUnitQcoh U) (𝓖 := 𝓖q)) hP).trans
    (chartSectionMap_comp (𝓑 := @chartPullbackQcoh B S hS Z U w
          (SheafOfModules.unit _) (SheafOfModules.isQuasicoherentOnSite_unit _)) _ _)
  exact ⟨σ, Stacks.CokernelSupport.notMem_supp_cokernel_of_comp _ _ x (h₁ ▸ hσ)⟩

end AlgebraicGeometry.Space

end

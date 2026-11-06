module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartFinitePresentation

/-!
# The canonical chain map on the kernels of the differentials

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a diagram of
étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R` of `Y`.
Write `Γ` for the ring of global functions of the small étale site of `X` localized at `V`,
`N ↦ N ⊗_A 𝒪` for the functor `AlgebraicGeometry.Space.chartTensorFunctor`, and
`H = H₁(L_{A/R})`, the kernel of the differential `δ : I/I² ⟶ Ω ⊗ A` of the canonical naive
cotangent complex `NL_{A/R}`.

This file proves that the canonical chain map `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V` of
`StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartFinitePresentation` induces an
isomorphism on the kernels of the two differentials.  The proof:

* `M ↦ M ⊗_Γ 𝒪` preserves monomorphisms (`AlgebraicGeometry.Space.mono_chartSectionTensor_map`,
  the stalks of `𝒪_X` being flat over `A`) and cokernels (it is a left adjoint), so it preserves
  kernels; hence `H ⊗_Γ 𝒪 ⟶ (I/I²) ⊗_A 𝒪` is a kernel of `δ ⊗_A 𝒪`;
* restriction to the slice at `V` preserves kernels, so the kernel of the restricted
  differential of `NL_{X/Y}` is the restriction `𝒦|_V` of its kernel `𝒦`;
* under these identifications the map on kernels is the isomorphism `H ⊗_Γ 𝒪 ≅ 𝒦|_V` of
  `AlgebraicGeometry.Space.chartKernelSliceHom`, which is checked on global sections through
  the universal property of `H ⊗_Γ 𝒪`.

## Main results

* `AlgebraicGeometry.Space.chartH1TensorKernelIso`: `H ⊗_Γ 𝒪` is the kernel of `δ ⊗_A 𝒪`.
* `AlgebraicGeometry.Space.chartH1Inclusion_conormalTensorHom`: the degree `-1` component of the
  chain map restricted to `H ⊗_Γ 𝒪` is `H ⊗_Γ 𝒪 ≅ 𝒦|_V` followed by the inclusion of `𝒦|_V`.
* `AlgebraicGeometry.Space.isIso_chartKernelMap`: the map induced on the kernels of the two
  differentials is an isomorphism.

## References

* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
  TensorProduct Stacks.Cohomology.SiteModules Algebra

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace AlgebraicGeometry.Space

open Stacks.NaiveCotangentFinitePresentation

attribute [local instance] chartDiagramAlgebraInst

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-! ### The adjunct of `H ⊗_Γ 𝒪 ≅ 𝒦|_V` -/

/-- **The adjunct of `H ⊗_Γ 𝒪 ⟶ 𝒦|_V`** under `M ⊗_Γ 𝒪 ⊣ Γ` is the `Γ`-linear map
`H ⟶ Γ(𝒦|_V)` it was built from. -/
theorem chartKernelSliceHom_homEquiv :
    (sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv _ _
      (chartKernelSliceHom B S hS f d) = chartKernelTheta B S hS f d := by
  have h : (sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv =
      sectionTensorHomEquiv.{u + 1, u, u, u} (chartSliceRing B S hS f d) :=
    Adjunction.mkOfHomEquiv_homEquiv _
  refine (DFunLike.congr_fun (congrFun (congrFun h _) _) _).trans ?_
  refine (congrArg (sectionTensorPresheafHomEquiv.{u + 1, u, u, u}
    (O := chartSliceRing B S hS f d) _ _) (Equiv.apply_symm_apply _ _)).trans ?_
  exact (sectionTensorPresheafHomEquiv.{u + 1, u, u, u} (O := chartSliceRing B S hS f d) _
    _).apply_symm_apply _

/-! ### `H` as the kernel of the differential, read over `Γ` -/

/-- **The inclusion `H ⟶ I/I²`** of `H₁(L_{A/R})` into the conormal module of the canonical
presentation of `A` over `R`, read over `Γ`. -/
def chartH1Inclusion :
    chartH1GlobalModule B S hS f d ⟶
      (chartModuleLift B S hS f d).obj (nlMod₁ (chartCanonicalGenerators B S hS f d)) :=
  ModuleCat.ofHom (X := chartH1GlobalModule B S hS f d)
      (Y := (chartModuleLift B S hS f d).obj (nlMod₁ (chartCanonicalGenerators B S hS f d)))
    { toFun := fun m => ULift.up (Extension.h1Cotangentι (chartH1Down B S hS f d m))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The inclusion `H ⟶ I/I²` read over `Γ` is injective. -/
theorem injective_chartH1Inclusion : Function.Injective (chartH1Inclusion B S hS f d) :=
  fun _ _ h => ULift.ext (Extension.h1Cotangentι_injective (congrArg ULift.down h))

/-- The inclusion `H ⟶ I/I²` followed by the differential is zero. -/
theorem chartH1Inclusion_comp_nlModD :
    chartH1Inclusion B S hS f d ≫
      (chartModuleLift B S hS f d).map (nlModD (chartCanonicalGenerators B S hS f d)) = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun m => congrArg ULift.up (chartH1Down B S hS f d m).2)

/-- The short complex `H ⟶ I/I² ⟶ Ω ⊗ A`, read over `Γ`. -/
abbrev chartH1ShortComplex : ShortComplex (ModuleCat.{u + 1} (chartGlobalRing B S hS f d)) :=
  ShortComplex.mk (chartH1Inclusion B S hS f d)
    ((chartModuleLift B S hS f d).map (nlModD (chartCanonicalGenerators B S hS f d)))
    (chartH1Inclusion_comp_nlModD B S hS f d)

/-- **`H ⟶ I/I² ⟶ Ω ⊗ A` is exact.** -/
theorem chartH1ShortComplex_exact : (chartH1ShortComplex B S hS f d).Exact := by
  refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 fun y =>
    ⟨fun hy => ?_, by rintro ⟨x, rfl⟩; exact congrArg ULift.up (chartH1Down B S hS f d x).2⟩
  obtain ⟨x, hx⟩ := (Extension.exact_hCotangentι_cotangentComplex (ULift.down y)).1
    (congrArg ULift.down hy)
  exact ⟨ULift.up x, ULift.ext hx⟩

/-! ### `M ↦ M ⊗_Γ 𝒪` preserves kernels -/

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
  (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))

include hU in
/-- `M ↦ M ⊗_Γ 𝒪` preserves monomorphisms on the slice at an affine chart. -/
theorem chartSectionTensor_preservesMonomorphisms :
    (sectionTensorSheafFunctor.{u + 1, u, u, u}
      (chartSliceRing B S hS f d)).PreservesMonomorphisms :=
  ⟨fun φ hφ => mono_chartSectionTensor_map B S hS f d hU φ
    ((ModuleCat.mono_iff_injective φ).1 hφ)⟩

include hU in
/-- **`M ↦ M ⊗_Γ 𝒪` is exact** on the slice at an affine chart. -/
theorem chartSectionTensor_preservesHomology :
    letI := (sectionTensorSheafAdjunction.{u + 1, u, u, u}
      (chartSliceRing B S hS f d)).left_adjoint_additive
    (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)).PreservesHomology :=
  let := (sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).left_adjoint_additive
  have := chartSectionTensor_preservesMonomorphisms B S hS f d hU
  have := (sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).leftAdjoint_preservesColimits
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

include hU in
/-- `H ⊗_Γ 𝒪 ⟶ (I/I²) ⊗_A 𝒪` is a kernel of the differential `δ ⊗_A 𝒪`. -/
def chartH1TensorIsLimit :
    letI := (sectionTensorSheafAdjunction.{u + 1, u, u, u}
      (chartSliceRing B S hS f d)).left_adjoint_additive
    IsLimit ((KernelFork.ofι (chartH1ShortComplex B S hS f d).f
      (chartH1ShortComplex B S hS f d).zero).map
        (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d))) :=
  letI := (sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).left_adjoint_additive
  haveI := (chartSectionTensor_preservesHomology B S hS f d hU).preservesKernels
    (chartH1ShortComplex B S hS f d).g
  haveI : Mono (chartH1ShortComplex B S hS f d).f :=
    (ModuleCat.mono_iff_injective _).2 (injective_chartH1Inclusion B S hS f d)
  KernelFork.mapIsLimit _ (chartH1ShortComplex_exact B S hS f d).fIsKernel _

include hU in
/-- **`H ⊗_Γ 𝒪` is the kernel of `δ ⊗_A 𝒪`.** -/
def chartH1TensorKernelIso :
    (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)).obj
        (chartH1GlobalModule B S hS f d) ≅
      kernel ((chartTensorFunctor B S hS f d).map (nlModD (chartCanonicalGenerators B S hS f d))) :=
  IsLimit.conePointUniqueUpToIso (chartH1TensorIsLimit B S hS f d hU) (limit.isLimit _)

/-- The identification `H ⊗_Γ 𝒪 ≅ ker(δ ⊗_A 𝒪)`, followed by the inclusion of the kernel, is
the inclusion `H ⊗_Γ 𝒪 ⟶ (I/I²) ⊗_A 𝒪`. -/
theorem chartH1TensorKernelIso_hom_ι :
    (chartH1TensorKernelIso B S hS f d hU).hom ≫
        kernel.ι ((chartTensorFunctor B S hS f d).map
          (nlModD (chartCanonicalGenerators B S hS f d))) =
      (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)).map
        (chartH1Inclusion B S hS f d) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (chartH1TensorIsLimit B S hS f d hU) (limit.isLimit _)
    WalkingParallelPair.zero

/-! ### The degree `-1` component on `H ⊗_Γ 𝒪` -/

/-- The degree `-1` comparison on sections over `V`, on an element of `H`, is the comparison `σ`
of `Stacks.SheafOfModules.sectionsH1Comparison` applied to its image in
`H₁(L_{𝒪_X(V)/(f⁻¹𝒪_Y)(V)})`. -/
theorem chartConormalSection_h1Cotangentι (h : chartH1 B S hS f d) :
    chartConormalSection B S hS f d (Extension.h1Cotangentι h) =
      naiveCotangentSigma B S hS f d.U (chartH1Map B S hS f d (Over.mk (𝟙 d.U)) h) :=
  rfl

/-- **The degree `-1` component of the chain map on `H ⊗_Γ 𝒪`** is the identification
`H ⊗_Γ 𝒪 ≅ 𝒦|_V` followed by the inclusion of `𝒦|_V` into the restricted conormal sheaf. -/
theorem chartH1Inclusion_conormalTensorHom :
    (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)).map
        (chartH1Inclusion B S hS f d) ≫ chartConormalTensorHom B S hS f d =
      chartKernelSliceHom B S hS f d ≫
        (_root_.SheafOfModules.overFunctor _ d.U).map (kernel.ι (chartCS B S hS f).f) := by
  apply ((sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv _
    _).injective
  refine ((sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ ((sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).homEquiv_naturality_right _ _).symm
  refine (congrArg (fun t => chartH1Inclusion B S hS f d ≫ t)
    (chartSectionsTensorHom_homEquiv B S hS f d _ (chartConormalSection B S hS f d)
      (chartConormalSection_smul B S hS f d))).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => t ≫ (globalSectionsFunctor
    (chartSliceRingSheaf B S hS f d)).map ((_root_.SheafOfModules.overFunctor _ d.U).map
      (kernel.ι (chartCS B S hS f).f)))
    (chartKernelSliceHom_homEquiv B S hS f d)).symm
  refine ModuleCat.hom_ext (LinearMap.ext fun m => PresheafOfModules.sections_ext _ _ fun U => ?_)
  change (chartCS B S hS f).X₁.val.map U.unop.hom.op
      (chartConormalSection B S hS f d (Extension.h1Cotangentι (chartH1Down B S hS f d m))) =
    (kernel.ι (chartCS B S hS f).f).val.app (op U.unop.left)
      ((naiveCotangentKernel B S hS f).val.map U.unop.hom.op
        (chartKernelSection B S hS f d (chartH1Down B S hS f d m)))
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply (kernel.ι (chartCS B S hS f).f).val
    U.unop.hom.op _).symm
  exact congrArg ((chartCS B S hS f).X₁.val.map U.unop.hom.op)
    ((chartConormalSection_h1Cotangentι B S hS f d _).trans
      (naiveCotangentKernelι_chartKernelSection B S hS f d _).symm)

/-! ### The map on kernels -/

/-- Restriction to the slice at `V` carries the kernel `𝒦` of the differential of `NL_{X/Y}` to
the kernel of the restricted differential. -/
theorem isIso_chartKernelComparison :
    IsIso (kernelComparison (chartCS B S hS f).f (_root_.SheafOfModules.overFunctor _ d.U)) := by
  have : PreservesFiniteLimits (_root_.SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U :
        _root_.SheafOfModules.{u + 1} _ ⥤ _) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits _
  infer_instance

/-- The map on kernels, after `H ⊗_Γ 𝒪 ≅ ker(δ ⊗_A 𝒪)`, is `H ⊗_Γ 𝒪 ≅ 𝒦|_V` followed by the
comparison of `𝒦|_V` with the kernel of the restricted differential. -/
theorem chartH1TensorKernelIso_hom_kernelMap :
    (chartH1TensorKernelIso B S hS f d hU).hom ≫
        kernel.map ((chartTensorFunctor B S hS f d).map
          (nlModD (chartCanonicalGenerators B S hS f d)))
          ((_root_.SheafOfModules.overFunctor _ d.U).map (chartCS B S hS f).f)
          (chartConormalTensorHom B S hS f d) (chartTensorTensorHom B S hS f d)
          (chartTensorHom_comm B S hS f d) =
      chartKernelSliceHom B S hS f d ≫
        kernelComparison (chartCS B S hS f).f (_root_.SheafOfModules.overFunctor _ d.U) := by
  refine equalizer.hom_ext ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (chartH1TensorKernelIso B S hS f d hU).hom ≫ t)
    (kernel.lift_ι _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ chartConormalTensorHom B S hS f d)
    (chartH1TensorKernelIso_hom_ι B S hS f d hU)).trans ?_
  refine (chartH1Inclusion_conormalTensorHom B S hS f d).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun t => chartKernelSliceHom B S hS f d ≫ t)
    (kernelComparison_comp_ι _ _).symm

include hU hW in
/-- **The canonical chain map `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V` is an isomorphism on the kernels
of the two differentials**: the map it induces from `ker(δ ⊗_A 𝒪) = H₁(L_{A/R}) ⊗_A 𝒪` to the
kernel of the restricted differential of `NL_{X/Y}`, that is `𝒦|_V`, is an isomorphism. -/
theorem isIso_chartKernelMap :
    IsIso (kernel.map ((chartTensorFunctor B S hS f d).map
      (nlModD (chartCanonicalGenerators B S hS f d)))
      ((_root_.SheafOfModules.overFunctor _ d.U).map (chartCS B S hS f).f)
      (chartConormalTensorHom B S hS f d) (chartTensorTensorHom B S hS f d)
      (chartTensorHom_comm B S hS f d)) := by
  have h₁ := isIso_chartKernelSliceHom B S hS f d hU hW
  have h₂ := isIso_chartKernelComparison B S hS f d
  have : IsIso ((chartH1TensorKernelIso B S hS f d hU).hom ≫
      kernel.map ((chartTensorFunctor B S hS f d).map
        (nlModD (chartCanonicalGenerators B S hS f d)))
        ((_root_.SheafOfModules.overFunctor _ d.U).map (chartCS B S hS f).f)
        (chartConormalTensorHom B S hS f d) (chartTensorTensorHom B S hS f d)
        (chartTensorHom_comm B S hS f d)) := by
    rw [chartH1TensorKernelIso_hom_kernelMap B S hS f d hU]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
  exact IsIso.of_isIso_comp_left (chartH1TensorKernelIso B S hS f d hU).hom _

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSurjectiveIndexChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelViaSurjectiveChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal

/-!
# The kernel ideal sheaf of a quasi-compact morphism of algebraic spaces

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`.  The kernel of the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 is a
sheaf of ideals of `𝒪_Y` on the small étale site of `Y`
(`AlgebraicGeometry.Space.kernelIdealSheaf`); this file proves that for a quasi-compact `f` it is
quasi-coherent, and hence cuts out a closed subspace of `Y`.

## Main results

* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_kernelIdealSheaf`: for a quasi-compact
  `f` the base change comparison of the kernel ideal sheaf is bijective over every morphism of
  affine étale charts of `Y`.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernelIdealSheaf`: the kernel ideal sheaf of
  a quasi-compact morphism is cartesian on affine charts.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernelIdealSheaf`: **the kernel of
  `f♯ : 𝒪_Y ⟶ f_*𝒪_X` is a quasi-coherent sheaf of ideals for a quasi-compact `f`.**
* `AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_kernelIdealSheaf`: that sheaf of ideals
  is the defining ideal sheaf of a closed subspace of `Y`.

## References

* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **The base change comparison of the kernel ideal sheaf of a quasi-compact morphism is
bijective over a morphism of affine étale charts.** -/
theorem bijective_sectionsBaseChange_kernelIdealSheaf (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f.hom) {U V : SmallEtale B S hS Y.1} (m : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    Function.Bijective (sectionsBaseChange (kernelIdealSheaf B S hS f).toSheafOfModules m) := by
  obtain ⟨j₀, hj₀aff, hj₀⟩ := exists_isAffine_isSurjective_index B S hS f U hU hf
  obtain ⟨j₁, r, _, hj₁, hpb⟩ :=
    exists_isAffine_isSurjective_index_pullback B S hS f m hU hV j₀ hj₀aff hj₀
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y.1).obj U)) := hU
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS Y.1).obj V)) := hV
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X.1).obj j₀.right.unop)) := hj₀aff
  have hpo := isPushout_appTop_of_isPullback hpb
  refine bijective_sectionsBaseChange_kerSubmodule_of_isPushout _ m
    ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f U j₀)).appTop.hom
    ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f V j₁)).appTop.hom
    ((BigFppfOver.toScheme B S hS).map r).appTop.hom ?_ ?_ ?_
    (flat_chartRestrict_of_isAffine m hU hV) hpo
  · exact RingHom.ext fun x => ConcreteCategory.congr_hom hpo.w.symm x
  all_goals exact fun a => (Iff.of_eq (congrArg (fun I => a ∈ I)
    (ker_structureSharp_eq_of_isSurjective B S hS f _ _ (by assumption)))).trans RingHom.mem_ker

/-- **The kernel ideal sheaf of a quasi-compact morphism of algebraic spaces is cartesian on
affine charts.**  This is the base change criterion of Descent 03DX(2) for the kernel of
`f♯ : 𝒪_Y ⟶ f_*𝒪_X`. -/
theorem isCartesianOnAffineCharts_kernelIdealSheaf (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f.hom) :
    IsCartesianOnAffineCharts (kernelIdealSheaf B S hS f).toSheafOfModules :=
  fun _ _ hU hV m => bijective_sectionsBaseChange_kernelIdealSheaf B S hS f hf m hU hV

/-- **The kernel of the structure map of a quasi-compact morphism of algebraic spaces is a
quasi-coherent sheaf of ideals.** -/
@[stacks 082Z "part (1): the ideal sheaf of the image is quasi-coherent"]
theorem isQuasicoherentOnSite_kernelIdealSheaf (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f.hom) :
    (kernelIdealSheaf B S hS f).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_kernelIdealSheaf B S hS f hf)

/-- **The kernel of the structure map of a quasi-compact morphism of algebraic spaces cuts out a
closed subspace of the target.**  The kernel ideal sheaf is the defining ideal sheaf of that
closed subspace, which in Stacks 082Z is the scheme-theoretic image of `f`. -/
theorem exists_definingIdealSheaf_eq_kernelIdealSheaf (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f.hom) :
    ∃ Z : ClosedSubspaces B S hS Y.1,
      definingIdealSheaf B S hS Y Z = kernelIdealSheaf B S hS f :=
  exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts B S hS Y _
    (isCartesianOnAffineCharts_kernelIdealSheaf B S hS f hf)

end AlgebraicGeometry.Space

end

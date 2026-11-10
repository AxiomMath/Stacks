module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartComparison

/-!
# Local generators of the degree `-1` cohomology sheaf of `NL_{X/Y}`

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `d` a diagram of affine étale charts
`V = Spec A` of `X` over `W = Spec R` of `Y`.  The restriction of the degree `-1` cohomology sheaf
`𝒦` of `NL_{X/Y}` to the slice at `V` is the sheaf attached to `H = H₁(L_{A/R})`
(`AlgebraicGeometry.Space.chartKernelSliceIso`), through the comparison
`s ⊗ h ↦ s · (image of h in 𝒦(V))|_U`, which is locally surjective.  Hence the images in `𝒦(V)`
of any family spanning `H` over `A` generate `𝒦` locally over `V`: every section of `𝒦` over a
chart `U ⟶ V` is, on a covering of `U`, a combination of their restrictions.

## Main results

* `AlgebraicGeometry.Space.chartKernelSection_mem_span`: the image in `𝒦` of an element of `H`
  lies in the span of the images of a spanning family.
* `AlgebraicGeometry.Space.naiveCotangentKernel_exists_sum_eq`: the local generation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)


/-- The image of `0` in `𝒦(V)` is `0`. -/
theorem chartKernelSection_zero : chartKernelSection B S hS f d 0 = 0 := by
  have h := chartKernelSection_add B S hS f d 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

/-- The restriction to a chart `q : D ⟶ V` of the image in `𝒦(V)` of an element of `H`, as a
section of `𝒦` over `D`. -/
abbrev chartKernelSectionRestrict {D : SmallEtale B S hS X.1} (q : D ⟶ d.U)
    (x : chartH1 B S hS f d) : (naiveCotangentKernel B S hS f).val.obj (op D) :=
  ((naiveCotangentKernel B S hS f).val.map q.op).hom (chartKernelSection B S hS f d x)

/-- **The image of an element of `H` lies in the span of the images of a spanning family**, after
restriction to any chart over `V`. -/
theorem chartKernelSection_mem_span {n : ℕ} (h : Fin n → chartH1 B S hS f d)
    (hspan : letI := chartDiagramAlgebraInst B S hS f d
      Submodule.span (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
        (Set.range h) = ⊤)
    {D : SmallEtale B S hS X.1} (q : D ⟶ d.U) (x : chartH1 B S hS f d) :
    chartKernelSectionRestrict B S hS f d q x ∈
      Submodule.span ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O).obj.obj (op D))
        (Set.range fun i => chartKernelSectionRestrict B S hS f d q (h i)) := by
  let := chartDiagramAlgebraInst B S hS f d
  have hx : x ∈ Submodule.span (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
      (Set.range h) := by
    rw [hspan]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    have e : chartKernelSectionRestrict B S hS f d q 0 = 0 := by
      simp only [chartKernelSectionRestrict, chartKernelSection_zero, map_zero]
      rfl
    rw [e]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have e : chartKernelSectionRestrict B S hS f d q (y + z) =
        chartKernelSectionRestrict B S hS f d q y + chartKernelSectionRestrict B S hS f d q z := by
      simp only [chartKernelSectionRestrict, chartKernelSection_add, map_add]
      rfl
    rw [e]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    have e : chartKernelSectionRestrict B S hS f d q (a • y) =
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.map q.op
          (a : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj
            (op d.U))) • chartKernelSectionRestrict B S hS f d q y := by
      simp only [chartKernelSectionRestrict]
      rw [chartKernelSection_smul]
      exact (naiveCotangentKernel B S hS f).val.map_smul q.op _ _
    rw [e]
    exact Submodule.smul_mem _ _ hy

/-- The comparison `(U ↦ 𝒪_X(U) ⊗_Γ H) ⟶ 𝒦|_V` over a chart `W` above `V`, as an additive map
into the sections of `𝒦` over `W`. -/
def chartKernelPresheafHomApp (W : Over d.U) :
    chartGlobalTensor B S hS f d W →+
      ToType ((naiveCotangentKernel B S hS f).val.obj (op W.left)) :=
  ((chartKernelPresheafHom B S hS f d).app (op W)).hom.toAddMonoidHom

/-- **The comparison lands in the span of the images of a spanning family**: over every chart
`W` above `V`, the image of an element of `𝒪_X(W) ⊗_Γ H` in `𝒦(W)` is a combination of the
restrictions of the images of the family. -/
theorem chartKernelPresheafHom_mem_span {n : ℕ} (h : Fin n → chartH1 B S hS f d)
    (hspan : letI := chartDiagramAlgebraInst B S hS f d
      Submodule.span (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
        (Set.range h) = ⊤)
    (W : Over d.U) (t : chartGlobalTensor B S hS f d W) :
    chartKernelPresheafHomApp B S hS f d W t ∈
      Submodule.span ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O).obj.obj (op W.left))
        (Set.range fun i => chartKernelSectionRestrict B S hS f d W.hom (h i)) := by
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
    have e1 : chartKernelPresheafHomApp B S hS f d W (a ⊗ₜ m) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O).obj.obj (op W.left) from a) •
          chartKernelSectionRestrict B S hS f d W.hom (chartH1Down B S hS f d m) :=
      (sectionTensorPresheafHomOfSections_app_tmul.{u + 1, u, u, u} (chartKernelTheta B S hS f d)
        (op W) a m).trans
        (congrArg (fun z => ringSheafSection (O := chartSliceRing B S hS f d) a • z)
          (chartKernelTheta_apply_val B S hS f d m W))
    rw [e1]
    exact Submodule.smul_mem _ _
      (chartKernelSection_mem_span B S hS f d h hspan W.hom (chartH1Down B S hS f d m))
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

/-- **The images of a spanning family of `H` generate `𝒦` locally over `V`.**  Every section of
`𝒦` over a chart `p : U ⟶ V` is, on a covering sieve of `U`, a combination of the restrictions of
the images of the family. -/
theorem naiveCotangentKernel_exists_sum_eq
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    {n : ℕ} (h : Fin n → chartH1 B S hS f d)
    (hspan : letI := chartDiagramAlgebraInst B S hS f d
      Submodule.span (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
        (Set.range h) = ⊤)
    (U : SmallEtale B S hS X.1) (p : U ⟶ d.U)
    (y : (naiveCotangentKernel B S hS f).val.obj (op U)) :
    ∃ T : Sieve U, T ∈ SmallEtale.topology B S hS X.1 U ∧ ∀ ⦃D : SmallEtale B S hS X.1⦄
      (k : D ⟶ U), T.arrows k → ∃ c : Fin n → (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O).obj.obj (op D),
        ∑ i, c i • chartKernelSectionRestrict B S hS f d (k ≫ p) (h i) =
          (show ToType ((naiveCotangentKernel B S hS f).val.obj (op D)) from
            ((naiveCotangentKernel B S hS f).val.map k.op).hom y) := by
  have hmem := chartKernelPresheafHom_imageSieve_mem B S hS f d hU hW (Over.mk p) y
  refine ⟨Sieve.overEquiv (Over.mk p) _, (GrothendieckTopology.mem_over_iff _ _).mp hmem, ?_⟩
  intro D k hk
  obtain ⟨t, ht⟩ := (Sieve.overEquiv_iff _ (show D ⟶ (Over.mk p).left from k)).mp hk
  refine (Submodule.mem_span_range_iff_exists_fun _).mp ?_
  have key := chartKernelPresheafHom_mem_span B S hS f d h hspan (Over.mk (k ≫ p)) t
  have ht' : chartKernelPresheafHomApp B S hS f d (Over.mk (k ≫ p)) t =
      ((naiveCotangentKernel B S hS f).val.map k.op).hom y := ht
  rw [ht'] at key
  exact key

end AlgebraicGeometry.Space

end

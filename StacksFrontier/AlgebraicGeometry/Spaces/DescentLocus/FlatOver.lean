module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingFlatnessChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat

/-!
# A finite locally free module is flat over the base of a flat morphism

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces and `E` a finite locally free
`𝒪_X`-module. Then `E` is flat over `Y` (Stacks 05VV): its geometric stalks are free over the
étale local rings of `X`, which are flat over those of `Y`.

The case of a single rank is `AlgebraicGeometry.Space.isFlatOver_id_of_isFiniteLocallyFreeOfRank`;
here the rank may vary, the sections over small enough affine charts being free of some rank.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.isFlatOver_of_isFiniteLocallyFree`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.DescentStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The affine charts over which the sections of a finite locally free module are flat cover
every étale chart.** -/
theorem flatPresieve_mem_topology {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (H : Modules.{u, u} B S hS F hF)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite H) (U : SmallEtale B S hS F) :
    Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) ∧
        Module.Flat (chartRing B S hS F hF V) (H.val.obj (op V))) ∈
      SmallEtale.topology B S hS F U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z => ?_
  obtain ⟨I, A, a, hcov, hfree⟩ := h U
  have hcov' : Sieve.ofArrows A a ∈ SmallEtale.topology B S hS F U := hcov
  obtain ⟨V₁, g₁, hg₁, z₁, hz₁⟩ := exists_mem_sieve_scheme_point B S hS F U hcov' z
  obtain ⟨Z, t, ff, ⟨i⟩, hfac⟩ := hg₁
  obtain ⟨T₀, j, hT₀aff, w₀, hw₀⟩ := exists_affine_chart_at B S hS F V₁ z₁
  obtain ⟨n, κ, ⟨hcofan⟩⟩ := (SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 (hfree i)
  refine ⟨T₀, j ≫ g₁, ⟨T₀, 𝟙 _, j ≫ g₁, ⟨hT₀aff, ?_⟩, Category.id_comp _⟩, w₀, ?_⟩
  · exact Module.flat_of_isFiniteLocallyFreeOfRank (Module.isFiniteLocallyFreeOfRank_of_basis
      (RingedSite.nonempty_basis_sections_of_isColimitCofanUnit
        (smallEtaleRingedSite B S hS F hF) H n (A i) κ hcofan (j ≫ t)).some)
  · rw [Functor.map_comp, Functor.map_comp]
    exact (congrArg _ hw₀).trans hz₁

/-- **A finite locally free module has a flat chart stalk at every geometric point.** -/
theorem exists_flat_chartZariskiModuleStalk_of_isFiniteLocallyFreeOnSite
    {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F)
    (x : GeometricPoint B S hS X.1) :
    ∃ N : SmallEtaleNeighborhood x,
      Module.Flat ↥(chartLocalRing B S hS X.1 N)
        ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) := by
  obtain ⟨N₀⟩ := (isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x).nonempty
  obtain ⟨V, f, hf, q, -⟩ := (etaleSitePoint B S hS X.1 x X.2).jointly_surjective
    (Sieve.generate (fun (W : SmallEtale B S hS X.1) (_ : W ⟶ N₀.chart) =>
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
        Module.Flat (chartRing B S hS X.1 X.2 W) (F.val.obj (op W))))
    (flatPresieve_mem_topology X.2 F hF N₀.chart)
    (show GeometricFiber B S hS X.1 x N₀.chart from ⟨N₀.point, N₀.point_comp⟩)
  obtain ⟨Z, g, -, ⟨haff, hflat⟩, -⟩ := hf
  refine ⟨⟨Z, ((geometricFiber B S hS X.1 x).map g q).1,
    ((geometricFiber B S hS X.1 x).map g q).2⟩, ?_⟩
  exact flat_chartZariskiModuleStalk_of_flat_sections B S hS X F hqc _ haff hflat

/-- **A finite locally free module is flat over the base of a flat morphism.** -/
theorem isFlatOver_of_isFiniteLocallyFree {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) (E : Modules.{u, u} B S hS X.1 X.2)
    (hE : SheafOfModules.IsFiniteLocallyFree E) :
    IsFlatOver B S hS X.2 f.hom E := by
  have := isQuasicoherentOnSite_of_isFiniteLocallyFree E hE
  have h₁ : IsFlatOver B S hS X.2 (𝟙 X : X ⟶ X).hom E :=
    isFlatOver_id_of_forall_exists_flat_chartZariskiModuleStalk B S hS E
      (exists_flat_chartZariskiModuleStalk_of_isFiniteLocallyFreeOnSite E inferInstance
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree E hE))
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint] at h₁ ⊢
  intro x
  have h₂ := isFlatOverAtGeometricPoint_comp B S hS (𝟙 X) f E x (h₁ x)
    ((isFlat_iff_forall_isFlatAt B S hS f.hom).1 hf _)
  rwa [Category.id_comp] at h₂

end AlgebraicGeometry.Space.DescentStratum

end

module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Flat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.Neighbourhood
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# The infinitesimal neighbourhoods of the reduction on Noetherian charts

Let `W` be a locally Noetherian formal algebraic space with reduction `i : W_red ⟶ W`. It has a
jointly surjective family of affine formal charts `f_j : Spf A_j ⟶ W`, representable by algebraic
spaces and étale, with `A_j` Noetherian and adic
(`AlgebraicGeometry.FormalSpace.exists_presentedEtaleCharts`). Over such a chart the `k`-th
infinitesimal neighbourhood `W_k` of `W_red` pulls back to the stage `Spec(A_j/𝔞_j^(k+1))`, and
`W_k` is the sheafified union of the images of these stages.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_presentedEtaleCharts`: Noetherian adic affine charts
  of a locally Noetherian formal algebraic space.
* `AlgebraicGeometry.FormalSpace.PresentedEtaleChart.mem_range_powStage_iff_mem`: a section of
  a chart lies in the stage `Spec(A/𝔞^(k+1))` iff its image lies in `W_k`.
* `AlgebraicGeometry.FormalSpace.reductionNeighbourhood_eq_sheafify`: `W_k` is the sheafified
  union of the images of the stages of a covering family of charts.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Precomposing a jointly locally surjective family with isomorphisms keeps it jointly locally
surjective. -/
theorem isLocallySurjective_sigmaDesc_iso_comp {X : FppfSheaf B S hS} {I : Type (u + 1)}
    {U V : I → FppfSheaf B S hS} (e : ∀ i, U i ≅ V i) (f : ∀ i, V i ⟶ X)
    (hf : Sheaf.IsLocallySurjective (Sigma.desc f)) :
    Sheaf.IsLocallySurjective (Sigma.desc fun i => (e i).hom ≫ f i) := by
  refine (Sheaf.isLocallySurjective_sigmaDesc_iff _).2 fun T s => ?_
  obtain ⟨R, hR, h⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff f).1 hf s
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨i, t, ht⟩ := h g hg
  refine ⟨i, (e i).inv.hom.app _ t, ?_⟩
  rw [← ht]
  change ((e i).inv ≫ (e i).hom ≫ f i).hom.app _ t = _
  rw [Iso.inv_hom_id_assoc]

/-- A locally Noetherian formal algebraic space has a jointly locally surjective family of affine
formal charts which are representable by algebraic spaces and étale and whose sources are formal
spectra of Noetherian adic topological rings. -/
theorem exists_presentedEtaleCharts {W : FppfSheaf B S hS} (hW : IsLocallyNoetherian B S hS W) :
    ∃ (I : Type (u + 1)) (c : I → PresentedEtaleChart B S hS W),
      Sheaf.IsLocallySurjective (Sigma.desc fun j => (c j).chart) := by
  classical
  obtain ⟨-, I, Xi, f, hXi, hf, hcover, hN⟩ := hW
  choose A i₁ i₂ i₃ i₄ hP hNoeth hadic using fun j => (hN j).2
  choose hwa P using hP
  let P' := fun j => (P j).some
  let c : I → PresentedEtaleChart B S hS W := fun j =>
    let := i₁ j; let := i₂ j; let := i₃ j; let := i₄ j; let := hNoeth j
    { ring := A j
      isAdic := hadic j
      weaklyAdmissible := hwa j
      system := (P' j).quotientSystem
      affine := isAffineFormalAlgebraicSpace_of_iso B S hS (P' j).formalSpectrumIso (hXi j)
      chart := (P' j).formalSpectrumIso.inv ≫ f j
      representable := ((isRepresentableEtale_of_isIso B S hS _).comp B S hS (hf j)).1
      etale := ((isRepresentableEtale_of_isIso B S hS _).comp B S hS (hf j)).2 }
  exact ⟨I, c, isLocallySurjective_sigmaDesc_iso_comp (fun j => (P' j).formalSpectrumIso.symm)
    f hcover⟩

namespace PresentedEtaleChart

variable {W : FppfSheaf B S hS} (c : PresentedEtaleChart B S hS W)

/-- The powers `𝔞^(k+1)` of the ideal of topologically nilpotent elements of a Noetherian adic
ring are open. -/
theorem isOpen_pow (k : ℕ) :
    IsOpen ((topologicalNilradical c.ring ^ (k + 1) : Ideal c.ring) : Set c.ring) := by
  obtain ⟨⟨I, -, hI⟩, -⟩ := c.isAdic
  exact (isAdic_iff.mp (isAdic_topologicalNilradical hI)).1 (k + 1)

/-- The stage `Spec(A/𝔞^(k+1))` of a chart, as a weak ideal of definition. -/
abbrev powStage (k : ℕ) : { I : Ideal c.ring // IsWeakIdealOfDefinition I } :=
  powNilWeakIdeal c.isOpen_pow k

variable {Wred : FppfSheaf B S hS} {i : Wred ⟶ W}

/-- A section `y` of a chart lies in the image of the stage `Spec(A/𝔞^(k+1))` if and only if its
image under the chart lies in the `k`-th infinitesimal neighbourhood `W_k` of the reduction. -/
theorem mem_range_powStage_iff_mem (hred : IsReduction B S hS W Wred i) (k : ℕ)
    {T : BigFppfOver B S hS} (y : (formalSpectrum c.system).obj.obj (op T)) :
    y ∈ (Subfunctor.range (stageIncl c.system (c.powStage k)).hom).obj (op T) ↔
      c.chart.hom.app (op T) y ∈ (reductionNeighbourhood i k).obj (op T) := by
  constructor
  · intro hy V h hV K hK
    rw [← NatTrans.naturality_apply] at hK
    exact (mem_range_powStage_iff c.weaklyAdmissible c.isOpen_pow c.system hred c.chart
      c.representable c.etale k _ hK).1 (Subfunctor.map _ h.op hy)
  · intro hy
    let Rg := Subfunctor.range (stageIncl c.system (c.powStage k)).hom
    refine (Rg.isSheaf_iff ((isSheaf_iff_isSheaf_of_type _ _).1
      (formalSpectrum c.system).property)).1
      (isSheaf_range_stageIncl c.weaklyAdmissible c.system _) (op T) y
      (mem_topology_of_affine ((BigFppfOver.topology B S hS).top_mem T) fun V g hV _ => ?_)
    obtain ⟨K, hK⟩ := hred.exists_isReductionIdeal (c.chart.hom.app (op V)
      ((formalSpectrum c.system).obj.map g.op y))
    refine (mem_range_powStage_iff c.weaklyAdmissible c.isOpen_pow c.system hred c.chart
      c.representable c.etale k _ hK).2 ?_
    refine (mem_reductionNeighbourhood_iff k hK).1 ?_
    rw [NatTrans.naturality_apply]
    exact Subfunctor.map _ g.op hy

end PresentedEtaleChart

variable {W Wred : FppfSheaf B S hS} {i : Wred ⟶ W}

/-- The `k`-th infinitesimal neighbourhood `W_k` of the reduction is the sheafified union of the
images of the `k`-th stages of a jointly locally surjective family of Noetherian charts. -/
theorem reductionNeighbourhood_eq_sheafify (hred : IsReduction B S hS W Wred i)
    {I : Type (u + 1)} (c : I → PresentedEtaleChart B S hS W)
    (hcover : Sheaf.IsLocallySurjective (Sigma.desc fun j => (c j).chart)) (k : ℕ) :
    reductionNeighbourhood i k = (⨆ j, Subfunctor.range
      (stageIncl (c j).system ((c j).powStage k) ≫ (c j).chart).hom).sheafify
        (BigFppfOver.topology B S hS) := by
  refine le_antisymm (fun T t ht => ?_) (Subfunctor.sheafify_le _ _ (iSup_le fun j => ?_)
    ((isSheaf_iff_isSheaf_of_type _ _).1 W.property) (isSheaf_reductionNeighbourhood k))
  · obtain ⟨R, hR, h⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff _).1 hcover t
    refine mem_topology_of_affine hR fun V g hV hg => ?_
    obtain ⟨j, y, hy⟩ := h g hg
    obtain ⟨z, rfl⟩ := ((c j).mem_range_powStage_iff_mem hred k y).2
      (hy ▸ (reductionNeighbourhood i k).map g.op ht)
    exact (le_iSup (fun j => Subfunctor.range
      (stageIncl (c j).system ((c j).powStage k) ≫ (c j).chart).hom) j) _ ⟨z, hy⟩
  · rintro T _ ⟨z, rfl⟩
    exact ((c j).mem_range_powStage_iff_mem hred k _).1 ⟨z, rfl⟩

end AlgebraicGeometry.FormalSpace

end

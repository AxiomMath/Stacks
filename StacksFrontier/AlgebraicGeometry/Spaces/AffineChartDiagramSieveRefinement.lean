module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSurjectiveIndexChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# Refining a chart diagram along a covering sieve of its chart of the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let `d` be a commuting square of étale scheme charts over `f` — a chart `d.U` of `X` above a
chart `d.V` of `Y` — with both charts affine, and let `T` be a covering sieve of `d.V`. Then the
chart `d.U` is covered by finitely many affine charts of `X`, each of which is the chart of `X`
of a commuting square over `f` whose chart of `Y` is affine and lies in `T`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_chartDiagram_cover_of_sieve`: a covering sieve of the
  chart of `Y` of an affine chart diagram is pulled back to a finite affine covering family of
  its chart of `X`, each member carrying a chart diagram over a member of the sieve.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Let `d` be a commuting square of étale scheme charts over `f : X ⟶ Y` whose two charts are
affine, and let `T` be a covering sieve of its chart `d.V` of `Y`. Then `d.U` carries a finite
covering family of affine charts of `X`, each of which is the chart of `X` of a commuting square
over `f` whose chart of `Y` is affine and is the source of a member of `T`, and which maps to `d`
as a square. -/
theorem exists_affine_chartDiagram_cover_of_sieve (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj d.U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V)))
    {T : Sieve d.V} (hT : T ∈ SmallEtale.topology B S hS Y.1 d.V) :
    ∃ (n : ℕ) (d' : Fin n → ChartDiagram B S hS X.1 Y.1 f.hom)
      (a : ∀ i, (d' i).U ⟶ d.U) (k : ∀ i, (d' i).V ⟶ d.V),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj (d' i).U))) ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS Y.1).obj (d' i).V))) ∧
      (∀ i, T (k i)) ∧
      (∀ i, (SmallEtale.toOver B S hS X.1).map (a i) ≫ d.g =
        (d' i).g ≫ (SmallEtale.toOver B S hS Y.1).map (k i)) ∧
      Sieve.ofArrows (fun i ↦ (d' i).U) a ∈ SmallEtale.topology B S hS X.1 d.U := by
  classical
  obtain ⟨n, z, φ, hzaff, hzT, -, hzpre⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS Y.1 hV hT
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hgj : chartBaseChangeMap B S hS f d.V (indexOfChartDiagram B S hS f d) = d.g :=
    chartBaseChangeMap_indexOfChartDiagram B S hS f d
  have hUj : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj (indexOfChartDiagram B S hS f d).right.unop)) := hU
  refine ⟨n, fun i ↦ pullbackChartDiagram B S hS f (indexOfChartDiagram B S hS f d) (φ i),
    fun i ↦ pullbackIndexChartHom B S hS f (indexOfChartDiagram B S hS f d) (φ i), φ,
    fun i ↦ ?_, hzaff, hzT, fun i ↦ ?_, ?_⟩
  · have hVi : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj (z i))) := hzaff i
    have hVd : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V)) := hV
    exact IsAffine.of_isPullback
      (isPullback_pullbackIndexChart B S hS f (indexOfChartDiagram B S hS f d) (φ i))
  · have hfst : (SmallEtale.toOver B S hS X.1).map (pullbackIndexChartHom B S hS f
          (indexOfChartDiagram B S hS f d) (φ i)) =
        pullback.fst (chartBaseChangeMap B S hS f d.V (indexOfChartDiagram B S hS f d))
          ((SmallEtale.toOver B S hS Y.1).map (φ i)) := rfl
    show (SmallEtale.toOver B S hS X.1).map (pullbackIndexChartHom B S hS f
        (indexOfChartDiagram B S hS f d) (φ i)) ≫ d.g =
      (pullbackChartDiagram B S hS f (indexOfChartDiagram B S hS f d) (φ i)).g ≫
        (SmallEtale.toOver B S hS Y.1).map (φ i)
    rw [hfst, ← hgj]
    exact pullback.condition
  · refine SmallEtale.ofArrows_mem_topology B S hS X.1 _ _ ?_
    rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ etale_toScheme_toOver_map B S hS X.1 _⟩
    obtain ⟨i, v, hv⟩ := (Scheme.ofArrows_mem_etalePrecoverage_iff.mp hzpre).1
      (((BigFppfOver.toScheme B S hS).map d.g).base x)
    obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_pullbackIndexChart B S hS f (indexOfChartDiagram B S hS f d) (φ i)) v x
      (by rwa [hgj])
    exact ⟨i, p, hp⟩

end AlgebraicGeometry.Space

end

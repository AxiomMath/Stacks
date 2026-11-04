module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramSieveRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseRankCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange

/-!
# The rank of a module is preserved by an arbitrary pullback

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B` and let `G` be a quasi-coherent `𝒪_Y`-module on the small étale site which is finite locally
free of rank `r` in the sense of the rank clause of Stacks 0409. Then the pullback `f^*G` of
Stacks 03LU is finite locally free of rank `r` on the small étale site of `X`.

This is the rank-indexed form of Stacks 03DO, the rankless case of which is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_sections_modulePullback_chartDiagram`: over a
  diagram of affine étale charts over `f`, the sections of `f^*G` are finite locally free of the
  same rank as the sections of `G`.
* `AlgebraicGeometry.Space.freeRankPresieve_modulePullback_mem_topology`: the affine étale charts
  of `X` over which the sections of `f^*G` are finite locally free of rank `r` generate a
  covering sieve of every chart.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_of_isQuasicoherentOnSite`:
  the pullback of a quasi-coherent module finite locally free of rank `r` is finite locally free
  of rank `r`.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The rank of the sections over an affine chart diagram -/

/-- Let `d : U ⟶ V` be a diagram of affine étale charts over `f : X ⟶ Y`, and let `G` be an
`𝒪_Y`-module cartesian on affine chart diagrams over `f`. If the sections of `G` over `V` are
finite locally free of rank `r`, then so are the sections of `f^*G` over `U`. -/
theorem isFiniteLocallyFreeOfRank_sections_modulePullback_chartDiagram (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hcd : IsCartesianOnAffineChartDiagrams B S hS f G)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (r : ℕ)
    (hr : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS Y.1 Y.2 d.V)
      (G.val.obj (op d.V)) r) :
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 d.U)
      (((modulePullback B S hS f).obj G).val.obj (op d.U)) r :=
  let := chartDiagramAlgebra B S hS f d
  have := Module.IsFiniteLocallyFreeOfRank.finite hr
  Module.IsFiniteLocallyFreeOfRank.of_linearEquiv (hcd d haU haV).some
    (Module.IsFiniteLocallyFreeOfRank.baseChange _ hr)

/-! ### The charts of `X` trivialising the pullback are cover-dense -/

/-- Let `G` be an `𝒪_Y`-module which is cartesian on affine charts and on affine chart diagrams
over `f : X ⟶ Y`, and finite locally free of rank `r`. The affine étale charts of `X` over which
the sections of `f^*G` are finite locally free of rank `r` generate a covering sieve of every
object of the small étale site of `X`. -/
theorem freeRankPresieve_modulePullback_mem_topology (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hGcart : IsCartesianOnAffineCharts G)
    (hcd : IsCartesianOnAffineChartDiagrams B S hS f G) (r : ℕ)
    (hG : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) G r)
    (U₀ : SmallEtale B S hS X.1) :
    Sieve.generate (fun (V : SmallEtale B S hS X.1) (_ : V ⟶ U₀) =>
      IsAffine (chartScheme V) ∧
        Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 V)
          (((modulePullback B S hS f).obj G).val.obj (op V)) r) ∈
      SmallEtale.topology B S hS X.1 U₀ := by
  classical
  have hbasis : ∀ V : SmallEtale B S hS Y.1,
      Sieve.generate (basisPresieve B S hS Y.1 Y.2 G r V) ∈
        SmallEtale.topology B S hS Y.1 V :=
    basisPresieve_mem_topology_of_freeRankPresieve B S hS Y.1 Y.2 G hGcart r
      (freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS Y.1 Y.2 G r hG)
  refine GrothendieckTopology.transitive _
    (generate_affineChartDiagram_mem_topology B S hS f (fun _ => True) (fun _ _ => trivial) U₀)
    _ ?_
  rintro Z c ⟨T, l, a, ⟨hTaff, d, hdU, hdVaff, -⟩, rfl⟩
  subst hdU
  rw [Sieve.pullback_comp]
  refine GrothendieckTopology.pullback_stable _ l ?_
  obtain ⟨n, d', aa, kk, haffU, haffV, hkT, -, hcov⟩ :=
    exists_affine_chartDiagram_cover_of_sieve B S hS f d hTaff hdVaff (hbasis d.V)
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  rintro T' m ⟨W', p, q, ⟨i⟩, rfl⟩
  refine ⟨(d' i).U, p, aa i ≫ a, ⟨haffU i, ?_⟩, (Category.assoc p (aa i) a).symm⟩
  obtain ⟨V'', m'', v'', ⟨hV''aff, hV''basis⟩, -⟩ := hkT i
  exact isFiniteLocallyFreeOfRank_sections_modulePullback_chartDiagram B S hS f G hcd (d' i)
    (haffU i) (haffV i) r
    (Module.isFiniteLocallyFreeOfRank_of_basis
      (chartRestrictBasis B S hS _ _ G hGcart hV''aff (haffV i) m'' hV''basis.some))

/-! ### Stacks 03DO with the rank -/

/-- For a morphism `f : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_Y`-module `G` which
is finite locally free of rank `r` in the sense of the rank clause of Stacks 0409, the pullback
`f^*G` of Stacks 03LU is finite locally free of rank `r` on the small étale site of `X`. -/
theorem isFiniteLocallyFreeOfRank_modulePullback_of_isQuasicoherentOnSite (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hGqc : G.IsQuasicoherentOnSite) (r : ℕ)
    (hG : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) G r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      ((modulePullback B S hS f).obj G) r :=
  isFiniteLocallyFreeOfRank_of_freeRankPresieve B S hS X.1 X.2
    ((modulePullback B S hS f).obj G)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2
      ((modulePullback B S hS f).obj G)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hGqc)) r
    (freeRankPresieve_modulePullback_mem_topology B S hS f G
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 G hGqc)
      (isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite B S hS f G hGqc) r hG)

end AlgebraicGeometry.Space

end

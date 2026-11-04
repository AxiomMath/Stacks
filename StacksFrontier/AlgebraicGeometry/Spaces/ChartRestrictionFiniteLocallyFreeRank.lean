module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ArbitraryRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsRankUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport

/-!
# The restriction of a module of rank `r` to an étale chart has rank `r`

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module which is
finite locally free of rank `r` in the sense of the rank clause of Stacks 0409.  Then for every
étale scheme chart `V` of `X` the restriction `ℰ|_V` is a finite locally free `𝒪_V`-module of
rank `r` in the Zariski sense.

The restriction is finite locally free
(`AlgebraicGeometry.Space.isFiniteLocallyFree_restrictToChartScheme`), so it suffices to compute
its rank at each point `v` of `V`.  The affine étale charts over which the sections of `ℰ` are
finite locally free of rank `r` cover `V`
(`AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`), so `v` is
the image of a point of such an affine chart `T`.  Over `T` the restriction `ℰ|_T` has global
sections `ℰ(T)`, so it has rank `r` on the affine scheme `T`
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_isAffine`), and it is the
pullback of `ℰ|_V` along `T ⟶ V`; a pullback of rank `r` forces the rank `r` at the image point
(`Stacks.Chow.SectionZeroScheme.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback`).

## Main results

* `Module.IsFiniteLocallyFreeOfRank.of_addEquiv_symm`: the rank transports along an additive
  equivalence compatible with the scalar actions.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_restrictToChartScheme`: **the chart
  restriction of a module of rank `r` has rank `r`.**
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

/-- A finite locally free module of rank `d` transports along an additive equivalence which is
compatible with the scalar actions. -/
theorem Module.IsFiniteLocallyFreeOfRank.of_addEquiv_symm {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃+ N)
    (he : ∀ (c : R) (x : M), e (c • x) = c • e x) {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R N d) : Module.IsFiniteLocallyFreeOfRank R M d :=
  h.of_linearEquiv (e.toLinearEquiv he).symm

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction of a quasi-coherent module of rank `r` to the scheme of an étale chart is
finite locally free of rank `r`.** -/
theorem isFiniteLocallyFreeOfRank_restrictToChartScheme (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (r : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) M r)
    (V : SmallEtale B S hS X.1) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (restrictToChartSchemeModules B S hS X.1 X.2 M V) r := by
  have hcart : IsCartesianOnAffineCharts M :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM
  have hfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (restrictToChartSchemeModules B S hS X.1 X.2 M V) :=
    isFiniteLocallyFree_restrictToChartScheme B S hS X M hM hr.isFiniteLocallyFreeOnSite V
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq _ r fun v => ?_
  rw [Stacks.Chow.fiberRank_eq_moduleRank]
  obtain ⟨V₁, g₁, hg₁, z₁, hz₁⟩ := exists_mem_sieve_scheme_point B S hS X.1 V
    (freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS X.1 X.2 M r hr V) v
  obtain ⟨W, t, ff, ⟨hWaff, hWr⟩, -⟩ := hg₁
  obtain ⟨T₀, j, hT₀aff, w₀, hw₀⟩ := exists_affine_chart_at B S hS X.1 V₁ z₁
  have hT : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 T₀)
      (M.val.obj (op T₀)) r :=
    isFiniteLocallyFreeOfRank_sections_of_hom B S hS X.1 X.2 M hcart (j ≫ t) hWaff hT₀aff hWr
  have : IsAffine (chartScheme T₀) := hT₀aff
  have := isQuasicoherent_restrictToChartScheme B S hS X M hM T₀
  have hT₂ : Module.IsFiniteLocallyFreeOfRank Γ(chartScheme T₀, ⊤) (M.val.obj (op T₀)) r := hT
  have hT' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (restrictToChartSchemeModules B S hS X.1 X.2 M T₀) r :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_isAffine _
      (Module.IsFiniteLocallyFreeOfRank.of_addEquiv_symm
        (restrictToChartSchemeTopSectionsAddEquiv B S hS X M T₀)
        (restrictToChartSchemeTopSectionsAddEquiv_smul B S hS X M T₀) hT₂)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (chartSchemeMap (j ≫ g₁))).obj
        (restrictToChartSchemeModules B S hS X.1 X.2 M V)) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (asIso (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M (j ≫ g₁))).symm hT'
  have hmem := Stacks.Chow.SectionZeroScheme.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback
    (restrictToChartSchemeModules B S hS X.1 X.2 M V) (chartSchemeMap (j ≫ g₁)) r w₀
  have hpt : (chartSchemeMap (j ≫ g₁)) w₀ = v := by
    show (chartSchemeMap g₁) ((chartSchemeMap j) w₀) = v
    rw [show (chartSchemeMap j) w₀ = z₁ from hw₀]
    exact hz₁
  rw [hpt] at hmem
  exact hmem

end AlgebraicGeometry.Space

end

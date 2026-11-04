module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneModule.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingFlatnessFunctorStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint

/-!
# A module finite locally free of rank `r` on the small étale site is flat over its space

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `F` be a
quasi-coherent `𝒪_X`-module which is finite locally free of rank `r` in the sense of the rank
clause of Stacks 0409.  This file proves that `F` is then flat over `X` itself, that is, that
`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV holds along the identity of `X`.

This is the implication the *backward* half of the flatness clause of Stacks 0CZA needs: the
pullback of `G` to a Fitting rank stratum `X_r` is finite locally free of rank `r`
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback_fittingRankStratumHom`), so a
test object factoring through a stratum has `G_T` flat over `T`.

The geometric stalk of a module finite locally free of rank `r` is **not** shown to be free
here, and need not be reached: by Stacks 05VP the geometric stalk is a base change of the
Zariski stalk of a chart restriction, flatness ascends along a base change, and the geometric
point has *some* chart over which the sections are free.  That is the content of
`AlgebraicGeometry.Space.flat_geometricModuleStalk_of_flat_chartZariskiModuleStalk`, which this
file feeds.

## Main results

* `Stacks.ModuleStalkSpecialization.flat_stalk_of_flat_sections`: **the stalk of a
  quasi-coherent module on a scheme is flat over the local ring as soon as its sections over an
  affine open containing the point are flat over the functions on that open.**  The stalk is a
  localization of the sections, by the module analogue of
  `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`.
* `AlgebraicGeometry.Space.flat_chartZariskiModuleStalk_of_flat_sections`: **the Zariski stalk
  of the restriction of a quasi-coherent `𝒪_X`-module to an affine étale scheme chart is flat
  over the local ring of the chart as soon as the sections of the module over that chart are
  flat over the chart ring.**
* `AlgebraicGeometry.Space.exists_flat_chartZariskiModuleStalk_of_isFiniteLocallyFreeOfRank`:
  every geometric point of `X` has a small étale neighbourhood whose chart is affine and on
  which that Zariski stalk is flat, for a module finite locally free of rank `r`.
* `AlgebraicGeometry.Space.isFlatOver_id_of_isFiniteLocallyFreeOfRank`: **a quasi-coherent
  `𝒪_X`-module finite locally free of rank `r` is flat over `X`**, in the sense of
  Stacks 05VV read along the identity.

## Implementation notes

The neighbourhood of a geometric point is produced from a covering sieve, not chosen.  The
affine charts over which the sections are finite locally free of rank `r` generate a covering
sieve of every chart
(`AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`), and a
geometric point lifts through every covering sieve because it is a point of the small étale
site (Stacks 04K0, `AlgebraicGeometry.Space.etaleSitePoint`); the sieve-level lifting is
Mathlib's `CategoryTheory.GrothendieckTopology.Point.jointly_surjective`, so the precoverage
form `AlgebraicGeometry.Space.geometricFiber_jointly_surjective` is not used directly.  The
lift lands in a member of the *generated* sieve, which factors through a member of the
presieve, and it is that member — affine, with free sections — which becomes the
neighbourhood.

Three spellings of one ring and one module have to be reconciled, and all three are
definitional:

* `AlgebraicGeometry.Space.chartRing` and `Γ(chartScheme A, ⊤)` are the same type with the
  same module structure on the sections of `F`; only the `CommRing` instance is assembled
  differently, by `AlgebraicGeometry.Space.chartRing_commRing` against `CommRingCat`'s, and the
  two agree up to the proof field `mul_comm`.
* `AlgebraicGeometry.Space.restrictToChart` is typed as a `SheafOfModules` over the
  `RingCat`-valued structure sheaf, while `AlgebraicGeometry.Scheme.Modules` is a `def` that
  does not unfold at instance-reducible transparency, so neither the `Γ(-, V)` notation's module
  structure nor the quasi-coherence instance is found on it.  `chartRestrictionModules` is the
  same term with the type spelled the other way round.
* the repository carries a second module structure on the ordinary stalk, which instance search
  prefers in this import closure; Mathlib's is the one
  `AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv` is stated over, so it is supplied
  by `let`, exactly as in
  `AlgebraicGeometry.Space.finitePresentation_chartZariskiModuleStalk`.

`AlgebraicGeometry.Space.flat_sections_of_iso` is stated for an abstract isomorphism of
`AlgebraicGeometry.Scheme.Modules` rather than applied at
`AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf` directly.  That is not
cosmetic: `restrictToChart` sheafifies through `hasSheafifyEssentiallySmallSite`, and any
unification that has to reduce the resulting term exhausts the default heartbeat limit, and
raising that limit is not an option in this repository.

No declaration here carries a `stacks` tag.  Stacks 05VV is tagged at
`AlgebraicGeometry.Space.IsFlatOver`, Stacks 05VP at the comparison map and at
`AlgebraicGeometry.Space.chartZariskiModuleStalk`, Stacks 0409 at
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` and Stacks 0CZA at
`AlgebraicGeometry.Space.exists_fittingRankStratification_spec`, whose suffix records that the
representability of the flatness functor is not claimed.  What is below is one implication
between those predicates, which is a step in the representability and not a clause of any tag;
the other implication, flatness of `G_T` forcing a factorisation through a stratum, is not
proved here.

## References

* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.ModuleStalkSpecialization

/-- **The stalk of a quasi-coherent module is flat as soon as its sections over an affine open
are.**  Let `F` be a quasi-coherent `𝒪_X`-module on a scheme `X`, let `U` be an affine open and
let `x ∈ U`.  If `Γ(F, U)` is a flat `Γ(X, U)`-module then the stalk `F_x` is a flat
`𝒪_{X, x}`-module.

The germ map exhibits `F_x` as the localization of `Γ(F, U)` at the prime of `x`
(`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`) over the localization
`𝒪_{X, x}` of `Γ(X, U)` at that prime
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), and a localization of a flat module is
flat over the localized ring. -/
theorem flat_stalk_of_flat_sections {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (hflat : Module.Flat Γ(X, U) Γ(F, U)) :
    letI := stalkModule F x
    Module.Flat ↥(X.presheaf.stalk x) ↥(F.presheaf.stalk x) := by
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  let := stalkModule F x
  let := sectionsStalkModule F hx
  have := isScalarTower_sectionsStalk F hx
  have := isLocalizedModule_germₗ F hU hx
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact Module.Flat.of_isLocalizedModule ↥(X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (germₗ F hx)

end Stacks.ModuleStalkSpecialization

namespace AlgebraicGeometry.Space

/-- Flatness of the sections over an open transfers along an isomorphism of
`AlgebraicGeometry.Scheme.Modules`.

Stated for an abstract isomorphism rather than applied directly at the one it is used for, so
that no unification has to look inside `AlgebraicGeometry.Space.restrictToChart`, whose
sheafification carries the `HasSheafify` instance of an essentially small site. -/
private theorem flat_sections_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (ι : M ≅ N)
    (V : Y.Opens) (h : Module.Flat Γ(Y, V) Γ(N, V)) :
    Module.Flat Γ(Y, V) Γ(M, V) := by
  let e := ((SheafOfModules.evaluation Y.ringCatSheaf (op V)).mapIso ι).toLinearEquiv
  exact Module.Flat.of_semilinearEquiv (RingEquiv.refl Γ(Y, V))
    (show (Γ(M, V) : Type u) ≃+ (Γ(N, V) : Type u) from e.toAddEquiv)
    fun a m => e.map_smul a m

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- `AlgebraicGeometry.Space.restrictToChart` at the module universe of the structure rings,
with its type spelled as `AlgebraicGeometry.Scheme.Modules` of the chart's scheme.  The two
spellings are definitionally equal, but `AlgebraicGeometry.Scheme.Modules` does not unfold at
instance-reducible transparency, so the `Γ(-, V)` notation's module structure on the sections is
available only on this one. -/
private noncomputable abbrev chartRestrictionModules (F : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) : (chartScheme A).Modules :=
  restrictToChart B S hS X.2 F A

/-- **The sections of the chart restriction over the whole chart are flat as soon as the
sections of the module over the chart are.**  The two differ by the identification of the étale
chart cut out by the whole of the chart's scheme with the chart itself
(`AlgebraicGeometry.Space.isIso_chartOpensTopHom`) and by the universe lift which
`AlgebraicGeometry.Space.restrictToChart` introduces; the change of scalars along that
identification is the structure sheaf applied to it, on the nose. -/
theorem flat_sections_chartRestrictionSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1)
    (hflat : Module.Flat Γ(chartScheme A, ⊤) (F.val.obj (op A))) :
    Module.Flat Γ(chartScheme A, ⊤) Γ(chartRestrictionSheaf B S hS X F A, ⊤) := by
  let k : (F.val.obj (op A) : Type u) ≃+ (Γ(chartRestrictionSheaf B S hS X F A, ⊤) : Type u) :=
    (F.val.presheaf.mapIso
        (asIso (chartOpensTopHom B S hS X A)).op).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift.symm
  have hk : ∀ (a : Γ(chartScheme A, ⊤)) (m : F.val.obj (op A)), k (a • m) = a • k m := fun a m =>
    congrArg ULift.up (F.val.map_smul (chartOpensTopHom B S hS X A).op _ m)
  exact Module.Flat.of_semilinearEquiv (RingEquiv.refl Γ(chartScheme A, ⊤)) k.symm
    fun a m => k.symm_apply_eq.2 (by rw [hk, k.apply_symm_apply]; rfl)

/-- **The Zariski stalk of the chart restriction is flat as soon as the sections over the chart
are.**  Let `F` be a quasi-coherent `𝒪_X`-module and let `N` be a small étale neighbourhood of a
geometric point whose chart has affine underlying scheme `U`.  If `F(N)` is a flat module over
the chart ring `Γ(U, ⊤)`, then the Zariski stalk `(a^* F)_u` of Stacks 05VP is a flat module
over the local ring `𝒪_{U, u}` of the chart.

The Zariski stalk is the ordinary stalk of the chart restriction
(`AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv`), the chart restriction is
quasi-coherent (`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`) and its sections over
`⊤` are the sections of `F` over the chart, so the stalk is a localization of a flat module. -/
theorem flat_chartZariskiModuleStalk_of_flat_sections (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) {x : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood x) (haff : IsAffine (chartScheme N.chart))
    (hflat : Module.Flat Γ(chartScheme N.chart, ⊤) (F.val.obj (op N.chart))) :
    Module.Flat ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) := by
  have := isQuasicoherent_restrictToChart B S hS X F hqc N.chart
  have hsec : Module.Flat Γ(chartScheme N.chart, ⊤)
      Γ(chartRestrictionModules B S hS X F N.chart, ⊤) :=
    flat_sections_of_iso (M := chartRestrictionModules B S hS X F N.chart)
      (N := chartRestrictionSheaf B S hS X F N.chart)
      (restrictToChartIsoChartRestrictionSheaf B S hS X F N.chart) ⊤
      (flat_sections_chartRestrictionSheaf B S hS X F N.chart hflat)
  have h := Stacks.ModuleStalkSpecialization.flat_stalk_of_flat_sections
    (chartRestrictionModules B S hS X F N.chart) (isAffineOpen_top _)
    (show chartPoint B S hS X.1 N ∈ (⊤ : (chartScheme N.chart).Opens) from trivial) hsec
  -- the repository carries a second module structure on the stalk, which instance search
  -- prefers in this import closure; Mathlib's is the one the comparison is stated over
  let : Module ↥(chartLocalRing B S hS X.1 N)
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS X.2 N F).presheaf
        (chartPoint B S hS X.1 N)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (chartRestrictionPresheafOfModules B S hS X.2 N F) (chartPoint B S hS X.1 N)
  exact (Module.Flat.equiv_iff
    (chartZariskiModuleStalkStalkEquiv B S hS X.2 N F)).2 h

/-- **A module finite locally free of rank `r` has a flat chart stalk at every geometric
point.**  For a quasi-coherent `𝒪_X`-module `F` which is finite locally free of rank `r` in the
sense of the rank clause of Stacks 0409, every geometric point of `X` has a small étale
neighbourhood on whose chart the Zariski stalk of the restriction of `F` is flat over the local
ring of the chart.

The affine charts over which the sections of `F` are finite locally free of rank `r` generate a
covering sieve of every chart, and a geometric point lifts through every covering sieve of the
small étale site, being a point of it by Stacks 04K0.  The sections over such a chart are flat
by Stacks 00NW. -/
theorem exists_flat_chartZariskiModuleStalk_of_isFiniteLocallyFreeOfRank
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite) (r : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) F r)
    (x : GeometricPoint B S hS X.1) :
    ∃ N : SmallEtaleNeighborhood x,
      Module.Flat ↥(chartLocalRing B S hS X.1 N)
        ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) := by
  obtain ⟨N₀⟩ := (isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x).nonempty
  obtain ⟨V, f, hf, q, -⟩ := (etaleSitePoint B S hS X.1 x X.2).jointly_surjective
    (Sieve.generate (fun (W : SmallEtale B S hS X.1) (_ : W ⟶ N₀.chart) =>
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
        Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 W)
          (F.val.obj (op W)) r))
    (freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS X.1 X.2 F r hr N₀.chart)
    (show GeometricFiber B S hS X.1 x N₀.chart from ⟨N₀.point, N₀.point_comp⟩)
  obtain ⟨Z, g, -, ⟨haff, hfree⟩, -⟩ := hf
  exact ⟨⟨Z, ((geometricFiber B S hS X.1 x).map g q).1,
    ((geometricFiber B S hS X.1 x).map g q).2⟩,
    flat_chartZariskiModuleStalk_of_flat_sections B S hS X F hqc _ haff
      (Module.flat_of_isFiniteLocallyFreeOfRank hfree)⟩

/-- **A quasi-coherent `𝒪_X`-module finite locally free of rank `r` is flat over its own
algebraic space**, in the sense of Stacks 05VV read along the identity of `X`.

Every geometric point has a chart on which the Zariski stalk of the restriction is flat, and by
Stacks 05VP the geometric stalk is a base change of that Zariski stalk, so every geometric stalk
is flat; the stalk criterion for flatness over the space itself then applies. -/
theorem isFlatOver_id_of_isFiniteLocallyFreeOfRank (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) (r : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) F r) :
    IsFlatOver B S hS X.2 (𝟙 X : X ⟶ X).hom F :=
  isFlatOver_id_of_forall_exists_flat_chartZariskiModuleStalk B S hS F
    (exists_flat_chartZariskiModuleStalk_of_isFiniteLocallyFreeOfRank B S hS X F hqc r hr)

end AlgebraicGeometry.Space

end

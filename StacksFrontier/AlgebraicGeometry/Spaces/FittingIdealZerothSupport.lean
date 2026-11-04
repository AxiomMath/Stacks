module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealChain
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi

/-!
# The zeroth Fitting ideal annihilates the module

Let `X` be an algebraic space over a scheme `S` and let `G` be an `𝒪_X`-module of finite type,
cartesian on affine étale charts.  The zeroth Fitting ideal sheaf `Fit_0(G)` annihilates `G`, and
its zero locus is the support of `G`.  These are the inputs of Stacks 0CZ6, which is
`AlgebraicGeometry.Space.schemeTheoreticSupport_le_fittingClosedSubspace`,
`AlgebraicGeometry.Space.range_pointsMap_schemeTheoreticSupport_eq_supportOfSheaf` and
`AlgebraicGeometry.Space.exists_module_on_fittingClosedSubspace`.

## Main results

* `AlgebraicGeometry.Space.fittingIdeal_zero_smul_eq_zero` and
  `AlgebraicGeometry.Space.idealSmul_fittingIdeal_zero_top_eq_bot`: `Fit_0(G) · G = 0`.
* `AlgebraicGeometry.Space.idealZeroLocus_fittingIdeal_zero_eq_supportOfSheaf`: the zero locus
  of `Fit_0(G)` is the support of `G`.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_of_definingIdealSheaf_eq_fittingIdeal_zero`: the
  ideal cutting out the closed subspace `Z₀` defined by `Fit_0(G)` annihilates `G`.

## Implementation notes

Everything rests on the annihilation `Fit_0(G) · G = 0`, which is the sheaf-theoretic form of
the ring-theoretic inclusion `Fit_0(M) ⊆ Ann(M)` of Stacks 07ZA.  It is checked on affine étale
charts, where the sections of `Fit_0(G)` are the ordinary zeroth Fitting ideal of the module of
sections (`AlgebraicGeometry.Space.fittingIdeal_obj_eq_fittingIdealOnChart`) and the
ring-theoretic inclusion applies; the affine charts cover every chart, so the sheaf condition on
`G` glues the chartwise statements.

The statements here take the finiteness of `G` in the chartwise form `hfin`, that the sections of
`G` over every affine étale chart form a finite module over the chart ring, together with the
cartesian condition `hG`.  For a quasi-coherent module of finite type both hold, by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`.

## References

* [Stacks Project, Tag 0CZ6](https://stacks.math.columbia.edu/tag/0CZ6)
* [Stacks Project, Tag 0CYX](https://stacks.math.columbia.edu/tag/0CYX)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The zeroth Fitting ideal sheaf annihilates the module -/

/-- Over an affine étale chart the sections of the zeroth Fitting ideal sheaf annihilate the
sections of the module: there they are the ordinary zeroth Fitting ideal of the module of
sections, which is contained in its annihilator by Stacks 07ZA. -/
private theorem fittingIdeal_zero_smul_eq_zero_of_isAffine
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    {V : SmallEtale B S hS X.1}
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (a : chartRing B S hS X.1 X.2 V)
    (ha : a ∈ (fittingIdeal B S hS X.1 X.2 G 0).obj (op V))
    (t : G.val.obj (op V)) : a • t = 0 := by
  have hfinV := hfin V hV
  have ha' : a ∈ @fittingIdealOnChart B S hS X.1 X.2 G 0 V hfinV := by
    rw [← fittingIdeal_obj_eq_fittingIdealOnChart G hG hfin 0 hV]
    exact ha
  have hann : a ∈ Module.annihilator (chartRing B S hS X.1 X.2 V) (G.val.obj (op V)) :=
    (fittingIdeal_basic_properties.{u, u, u, u}
      (R := chartRing B S hS X.1 X.2 V) (M := G.val.obj (op V))).2.2.2.2.2.1 ha'
  exact Module.mem_annihilator.mp hann t

/-- **The zeroth Fitting ideal sheaf annihilates the module.**  This is the sheaf-theoretic form
of the ring-theoretic inclusion `Fit_0(M) ⊆ Ann(M)` of Stacks 07ZA, and it is the content of
parts (1) and (3) of Stacks 0CZ6: it says that the module is a module over the structure sheaf
of the closed subspace cut out by `Fit_0(G)`.

The affine étale charts cover every chart, the statement holds on them by
`AlgebraicGeometry.Space.fittingIdeal_obj_eq_fittingIdealOnChart`, and the sheaf condition on
`G` glues the chartwise statements. -/
theorem fittingIdeal_zero_smul_eq_zero
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (W : SmallEtale B S hS X.1) (a : chartRing B S hS X.1 X.2 W)
    (ha : a ∈ (fittingIdeal B S hS X.1 X.2 G 0).obj (op W)) (t : G.val.obj (op W)) :
    a • t = 0 := by
  obtain ⟨ι, V, f, hVaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X.1 W
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      (G.val.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.HasSheafCompose.isSheaf _ G.isSheaf
  have hsep := (Presieve.isSheafFor_iff_generate (Presieve.ofArrows V f)).mpr (hsheaf _ hcov)
  refine hsep.isSeparatedFor.ext fun Y g hg ↦ ?_
  obtain ⟨i⟩ := hg
  show G.val.map (f i).op (a • t) = G.val.map (f i).op 0
  rw [map_zero]
  refine (G.val.map_smul (f i).op a t).trans ?_
  exact fittingIdeal_zero_smul_eq_zero_of_isAffine B S hS X G hG hfin (hVaff i) _
    ((fittingIdeal B S hS X.1 X.2 G 0).map_mem (f i).op ha) _

/-- **The zeroth Fitting ideal of the sections over an étale chart annihilates the sections of
the module there.**  This is the chartwise form of
`AlgebraicGeometry.Space.fittingIdeal_zero_smul_eq_zero`. -/
theorem chartSectionIdeal_fittingIdeal_zero_smul_top_eq_bot
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (W : SmallEtale B S hS X.1) :
    chartSectionIdeal B S hS X.1 X.2 (fittingIdeal B S hS X.1 X.2 G 0) W •
        (⊤ : Submodule (chartRing B S hS X.1 X.2 W) (G.val.obj (op W))) = ⊥ :=
  le_bot_iff.1 (Submodule.smul_le.2 fun a ha z _ ↦ (Submodule.mem_bot _).2
    (fittingIdeal_zero_smul_eq_zero B S hS X G hG hfin W a ha z))

/-- **`Fit_0(G) · G = 0`**, as sheaf submodules of `G`.  This says that `G` is a module over the
structure sheaf of the closed subspace cut out by `Fit_0(G)`, which is the assertion of
Stacks 0CZ6 that parts (1) and (3) rest on. -/
theorem idealSmul_fittingIdeal_zero_top_eq_bot
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W))) :
    Stacks.Sites.idealSmul (M := G)
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
          (fittingIdeal B S hS X.1 X.2 G 0) 1) ⊤ = ⊥ :=
  (idealSmul_idealPow_top_eq_bot_iff B S hS X.1 X.2 _ G 1).2 fun W ↦ by
    rw [pow_one]
    exact chartSectionIdeal_fittingIdeal_zero_smul_top_eq_bot B S hS X G hG hfin W

/-- A chart on which the zeroth Fitting ideal sheaf is the whole structure sheaf carries only the
zero section of the module. -/
theorem subsingleton_of_fittingIdeal_zero_obj_eq_top
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (W : SmallEtale B S hS X.1)
    (hW : (fittingIdeal B S hS X.1 X.2 G 0).obj (op W) = ⊤) :
    Subsingleton (G.val.obj (op W)) :=
  subsingleton_sections_of_chartIdeal_eq_top B S hS X.1 X.2 _ G (n := 1)
    (by rw [pow_one]
        exact chartSectionIdeal_fittingIdeal_zero_smul_top_eq_bot B S hS X G hG hfin W) hW

/-! ### The zero locus of the zeroth Fitting ideal -/

/-- **One half of Stacks 0CZ6, part (2).**  The support of a quasi-coherent `𝒪_X`-module of
finite type is contained in the point set of the closed subspace cut out by its zeroth Fitting
ideal.

Over a chart on which `Fit_0(G)` is the whole structure sheaf, and over every chart below it,
the unit function annihilates `G`, so `G` has only the zero section there and the support misses
the image of that chart. -/
@[sga "7 VI 5.1" "5.1(c)"]
theorem supportOfSheaf_subset_idealZeroLocus_fittingIdeal_zero
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W))) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) ⊆
      idealZeroLocus B S hS X (fittingIdeal B S hS X.1 X.2 G 0) :=
  supportOfSheaf_subset_idealZeroLocus_of_idealSmul_idealPow_top_eq_bot B S hS X G _
    (idealSmul_fittingIdeal_zero_top_eq_bot B S hS X G hG hfin)

/-- **The zero locus of the zeroth Fitting ideal is the support.**  The point set cut out by the
zeroth Fitting ideal sheaf of an `𝒪_X`-module of finite type, cartesian on affine charts, is the
support of the module.

For the inclusion of the support, `Fit_0(G)` annihilates `G`, so `G` vanishes over every chart on
which `Fit_0(G)` is the whole structure sheaf.  Conversely, at a point outside the support a
geometric point over it has vanishing stalk, so some small étale neighbourhood of it carries only
the zero section of `G`; refining that neighbourhood to an affine étale chart, the zeroth Fitting
ideal of the zero module there is the unit ideal, and the point lies in the image of that
chart. -/
@[sga "7 VI 5.1" "more general"]
theorem idealZeroLocus_fittingIdeal_zero_eq_supportOfSheaf
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (hGft : SheafOfModules.IsFiniteTypeOnSite G) :
    idealZeroLocus B S hS X (fittingIdeal B S hS X.1 X.2 G 0) =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) := by
  have _ := hGft
  refine Set.Subset.antisymm (fun x hx ↦ ?_)
    (supportOfSheaf_subset_idealZeroLocus_fittingIdeal_zero B S hS X G hG hfin)
  by_contra hxs
  obtain ⟨p, hpx⟩ := exists_geometricRepresentative B S hS X.1 x
  have hpzero : Subsingleton (stalkSet p
      (((SheafOfModules.toSheaf _).obj G).obj ⋙ forget AddCommGrpCat)) := by
    by_contra h
    exact hxs ⟨p, hpx, h⟩
  obtain ⟨U₀, hU₀⟩ :=
    exists_zero_neighborhood_of_isFiniteTypeOnSite B S hS X.1 X.2 (𝟙 G) p hpzero
  obtain ⟨ι, V, f, hVaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X.1 U₀.chart
  obtain ⟨W, g, hg, w, -⟩ :=
    (etaleSitePoint B S hS X.1 p X.2).jointly_surjective _ hcov
      (show (etaleSitePoint B S hS X.1 p X.2).fiber.obj U₀.chart from
        ⟨U₀.point, U₀.point_comp⟩)
  obtain ⟨i, k, -⟩ := Sieve.ofArrows.exists hg
  have hsub : Subsingleton (G.val.obj (op (V i))) := hU₀ (V i) (f i)
  have hspan : Submodule.span (chartRing B S hS X.1 X.2 (V i))
      (Set.range (Fin.elim0 : Fin 0 → G.val.obj (op (V i)))) = ⊤ :=
    Submodule.eq_top_iff'.2 fun y ↦ by
      rw [Subsingleton.elim y 0]
      exact Submodule.zero_mem _
  have hTop : (fittingIdeal B S hS X.1 X.2 G 0).obj (op (V i)) = ⊤ :=
    fittingIdeal_obj_eq_top_of_span_eq_top G (V i) (hVaff i)
      (Fin.elim0 : Fin 0 → G.val.obj (op (V i))) hspan
  let N : SmallEtaleNeighborhood p :=
    ⟨V i, ((geometricFiber B S hS X.1 p).map k w).val,
      ((geometricFiber B S hS X.1 p).map k w).property⟩
  exact hx ⟨V i, hTop, (neighborhoodPoint B S hS X.1 N).image,
    (neighborhoodPoint_image B S hS X.1 N).trans hpx⟩

/-! ### The ideal of the zeroth Fitting subspace annihilates the module -/

/-- **The ideal cutting out the zeroth Fitting subspace annihilates the module.**  This is
`AlgebraicGeometry.Space.fittingIdeal_zero_smul_eq_zero` read through the identification of the
defining ideal of the subspace with `Fit_0(G)`. -/
theorem annihilatedByKerIdeal_of_definingIdealSheaf_eq_fittingIdeal_zero
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (Z₀ : ClosedSubspaces B S hS X.1)
    (hZ₀ : definingIdealSheaf B S hS X Z₀ = fittingIdeal B S hS X.1 X.2 G 0) :
    AnnihilatedByKerIdeal B S hS
      (ObjectProperty.homMk Z₀.1.ι :
        (⟨Z₀.1.toFunctor, Z₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) G := by
  intro U a ha t
  refine fittingIdeal_zero_smul_eq_zero B S hS X G hG hfin U.unop a ?_ t
  have hmem : a ∈ (definingIdealSheaf B S hS X Z₀).obj U := by
    rw [definingIdealSheaf_obj]
    exact (SheafOfModules.mem_kerIdeal _ U a).1 ha
  rwa [hZ₀] at hmem

end AlgebraicGeometry.Space

end

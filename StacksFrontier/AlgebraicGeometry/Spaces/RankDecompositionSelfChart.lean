module

public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.FiniteDegree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseRankCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleRepresentedSelf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFittingRank

/-!
# The constant-rank decomposition of a scheme carrying a finite locally free module on its
small étale site

Let `W` be an object of a big fppf site `B` over `S` and let `H` be a quasi-coherent `𝒪`-module
on the small étale site of the represented algebraic space `h_W` whose sections over the
identity chart are finite locally free over the ring of regular functions of `W`.  This file
produces the decomposition of `W` into open pieces on which `H` has a **single** rank: every
point of the scheme of `W` has a basic-open neighbourhood `D(g)` such that the pullback of `H`
to `h_{D(g)}` is finite locally free of one rank `n` in the sense of the rank clause of
Stacks 0409, `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`.

This is the step that turns a rank depending on the chart into a rank.  The chartwise
machinery of `StacksFrontier/AlgebraicGeometry/Spaces/ChartwiseRankCartesian.lean` concludes
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` from a rank known at *every* affine
chart, but the ranks it is handed need not agree; over a representable base the identity chart
is terminal, so one rank read there propagates to all of them.

## Main results

* `AlgebraicGeometry.Space.chartToSelfChart`: the unique morphism from an étale chart of a
  represented presheaf to its identity chart.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_selfChart`: **a rank at the identity
  chart of an affine object is a rank on the whole small étale site.**
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_sections_modulePullback`: the converse of
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_sections_smallEtalePostcomp` — a rank of
  the sections over a composite chart is a rank of the sections of the étale pullback.
* `AlgebraicGeometry.Space.exists_basicOpen_chart_basis_of_isFiniteLocallyFree`: around every
  point of an affine chart over which the sections are finite locally free there is a
  basic-open chart over which they are *free*, of a definite rank.
* `AlgebraicGeometry.Space.exists_basicOpen_isFiniteLocallyFreeOfRank`: **the constant-rank
  decomposition.** Every point of an affine object `W` has a basic-open neighbourhood on which
  the pullback of `H` is finite locally free of a single rank.
* `AlgebraicGeometry.Space.flat_sections_selfChart_of_isFlatOver_id` and
  `isFiniteLocallyFree_sections_selfChart`: the sections over the identity chart of an affine
  object of a quasi-coherent module of finite presentation flat over its own space are finite
  locally free -- Stacks 00NX read at that chart.
* `AlgebraicGeometry.Space.exists_basicOpen_isFiniteLocallyFreeOfRank_of_isFlatOver_id`: **the
  constant-rank decomposition from the hypotheses of Stacks 0CZA.**

## Implementation notes

Two chart identifications carry the geometry, and both hold on the nose:
`AlgebraicGeometry.Space.openChart_selfChart_eq_etaleHomChart` reads a Zariski open of the
scheme of `W` either as an étale chart of `h_W` or as the chart cut out by the open immersion,
and `AlgebraicGeometry.Space.smallEtalePostcomp_obj_selfChart` says that pushing the identity
chart of the open subscheme forward along the open immersion gives the same chart.  Together
with `AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`, which is also definitional, they
make the sections of the pullback over the identity chart of the piece *be* the sections of `H`
over the basic-open chart, so no comparison isomorphism has to be carried.

The rank is read off from a genuine basis rather than from a rank function: the definition of
`Module.IsFiniteLocallyFree` already supplies a family of elements whose basic opens cover and
over whose away-localizations the module is free and finite, and a free finite module has a
basis indexed by `Fin n` for `n` the cardinality of any basis.  This is why no
`AlgebraicGeometry.Scheme.Modules.fiberRank` analogue for algebraic spaces is needed here: the
rank that has to be collected is the cardinality of a local basis, and the localization
comparisons of `StacksFrontier/AlgebraicGeometry/Spaces/ChartBasicOpenLocalization.lean` transport
that basis to the basic-open chart directly.

Finiteness of the sections over the identity chart, which
`Module.IsFiniteLocallyFreeOfRank.baseChange` needs, comes from the basis as well
(`Module.Finite.of_basis`), so nothing has to be assumed about it.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The identity chart is terminal -/

section SelfChart

variable (W : BigFppfOver B S hS)

/-- The unique morphism from an étale chart of a represented presheaf to its identity chart.

The identity `CostructuredArrow.mk (𝟙 (yoneda.obj W))` is terminal in the category of scheme
charts of `h_W` because `yoneda` is fully faithful, and the étale charts form a full
subcategory of it. -/
noncomputable def chartToSelfChart (V : SmallEtale B S hS (yoneda.obj W)) :
    V ⟶ selfChart B S hS W :=
  ObjectProperty.homMk (CostructuredArrow.mkIdTerminal.from V.1)

variable (hW : IsAlgebraicSpace B S hS (yoneda.obj W))

/-- **A rank of the sections over the identity chart of an affine object is a rank on the whole
small étale site.**  Let `W` be an object of the big fppf site whose scheme is affine and whose
represented presheaf is an algebraic space, and let `H` be an `𝒪`-module on the small étale site
of `h_W` cartesian on affine charts whose sections over the identity chart are finite locally
free of rank `s`.  Then `H` is finite locally free of rank `s` in the sense of the rank clause
of Stacks 0409.

The identity chart is terminal, so every affine chart `V` carries a morphism to it, and
cartesianness identifies `H(V)` with `𝒪(V) ⊗_{𝒪(W)} H(W)`; the rank is preserved by that base
change (`Module.IsFiniteLocallyFreeOfRank.baseChange`), and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_forall_isAffine` assembles the chartwise
ranks. -/
theorem isFiniteLocallyFreeOfRank_of_selfChart
    (H : Modules.{u, u} B S hS (yoneda.obj W) hW) (hH : IsCartesianOnAffineCharts H)
    (hWaff : IsAffine (chartScheme (selfChart B S hS W))) (s : ℕ)
    (hfin : Module.Finite (chartRing B S hS (yoneda.obj W) hW (selfChart B S hS W))
      (H.val.obj (op (selfChart B S hS W))))
    (hs : Module.IsFiniteLocallyFreeOfRank
      (chartRing B S hS (yoneda.obj W) hW (selfChart B S hS W))
      (H.val.obj (op (selfChart B S hS W))) s) :
    RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite B S hS (yoneda.obj W) hW) H s := by
  refine isFiniteLocallyFreeOfRank_of_forall_isAffine B S hS (yoneda.obj W) hW H hH s
    fun V hVaff => ?_
  have := hfin
  let := chartAlgebra (hF := hW) (chartToSelfChart B S hS W V)
  exact Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
    (LinearEquiv.ofBijective (sectionsBaseChange H (chartToSelfChart B S hS W V))
      (hH (selfChart B S hS W) V hWaff hVaff (chartToSelfChart B S hS W V)))
    (Module.IsFiniteLocallyFreeOfRank.baseChange _ hs)

end SelfChart

/-! ### The two chart identifications -/

section ChartComparison

variable {W : BigFppfOver B S hS}

/-- **A Zariski open of the scheme of `W`, read as an étale chart of `h_W`, is the chart cut
out by the open immersion it induces.**  Both sides are the costructured arrow on the open
subscheme with structure morphism the open immersion. -/
theorem openChart_selfChart_eq_etaleHomChart
    (O : ((BigFppfOver.toScheme B S hS).obj W).Opens) :
    openChart B S hS (yoneda.obj W) (selfChart B S hS W) O =
      etaleHomChart B S hS (openSub W O) (openSubHom W O)
        (etale_toScheme_map_openSubHom B S hS W O) :=
  rfl

/-- **Pushing the identity chart of the source of an étale morphism of the site forward is the
chart cut out by that morphism.** -/
theorem smallEtalePostcomp_obj_selfChart {W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g)) :
    (smallEtalePostcomp B S hS (schemeSpaceMap g)
        (isEtale_schemeSpaceMap B S hS W' g hg)).obj (selfChart B S hS W') =
      etaleHomChart B S hS W' g hg :=
  rfl

end ChartComparison

/-! ### Transporting a chartwise rank to an étale pullback -/

/-- The sections over a chart of the module pullback along an étale morphism agree with those of
the étale module pullback. -/
private noncomputable def modulePullbackSectionsEquiv {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS X.1) :
    (((modulePullback B S hS f).obj G).val.obj (op V)) ≃ₗ[chartRing B S hS X.1 X.2 V]
      (((etaleModulePullback.{u, u} B S hS f hf).obj G).val.obj (op V)) :=
  ((SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) (op V)).mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).app G)).toLinearEquiv

/-- **A rank of the sections of a module over a composite chart is a rank of the sections of its
étale pullback over the chart.**  This is the converse of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_sections_smallEtalePostcomp`, proved the same
way: pullback along an étale morphism is étale restriction (Stacks 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`), and étale restriction leaves
the sections over a chart alone. -/
theorem isFiniteLocallyFreeOfRank_sections_modulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (G : Modules.{u, u} B S hS Y.1 Y.2) (k : ℕ)
    (V : SmallEtale B S hS X.1)
    (hV : Module.IsFiniteLocallyFreeOfRank
      (chartRing B S hS Y.1 Y.2 ((smallEtalePostcomp B S hS f hf).obj V))
      (G.val.obj (op ((smallEtalePostcomp B S hS f hf).obj V))) k) :
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS X.1 X.2 V)
      (((modulePullback B S hS f).obj G).val.obj (op V)) k :=
  Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
    (modulePullbackSectionsEquiv B S hS f hf G V).symm hV

/-- **The sections of an étale pullback over a chart are finite over the regular functions of
the chart as soon as the sections of the module over the composite chart are.** -/
theorem module_finite_sections_modulePullback_of_smallEtalePostcomp
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS X.1)
    (hV : Module.Finite (chartRing B S hS Y.1 Y.2 ((smallEtalePostcomp B S hS f hf).obj V))
      (G.val.obj (op ((smallEtalePostcomp B S hS f hf).obj V)))) :
    Module.Finite (chartRing B S hS X.1 X.2 V)
      (((modulePullback B S hS f).obj G).val.obj (op V)) := by
  have : Module.Finite (chartRing B S hS X.1 X.2 V)
      (((etaleModulePullback.{u, u} B S hS f hf).obj G).val.obj (op V)) := hV
  exact Module.Finite.equiv (modulePullbackSectionsEquiv B S hS f hf G V).symm

/-! ### A basis of a definite rank on a basic-open chart -/

section Decomposition

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Around every point of an affine chart over which the sections are finite locally free
there is a basic-open chart over which they are free, of a definite rank.**

This is the unranked companion of
`AlgebraicGeometry.Space.exists_basicOpen_chart_basis`: the elements cutting out the
trivializing basic opens of `Module.IsFiniteLocallyFree` span the unit ideal, so one of them is
invertible at the point, and over the basic-open chart it cuts out the functions are the
away-localization and the sections are the localized module, so the basis transports by
`Module.nonempty_basis_of_isLocalizedModule_away`.  The rank is the cardinality of the chosen
basis of the localized module, which is finite because that module is. -/
theorem exists_basicOpen_chart_basis_of_isFiniteLocallyFree (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H) {V : SmallEtale B S hS F}
    (hV : IsAffine (chartScheme V))
    (hfree : Module.IsFiniteLocallyFree (chartRing B S hS F hF V) (H.val.obj (op V)))
    (z : chartScheme V) :
    ∃ (g : chartRing B S hS F hF V) (n : ℕ), z ∈ (chartScheme V).basicOpen g ∧
      Nonempty (Module.Basis (Fin n)
        (chartRing B S hS F hF (openChart B S hS F V ((chartScheme V).basicOpen g)))
        (H.val.obj (op (openChart B S hS F V ((chartScheme V).basicOpen g))))) := by
  classical
  obtain ⟨κ, gf, hspan, hloc⟩ := hfree
  have := hV
  have hle : (⊤ : (chartScheme V).Opens) ≤
      ⨆ f : (Set.range gf), (chartScheme V).basicOpen f.1 :=
    (isAffineOpen_top (chartScheme V)).self_le_iSup_basicOpen_iff.mpr hspan
  obtain ⟨f, hzf⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hle (show z ∈ (⊤ : (chartScheme V).Opens) from trivial))
  obtain ⟨i, hi⟩ := f.2
  have := (hloc i).1
  have := (hloc i).2
  have := Module.Free.ChooseBasisIndex.fintype (Localization.Away (gf i))
    (LocalizedModule (Submonoid.powers (gf i)) (H.val.obj (op V)))
  refine ⟨gf i, Fintype.card (Module.Free.ChooseBasisIndex (Localization.Away (gf i))
      (LocalizedModule (Submonoid.powers (gf i)) (H.val.obj (op V)))),
    by rw [hi]; exact hzf, ?_⟩
  let := chartAlgebra (hF := hF)
    (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i)))
  let := chartSectionsModule H
    (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i)))
  have := chartSections_isScalarTower H
    (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i)))
  have := isLocalization_away_chartRing_openChart_basicOpen B S hS hF V hV (gf i)
  have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS hF H hH V hV (gf i)
  exact Module.nonempty_basis_of_isLocalizedModule_away (gf i)
    (chartRestrictLinear H
      (openChartInclusion B S hS F V ((chartScheme V).basicOpen (gf i))))
    ((Module.Free.chooseBasis (Localization.Away (gf i))
      (LocalizedModule (Submonoid.powers (gf i)) (H.val.obj (op V)))).reindex
        (Fintype.equivFin _))

end Decomposition

/-! ### The constant-rank decomposition -/

/-- **The constant-rank decomposition of an affine object of the big fppf site.**  Let `W` be an
object of the big fppf site whose scheme is affine, and let `H` be a quasi-coherent `𝒪`-module
on the small étale site of `h_W` whose sections over the identity chart are finite locally free
over the regular functions of `W`.  Then every point of the scheme of `W` lies in a basic open
`D(g)` such that the pullback of `H` to `h_{D(g)}` is finite locally free of **one** rank `n`,
in the sense of the rank clause of Stacks 0409.

This is the collection step the flatness clause of Stacks 0CZA needs: the chain of
`StacksFrontier/AlgebraicGeometry/Spaces/FittingStratificationFinitePresentation.lean` delivers
finite local freeness of the sections over each affine chart with no control of the rank, and
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` — the hypothesis of
`AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratum_iff` — needs a single rank.

The pieces are the basic opens of
`AlgebraicGeometry.Space.exists_basicOpen_chart_basis_of_isFiniteLocallyFree`, over which the
sections are genuinely free; `AlgebraicGeometry.Space.openChart_selfChart_eq_etaleHomChart` and
`AlgebraicGeometry.Space.smallEtalePostcomp_obj_selfChart` identify that basic-open chart of
`h_W` with the identity chart of the piece, and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_selfChart` propagates the rank from there
to every chart of the piece. -/
theorem exists_basicOpen_isFiniteLocallyFreeOfRank (W : BigFppfOver B S hS)
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W)) (H : Modules.{u, u} B S hS (yoneda.obj W) hW)
    (hHqc : H.IsQuasicoherentOnSite)
    (hWaff : IsAffine (chartScheme (selfChart B S hS W)))
    (hfree : Module.IsFiniteLocallyFree
      (chartRing B S hS (yoneda.obj W) hW (selfChart B S hS W))
      (H.val.obj (op (selfChart B S hS W))))
    (z : (BigFppfOver.toScheme B S hS).obj W) :
    ∃ (g : chartRing B S hS (yoneda.obj W) hW (selfChart B S hS W)) (n : ℕ),
      z ∈ ((BigFppfOver.toScheme B S hS).obj W).basicOpen g ∧
      RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS
          (yoneda.obj (openSub W (((BigFppfOver.toScheme B S hS).obj W).basicOpen g)))
          (isAlgebraicSpace_yoneda B S hS
            (openSub W (((BigFppfOver.toScheme B S hS).obj W).basicOpen g))))
        ((modulePullback B S hS (schemeSpaceMap
          (openSubHom W (((BigFppfOver.toScheme B S hS).obj W).basicOpen g)))).obj H) n := by
  obtain ⟨g, n, hzg, ⟨b⟩⟩ := exists_basicOpen_chart_basis_of_isFiniteLocallyFree B S hS
    (yoneda.obj W) hW H (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS
      (yoneda.obj W) hW H hHqc) hWaff hfree z
  set O := ((BigFppfOver.toScheme B S hS).obj W).basicOpen g with hO
  set W' := openSub W O with hW'
  have hgetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (openSubHom W O)) :=
    etale_toScheme_map_openSubHom B S hS W O
  have hetale : IsEtale B S hS (schemeSpaceMap (openSubHom W O)).hom :=
    isEtale_schemeSpaceMap B S hS W' (openSubHom W O) hgetale
  -- the sections of `H` over the basic-open chart, with their basis of rank `n`
  have hrank : Module.IsFiniteLocallyFreeOfRank
      (chartRing B S hS (yoneda.obj W) hW
        (openChart B S hS (yoneda.obj W) (selfChart B S hS W) O))
      (H.val.obj (op (openChart B S hS (yoneda.obj W) (selfChart B S hS W) O))) n :=
    Module.IsFiniteLocallyFreeOfRank.of_basis' b
  have hfin : Module.Finite
      (chartRing B S hS (yoneda.obj W) hW
        (openChart B S hS (yoneda.obj W) (selfChart B S hS W) O))
      (H.val.obj (op (openChart B S hS (yoneda.obj W) (selfChart B S hS W) O))) :=
    Module.Finite.of_basis b
  refine ⟨g, n, hzg, ?_⟩
  refine isFiniteLocallyFreeOfRank_of_selfChart B S hS W'
    (isAlgebraicSpace_yoneda B S hS W') _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS (yoneda.obj W')
      (isAlgebraicSpace_yoneda B S hS W') _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (schemeSpaceMap (openSubHom W O)) H hHqc))
    (isAffine_chartScheme_openChart_basicOpen B S hS (yoneda.obj W) (selfChart B S hS W)
      hWaff g)
    n
    (module_finite_sections_modulePullback_of_smallEtalePostcomp B S hS
      (schemeSpaceMap (openSubHom W O)) hetale H (selfChart B S hS W') hfin)
    (isFiniteLocallyFreeOfRank_sections_modulePullback B S hS
      (schemeSpaceMap (openSubHom W O)) hetale H n (selfChart B S hS W') hrank)


/-! ### The sections over the identity chart are finite locally free -/

section FromFlatness

/-- Flatness of the sections of a sheaf of modules on a scheme over an open is unchanged by an
isomorphism of the sheaf.

The isomorphism is left abstract on purpose: with a concrete
`AlgebraicGeometry.Space.restrictToChart` in its place, unification has to reduce a
sheafification carrying the `HasSheafify` instance of an essentially small site, which does not
terminate in the available budget. -/
private theorem flat_sections_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (V : Y.Opens) (h : Module.Flat Γ(Y, V) Γ(N, V)) :
    Module.Flat Γ(Y, V) Γ(M, V) := by
  have := h
  let l := ((SheafOfModules.evaluation Y.ringCatSheaf (op V)).mapIso e).toLinearEquiv
  exact Module.Flat.of_semilinearEquiv (RingEquiv.refl Γ(Y, V))
    (show (Γ(M, V) : Type u) ≃+ (Γ(N, V) : Type u) from l.toAddEquiv)
    fun a m => l.map_smul a m

variable (X : AlgebraicSpaces B S hS)

/-- **The sections of a module over a chart are flat as soon as the sections of its chart
restriction over the whole chart scheme are.**  This is the converse of
`AlgebraicGeometry.Space.flat_sections_chartRestrictionSheaf`, proved by the same semilinear
equivalence read in the other direction: the two sides differ by the identification of the
étale chart cut out by the whole of the chart's scheme with the chart itself
(`AlgebraicGeometry.Space.isIso_chartOpensTopHom`) and by the universe lift. -/
theorem flat_sections_of_flat_sections_chartRestrictionSheaf
    (F : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1)
    (hflat : Module.Flat Γ(chartScheme A, ⊤)
      Γ(chartRestrictionSheaf B S hS X F A, ⊤)) :
    Module.Flat Γ(chartScheme A, ⊤) (F.val.obj (op A)) := by
  have := hflat
  let k : (F.val.obj (op A) : Type u) ≃+ (Γ(chartRestrictionSheaf B S hS X F A, ⊤) : Type u) :=
    (F.val.presheaf.mapIso
        (asIso (chartOpensTopHom B S hS X A)).op).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift.symm
  exact Module.Flat.of_semilinearEquiv (RingEquiv.refl Γ(chartScheme A, ⊤)) k
    fun a m => congrArg ULift.up (F.val.map_smul (chartOpensTopHom B S hS X A).op a m)

/-- **The sections of a quasi-coherent module flat over its own affine represented algebraic
space are flat over the regular functions of the identity chart.**

Stacks 05VV flatness over the space restricts to ringed-space flatness of the Zariski
restriction over the identity of the representing scheme
(`AlgebraicGeometry.Space.flat_sections_representedZariskiRestriction_of_isFlatOver_id`), which
on an affine representing scheme is flatness of its global sections; those are the sections of
the module over the identity chart. -/
theorem flat_sections_selfChart_of_isFlatOver_id (T : BigFppfOver B S hS)
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T)) (G : Modules.{u, u} B S hS (yoneda.obj T) hT)
    (hGqc : G.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS hT (𝟙 (yoneda.obj T)) G)
    (hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    Module.Flat (chartRing B S hS (yoneda.obj T) hT (selfChart B S hS T))
      (G.val.obj (op (selfChart B S hS T))) := by
  have := hTaff
  refine flat_sections_of_flat_sections_chartRestrictionSheaf B S hS ⟨yoneda.obj T, hT⟩ G
    (selfChart B S hS T) (flat_sections_of_iso
      (restrictToChartIsoChartRestrictionSheaf B S hS ⟨yoneda.obj T, hT⟩ G
        (selfChart B S hS T)).symm ⊤ ?_)
  exact flat_sections_representedZariskiRestriction_of_isFlatOver_id B S hS T hT G hGqc hflat ⊤
    (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj T))

/-- **The sections over the identity chart of an affine object of a quasi-coherent module of
finite presentation flat over its own space are finite locally free.**  This is Stacks 00NX, the
equivalence of finite local freeness with finite presentation and flatness
(`Module.isFiniteLocallyFree_iff`), applied to the sections over the identity chart: those are
finitely presented by Stacks 0CZ3,
`AlgebraicGeometry.Space.module_finitePresentation_sections_of_isFinitePresentationOnSite`, and
flat by `AlgebraicGeometry.Space.flat_sections_selfChart_of_isFlatOver_id`. -/
theorem isFiniteLocallyFree_sections_selfChart (T : BigFppfOver B S hS)
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T)) (G : Modules.{u, u} B S hS (yoneda.obj T) hT)
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (hflat : IsFlatOver B S hS hT (𝟙 (yoneda.obj T)) G)
    (hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    Module.IsFiniteLocallyFree (chartRing B S hS (yoneda.obj T) hT (selfChart B S hS T))
      (G.val.obj (op (selfChart B S hS T))) :=
  (Module.isFiniteLocallyFree_iff _ _).2
    ⟨module_finitePresentation_sections_of_isFinitePresentationOnSite G hGqc hGfp
      (selfChart B S hS T) hTaff,
      flat_sections_selfChart_of_isFlatOver_id B S hS T hT G hGqc hflat hTaff⟩

/-- **The constant-rank decomposition, from the hypotheses of Stacks 0CZA.**  Let `W` be an
object of the big fppf site whose scheme is affine and whose represented presheaf is an
algebraic space, and let `H` be a quasi-coherent `𝒪`-module of finite presentation on the small
étale site of `h_W` which is flat over `h_W` in the sense of Stacks 05VV.  Then every point of
the scheme of `W` lies in a basic open `D(g)` such that the pullback of `H` to `h_{D(g)}` is
finite locally free of **one** rank `n`.

This is `AlgebraicGeometry.Space.exists_basicOpen_isFiniteLocallyFreeOfRank` with its
finite-local-freeness hypothesis discharged by
`AlgebraicGeometry.Space.isFiniteLocallyFree_sections_selfChart`, and it is the decomposition
clause the flatness clause of Stacks 0CZA needs of an affine test object: the rank it produces
is the single `s` that
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_forall_isAffine_of_isQuasicoherentOnSite`
and then `AlgebraicGeometry.Space.existsUnique_lift_fittingRankStratum_iff` consume. -/
theorem exists_basicOpen_isFiniteLocallyFreeOfRank_of_isFlatOver_id (W : BigFppfOver B S hS)
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W)) (H : Modules.{u, u} B S hS (yoneda.obj W) hW)
    (hHqc : H.IsQuasicoherentOnSite) (hHfp : SheafOfModules.IsFinitePresentationOnSite H)
    (hflat : IsFlatOver B S hS hW (𝟙 (yoneda.obj W)) H)
    (hWaff : IsAffine (chartScheme (selfChart B S hS W)))
    (z : (BigFppfOver.toScheme B S hS).obj W) :
    ∃ (g : chartRing B S hS (yoneda.obj W) hW (selfChart B S hS W)) (n : ℕ),
      z ∈ ((BigFppfOver.toScheme B S hS).obj W).basicOpen g ∧
      RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS
          (yoneda.obj (openSub W (((BigFppfOver.toScheme B S hS).obj W).basicOpen g)))
          (isAlgebraicSpace_yoneda B S hS
            (openSub W (((BigFppfOver.toScheme B S hS).obj W).basicOpen g))))
        ((modulePullback B S hS (schemeSpaceMap
          (openSubHom W (((BigFppfOver.toScheme B S hS).obj W).basicOpen g)))).obj H) n :=
  exists_basicOpen_isFiniteLocallyFreeOfRank B S hS W hW H hHqc hWaff
    (isFiniteLocallyFree_sections_selfChart B S hS W hW H hHqc hHfp hflat hWaff) z

end FromFlatness

end AlgebraicGeometry.Space

end

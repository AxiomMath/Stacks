module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.SiteContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent

/-!
# Restricting a sheaf of algebras on an algebraic space to an étale scheme chart

A sheaf of `𝒪_X`-algebras on an algebraic space `X` restricts, along the Zariski opens of an
étale scheme chart `V` of `X`, to a sheaf of `𝒪_V`-algebras on the chart's scheme. The
restriction of a quasi-coherent algebra is quasi-coherent, and under a cofinality hypothesis its
relative spectrum is an object of the ambient big fppf site.

## Main definitions

* `AlgebraicGeometry.Space.chartOpensPushforward`: restriction of sheaves of commutative rings
  along `AlgebraicGeometry.Space.chartOpens`.
* `AlgebraicGeometry.Space.chartStructureSheafIso`: the restriction of the structure sheaf of
  the algebraic space is the structure sheaf of the chart's scheme.
* `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartScheme`: the restriction of a sheaf of
  `𝒪_X`-algebras to an étale scheme chart of `X`, as a `Stacks.RelativeSpec.AlgebraSheaf`.
* `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeFunctor`: the restriction, as a
  functor.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartScheme_sections`: the sections of the
  restriction over a Zariski open of the chart are the sections of the algebra over that open
  read as an étale chart.
* `AlgebraicGeometry.Space.AlgebraSheaf.mk_sections_restrictToChartScheme_lt_cutoff`: sections
  below the cutoff at every étale chart give sections below the cutoff over every Zariski open of
  every chart.
* `AlgebraicGeometry.Space.AlgebraSheaf.exists_bound_restrictToChartScheme` and
  `AlgebraicGeometry.Space.AlgebraSheaf.exists_bound_restrictToChartScheme_of_mk_le_aleph0`: a
  uniform bound below the cutoff on the sections over the affine opens of a chart with few
  affine opens.
* `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_restrictToChartScheme` and
  `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_restrictToChartScheme`: the chart
  restriction of a quasi-coherent algebra sheaf is quasi-coherent.
* `AlgebraicGeometry.Space.contains_relativeSpec_restrictToChartScheme`: the relative spectrum
  of the chart restriction is an object of the ambient big fppf site.
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}

/-! ### Restriction of sheaves of rings along the Zariski opens of a chart -/

/-- Restriction of sheaves of commutative rings on the small étale site of `X` along
`AlgebraicGeometry.Space.chartOpens`, the inclusion of the Zariski opens of an étale scheme
chart. -/
def chartOpensPushforward (V : SmallEtale B S hS X.1) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥(chartScheme V)) CommRingCat.{u} :=
  letI := isContinuous_chartOpens B S hS X.1 X.2 V
  (chartOpens B S hS V).sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology ↥(chartScheme V)) (SmallEtale.topology B S hS X.1)

/-- The restriction of the structure sheaf of `X` to an étale scheme chart is the structure
sheaf of the chart's scheme, componentwise by `AlgebraicGeometry.Scheme.restrictFunctorΓ`. -/
def chartStructureSheafIso (V : SmallEtale B S hS X.1) :
    (chartOpensPushforward B S hS V).obj (structureSheaf B S hS X.1 X.2) ≅
      (chartScheme V).sheaf where
  hom := ⟨(Scheme.restrictFunctorΓ (X := chartScheme V)).hom⟩
  inv := ⟨(Scheme.restrictFunctorΓ (X := chartScheme V)).inv⟩
  hom_inv_id := Sheaf.hom_ext (Scheme.restrictFunctorΓ (X := chartScheme V)).hom_inv_id
  inv_hom_id := Sheaf.hom_ext (Scheme.restrictFunctorΓ (X := chartScheme V)).inv_hom_id

/-! ### Restriction of an algebra sheaf to an étale scheme chart -/

/-- The restriction of a sheaf of `𝒪_X`-algebras to an étale scheme chart of `X`: the
underlying sheaf of commutative rings is restricted along the Zariski opens of the chart, with
the restricted structure map read through `AlgebraicGeometry.Space.chartStructureSheafIso`. -/
def AlgebraSheaf.restrictToChartScheme (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) : Stacks.RelativeSpec.AlgebraSheaf (chartScheme V) :=
  Under.mk ((chartStructureSheafIso B S hS V).inv ≫ (chartOpensPushforward B S hS V).map A.hom)

/-- Restriction to an étale scheme chart, as a functor from the sheaves of `𝒪_X`-algebras to the
algebra sheaves on the chart's scheme. -/
def AlgebraSheaf.restrictToChartSchemeFunctor (V : SmallEtale B S hS X.1) :
    AlgebraSheaf.{u, u} B S hS X.1 X.2 ⥤ Stacks.RelativeSpec.AlgebraSheaf (chartScheme V) where
  obj A := A.restrictToChartScheme B S hS V
  map {A _} f := Under.homMk ((chartOpensPushforward B S hS V).map f.right)
    ((Category.assoc _ _ _).trans
      (congrArg (fun k => (chartStructureSheafIso B S hS V).inv ≫ k)
        (((chartOpensPushforward B S hS V).map_comp A.hom f.right).symm.trans
          (congrArg (chartOpensPushforward B S hS V).map
            (AlgebraSheaf.hom_comp_right f)))))
  map_id A := Under.UnderMorphism.ext
    (((chartOpensPushforward B S hS V).congr_map (AlgebraSheaf.id_right A)).trans
      ((chartOpensPushforward B S hS V).map_id A.right))
  map_comp f g := Under.UnderMorphism.ext
    (((chartOpensPushforward B S hS V).congr_map (AlgebraSheaf.comp_right f g)).trans
      ((chartOpensPushforward B S hS V).map_comp f.right g.right))

@[simp]
theorem AlgebraSheaf.restrictToChartSchemeFunctor_obj (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    (AlgebraSheaf.restrictToChartSchemeFunctor B S hS V).obj A =
      A.restrictToChartScheme B S hS V :=
  rfl

/-- The sections of the chart restriction of an algebra sheaf over a Zariski open of the chart
are the sections of the algebra over that open read as an étale chart of `X`. -/
theorem AlgebraSheaf.restrictToChartScheme_sections (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (W : (chartScheme V).Opens) :
    (A.restrictToChartScheme B S hS V).right.obj.obj (op W) =
      A.right.obj.obj (op ((chartOpens B S hS V).obj W)) :=
  rfl

/-! ### Quasi-coherence of the restriction -/

/-- The module underlying the chart restriction of an algebra sheaf is the chart restriction
of the module underlying the algebra sheaf, in the continuous-pushforward reading of the
latter. -/
theorem AlgebraSheaf.underlyingModule_restrictToChartScheme
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1) :
    (A.restrictToChartScheme B S hS V).underlyingModule =
      letI := isContinuous_chartOpens B S hS X.1 X.2 V
      (SheafOfModules.pushforward.{u} (chartRestrictionSheafHom B S hS X.2 V)).obj
        A.underlyingModule :=
  rfl

/-- The chart restriction of a quasi-coherent algebra sheaf is quasi-coherent. -/
theorem AlgebraSheaf.isQuasicoherent_restrictToChartScheme
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (hA : A.IsQuasicoherent)
    (V : SmallEtale B S hS X.1) :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (A.restrictToChartScheme B S hS V) :=
  let := isContinuous_chartOpens B S hS X.1 X.2 V
  (SheafOfModules.isQuasicoherent (chartScheme V).ringCatSheaf).prop_of_iso
    ((restrictToChartIsoRestrictToChartScheme B S hS X.2 A.underlyingModule V).symm ≪≫
      restrictToChartIsoPushforward B S hS X.2 V A.underlyingModule)
    (AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme B S hS X
      A.underlyingModule hA V)

instance AlgebraSheaf.instIsQuasicoherentRestrictToChartScheme
    (A : QuasicoherentAlgebra B S hS X) (V : SmallEtale B S hS X.1) :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (A.obj.restrictToChartScheme B S hS V) :=
  AlgebraSheaf.isQuasicoherent_restrictToChartScheme B S hS A.property V

/-! ### The size condition on the chart -/

/-- If an algebra sheaf has fewer than `B.cutoff` sections at every étale chart of `X`, then its
restriction to an étale scheme chart has fewer than `B.cutoff` sections over every Zariski open
of that chart. -/
theorem AlgebraSheaf.mk_sections_restrictToChartScheme_lt_cutoff
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A)
    (V : SmallEtale B S hS X.1) (W : (chartScheme V).Opens) :
    #((A.restrictToChartScheme B S hS V).right.obj.obj (op W)) < B.cutoff :=
  hA ((chartOpens B S hS V).obj W)

/-- If the affine opens of the chart's scheme number fewer than the cofinality of the cutoff,
the sections of the chart restriction over its affine opens are uniformly bounded below the
cutoff. -/
theorem AlgebraSheaf.exists_bound_restrictToChartScheme
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A)
    (V : SmallEtale B S hS X.1)
    (hV : #(chartScheme V).affineOpens < B.cutoff.ord.cof) :
    ∃ μ < B.cutoff, ∀ W : (chartScheme V).affineOpens,
      #((A.restrictToChartScheme B S hS V).right.obj.obj
        (op (W : (chartScheme V).Opens))) ≤ μ :=
  ⟨⨆ W : (chartScheme V).affineOpens,
      #((A.restrictToChartScheme B S hS V).right.obj.obj (op (W : (chartScheme V).Opens))),
    iSup_lt_of_lt_cof_ord hV
      (fun _ => AlgebraSheaf.mk_sections_restrictToChartScheme_lt_cutoff B S hS hA V _),
    fun W => le_ciSup Cardinal.bddAbove_of_small W⟩

/-- If the chart's scheme has at most countably many affine opens, the sections of the chart
restriction over its affine opens are uniformly bounded below the cutoff. -/
theorem AlgebraSheaf.exists_bound_restrictToChartScheme_of_mk_le_aleph0
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A)
    (V : SmallEtale B S hS X.1) (hV : #(chartScheme V).affineOpens ≤ ℵ₀) :
    ∃ μ < B.cutoff, ∀ W : (chartScheme V).affineOpens,
      #((A.restrictToChartScheme B S hS V).right.obj.obj
        (op (W : (chartScheme V).Opens))) ≤ μ :=
  AlgebraSheaf.exists_bound_restrictToChartScheme B S hS hA V
    (hV.trans_lt B.aleph0_lt_cutoff_cof)

/-! ### The relative spectrum of the chart restriction lies in the site -/

/-- The relative spectrum of the chart restriction of a quasi-coherent `𝒪_X`-algebra is an
object of the ambient big fppf site, provided the affine opens of the chart's scheme number fewer
than the cofinality of the cutoff. -/
theorem contains_relativeSpec_restrictToChartScheme
    (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)
    (V : SmallEtale B S hS X.1)
    (hV : #(chartScheme V).affineOpens < B.cutoff.ord.cof) :
    B.Contains (Stacks.AffineAlgebraEquivalence.relativeSpec
      (A.obj.restrictToChartScheme B S hS V)) := by
  obtain ⟨μ, hμ, hbound⟩ := AlgebraSheaf.exists_bound_restrictToChartScheme B S hS hA V hV
  exact B.contains_relativeSpec (A.obj.restrictToChartScheme B S hS V)
    V.obj.left.left.property hμ hbound

end AlgebraicGeometry.Space

end

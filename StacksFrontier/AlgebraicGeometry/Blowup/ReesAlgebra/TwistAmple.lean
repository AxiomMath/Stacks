module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.ProjHeightOne
public import StacksFrontier.AlgebraicGeometry.ProjAmple.DegreeOneCover
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwist

/-!
# The twisting sheaf of a blowup is invertible and relatively ample

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, and let `b : X' ⟶ X` be the
blowup of `X` in `ℐ`, that is, the relative `Proj` of the Rees algebra `⨁_{n ≥ 0} ℐⁿ`. The
twisting sheaf `𝒪_{X'}(n)` is glued from the absolute twisting sheaves `𝒪(n)` of the charts
`Proj (⨁_n ℐⁿ(V))` over the affine opens `V` of `X`. This file proves that `𝒪_{X'}(n)` is
invertible, and that `𝒪_{X'}(1)` is ample relative to `b` when `ℐ` is of finite type.

Over an affine open `V` of the base the chart is the whole of `b⁻¹(V)`, and the Rees algebra is
generated in degree one there, so `𝒪(1)` on the chart is trivialized on the standard opens of the
degree-one sections, which cover it. That gives invertibility at once, and ampleness on the chart
because those standard opens are affine; the chart is quasi-compact because `ℐ(V)` is finitely
generated. Relative ampleness is exactly ampleness on each `b⁻¹(V)`, so nothing else is needed.

## Main results

* `Stacks.RelativeProj.Situation.relativeProjToBase_preimage_eq_opensRange`: the part of a
  relative `Proj` lying over an affine open of the base is the range of the chart there.
* `AlgebraicGeometry.isInvertibleModule_twistingSheaf_reesSituation` and
  `AlgebraicGeometry.isAmple_twistingSheaf_reesSituation`: on the blowup chart over an affine
  open, `𝒪(n)` is invertible and `𝒪(1)` is ample.
* `AlgebraicGeometry.isInvertibleModule_twist_reesSituation`: **`𝒪_{X'}(n)` is invertible**, for
  every `n` and with no finiteness hypothesis on `ℐ`.
* `AlgebraicGeometry.isRelativelyAmple_twist_reesSituation`: **`𝒪_{X'}(1)` is a `b`-relatively
  ample invertible sheaf** when `ℐ` is of finite type. This is part (2) of Stacks tag 02NS.

## The carried hypothesis

The twisting sheaves of a relative `Proj` are glued from the chart twists along the comparison
isomorphisms of Stacks tag 01NO, clauses (3) and (4). Those comparisons are not constructed in
this repository; `Stacks.RelativeProj.Situation.TwistTransition`, the structure carrying exactly
them, is what `Stacks.RelativeProj.Situation.twist` is already stated over, and the two results
about `𝒪_{X'}(n)` below carry a term `t` of it as a hypothesis. Supplying it once tag 01NO is
available is a substitution: no statement below says anything about `t` beyond its existence, and
the twist is pinned by `Stacks.RelativeProj.Situation.twistChartIso`, which says it restricts to
the absolute `𝒪(n)` on every chart.

Nothing of tag 02NS's own content is assumed: neither projectivity, nor ampleness, nor
invertibility of the twist is a hypothesis anywhere below.

## Not done here

Part (1) of tag 02NS — that `b` is a projective morphism — is not here. It asks for a closed
immersion of `X'` into the projective bundle `𝐏(ℐ)` over `X`, which needs the surjection
`Sym_{𝒪_X}(ℐ) ↠ ⨁_n ℐⁿ` of graded `𝒪_X`-algebras. Properness of `b`, which is weaker, is
`AlgebraicGeometry.isProper_blowUpToBase_of_fg`.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry

universe u

namespace Stacks.RelativeProj.Situation

/-- **The part of a relative `Proj` lying over an affine open of the base is the chart there.**
This is the cartesian chart square of Stacks tag 01NQ read as an equality of opens of the
relative `Proj`. -/
public theorem relativeProjToBase_preimage_eq_opensRange (s : Situation.{u})
    (W : s.base.affineOpens) :
    relativeProjToBase s ⁻¹ᵁ W.1 = (relativeProjChart s W).opensRange :=
  (chartData s).toBase_preimage_coe W

end Stacks.RelativeProj.Situation

namespace AlgebraicGeometry

open Stacks.RelativeProj

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The twisting sheaves of a blowup chart are invertible.** The Rees algebra is generated in
degree one over an affine open of the base, so on the chart there every `𝒪(n)` is trivialized by
the ratios of degree-one sections, whose standard opens cover the chart. -/
public instance isInvertibleModule_twistingSheaf_reesSituation (W : X.affineOpens) (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (Proj ((reesSituation I).sectionRingGrading W.1))
      (ProjectiveSpectrum.Proj.twistingSheaf ((reesSituation I).sectionRingGrading W.1) n) :=
  TwistMapsInvertible.isInvertibleModule_twistingSheaf_of_adjoin _
    (Situation.adjoin_sectionRingGrading_one_eq_top_of_isGeneratedInDegreeOne
      (reesSituation I) W.1 (reesSituation_isGeneratedInDegreeOne I W)) n

/-- **`𝒪(1)` is ample on a blowup chart over an affine open on which the ideal is finitely
generated.** The chart is quasi-compact, and a degree-one section nonvanishing at a given point
has an affine standard open as its nonvanishing locus. -/
public theorem isAmple_twistingSheaf_reesSituation (W : X.affineOpens) (hfg : (I.ideal W).FG) :
    Stacks.Ample.IsAmple (Proj ((reesSituation I).sectionRingGrading W.1))
      (ProjectiveSpectrum.Proj.twistingSheaf ((reesSituation I).sectionRingGrading W.1) 1) := by
  have hgen := Situation.adjoin_sectionRingGrading_one_eq_top_of_isGeneratedInDegreeOne
    (reesSituation I) W.1 (reesSituation_isGeneratedInDegreeOne I W)
  refine (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (Stacks.ProjDegreeOneCover.isAmple_twistingModule_one _
      (Stacks.Blowup.compactSpace_proj_reesSectionRingGrading hfg) fun x => ?_)
  exact ProjectiveSpectrum.Proj.exists_mem_degreeOne_notMem _ hgen
    (p := x.asHomogeneousIdeal.toIdeal) x.not_irrelevant_le

/-- **The twisting sheaf `𝒪_{X'}(n)` of a blowup is invertible.** It restricts on the chart over
an affine open of the base to the absolute `𝒪(n)` there, which is invertible, and the charts
cover the blowup. -/
public instance isInvertibleModule_twist_reesSituation {n : ℤ}
    (t : (reesSituation I).TwistTransition n) :
    Stacks.Ample.IsInvertibleModule (blowUp I) (Situation.twist t) := by
  refine TwistMapsInvertible.isInvertibleModule_of_forall_exists_isoUnit_openImmersion _
    fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := (Situation.relativeProjToBase (reesSituation I)).base x) (U := ⊤) trivial
  set W : X.affineOpens := ⟨V, hV⟩ with hW
  have hmem : x ∈ (Situation.relativeProjChart (reesSituation I) W).opensRange := by
    rw [← Situation.relativeProjToBase_preimage_eq_opensRange (reesSituation I) W]
    exact hxV
  obtain ⟨y, hy⟩ := hmem
  have hgen := Situation.adjoin_sectionRingGrading_one_eq_top_of_isGeneratedInDegreeOne
    (reesSituation I) V (reesSituation_isGeneratedInDegreeOne I W)
  obtain ⟨U, hyU, ⟨eU⟩⟩ := TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin
    ((reesSituation I).sectionRingGrading V) hgen n y
  refine ⟨U.toScheme, U.ι ≫ Situation.relativeProjChart (reesSituation I) W,
    inferInstance, ⟨⟨y, hyU⟩, hy⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorComp U.ι
      (Situation.relativeProjChart (reesSituation I) W)).app (Situation.twist t) ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (Situation.twistChartIso t W) ≪≫ eU

/-- **Stacks Project, Tag 02NS, part (2).** The twisting sheaf `𝒪_{X'}(1)` of the blowup of a
scheme in a quasi-coherent sheaf of ideals of finite type is a relatively ample invertible sheaf
for the blowup morphism: over an affine open `V` of the base the blowup is the `Proj` of the Rees
algebra of `ℐ(V)`, the twist restricts there to the absolute `𝒪(1)`, and that is ample. -/
@[stacks 02NS "part (2): `𝒪_{X'}(1)` is a `b`-relatively ample invertible sheaf, for the twist \
glued from the chart twists along a transition datum for Tag 01NO (3) and (4), which is carried \
as the hypothesis `Stacks.RelativeProj.Situation.TwistTransition`"]
public theorem isRelativelyAmple_twist_reesSituation (hI : I.IsFiniteType)
    (t : (reesSituation I).TwistTransition 1) :
    Stacks.RelativeAmple.IsRelativelyAmple (blowUpToBase I) (Situation.twist t) := by
  refine ⟨Stacks.Blowup.quasiCompact_blowUpToBase hI, fun V hV => ?_⟩
  set W : X.affineOpens := ⟨V, hV⟩ with hW
  set c := Situation.relativeProjChart (reesSituation I) W with hc
  have hrange : Set.range c.base = Set.range (blowUpToBase I ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι, hc]
    exact congrArg (fun U : (blowUp I).Opens => (U : Set (blowUp I)))
      (Situation.relativeProjToBase_preimage_eq_opensRange (reesSituation I) W).symm
  set φ := IsOpenImmersion.isoOfRangeEq c (blowUpToBase I ⁻¹ᵁ V).ι hrange with hφ
  have hfac : φ.hom ≫ (blowUpToBase I ⁻¹ᵁ V).ι = c :=
    IsOpenImmersion.isoOfRangeEq_hom_fac c (blowUpToBase I ⁻¹ᵁ V).ι hrange
  have hfac' : φ.inv ≫ c = (blowUpToBase I ⁻¹ᵁ V).ι := (Iso.inv_comp_eq φ).mpr hfac.symm
  have hinvC : Stacks.Ample.IsInvertibleModule
      (Proj ((reesSituation I).sectionRingGrading W.1))
      (ProjectiveSpectrum.Proj.twistingSheaf ((reesSituation I).sectionRingGrading W.1) 1) :=
    isInvertibleModule_twistingSheaf_reesSituation I W 1
  have hinvP : Stacks.Ample.IsInvertibleModule (blowUpToBase I ⁻¹ᵁ V).toScheme
      ((Scheme.Modules.pullback φ.inv).obj
        (ProjectiveSpectrum.Proj.twistingSheaf ((reesSituation I).sectionRingGrading W.1) 1)) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback φ.inv.toLRSHom.toShHom _
  have hinvQ : Stacks.Ample.IsInvertibleModule (blowUpToBase I ⁻¹ᵁ V).toScheme
      ((Scheme.Modules.pullback (blowUpToBase I ⁻¹ᵁ V).ι).obj (Situation.twist t)) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      (blowUpToBase I ⁻¹ᵁ V).ι.toLRSHom.toShHom _
  have hA := Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion φ.inv
    (ProjectiveSpectrum.Proj.twistingSheaf ((reesSituation I).sectionRingGrading W.1) 1)
    (isAmple_twistingSheaf_reesSituation I W (hI W))
  have e₁ : (Scheme.Modules.pullback c).obj (Situation.twist t) ≅
      ProjectiveSpectrum.Proj.twistingSheaf ((reesSituation I).sectionRingGrading W.1) 1 :=
    ((Scheme.Modules.restrictFunctorIsoPullback c).app (Situation.twist t)).symm ≪≫
      Situation.twistChartIso t W
  have e := (Scheme.Modules.pullback φ.inv).mapIso e₁.symm ≪≫
    (Scheme.Modules.pullbackComp φ.inv c).app (Situation.twist t) ≪≫
    (Scheme.Modules.pullbackCongr hfac').app (Situation.twist t)
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp hA

end AlgebraicGeometry

end

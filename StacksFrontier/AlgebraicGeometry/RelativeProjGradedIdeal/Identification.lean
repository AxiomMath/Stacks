module

public import StacksFrontier.AlgebraicGeometry.ProjQuotientFiniteCover.UniformDegree
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ChartComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0801: a closed subscheme of a relative Proj is the relative Proj of a quotient

Work in Situation 01NN: a scheme `S`, a quasi-coherent graded `𝒪_S`-algebra `𝒜` in the
sheaf-level form `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, twists `D` on
`Proj_S(𝒜)`, and a closed immersion `i : Z ⟶ Proj_S(𝒜)` whose structure morphism
`p : Proj_S(𝒜) ⟶ S` is quasi-compact. `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal`
`.twistKerGradedIdeal` is Tag 0801's graded ideal

    ℐ_d = ker (𝒜_d ⟶ p_*((i_*𝒪_Z)(d))).

**This file identifies `Z` with `Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)`, which is Stacks Tag 0801.**

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.ker_eq_ker_projQuotientHom_of_ker_chart`:
  **the gluing step, for an arbitrary graded ideal with quasi-coherent pieces.** A chartwise
  equality of the two kernel ideal sheaves glues to an equality on `Proj_S(𝒜)`. The ideal is a
  parameter, so this serves both Tag 0801's saturated ideal and the ideal generated in a single
  degree that Tags 0802 and 0803 produce; its chartwise step is
  `ideal_ker_chartStandardOpen_eq_of_ker_chart` and the normal form of the chart map it uses is
  `chartMap_eq_comp_projMap_quotientMk`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.ker_chartRestrict_eq_ker_chartMap`: over an
  affine open of the base, `Z` and `Proj_S(𝒜/ℐ)` cut out the same ideal sheaf of the chart
  `Proj Γ(U, 𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.ker_eq_ker_projQuotientHom_twistKer`: they
  cut out the same ideal sheaf of `Proj_S(𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer`: **Stacks
  Tag 0801**, as the isomorphism `Z ≅ Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)`, and
  `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.gradedQuotientPresentation_twistKer`, the
  same packaged as a
  `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedQuotientPresentation`.

## The three steps, and what each needed

The `Not done here` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistRestriction.lean` lists three
things needed between the chart comparison `sectionIdeal_eq_idealOfClosedSubscheme` and the
equality of ideal sheaves that
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_iff_ker_eq` consumes.

* **The absolute identification chain was stated at the wrong kind of grading.**
  `Stacks.ProjQuotientFiniteCover.ker_eq_ker_ambientHom_of_cover` lives under
  `{R S} [Algebra R S] (𝒮 : ℕ → Submodule R S) [GradedAlgebra 𝒮]`, and a chart of a relative Proj
  carries `…RelativeProjBridge.SheafGradedAlgebra.grading`, an `AddSubgroup`-valued `GradedRing`.
  The restatement is `Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover` of
  `StacksFrontier/AlgebraicGeometry/ProjQuotientFiniteCover/GradedRing.lean`. The `GradedAlgebra`
  hypothesis buys exactly one thing,
  `Stacks.ProjQuotientChartIdeal.ambientHom_eq_projMap`, which identifies the glued
  `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` with Mathlib's `AlgebraicGeometry.Proj.map`,
  so stating the conclusion at `Proj.map` of `Stacks.HomogeneousIdeal.quotientMk` deletes it.

* **A chart cover of a single degree.** A finite cover of the chart by
  standard opens of *degree-one* elements would need `𝒜` generated in degree one — a
  hypothesis Tag 0801 does not make. What is used instead is
  `Stacks.ProjQuotientFiniteCover.exists_finite_uniform_degree_cover`: a quasi-compact `Proj 𝒮`
  is covered by the standard opens of finitely many homogeneous elements of **one** positive
  degree `d`, obtained from `AlgebraicGeometry.Proj.compactSpace_iff` by raising each element to
  the power that makes its degree the product of all the degrees, which changes no standard open
  (`AlgebraicGeometry.Proj.basicOpen_pow`). That is the device of the source's own proof, which
  takes `f_0, …, f_n ∈ A_+` and passes to `d = lcm (deg f_i)`; the whole absolute chart
  comparison is redone at that degree in
  `StacksFrontier/AlgebraicGeometry/ProjSaturation/UniformDegree.lean` and
  `StacksFrontier/AlgebraicGeometry/ProjQuotientFiniteCover/UniformDegree.lean`. Quasi-compactness
  of the chart is `compactSpace_proj_grading`, which is quasi-compactness of `p`, i.e. Tag 0801's
  own hypothesis.

* **The glue from chartwise kernels to the ideal sheaf.** Although nothing computes
  `(I.comap W.ι).ideal` from `I.ideal` directly, the `comap` route is not blocked and no
  ring-level detour through `AlgebraicGeometry.morphismRestrict_app` is needed:
  `AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` is in Mathlib and
  computes exactly the comparison wanted — for a cartesian square whose vertical maps are open
  immersions, the ideal of `f'.ker` at an affine open `W` of the chart is the ideal of `f.ker` at
  `iV ''ᵁ W`, pulled back along the isomorphism `iV.appIso W`. Applied to `i` and to
  `projQuotientHom` over one chart and cancelled with `Ideal.comap_injective_of_surjective`, it
  turns the chartwise equality of kernel ideal sheaves into an equality of ideals at
  `chart ''ᵁ D₊(f)`, which `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top` glues.

## Implementation notes

The two cartesian squares are supplied, not built: for `projQuotientHom` it is
`Stacks.AlgebraicGeometry.ProjBundleSurjection.isPullback_chart`, flipped, and for `i` it is
`AlgebraicGeometry.IsOpenImmersion.isPullback` applied to
`Stacks.AlgebraicGeometry.ChartBaseChange.chartRestrict_comp`, whose range hypothesis is
`AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`.

The index of the affine open cover is `Σ U : AffineOpen S, ι U`, over the subtype
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen` rather than
`AlgebraicGeometry.Scheme.affineOpens`, because the chart's `IsOpenImmersion` argument is
computed from the affineness proof; that file's implementation notes record the rewrite failures
the `Set` spelling causes. Both the degree `d` and the index type of the chart cover depend on
the affine open of the base, and are extracted by `choose`; no uniformity across the base is
needed, since each chart is compared separately.

`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionIdeal` is fed to the absolute statement
as an arbitrary homogeneous ideal together with the chart comparison
`sectionIdeal_eq_idealOfClosedSubscheme`, rather than the absolute statement being instantiated
at the ideal of equations: the two ideals are equal only propositionally, and rewriting the ideal
inside the type `Proj (quotientGrading I)` is not type-correct.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ChartBaseChange
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.HomogeneousIdeal

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S)

/-! ### The standard opens of the charts -/

/-- The affine open `chart(U) ''ᵁ D₊(x)` of `Proj_S(𝒜)`, for `U` an affine open of the base and
`x` a homogeneous section of positive degree over it. It is affine because `D₊(x)` is
(`AlgebraicGeometry.Proj.isAffineOpen_basicOpen`) and the chart is an open immersion. -/
@[sga "6 VI 2.3.2" "each D_+(U"]
def chartStandardOpen (U : AffineOpen S) {d : ℕ} (hd : 0 < d) {x : 𝒜.sectionRing U.1}
    (hx : x ∈ 𝒜.grading U.1 d) : (relativeProj 𝒜).scheme.affineOpens :=
  ⟨(relativeProj 𝒜).chart U.1 U.2 ''ᵁ AlgebraicGeometry.Proj.basicOpen (𝒜.grading U.1) x,
    (AlgebraicGeometry.Proj.isAffineOpen_basicOpen (𝒜.grading U.1) x hx
      hd).image_of_isOpenImmersion _⟩

/-! ### Gluing a chartwise identification, for an arbitrary graded ideal -/

section Generic

variable {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme) (ℐ : QcohGradedIdeal 𝒜)

/-- **The chart map of `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` is Mathlib's `AlgebraicGeometry.Proj.map` of a
graded quotient map, after an isomorphism of the source.** The isomorphism identifies the chart
`Proj Γ(U, 𝒜/ℐ)` of the quotient with `Proj` of the quotient of `Γ(U, 𝒜)` by the homogeneous
ideal `sectionIdeal 𝒜 ℐ U`; it is invisible to `AlgebraicGeometry.Scheme.Hom.ker`, which is what
makes this the useful shape. -/
theorem chartMap_eq_comp_projMap_quotientMk (U : S.Opens) (hU : IsAffineOpen U) :
    ProjBundleSurjection.chartMap (surjectiveOnAffineSections_quotHom 𝒜 ℐ) U hU =
      (chartIsoProjSectionQuotient 𝒜 ℐ U hU).hom ≫
        AlgebraicGeometry.Proj.map (quotientMk (sectionIdeal 𝒜 ℐ U))
          (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
            (surjective_quotientMk (sectionIdeal 𝒜 ℐ U))) := by
  rw [chartMap_eq_comp_mapHomOfTop_quotientMk 𝒜 ℐ U hU,
    RelativeProj.mapHomOfTop_eq_map _ _ _
      (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
        (surjective_quotientMk (sectionIdeal 𝒜 ℐ U))) _]

/-- **The ideals of the two kernel ideal sheaves agree at a standard open of a chart**, given that
they agree on the chart. Both are computed by
`AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` as the ideal of the
corresponding chartwise kernel pulled back along the isomorphism of sections
`chart(U).appIso D₊(x)`. -/
theorem ideal_ker_chartStandardOpen_eq_of_ker_chart [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] (U : AffineOpen S) {d : ℕ} (hd : 0 < d)
    {x : 𝒜.sectionRing U.1} (hx : x ∈ 𝒜.grading U.1 d)
    (H : (chartRestrict ((relativeProj 𝒜).chart U.1 U.2) i).ker =
      (ProjBundleSurjection.chartMap (surjectiveOnAffineSections_quotHom 𝒜 ℐ) U.1 U.2).ker) :
    (Scheme.Hom.ker i).ideal (chartStandardOpen 𝒜 U hd hx) =
      (Scheme.Hom.ker (projQuotientHom 𝒜 ℐ)).ideal (chartStandardOpen 𝒜 U hd hx) := by
  have : IsClosedImmersion (projQuotientHom 𝒜 ℐ) := isClosedImmersion_projQuotientHom 𝒜 ℐ
  let W : (AlgebraicGeometry.Proj (𝒜.grading U.1)).affineOpens :=
    ⟨AlgebraicGeometry.Proj.basicOpen (𝒜.grading U.1) x,
      AlgebraicGeometry.Proj.isAffineOpen_basicOpen (𝒜.grading U.1) x hx hd⟩
  refine Ideal.comap_injective_of_surjective
    (((relativeProj 𝒜).chart U.1 U.2).appIso W).inv.hom
    (ConcreteCategory.bijective_of_isIso _).2 ?_
  exact (AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i
      (chartRestrict ((relativeProj 𝒜).chart U.1 U.2) i)
      ((i ⁻¹ᵁ ((relativeProj 𝒜).chart U.1 U.2 ''ᵁ
        (⊤ : (AlgebraicGeometry.Proj (𝒜.grading U.1)).Opens))).ι)
      ((relativeProj 𝒜).chart U.1 U.2)
      (AlgebraicGeometry.IsOpenImmersion.isPullback _ _ _ _
        (chartRestrict_comp ((relativeProj 𝒜).chart U.1 U.2) i).symm
        (by rw [Scheme.Opens.opensRange_ι, Scheme.Hom.image_top_eq_opensRange])) W).symm.trans
    ((congrArg (·.ideal W) H).trans
      (AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
        (projQuotientHom 𝒜 ℐ)
        (ProjBundleSurjection.chartMap (surjectiveOnAffineSections_quotHom 𝒜 ℐ) U.1 U.2)
        ((relativeProj (quotAlgebra 𝒜 ℐ)).chart U.1 U.2)
        ((relativeProj 𝒜).chart U.1 U.2)
        (ProjBundleSurjection.isPullback_chart
          (surjectiveOnAffineSections_quotHom 𝒜 ℐ) U.1 U.2).flip W))

/-- **`Z` and `Proj_S(𝒜/ℐ)` cut out the same ideal sheaf of `Proj_S(𝒜)` as soon as they do so on
the charts of a family of affine opens of the base whose preimages cover.**

Every chart of `Proj_S(𝒜)` is quasi-compact, so it has a finite cover by standard opens of
homogeneous sections of one positive degree
(`Stacks.ProjQuotientFiniteCover.exists_finite_uniform_degree_cover`); those standard opens,
pushed forward along the charts of the given family, are an affine open cover of `Proj_S(𝒜)`, and
on each of them the two ideals agree by `ideal_ker_chartStandardOpen_eq_of_ker_chart`.

The family is a parameter rather than all affine opens of the base because the cutting-out data
of Tag 0802 names its own affine cover and no other. -/
theorem ker_eq_ker_projQuotientHom_of_ker_chart_cover [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] {ι : Type*} (V : ι → AffineOpen S)
    (hV : (⨆ k, (relativeProj 𝒜).toBase ⁻¹ᵁ (V k).1) = ⊤)
    (H : ∀ k, (chartRestrict ((relativeProj 𝒜).chart (V k).1 (V k).2) i).ker =
      (ProjBundleSurjection.chartMap (surjectiveOnAffineSections_quotHom 𝒜 ℐ)
        (V k).1 (V k).2).ker) :
    i.ker = (projQuotientHom 𝒜 ℐ).ker := by
  classical
  have hcover : ∀ U : AffineOpen S, ∃ (d : ℕ) (_ : 0 < d) (κ : Type u) (_ : Fintype κ)
      (g : κ → 𝒜.sectionRing U.1), (∀ j, g j ∈ 𝒜.grading U.1 d) ∧
        (⨆ j, AlgebraicGeometry.Proj.basicOpen (𝒜.grading U.1) (g j)) = ⊤ := by
    intro U
    have := compactSpace_proj_grading 𝒜 U.1 U.2
    exact Stacks.ProjQuotientFiniteCover.exists_finite_uniform_degree_cover (𝒜.grading U.1)
  choose dd hdd idx hfin gg hgg hcovv using hcover
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun k : Σ k : ι, idx (V k) =>
      chartStandardOpen 𝒜 (V k.1) (hdd (V k.1)) (hgg (V k.1) k.2)) ?_
    (fun k => ideal_ker_chartStandardOpen_eq_of_ker_chart 𝒜 i ℐ (V k.1) (hdd (V k.1))
      (hgg (V k.1) k.2) (H k.1))
  refine top_unique fun z _ => ?_
  obtain ⟨k, hkz⟩ := TopologicalSpace.Opens.mem_iSup.mp (hV.ge (Set.mem_univ z))
  rw [← chart_image_top (relativeProj 𝒜) (V k).1 (V k).2] at hkz
  obtain ⟨y, -, hy⟩ := hkz
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp ((hcovv (V k)).ge (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, j⟩, ⟨y, hj, hy⟩⟩

/-- **`Z` and `Proj_S(𝒜/ℐ)` cut out the same ideal sheaf of `Proj_S(𝒜)` as soon as they do so on
every chart**: `ker_eq_ker_projQuotientHom_of_ker_chart_cover` at the family of all affine opens
of the base, whose preimages cover by
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.iSup_toBase_preimage_eq_top'`. -/
theorem ker_eq_ker_projQuotientHom_of_ker_chart [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase]
    (H : ∀ (U : S.Opens) (hU : IsAffineOpen U),
      (chartRestrict ((relativeProj 𝒜).chart U hU) i).ker =
        (ProjBundleSurjection.chartMap (surjectiveOnAffineSections_quotHom 𝒜 ℐ) U hU).ker) :
    i.ker = (projQuotientHom 𝒜 ℐ).ker :=
  ker_eq_ker_projQuotientHom_of_ker_chart_cover 𝒜 i ℐ (fun U : AffineOpen S => U)
    (iSup_toBase_preimage_eq_top' 𝒜 (relativeProj 𝒜)) fun U => H U.1 U.2

end Generic

/-! ### The chart form of the identification -/

variable (D : TwistData 𝒜) {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)

/-- **The chart form of Stacks Tag 0801.** Over an affine open `U` of the base, the closed
subscheme `Z` cuts out of the chart `Proj Γ(U, 𝒜)` and the chart map of `Proj_S(𝒜/ℐ)` have the
same kernel ideal sheaf.

This is `Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover_uniform` at the
graded ring `𝒜.grading U`, whose only hypothesis is quasi-compactness of the chart — which is
`compactSpace_proj_grading`, i.e. quasi-compactness of `p` — with the homogeneous ideal
`sectionIdeal 𝒜 ℐ U` and the chart comparison `sectionIdeal_eq_idealOfClosedSubscheme`. The chart
map is put into the shape `Proj.map` of a quotient by `chartMap_eq_comp_mapHomOfTop_quotientMk`
and `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`, the leading isomorphism being
invisible to `AlgebraicGeometry.Scheme.Hom.ker`. -/
@[ega "II 3.6.2" "(ii), special case"]
theorem ker_chartRestrict_eq_ker_chartMap [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] (U : S.Opens) (hU : IsAffineOpen U) :
    (chartRestrict ((relativeProj 𝒜).chart U hU) i).ker =
      (ProjBundleSurjection.chartMap
        (surjectiveOnAffineSections_quotHom 𝒜 (twistKerGradedIdeal 𝒜 D i)) U hU).ker := by
  have := compactSpace_proj_grading 𝒜 U hU
  rw [chartMap_eq_comp_projMap_quotientMk 𝒜 (twistKerGradedIdeal 𝒜 D i) U hU,
    Scheme.Hom.ker_comp_of_isIso]
  exact Stacks.ProjQuotientFiniteCover.ker_eq_ker_projMap_quotientMk_of_cover_uniform
    (𝒜.grading U) (chartRestrict ((relativeProj 𝒜).chart U hU) i)
    (sectionIdeal 𝒜 (twistKerGradedIdeal 𝒜 D i) U)
    (sectionIdeal_eq_idealOfClosedSubscheme 𝒜 D i U hU) _

/-! ### Tag 0801 -/

/-- **`Z` and `Proj_S(𝒜/ℐ)` cut out the same ideal sheaf of `Proj_S(𝒜)`**, for `ℐ` Stacks Tag
0801's graded ideal.

This is `ker_eq_ker_projQuotientHom_of_ker_chart` fed the chart comparison
`ker_chartRestrict_eq_ker_chartMap`. -/
theorem ker_eq_ker_projQuotientHom_twistKer [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] :
    i.ker = (projQuotientHom 𝒜 (twistKerGradedIdeal 𝒜 D i)).ker :=
  ker_eq_ker_projQuotientHom_of_ker_chart 𝒜 i (twistKerGradedIdeal 𝒜 D i)
    (ker_chartRestrict_eq_ker_chartMap 𝒜 D i)

/-- **Stacks Tag 0801.** Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra,
`p : X = Proj_S(𝒜) ⟶ S` the relative homogeneous spectrum and `i : Z ⟶ X` a closed subscheme.
Let `ℐ ⊆ 𝒜` be the kernel of the canonical map `𝒜 ⟶ ⨁_{d ≥ 0} p_*((i_*𝒪_Z)(d))`. If `p` is
quasi-compact then `Z = Proj_S(𝒜/ℐ)`.

The ideal is `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal`, the
degreewise kernel of the homogeneous-section map of Tag 01NR followed by the unit of the
pullback–pushforward adjunction at `i`; the quotient is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra` and the closed immersion
`Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` is `projQuotientHom`. The equality `Z = Proj_S(𝒜/ℐ)` of the source is
read, as everywhere in this repository, as an isomorphism over the ambient relative Proj.

The proof is `ker_eq_ker_projQuotientHom_twistKer` fed to `exists_iso_projQuotient_of_ker_eq`,
which produces the isomorphism from the equality of ideal sheaves by
`AlgebraicGeometry.IsClosedImmersion.lift` and `isIso_lift`. -/
@[stacks 0801, ega "II 2.9.2" "more general", ega "II 3.6.2" "more general"]
theorem exists_iso_projQuotient_twistKer [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] :
    ∃ e : Z ≅ (relativeProj (quotAlgebra 𝒜 (twistKerGradedIdeal 𝒜 D i))).scheme,
      e.hom ≫ projQuotientHom 𝒜 (twistKerGradedIdeal 𝒜 D i) = i :=
  exists_iso_projQuotient_of_ker_eq 𝒜 (twistKerGradedIdeal 𝒜 D i) i
    (ker_eq_ker_projQuotientHom_twistKer 𝒜 D i)

/-- **Stacks Tag 0801's conclusion-as-data**: the quotient algebra, the quotient homomorphism,
its surjectivity on the sections over the affine opens of the base, and the identification of `Z`
with `Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)`.

No `@[stacks 0801]` attribute here: the tag's statement is the identification, which
`exists_iso_projQuotient_twistKer` above carries, and this is that identification bundled with
the quotient data rather than a second statement of the tag. -/
def gradedQuotientPresentation_twistKer [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] :
    GradedQuotientPresentation 𝒜 i :=
  gradedQuotientPresentationOfKerEq 𝒜 (twistKerGradedIdeal 𝒜 D i) i
    (ker_eq_ker_projQuotientHom_twistKer 𝒜 D i)

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end

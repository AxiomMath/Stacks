module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionRepresentable

/-!
# Residue (iii) of Tag 01NY: the `U_d` are opens of the relative Proj covering it

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN). The proof of
Tag 01NY runs over a scheme `X` carrying opens `U_d`, one for each `d ≥ 1`, such that `U_d`
represents the functor `F_d` of Section 01NS — that is residue (i), Tag 01NU — and such that the
`U_d` cover `X` and are nested along divisibility, `U_d ⊆ U_e` whenever `d ∣ e` — that is
residue (iii).

This file **proves residue (iii)**, for `X` an arbitrary
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData` — hence in particular for the
constructed relative homogeneous spectrum `Proj_S(A)` of Tag 01NQ. The opens are not assumed: the
open `U_d ⊆ X` is *constructed*, as the union over the affine opens `U` of `S` of the images under
the chart `Proj Γ(U, A) ⟶ X` of the absolute degree-`d` opens
`AlgebraicGeometry.Proj.degreeOpen (A.grading U) d` of Equation 27.12.0.1.

Everything the absolute construction proves about those opens transfers along the charts, which
are open immersions (`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart`)
whose images are the inverse images of the affine opens of the base
(`...RelativeProjTwistGlue.chart_image_top`) and cover `X`
(`...RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`): the divisibility nesting is
`AlgebraicGeometry.Proj.degreeOpen_le_of_dvd` chart by chart, and the covering is
`AlgebraicGeometry.Proj.iSup_degreeOpen_eq_top` chart by chart together with the fact that the
charts cover.

The construction is moreover **chart-wise exact**, not merely chart-wise sufficient: the inverse
image of `U_d` under the chart of `U` is the absolute degree-`d` open of `Proj Γ(U, A)` on the
nose (`RelativeProjData.chart_preimage_degreeOpen`). That is what identifies these `U_d` with the
`U_d` of the source's proof, whose own `U_d` base-changed to an affine `V` of the base is
`⋃_{f ∈ Γ(V, A)_d} D₊(f)`; the definition as a union of chart images gives by itself only the
inclusion `chart_image_degreeOpen_le`. Its content is the compatibility of the absolute degree
opens with the transition morphisms of Tag 01NO, which is quasi-coherence of `A` read in a single
degree — see
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpen`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.degreeOpen`: **the relative `U_d`**, an
  open of the relative Proj for each `d`.
* `...RelativeProj.RelativeProjData.degreeOpenChartIso`: **the identification of a member of the
  covering of the relative `U_d` with an absolute `U_d`**, as schemes.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.ProjDegreeRepresentation`: what is **left** of
  the hypothesis bundle `...RelativeProjQcohSheaf.DegreeRepresentation` once residue (iii) is
  proved — residue (i) alone, as a representation of `F_d` by the constructed `U_d`, together
  with its naturality and its compatibility with the transitions.

## Main results

* `...RelativeProj.RelativeProjData.chart_preimage_degreeOpen`: **the chart-wise identification**
  — over an affine open `U` of the base the relative `U_d` is the absolute
  `AlgebraicGeometry.Proj.degreeOpen (A.grading U) d`.
* `...RelativeProj.RelativeProjData.degreeOpen_le_of_dvd` and
  `...RelativeProjData.degreeOpen_toNat_le_of_dvd`: **`U_d ⊆ U_e` when `d ∣ e`**, the nesting
  clause of residue (iii), in the `ℕ`- and `ℤ`-indexed spellings.
* `...RelativeProj.RelativeProjData.iSup_degreeOpen_eq_top` and
  `...RelativeProjData.isOpenCover_degreeOpen`: **the `U_d` for `d ≥ 1` cover the relative
  Proj**, the covering clause of residue (iii), in the same two spellings.
* `...RelativeProj.RelativeProjData.chart_image_degreeOpen` and
  `...RelativeProjData.iSup_inf_degreeOpen_eq`: **the relative `U_d` is the union over the affine
  opens `U` of the base of the opens `U_d ⊓ f⁻¹(U)`**, and each of those is the chart image of
  the absolute degree-`d` open of `Proj Γ(U, A)`. Together with `degreeOpenChartIso` and
  `...RelativeProjData.degreeOpenChartIso_hom_fac` this is the statement that the relative `U_d`
  is glued from absolute `U_d`, which is where residue (i) would be glued.
* `...RelativeProjQcohSheaf.ProjDegreeRepresentation.toDegreeRepresentation`: the hypothesis
  bundle of Tag 01NY **with its three geometric fields discharged**.
* `...RelativeProjQcohSheaf.F.representableByRelativeProj`: **Tag 01NY conditional on residue (i)
  only** — the relative Proj represents the functor `F` of the display 01NX as soon as its
  constructed opens `U_d` represent the `F_d`.

## Implementation notes

**Which fields of the bundle this discharges, and which it does not.** The bundle
`...RelativeProjQcohSheaf.DegreeRepresentation` has seven fields. Three of them — `opens`,
`isOpenCover` and `monotone` — are residue (iii) proper and are supplied here by
`RelativeProjData.degreeOpen`, `isOpenCover_degreeOpen` and `degreeOpen_toNat_le_of_dvd`. Two
more — `equiv` and `equiv_pullback` — are residue (i) over a general base, the descent of
[Stacks, Tag 01NU] along the charts, and remain hypotheses; Tag 01NU itself is proved. The
seventh, `equiv_scale`, is the compatibility of the two residues: that the inclusion
`U_d ⊆ U_{a d}` is the transition `F_d → F_{a d}`. **Its statement mentions `equiv`**, so it
cannot be stated, let alone proved, without residue (i)'s data, and it therefore stays in
`ProjDegreeRepresentation` alongside residue (i). It is not an independent assumption of residue
(iii) that is being hidden: there is no residue-(iii)-only statement it could be.

**Indexing.** The bundle indexes its opens by `ℤ`, as the source does, and uses them only in
positive degrees; the construction here is indexed by `ℕ`, as the absolute `degreeOpen` is, and
the bundle's `opens` field is `fun d => P.degreeOpen d.toNat`. In nonpositive degrees that reads
`P.degreeOpen 0`, which no field of the bundle mentions.

**Why the chart-wise identification is stated on inverse images.** `f ''ᵁ U` carries an
`IsOpenImmersion f` instance argument, so no rewrite of the morphism underneath it is type-correct
at `implicit` transparency and `rw` refuses to fire; `f ⁻¹ᵁ U` has no such argument. Hence
`chart_preimage_degreeOpen` compares `P.chart U hU ⁻¹ᵁ P.degreeOpen d` with the absolute open
rather than comparing images, and the chart facts it uses
(`RelativeProjData.chart_transition_apply`, `...toBase_chart_apply`) are stated at a point.

**What this does and does not say about residue (i).** It identifies the *opens*, not the functor
they represent. `Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.existsUnique_hom` is the
absolute statement — the absolute `U_d ⊆ Proj 𝒜` represents the triples of Section 27.12 — and the
identification is what lets residue (i) be stated against it chart by chart: the relative `U_d` is
covered by opens, one for each affine open `U` of the base, each of which *is* an absolute `U_d`.
That last sentence is itself proved below and not only asserted: the member of the covering is
`U_d ⊓ f⁻¹(U)` (`RelativeProjData.chart_image_degreeOpen`,
`RelativeProjData.iSup_inf_degreeOpen_eq`) and it is isomorphic as a scheme over the relative
Proj to `AlgebraicGeometry.Proj.degreeOpen (A.grading U) d`
(`RelativeProjData.degreeOpenChartIso`, `RelativeProjData.degreeOpenChartIso_hom_fac`).
Carrying out the glueing is residue (i) over a general base and is **not** done, here or anywhere
in this repository. What is missing is no longer the functor-level input over an affine base, and
no longer its naturality either: [Stacks, Tag 01NU] is proved, with its naturality in the test
scheme, as `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen` — a
`CategoryTheory.Functor.RepresentableBy` for `...RelativeProjQcohSheaf.Fd.functor`, for `S`
affine, `𝒜` with quasi-coherent homogeneous pieces and `d ≥ 1`. It is no longer the agreement of
the chart-wise morphisms either; that is the implementation note "The transport of that statement
is done" below. It is the **Zariski sheaf property of `F_d`**, named in the note after it. So
Tag 01NY stays conditional on residue (i); nothing below is weaker or stronger for these
identifications.

**What the descent still owes.** Residue (i) over the *relative* `U_d` is the descent of the
affine-base representations of [Stacks, Tag 01NU] along the charts. **One chart of it is done.**
`...RelativeProjQcohSheaf.Fd.chartRelativeEquiv` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartFdRepresentation`, with its naturality
`...Fd.chartRelativeEquiv_pullback`, is the bijection between `F_d(T)` for the restricted algebra
`A|_U` and the morphisms `T ⟶ U_d ⊓ f⁻¹(U)`, for `U` an affine open of the base, natural in `T`.
Its three inputs are all available: the base change of [Stacks, Tag 01NT]
(`...RelativeProjQcohSheaf.Fd.baseFibreEquiv`, which identifies the part of `F_d(W)` whose
structure morphism factors through an open `U` of the base with an `F_d` for the inverse-image
algebra `...RelativeProjQcohSheaf.baseAlgebra` on `U`); the comparison of that spelling with the
**restriction** `...RelativeProjBridge.SheafGradedAlgebra.restrict`, whose projective spectrum is
the chart (`...RelativeProjQcohSheaf.Fd.restrictPullbackEquiv` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport`, with its naturality
`...Fd.restrictPullbackEquiv_pullback`); and the grading identification
`...RelativeProjBridge.SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictDegreeOpen`, which identifies the
degree-`d` open of the graded ring of *global* sections of `A|_U`, where Tag 01NU's bijection
lands, with the degree-`d` open of `Γ(U, A)`, where the chart of `U` starts.

The agreement of the chart-wise morphisms of two *different* affine opens of the base used to be
recorded here as unavailable. It is **now available**, for an inclusion `Z ≤ U` of affine opens:
`...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_comp_projInclusionMap` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport` says that the
morphism built from the chart of `Z`, followed by the transition
`...RelativeProj.projInclusionMap A Z U` of [Stacks, Tag 01NO], is the morphism built from the
chart of `U`, and its one hypothesis on the Veronese families is discharged by
`...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap`. That is a compatibility of
the classifying morphism with a change of *chart*, not naturality in the test scheme — which was
already proved.

**The change of chart is proved for the classifying morphism itself.** It used to be recorded
here that the geometric ingredient existed —
`Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projInclusionMap`,
the functoriality of the [Stacks, Tag 01NK] morphism `r_{L, ψ}` along `projInclusionMap` — but
that the classifying morphism of a quadruple is
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom`, produced from the `∃!` of
[Stacks, Tag 01N8] whose witness is `Stacks.AlgebraicGeometry.ProjChartCocycle.glued` and not
that `r_{L, ψ}`, with no lemma identifying the two. That lemma is now
`...ProjChartGradedClassifying.classifyingHom_eq_glued` of
`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClassifying`: the pair the existence
half of [Stacks, Tag 01N8] builds is exhibited as compatible with `ψ`
(`...ProjChartGradedClassifying.isCompatible_glued`, which is what `existsUnique_pair` proves
inside its own `∃!` and does not export), and the uniqueness half then says the chosen morphism
*is* the glued chart morphism. With it the charts' functoriality in the graded ring transfers to
the classifying morphism, and the change of chart is
`...ProjChartGradedClassifying.toProj_classifyingHom_comp_projInclusionMap`.

**The transport of that statement is done, and so is the change of chart for `Fd.chartEquiv`.**
It used to be recorded here that two things were owed: a restriction of quadruples along an
inclusion `Z ≤ U` of affine opens of the base, and the identification of the Veronese family
`...RelativeProjQcohSheaf.veroneseSections` of the restricted quadruple with
`...ProjChartGradedClassifying.comapVeronese` of the one over the larger open. Both exist. The
restriction of quadruples is `...RelativeProjQcohSheaf.Fd.chartClass` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport` — not a map from
quadruples for `A|_U` to quadruples for `A|_Z`, which cannot exist, but the chart-wise class of
**one** quadruple for `A` on `S` taken at each of the two opens. Its Veronese family is computed
by `...RelativeProjQcohSheaf.veroneseSections_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassVeronese`, and the two are
identified by `...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap`. So
`AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover` — whose other hypotheses were already
met, the chart-wise identification of the opens being
`RelativeProjData.chart_preimage_degreeOpen` and `RelativeProjData.degreeOpenChartIso` of this
file and the covering being `RelativeProjData.iSup_inf_degreeOpen_eq` — now has an
unconditional compatibility hypothesis to be given, and the *forward* map of residue (i) over a
general base can be glued from the chart-wise morphisms.

**What residue (i) over a general base still owes is the Zariski sheaf property of `F_d`.** The
`equiv` field of `...RelativeProjQcohSheaf.ProjDegreeRepresentation` is a *bijection*
`F_d(W) ≃ Mor(W, U_d)`. The chart agreement gives the forward map, and
`...ZariskiSeparated.Fd.eq_of_pullback_eq_of_cover` — a class in `F_d(W)` is determined by its
restrictions to an open covering, proved unconditionally — gives its injectivity. The **inverse**
asks for a compatible family of chart-wise classes, one over each part of `W` lying over an affine
open of `S`, to be amalgamated into a single class in `F_d(W)`. That is exactly
`...RelativeProjQcohSheaf.QuadrupleGlues` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiAmalgamation`, and it is **proved**:
`...RelativeProjQcohSheaf.quadrupleGlues_proof` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleGluesProof.lean`, which by
`...Fd.quadrupleGlues_iff_isSheaf` also makes step (1) of the proof of [Stacks, Tag 01NV] a
theorem with no hypothesis, `...RelativeProjQcohSheaf.Fd.isSheaf_functor`. In the shape the
descent wants, the amalgamation is `...RelativeProjQcohSheaf.Fd.exists_amalgamation_opens` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean`.

So **both ingredients of the bijection are available, and its forward map is assembled out of
them**: `...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartGlue.lean`, with its naturality in the
test scheme. The chart agreement that made it possible is extended from a *nested* pair `Z ≤ U`
to two arbitrary affine opens of the base by
`...RelativeProjQcohSheaf.Fd.chartHom_eq_of_chartClassInv_eq`, and the inverse of
`...RelativeProjQcohSheaf.Fd.chartClass` — which carries a class for `𝒜` on `S` to a chart-wise
class for `𝒜|_V` — is `...RelativeProjQcohSheaf.Fd.chartClassInv`, a bijection by
`...Fd.chartClassEquiv`. Two things are still owed: the **inverse** of the bijection, whose
obstruction is not the amalgamation but the *converse* of the chart agreement,
that two chart-wise classes with the same morphism into `X` have the same image under
`Fd.chartClassInv` — which is **proved**, as
`...RelativeProjQcohSheaf.Fd.chartClassInv_eq_of_chartHom_eq` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartConverse`, but carrying the clause that
the two chart-wise classes record the same morphism to `S`, which is implied by its conclusion
and whose discharge needs `Fd.chartHom ≫ P.toBase = ξ.1 ≫ U.ι` at a *chart* — and `equiv_scale`,
whose chart-wise Veronese computation is `...RelativeProjQcohSheaf.Fd.chartHom_scale` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartScale` and which still needs
`Fd.chartClassInv` to commute with `...RelativeProjQcohSheaf.Fd.scale`.

**The grading identification is proved.** Tag 01NU's bijection lands in the morphisms into
`AlgebraicGeometry.Proj.degreeOpen ((A.restrict U.ι).grading ⊤) k`, and identifying that with
`AlgebraicGeometry.Proj.degreeOpen (A.grading U) k` directly runs out of heartbeats at `whnf`.
The identification is
`...RelativeProjBridge.SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`, proved through
the congruence `AlgebraicGeometry.Proj.degreeOpen_toScheme_congr`, which takes the `GradedRing`
instance of each side as an **explicit argument** and never compares the two — the comparison of
`(A.restrict U.ι).instGradedRing ⊤` with `A.instGradedRing (U.ι ''ᵁ ⊤)` being the entire
cost: those two instances differ in their arguments down
to the base scheme itself, so the congruence of two applications of one constant fails and the
`GradedRing`/`DirectSum` tower over `A.sectionRing` is unfolded, the cost
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing` documents. Inside the proof the
two instances are shown equal instead, by `AlgebraicGeometry.Proj.gradedRing_eq`: a
`DirectSum.Decomposition` is a subsingleton and a `SetLike.GradedMonoid` is a proposition.
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictDegreeOpen` records the rest of the
discipline the application needs.

**Why the supremum is over `S.Opens` and an affineness proof rather than over `S.affineOpens`.**
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` is an instance keyed on
`P.chart U hU` with the open and the proof of its affineness separate, and it does not fire at
`P.chart U.1 U.2` for `U : S.affineOpens`; the image notation `P.chart U hU ''ᵁ ·` needs that
instance.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProj

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

namespace RelativeProjData

variable (P : RelativeProjData A)

/-! ### The relative degree-`d` open -/

/-- **The relative `U_d`**, the degree-`d` open of a relative homogeneous spectrum: the union over
the affine opens `U` of the base of the image under the chart `Proj Γ(U, A) ⟶ X` of the absolute
degree-`d` open `⋃_{f ∈ Γ(U, A)_d} D₊(f)` of `Proj Γ(U, A)`.

The chart is an open immersion, so each of those images is an open of `X`. -/
def degreeOpen (d : ℕ) : P.scheme.Opens :=
  ⨆ U : S.Opens, ⨆ hU : IsAffineOpen U,
    P.chart U hU ''ᵁ AlgebraicGeometry.Proj.degreeOpen (A.grading U) d

/-- The chart over an affine open of the base carries the absolute degree-`d` open into the
relative one. -/
theorem chart_image_degreeOpen_le (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) :
    P.chart U hU ''ᵁ AlgebraicGeometry.Proj.degreeOpen (A.grading U) d ≤ P.degreeOpen d :=
  le_iSup₂ (f := fun (U : S.Opens) (hU : IsAffineOpen U) =>
    P.chart U hU ''ᵁ AlgebraicGeometry.Proj.degreeOpen (A.grading U) d) U hU

/-- **The chart-wise description of the relative `U_d`**: over an affine open `U` of the base the
relative degree-`d` open is exactly the absolute one. Its inverse image under the chart
`Proj Γ(U, A) ⟶ X` is `AlgebraicGeometry.Proj.degreeOpen (A.grading U) d`, the union
`⋃_{f ∈ Γ(U, A)_d} D₊(f)` of Equation 27.12.0.1.

One inclusion is `RelativeProjData.chart_image_degreeOpen_le` read through
`AlgebraicGeometry.Scheme.Hom.preimage_image_eq`. The other is the content: a point of the chart
of `U` lying in the chart image of the degree-`d` open of *another* affine open `V` has to be put
in the degree-`d` open of `U`. Both charts restrict, over an affine open `W ⊆ U ⊓ V` of the base
containing its base point, to the chart of `W`
(`RelativeProjData.exists_projInclusionMap_eq`), and there the two transitions pull the degree-`d`
opens of `U` and of `V` back to the same thing, namely the degree-`d` open of `W`. That last step
is `...RelativeProj.projInclusionMap_preimage_degreeOpen`, and it is where quasi-coherence of `A`
enters: a homogeneous section of degree `d` over `W` is an `Γ(W, 𝒪_S)`-combination of
restrictions of homogeneous sections of degree `d` over `U`. -/
theorem chart_preimage_degreeOpen (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) :
    P.chart U hU ⁻¹ᵁ P.degreeOpen d = AlgebraicGeometry.Proj.degreeOpen (A.grading U) d := by
  refine le_antisymm (fun x hx => ?_) ?_
  · -- `x` lies in the chart image of the degree-`d` open of some affine open `V` of the base
    have hx' : P.chart U hU x ∈ ⨆ V : S.Opens, ⨆ hV : IsAffineOpen V,
        P.chart V hV ''ᵁ AlgebraicGeometry.Proj.degreeOpen (A.grading V) d := hx
    obtain ⟨V, hVmem⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    obtain ⟨hV, hmem⟩ := TopologicalSpace.Opens.mem_iSup.mp hVmem
    obtain ⟨y, hy, hyx⟩ := hmem
    -- the base point of a point of a chart lies in the corresponding open
    have hb : ∀ (V : S.Opens) (hV : IsAffineOpen V) (y), P.toBase (P.chart V hV y) ∈ V := by
      intro V hV y
      rw [P.toBase_chart_apply V hV y]
      exact (projInclusionToOpen A V hV y).2
    have hbU := hb U hU x
    have hbV : P.toBase (P.chart U hU x) ∈ V := by
      rw [← hyx]
      exact hb V hV y
    obtain ⟨-, ⟨W, hWmem, rfl⟩, hbW, hWUV⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (show P.toBase (P.chart U hU x) ∈ ((U ⊓ V : S.Opens) : Set S) from ⟨hbU, hbV⟩) (U ⊓ V).2
    have hW : IsAffineOpen W := hWmem
    have hWU : W ≤ U := fun z hz => (hWUV hz).1
    have hWV : W ≤ V := fun z hz => (hWUV hz).2
    -- `x` comes from the chart over `W`, and so does `y`
    obtain ⟨z, hz⟩ := P.exists_projInclusionMap_eq hWU hW hU x hbW
    have echart : P.chart V hV (projInclusionMap A W V hWV hW hV z) = P.chart V hV y := by
      rw [P.chart_transition_apply W V hWV hW hV z,
        ← P.chart_transition_apply W U hWU hW hU z, hz]
      exact hyx.symm
    have hzy : projInclusionMap A W V hWV hW hV z = y :=
      (P.chart V hV).isOpenEmbedding.injective echart
    -- the two transitions pull the degree-`d` opens of `V` and of `U` back to that of `W`
    have hzW : z ∈ AlgebraicGeometry.Proj.degreeOpen (A.grading W) d := by
      rw [← projInclusionMap_preimage_degreeOpen A W V hWV hW hV d]
      change projInclusionMap A W V hWV hW hV z ∈
        AlgebraicGeometry.Proj.degreeOpen (A.grading V) d
      rw [hzy]
      exact hy
    have hfin : projInclusionMap A W U hWU hW hU z ∈
        AlgebraicGeometry.Proj.degreeOpen (A.grading U) d :=
      (projInclusionMap_preimage_degreeOpen A W U hWU hW hU d).ge hzW
    rwa [hz] at hfin
  · calc AlgebraicGeometry.Proj.degreeOpen (A.grading U) d
        = P.chart U hU ⁻¹ᵁ (P.chart U hU ''ᵁ AlgebraicGeometry.Proj.degreeOpen (A.grading U) d) :=
          (Scheme.Hom.preimage_image_eq (P.chart U hU) _).symm
      _ ≤ _ := (P.chart U hU).preimage_mono (P.chart_image_degreeOpen_le U hU d)

/-! ### The relative `U_d` is covered by absolute `U_d`, one for each affine open of the base -/

/-- **The chart image of the absolute degree-`d` open is the part of the relative `U_d` lying
over `U`.** Over an affine open `U` of the base the image under the chart
`Proj Γ(U, A) ⟶ X` of `AlgebraicGeometry.Proj.degreeOpen (A.grading U) d` is `U_d ⊓ f⁻¹(U)`,
where `f : X ⟶ S` is the structure morphism.

This is `RelativeProjData.chart_preimage_degreeOpen` read through
`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`, the range of the chart being
`f⁻¹(U)` (`...RelativeProjTwistGlue.chart_image_top`). -/
theorem chart_image_degreeOpen (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) :
    P.chart U hU ''ᵁ AlgebraicGeometry.Proj.degreeOpen (A.grading U) d =
      P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen d := by
  rw [← P.chart_preimage_degreeOpen U hU d, Scheme.Hom.image_preimage_eq_opensRange_inf,
    ← Scheme.Hom.image_top_eq_opensRange, chart_image_top P U hU]

/-- The range of the composite `U_d(Γ(U, A)) ⟶ Proj Γ(U, A) ⟶ X` of the absolute degree-`d` open
with the chart of an affine open `U` of the base. -/
theorem opensRange_ι_comp_chart (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) :
    ((AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι ≫ P.chart U hU).opensRange =
      P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen d := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, P.chart_image_degreeOpen U hU d]

/-- **Each member of the covering of the relative `U_d` *is* an absolute `U_d`.** Over an affine
open `U` of the base the open subscheme `U_d ⊓ f⁻¹(U)` of a relative homogeneous spectrum is
isomorphic to the absolute degree-`d` open `⋃_{g ∈ Γ(U, A)_d} D₊(g)` of `Proj Γ(U, A)` of
Equation 27.12.0.1, compatibly with the two inclusions into the relative Proj
(`RelativeProjData.degreeOpenChartIso_hom_fac`).

Both are opens of the relative Proj with the same points: the chart is an open immersion whose
image of the absolute degree-`d` open is exactly `U_d ⊓ f⁻¹(U)`
(`RelativeProjData.chart_image_degreeOpen`), so the two open immersions into `X` have the same
range and `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` compares their sources. -/
def degreeOpenChartIso (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) :
    (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).toScheme ≅
      (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen d).toScheme :=
  AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq
    ((AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι ≫ P.chart U hU)
    (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen d).ι
    (by
      have h := P.opensRange_ι_comp_chart U hU d
      rw [← Scheme.Opens.opensRange_ι (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen d)] at h
      exact congrArg (fun V : P.scheme.Opens => (V : Set P.scheme)) h)

/-- The comparison of `U_d ⊓ f⁻¹(U)` with the absolute degree-`d` open is compatible with the two
inclusions into the relative Proj: composed with the inclusion of `U_d ⊓ f⁻¹(U)` it is the
chart. -/
theorem degreeOpenChartIso_hom_fac (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ) :
    (P.degreeOpenChartIso U hU d).hom ≫ (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen d).ι =
      (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι ≫ P.chart U hU :=
  AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- **The relative `U_d` is the union, over the affine opens `U` of the base, of the opens
`U_d ⊓ f⁻¹(U)`**, each of which is an absolute degree-`d` open by
`RelativeProjData.degreeOpenChartIso`. -/
theorem iSup_inf_degreeOpen_eq (d : ℕ) :
    (⨆ U : S.Opens, ⨆ _ : IsAffineOpen U, P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen d) = P.degreeOpen d := by
  refine le_antisymm (iSup₂_le fun _ _ => inf_le_right) ?_
  refine iSup₂_le fun U hU => ?_
  exact le_iSup₂_of_le U hU (le_of_eq (P.chart_image_degreeOpen U hU d))

/-! ### Residue (iii) of Tag 01NY -/

/-- **The nesting clause of residue (iii) of Tag 01NY**: `U_d ⊆ U_e` whenever `d ∣ e` and `e` is
positive.

Chart by chart this is `AlgebraicGeometry.Proj.degreeOpen_le_of_dvd`, the absolute statement, and
the image of an open under the chart is monotone in that open. -/
theorem degreeOpen_le_of_dvd {d e : ℕ} (hdvd : d ∣ e) (he : 0 < e) :
    P.degreeOpen d ≤ P.degreeOpen e :=
  iSup₂_le fun U hU =>
    (Scheme.Hom.image_mono _
        (AlgebraicGeometry.Proj.degreeOpen_le_of_dvd (A.grading U) hdvd he)).trans
      (P.chart_image_degreeOpen_le U hU e)

/-- **The covering clause of residue (iii) of Tag 01NY**: the opens `U_d` for `d ≥ 1` cover the
relative homogeneous spectrum.

The charts cover it (`...RelativeProjTwistGlue.iSup_toBase_preimage_eq_top` together with
`...RelativeProjTwistGlue.chart_image_top`), and on each chart the absolute degree opens cover
(`AlgebraicGeometry.Proj.iSup_degreeOpen_eq_top`). -/
theorem iSup_degreeOpen_eq_top : (⨆ d : ℕ, ⨆ _ : 0 < d, P.degreeOpen d) = ⊤ := by
  have key : ∀ (U : S.Opens) (hU : IsAffineOpen U),
      P.toBase ⁻¹ᵁ U ≤ ⨆ d : ℕ, ⨆ _ : 0 < d, P.degreeOpen d := by
    intro U hU
    have h : P.chart U hU ''ᵁ (⊤ : (AlgebraicGeometry.Proj (A.grading U)).Opens) ≤
        ⨆ d : ℕ, ⨆ _ : 0 < d, P.degreeOpen d := by
      rw [← AlgebraicGeometry.Proj.iSup_degreeOpen_eq_top (A.grading U),
        Scheme.Hom.image_iSup₂]
      exact iSup₂_le fun d hd =>
        le_iSup₂_of_le d hd (P.chart_image_degreeOpen_le U hU d)
    rwa [chart_image_top P U hU] at h
  refine top_le_iff.mp ?_
  rw [← iSup_toBase_preimage_eq_top P]
  exact iSup_le fun U => key U.1 U.2

/-- The nesting clause of residue (iii) in the `ℤ`-indexed spelling the hypothesis bundle of
Tag 01NY uses. -/
theorem degreeOpen_toNat_le_of_dvd {d e : ℤ} (hd : 0 < d) (he : 0 < e) (hdvd : d ∣ e) :
    P.degreeOpen d.toNat ≤ P.degreeOpen e.toNat := by
  refine P.degreeOpen_le_of_dvd ?_ (by omega)
  rwa [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg he.le]

/-- **Residue (iii) of Tag 01NY, in the spelling its hypothesis bundle uses**: the opens `U_d`
indexed by the positive integers are an open cover of the relative homogeneous spectrum. -/
theorem isOpenCover_degreeOpen :
    IsOpenCover fun d : {d : ℤ // 0 < d} => P.degreeOpen d.1.toNat := by
  refine IsOpenCover.mk (top_le_iff.mp ?_)
  rw [← P.iSup_degreeOpen_eq_top]
  refine iSup₂_le fun d hd => ?_
  refine le_iSup_of_le ⟨(d : ℤ), by exact_mod_cast hd⟩ ?_
  simp

end RelativeProjData

end Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProj

variable {S : Scheme.{u}}

/-! ### What is left of the hypothesis bundle -/

/-- **Residue (i) of Tag 01NY alone**, over the constructed opens of a relative homogeneous
spectrum: for every positive `d` the open `U_d` of `RelativeProjData.degreeOpen` represents the
functor `F_d` of Section 01NS on the quasi-compact test schemes, naturally in the test scheme and
compatibly with the transitions `F_d → F_{a d}`.

This is what remains of the hypothesis bundle
`...RelativeProjQcohSheaf.DegreeRepresentation` once residue (iii) is proved: its three geometric
fields `opens`, `isOpenCover` and `monotone` are discharged by
`...RelativeProj.RelativeProjData.degreeOpen`,
`...RelativeProjData.isOpenCover_degreeOpen` and `...RelativeProjData.degreeOpen_toNat_le_of_dvd`.

Nothing here is proved: this is residue (i) over a general base, the descent of [Stacks,
Tag 01NU] along the charts. Tag 01NU itself — residue (i) over an *affine* base, with its
naturality in the test scheme — **is** proved, as
`...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`, and one chart of the descent is proved
as `...RelativeProjQcohSheaf.Fd.chartRelativeEquiv`, and the charts now *agree*
(`...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_comp_projInclusionMap` with its hypothesis
discharged by `...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting`).

The Zariski sheaf property of `F_d`, which the **inverse** of the glued bijection needs, is no
longer missing either: it is the theorem `...RelativeProjQcohSheaf.Fd.isSheaf_functor`, and the
amalgamation it provides is `...RelativeProjQcohSheaf.Fd.exists_amalgamation_opens` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean`, with no
hypothesis. The **forward** map of the bijection over a general base is now constructed too, as
`...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartGlue.lean`, with its naturality in the
test scheme; the chart agreement it rests on is extended from a nested pair to two *arbitrary*
affine opens by `...RelativeProjQcohSheaf.Fd.chartHom_eq_of_chartClassInv_eq`, and the inverse of
`...RelativeProjQcohSheaf.Fd.chartClass` is `...RelativeProjQcohSheaf.Fd.chartClassInv`, a
bijection by `...Fd.chartClassEquiv`. What is still missing is the **inverse** of the bijection —
whose obstruction is not the amalgamation but the *converse* of the chart agreement,
that two chart-wise classes with the same morphism into `X` have the same image under
`Fd.chartClassInv` — which is **proved**, as
`...RelativeProjQcohSheaf.Fd.chartClassInv_eq_of_chartHom_eq` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartConverse`, but carrying the clause that
the two chart-wise classes record the same morphism to `S`, which is implied by its conclusion
and whose discharge needs `Fd.chartHom ≫ P.toBase = ξ.1 ≫ U.ι` at a *chart* — and `equiv_scale`,
whose chart-wise Veronese computation is `...RelativeProjQcohSheaf.Fd.chartHom_scale` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartScale` and which still needs
`Fd.chartClassInv` to commute with `...RelativeProjQcohSheaf.Fd.scale`. As in
`DegreeRepresentation`,
the `equiv` field
compares the `Type (u + 1)` set `F_d(W)` with the `Type u` set `Mor(W, U_d)`; the essential
smallness of `F_d(W)` that this entails is **not** an extra unproved assumption, being the
theorem `...RelativeProjQcohSheaf.Fd.small` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleSmall`. The field `equiv_scale` is
a compatibility *between* the two residues — its statement mentions `equiv` — and so belongs here
rather than to residue (iii). -/
structure ProjDegreeRepresentation (A : SheafGradedAlgebra S) (P : RelativeProjData A) where
  /-- `U_d` represents `F_d` on quasi-compact test schemes: residue (i) over a general base,
  i.e. the descent of [Stacks, Tag 01NU] along the charts. -/
  equiv : ∀ (d : ℤ), 0 < d → ∀ W : Scheme.{u}, CompactSpace W →
    Fd (situationAlgebra A) d W ≃ (W ⟶ (P.degreeOpen d.toNat).toScheme)
  /-- The representation is natural in the test scheme. -/
  equiv_pullback : ∀ (d : ℤ) (hd : 0 < d) (W W' : Scheme.{u}) (hW : CompactSpace W)
    (hW' : CompactSpace W') (h : W' ⟶ W) (ξ : Fd (situationAlgebra A) d W),
    equiv d hd W' hW' (Fd.pullback h ξ) = h ≫ equiv d hd W hW ξ
  /-- The transition `F_d → F_{a d}` is the inclusion `U_d ⊆ U_{a d}`, whose proof is now the
  theorem `...RelativeProj.RelativeProjData.degreeOpen_toNat_le_of_dvd` rather than a field. -/
  equiv_scale : ∀ (d a : ℤ) (hd : 0 < d) (ha : 0 < a) (W : Scheme.{u}) (hW : CompactSpace W)
    (ξ : Fd (situationAlgebra A) d W),
    equiv (a * d) (mul_pos ha hd) W hW (Fd.scale ha ξ)
      = equiv d hd W hW ξ ≫ P.scheme.homOfLE
          (P.degreeOpen_toNat_le_of_dvd hd (mul_pos ha hd) ⟨a, mul_comm a d⟩)

namespace ProjDegreeRepresentation

variable {A : SheafGradedAlgebra S} {P : RelativeProjData A}

/-- **The hypothesis bundle of Tag 01NY with residue (iii) discharged.** The three geometric
fields are the theorems of this file; only residue (i) over a general base — the descent of
[Stacks, Tag 01NU] along the charts, Tag 01NU itself being proved — and its compatibility with
the transitions are carried. -/
def toDegreeRepresentation (R : ProjDegreeRepresentation A P) :
    DegreeRepresentation (situationAlgebra A) P.scheme where
  opens d := P.degreeOpen d.toNat
  isOpenCover := P.isOpenCover_degreeOpen
  monotone _ _ hd he hdvd := P.degreeOpen_toNat_le_of_dvd hd he hdvd
  equiv := R.equiv
  equiv_pullback := R.equiv_pullback
  equiv_scale := R.equiv_scale

end ProjDegreeRepresentation

/-- **Tag 01NY, conditional on residue (i) alone.** Let `S` be a scheme and `A` a quasi-coherent
graded `𝒪_S`-algebra (Situation 01NN), and let `X` be a relative homogeneous spectrum of `A` —
in particular `Proj_S(A)` itself. If for every `d ≥ 1` the constructed open `U_d ⊆ X` represents
the functor `F_d` of Section 01NS, compatibly with the transitions, then `X` represents the
functor `F` of the display 01NX.

Residue (iii) — that the `U_d` are opens of one scheme covering it and nested along divisibility
— is **proved**, in this file. Residue (i) — that `U_d` represents `F_d` — is the descent of
[Stacks, Tag 01NU] along the charts and is **not** proved; it is the hypothesis `R`. Tag 01NU
itself, residue (i) over an affine base with its naturality in the test scheme, *is* proved
(`...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`), and so is one chart of the descent
(`...RelativeProjQcohSheaf.Fd.chartRelativeEquiv`). -/
def F.representableByRelativeProj {A : SheafGradedAlgebra S} {P : RelativeProjData A}
    (R : ProjDegreeRepresentation A P) :
    (F.limFunctor (situationAlgebra A)).RepresentableBy P.scheme :=
  F.representableBy R.toDegreeRepresentation

/-- Under residue (i) alone, the functor `F` of the display 01NX is representable as a
predicate. -/
theorem F.isRepresentable_relativeProj {A : SheafGradedAlgebra S} {P : RelativeProjData A}
    (R : ProjDegreeRepresentation A P) : (F.limFunctor (situationAlgebra A)).IsRepresentable :=
  (F.representableByRelativeProj R).isRepresentable

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end

module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart
public import StacksFrontier.AlgebraicGeometry.Morphism.Nested
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 07ZG, assertion (2): the morphism of relative projective spectra

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras. Tag 07ZG attaches to
it an open `U(ψ)` of `Proj_S(B)` — defined as
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.relativeMapDomain`
— and a morphism

`r_ψ : U(ψ) ⟶ Proj_S(A)`

over `S`, whose restriction to the chart over an affine open `U` of the base is the absolute
morphism `U(ψ_U) ⟶ Proj Γ(U, A)` of Tag 01MY. This file constructs that morphism and proves the
affine-local characterization, that it is a morphism over `S`, and that those properties determine
it.

No surjectivity is assumed. The everywhere-defined case, where `U(ψ) = ⊤` and the morphism is a
closed immersion, is `Stacks.AlgebraicGeometry.ProjBundleSurjection.map`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage`: the open `U(ψ) ⊓ p⁻¹(U)` of `Proj_S(B)`,
  as the image of the chart domain under the chart over an affine open `U` of the base. These are
  the pieces `U(ψ)` is the supremum of, by the definition of `relativeMapDomain`.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.localHom`: the morphism on one such piece.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom`: **Tag 07ZG, assertion (2).**
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartPieceIso`: the canonical identification of the
  piece `U(ψ) ⊓ q⁻¹(W)` over an affine open `W` of the base with the chart domain `U(ψ_W)`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.homOfLE_comp_relativeMapHom`: its defining equation —
  on the piece over an affine open of the base it is the local morphism.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chart_comp_relativeMapHom`: **the affine-local
  characterization.** Read through the chart over an affine open `U` of the base, `r_ψ` is the
  absolute morphism of Tag 01MY followed by the chart of `Proj_S(A)` over `U`.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartPieceIso_hom_comp_homOfLE_comp_relativeMapHom`:
  the same statement in the shape the source gives it, about the restriction of `r_ψ` to
  `U(ψ) ⊓ q⁻¹(W)`.
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom_comp_toBase`: **it is a morphism over
  the base.**
* `Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom_unique`: a morphism with the
  affine-local characterization is `r_ψ`.

## The route

`U(ψ)` is by definition the supremum, over the affine opens `U` of `S`, of the chart images of the
chart domains, so `AlgebraicGeometry.Scheme.Opens.iSupOpenCover` covers it by them and
`AlgebraicGeometry.Scheme.Cover.glueMorphisms` glues. Two things are needed.

**Compatibility for a nested pair** is
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartDomainTrans_comp_mapHom`, the nested square of the
sibling file, transported from the chart domains to their chart images along
`AlgebraicGeometry.Scheme.Hom.isoImage` — which is
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.isoImage_hom_comp_homOfLE`, a statement about open
immersions and the chart transitions only.

**Compatibility for an arbitrary pair** is reduced to the nested case by refinement, and the
refinement is available because the pieces have a second description with no chart in it:
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage_eq_inf` says the piece over `U` is
`U(ψ) ⊓ p⁻¹(U)`. Hence the overlap of the pieces over `T` and `U` is `U(ψ) ⊓ p⁻¹(T ⊓ U)`, and the
affine opens of `S` contained in `T ⊓ U` cover `T ⊓ U`, so the pieces over them cover the overlap
(`Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage_inf_eq_iSup`). Both morphisms restrict to the
local morphism on each, by the nested case.

Being a morphism over `S` is again checked on the pieces, where it is
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.mapHom_comp_toOpen`: the absolute morphism of Tag 01MY
is a morphism over the affine open, because the degree-zero part of the induced homomorphism of
section rings is compatible with the two structure maps
(`Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf_comp_zeroHom`, which needs no
surjectivity) and because of the commuting square of Tags 01N2 and 01NO
(`Stacks.AlgebraicGeometry.RelativeProj.mapHom_toSpecZero`).

## Implementation notes

Everything is stated at the `Stacks.AlgebraicGeometry.ProjShared.mapDomain` spelling of the chart
domain rather than at
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.chartDomain`,
for the reason recorded in
the sibling file: the two are definitionally equal, and a goal mixing them is not type-correct at
implicit transparency, so rewrites fail on patterns that are present.

The identification of the affine open with the spectrum of its functions is kept as a *variable*
`i` inside the proof of `mapHom_comp_toOpen` and instantiated only at the end, exactly as in
`Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_comp_toOpen`: the term `V.2.isoSpec.inv`
makes the goal ill-typed at implicit transparency and every `rw` then fails on a pattern that is
present.

The index of the cover is `Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen`,
whose second projection
has type `IsAffineOpen U` on the nose, rather than `AlgebraicGeometry.Scheme.affineOpens`; see the
reason recorded at that definition.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Where assertion (3) is

Assertion (3) of Tag 07ZG — the maps on twists
`θ_n : r_ψ^*𝒪_X(n) ⟶ 𝒪_{U(ψ)}(n)` — is not here. It is glued over the same cover as the morphism
above: over an affine open `U` of the base the local datum is the comparison map of Tag 01MY for
`ψ_U`, conjugated by the chart identifications
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.chartIso` of the two twist data and by the
cartesian square
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.isPullback_chart_relativeMapHom`, written out as
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart`; for a nested pair `T ⊆ U` the two
local data agree by `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart_nested`, whose two
inputs are the twist assertion of Tag 01MZ in the form
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp_of` and the agreement of the two
chart identifications of Tag 01NR,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_eq`. The glued map is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap`, and
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage_inf_eq_iSup` below is what reduces an
arbitrary overlap of two pieces to that nested case.

The separation half is: such a `θ` is unique given its affine-local description, by
`Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.twistMap_ext`. The tag is therefore claimed with
scoped clause strings on the open and the morphism, and not as a whole.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-! ### The local morphism is a morphism over the affine open -/

/-- The absolute morphism of Tag 01MY is compatible with the structure morphisms of the two
projective spectra to the spectrum of the ring of functions on the affine open. -/
@[reassoc]
public theorem mapHom_comp_toSpecZero_comp_strZeroSheaf (U : S.Opens) :
    mapHom (A.grading U) (B.grading U) (ψ.sectionHom U) ≫
        Proj.toSpecZero (A.grading U) ≫
          Spec.map (ProjBundleSurjection.strZeroSheaf A U) =
      (mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U)).ι ≫
        Proj.toSpecZero (B.grading U) ≫
          Spec.map (ProjBundleSurjection.strZeroSheaf B U) := by
  rw [← Category.assoc, mapHom_toSpecZero (A.grading U) (B.grading U) (ψ.sectionHom U),
    Category.assoc, Category.assoc, ← Spec.map_comp,
    ProjBundleSurjection.strZeroSheaf_comp_zeroHom ψ U]

/-- **The absolute morphism of Tag 01MY is a morphism over the affine open of the base**, stated
over the small affine Zariski site. -/
@[reassoc]
public theorem mapHom_comp_toOpen (V : S.AffineZariskiSite) :
    mapHom (A.grading V.toOpens) (B.grading V.toOpens) (ψ.sectionHom V.toOpens) ≫
        A.toGradedAlgebra.toOpen V =
      (mapDomain (A.grading V.toOpens) (B.grading V.toOpens)
          (ψ.sectionHom V.toOpens)).ι ≫ B.toGradedAlgebra.toOpen V := by
  exact mapHom_comp_toSpecZero_comp_strZeroSheaf_assoc ψ V.toOpens _

/-- **The absolute morphism of Tag 01MY is a morphism over the affine open of the base.** -/
@[reassoc]
public theorem mapHom_comp_projInclusionToOpen (U : S.Opens) (hU : IsAffineOpen U) :
    mapHom (A.grading U) (B.grading U) (ψ.sectionHom U) ≫ projInclusionToOpen A U hU =
      (mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U)).ι ≫
        projInclusionToOpen B U hU :=
  mapHom_comp_toOpen ψ (⟨U, hU⟩ : S.AffineZariskiSite)

/-! ### The pieces of the open subscheme -/

/-- The piece of `U(ψ)` over an affine open `U` of the base: the image of the chart domain under
the chart. By the definition of
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.relativeMapDomain`,
`U(ψ)` is the supremum
of these. -/
public abbrev chartImage (U : AffineOpen S) : (relativeProj B).scheme.Opens :=
  (relativeProj B).chart U.1 U.2 ''ᵁ
    mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)

/-- `U(ψ)` is the supremum of its pieces. -/
public theorem relativeMapDomain_eq_iSup :
    ψ.relativeMapDomain = ⨆ U : AffineOpen S, chartImage ψ U :=
  rfl

/-- **The piece over `U` has a description with no chart in it**: it is `U(ψ) ⊓ p⁻¹(U)`. This is
what makes the refinement argument for an arbitrary pair of affine opens possible. -/
public theorem chartImage_eq_inf (U : AffineOpen S) :
    chartImage ψ U = ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) := by
  show (relativeProj B).chart U.1 U.2 ''ᵁ
      mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) = _
  rw [show mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) =
      (relativeProj B).chart U.1 U.2 ⁻¹ᵁ ψ.relativeMapDomain from
    (ψ.chart_preimage_relativeMapDomain U.1 U.2).symm,
    Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_top_eq_opensRange,
    chart_image_top (relativeProj B) U.1 U.2, inf_comm]

/-- Each piece is contained in `U(ψ)`. Stated at the `relativeMapDomain` spelling, which is the
one every exported statement below uses: `le_iSup` produces the `⨆` spelling instead, and the two
are definitionally equal but not interchangeable in a goal. -/
public theorem chartImage_le (U : AffineOpen S) : chartImage ψ U ≤ ψ.relativeMapDomain :=
  le_iSup (chartImage ψ) U

/-- The pieces grow along inclusions of affine opens of the base. -/
public theorem chartImage_mono {T U : AffineOpen S} (h : T.1 ≤ U.1) :
    chartImage ψ T ≤ chartImage ψ U :=
  ψ.chart_image_chartDomain_mono T.1 U.1 h T.2 U.2

/-- **The overlap of two pieces is covered by the pieces over the affine opens refining the
intersection.** The overlap is `U(ψ) ⊓ p⁻¹(T ⊓ U)` by
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage_eq_inf`, and the affine opens contained in
`T ⊓ U` cover it. -/
public theorem chartImage_inf_eq_iSup (T U : AffineOpen S) :
    chartImage ψ T ⊓ chartImage ψ U =
      ⨆ W : {W : AffineOpen S // W.1 ≤ T.1 ⊓ U.1}, chartImage ψ W.1 := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun W => le_inf
    (chartImage_mono ψ (le_trans W.2 inf_le_left))
    (chartImage_mono ψ (le_trans W.2 inf_le_right)))
  rw [chartImage_eq_inf ψ T, chartImage_eq_inf ψ U] at hx
  obtain ⟨⟨hxD, hxT⟩, -, hxU⟩ := hx
  obtain ⟨-, ⟨W, hWmem, rfl⟩, hbW, hWTU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (show (relativeProj B).toBase x ∈ ((T.1 ⊓ U.1 : S.Opens) : Set S) from ⟨hxT, hxU⟩)
      (T.1 ⊓ U.1).2
  have hW : IsAffineOpen W := hWmem
  refine TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨(⟨W, hW⟩ : AffineOpen S), fun y hy => hWTU hy⟩, ?_⟩
  rw [chartImage_eq_inf ψ (⟨W, hW⟩ : AffineOpen S)]
  exact ⟨hxD, hbW⟩

/-! ### The local morphisms and their compatibility -/

/-- **The morphism on one piece.** Through the identification of the piece with the chart domain
it is the absolute morphism of Tag 01MY followed by the chart of `Proj_S(A)`. -/
public def localHom (U : AffineOpen S) :
    (chartImage ψ U).toScheme ⟶ (relativeProj A).scheme :=
  (((relativeProj B).chart U.1 U.2).isoImage
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).inv ≫
    mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
      (relativeProj A).chart U.1 U.2

/-- The identifications of the pieces with the chart domains carry the inclusion of pieces to the
transition on the chart domains. This is a statement about open immersions and the chart
transitions of Tag 01NQ only. -/
@[reassoc]
public theorem isoImage_hom_comp_homOfLE {T U : AffineOpen S} (h : T.1 ≤ U.1) :
    (((relativeProj B).chart T.1 T.2).isoImage
          (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1))).hom ≫
        (relativeProj B).scheme.homOfLE (chartImage_mono ψ h) =
      chartDomainTrans ψ T.1 U.1 h T.2 U.2 ≫
        (((relativeProj B).chart U.1 U.2).isoImage
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).hom := by
  rw [← cancel_mono (chartImage ψ U).ι, Category.assoc, Scheme.homOfLE_ι,
    Scheme.Hom.isoImage_hom_ι, Category.assoc, Scheme.Hom.isoImage_hom_ι, ← Category.assoc,
    chartDomainTrans_ι, Category.assoc,
    (relativeProj B).chart_transition T.1 U.1 h T.2 U.2]

/-- **The compatibility for a nested pair.** The morphism on the larger piece restricts to the
morphism on the smaller one. This is the nested square of the sibling file, transported to the
chart images. -/
public theorem homOfLE_comp_localHom {T U : AffineOpen S} (h : T.1 ≤ U.1) :
    (relativeProj B).scheme.homOfLE (chartImage_mono ψ h) ≫ localHom ψ U = localHom ψ T := by
  rw [← cancel_epi (((relativeProj B).chart T.1 T.2).isoImage
      (mapDomain (A.grading T.1) (B.grading T.1) (ψ.sectionHom T.1))).hom, localHom, localHom,
    Iso.hom_inv_id_assoc, ← Category.assoc, isoImage_hom_comp_homOfLE ψ h, Category.assoc,
    Iso.hom_inv_id_assoc, chartDomainTrans_comp_mapHom_assoc ψ T.1 U.1 h T.2 U.2,
    (relativeProj A).chart_transition T.1 U.1 h T.2 U.2]

/-- The inclusion of a refining piece into the overlap of two pieces, read through the cover of
the overlap: it is the inclusion of that piece.

Stated with the index of the cover as a variable of the honest subtype, because inside the
extensionality obligation of
`AlgebraicGeometry.Scheme.Opens.iSupOpenCover` the index appears at the type
`(… ).I₀`, which is a projection out of a `def` and makes the goal ill-typed at implicit
transparency; every `rw` then fails on a pattern that is present. -/
public theorem homOfLE_le_iSup_comp_isoOfEq_inv_homOfLE (T U : AffineOpen S)
    (W : {W : AffineOpen S // W.1 ≤ T.1 ⊓ U.1}) (Z : AffineOpen S)
    (hZ : chartImage ψ W.1 ≤ chartImage ψ Z)
    (hle : chartImage ψ T ⊓ chartImage ψ U ≤ chartImage ψ Z) :
    (relativeProj B).scheme.homOfLE
          (le_iSup (fun W' : {W' : AffineOpen S // W'.1 ≤ T.1 ⊓ U.1} =>
            chartImage ψ W'.1) W) ≫
        ((relativeProj B).scheme.isoOfEq (chartImage_inf_eq_iSup ψ T U)).inv ≫
          (relativeProj B).scheme.homOfLE hle =
      (relativeProj B).scheme.homOfLE hZ := by
  rw [← cancel_mono (chartImage ψ Z).ι]
  simp

/-- On each piece of the refinement, both morphisms are the local morphism of that piece. -/
public theorem homOfLE_le_iSup_comp_localHom_eq (T U : AffineOpen S)
    (W : {W : AffineOpen S // W.1 ≤ T.1 ⊓ U.1}) :
    (relativeProj B).scheme.homOfLE
          (le_iSup (fun W' : {W' : AffineOpen S // W'.1 ≤ T.1 ⊓ U.1} =>
            chartImage ψ W'.1) W) ≫
        ((relativeProj B).scheme.isoOfEq (chartImage_inf_eq_iSup ψ T U)).inv ≫
          (relativeProj B).scheme.homOfLE
              (inf_le_left : chartImage ψ T ⊓ chartImage ψ U ≤ _) ≫ localHom ψ T =
      (relativeProj B).scheme.homOfLE
          (le_iSup (fun W' : {W' : AffineOpen S // W'.1 ≤ T.1 ⊓ U.1} =>
            chartImage ψ W'.1) W) ≫
        ((relativeProj B).scheme.isoOfEq (chartImage_inf_eq_iSup ψ T U)).inv ≫
          (relativeProj B).scheme.homOfLE
              (inf_le_right : chartImage ψ T ⊓ chartImage ψ U ≤ _) ≫ localHom ψ U := by
  rw [reassoc_of% (homOfLE_le_iSup_comp_isoOfEq_inv_homOfLE ψ T U W T
      (chartImage_mono ψ (le_trans W.2 inf_le_left)) inf_le_left),
    reassoc_of% (homOfLE_le_iSup_comp_isoOfEq_inv_homOfLE ψ T U W U
      (chartImage_mono ψ (le_trans W.2 inf_le_right)) inf_le_right),
    homOfLE_comp_localHom ψ (le_trans W.2 inf_le_left),
    homOfLE_comp_localHom ψ (le_trans W.2 inf_le_right)]

/-- **The compatibility for an arbitrary pair**, in the form
`AlgebraicGeometry.Scheme.Cover.glueMorphisms` asks for it: the two morphisms agree on the
overlap. Both restrict to the local morphism on each piece of the refinement. -/
public theorem homOfLE_inf_comp_localHom (T U : AffineOpen S) :
    (relativeProj B).scheme.homOfLE (inf_le_left :
          chartImage ψ T ⊓ chartImage ψ U ≤ _) ≫ localHom ψ T =
      (relativeProj B).scheme.homOfLE (inf_le_right :
          chartImage ψ T ⊓ chartImage ψ U ≤ _) ≫ localHom ψ U := by
  rw [← cancel_epi ((relativeProj B).scheme.isoOfEq (chartImage_inf_eq_iSup ψ T U)).inv]
  exact (Scheme.Opens.iSupOpenCover
    (fun W' : {W' : AffineOpen S // W'.1 ≤ T.1 ⊓ U.1} => chartImage ψ W'.1)).hom_ext _ _
      fun W => homOfLE_le_iSup_comp_localHom_eq ψ T U W

/-! ### The morphism -/

/-- **Tag 07ZG, assertion (2).** The morphism `U(ψ) ⟶ Proj_S(A)` induced by a homomorphism of
quasi-coherent graded `𝒪_S`-algebras on the open subscheme of `Proj_S(B)` where it is defined.

It is glued from the absolute morphisms of Tag 01MY over the affine opens of the base. -/
@[ega "II 3.5.1"]
public def relativeMapHom : ψ.relativeMapDomain.toScheme ⟶ (relativeProj A).scheme :=
  (Scheme.Opens.iSupOpenCover (chartImage ψ)).glueMorphisms (localHom ψ) fun T U => by
    dsimp only [Scheme.Opens.iSupOpenCover]
    rw [← cancel_epi (AlgebraicGeometry.isPullback_opens_inf_le
        (le_iSup (chartImage ψ) T) (le_iSup (chartImage ψ) U)).isoPullback.hom,
      ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_fst,
      ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_snd]
    exact homOfLE_inf_comp_localHom ψ T U

/-- **The defining equation of the morphism**: on the piece over an affine open of the base it is
the local morphism. -/
@[reassoc]
public theorem homOfLE_comp_relativeMapHom (U : AffineOpen S) :
    (relativeProj B).scheme.homOfLE (chartImage_le ψ U) ≫ relativeMapHom ψ =
      localHom ψ U :=
  (Scheme.Opens.iSupOpenCover (chartImage ψ)).ι_glueMorphisms _ _ U

/-- **The affine-local characterization of Tag 07ZG's morphism.** Read through the chart over an
affine open `U` of the base, `r_ψ` is the absolute morphism `U(ψ_U) ⟶ Proj Γ(U, A)` of Tag 01MY
followed by the chart of `Proj_S(A)` over `U`. -/
public theorem chart_comp_relativeMapHom (U : AffineOpen S) :
    (((relativeProj B).chart U.1 U.2).isoImage
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).hom ≫
        (relativeProj B).scheme.homOfLE (chartImage_le ψ U) ≫ relativeMapHom ψ =
      mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
        (relativeProj A).chart U.1 U.2 := by
  rw [homOfLE_comp_relativeMapHom ψ U, localHom, Iso.hom_inv_id_assoc]

/-- Two morphisms out of `U(ψ)` agree as soon as they agree on each piece. -/
public theorem relativeMapDomain_hom_ext {Y : Scheme.{u}}
    (p q : ψ.relativeMapDomain.toScheme ⟶ Y)
    (H : ∀ U : AffineOpen S,
      (relativeProj B).scheme.homOfLE (chartImage_le ψ U) ≫ p =
        (relativeProj B).scheme.homOfLE (chartImage_le ψ U) ≫ q) :
    p = q :=
  (Scheme.Opens.iSupOpenCover (chartImage ψ)).hom_ext p q H

/-- **The morphism of Tag 07ZG is a morphism over the base.** Checked on the pieces, where it is
the fact that the absolute morphism of Tag 01MY is a morphism over the affine open. -/
public theorem relativeMapHom_comp_toBase :
    relativeMapHom ψ ≫ (relativeProj A).toBase =
      ψ.relativeMapDomain.ι ≫ (relativeProj B).toBase := by
  refine relativeMapDomain_hom_ext ψ _ _ fun U => ?_
  rw [← Category.assoc, homOfLE_comp_relativeMapHom ψ U, ← Category.assoc, Scheme.homOfLE_ι,
    localHom]
  simp only [Category.assoc]
  rw [chart_comp_toBase A U.1 U.2, mapHom_comp_projInclusionToOpen_assoc ψ U.1 U.2,
    ← chart_comp_toBase B U.1 U.2, Scheme.Hom.isoImage_inv_ι_assoc]

/-! ### The characterization in the shape the source states it -/

/-- **The canonical identification of the piece of `U(ψ)` over an affine open `W` of the base with
the chart domain over `W`.** The piece is `U(ψ) ⊓ q⁻¹(W)`, the chart identifies `q⁻¹(W)` with
`Proj Γ(W, B)`, and under that identification the piece is `U(ψ_W)`. -/
public def chartPieceIso (U : AffineOpen S) :
    (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).toScheme ≅
      (ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1)).toScheme :=
  ((relativeProj B).chart U.1 U.2).isoImage
      (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)) ≪≫
    (relativeProj B).scheme.isoOfEq (chartImage_eq_inf ψ U)

/-- Passing from the chart-image description of the piece to the description as `U(ψ) ⊓ q⁻¹(W)`
does not change its inclusion into `U(ψ)`. -/
@[reassoc]
public theorem isoOfEq_hom_comp_homOfLE_inf (U : AffineOpen S) :
    ((relativeProj B).scheme.isoOfEq (chartImage_eq_inf ψ U)).hom ≫
        (relativeProj B).scheme.homOfLE
          (inf_le_left : ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) ≤ _) =
      (relativeProj B).scheme.homOfLE (chartImage_le ψ U) := by
  rw [← cancel_mono ψ.relativeMapDomain.ι, Category.assoc, Scheme.homOfLE_ι,
    Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]

/-- **The affine-local characterization of Tag 07ZG's morphism, in the shape the source states
it.** Over an affine open `W` of the base, the restriction of `r_ψ` to `U(ψ) ⊓ q⁻¹(W)` is, under
the canonical identification of that open with `U(ψ_W)`, the absolute morphism
`U(ψ_W) ⟶ Proj Γ(W, A)` of Tag 01MY followed by the chart of `Proj_S(A)` over `W`. -/
public theorem chartPieceIso_hom_comp_homOfLE_comp_relativeMapHom (U : AffineOpen S) :
    (chartPieceIso ψ U).hom ≫
        (relativeProj B).scheme.homOfLE
            (inf_le_left : ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) ≤ _) ≫
          relativeMapHom ψ =
      mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
        (relativeProj A).chart U.1 U.2 := by
  rw [chartPieceIso, Iso.trans_hom, Category.assoc,
    isoOfEq_hom_comp_homOfLE_inf_assoc ψ U (relativeMapHom ψ)]
  exact chart_comp_relativeMapHom ψ U

/-- **The affine-local characterization determines the morphism.** A morphism out of `U(ψ)` whose
restriction to every piece is the absolute morphism of Tag 01MY, read through the chart, is
`r_ψ`. -/
public theorem relativeMapHom_unique (r : ψ.relativeMapDomain.toScheme ⟶ (relativeProj A).scheme)
    (hr : ∀ U : AffineOpen S,
      (((relativeProj B).chart U.1 U.2).isoImage
            (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).hom ≫
          (relativeProj B).scheme.homOfLE (chartImage_le ψ U) ≫ r =
        mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
          (relativeProj A).chart U.1 U.2) :
    r = relativeMapHom ψ := by
  refine relativeMapDomain_hom_ext ψ _ _ fun U => ?_
  rw [← cancel_epi (((relativeProj B).chart U.1 U.2).isoImage
    (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).hom, hr U,
    chart_comp_relativeMapHom ψ U]

end Stacks.AlgebraicGeometry.Tag07ZGMorphism

end

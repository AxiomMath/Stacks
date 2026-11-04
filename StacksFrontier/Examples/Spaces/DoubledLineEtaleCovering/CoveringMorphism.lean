module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.CoproductFold
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionNotSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ClassGroupOfUniversalHomeomorphismToLine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionDisjointUnion
public import StacksFrontier.Examples.GroupSchemes.DoubleGlue
public import StacksFrontier.Examples.Spaces.AffineOverSpaceNoImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The doubled-origin covering of the involution quotient

Stacks 05ZI covers the algebraic space `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` of Stacks 05Z6 by the
affine line with its origin doubled, the scheme of Stacks 01JD: writing `Y = Y₁ ∪ Y₂` with
`Yᵢ = 𝐀¹_k` glued along `𝐀¹_k ∖ \{0\}`, the first chart is sent to `X` by the chart
`𝐀¹_k ⟶ X` of Stacks 05Z6 and the second by negation of the coordinate followed by that same
chart. The two prescriptions agree over the overlap of the charts, so they glue to a morphism
`Y ⟶ X`.

This file builds `Y` and that morphism. The gluing step is the sheaf condition of the quotient
on the Zariski covering of `Y` by its two charts: the two charts are jointly surjective open
immersions, hence an fppf covering of the site, and `X` is a sheaf there.

## Main definitions

* `AlgebraicGeometry.AffineLineInvolution.doubledLineData`: the affine line with its origin
  doubled, as two copies of the chart `𝐀¹_k` of Stacks 05Z6 glued along the punctured affine
  line, together with its two charts.
* `AlgebraicGeometry.AffineLineInvolution.doubledLine`: the resulting scheme over the ground
  field, and `AlgebraicGeometry.AffineLineInvolution.doubledLineChart` its two charts.
* `AlgebraicGeometry.AffineLineInvolution.doubledLineSite`,
  `AlgebraicGeometry.AffineLineInvolution.doubledChartHom` and
  `AlgebraicGeometry.AffineLineInvolution.doubledProjHom`: the same, as an object of a big
  fppf site containing `Spec k`, two of its morphisms, and the retraction of which the two
  charts are sections.
* `AlgebraicGeometry.AffineLineInvolution.doubledChartQuotientMap`: the two prescriptions on
  the charts, the identity on the first and negation of the coordinate on the second.
* `AlgebraicGeometry.AffineLineInvolution.coveringMorphism`: **the morphism `Y ⟶ X` of
  Stacks 05ZI.**

## Main results

* `AlgebraicGeometry.AffineLineInvolution.ofArrows_doubledChartHom_mem_topology`: the two
  charts of `Y` generate a covering sieve of the big fppf site.
* `AlgebraicGeometry.AffineLineInvolution.isSheafFor_involutionQuotient_doubledChartHom`: the
  sheaf condition of the quotient of Stacks 05Z6 on that covering.
* `AlgebraicGeometry.AffineLineInvolution.coveringMorphismData`: the morphism `Y ⟶ X` together
  with its two chart equations, and
  `AlgebraicGeometry.AffineLineInvolution.eq_coveringMorphism_of_doubledChartHom_comp`: it is
  the only morphism with those equations.

## Implementation notes

`Y` is produced by `Stacks.Examples.doubleSectionCover`, which glues two copies of a scheme
along an open subscheme; it is applied to the chart `𝐀¹_k` of Stacks 05Z6 and to its punctured
open `AlgebraicGeometry.AffineLineInvolution.puncturedAffineLineOpen`. Presenting `Y` this way,
rather than as `AlgebraicGeometry.affineSpaceWithDoubledZero` at `n = 1`, keeps the two charts
of `Y` *equal as schemes over the ground field* to the chart of Stacks 05Z6, which is what lets
the overlap identity
`AlgebraicGeometry.AffineLineInvolution.yoneda_puncturedChart_comp_quotientChart` be applied
without a comparison of the two presentations of the affine line, `AffineSpace PUnit (Spec k)`
and `Spec k[x]`.

Both facts that the gluing needs come with that construction: the two charts are jointly
surjective open immersions, by `Stacks.Examples.SectionCoverData.exists_chart_eq` and
`Stacks.Examples.SectionCoverData.isOpenImmersion_chart`, and their fibre product over `Y` is
the punctured line included in either chart in the standard way, by
`Stacks.Examples.doubleSectionCover_isPullback_chart`. Because *both* legs of that fibre
product are the same inclusion, two morphisms of the site into the chart whose composites with
the two distinct charts of `Y` agree are in fact *equal*, and factor through the punctured
line; that is `AlgebraicGeometry.AffineLineInvolution.eq_and_exists_punctured_factor`, and it
reduces the compatibility condition of the gluing to the overlap identity. For two equal
labels the same conclusion is immediate from the two charts being sections of
`AlgebraicGeometry.AffineLineInvolution.doubledProjHom`.

`Y` meets the size cutoff of the site because its structure morphism to the affine line is of
finite type: it is locally of finite type by `Stacks.Examples.SectionCoverData.proj_prop`, that
property being Zariski local at the source and holding for the identity, and quasi-compact by
`Stacks.Examples.SectionCoverData.quasiCompact_proj`, the affine line being a compact
quasi-separated space.

Morphisms of the site are produced and computed through `AlgebraicGeometry.BigFppfOver.homMk`
and `AlgebraicGeometry.BigFppfOver.toScheme_map_homMk`, and identities between them are
proved by `AlgebraicGeometry.BigFppfOver.map_toScheme_injective`, so that every equation is
checked in the category of schemes. Rewriting across `CategoryTheory.Over.post` is avoided for
the reason recorded on
`AlgebraicGeometry.AffineLineInvolution.yoneda_puncturedChart_comp_quotientChart`: the target
of that functor is only definitionally the category of `Spec k`-schemes in which the affine
line lives.

## References

* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
* [Stacks Project, Tag 05ZI](https://stacks.math.columbia.edu/tag/05ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Examples Stacks.Examples.AffineOverAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

/-! ### The affine line with its origin doubled -/

/-- **Stacks 05ZI.** The affine line with its origin doubled: two copies of the chart `𝐀¹_k`
of Stacks 05Z6, glued along the punctured affine line, together with its two charts. -/
@[ega "IV 18.2.10"]
noncomputable abbrev doubledLineData : SectionCoverData (affineLine k).left :=
  doubleSectionCover (affineLine k).left (puncturedAffineLineOpen k)

/-- **Stacks 05ZI.** The affine line with its origin doubled, as a scheme over the ground
field. -/
@[ega "I 5.5.11"]
noncomputable abbrev doubledLine : Over (Spec (.of k)) :=
  Over.mk ((doubledLineData k).proj ≫ (affineLine k).hom)

/-- The two charts of the affine line with doubled origin, as morphisms of schemes over the
ground field. -/
noncomputable def doubledLineChart (b : Bool) : affineLine k ⟶ doubledLine k :=
  Over.homMk ((doubledLineData k).chart b) (by
    change (doubledLineData k).chart b ≫ (doubledLineData k).proj ≫ (affineLine k).hom =
      (affineLine k).hom
    rw [← Category.assoc, (doubledLineData k).chart_comp_proj, Category.id_comp])

/-- The underlying morphism of schemes of the `b`-th chart of the doubled line. -/
@[simp]
theorem doubledLineChart_left (b : Bool) :
    (doubledLineChart k b).left = (doubledLineData k).chart b := rfl

/-- The two charts of the affine line with doubled origin agree over the punctured line. -/
theorem puncturedAffineLineInclusion_comp_doubledLineChart :
    puncturedAffineLineInclusion k ≫ doubledLineChart k true =
      puncturedAffineLineInclusion k ≫ doubledLineChart k false :=
  Over.OverMorphism.ext
    (doubleSectionCover_chart_agree (affineLine k).left (puncturedAffineLineOpen k))

/-- **The overlap of the two charts of the doubled line is the punctured affine line**, included
in either chart in the standard way: both legs of the fibre product are that inclusion, because
the two copies are glued by the identity. -/
theorem isPullback_doubledLineChart {b c : Bool} (hbc : b ≠ c) :
    IsPullback (puncturedAffineLineOpen k).ι (puncturedAffineLineOpen k).ι
      ((doubledLineData k).chart b) ((doubledLineData k).chart c) :=
  doubleSectionCover_isPullback_chart (affineLine k).left (puncturedAffineLineOpen k) hbc

/-! ### Negation of the coordinate preserves the punctured line -/

/-- The nonvanishing locus of the negative of the standard coordinate is the punctured line:
the two sections differ by the unit `-1`. -/
theorem basicOpen_neg_coord :
    (affineLine k).left.basicOpen (-(AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
      puncturedAffineLineOpen k := by
  rw [neg_eq_neg_one_mul, Scheme.basicOpen_mul,
    (affineLine k).left.basicOpen_of_isUnit (isUnit_one.neg), top_inf_eq]

/-- Negation of the coordinate carries the punctured affine line into itself. -/
theorem range_puncturedAffineLineOpen_ι_comp_affineLineNeg :
    Set.range ((puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left).base ⊆
      ((puncturedAffineLineOpen k : (affineLine k).left.Opens) : Set _) := by
  have hneg : (affineLineNeg k).left ⁻¹ᵁ puncturedAffineLineOpen k =
      puncturedAffineLineOpen k := by
    change (affineLineNeg k).left ⁻¹ᵁ
      ((affineLine k).left.basicOpen (AffineSpace.coord (Spec (.of k)) PUnit.unit)) = _
    rw [Scheme.preimage_basicOpen_top, affineLineNeg_left,
      AffineSpace.homOfVector_appTop_coord, basicOpen_neg_coord]
  have hpre : ((puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left) ⁻¹ᵁ
      puncturedAffineLineOpen k = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hneg, Scheme.Opens.ι_preimage_self]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ ((puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left) ⁻¹ᵁ
      puncturedAffineLineOpen k := by rw [hpre]; trivial
  exact hx

/-- Negation of the coordinate carries the punctured affine line into itself, read as an
inclusion of the ranges of the two inclusions. -/
theorem range_subset_range_puncturedAffineLineOpen_ι :
    Set.range ((puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left).base ⊆
      Set.range ((puncturedAffineLineOpen k).ι).base := by
  rw [Scheme.Opens.range_ι]
  exact range_puncturedAffineLineOpen_ι_comp_affineLineNeg k

/-! ### The two sheets of the covering are disjoint -/

/-- **Away from characteristic two the inclusion of the punctured affine line and its composite
with negation of the coordinate agree nowhere.** On a scheme over the ground field where they
agree, the pullback of the standard coordinate is a section equal to its own negative, hence
zero because two is invertible in the ground field; but that same section has the whole scheme
as its nonvanishing locus, so the scheme is empty. -/
theorem isEmpty_of_comp_puncturedAffineLineOpen_ι_eq (hchar : (2 : k) ≠ 0) {W : Scheme.{u}}
    (p : W ⟶ Spec (.of k)) (w : W ⟶ (puncturedAffineLineOpen k).toScheme)
    (h : w ≫ (puncturedAffineLineOpen k).ι =
      w ≫ (puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left) :
    IsEmpty W := by
  have hneg : (affineLineNeg k).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      -AffineSpace.coord (Spec (.of k)) PUnit.unit := by
    rw [affineLineNeg_left]
    exact AffineSpace.homOfVector_appTop_coord _ _ _
  set g := w ≫ (puncturedAffineLineOpen k).ι with hgdef
  set s := g.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) with hsdef
  have hss : s = -s := by
    have hh := congrArg
      (fun z : W ⟶ (affineLine k).left =>
        z.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hh
    rw [hneg, map_neg, map_neg] at hh
    exact hh
  have hunit : IsUnit (2 : Γ(W, ⊤)) := by
    have h2 : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr hchar
    have hmap : IsUnit ((p.appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom (2 : k))) :=
      (h2.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom).map (p.appTop).hom
    rwa [map_ofNat, map_ofNat] at hmap
  have hs0 : s = 0 := hunit.mul_right_eq_zero.mp
    ((two_mul s).trans (add_eq_zero_iff_eq_neg.mpr hss))
  have htop : W.basicOpen s = ⊤ := by
    rw [hsdef, ← Scheme.preimage_basicOpen_top, hgdef, Scheme.Hom.comp_preimage]
    change w ⁻¹ᵁ ((puncturedAffineLineOpen k).ι ⁻¹ᵁ puncturedAffineLineOpen k) = ⊤
    rw [Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  rw [hs0, Scheme.basicOpen_zero] at htop
  refine Set.univ_eq_empty_iff.mp ?_
  simpa using congrArg (fun U : W.Opens => (U : Set W)) htop.symm

/-! ### The doubled line as an object of the site -/

variable (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

include hk in
/-- The affine line with doubled origin satisfies the size cutoff of a big fppf site containing
`Spec k`: it is of finite type over the affine line, which is an object of the site. -/
theorem contains_doubledLine : B.Contains (doubledLine k).left := by
  have : LocallyOfFiniteType (doubledLineData k).proj :=
    (doubledLineData k).proj_prop _
      (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType))
      inferInstance
  have : QuasiCompact (doubledLineData k).proj := (doubledLineData k).quasiCompact_proj
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (doubledLineData k).proj
    (contains_affineLine k B hk)

/-- The affine line with doubled origin, as an object of a big fppf site containing
`Spec k`. -/
noncomputable def doubledLineSite : BigFppfOver B (Spec (.of k)) hk :=
  BigFppfOver.mk B (Spec (.of k)) hk (contains_doubledLine k B hk) (doubledLine k).hom

/-- The doubled line as an object of the site lies over the doubled line as a scheme over `k`. -/
@[simp]
theorem doubledLineSite_post :
    (Over.post B.inclusion).obj (doubledLineSite k B hk) = doubledLine k := rfl

/-- The two charts of the affine line with doubled origin, as morphisms of the site. -/
noncomputable def doubledChartHom (b : Bool) :
    affineLineChart k B hk ⟶ doubledLineSite k B hk :=
  BigFppfOver.homMk B (Spec (.of k)) hk (contains_doubledLine k B hk) (doubledLine k).hom
    ((doubledLineData k).chart b) (by
      change (doubledLineData k).chart b ≫ (doubledLineData k).proj ≫ (affineLine k).hom =
        (affineLine k).hom
      rw [← Category.assoc, (doubledLineData k).chart_comp_proj, Category.id_comp])

/-- The underlying morphism of schemes of the `b`-th chart of the doubled line in the site. -/
@[simp]
theorem toScheme_map_doubledChartHom (b : Bool) :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (doubledChartHom k B hk b) =
      (doubledLineData k).chart b :=
  BigFppfOver.toScheme_map_homMk B (Spec (.of k)) hk _ _ _ _

/-- The structure morphism of the doubled line over the affine line, as a morphism of the
site. -/
noncomputable def doubledProjHom : doubledLineSite k B hk ⟶ affineLineChart k B hk :=
  BigFppfOver.homMk B (Spec (.of k)) hk (contains_affineLine k B hk) (affineLine k).hom
    (doubledLineData k).proj rfl

/-- The underlying morphism of schemes of `doubledProjHom` is the projection of the doubled
line. -/
@[simp]
theorem toScheme_map_doubledProjHom :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (doubledProjHom k B hk) =
      (doubledLineData k).proj :=
  BigFppfOver.toScheme_map_homMk B (Spec (.of k)) hk _ _ _ _

/-- Each chart of the doubled line is a section of its structure morphism over the affine
line, read on the morphisms of the site. -/
theorem doubledChartHom_comp_doubledProjHom (b : Bool) :
    doubledChartHom k B hk b ≫ doubledProjHom k B hk = 𝟙 (affineLineChart k B hk) := by
  have hmap : (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (doubledChartHom k B hk b ≫ doubledProjHom k B hk) =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (𝟙 (affineLineChart k B hk)) := by
    simp only [Functor.map_comp, toScheme_map_doubledChartHom,
      toScheme_map_doubledProjHom]
    exact (doubledLineData k).chart_comp_proj b
  exact BigFppfOver.map_toScheme_injective B (Spec (.of k)) hk hmap

/-- **The two charts of the doubled line are a covering of the big fppf site.** They are
jointly surjective open immersions, hence a Zariski, hence an fppf, covering. -/
theorem ofArrows_doubledChartHom_mem_topology :
    Sieve.ofArrows (fun _ : Bool => affineLineChart k B hk) (doubledChartHom k B hk) ∈
      BigFppfOver.topology B (Spec (.of k)) hk (doubledLineSite k B hk) := by
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B (Spec (.of k)) hk
    (doubledChartHom k B hk) (fun b => ?_) (fun x => ?_)
  · rw [toScheme_map_doubledChartHom k B hk b]
    exact (doubledLineData k).isOpenImmersion_chart b
  · obtain ⟨b, y, hy⟩ := (doubledLineData k).exists_chart_eq x
    refine ⟨b, ?_⟩
    rw [toScheme_map_doubledChartHom k B hk b]
    exact ⟨y, hy⟩

/-! ### The overlap of two distinct charts -/

/-- **Two morphisms of the site into the chart `𝐀¹_k` whose composites with two distinct charts
of the doubled line agree are equal, and factor through the punctured line.** Both legs of the
fibre product of the two charts are the inclusion of the punctured line, so the lift through
that fibre product is a common factorization of the two morphisms. -/
theorem eq_and_exists_punctured_factor {b c : Bool} (hbc : b ≠ c)
    {Z : BigFppfOver B (Spec (.of k)) hk} (s t : Z ⟶ affineLineChart k B hk)
    (h : s ≫ doubledChartHom k B hk b = t ≫ doubledChartHom k B hk c) :
    s = t ∧ ∃ q : Z ⟶ puncturedAffineLineChart k B hk,
      q ≫ puncturedChartInclusion k B hk = s := by
  have hleft : (BigFppfOver.toScheme B (Spec (.of k)) hk).map s ≫ (doubledLineData k).chart b =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map t ≫ (doubledLineData k).chart c := by
    have h' := congrArg (BigFppfOver.toScheme B (Spec (.of k)) hk).map h
    simp only [Functor.map_comp, toScheme_map_doubledChartHom] at h'
    exact h'
  have P := isPullback_doubledLineChart k hbc
  obtain ⟨q₀, hq₁, hq₂⟩ : ∃ q₀ : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj Z ⟶
        (puncturedAffineLineOpen k).toScheme,
      q₀ ≫ (puncturedAffineLineOpen k).ι =
          (BigFppfOver.toScheme B (Spec (.of k)) hk).map s ∧
        q₀ ≫ (puncturedAffineLineOpen k).ι =
          (BigFppfOver.toScheme B (Spec (.of k)) hk).map t :=
    ⟨P.lift _ _ hleft, P.lift_fst _ _ _, P.lift_snd _ _ _⟩
  have hws : (BigFppfOver.toScheme B (Spec (.of k)) hk).map s ≫ (affineLine k).hom =
      B.inclusion.map Z.hom := by
    have hw := congrArg B.inclusion.map (Over.w s)
    rwa [Functor.map_comp] at hw
  have hwq : q₀ ≫ (puncturedAffineLine k).hom = B.inclusion.map Z.hom := by
    change q₀ ≫ (puncturedAffineLineOpen k).ι ≫ (affineLine k).hom = _
    rw [← Category.assoc, hq₁]
    exact hws
  obtain ⟨q, hq⟩ : ∃ q : Z ⟶ puncturedAffineLineChart k B hk,
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map q = q₀ :=
    ⟨BigFppfOver.homMk B (Spec (.of k)) hk (contains_puncturedAffineLine k B hk)
      (puncturedAffineLine k).hom q₀ hwq,
      BigFppfOver.toScheme_map_homMk B (Spec (.of k)) hk _ _ _ _⟩
  have hfac : (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (q ≫ puncturedChartInclusion k B hk) =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map s := by
    rw [Functor.map_comp, hq, toScheme_map_puncturedChartInclusion]
    exact hq₁
  exact ⟨BigFppfOver.map_toScheme_injective B (Spec (.of k)) hk (hq₁.symm.trans hq₂), q,
    BigFppfOver.map_toScheme_injective B (Spec (.of k)) hk hfac⟩

/-! ### The morphism `Y ⟶ X` -/

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-- The two prescriptions on the charts of the doubled line: the chart `𝐀¹_k ⟶ X` of
Stacks 05Z6 on the first chart, and negation of the coordinate followed by that chart on the
second. -/
noncomputable def doubledChartQuotientMap (b : Bool) :
    yoneda.obj (affineLineChart k B hk) ⟶ (involutionQuotient k B hk).obj :=
  bif b then yoneda.map (chartNeg k B hk) ≫ quotientChart k B hk else quotientChart k B hk

/-- On the first chart the prescription is the chart `𝐀¹_k ⟶ X`. -/
@[simp]
theorem doubledChartQuotientMap_false :
    doubledChartQuotientMap k B hk false = quotientChart k B hk := rfl

/-- On the second chart the prescription is negation followed by the chart `𝐀¹_k ⟶ X`. -/
@[simp]
theorem doubledChartQuotientMap_true :
    doubledChartQuotientMap k B hk true =
      yoneda.map (chartNeg k B hk) ≫ quotientChart k B hk := rfl

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The inclusion of the punctured affine line into the affine line, read on the schemes over
the ground field. -/
@[simp]
theorem post_puncturedChartInclusion :
    (Over.post (X := B.obj hk) B.inclusion).map (puncturedChartInclusion k B hk) =
      puncturedAffineLineInclusion k :=
  (Over.post (X := B.obj hk) B.inclusion).map_preimage
    (X := puncturedAffineLineChart k B hk) (Y := affineLineChart k B hk)
    (puncturedAffineLineInclusion k)

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The inclusion of the punctured affine line followed by negation of the coordinate, read on
the schemes over the ground field. -/
@[simp]
theorem post_puncturedChartNeg :
    (Over.post (X := B.obj hk) B.inclusion).map (puncturedChartNeg k B hk) =
      puncturedAffineLineInclusion k ≫ affineLineNeg k :=
  (Over.post (X := B.obj hk) B.inclusion).map_preimage
    (X := puncturedAffineLineChart k B hk) (Y := affineLineChart k B hk)
    (puncturedAffineLineInclusion k ≫ affineLineNeg k)

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Negation of the coordinate on the punctured line is the inclusion of the punctured line
followed by negation on the affine line, read on the morphisms of the site. -/
theorem puncturedChartNeg_eq_comp :
    puncturedChartNeg k B hk = puncturedChartInclusion k B hk ≫ chartNeg k B hk := by
  refine (Over.post (X := B.obj hk) B.inclusion).map_injective ?_
  simp only [Functor.map_comp, post_puncturedChartNeg, post_puncturedChartInclusion,
    post_chartNeg]
  rfl

/-- **The sheaf condition of the quotient of Stacks 05Z6 on the Zariski covering of the doubled
line by its two charts.** This is what the gluing of the two chart maps of Stacks 05ZI needs. -/
theorem isSheafFor_involutionQuotient_doubledChartHom :
    (Presieve.ofArrows (fun _ : Bool => affineLineChart k B hk)
        (doubledChartHom k B hk)).IsSheafFor (involutionQuotient k B hk).obj :=
  ((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B (Spec (.of k)) hk) _).1
      (involutionQuotient k B hk).property).isSheafFor _
    (ofArrows_doubledChartHom_mem_topology k B hk)

/-- **The gluing datum of the covering of Stacks 05ZI.** The two prescriptions on the charts of
the doubled line agree on every common refinement of the two charts, which is what the sheaf
condition asks in order to glue them. -/
theorem doubledChartQuotientMap_compatible (b c : Bool)
    (Z : BigFppfOver B (Spec (.of k)) hk) (s : Z ⟶ affineLineChart k B hk)
    (t : Z ⟶ affineLineChart k B hk)
    (h : s ≫ doubledChartHom k B hk b = t ≫ doubledChartHom k B hk c) :
    yoneda.map s ≫ doubledChartQuotientMap k B hk b =
      yoneda.map t ≫ doubledChartQuotientMap k B hk c := by
  by_cases hbc : b = c
  · subst hbc
    have h₁ := congrArg (fun z => z ≫ doubledProjHom k B hk) h
    simp only [Category.assoc, doubledChartHom_comp_doubledProjHom, Category.comp_id] at h₁
    rw [h₁]
  · obtain ⟨hst, q, hq⟩ := eq_and_exists_punctured_factor k B hk hbc s t h
    have key : yoneda.map s ≫ quotientChart k B hk =
        yoneda.map s ≫ yoneda.map (chartNeg k B hk) ≫ quotientChart k B hk :=
      calc yoneda.map s ≫ quotientChart k B hk
          = yoneda.map (q ≫ puncturedChartInclusion k B hk) ≫ quotientChart k B hk := by
            rw [hq]
        _ = yoneda.map q ≫ yoneda.map (puncturedChartInclusion k B hk) ≫
              quotientChart k B hk := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map q ≫ yoneda.map (puncturedChartNeg k B hk) ≫ quotientChart k B hk := by
            rw [yoneda_puncturedChart_comp_quotientChart]
        _ = yoneda.map q ≫ yoneda.map (puncturedChartInclusion k B hk ≫ chartNeg k B hk) ≫
              quotientChart k B hk := by
            rw [puncturedChartNeg_eq_comp]
        _ = yoneda.map (q ≫ puncturedChartInclusion k B hk) ≫
              yoneda.map (chartNeg k B hk) ≫ quotientChart k B hk := by
            simp only [Functor.map_comp, Category.assoc]
        _ = yoneda.map s ≫ yoneda.map (chartNeg k B hk) ≫ quotientChart k B hk := by rw [hq]
    rw [← hst]
    cases b with
    | false =>
      cases c with
      | false => exact absurd rfl hbc
      | true => exact key
    | true =>
      cases c with
      | false => exact key.symm
      | true => exact absurd rfl hbc

/-- **Stacks 05ZI.** The morphism `Y ⟶ X` from the affine line with doubled origin to the
quotient `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` of Stacks 05Z6, together with its two chart equations:
on the first chart it is the chart `𝐀¹_k ⟶ X` of Stacks 05Z6, and on the second it is negation
of the coordinate followed by that chart. -/
noncomputable def coveringMorphismData :
    { f : yoneda.obj (doubledLineSite k B hk) ⟶ (involutionQuotient k B hk).obj //
      ∀ b : Bool, yoneda.map (doubledChartHom k B hk b) ≫ f =
        doubledChartQuotientMap k B hk b } :=
  have h := Space.exists_glue_of_mem_topology
    (BigFppfOver.topology B (Spec (.of k)) hk) (involutionQuotient k B hk).property
    (fun _ : Bool => affineLineChart k B hk) (doubledChartHom k B hk)
    (ofArrows_doubledChartHom_mem_topology k B hk) (doubledChartQuotientMap k B hk)
    (doubledChartQuotientMap_compatible k B hk)
  ⟨h.choose, h.choose_spec⟩

/-- **Stacks 05ZI.** The morphism `Y ⟶ X` from the affine line with doubled origin to the
quotient of Stacks 05Z6. -/
noncomputable abbrev coveringMorphism :
    yoneda.obj (doubledLineSite k B hk) ⟶ (involutionQuotient k B hk).obj :=
  (coveringMorphismData k B hk).val

/-- On each chart of the doubled line, `coveringMorphism` is the prescribed map. -/
theorem doubledChartHom_comp_coveringMorphism (b : Bool) :
    yoneda.map (doubledChartHom k B hk b) ≫ coveringMorphism k B hk =
      doubledChartQuotientMap k B hk b :=
  (coveringMorphismData k B hk).property b

/-- **The morphism `Y ⟶ X` of Stacks 05ZI is the only one restricting to the two prescriptions
on the charts**: the two charts generate a covering sieve and `X` is a sheaf, so a morphism out
of `Y` is determined by its restrictions to them. -/
theorem eq_coveringMorphism_of_doubledChartHom_comp
    (f : yoneda.obj (doubledLineSite k B hk) ⟶ (involutionQuotient k B hk).obj)
    (hf : ∀ b : Bool, yoneda.map (doubledChartHom k B hk b) ≫ f =
      doubledChartQuotientMap k B hk b) :
    f = coveringMorphism k B hk := by
  refine Space.hom_ext_of_mem_topology (BigFppfOver.topology B (Spec (.of k)) hk)
    (involutionQuotient k B hk).property _
    (ofArrows_doubledChartHom_mem_topology k B hk) fun {Z} e he => ?_
  obtain ⟨b, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ e).1 he
  rw [Functor.map_comp, Category.assoc, Category.assoc, hf b,
    doubledChartHom_comp_coveringMorphism]

end AlgebraicGeometry.AffineLineInvolution

end

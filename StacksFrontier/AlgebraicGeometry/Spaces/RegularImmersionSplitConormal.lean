module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalH1Regular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalKoszulRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalQuasiRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Permanence of the regularity conditions for the first of two immersions of algebraic spaces

Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of algebraic spaces over a scheme `S`, with `j`
locally of finite presentation and with the conormal sequence
`0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of [Stacks Project, Tag 06BD] exact and locally
split.  Then quasi-regularity of `i ≫ j` descends to `i`, `H₁`-regularity of `i ≫ j` descends to
`i`, and `i` is Koszul-regular as soon as both `j` and `i ≫ j` are.  These are the three clauses
of Stacks tag 09S1, the analogue for algebraic spaces of Stacks tag 068Z.

## Main definitions

* `AlgebraicGeometry.Space.IsSplitExactConormalSequenceOnEtaleCharts`: the conormal-sequence
  hypothesis of Stacks tag 09S1, read on the étale scheme charts of `X`.

## Main results

* `AlgebraicGeometry.Space.isQuasiRegularImmersion_of_comp_of_isSplitExactConormalSequence`:
  **Stacks tag 09S1**, clause (1).
* `AlgebraicGeometry.Space.isH1RegularImmersion_of_comp_of_isSplitExactConormalSequence`:
  **Stacks tag 09S1**, clause (2).
* `AlgebraicGeometry.Space.isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence`:
  **Stacks tag 09S1**, clause (3).

## Implementation notes

**The conormal hypothesis is read on étale charts of `X`.**  The conormal sequence of a pair of
immersions of algebraic spaces has no left-hand map in this development: the module
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`, which carries the
surjectivity clause of Stacks tag 06BD, records in its own notes that the sequence
`𝒞_{Y/X} ⊗ 𝒪_Z ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` has no first map there, so there is no object whose
exactness and local splitness could be asserted.  At the scheme level the hypothesis *is*
available, as `Stacks.AlgebraicGeometry.IsSplitExactConormalSequence`, and the development's
standing device for a condition on algebraic spaces is to read the corresponding condition of
schemes on the étale scheme charts of the target: that is how each of the three regularity
predicates of Stacks tag 06BN is defined, and how local finite presentation and the other
conditions of Stacks tag 03MJ are defined.  `IsSplitExactConormalSequenceOnEtaleCharts` applies
that device to the conormal hypothesis.  Over a chart `c` of `X` the pair of scheme immersions is
the base change of `j` to `c` together with the base change of `i` to the chart of `Y` that `j`
pulls back from `c`; those two base changes compose to the base change of `i ≫ j`, which is the
decomposition already used for Stacks tag 09S0 in
`StacksFrontier/AlgebraicGeometry/Spaces/RegularImmersionComposition.lean`.

**From the charts pulled back from `X` to all charts of `Y`.**  The conclusion of each clause is
a condition on *every* étale chart of `Y`, whereas the scheme-level tag 068Z is applied over the
charts of `Y` that `j` pulls back from charts of `X`.  Passing from those charts to all of them
is exactly the equivalence of the two conditions of Stacks tag 06BM, which
`AlgebraicGeometry.Space.property_on_all_etale_charts_iff_exists_atlas` supplies for a property of
scheme morphisms that is étale local on the target.  The locality of the three regularity
conditions is Stacks tag 0694, in the form
`AlgebraicGeometry.isLocalAtTarget_quasiRegularImmersion_etale` and its two companions:  the
condition itself, with no finiteness qualifier, local on the target for the étale topology.

**Algebraicity is a hypothesis here**, unlike in the tags 06BP and 09S0 of this development:  the
surjective étale atlas of `X` is what produces the surjective chart of `Y` over which tag 068Z is
applied, and the atlas of `Y` is what the equivalence of Stacks tag 06BM consumes.  The source
statement does assume that `Z`, `Y` and `X` are algebraic spaces.

The three helpers below reproduce, for a general property of scheme morphisms and in the
direction needed here, the base-change transfer of a chart condition, the comparison
isomorphism between the base change of a composite and the composite of the base changes, and
the passage of Stacks tag 06BM from the charts pulled back from `X` to all charts of `Y`.  The
first two are available in
`StacksFrontier/AlgebraicGeometry/Spaces/RegularImmersionComposition.lean` only as declarations
private to that module.  `AlgebraicGeometry.Space.exists_toSchemeIso_comp` and
`AlgebraicGeometry.Space.forall_etale_chart_of_atlas` are not private here because
`StacksFrontier/AlgebraicGeometry/Spaces/RegularImmersionNoetherianSplitConormal.lean`, which
proves Stacks tag 09S2 from the same decomposition, consumes both.

## References

* [Stacks Project, Lemma 76.44.6 (Tag 09S1)](https://stacks.math.columbia.edu/tag/09S1)
* [Stacks Project, Lemma 31.22.8 (Tag 068Z)](https://stacks.math.columbia.edu/tag/068Z)
* [Stacks Project, Lemma 76.17.11 (Tag 06BD)](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Lemma 76.44.1 (Tag 06BM)](https://stacks.math.columbia.edu/tag/06BM)
* [Stacks Project, Definition 76.44.2 (Tag 06BN)](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Lemma 35.23.3 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The chart condition used as a hypothesis -/

/-- **The conormal-sequence hypothesis of Stacks tag 09S1, read on the étale charts of `X`.**
For representable morphisms `i : Z ⟶ Y` and `j : Y ⟶ X` of algebraic spaces over `S`, the
condition that over every étale scheme chart `c` of `X` the base change of `j` to `c` and the
base change of `i` to the chart of `Y` pulled back from `c` are immersions of schemes whose
conormal sequence is exact and locally split in the sense of
`Stacks.AlgebraicGeometry.IsSplitExactConormalSequence`.

This is the hypothesis of Stacks tag 09S1 in the shape in which the conditions of Stacks tags
06BM, 06BN and 03MJ are stated for algebraic spaces; see the implementation notes of this
module for why the hypothesis is not stated on `X` itself. -/
abbrev IsSplitExactConormalSequenceOnEtaleCharts (i : Z ⟶ Y) (j : Y ⟶ X) : Prop :=
  ∃ (hi : yoneda.relativelyRepresentable i) (hj : yoneda.relativelyRepresentable j),
    ∀ (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      ∃ (hic : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map (hi.snd (hj.fst c))))
        (hjc : _root_.AlgebraicGeometry.IsImmersion
          ((BigFppfOver.toScheme B S hS).map (hj.snd c))),
        @Stacks.AlgebraicGeometry.IsSplitExactConormalSequence _ _ _
          ((BigFppfOver.toScheme B S hS).map (hi.snd (hj.fst c)))
          ((BigFppfOver.toScheme B S hS).map (hj.snd c)) hic hjc

/-! ### The comparison isomorphism -/

/-- **The base change of a composite to a chart is the composite of the base changes.**  For a
morphism `c` from a representable presheaf to `X` the canonical represented base change of
`i ≫ j` along `c` is isomorphic, over the two factors, to the base change of `i` along the
morphism `hj.fst c` followed by the base change of `j` along `c`. -/
theorem exists_toSchemeIso_comp {i : Z ⟶ Y} {j : Y ⟶ X}
    (hi : yoneda.relativelyRepresentable i) (hj : yoneda.relativelyRepresentable j)
    (hij : yoneda.relativelyRepresentable (i ≫ j)) {V : BigFppfOver B S hS}
    (c : yoneda.obj V ⟶ X) :
    ∃ e : (BigFppfOver.toScheme B S hS).obj (hij.pullback c) ≅
        (BigFppfOver.toScheme B S hS).obj (hi.pullback (hj.fst c)),
      e.hom ≫ ((BigFppfOver.toScheme B S hS).map (hi.snd (hj.fst c)) ≫
          (BigFppfOver.toScheme B S hS).map (hj.snd c)) =
        (BigFppfOver.toScheme B S hS).map (hij.snd c) := by
  have hOuter : IsPullback (hi.fst (hj.fst c))
      (yoneda.map (hi.snd (hj.fst c) ≫ hj.snd c)) (i ≫ j) c := by
    simpa only [Functor.map_comp] using
      ((hi.isPullback (hj.fst c)).flip.paste_horiz (hj.isPullback c).flip).flip
  have hPB := hij.isPullback c
  refine ⟨(BigFppfOver.toScheme B S hS).mapIso
    (yoneda.preimageIso (hPB.isoIsPullback _ _ hOuter)), ?_⟩
  have he : (yoneda.preimageIso (hPB.isoIsPullback _ _ hOuter)).hom ≫
      (hi.snd (hj.fst c) ≫ hj.snd c) = hij.snd c := by
    apply yoneda.map_injective
    rw [Functor.map_comp]
    simpa only [Functor.preimageIso_hom, Functor.map_preimage] using
      hPB.isoIsPullback_hom_snd _ _ hOuter
  simpa only [Functor.mapIso_hom, Functor.map_comp] using
    congrArg (BigFppfOver.toScheme B S hS).map he

/-- **From the charts of `Y` pulled back from `X` to all charts of `Y`.**  Let `P` be a property
of scheme morphisms which is étale local on the target.  If the base change of `i` to the chart
of `Y` that `j` pulls back from a surjective étale chart of `X` has `P`, then the base change of
`i` to every étale chart of `Y` has `P`.

This is the implication from condition (2) to condition (1) of Stacks tag 06BM, applied to the
chart of `Y` produced by an atlas of `X`:  a surjective étale chart stays surjective and étale
after base change along `j`. -/
theorem forall_etale_chart_of_atlas (P : MorphismProperty Scheme.{u})
    (hP : P.IsLocalAtTarget Scheme.etalePrecoverage)
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) {i : Z ⟶ Y} {j : Y ⟶ X}
    (hi : yoneda.relativelyRepresentable i) (hj : yoneda.relativelyRepresentable j)
    (step : ∀ (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      P ((BigFppfOver.toScheme B S hS).map (hi.snd (hj.fst c)))) :
    ∀ (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c →
      P ((BigFppfOver.toScheme B S hS).map (hi.snd c)) := by
  have := hP
  obtain ⟨V, c, hcSurj, hcEtale⟩ := hX.exists_atlas
  refine (property_on_all_etale_charts_iff_exists_atlas B S hS P hZ hY i hi).mpr
    ⟨hj.pullback c, hj.fst c, presheaf_of_isPullback B S hS (hj.isPullback c).flip hcSurj,
      presheaf_of_isPullback B S hS (hj.isPullback c).flip hcEtale, step V c hcSurj hcEtale⟩

/-! ### The three clauses of Stacks tag 09S1 -/

/-- **Data over an étale chart of `X`.**  The base change of `j` to the chart is locally of finite
presentation, and the base change of `i ≫ j` is isomorphic to the composite of the base changes
of `i` and `j`, compatibly with the maps to the chart. -/
private theorem chart_comp_data {i : Z ⟶ Y} {j : Y ⟶ X}
    (hjfp : IsLocallyOfFinitePresentation B S hS j)
    (hi : yoneda.relativelyRepresentable i) (hj : yoneda.relativelyRepresentable j)
    (hij : yoneda.relativelyRepresentable (i ≫ j)) {W : BigFppfOver B S hS}
    (c : yoneda.obj W ⟶ X)
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (hj.snd c)) ∧
      ∃ e : (BigFppfOver.toScheme B S hS).obj (hi.pullback (hj.fst c)) ≅
          (BigFppfOver.toScheme B S hS).obj (hij.pullback c),
        e.hom ≫ (BigFppfOver.toScheme B S hS).map (hij.snd c) =
          (BigFppfOver.toScheme B S hS).map (hi.snd (hj.fst c)) ≫
            (BigFppfOver.toScheme B S hS).map (hj.snd c) := by
  obtain ⟨e, he⟩ := exists_toSchemeIso_comp B S hS hi hj hij c
  exact ⟨hjfp (hj.pullback c) W (hj.fst c) c (hj.snd c)
      (presheaf_of_isPullback B S hS (hj.isPullback c).flip hc) hc (hj.isPullback c).w.symm,
    e.symm, by rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]⟩

/-- **Stacks tag 09S1, clause (1).**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be representable morphisms
of algebraic spaces over `S` with `j` locally of finite presentation and with the conormal
sequence of Stacks tag 06BD exact and locally split on the étale charts of `X`.  If `i ≫ j` is a
quasi-regular immersion, so is `i`.

The sibling clauses are
`AlgebraicGeometry.Space.isH1RegularImmersion_of_comp_of_isSplitExactConormalSequence`, clause
(2) for `H₁`-regularity, and
`AlgebraicGeometry.Space.isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence`,
clause (3) for Koszul-regularity. -/
@[stacks 09S1 "(1) quasi-regularity descends to the first immersion, with the conormal \
hypothesis read on the étale charts of X"]
theorem isQuasiRegularImmersion_of_comp_of_isSplitExactConormalSequence
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ Y) (j : Y ⟶ X)
    (hjfp : IsLocallyOfFinitePresentation B S hS j)
    (hcon : IsSplitExactConormalSequenceOnEtaleCharts B S hS i j)
    (hij : IsQuasiRegularImmersion B S hS (i ≫ j)) :
    IsQuasiRegularImmersion B S hS i := by
  obtain ⟨hri, hrj, hcharts⟩ := hcon
  obtain ⟨hrij, hijcharts⟩ := hij
  refine ⟨hri, forall_etale_chart_of_atlas B S hS _
    isLocalAtTarget_quasiRegularImmersion_etale.{u} hZ hY hX hri hrj fun W c _ hcEtale => ?_⟩
  obtain ⟨hic, hjc, hseq⟩ := hcharts W c hcEtale
  obtain ⟨hImmOut, hOut⟩ := hijcharts W c hcEtale
  obtain ⟨hlfp, e, heInv⟩ := chart_comp_data B S hS hjfp hri hrj hrij c hcEtale
  have := hic
  have := hjc
  have := hImmOut
  have hcomp : ∃ hf : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hri.snd (hrj.fst c)) ≫
        (BigFppfOver.toScheme B S hS).map (hrj.snd c)),
      @Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion _ _ _ hf := by
    rw [← heInv]
    exact ⟨inferInstance,
      Stacks.AlgebraicGeometry.isQuasiRegularImmersion_iso_hom_comp e _ hOut⟩
  obtain ⟨hfcomp, hcompReg⟩ := hcomp
  have hreg :=
    Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_comp_of_isSplitExactConormalSequence
      _ _ hseq hcompReg
  exact ⟨hic, hreg⟩

/-- **Stacks tag 09S1, clause (2).**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be representable morphisms
of algebraic spaces over `S` with `j` locally of finite presentation and with the conormal
sequence of Stacks tag 06BD exact and locally split on the étale charts of `X`.  If `i ≫ j` is an
`H₁`-regular immersion, so is `i`.

The sibling clauses are
`AlgebraicGeometry.Space.isQuasiRegularImmersion_of_comp_of_isSplitExactConormalSequence`, clause
(1) for quasi-regularity, and
`AlgebraicGeometry.Space.isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence`,
clause (3) for Koszul-regularity. -/
@[stacks 09S1 "(2) H₁-regularity descends to the first immersion, with the conormal hypothesis \
read on the étale charts of X"]
theorem isH1RegularImmersion_of_comp_of_isSplitExactConormalSequence
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ Y) (j : Y ⟶ X)
    (hjfp : IsLocallyOfFinitePresentation B S hS j)
    (hcon : IsSplitExactConormalSequenceOnEtaleCharts B S hS i j)
    (hij : IsH1RegularImmersion B S hS (i ≫ j)) :
    IsH1RegularImmersion B S hS i := by
  obtain ⟨hri, hrj, hcharts⟩ := hcon
  obtain ⟨hrij, hijcharts⟩ := hij
  refine ⟨hri, forall_etale_chart_of_atlas B S hS _
    isLocalAtTarget_h1RegularImmersion_etale.{u} hZ hY hX hri hrj fun W c _ hcEtale => ?_⟩
  obtain ⟨hic, hjc, hseq⟩ := hcharts W c hcEtale
  obtain ⟨hImmOut, hOut⟩ := hijcharts W c hcEtale
  obtain ⟨hlfp, e, heInv⟩ := chart_comp_data B S hS hjfp hri hrj hrij c hcEtale
  have := hic
  have := hjc
  have := hImmOut
  have hcomp : ∃ hf : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hri.snd (hrj.fst c)) ≫
        (BigFppfOver.toScheme B S hS).map (hrj.snd c)),
      @Stacks.AlgebraicGeometry.RegularIdealSheaf.IsH1RegularImmersion _ _ _ hf := by
    rw [← heInv]
    exact ⟨inferInstance,
      Stacks.AlgebraicGeometry.isH1RegularImmersion_iso_hom_comp e _ hOut⟩
  obtain ⟨hfcomp, hcompReg⟩ := hcomp
  have hreg :=
    Stacks.AlgebraicGeometry.isH1RegularImmersion_of_comp_of_isSplitExactConormalSequence
      _ _ hseq hcompReg
  exact ⟨hic, hreg⟩

/-- **Stacks tag 09S1, clause (3).**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be representable morphisms
of algebraic spaces over `S` with `j` locally of finite presentation and with the conormal
sequence of Stacks tag 06BD exact and locally split on the étale charts of `X`.  If both `j` and
`i ≫ j` are Koszul-regular immersions, so is `i`.

The sibling clauses are
`AlgebraicGeometry.Space.isQuasiRegularImmersion_of_comp_of_isSplitExactConormalSequence`, clause
(1) for quasi-regularity, and
`AlgebraicGeometry.Space.isH1RegularImmersion_of_comp_of_isSplitExactConormalSequence`, clause
(2) for `H₁`-regularity. -/
@[stacks 09S1 "(3) Koszul-regularity of the first immersion, with the conormal hypothesis read \
on the étale charts of X"]
theorem isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ Y) (j : Y ⟶ X)
    (hjfp : IsLocallyOfFinitePresentation B S hS j)
    (hcon : IsSplitExactConormalSequenceOnEtaleCharts B S hS i j)
    (hj : IsKoszulRegularImmersion B S hS j)
    (hij : IsKoszulRegularImmersion B S hS (i ≫ j)) :
    IsKoszulRegularImmersion B S hS i := by
  obtain ⟨hri, hrj, hcharts⟩ := hcon
  obtain ⟨hrjkos, hjcharts⟩ := hj
  obtain ⟨hrij, hijcharts⟩ := hij
  refine ⟨hri, forall_etale_chart_of_atlas B S hS _
    isLocalAtTarget_koszulRegularImmersion_etale.{u} hZ hY hX hri hrj fun W c _ hcEtale => ?_⟩
  obtain ⟨hic, hjc, hseq⟩ := hcharts W c hcEtale
  obtain ⟨hImmMid, hMid⟩ := hjcharts W c hcEtale
  obtain ⟨hImmOut, hOut⟩ := hijcharts W c hcEtale
  obtain ⟨hlfp, e, heInv⟩ := chart_comp_data B S hS hjfp hri hrj hrij c hcEtale
  have := hic
  have := hjc
  have := hImmOut
  have hcomp : ∃ hf : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hri.snd (hrj.fst c)) ≫
        (BigFppfOver.toScheme B S hS).map (hrj.snd c)),
      @Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion _ _ _ hf := by
    rw [← heInv]
    exact ⟨inferInstance,
      Stacks.AlgebraicGeometry.isKoszulRegularImmersion_iso_hom_comp e _ hOut⟩
  obtain ⟨hfcomp, hcompReg⟩ := hcomp
  have hreg :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence
      _ _ hseq hMid hcompReg
  exact ⟨hic, hreg⟩

end AlgebraicGeometry.Space

end


module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfFormalSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValuedRefined
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover

/-!
# Charts of a directed colimit: factorization local on the test object

Let `S` be a scheme contained in a big fppf site `B` and let `E : Λ ⥤ FppfSheaf B S hS` be a
directed diagram of fppf sheaves over `S`. The proofs of **Stacks 0AIU** and **Stacks 0GVN**
assemble an atlas of `colim E` out of a system of charts of the stages, and the step which makes
a chart colimit representable étale over `colim E` is the assertion that a scheme-valued point
of `colim E` factors through a stage.

That assertion is **false** for an arbitrary object of the site. The colimit of a directed
diagram of sheaves is only a colimit after sheafification, so a point factors through a stage
only *locally* on the test object: with `E` the system of stages of `Spf k⟦t⟧` and
`U = ⨆ₙ Spec k[t]/tⁿ`, the point `U ⟶ colim E` whose `n`-th component is the `n`-th stage
inclusion factors through no single stage, because `U` is not quasi-compact. It does factor on
each member of the affine open covering of `U`.

This file replaces the global factorization by the local one. The two statements it supplies are

* that a morphism of fppf sheaves whose base change along every point of its target *out of an
  affine object of the site* is an open subscheme of that affine is representable by algebraic
  spaces and étale — so representability and étaleness really are local on the test object; and
* that for a diagram with monomorphic transition morphisms the factorization through a stage
  *holds* for every quasi-compact test object,

and the two combine into a chart-system criterion from which the factorization hypothesis has
disappeared altogether.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_openImmersion_over_affinePoints`:
  a morphism of fppf sheaves over `S` whose base change along every affine point of its target
  is represented by an open subscheme of that affine is representable by algebraic spaces and
  étale.
* `AlgebraicGeometry.FormalSpace.exists_factor_through_stage_of_compact`: a scheme-valued point
  of the colimit of a directed diagram with monomorphic transition morphisms, out of a
  quasi-compact object of the site, factors through a stage.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem`: the chart-system
  criterion of `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem` with the
  factorization hypothesis `hfac` removed, for a diagram with monomorphic transition morphisms
  whose chart morphisms are representable open immersions.

## Implementation notes

*Why open immersions.* The locality argument needs the fibre products over the members of an
affine open covering of a test object `T` to have a coproduct inside the site, and
`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le` produces one from a
*uniform* size bound: the index type and all the members must be bounded by one cardinal below
the site's cutoff. An open subscheme of an affine open of `T` is bounded by `T.size`
(`AlgebraicGeometry.Scheme.size_le_of_isOpenImmersion`), which is the bound `T` itself supplies,
so the open-immersion hypothesis is exactly what makes the coproduct available. It is no
restriction for the intended use: the charts of a stage which is a *scheme* are its affine
opens, transported across the thickenings, and those are open immersions. For a chart which is
merely étale no such bound exists — an algebraic space étale over an affine scheme is an
arbitrary disjoint union of copies of it — which is the set-theoretic phenomenon the condition
of Stacks 0AIS governs.

*Both halves from one construction.* Over the coproduct `V` of the affine opens of `T` the fibre
product is the coproduct of the fibre products over the members, coproducts of sheaves of sets
being van Kampen (`CategoryTheory.Sheaf.nonempty_isColimit_cofanMk_of_isPullback`), hence is
represented by the object `Wt` of the site which is the coproduct of the open subschemes; and
the projection to `V` is the universe-lifted Yoneda image of the morphism `Wt ⟶ V` assembled
from them, which is étale because étaleness is Zariski local on the source. Representability by
algebraic spaces is then locality on the target
(`AlgebraicGeometry.FormalSpace.isRepresentable_of_forall_surjective_etale_cover`) and étaleness
is base change to that chart
(`AlgebraicGeometry.FormalSpace.isEtaleULift_of_targetChart`).

*The factorization for a quasi-compact test object* is
`AlgebraicGeometry.FormalSpace.compact_map_factors_through_filtered_colimit`, which asks only
that the transition morphisms be monomorphisms; a thickening is a closed immersion, hence a
monomorphism, so the hypothesis holds for every diagram the two tags are about.

## What is not done here

`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem` still takes the chart
system itself as data, exactly as
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem` and
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_thickenings` do; what has been
removed from it is the factorization hypothesis, which was the one assertion in those statements
that is not true as quantified.

*Which colimit the two fibre-product tags need.* Stacks 0AJ2 reduces, by two applications of
Stacks 0AJ1 (`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_affineStages`),
to the fibre product of two *affine* formal algebraic spaces `colim Spec A_λ` and
`colim Spec B_μ` over the base `Z`, which is `colim (Spec A_λ ×_Z Spec B_μ)` along thickenings.
What those stages are is decided by *how* the diagonal of `Z` is representable, and that is what
separates the two tags:

* Stacks 0AJ2 asks of `Z` only that its diagonal be representable by **algebraic spaces**, so
  each `Spec A_λ ×_Z Spec B_μ` is an algebraic space and no more. Its chart system therefore
  needs an affine *étale* chart of one stage transported along a thickening of algebraic spaces
  of arbitrary order, which is Stacks 05ZH. This library carries 05ZH only at a **first-order**
  thickening (`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening`;
  every `@[stacks 05ZH]` note in the library says "first-order"), and
  `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEquivalence` records why the
  general case is not an induction on the order: the defining ideal of a thickening need not be
  nilpotent. That hypothesis on `Z` also puts the set-theoretic condition of Stacks 0AIS out of
  reach, since `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_pullback'` asks of
  `Z` that its relative products of representables be representable by **objects of the site**,
  which is strictly stronger than representability of the diagonal by algebraic spaces.
* Stacks 0AJ3 has `Z` a formal algebraic space, and then
  `AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isFormalAlgebraicSpace` and
  `AlgebraicGeometry.FormalSpace.hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace` —
  both unconditional — make the diagonal representable by objects of the site. So each
  `Spec A_λ ×_Z Spec B_μ` is a **scheme**, the set-theoretic condition is discharged by
  `satisfiesSetTheoreticCondition_pullback_of_isFormalAlgebraicSpace`, and
  `isFormalAlgebraicSpace_pullback_of_affineStages_of_representableProducts` leaves exactly one
  input open: that a directed colimit of *schemes* along thickenings is a formal algebraic space.

That last statement is what the criterion below is shaped for. Constructing its chart system
still needs three things this library does not carry:

* the transport of an affine open covering of one stage across the thickenings, as a *functor*
  on the index. The scheme-level ingredients are all present —
  `Stacks.Thickenings.IsThickening.opensCongr` is an order isomorphism of the lattices of opens,
  `Stacks.Thickenings.IsThickening.preimage_opensCongr` identifies the restriction,
  `Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage` preserves affineness and
  `Stacks.Thickenings.IsThickening.morphismRestrict` makes each restricted transition a
  thickening — but the functoriality in the index is not assembled;
* the passage from the index `Λ` to the up-set of the chosen base index, the transported charts
  being defined only there, which is a cofinality statement about a directed preorder;
* the set-theoretic condition of Stacks 0AIS for each chart colimit. Its index is a type of
  `Type (u + 1)`, so `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`
  does not apply for want of the coproduct of the stages inside the site, and
  `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_colimit` does not
  apply for want of countability. What should discharge it is the condition for the colimit
  itself together with the chart being a representable monomorphism into it.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal
open AlgebraicGeometry.FormalSpace.CartesianColimit (equifibered_colimit_isPullback)

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Locality of representable étaleness on the test object -/

/-- **The fibre product over the coproduct of the affine opens of a scheme-valued point.** Let
`Φ : X ⟶ Z` be a morphism of fppf sheaves over `S` whose base change along every point of `Z`
out of an affine object of the site is represented by an open subscheme of that affine. Then
every scheme-valued point `ξ : T ⟶ Z` is covered, surjectively and étale, by one object `V` of
the site over which the base change of `Φ` is represented by an object `Wt` of the site, étale
over `V`.

`V` is the coproduct of the affine opens of `T` and `Wt` the coproduct of the open subschemes
representing the base changes over them; both lie in the site because `T.size` bounds the number
of affine opens of `T` and the size of each, and an open immersion does not raise the size of a
scheme. -/
private theorem exists_representable_etale_pullback_of_openImmersion_over_affinePoints
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z)
    (h : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ Z,
      ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
        (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
        IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p))
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ T) (Wt : BigFppfOver B S hS) (m : Wt ⟶ V)
      (e : (uliftYoneda.{u + 1}).obj Wt ≅ pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map m) ∧
      e.hom ≫ pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom =
        (uliftYoneda.{u + 1}).map m := by
  classical
  let J := BigFppfOver.topology B S hS
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨ι, Xf, V, j, q, hXaff, hjopen, hιsize, hXsize, hqsurj, hqetale, -, ⟨hsheaf⟩⟩ :=
    BigFppfOver.exists_affineOpens_surjective_etale_sigma' B S hS T
  set ξV : J.uliftYoneda.{u + 1}.obj V ⟶ Z := ⟨(uliftYoneda.{u + 1}).map q ≫ ξ⟩ with hξV
  choose W p r hpb hopen using fun i =>
    h (Xf i) (hXaff i) (J.uliftYoneda.{u + 1}.map (j i) ≫ ξV)
  -- the open subschemes are bounded by the size of the point
  have hWsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤
      ((BigFppfOver.toScheme B S hS).obj T).size := by
    intro i
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (p i)) := hopen i
    exact le_trans
      (Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map (p i))) (hXsize i)
  obtain ⟨Wt, jw, hjwopen, hjwcov, -, ⟨hWsite⟩, ⟨hWsheaf⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS W T.left.property hιsize hWsize
  set m : Wt ⟶ V := Cofan.IsColimit.desc hWsite (fun i => p i ≫ j i) with hm
  have hmfac : ∀ i, jw i ≫ m = p i ≫ j i := fun i => Cofan.IsColimit.fac hWsite _ i
  -- `m` is étale, étaleness being Zariski local on the source
  have hmet : Etale ((BigFppfOver.toScheme B S hS).map m) := by
    let 𝒰 : ((BigFppfOver.toScheme B S hS).obj Wt).OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (BigFppfOver.toScheme B S hS).obj (W i)
        f := fun i => (BigFppfOver.toScheme B S hS).map (jw i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hjwcov, hjwopen⟩ }
    have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    have hfac : 𝒰.f i ≫ (BigFppfOver.toScheme B S hS).map m =
        (BigFppfOver.toScheme B S hS).map (p i) ≫
          (BigFppfOver.toScheme B S hS).map (j i) := by
      show (BigFppfOver.toScheme B S hS).map (jw i) ≫ _ = _
      rw [← Functor.map_comp, ← Functor.map_comp, hmfac i]
    rw [hfac]
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (p i)) := hopen i
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)) := hjopen i
    infer_instance
  -- the fibre product over `V` is the coproduct of the fibre products over the affine opens
  have ht : IsPullback (pullback.snd ξV Φ) (pullback.fst ξV Φ) Φ ξV :=
    (IsPullback.of_hasPullback ξV Φ).flip
  have hleft := fun i => IsPullback.of_right' (hpb i) ht
  obtain ⟨hPcol⟩ := Sheaf.nonempty_isColimit_cofanMk_of_isPullback J
    (fun i => J.uliftYoneda.{u + 1}.map (j i)) hsheaf (pullback.fst ξV Φ) _
    (fun i => J.uliftYoneda.{u + 1}.map (p i)) hleft
  set eW := IsColimit.coconePointUniqueUpToIso hWsheaf hPcol with heW
  have hfstm : eW.hom ≫ pullback.fst ξV Φ = J.uliftYoneda.{u + 1}.map m := by
    refine Cofan.IsColimit.hom_ext hWsheaf _ _ fun i => ?_
    have h1 := IsColimit.comp_coconePointUniqueUpToIso_hom hWsheaf hPcol ⟨i⟩
    have h2 : J.uliftYoneda.{u + 1}.map (jw i) ≫ eW.hom ≫ pullback.fst ξV Φ =
        J.uliftYoneda.{u + 1}.map (p i) ≫ J.uliftYoneda.{u + 1}.map (j i) := by
      rw [← Category.assoc]
      rw [show J.uliftYoneda.{u + 1}.map (jw i) ≫ eW.hom =
        (Cofan.mk (pullback ξV Φ)
          fun k ↦ ht.lift (r k) (J.uliftYoneda.{u + 1}.map (p k) ≫
            J.uliftYoneda.{u + 1}.map (j k))
            (by rw [(hpb k).w, Category.assoc])).ι.app ⟨i⟩ from h1]
      exact (hleft i).w
    have h3 : J.uliftYoneda.{u + 1}.map (jw i) ≫ J.uliftYoneda.{u + 1}.map m =
        J.uliftYoneda.{u + 1}.map (p i) ≫ J.uliftYoneda.{u + 1}.map (j i) := by
      rw [← Functor.map_comp, ← Functor.map_comp, hmfac i]
    show J.uliftYoneda.{u + 1}.map (jw i) ≫ eW.hom ≫ pullback.fst ξV Φ =
      J.uliftYoneda.{u + 1}.map (jw i) ≫ J.uliftYoneda.{u + 1}.map m
    rw [h2, h3]
  -- read the sheaf-level square at the level of presheaves
  have hPpre := (IsPullback.of_hasPullback ξV Φ).map (sheafToPresheaf J (Type (u + 1)))
  refine ⟨V, q, Wt, m,
    (sheafToPresheaf J (Type (u + 1))).mapIso eW ≪≫ hPpre.isoPullback,
    hqsurj, hqetale, hmet, ?_⟩
  have h4 : eW.hom.hom ≫ (pullback.fst ξV Φ).hom = (uliftYoneda.{u + 1}).map m :=
    congrArg (fun t : J.uliftYoneda.{u + 1}.obj Wt ⟶ J.uliftYoneda.{u + 1}.obj V ↦ t.hom) hfstm
  have h5 : hPpre.isoPullback.hom ≫ pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom =
      (pullback.fst ξV Φ).hom := hPpre.isoPullback_hom_fst
  show eW.hom.hom ≫ hPpre.isoPullback.hom ≫
      pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom = (uliftYoneda.{u + 1}).map m
  rw [h5]
  exact h4

/-- **Representability and étaleness of a morphism of fppf sheaves are local on the test
object.** A morphism `Φ : X ⟶ Z` of fppf sheaves over `S` whose base change along every point
of `Z` out of an *affine* object of the site is represented by an open subscheme of that affine
is representable by algebraic spaces and étale.

Nothing is asked of a point of `Z` out of a general object of the site, which is the whole
content: an affine open covering of such a point is infinite as soon as the point is not
quasi-compact, and the covering is handled by taking the coproduct of its members inside the
site, which the open-immersion hypothesis makes possible. -/
theorem isRepresentableEtale_of_openImmersion_over_affinePoints
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z)
    (h : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ Z,
      ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
        (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
        IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    IsRepresentableEtale B S hS Φ := by
  classical
  have hkey := exists_representable_etale_pullback_of_openImmersion_over_affinePoints
    B S hS Φ h
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS Φ.hom := by
    refine isRepresentable_of_forall_surjective_etale_cover B S hS Φ fun T ξ ↦ ?_
    obtain ⟨V, q, Wt, m, e, hqs, hqe, -, -⟩ := hkey T ξ
    exact ⟨V, q, hqs, hqe, Space.isAlgebraicSpaceULift_of_iso B S hS e
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Wt)⟩
  refine ⟨hrep, ?_⟩
  intro T ξ
  obtain ⟨V, q, Wt, m, e, hqs, hqe, hme, hfst⟩ := hkey T ξ
  -- the base change of `Φ` along the point is étale over the chart `V`
  have hVet : Space.IsEtaleULift.{u + 1} B S hS
      (pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom) := by
    have hmet : Space.IsEtaleULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).map m) :=
      (Space.isEtaleULift_uliftYoneda_map_iff.{u + 1} B S hS m).mpr hme
    have hpre := isEtaleULift_precomp_iso B S hS e.symm _ hmet
    rw [Iso.symm_hom, ← hfst, Iso.inv_hom_id_assoc] at hpre
    exact hpre
  refine isEtaleULift_of_targetChart B S hS
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)
    (pullback.fst ξ Φ.hom) V ((uliftYoneda.{u + 1}).map q)
    (Space.relative_uliftYoneda_map B S hS _ q hqs)
    (Space.relative_uliftYoneda_map B S hS _ q hqe) ?_
  have hpre := isEtaleULift_precomp_iso B S hS
    (pullbackRightPullbackFstIso ξ Φ.hom ((uliftYoneda.{u + 1}).map q)) _ hVet
  rwa [pullbackRightPullbackFstIso_hom_fst] at hpre

/-- **A representable open immersion of fppf sheaves is representable by algebraic spaces and
étale.** This is the special case of
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_openImmersion_over_affinePoints` in which
the base change is an open subscheme over *every* point of the target, not only over the affine
ones; it records that the chart hypothesis of
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem` implies the hypothesis
`hαet` of `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem`. -/
theorem isRepresentableEtale_of_relative_openImmersion
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z)
    (h : ∀ (U : BigFppfOver B S hS)
      (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ Z),
      ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
        (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
        IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    IsRepresentableEtale B S hS Φ :=
  isRepresentableEtale_of_openImmersion_over_affinePoints B S hS Φ fun U _ ξ ↦ h U ξ

/-! ### The factorization through a stage, for a quasi-compact test object -/

/-- **A scheme-valued point of a directed colimit out of a quasi-compact object of the site
factors through a stage.** The transition morphisms are asked only to be monomorphisms, which a
thickening is.

This is `AlgebraicGeometry.FormalSpace.compact_map_factors_through_filtered_colimit` in the
shape the chart-system criterion consumes. -/
theorem exists_factor_through_stage_of_compact
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hmono : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), Mono (E.map f))
    (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶
      letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
      colimit E) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (i : Λ) (ξ' : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ E.obj i),
      ξ = ξ' ≫ colimit.ι E i := by
  let J := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  have hUqc := isQuasiCompactObject_over_of_compact_scheme B S hS U
  have heq : (Sheaf.sheafifiedYoneda J).obj U ≅ J.uliftYoneda.{u + 1}.obj U :=
    (Sheaf.uliftYonedaIsoSheafifiedYoneda J).app U |>.symm
  obtain ⟨i, g, hg⟩ := compact_map_factors_through_filtered_colimit E
    (fun k l f ↦ hmono f) U hUqc (heq.hom ≫ ξ)
  exact ⟨i, heq.inv ≫ g, by rw [Category.assoc, hg, ← Category.assoc, heq.inv_hom_id,
    Category.id_comp]⟩

/-! ### The chart-system criterion with no factorization hypothesis -/

/-- **A chart system by representable open immersions makes a directed colimit a formal
algebraic space**, with no factorization hypothesis.

Let `E` be a directed diagram of fppf sheaves over `S` whose transition morphisms are
monomorphisms, carrying a system of chart diagrams `G` whose colimits are affine formal
algebraic spaces, whose chart morphisms `(α k).app i` are representable open immersions, which
base change along the transitions (`hα`) and which cover each stage (`hcov`). Then a sheaf `Z`
isomorphic to `colim E` and satisfying the set-theoretic condition of **Stacks 0AIS** is a
formal algebraic space over `S`.

The hypothesis `hα` is asked at the *transitions* of the index, where a chart system transported
across thickenings has it (`AlgebraicGeometry.FormalSpace.isPullback_transportedOpenInclusion`),
rather than at the colimit; the two are equivalent, by
`AlgebraicGeometry.FormalSpace.CartesianColimit.equifibered_colimit_isPullback` and, conversely,
by pasting Cartesian squares, and the first of these is what supplies the comparison squares at
the colimit used below. Neither form can be dropped: over the constant
diagram `E` at a representable `Spec A`, whose transitions are identities, take two charts, one
of them the identity and the other the empty open subscheme at the first stage and the identity
at the second. Every other hypothesis holds — the transitions are monomorphisms, the empty open
subscheme and the identity base change to open immersions over every point, both chart colimits
are `Spec A`, and the second chart alone covers each stage — while the square at the first stage
is Cartesian only if the empty scheme and `Spec A` agree.

This is `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_chartSystem` with the
hypothesis `hfac` — a scheme-valued point of the colimit factors through a stage — *proved*
rather than assumed. It is false as that statement quantifies it, over every object of the site;
what is true is its restriction to a quasi-compact object, which is
`AlgebraicGeometry.FormalSpace.exists_factor_through_stage_of_compact`, and that restriction
suffices because representability and étaleness are local on the test object
(`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_openImmersion_over_affinePoints`). -/
theorem isFormalAlgebraicSpace_of_openChartSystem
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hmono : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), Mono (E.map f))
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (colimit (G k)))
    (hαopen : ∀ (k : I) (i : Λ) (U : BigFppfOver B S hS)
      (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ E.obj i),
      ∃ (W : BigFppfOver B S hS) (pr : W ⟶ U)
        (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ (G k).obj i),
        IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr)
          ((α k).app i) ξ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pr))
    (hα : ∀ k, (α k).Equifibered)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ i : Λ, Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i)))
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨eZ⟩ := hZ
  -- the comparison squares at the colimit, from the equifiberedness of each chart diagram
  have hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i) := by
    intro k i
    have _ : IsConnected (Under i) := IsFiltered.isConnected _
    exact equifibered_colimit_isPullback (α k) (hα k) i
  refine ⟨hZset, I, (fun k ↦ colimit (G k)), (fun k ↦ colimMap (α k) ≫ eZ.inv), haff, ?_, ?_⟩
  · -- the colimit of each chart diagram is representable étale over `Z`
    intro k
    refine isRepresentableEtale_of_openImmersion_over_affinePoints B S hS
      (colimMap (α k) ≫ eZ.inv) fun U hU ξ ↦ ?_
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
    obtain ⟨i, ξ', hξ'⟩ :=
      exists_factor_through_stage_of_compact B S hS E hmono U (ξ ≫ eZ.hom)
    obtain ⟨W, pr, c, hpb, hopen⟩ := hαopen k i U ξ'
    refine ⟨W, pr, c ≫ colimit.ι (G k) i, ?_, hopen⟩
    have hpaste : IsPullback (c ≫ colimit.ι (G k) i)
        ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr) (colimMap (α k))
        (ξ' ≫ colimit.ι E i) :=
      hpb.paste_horiz (hsq k i)
    rw [← hξ'] at hpaste
    refine hpaste.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eZ.symm
      (by simp) (by simp) (by simp) (by simp)
  · -- the chart colimits cover `Z`
    rw [Sheaf.isLocallySurjective_iff_epi]
    refine ⟨?_⟩
    intro T k l hkl
    have hζkl : ∀ m : I, (colimMap (α m) ≫ eZ.inv) ≫ k = (colimMap (α m) ≫ eZ.inv) ≫ l := by
      intro m
      have h := congrArg (fun t ↦ Sigma.ι (fun m : I ↦ colimit (G m)) m ≫ t) hkl
      simpa using h
    have hcolim : eZ.inv ≫ k = eZ.inv ≫ l := by
      refine colimit.hom_ext (fun i ↦ ?_)
      have hepi : Epi (Sigma.desc (fun m ↦ (α m).app i)) :=
        (Sheaf.isLocallySurjective_iff_epi _).mp (hcov i)
      refine (cancel_epi (Sigma.desc (fun m ↦ (α m).app i))).1 (Sigma.hom_ext _ _ (fun m ↦ ?_))
      have hm := hζkl m
      simp only [Category.assoc] at hm
      have hm2 := congrArg (fun t ↦ colimit.ι (G m) i ≫ t) hm
      simp only [ι_colimMap_assoc] at hm2
      simpa using hm2
    exact (cancel_epi eZ.inv).1 hcolim

end AlgebraicGeometry.FormalSpace

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedChartRelativeSpecContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalChartDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections

/-!
# The disjoint union of the affine opens of a chart, as a chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`V` be an étale chart of `X`. The affine opens of the scheme `chartScheme V` are étale charts
of `X`, through `AlgebraicGeometry.Space.chartOpens`, and their disjoint union is a single étale
chart `V'` of `X`, over which they sit by pairwise disjoint monomorphisms generating a covering
sieve. A sheaf on the small étale site of `X` sends this family to a product, so its restriction
map from `V'` to each affine open of `chartScheme V` is surjective. Consequently the chart-level
relative spectrum of a bounded quasi-coherent `𝒪_X`-algebra is an object of the site at every
chart.

## Main results

* `AlgebraicGeometry.Space.isEtaleChart_comp_of_etale`: an étale morphism of the big fppf site
  into the object underlying an étale chart composes with that chart to an étale chart.
* `AlgebraicGeometry.Space.exists_chart_affineOpenCoproduct`: there is an étale chart `V'` of
  `X` and a morphism of charts from every affine open of `chartScheme V` into `V'`, such that
  these are monomorphisms, generate a covering sieve of `V'`, and are pairwise disjoint.
* `AlgebraicGeometry.Space.AlgebraSheaf.exists_dominatingChart`: a sheaf of algebras has, at
  every chart `V`, a chart whose ring of sections surjects onto its sections over every affine
  open of `chartScheme V`.
* `AlgebraicGeometry.Space.AlgebraSheaf.exists_bound_restrictToChartScheme_of_sectionsBelowCutoff`
  and
  `AlgebraicGeometry.Space.contains_relativeSpec_restrictToChartScheme_of_sectionsBelowCutoff`:
  under `AlgebraSheaf.SectionsBelowCutoff`, the sections over the affine opens of every chart
  are uniformly bounded below the cutoff, and the chart-level relative spectrum is an object of
  the site.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Charts from étale morphisms into a chart -/

/-- If `U` is an étale chart of the presheaf `F` and `q : A ⟶ U.obj.left` is a morphism of the
big fppf site of `S` whose underlying morphism of schemes is étale, then
`yoneda.map q ≫ U.obj.hom` is an étale chart of `F`. -/
theorem isEtaleChart_comp_of_etale {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS F) (A : BigFppfOver B S hS) (q : A ⟶ U.obj.left)
    (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    IsEtaleChart B S hS F (CostructuredArrow.mk (yoneda.map q ≫ U.obj.hom)) := by
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    (inferInstance :
      MorphismProperty.IsMultiplicative
        (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  have : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have : P.IsStableUnderBaseChange :=
    ⟨fun sq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (sq.map (BigFppfOver.toScheme B S hS)) hg⟩
  have : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  exact MorphismProperty.IsStableUnderComposition.comp_mem (P := P.presheaf)
    _ _ ((P.relative_map_iff (F := yoneda)).2 hq) U.property

/-! ### The disjoint union of the affine opens of a chart -/

/-- For an étale chart `V` of an algebraic space `X` there is an étale chart `V'` of `X` together
with, for every affine open `W` of `chartScheme V`, a morphism of charts from `W` — read as a
chart through `AlgebraicGeometry.Space.chartOpens` — to `V'`, such that these morphisms are
monomorphisms, generate a covering sieve of `V'`, and are pairwise disjoint: a chart mapping to
two of them with different indices, compatibly over `V'`, is covered by the empty sieve. -/
theorem exists_chart_affineOpenCoproduct {X : AlgebraicSpaces B S hS}
    (V : SmallEtale B S hS X.1) :
    ∃ (V' : SmallEtale B S hS X.1)
      (j : ∀ W : (chartScheme V).affineOpens,
        (chartOpens B S hS V).obj (W : (chartScheme V).Opens) ⟶ V'),
      (∀ W, Mono (j W)) ∧
      Sieve.ofArrows (fun W : (chartScheme V).affineOpens =>
          (chartOpens B S hS V).obj (W : (chartScheme V).Opens)) j ∈
        SmallEtale.topology B S hS X.1 V' ∧
      (∀ W W' : (chartScheme V).affineOpens, W ≠ W' →
        ∀ {Z : SmallEtale B S hS X.1}
          (a : Z ⟶ (chartOpens B S hS V).obj (W : (chartScheme V).Opens))
          (b : Z ⟶ (chartOpens B S hS V).obj (W' : (chartScheme V).Opens)),
          a ≫ j W = b ≫ j W' → (⊥ : Sieve Z) ∈ SmallEtale.topology B S hS X.1 Z) := by
  classical
  let incl : ∀ W : (chartScheme V).affineOpens,
      (chartOpens B S hS V).obj (W : (chartScheme V).Opens) ⟶ V := fun W =>
    ObjectProperty.homMk (CostructuredArrow.homMk
      (chartOpenOverι B S hS V (W : (chartScheme V).Opens)) rfl)
  have hinclmap : ∀ W : (chartScheme V).affineOpens,
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map (incl W)) =
        (W : (chartScheme V).Opens).ι := fun _ => rfl
  obtain ⟨V₀, jj, hjjoi, hjjcov, ⟨hsch⟩, ⟨hsite⟩, -⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS
      (fun W : (chartScheme V).affineOpens => (SmallEtale.toOver B S hS X.1).obj
        ((chartOpens B S hS V).obj (W : (chartScheme V).Opens)))
      V.obj.left.left.property (chartScheme V).mk_affineOpens_le_size
      (fun W => Scheme.size_coe_opens_le (chartScheme V) (W : (chartScheme V).Opens))
  obtain ⟨q, hqfac⟩ : ∃ q : V₀ ⟶ V.obj.left,
      ∀ W, jj W ≫ q = (SmallEtale.toOver B S hS X.1).map (incl W) :=
    ⟨Cofan.IsColimit.desc hsite (fun W => (SmallEtale.toOver B S hS X.1).map (incl W)),
      fun W => Cofan.IsColimit.fac hsite _ W⟩
  have hqet : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) := by
    have hloc : IsZariskiLocalAtSource
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @_root_.AlgebraicGeometry.Etale.{u})
    refine MorphismProperty.IsLocalAtSource.of_forall_comp (K := Scheme.zariskiPrecoverage)
      (R := Presieve.ofArrows
        (fun W : (chartScheme V).affineOpens => (BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj
            ((chartOpens B S hS V).obj (W : (chartScheme V).Opens))))
        fun W => (BigFppfOver.toScheme B S hS).map (jj W)) ?_ ?_
    · exact (Scheme.ofArrows_mem_precoverage_iff
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
          MorphismProperty Scheme.{u})).2 ⟨hjjcov, hjjoi⟩
    · intro U' gg hR
      obtain ⟨W⟩ := hR
      have hcomp : (BigFppfOver.toScheme B S hS).map (jj W) ≫
          (BigFppfOver.toScheme B S hS).map q =
            (W : (chartScheme V).Opens).ι := by
        rw [← Functor.map_comp, hqfac W, hinclmap W]
      rw [hcomp]
      exact inferInstanceAs
        (_root_.AlgebraicGeometry.Etale (W : (chartScheme V).Opens).ι)
  refine ⟨⟨CostructuredArrow.mk (yoneda.map q ≫ V.obj.hom),
      isEtaleChart_comp_of_etale B S hS V V₀ q hqet⟩,
    fun W => ObjectProperty.homMk (CostructuredArrow.homMk (jj W) ?_), ?_, ?_, ?_⟩
  · change yoneda.map (jj W) ≫ yoneda.map q ≫ V.obj.hom =
      yoneda.map (chartOpenOverι B S hS V (W : (chartScheme V).Opens)) ≫ V.obj.hom
    rw [← Category.assoc, ← Functor.map_comp, hqfac W]
    rfl
  · intro W
    exact SmallEtale.mono_of_mono_toOver_map B S hS
      (mono_of_isColimit_toScheme B S hS _ V₀ jj hsch W)
  · refine SmallEtale.ofArrows_mem_topology B S hS X.1 _ _ ?_
    refine Scheme.ofArrows_mem_etalePrecoverage_iff.2 ⟨hjjcov, fun W => ?_⟩
    have := hjjoi W
    exact inferInstanceAs
      (_root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (jj W)))
  · intro W W' hWW' Z a b hab
    refine SmallEtale.bot_mem_topology B S hS X.1 Z ?_
    have hab' : (SmallEtale.toOver B S hS X.1).map a ≫ jj W =
        (SmallEtale.toOver B S hS X.1).map b ≫ jj W' := by
      have h := congrArg (SmallEtale.toOver B S hS X.1).map hab
      rw [Functor.map_comp, Functor.map_comp] at h
      exact h
    exact isEmpty_of_commSq_of_isColimit_cofanMk hsch hWW'
      (a := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a))
      (b := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map b))
      (by rw [← Functor.map_comp, ← Functor.map_comp, hab'])

/-! ### The dominating chart, and the containment it buys -/

/-- A sheaf of algebras on the small étale site of `X` has, at every chart `V`, a chart whose
ring of sections surjects onto its sections over every affine open of `chartScheme V`. -/
theorem AlgebraSheaf.exists_dominatingChart {X : AlgebraicSpaces B S hS}
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1) :
    ∃ V' : SmallEtale B S hS X.1, ∀ W : (chartScheme V).affineOpens,
      ∃ k : (chartOpens B S hS V).obj (W : (chartScheme V).Opens) ⟶ V',
        Function.Surjective ((CategoryTheory.forget CommRingCat.{u}).map
          (A.right.obj.map k.op)) := by
  classical
  obtain ⟨V', j, hmono, hcov, hdisj⟩ := exists_chart_affineOpenCoproduct B S hS V
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      (A.right.obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _ A.right.property)
  refine ⟨V', fun W => ⟨j W, fun s => ?_⟩⟩
  obtain ⟨t, ht, -⟩ := hsheaf.existsUnique_section_of_disjoint_arrows j hcov hmono hdisj
    (Function.update (fun W' : (chartScheme V).affineOpens =>
      (0 : A.right.obj.obj (op ((chartOpens B S hS V).obj
        (W' : (chartScheme V).Opens))))) W s)
  exact ⟨t, by simpa using ht W⟩

/-- For a sheaf of algebras satisfying `AlgebraSheaf.SectionsBelowCutoff` and any chart `V`, the
sections of its restriction to `chartScheme V` over the affine opens of `chartScheme V` have
cardinality bounded by a single cardinal below the cutoff. -/
theorem AlgebraSheaf.exists_bound_restrictToChartScheme_of_sectionsBelowCutoff
    {X : AlgebraicSpaces B S hS} {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A) (V : SmallEtale B S hS X.1) :
    ∃ μ < B.cutoff, ∀ W : (chartScheme V).affineOpens,
      #((A.restrictToChartScheme B S hS V).right.obj.obj
        (op (W : (chartScheme V).Opens))) ≤ μ := by
  obtain ⟨V', hV'⟩ := AlgebraSheaf.exists_dominatingChart B S hS A V
  exact AlgebraSheaf.exists_bound_restrictToChartScheme_of_dominatingChart B S hS hA V V' hV'

/-- For a quasi-coherent `𝒪_X`-algebra satisfying `AlgebraSheaf.SectionsBelowCutoff` and any
chart `V`, the relative spectrum of its restriction to `chartScheme V` is an object of the
site. -/
theorem contains_relativeSpec_restrictToChartScheme_of_sectionsBelowCutoff
    {X : AlgebraicSpaces B S hS} (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) (V : SmallEtale B S hS X.1) :
    B.Contains (Stacks.AffineAlgebraEquivalence.relativeSpec
      (A.obj.restrictToChartScheme B S hS V)) := by
  obtain ⟨V', hV'⟩ := AlgebraSheaf.exists_dominatingChart B S hS A.obj V
  exact contains_relativeSpec_restrictToChartScheme_of_dominatingChart B S hS A hA V V' hV'

end AlgebraicGeometry.Space

end

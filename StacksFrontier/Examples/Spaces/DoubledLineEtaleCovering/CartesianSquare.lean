module

public import StacksFrontier.Examples.Spaces.DoubledLineEtaleCovering.CoveringMorphism

/-!
# The cartesian square of the doubled-origin covering

The square `Y ← Y₁ ⨿ Y₂`, `X ← 𝐀¹_k` of Stacks 05ZI: it commutes, the morphism `Y ⟶ X` is a
surjection of fppf sheaves, and away from characteristic two the square is cartesian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Examples Stacks.Examples.AffineOverAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

variable (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-! ### The square of the remark -/

/-- `Y₁ ⨿ Y₂` of the square of Stacks 05ZI: the coproduct of two copies of the chart `𝐀¹_k`
of Stacks 05Z6, as an object of the site. -/
noncomputable abbrev chartPair : BigFppfOver B (Spec (.of k)) hk :=
  BigFppfOver.sigmaObj B (Spec (.of k)) hk fun _ : Bool => affineLineChart k B hk

/-- The inclusion of the `b`-th copy of the chart `𝐀¹_k` into `Y₁ ⨿ Y₂`. -/
noncomputable abbrev chartPairIncl (b : Bool) :
    affineLineChart k B hk ⟶ chartPair k B hk :=
  BigFppfOver.sigmaIncl B (Spec (.of k)) hk (fun _ : Bool => affineLineChart k B hk) b

/-- **The top edge of the square of Stacks 05ZI**, `Y₁ ⨿ Y₂ ⟶ Y`: the two charts of the
doubled line. -/
noncomputable def chartPairToDoubledLine : chartPair k B hk ⟶ doubledLineSite k B hk :=
  Cofan.IsColimit.desc
    (BigFppfOver.isColimit_sigmaCofan B (Spec (.of k)) hk fun _ : Bool => affineLineChart k B hk)
    (doubledChartHom k B hk)

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- On the `b`-th copy of `𝐀¹_k`, the top edge `Y₁ ⨿ Y₂ ⟶ Y` is the `b`-th chart. -/
@[simp]
theorem chartPairIncl_comp_chartPairToDoubledLine (b : Bool) :
    chartPairIncl k B hk b ≫ chartPairToDoubledLine k B hk = doubledChartHom k B hk b :=
  Cofan.IsColimit.fac
    (BigFppfOver.isColimit_sigmaCofan B (Spec (.of k)) hk fun _ : Bool => affineLineChart k B hk)
    (doubledChartHom k B hk) b

/-- The twist of the `b`-th copy of the chart `𝐀¹_k`: the identity on the first copy and
negation of the coordinate on the second. -/
noncomputable def chartTwist (b : Bool) : affineLineChart k B hk ⟶ affineLineChart k B hk :=
  bif b then chartNeg k B hk else 𝟙 (affineLineChart k B hk)

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The twist of the first copy is the identity. -/
@[simp]
theorem chartTwist_false : chartTwist k B hk false = 𝟙 (affineLineChart k B hk) := rfl

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The twist of the second copy is negation of the coordinate. -/
@[simp]
theorem chartTwist_true : chartTwist k B hk true = chartNeg k B hk := rfl

/-- **The right edge of the square of Stacks 05ZI**, `Y₁ ⨿ Y₂ ⟶ 𝐀¹_k`: the identity on the
first copy of the affine line and negation of the coordinate on the second. -/
noncomputable def chartPairToAffineLine : chartPair k B hk ⟶ affineLineChart k B hk :=
  Cofan.IsColimit.desc
    (BigFppfOver.isColimit_sigmaCofan B (Spec (.of k)) hk fun _ : Bool => affineLineChart k B hk)
    (chartTwist k B hk)

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- On the `b`-th copy of `𝐀¹_k`, the map `Y₁ ⨿ Y₂ ⟶ 𝐀¹_k` is the twist `chartTwist`. -/
@[simp]
theorem chartPairIncl_comp_chartPairToAffineLine (b : Bool) :
    chartPairIncl k B hk b ≫ chartPairToAffineLine k B hk = chartTwist k B hk b :=
  Cofan.IsColimit.fac
    (BigFppfOver.isColimit_sigmaCofan B (Spec (.of k)) hk fun _ : Bool => affineLineChart k B hk)
    (chartTwist k B hk) b

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The two copies of the chart `𝐀¹_k` cover their coproduct `Y₁ ⨿ Y₂`. -/
theorem ofArrows_chartPairIncl_mem_topology :
    Sieve.ofArrows (fun _ : Bool => affineLineChart k B hk) (chartPairIncl k B hk) ∈
      BigFppfOver.topology B (Spec (.of k)) hk (chartPair k B hk) :=
  BigFppfOver.sieve_sigmaCofan_mem_topology B (Spec (.of k)) hk
    fun _ : Bool => affineLineChart k B hk

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The inclusion of the punctured affine line followed by negation of the coordinate, read on
the underlying schemes of the site. -/
@[simp]
theorem toScheme_map_puncturedChartNeg :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (puncturedChartNeg k B hk) =
      (puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left :=
  congrArg Over.Hom.left (post_puncturedChartNeg k B hk)

/-- Each chart of the doubled line is a split monomorphism of the site, being a section of
`AlgebraicGeometry.AffineLineInvolution.doubledProjHom`. -/
instance isSplitMono_doubledChartHom (b : Bool) : IsSplitMono (doubledChartHom k B hk b) :=
  ⟨⟨{ retraction := doubledProjHom k B hk
      id := doubledChartHom_comp_doubledProjHom k B hk b }⟩⟩

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **Away from characteristic two, two morphisms of the site into the chart `𝐀¹_k` which land
in two *distinct* copies of the chart and agree after composing with both edges of the square of
Stacks 05ZI have a source with no points.** They are equal and factor through the punctured
line, by `AlgebraicGeometry.AffineLineInvolution.eq_and_exists_punctured_factor`; the two
distinct labels then make their common factorization equal to its own composite with negation of
the coordinate, which on the punctured line forces the source to be empty. -/
theorem isEmpty_of_comp_chartTwist_eq (hchar : (2 : k) ≠ 0)
    {Z : BigFppfOver B (Spec (.of k)) hk} {b b' : Bool} (hbb : b ≠ b')
    (e d : Z ⟶ affineLineChart k B hk)
    (hD : e ≫ doubledChartHom k B hk b = d ≫ doubledChartHom k B hk b')
    (hA : e ≫ chartTwist k B hk b = d ≫ chartTwist k B hk b') :
    IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj Z) := by
  obtain ⟨hed, q, hq⟩ := eq_and_exists_punctured_factor k B hk hbb e d hD
  rw [← hed] at hA
  have htw : e = e ≫ chartNeg k B hk := by
    cases b with
    | false =>
      cases b' with
      | false => exact absurd rfl hbb
      | true => simpa using hA
    | true =>
      cases b' with
      | false => simpa using hA.symm
      | true => exact absurd rfl hbb
  have hqq : q ≫ puncturedChartInclusion k B hk =
      q ≫ puncturedChartNeg k B hk := by
    rw [puncturedChartNeg_eq_comp, ← Category.assoc, hq]
    exact htw
  have h' := congrArg (BigFppfOver.toScheme B (Spec (.of k)) hk).map hqq
  simp only [Functor.map_comp, toScheme_map_puncturedChartInclusion,
    toScheme_map_puncturedChartNeg] at h'
  exact isEmpty_of_comp_puncturedAffineLineOpen_ι_eq k hchar (B.inclusion.map Z.hom)
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map q) h'

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **The two edges of the square of Stacks 05ZI separate the two copies of the chart.** Two
morphisms of the site into the chart `𝐀¹_k`, placed in the copies indexed by `b` and `b'`,
which agree after composing with both edges of the square, have the same composite with the
two coproduct inclusions. For `b = b'` this is because a chart of the doubled line is a split
monomorphism; for `b ≠ b'` the source has no points, by
`AlgebraicGeometry.AffineLineInvolution.isEmpty_of_comp_chartTwist_eq`. -/
theorem comp_chartPairIncl_eq (hchar : (2 : k) ≠ 0)
    {Z : BigFppfOver B (Spec (.of k)) hk} (b b' : Bool)
    (e d : Z ⟶ affineLineChart k B hk)
    (hD : e ≫ doubledChartHom k B hk b = d ≫ doubledChartHom k B hk b')
    (hA : e ≫ chartTwist k B hk b = d ≫ chartTwist k B hk b') :
    e ≫ chartPairIncl k B hk b = d ≫ chartPairIncl k B hk b' := by
  by_cases hbb : b = b'
  · subst hbb
    rw [(cancel_mono (doubledChartHom k B hk b)).mp hD]
  · have hempty : IsEmpty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj Z) :=
      isEmpty_of_comp_chartTwist_eq k B hk hchar hbb e d hD hA
    exact (Over.isInitialOfIsInitialLeft (Y := Z)
      (isInitial_schemeBelow B (isInitial_iff_isEmpty.mpr hempty).some)).hom_ext _ _

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The two charts of the doubled line agree on the punctured line, read on the morphisms of
the site. -/
theorem puncturedChartInclusion_comp_doubledChartHom :
    puncturedChartInclusion k B hk ≫ doubledChartHom k B hk true =
      puncturedChartInclusion k B hk ≫ doubledChartHom k B hk false := by
  have hmap : (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (puncturedChartInclusion k B hk ≫ doubledChartHom k B hk true) =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (puncturedChartInclusion k B hk ≫ doubledChartHom k B hk false) := by
    rw [Functor.map_comp, Functor.map_comp, toScheme_map_puncturedChartInclusion,
      toScheme_map_doubledChartHom, toScheme_map_doubledChartHom]
    exact doubleSectionCover_chart_agree (affineLine k).left (puncturedAffineLineOpen k)
  exact BigFppfOver.map_toScheme_injective B (Spec (.of k)) hk hmap

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Negation of the coordinate carries the punctured chart into itself: as a morphism of the
site it factors through the inclusion of the punctured chart. -/
theorem exists_puncturedChartNeg_factor :
    ∃ n : puncturedAffineLineChart k B hk ⟶ puncturedAffineLineChart k B hk,
      n ≫ puncturedChartInclusion k B hk = puncturedChartNeg k B hk := by
  have hι : _root_.AlgebraicGeometry.IsOpenImmersion (puncturedAffineLineOpen k).ι :=
    inferInstance
  have hoi : IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (puncturedChartInclusion k B hk)) := by
    rw [toScheme_map_puncturedChartInclusion]
    exact hι
  have hsub : Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (puncturedChartNeg k B hk)) ⊆
      Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (puncturedChartInclusion k B hk)) := by
    rw [toScheme_map_puncturedChartNeg, toScheme_map_puncturedChartInclusion]
    exact range_subset_range_puncturedAffineLineOpen_ι k
  obtain ⟨n, hn, -⟩ :=
    BigFppfOver.existsUnique_lift_of_isOpenImmersion (puncturedChartInclusion k B hk) hoi
      (puncturedChartNeg k B hk) hsub
  exact ⟨n, hn⟩

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The two charts of the doubled line also agree after negation of the coordinate on the
punctured line, negation carrying the punctured line into itself. -/
theorem puncturedChartNeg_comp_doubledChartHom :
    puncturedChartNeg k B hk ≫ doubledChartHom k B hk true =
      puncturedChartNeg k B hk ≫ doubledChartHom k B hk false := by
  obtain ⟨n, hn⟩ := exists_puncturedChartNeg_factor k B hk
  rw [← hn, Category.assoc, Category.assoc, puncturedChartInclusion_comp_doubledChartHom]

/-! ### Lifting the relation of Stacks 02Z1 to the pair of charts -/

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Twisting twice by the same label is the identity. -/
@[simp]
theorem chartTwist_comp_self (b : Bool) :
    chartTwist k B hk b ≫ chartTwist k B hk b = 𝟙 (affineLineChart k B hk) := by
  cases b with
  | false => exact Category.comp_id _
  | true =>
    rw [chartTwist_true]
    refine (Over.post (X := B.obj hk) B.inclusion).map_injective ?_
    rw [Functor.map_comp, post_chartNeg, CategoryTheory.Functor.map_id]
    exact affineLineNeg_comp_affineLineNeg k

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Two morphisms out of the relation chart of Stacks 02Z1 which agree on both summands are
equal: the relation scheme is a coproduct over the ground field. -/
theorem relationChart_hom_ext {Q : BigFppfOver B (Spec (.of k)) hk}
    (f g : AffineOverAlgebraicSpace.relationChart k B hk ⟶ Q)
    (hd : chartDelta k B hk ≫ f = chartDelta k B hk ≫ g)
    (hg : chartGamma k B hk ≫ f = chartGamma k B hk ≫ g) : f = g := by
  refine (Over.post (X := B.obj hk) B.inclusion).map_injective (coprod.hom_ext ?_ ?_)
  · have h := congrArg (Over.post (X := B.obj hk) B.inclusion).map hd
    rw [Functor.map_comp, Functor.map_comp, post_chartDelta] at h
    exact h
  · have h := congrArg (Over.post (X := B.obj hk) B.inclusion).map hg
    rw [Functor.map_comp, Functor.map_comp, post_chartGamma] at h
    exact h


omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The two projections of the relation chart of Stacks 02Z1, in the two spellings used in
this development. -/
theorem chartTarget_eq_relationTarget : chartTarget k B hk = relationTarget k B hk := rfl

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The source projection of the relation chart, in the two spellings used in this
development. -/
theorem chartSource_eq_relationSource : chartSource k B hk = relationSource k B hk := rfl

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The inclusion of the punctured line into the affine line, in the two spellings used in
this development. -/
theorem chartPunctured_eq_puncturedChartInclusion :
    chartPunctured k B hk = puncturedChartInclusion k B hk := rfl

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Negation of the coordinate is an involution of the chart of the site. -/
theorem chartNeg_comp_chartNeg :
    chartNeg k B hk ≫ chartNeg k B hk = 𝟙 (affineLineChart k B hk) := by
  have h := chartTwist_comp_self k B hk true
  rwa [chartTwist_true] at h

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The two charts of the doubled line agree on the punctured line. -/
theorem chartPunctured_comp_doubledChartHom :
    chartPunctured k B hk ≫ doubledChartHom k B hk true =
      chartPunctured k B hk ≫ doubledChartHom k B hk false :=
  puncturedChartInclusion_comp_doubledChartHom k B hk

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The two charts of the doubled line agree on the punctured line after negation of the
coordinate. -/
theorem chartPuncturedNeg_comp_doubledChartHom :
    (chartPunctured k B hk ≫ chartNeg k B hk) ≫ doubledChartHom k B hk true =
      (chartPunctured k B hk ≫ chartNeg k B hk) ≫ doubledChartHom k B hk false := by
  have h := puncturedChartNeg_comp_doubledChartHom k B hk
  rw [puncturedChartNeg_eq_comp] at h
  exact h

/-- **The relation of Stacks 02Z1, lifted to `Y₁ ⨿ Y₂`.** The diagonal summand is placed in the
copy of the chart indexed by `b`, twisted by `b`; the graph summand is placed in the other
copy, negated and twisted by that copy's own label. -/
noncomputable def relationToChartPair (b : Bool) :
    AffineOverAlgebraicSpace.relationChart k B hk ⟶ chartPair k B hk :=
  (Over.post B.inclusion).preimage
    (X := AffineOverAlgebraicSpace.relationChart k B hk) (Y := chartPair k B hk)
    (coprod.desc
      ((Over.post (X := B.obj hk) B.inclusion).map
        (chartTwist k B hk b ≫ chartPairIncl k B hk b))
      ((Over.post (X := B.obj hk) B.inclusion).map
        (((chartPunctured k B hk ≫ chartNeg k B hk) ≫ chartTwist k B hk (!b)) ≫
          chartPairIncl k B hk (!b))))

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- `relationToChartPair`, read on the schemes over `Spec k`. -/
theorem post_relationToChartPair (b : Bool) :
    (Over.post (X := B.obj hk) B.inclusion).map (relationToChartPair k B hk b) =
      coprod.desc
        ((Over.post (X := B.obj hk) B.inclusion).map
          (chartTwist k B hk b ≫ chartPairIncl k B hk b))
        ((Over.post (X := B.obj hk) B.inclusion).map
          (((chartPunctured k B hk ≫ chartNeg k B hk) ≫ chartTwist k B hk (!b)) ≫
            chartPairIncl k B hk (!b))) :=
  (Over.post (X := B.obj hk) B.inclusion).map_preimage _

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- On the diagonal summand, `relationToChartPair b` is the twisted inclusion of the `b`-th
copy. -/
theorem chartDelta_comp_relationToChartPair (b : Bool) :
    chartDelta k B hk ≫ relationToChartPair k B hk b =
      chartTwist k B hk b ≫ chartPairIncl k B hk b := by
  refine (Over.post (X := B.obj hk) B.inclusion).map_injective ?_
  rw [Functor.map_comp, post_chartDelta, post_relationToChartPair]
  exact coprod.inl_desc _ _

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- On the graph summand, `relationToChartPair b` is negation followed by the twisted inclusion
of the other copy. -/
theorem chartGamma_comp_relationToChartPair (b : Bool) :
    chartGamma k B hk ≫ relationToChartPair k B hk b =
      ((chartPunctured k B hk ≫ chartNeg k B hk) ≫ chartTwist k B hk (!b)) ≫
        chartPairIncl k B hk (!b) := by
  refine (Over.post (X := B.obj hk) B.inclusion).map_injective ?_
  rw [Functor.map_comp, post_chartGamma, post_relationToChartPair]
  exact coprod.inr_desc _ _

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The lift of the relation to `Y₁ ⨿ Y₂` has the second projection of the relation as its
composite with the right edge of the square. -/
theorem relationToChartPair_comp_chartPairToAffineLine (b : Bool) :
    relationToChartPair k B hk b ≫ chartPairToAffineLine k B hk = chartSource k B hk := by
  refine relationChart_hom_ext k B hk _ _ ?_ ?_
  · have h1 : chartDelta k B hk ≫ relationToChartPair k B hk b ≫
        chartPairToAffineLine k B hk =
        chartTwist k B hk b ≫ chartTwist k B hk b := by
      rw [← Category.assoc, chartDelta_comp_relationToChartPair]
      simp only [Category.assoc, chartPairIncl_comp_chartPairToAffineLine]
    rw [h1, chartTwist_comp_self, chartDelta_comp_chartSource]
  · have h1 : chartGamma k B hk ≫ relationToChartPair k B hk b ≫
        chartPairToAffineLine k B hk =
        chartPunctured k B hk ≫ chartNeg k B hk ≫
          chartTwist k B hk (!b) ≫ chartTwist k B hk (!b) := by
      rw [← Category.assoc, chartGamma_comp_relationToChartPair]
      simp only [Category.assoc, chartPairIncl_comp_chartPairToAffineLine]
    rw [h1, chartTwist_comp_self, Category.comp_id, chartGamma_comp_chartSource]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The lift of the relation to `Y₁ ⨿ Y₂` has the first projection of the relation, twisted by
`b` and followed by the `b`-th chart of the doubled line, as its composite with the top edge of
the square. -/
theorem relationToChartPair_comp_chartPairToDoubledLine (b : Bool) :
    relationToChartPair k B hk b ≫ chartPairToDoubledLine k B hk =
      chartTarget k B hk ≫ chartTwist k B hk b ≫ doubledChartHom k B hk b := by
  refine relationChart_hom_ext k B hk _ _ ?_ ?_
  · have h1 : chartDelta k B hk ≫ relationToChartPair k B hk b ≫
        chartPairToDoubledLine k B hk =
        chartTwist k B hk b ≫ doubledChartHom k B hk b := by
      rw [← Category.assoc, chartDelta_comp_relationToChartPair]
      simp only [Category.assoc, chartPairIncl_comp_chartPairToDoubledLine]
    have h2 : chartDelta k B hk ≫ chartTarget k B hk ≫ chartTwist k B hk b ≫
        doubledChartHom k B hk b = chartTwist k B hk b ≫ doubledChartHom k B hk b := by
      rw [← Category.assoc, chartDelta_comp_chartTarget, Category.id_comp]
    rw [h1, h2]
  · have h1 : chartGamma k B hk ≫ relationToChartPair k B hk b ≫
        chartPairToDoubledLine k B hk =
        (chartPunctured k B hk ≫ chartNeg k B hk) ≫
          chartTwist k B hk (!b) ≫ doubledChartHom k B hk (!b) := by
      rw [← Category.assoc, chartGamma_comp_relationToChartPair]
      simp only [Category.assoc, chartPairIncl_comp_chartPairToDoubledLine]
    have h2 : chartGamma k B hk ≫ chartTarget k B hk ≫ chartTwist k B hk b ≫
        doubledChartHom k B hk b =
        chartPunctured k B hk ≫ chartTwist k B hk b ≫ doubledChartHom k B hk b := by
      rw [← Category.assoc, chartGamma_comp_chartTarget]
    rw [h1, h2]
    cases b with
    | false =>
      simp only [Bool.not_false, chartTwist_false, chartTwist_true, Category.id_comp,
        Category.assoc]
      have h3 := chartPunctured_comp_doubledChartHom k B hk
      have h4 : (chartPunctured k B hk ≫ chartNeg k B hk) ≫ chartNeg k B hk ≫
          doubledChartHom k B hk true =
          chartPunctured k B hk ≫ doubledChartHom k B hk true := by
        rw [Category.assoc, ← Category.assoc (chartNeg k B hk), chartNeg_comp_chartNeg,
          Category.id_comp]
      simp only [Category.assoc] at h4
      rw [h4, h3]
    | true =>
      simp only [Bool.not_true, chartTwist_false, chartTwist_true, Category.id_comp,
        Category.assoc]
      have h3 := chartPuncturedNeg_comp_doubledChartHom k B hk
      simp only [Category.assoc] at h3
      exact h3.symm

/-- The two prescriptions on the charts are the twist by the label followed by the chart
`𝐀¹_k ⟶ X` of Stacks 05Z6. -/
theorem doubledChartQuotientMap_eq (b : Bool) :
    doubledChartQuotientMap k B hk b =
      yoneda.map (chartTwist k B hk b) ≫ quotientChart k B hk := by
  cases b with
  | false =>
    rw [doubledChartQuotientMap_false, chartTwist_false, CategoryTheory.Functor.map_id,
      Category.id_comp]
  | true => rw [doubledChartQuotientMap_true, chartTwist_true]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **Pulling back the covering of the doubled line by its two charts.** Any morphism of the
site into `Y` factors through one of the two charts of the doubled line on each member of an
open covering of its source. -/
theorem exists_doubledChartHom_factor_cover {T : BigFppfOver B (Spec (.of k)) hk}
    (y : T ⟶ doubledLineSite k B hk) :
    ∃ (W : Bool → BigFppfOver B (Spec (.of k)) hk) (p : ∀ b, W b ⟶ T)
      (c : ∀ b, W b ⟶ affineLineChart k B hk),
      (∀ b, IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b))) ∧
      (∀ x : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T,
        ∃ b, x ∈ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b))) ∧
      ∀ b, p b ≫ y = c b ≫ doubledChartHom k B hk b := by
  classical
  have hoi : ∀ b, IsOpenImmersion
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (doubledChartHom k B hk b)) := by
    intro b
    rw [toScheme_map_doubledChartHom]
    exact (doubledLineData k).isOpenImmersion_chart b
  choose W p hpimm hprange _hpuniv using fun b : Bool =>
    exists_restrict_bigFppfOver T
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map y ⁻¹ᵁ
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (doubledChartHom k B hk b)).opensRange)
  have hsub : ∀ b, Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b ≫ y)) ⊆
      Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (doubledChartHom k B hk b)) := by
    intro b z hz
    obtain ⟨x, rfl⟩ := hz
    have hx : (BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b) x ∈
        Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b)) := ⟨x, rfl⟩
    rw [hprange b] at hx
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hx
  choose c hc _hcu using fun b : Bool =>
    BigFppfOver.existsUnique_lift_of_isOpenImmersion (doubledChartHom k B hk b) (hoi b)
      (p b ≫ y) (hsub b)
  refine ⟨W, p, c, hpimm, fun x => ?_, fun b => (hc b).symm⟩
  obtain ⟨b, w, hw⟩ := (doubledLineData k).exists_chart_eq
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map y x)
  refine ⟨b, ?_⟩
  rw [hprange b]
  change (BigFppfOver.toScheme B (Spec (.of k)) hk).map y x ∈
    Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (doubledChartHom k B hk b)).base
  rw [toScheme_map_doubledChartHom]
  exact ⟨w, hw⟩

/-- **The lift exists where the morphism into `Y` factors through a chart.** If `hz` factors
through the `b`-th chart of the doubled line by `hf`, and the twist of `hf` by `b` has the same
image in `X` as `az`, then the pair `(hz, az)` comes from `Y₁ ⨿ Y₂`: the relation of Stacks 02Z1
is the kernel pair of the chart `𝐀¹_k ⟶ X`, and
`AlgebraicGeometry.AffineLineInvolution.relationToChartPair` carries it into `Y₁ ⨿ Y₂`. -/
theorem exists_chartPair_lift_of_factor (hchar : (2 : k) ≠ 0)
    {Z : BigFppfOver B (Spec (.of k)) hk} (b : Bool)
    (hz : Z ⟶ doubledLineSite k B hk) (az hf : Z ⟶ affineLineChart k B hk)
    (hfac : hf ≫ doubledChartHom k B hk b = hz)
    (hqc : yoneda.map (hf ≫ chartTwist k B hk b) ≫ quotientChart k B hk =
      yoneda.map az ≫ quotientChart k B hk) :
    ∃ u : Z ⟶ chartPair k B hk,
      u ≫ chartPairToDoubledLine k B hk = hz ∧
        u ≫ chartPairToAffineLine k B hk = az := by
  have hpb : IsPullback (yoneda.map (chartTarget k B hk)) (yoneda.map (chartSource k B hk))
      (quotientChart k B hk) (quotientChart k B hk) := isPullback_quotientChart k B hk hchar
  obtain ⟨r, hr⟩ := yoneda.map_surjective
    (hpb.lift (yoneda.map (hf ≫ chartTwist k B hk b)) (yoneda.map az) hqc)
  have hrt : r ≫ chartTarget k B hk = hf ≫ chartTwist k B hk b := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, hr]
    exact hpb.lift_fst _ _ _
  have hrs : r ≫ chartSource k B hk = az := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, hr]
    exact hpb.lift_snd _ _ _
  refine ⟨r ≫ relationToChartPair k B hk b, ?_, ?_⟩
  · rw [Category.assoc, relationToChartPair_comp_chartPairToDoubledLine, ← Category.assoc,
      hrt, Category.assoc, ← Category.assoc (chartTwist k B hk b), chartTwist_comp_self,
      Category.id_comp, hfac]
  · rw [Category.assoc, relationToChartPair_comp_chartPairToAffineLine, hrs]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **The decomposition of a test object along a morphism into `Y₁ ⨿ Y₂`.** A morphism of the
site into the coproduct of the two copies of the chart `𝐀¹_k` decomposes its source into two
open pieces which cover it, on each of which the morphism factors through the corresponding
coproduct inclusion. This is Stacks 02WO for the coproduct of two representable sheaves. -/
theorem exists_chartPair_decomposition {T : BigFppfOver B (Spec (.of k)) hk}
    (u : T ⟶ chartPair k B hk) :
    ∃ (W : Bool → BigFppfOver B (Spec (.of k)) hk) (p : ∀ b, W b ⟶ T)
      (c : ∀ b, W b ⟶ affineLineChart k B hk),
      (∀ b, IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b))) ∧
      (∀ x : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T,
        ∃ b, x ∈ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b))) ∧
      ∀ b, c b ≫ chartPairIncl k B hk b = p b ≫ u := by
  obtain ⟨W, p, hoi, hsec, -, hcov, -⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan
      (fun b : Bool => (BigFppfOver.topology B (Spec (.of k)) hk).yoneda.map
        (chartPairIncl k B hk b))
      (BigFppfOver.isColimit_yoneda_sigmaCofan B (Spec (.of k)) hk
        fun _ : Bool => affineLineChart k B hk)
      T u
  choose c hc using hsec
  exact ⟨W, p, c, hoi, hcov, hc⟩

/-- Two morphisms of the site which agree on every member of a covering family by open
immersions are equal. -/
private theorem hom_ext_of_ofArrows_mem_topology {k : Type u} [Field k] {B : BigFppfSite.{u}}
    {hk : B.Contains (Spec (.of k))} {ι : Type*} {T Q : BigFppfOver B (Spec (.of k)) hk}
    {W : ι → BigFppfOver B (Spec (.of k)) hk} {p : ∀ i, W i ⟶ T}
    (hsieve : Sieve.ofArrows W p ∈ BigFppfOver.topology B (Spec (.of k)) hk T)
    {f g : T ⟶ Q} (h : ∀ i, p i ≫ f = p i ≫ g) : f = g := by
  refine yoneda.map_injective (Space.hom_ext_of_mem_topology
    (BigFppfOver.topology B (Spec (.of k)) hk)
    (BigFppfOver.isSheaf_yoneda_obj B (Spec (.of k)) hk Q) _ hsieve fun {Z} e he => ?_)
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ e).1 he
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg yoneda.map (by rw [Category.assoc, Category.assoc, h i])

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **The two edges of the square of Stacks 05ZI are jointly monomorphic.** Away from
characteristic two a morphism of the site into `Y₁ ⨿ Y₂` is determined by its composites with
the two edges: decomposing its source along each of two such morphisms puts both of them in a
single copy of the chart locally, where
`AlgebraicGeometry.AffineLineInvolution.comp_chartPairIncl_eq` applies. -/
theorem chartPair_hom_ext (hchar : (2 : k) ≠ 0) {T : BigFppfOver B (Spec (.of k)) hk}
    (u u' : T ⟶ chartPair k B hk)
    (hD : u ≫ chartPairToDoubledLine k B hk = u' ≫ chartPairToDoubledLine k B hk)
    (hA : u ≫ chartPairToAffineLine k B hk = u' ≫ chartPairToAffineLine k B hk) :
    u = u' := by
  classical
  obtain ⟨W, p, c, hWoi, hWcov, hWfac⟩ := exists_chartPair_decomposition k B hk u
  have hstep : ∀ b, p b ≫ u = p b ≫ u' := by
    intro b
    obtain ⟨V, pp, d, hVoi, hVcov, hVfac⟩ :=
      exists_chartPair_decomposition k B hk (p b ≫ u')
    have hedge : ∀ {Q : BigFppfOver B (Spec (.of k)) hk} (g : chartPair k B hk ⟶ Q),
        u ≫ g = u' ≫ g → ∀ b', (pp b' ≫ c b) ≫ (chartPairIncl k B hk b ≫ g) =
          d b' ≫ (chartPairIncl k B hk b' ≫ g) := by
      intro Q g hg b'
      simp only [Category.assoc]
      rw [reassoc_of% hWfac b, hg, reassoc_of% hVfac b']
    have hlocal : ∀ b', pp b' ≫ p b ≫ u = pp b' ≫ p b ≫ u' := by
      intro b'
      have hD' := hedge (chartPairToDoubledLine k B hk) hD b'
      have hA' := hedge (chartPairToAffineLine k B hk) hA b'
      rw [chartPairIncl_comp_chartPairToDoubledLine,
        chartPairIncl_comp_chartPairToDoubledLine] at hD'
      rw [chartPairIncl_comp_chartPairToAffineLine,
        chartPairIncl_comp_chartPairToAffineLine] at hA'
      rw [← hWfac b, ← Category.assoc,
        comp_chartPairIncl_eq k B hk hchar b b' (pp b' ≫ c b) (d b') hD' hA', hVfac b']
    exact hom_ext_of_ofArrows_mem_topology
      (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B (Spec (.of k)) hk pp hVoi hVcov)
      hlocal
  exact hom_ext_of_ofArrows_mem_topology
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B (Spec (.of k)) hk p hWoi hWcov) hstep

/-- The chart `𝐀¹_k ⟶ X` of Stacks 05Z6 is a surjection of fppf sheaves: it is the projection
onto a quotient sheaf, read through an isomorphism. -/
theorem isLocallySurjective_quotientChart :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of k)) hk)
      (quotientChart k B hk) := by
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of k)) hk)
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)) :=
    Stacks.Groupoids.isLocallySurjective_toQuotientSheaf _ _ _
  exact inferInstanceAs (Presheaf.IsLocallySurjective _
    ((affineLinePointsIso k B hk).inv ≫
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post B.inclusion) (involutionRelation k)))

/-- **The morphism `Y ⟶ X` of Stacks 05ZI is a surjection of fppf sheaves.** The chart
`𝐀¹_k ⟶ X` of Stacks 05Z6 is one, and it factors through `Y ⟶ X` through the first chart of
the doubled line. -/
theorem isLocallySurjective_coveringMorphism :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of k)) hk)
      (coveringMorphism k B hk) := by
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of k)) hk)
      (doubledChartQuotientMap k B hk false) := isLocallySurjective_quotientChart k B hk
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (doubledChartHom_comp_coveringMorphism k B hk false)

/-- **The square of Stacks 05ZI commutes.** On the first copy of the affine line both ways
round the square are the chart `𝐀¹_k ⟶ X` of Stacks 05Z6, and on the second both are negation
of the coordinate followed by that chart. -/
theorem chartPairToDoubledLine_comp_coveringMorphism :
    yoneda.map (chartPairToDoubledLine k B hk) ≫ coveringMorphism k B hk =
      yoneda.map (chartPairToAffineLine k B hk) ≫ quotientChart k B hk := by
  refine Space.hom_ext_of_mem_topology (BigFppfOver.topology B (Spec (.of k)) hk)
    (involutionQuotient k B hk).property _
    (ofArrows_chartPairIncl_mem_topology k B hk) fun {Z} e he => ?_
  obtain ⟨b, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ e).1 he
  have hL : yoneda.map (chartPairIncl k B hk b) ≫
      yoneda.map (chartPairToDoubledLine k B hk) ≫ coveringMorphism k B hk =
      doubledChartQuotientMap k B hk b := by
    rw [← Category.assoc, ← Functor.map_comp, chartPairIncl_comp_chartPairToDoubledLine,
      doubledChartHom_comp_coveringMorphism]
  have hR : yoneda.map (chartPairIncl k B hk b) ≫
      yoneda.map (chartPairToAffineLine k B hk) ≫ quotientChart k B hk =
      doubledChartQuotientMap k B hk b := by
    rw [← Category.assoc, ← Functor.map_comp, chartPairIncl_comp_chartPairToAffineLine]
    cases b with
    | false => rw [chartTwist_false, CategoryTheory.Functor.map_id, Category.id_comp]; rfl
    | true => rw [chartTwist_true]; rfl
  rw [Functor.map_comp, Category.assoc, Category.assoc, hL, hR]

/-- **Stacks 05ZI: the square of the remark is cartesian.** Away from characteristic two a
morphism into `Y` together with a morphism into the chart `𝐀¹_k` of Stacks 05Z6 having the same
image in `X` comes from a unique morphism into `Y₁ ⨿ Y₂`.

Locally on the source the morphism into `Y` factors through one of the two charts of the
doubled line, and there the relation of Stacks 02Z1, being the kernel pair of the chart
`𝐀¹_k ⟶ X`, supplies the lift through
`AlgebraicGeometry.AffineLineInvolution.relationToChartPair`. The local lifts agree because the
two edges of the square are jointly monomorphic, so they glue; and the glued lift is unique for
the same reason. -/
@[stacks 05ZI "the remark's cartesian square: Y ← Y₁ ⨿ Y₂ over X ← 𝐀¹_k is cartesian"]
theorem isPullback_chartPairToDoubledLine (hchar : (2 : k) ≠ 0) :
    IsPullback (yoneda.map (chartPairToDoubledLine k B hk))
      (yoneda.map (chartPairToAffineLine k B hk)) (coveringMorphism k B hk)
      (quotientChart k B hk) := by
  classical
  refine CategoryTheory.isPullback_of_existsUnique_app
    (chartPairToDoubledLine_comp_coveringMorphism k B hk) fun V hz az hya => ?_
  have hya' : yoneda.map hz ≫ coveringMorphism k B hk =
      yoneda.map az ≫ quotientChart k B hk := by
    ext Z g
    refine (NatTrans.naturality_apply (coveringMorphism k B hk) g.op hz).trans ?_
    refine (congrArg ((involutionQuotient k B hk).obj.map g.op) hya).trans ?_
    exact (NatTrans.naturality_apply (quotientChart k B hk) g.op az).symm
  obtain ⟨W, p, c, hoi, hcov, hfac⟩ := exists_doubledChartHom_factor_cover k B hk hz
  have hloc : ∀ b, ∃ u : W b ⟶ chartPair k B hk,
      u ≫ chartPairToDoubledLine k B hk = p b ≫ hz ∧
        u ≫ chartPairToAffineLine k B hk = p b ≫ az := by
    intro b
    refine exists_chartPair_lift_of_factor k B hk hchar b _ _ (c b) (hfac b).symm ?_
    have h1 : yoneda.map (p b ≫ hz) ≫ coveringMorphism k B hk =
        yoneda.map (p b ≫ az) ≫ quotientChart k B hk := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hya']
    have h2 : yoneda.map (c b ≫ chartTwist k B hk b) ≫ quotientChart k B hk =
        yoneda.map (c b ≫ doubledChartHom k B hk b) ≫ coveringMorphism k B hk := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        doubledChartHom_comp_coveringMorphism, doubledChartQuotientMap_eq]
    rw [h2, ← hfac b]
    exact h1
  choose u hu1 hu2 using hloc
  have hsieve : Sieve.ofArrows W p ∈
      BigFppfOver.topology B (Spec (.of k)) hk V.unop :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B (Spec (.of k)) hk p hoi hcov
  have hcompat : ∀ (b b' : Bool) (Z : BigFppfOver B (Spec (.of k)) hk)
      (s : Z ⟶ W b) (t : Z ⟶ W b'), s ≫ p b = t ≫ p b' →
      yoneda.map s ≫ yoneda.map (u b) = yoneda.map t ≫ yoneda.map (u b') := by
    intro b b' Z s t hst
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg yoneda.map (chartPair_hom_ext k B hk hchar _ _ ?_ ?_)
    · rw [Category.assoc, Category.assoc, hu1 b, hu1 b', ← Category.assoc, ← Category.assoc,
        hst]
    · rw [Category.assoc, Category.assoc, hu2 b, hu2 b', ← Category.assoc, ← Category.assoc,
        hst]
  obtain ⟨d, hd⟩ := Space.exists_glue_of_mem_topology
    (BigFppfOver.topology B (Spec (.of k)) hk)
    (BigFppfOver.isSheaf_yoneda_obj B (Spec (.of k)) hk (chartPair k B hk))
    W p hsieve (fun b => yoneda.map (u b)) hcompat
  obtain ⟨uu, huu⟩ := yoneda.map_surjective d
  have hpu : ∀ b, p b ≫ uu = u b := by
    intro b
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, huu]
    exact hd b
  have hD : uu ≫ chartPairToDoubledLine k B hk = hz :=
    hom_ext_of_ofArrows_mem_topology hsieve fun b => by
      rw [← Category.assoc, hpu b, hu1 b]
  have hA : uu ≫ chartPairToAffineLine k B hk = az :=
    hom_ext_of_ofArrows_mem_topology hsieve fun b => by
      rw [← Category.assoc, hpu b, hu2 b]
  refine ⟨uu, ⟨hD, hA⟩, fun u' hu' => ?_⟩
  exact chartPair_hom_ext k B hk hchar u' uu (hu'.1.trans hD.symm) (hu'.2.trans hA.symm)

end AlgebraicGeometry.AffineLineInvolution

end

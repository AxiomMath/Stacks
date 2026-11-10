module

public import StacksFrontier.Examples.Spaces.DoubledLineEtaleCovering.CartesianSquare

/-!
# The doubled-origin covering is a nontrivial connected finite étale covering

The covering clause of Stacks 05ZI: the morphism `Y ⟶ X` is representable, finite locally free
of rank two and étale, its source is connected, and it admits no section.

## Implementation notes

*The covering clause.* The morphism `Y ⟶ X` is representable for free: away from characteristic
two the quotient of Stacks 05Z6 is an algebraic space by
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient_of_isAffineHom`, so
its diagonal is representable and
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace` applies. With
representability in hand, Stacks 03I2 in the shape of
`AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descendsAlong` carries any property
satisfying fppf descent from the right edge of the cartesian square to `Y ⟶ X` **with no
undischarged descent hypothesis**: that is
`AlgebraicGeometry.AffineLineInvolution.presheaf_coveringMorphism_of_chartPairToAffineLine`, used
at `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property 2` and at `AlgebraicGeometry.Etale`. The
right edge is the map out of two copies of the affine line given by the identity and by negation
of the coordinate, so `AlgebraicGeometry.isFiniteLocallyFreeOfRank_sigmaDesc_of_isIso` gives it
degree two and `AlgebraicGeometry.etale_sigmaDesc` gives it étaleness.

*Nontriviality.* It is stated as the absence of a section of `Y ⟶ X`, there being no predicate
for a trivial covering of an algebraic space in the library: `Stacks.Etale.IsSplitCover` is a
property of a morphism of *schemes*, and `X` is not one. A covering which is a finite disjoint
union of copies of its base admits a section, so a covering without one is not such a union. The
proof runs through the cartesian square: a section of `Y ⟶ X` becomes a section `u` of the right
edge over the chart `𝐀¹_k`, whose composite with the top edge is unchanged by negation of the
coordinate on the punctured line. The decomposition of the chart along `u` has two pieces with
disjoint images — on their overlap the coordinate would equal its own negative — so
irreducibility of the affine line leaves one piece equal to the whole line, and over the
punctured line that piece then carries the coordinate and its negative at once.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Examples Stacks.Examples.AffineOverAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

variable (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-! ### The right edge of the square is finite étale of degree two -/

/-- Each twist of the chart `𝐀¹_k` is an isomorphism of schemes: it is an involution, being the
identity or negation of the coordinate. -/
instance isIso_toScheme_map_chartTwist (b : Bool) :
    IsIso ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartTwist k B hk b)) := by
  refine ⟨(BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartTwist k B hk b), ?_, ?_⟩ <;>
    rw [← Functor.map_comp, chartTwist_comp_self, CategoryTheory.Functor.map_id]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **The right edge of the square of Stacks 05ZI, on underlying schemes.** Up to the comparison
of `Y₁ ⨿ Y₂` with the chosen coproduct of schemes, it is the map out of the disjoint union of two
copies of the affine line given by the identity on one copy and negation of the coordinate on the
other. -/
theorem exists_iso_toScheme_map_chartPairToAffineLine :
    ∃ e : (∐ fun _ : Bool =>
          (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk)) ≅
        (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (chartPair k B hk),
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartPairToAffineLine k B hk) =
        e.inv ≫ Sigma.desc fun b : Bool =>
          (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartTwist k B hk b) := by
  obtain ⟨e₀, he₀⟩ := BigFppfOver.exists_iso_sigma_of_isColimit_cofan
    (fun _ : Bool => affineLineChart k B hk)
    (BigFppfOver.isColimit_sigmaCofan B (Spec (.of k)) hk fun _ : Bool => affineLineChart k B hk)
  refine ⟨e₀, ?_⟩
  have he : ∀ b : Bool,
      Sigma.ι (fun _ : Bool => (BigFppfOver.toScheme B (Spec (.of k)) hk).obj
        (affineLineChart k B hk)) b ≫ e₀.hom =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartPairIncl k B hk b) := he₀
  set e : (∐ fun _ : Bool =>
      (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk)) ≅
      (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (chartPair k B hk) := e₀ with hedef
  have hgdesc : e.hom ≫
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartPairToAffineLine k B hk) =
      Sigma.desc fun b : Bool =>
        (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartTwist k B hk b) := by
    refine Sigma.hom_ext _ _ fun b => ?_
    rw [Sigma.ι_comp_desc, ← Category.assoc]
    refine (congrArg (· ≫ (BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (chartPairToAffineLine k B hk)) (he b)).trans ?_
    rw [← Functor.map_comp, chartPairIncl_comp_chartPairToAffineLine]
  rw [← hgdesc, Iso.inv_hom_id_assoc]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **The right edge of the square of Stacks 05ZI is finite locally free of degree two.** The
disjoint union of two copies of the affine line is, by any pair of automorphisms of the affine
line, finite locally free of rank two over it. -/
theorem isFiniteLocallyFreeOfRank_toScheme_map_chartPairToAffineLine :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartPairToAffineLine k B hk)) 2 := by
  obtain ⟨e, hfac⟩ := exists_iso_toScheme_map_chartPairToAffineLine k B hk
  have h0 := isFiniteLocallyFreeOfRank_sigmaDesc_of_isIso
    (X := (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk))
    (ι := Bool)
    (fun b : Bool => (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartTwist k B hk b))
  rw [hfac]
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp e.symm _ (by simpa using h0)

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **The right edge of the square of Stacks 05ZI is étale.** Being étale is Zariski local at
the source and each twist of the chart is an isomorphism. -/
theorem etale_toScheme_map_chartPairToAffineLine :
    Etale ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartPairToAffineLine k B hk)) := by
  obtain ⟨e, hfac⟩ := exists_iso_toScheme_map_chartPairToAffineLine k B hk
  have h0 : Etale (Sigma.desc fun b : Bool =>
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartTwist k B hk b)) :=
    etale_sigmaDesc _ fun _ => inferInstance
  rw [hfac]
  exact MorphismProperty.RespectsIso.precomp (@Etale.{u} : MorphismProperty Scheme.{u})
    e.inv _ h0

/-! ### The covering is representable, finite étale of degree two -/

/-- **The morphism `Y ⟶ X` of Stacks 05ZI is representable.** Away from characteristic two the
quotient of Stacks 05Z6 is an algebraic space, so its diagonal is representable, and every
morphism from a representable presheaf to it is representable. -/
theorem relativelyRepresentable_coveringMorphism (hchar : (2 : k) ≠ 0) :
    yoneda.relativelyRepresentable (coveringMorphism k B hk) :=
  Space.relativelyRepresentable_of_isAlgebraicSpace B (Spec (.of k)) hk
    (isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar) (coveringMorphism k B hk)

/-- **Every property of the right edge of the square of Stacks 05ZI which satisfies fppf descent
passes to the morphism `Y ⟶ X`.** The chart `𝐀¹_k ⟶ X` of Stacks 05Z6 is surjective and étale,
the square of the remark is cartesian with right edge the given morphism of schemes, and the
morphism `Y ⟶ X` is representable; so Stacks 03I2 applies with no further descent hypothesis. -/
theorem presheaf_coveringMorphism_of_chartPairToAffineLine (hchar : (2 : k) ≠ 0)
    {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hQbc : Q.IsStableUnderBaseChange)
    (hQ : Q ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartPairToAffineLine k B hk))) :
    (Q.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (coveringMorphism k B hk) :=
  Space.presheaf_of_surjectiveEtaleChart_of_descendsAlong
    (relativelyRepresentable_coveringMorphism k B hk hchar)
    (presheafSurjective_quotientChart k B hk hchar)
    (presheafEtale_quotientChart k B hk hchar)
    (isPullback_chartPairToDoubledLine k B hk hchar)
    (Space.presheaf_yoneda_map_of_inverseImage B (Spec (.of k)) hk hQbc
      (chartPairToAffineLine k B hk) hQ)

/-- **The morphism `Y ⟶ X` of Stacks 05ZI is finite locally free of degree two.** Away from
characteristic two the square of the remark is cartesian, its right edge is finite locally free
of degree two, and that property descends along the fppf coverings of the site. -/
theorem presheaf_isFiniteLocallyFreeOfRank_coveringMorphism (hchar : (2 : k) ≠ 0) :
    ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} 2).inverseImage
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf (coveringMorphism k B hk) :=
  have _ := Space.isFiniteLocallyFreeOfRank_descendsAlong_fppf.{u} 2
  presheaf_coveringMorphism_of_chartPairToAffineLine k B hk hchar
    (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} 2))
    (isFiniteLocallyFreeOfRank_toScheme_map_chartPairToAffineLine k B hk)

/-- **The morphism `Y ⟶ X` of Stacks 05ZI is étale.** Away from characteristic two the square
of the remark is cartesian, its right edge is étale, and étaleness descends along the fppf
coverings of the site. -/
theorem presheaf_etale_coveringMorphism (hchar : (2 : k) ≠ 0) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf (coveringMorphism k B hk) :=
  have _ := Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  presheaf_coveringMorphism_of_chartPairToAffineLine k B hk hchar
    (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@Etale.{u} : MorphismProperty Scheme.{u}))
    (etale_toScheme_map_chartPairToAffineLine k B hk)

/-! ### The covering is connected -/

/-- **Stacks 05ZI: the affine line with its origin doubled is connected.** Its two charts are
copies of the affine line, which is irreducible, hence connected; they cover the glued scheme;
and their images meet, because the two charts agree on the punctured line, which has a point. -/
theorem connectedSpace_doubledLine : ConnectedSpace (doubledLine k).left := by
  have _hirr : IrreducibleSpace (affineLine k).left := irreducibleSpace_affineLine k
  obtain ⟨η, hη, -⟩ := exists_genericPoint_affineLine k
  have hcomm : (puncturedAffineLineOpen k).ι ≫ (doubledLineData k).chart true =
      (puncturedAffineLineOpen k).ι ≫ (doubledLineData k).chart false :=
    doubleSectionCover_chart_agree (affineLine k).left (puncturedAffineLineOpen k)
  have hinter : (Set.range ((doubledLineData k).chart true) ∩
      Set.range ((doubledLineData k).chart false)).Nonempty :=
    ⟨(doubledLineData k).chart true ((puncturedAffineLineOpen k).ι ⟨η, hη⟩), ⟨_, rfl⟩,
      ⟨_, (congrArg (fun g => g ⟨η, hη⟩) hcomm).symm⟩⟩
  have hc0 : _root_.IsConnected (Set.range ((doubledLineData k).chart true)) :=
    isConnected_range (Scheme.Hom.continuous _)
  have hc1 : _root_.IsConnected (Set.range ((doubledLineData k).chart false)) :=
    isConnected_range (Scheme.Hom.continuous _)
  have huniv : Set.range ((doubledLineData k).chart true) ∪
      Set.range ((doubledLineData k).chart false) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨b, y, hy⟩ := (doubledLineData k).exists_chart_eq z
    cases b
    · exact Or.inr ⟨y, hy⟩
    · exact Or.inl ⟨y, hy⟩
  exact connectedSpace_iff_univ.mpr (huniv ▸ hc0.union hinter hc1)

/-! ### The covering is nontrivial -/

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Negation of the coordinate on the chart `𝐀¹_k`, read on the underlying schemes of the
site. -/
@[simp]
theorem toScheme_map_chartNeg :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartNeg k B hk) = (affineLineNeg k).left :=
  congrArg Over.Hom.left (post_chartNeg k B hk)

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- **The right edge of the square of Stacks 05ZI admits no section compatible with the relation
of Stacks 02Z1.** Away from characteristic two there is no morphism `u : 𝐀¹_k ⟶ Y₁ ⨿ Y₂` which
is a section of the right edge and whose composite with the top edge is unchanged by negation of
the coordinate on the punctured line.

Decomposing `𝐀¹_k` along `u` places `u` in a single copy of the chart over each member of an
open cover by two pieces, and the two pieces have disjoint images, by
`AlgebraicGeometry.AffineLineInvolution.isEmpty_of_comp_chartTwist_eq`; the affine line being
irreducible, one piece is therefore the whole line. Over that piece both the standard coordinate
and its negative are carried by the *same* copy of the chart, and a chart of the doubled line is
a monomorphism, so on the fibre product of the piece with the punctured line the coordinate
equals its own negative — which that fibre product, containing a point above the generic point
of the punctured line, forbids. -/
theorem not_exists_section_chartPairToAffineLine (hchar : (2 : k) ≠ 0) :
    ¬ ∃ u : affineLineChart k B hk ⟶ chartPair k B hk,
      u ≫ chartPairToAffineLine k B hk = 𝟙 (affineLineChart k B hk) ∧
      puncturedChartInclusion k B hk ≫ u ≫ chartPairToDoubledLine k B hk =
        (puncturedChartInclusion k B hk ≫ chartNeg k B hk) ≫ u ≫
          chartPairToDoubledLine k B hk := by
  classical
  rintro ⟨u, hu, hstar⟩
  obtain ⟨W, p, c, hoi, hcov, hfac⟩ := exists_chartPair_decomposition k B hk u
  -- over the `b`-th piece the section is the `b`-th twist of the piece's own map to the chart
  have hc : ∀ (b : Bool) {Z} (f : chartPair k B hk ⟶ Z) (g : affineLineChart k B hk ⟶ Z),
      chartPairIncl k B hk b ≫ f = g → c b ≫ g = p b ≫ u ≫ f := by
    intro b Z f g h
    rw [← h, ← Category.assoc, hfac b, Category.assoc]
  have hcA : ∀ b, c b ≫ chartTwist k B hk b = p b := fun b =>
    (hc b _ _ (chartPairIncl_comp_chartPairToAffineLine k B hk b)).trans
      (by rw [hu, Category.comp_id])
  have hcD : ∀ b, c b ≫ doubledChartHom k B hk b = p b ≫ u ≫ chartPairToDoubledLine k B hk :=
    fun b => hc b _ _ (chartPairIncl_comp_chartPairToDoubledLine k B hk b)
  -- the two pieces have disjoint images
  have hdisj : ∀ x : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk),
      x ∈ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p false)) →
      x ∉ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p true)) := by
    rintro x ⟨y, hy⟩ ⟨y', hy'⟩
    have hD : (Limits.pullback.fst (p false) (p true) ≫ c false) ≫
          doubledChartHom k B hk false =
        (Limits.pullback.snd (p false) (p true) ≫ c true) ≫ doubledChartHom k B hk true := by
      simp only [Category.assoc, hcD]
      rw [← Category.assoc, ← Category.assoc, Limits.pullback.condition]
      simp only [Category.assoc]
    have hA : (Limits.pullback.fst (p false) (p true) ≫ c false) ≫ chartTwist k B hk false =
        (Limits.pullback.snd (p false) (p true) ≫ c true) ≫ chartTwist k B hk true := by
      rw [Category.assoc, Category.assoc, hcA false, hcA true, Limits.pullback.condition]
    obtain ⟨z, -, -⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback (p false) (p true)).map
        (BigFppfOver.toScheme B (Spec (.of k)) hk)) y y' (by rw [hy, hy'])
    exact (isEmpty_of_comp_chartTwist_eq k B hk hchar (by decide) _ _ hD hA).false z
  -- the affine line is irreducible, so one piece is empty and the other is everything
  have _hirr : IrreducibleSpace
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk)) := by
    change IrreducibleSpace (affineLine k).left
    exact irreducibleSpace_affineLine k
  have hopen : ∀ b, IsOpen (Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b))) := fun b =>
    have := hoi b
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b) |>.isOpenEmbedding.isOpen_range
  have hsome : (∀ x, x ∉ Set.range
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p false))) ∨
      ∀ x, x ∉ Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p true)) := by
    rcases Set.eq_empty_or_nonempty (Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p false))) with h0 | ⟨x₀, hx₀⟩
    · exact Or.inl fun x hx => by rw [h0] at hx; exact hx
    rcases Set.eq_empty_or_nonempty (Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p true))) with h1 | ⟨x₁, hx₁⟩
    · exact Or.inr fun x hx => by rw [h1] at hx; exact hx
    obtain ⟨z, -, hz₀, hz₁⟩ := (IrreducibleSpace.isIrreducible_univ
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (affineLineChart k B hk))).2
      _ _ (hopen false) (hopen true) ⟨x₀, trivial, hx₀⟩ ⟨x₁, trivial, hx₁⟩
    exact absurd hz₁ (hdisj z hz₀)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Bool, ∀ x, x ∉ Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p b₀)) :=
    hsome.elim (fun h => ⟨false, h⟩) fun h => ⟨true, h⟩
  have hall : ∀ x, x ∈ Set.range
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (p (!b₀))) := by
    intro x
    obtain ⟨b', hb'⟩ := hcov x
    cases b₀ <;> cases b' <;> first
      | exact absurd hb' (hb₀ x)
      | exact hb'
  -- a point of the fibre product of that piece with the punctured line
  obtain ⟨η, hη, -⟩ := exists_genericPoint_affineLine k
  obtain ⟨y, hy⟩ := hall η
  have hsq := (IsPullback.of_hasPullback (p (!b₀)) (puncturedChartInclusion k B hk)).map
    (BigFppfOver.toScheme B (Spec (.of k)) hk)
  obtain ⟨t, -, -⟩ := Scheme.exists_preimage_of_isPullback hsq y
    (show (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (puncturedAffineLineChart k B hk) from
      ⟨η, hη⟩) (by rw [hy, toScheme_map_puncturedChartInclusion]; rfl)
  -- the negated coordinate also lands in that piece
  obtain ⟨z₂, hz₂, -⟩ := BigFppfOver.existsUnique_lift_of_isOpenImmersion (p (!b₀)) (hoi (!b₀))
    (Limits.pullback.snd (p (!b₀)) (puncturedChartInclusion k B hk) ≫
      puncturedChartInclusion k B hk ≫ chartNeg k B hk) (fun x _ => hall x)
  -- so the coordinate equals its own negative on the fibre product, which has a point
  have hD : (Limits.pullback.fst (p (!b₀)) (puncturedChartInclusion k B hk) ≫ c (!b₀)) ≫
        doubledChartHom k B hk (!b₀) =
      (z₂ ≫ c (!b₀)) ≫ doubledChartHom k B hk (!b₀) := by
    calc (Limits.pullback.fst (p (!b₀)) (puncturedChartInclusion k B hk) ≫ c (!b₀)) ≫
          doubledChartHom k B hk (!b₀)
        = (Limits.pullback.fst (p (!b₀)) (puncturedChartInclusion k B hk) ≫ p (!b₀)) ≫
            u ≫ chartPairToDoubledLine k B hk := by simp only [Category.assoc, hcD]
      _ = (Limits.pullback.snd (p (!b₀)) (puncturedChartInclusion k B hk) ≫
            puncturedChartInclusion k B hk) ≫ u ≫ chartPairToDoubledLine k B hk := by
            rw [Limits.pullback.condition]
      _ = Limits.pullback.snd (p (!b₀)) (puncturedChartInclusion k B hk) ≫
            (puncturedChartInclusion k B hk ≫ chartNeg k B hk) ≫ u ≫
              chartPairToDoubledLine k B hk := by
            rw [Category.assoc, hstar]
      _ = (z₂ ≫ p (!b₀)) ≫ u ≫ chartPairToDoubledLine k B hk := by
            rw [hz₂]; simp only [Category.assoc]
      _ = (z₂ ≫ c (!b₀)) ≫ doubledChartHom k B hk (!b₀) := by
            simp only [Category.assoc, hcD]
  have heq := (cancel_mono (doubledChartHom k B hk (!b₀))).mp hD
  have hw : Limits.pullback.snd (p (!b₀)) (puncturedChartInclusion k B hk) ≫
        puncturedChartInclusion k B hk =
      Limits.pullback.snd (p (!b₀)) (puncturedChartInclusion k B hk) ≫
        puncturedChartInclusion k B hk ≫ chartNeg k B hk := by
    have h2 := congrArg (· ≫ chartTwist k B hk (!b₀)) heq
    simp only [Category.assoc, hcA] at h2
    rw [Limits.pullback.condition, hz₂] at h2
    simpa only [Category.assoc] using h2
  have h' := congrArg (BigFppfOver.toScheme B (Spec (.of k)) hk).map hw
  simp only [Functor.map_comp, toScheme_map_puncturedChartInclusion, toScheme_map_chartNeg] at h'
  exact (isEmpty_of_comp_puncturedAffineLineOpen_ι_eq k hchar
    (B.inclusion.map (Limits.pullback (p (!b₀)) (puncturedChartInclusion k B hk)).hom)
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (Limits.pullback.snd (p (!b₀)) (puncturedChartInclusion k B hk))) h').false t

/-- **Stacks 05ZI: the covering `Y ⟶ X` is nontrivial — it admits no section.** A section of
`Y ⟶ X` restricts, along the chart `𝐀¹_k ⟶ X` of Stacks 05Z6, to a section of the right edge
`Y₁ ⨿ Y₂ ⟶ 𝐀¹_k` of the cartesian square of the remark, and the relation of Stacks 02Z1 makes
that section unchanged by negation of the coordinate on the punctured line;
`AlgebraicGeometry.AffineLineInvolution.not_exists_section_chartPairToAffineLine` rules such a
section out. -/
theorem not_exists_section_coveringMorphism (hchar : (2 : k) ≠ 0) :
    ¬ ∃ s : (involutionQuotient k B hk).obj ⟶ yoneda.obj (doubledLineSite k B hk),
      s ≫ coveringMorphism k B hk = 𝟙 (involutionQuotient k B hk).obj := by
  rintro ⟨s, hs⟩
  refine not_exists_section_chartPairToAffineLine k B hk hchar ?_
  -- the restriction of the section to the chart, as a morphism of the site
  set σ : affineLineChart k B hk ⟶ doubledLineSite k B hk :=
    yoneda.preimage (quotientChart k B hk ≫ s) with hσ
  have hσmap : yoneda.map σ = quotientChart k B hk ≫ s := yoneda.map_preimage _
  have hσcov : yoneda.map σ ≫ coveringMorphism k B hk = quotientChart k B hk := by
    rw [hσmap, Category.assoc, hs, Category.comp_id]
  -- the cartesian square lifts it to a section of the right edge
  obtain ⟨u₀, hu₀D, hu₀A⟩ : ∃ u₀ : yoneda.obj (affineLineChart k B hk) ⟶
      yoneda.obj (chartPair k B hk),
      u₀ ≫ yoneda.map (chartPairToDoubledLine k B hk) = yoneda.map σ ∧
      u₀ ≫ yoneda.map (chartPairToAffineLine k B hk) = 𝟙 _ :=
    ⟨(isPullback_chartPairToDoubledLine k B hk hchar).lift (yoneda.map σ) (𝟙 _)
      (by rw [hσcov, Category.id_comp]),
     (isPullback_chartPairToDoubledLine k B hk hchar).lift_fst _ _ _,
     (isPullback_chartPairToDoubledLine k B hk hchar).lift_snd _ _ _⟩
  obtain ⟨u, rfl⟩ := yoneda.map_surjective u₀
  refine ⟨u, yoneda.map_injective ?_, yoneda.map_injective ?_⟩
  · rw [Functor.map_comp, hu₀A, CategoryTheory.Functor.map_id]
  · -- the relation of Stacks 02Z1, composed with the section
    have hrel : yoneda.map (puncturedChartInclusion k B hk) ≫ yoneda.map σ =
        yoneda.map (puncturedChartNeg k B hk) ≫ yoneda.map σ := by
      rw [hσmap, ← Category.assoc, ← Category.assoc, yoneda_puncturedChart_comp_quotientChart]
    rw [puncturedChartNeg_eq_comp] at hrel
    simp only [Functor.map_comp, Category.assoc, hu₀D]
    simpa only [Functor.map_comp, Category.assoc] using hrel

/-! ### Stacks 05ZI: the covering clause of the remark -/

/-- **Stacks 05ZI.** The affine line with its origin doubled is a *nontrivial connected finite
étale covering of degree two* of the algebraic space `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` of
Stacks 05Z6: the morphism `Y ⟶ X` of the remark is representable and finite locally free of
degree two, it is étale, `Y` is a connected scheme, and `Y ⟶ X` admits no section.

The remark states this for `k` algebraically closed of characteristic zero; invertibility of two
in the ground field is all that is used. Nontriviality is expressed by the absence of a section:
a covering which is a finite disjoint union of copies of its base has one, so a covering without
one is not such a disjoint union. -/
@[stacks 05ZI "the remark's covering: Y, the affine line with its origin doubled, is a \
nontrivial connected finite étale covering of X of degree two"]
theorem nontrivial_connected_finiteEtale_degreeTwo_coveringMorphism (hchar : (2 : k) ≠ 0) :
    ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} 2).inverseImage
        (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf (coveringMorphism k B hk) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf (coveringMorphism k B hk) ∧
      ConnectedSpace (doubledLine k).left ∧
      ¬ ∃ s : (involutionQuotient k B hk).obj ⟶ yoneda.obj (doubledLineSite k B hk),
        s ≫ coveringMorphism k B hk = 𝟙 (involutionQuotient k B hk).obj :=
  ⟨presheaf_isFiniteLocallyFreeOfRank_coveringMorphism k B hk hchar,
    presheaf_etale_coveringMorphism k B hk hchar,
    connectedSpace_doubledLine k,
    not_exists_section_coveringMorphism k B hk hchar⟩

end AlgebraicGeometry.AffineLineInvolution

end

module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionEtaleChart

/-!
# The doubled-origin cover of the involution quotient

Stacks 05ZI builds a nontrivial connected finite étale covering of the algebraic space
`X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` of Stacks 05Z6 out of the affine line with its origin doubled,
the scheme of Stacks 01JD: the two charts of the doubled line are mapped to `X` by the chart
`𝐀¹_k ⟶ X` of Stacks 05Z6, the first through the identity and the second through negation of
the coordinate, and these two maps *agree on the overlap of the two charts*, which is the
punctured affine line. This file supplies that agreement and the connectedness of the doubled
line, together with the datum of the alternative construction of the same remark: the involution
of the doubled line which negates the coordinates and swaps the two charts, whose quotient the
source identifies with `X`.

## Main definitions

* `AlgebraicGeometry.AffineLineInvolution.puncturedAffineLineChart`: the punctured affine line
  as an object of a big fppf site containing `Spec k`.
* `AlgebraicGeometry.AffineLineInvolution.puncturedChartInclusion` and
  `AlgebraicGeometry.AffineLineInvolution.puncturedChartNeg`: the two morphisms of that site
  from the punctured affine line to the affine line, the inclusion and the inclusion followed
  by negation of the coordinate.
* `AlgebraicGeometry.negAffineSpace`: negation of the coordinates of affine `n`-space.
* `AlgebraicGeometry.chartSwapNegationData` and `AlgebraicGeometry.chartSwapNegation`: the
  endomorphism of affine space with doubled origin which negates the coordinates and swaps the
  two charts, with its restriction to each chart.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.whiskerLeft_punctured_comp_toQuotientSheaf`: the two
  maps from the punctured affine line to the quotient sheaf of Stacks 02Z1, through the
  inclusion and through negation, agree. No hypothesis on the ground field is used.
* `AlgebraicGeometry.AffineLineInvolution.yoneda_puncturedChart_comp_quotientChart`: the same
  identity for the chart `𝐀¹_k ⟶ X` of Stacks 05Z6, read on the presheaves represented by
  objects of the site. This is the gluing datum of the covering of Stacks 05ZI.
* `AlgebraicGeometry.connectedSpace_affineSpaceWithDoubledZero`: in positive dimension affine
  space with its origin doubled is a connected scheme.
* `AlgebraicGeometry.chartSwapNegation_comp_self`: negating the coordinates and swapping the
  two charts is an involution of affine space with doubled origin. This is the generator of
  the action of the group of order two of the alternative construction of Stacks 05ZI.

## Implementation notes

The agreement of the two maps is the coequalizer identity of the quotient sheaf restricted to
the second summand of the relation scheme `R = 𝐀¹_k ⨿ (𝐀¹_k ∖ \{0\})`: on that summand the two
projections of `AlgebraicGeometry.AffineLineInvolution.involutionRelation` are the inclusion of
the puncture and the inclusion followed by negation, so precomposing
`Stacks.Groupoids.sourceMap_toQuotientSheaf` with the second coproduct inclusion is exactly the
assertion. Nothing about the characteristic enters: the relation is an *equivalence* relation
only away from characteristic two, but the coequalizer identity holds for any pre-relation.

The identity is stated twice. The first form lives on the restricted functors of points, where
the projection to the quotient sheaf is defined, and is proved for an arbitrary functor
presenting a site of `Spec k`-schemes. The second form lives on the presheaves represented by
objects of a big fppf site, where the chart
`AlgebraicGeometry.AffineLineInvolution.quotientChart` is stated; the passage between the two is
`AlgebraicGeometry.Space.pointsYonedaIso_inv_comp_whiskerLeft`, and it needs the punctured
affine line as an object of the site, which is why
`AlgebraicGeometry.AffineLineInvolution.puncturedAffineLineChart` is introduced here. Its size
bound is `AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion` applied to the inclusion of the
puncture, the same bound used for the relation scheme. The second form is proved as a chain of
term-mode steps rather than by rewriting, because the target category of
`CategoryTheory.Over.post AlgebraicGeometry.BigFppfSite.inclusion` is only definitionally the
category of `Spec k`-schemes in which the relation lives.

Connectedness of the doubled line is read off the two charts: each is the spectrum of a
polynomial ring over a field, hence irreducible, the two jointly cover the glued scheme, and in
positive dimension their overlap contains the generic point, so the two chart images are
connected sets with a common point. That the two chart inclusions agree over the overlap is
`AlgebraicGeometry.comp_chartInclusion_eq`.

The involution of the alternative construction is glued from the two chart maps by
`CategoryTheory.Limits.Multicoequalizer.desc`, exactly as the coordinate morphism of
Stacks 01JD is. Its compatibility over the overlap of two distinct charts is again
`AlgebraicGeometry.comp_chartInclusion_eq`, applied to the overlap map followed by negation:
negation preserves the complement of the origin because a coordinate lies in a prime exactly
when its negative does. Over the self-overlap of a chart there is nothing to check, the
transition of a gluing datum at a repeated index being the identity.

**The morphism `Y ⟶ X`.** The gluing of the two chart maps is carried out in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalHomeomorphismEtaleFailure`'s
companion module `StacksFrontier.Examples.Spaces.DoubledLineEtaleCovering`. There the sheaf
condition of the quotient on the Zariski covering of `Y` by its two charts is
`AlgebraicGeometry.AffineLineInvolution.isSheafFor_involutionQuotient_doubledChartHom`, and the
morphism it produces, with its two chart equations, is
`AlgebraicGeometry.AffineLineInvolution.coveringMorphismData`; it is the unique morphism with
those equations. That module presents `Y` as two copies of the chart `𝐀¹_k` of Stacks 05Z6
glued along the punctured affine line, so that the overlap identity below applies to its two
charts with no comparison between the presentations `AffineSpace PUnit (Spec k)` and
`Spec k[x]` of the affine line.

**What is not proved here.** Stacks 05ZI further asserts that `Y ⟶ X` is a nontrivial
connected finite étale covering of degree two, which the source deduces from the cartesian
square `Y ← Y₁ ⨿ Y₂`, `X ← 𝐀¹_k` of the remark, and that Stacks 05ZH fails for universal
homeomorphisms. The latter additionally needs simple connectedness of the affine line in
characteristic zero, which the library does not contain — and which Stacks itself asserts with
the details omitted, under no tag. The alternative construction stops at the involution: that
the action it generates is free, and that the quotient of Stacks 02Z3 by it is `X`, are not
proved.

The remaining assertion of Stacks 05ZI, that a universal homeomorphism `X ⟶ 𝐀¹_k` can be
exhibited directly by `t ↦ t ^ 2` on affine spaces, *is* proved:
`AlgebraicGeometry.Space.universalHomeomorphism_squaringMap`.

## References

* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 02Z3](https://stacks.math.columbia.edu/tag/02Z3)
* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZI](https://stacks.math.columbia.edu/tag/05ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

/-! ### The overlap identity on the restricted functors of points -/

/-- The second coproduct inclusion of the relation scheme of Stacks 02Z1 composed with the
first projection of the relation is the inclusion of the punctured affine line. -/
theorem coprod_inr_comp_involutionRelation_target :
    (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) ≫
        (involutionRelation k).target =
      puncturedAffineLineInclusion k := by
  rw [involutionRelation_target]
  exact coprod.inr_desc _ _

/-- The second coproduct inclusion of the relation scheme of Stacks 02Z1 composed with the
second projection of the relation is the inclusion of the punctured affine line followed by
negation of the coordinate. -/
theorem coprod_inr_comp_involutionRelation_source :
    (coprod.inr : puncturedAffineLine k ⟶ relationScheme k) ≫
        (involutionRelation k).source =
      puncturedAffineLineInclusion k ≫ affineLineNeg k := by
  rw [involutionRelation_source]
  exact coprod.inr_desc _ _

/-- **The overlap identity of Stacks 05ZI.** The two maps from the punctured affine line to the
quotient sheaf of Stacks 02Z1, one through the inclusion of the puncture and one through
negation of the coordinate, agree. No hypothesis on the ground field is used. -/
@[stacks 05ZI "a construction input only: the gluing datum of the covering `Y` of the remark,
at the level of points. NEITHER assertion of the remark is asserted -- not that a universal
homeomorphism of algebraic spaces need be non-representable, and not that Tag 05ZH fails for
universal homeomorphisms"]
theorem whiskerLeft_punctured_comp_toQuotientSheaf {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over (Spec (.of k))) :
    F.op.whiskerLeft (yoneda.map (puncturedAffineLineInclusion k)) ≫
        Stacks.Groupoids.toQuotientSheaf J F (involutionRelation k) =
      F.op.whiskerLeft (yoneda.map (puncturedAffineLineInclusion k ≫ affineLineNeg k)) ≫
        Stacks.Groupoids.toQuotientSheaf J F (involutionRelation k) := by
  rw [← coprod_inr_comp_involutionRelation_source k,
    ← coprod_inr_comp_involutionRelation_target k, Functor.map_comp, Functor.map_comp,
    Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, Category.assoc, Category.assoc]
  exact congrArg (fun z => F.op.whiskerLeft (yoneda.map
    (coprod.inr : puncturedAffineLine k ⟶ relationScheme k)) ≫ z)
    (Stacks.Groupoids.sourceMap_toQuotientSheaf J F (involutionRelation k)).symm

/-! ### The overlap identity on the chart of the quotient -/

variable (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

include hk in
/-- The punctured affine line satisfies the size cutoff of a big fppf site containing
`Spec k`: it is an open subscheme of the affine line. -/
theorem contains_puncturedAffineLine : B.Contains (puncturedAffineLine k).left :=
  Scheme.size_lt_of_isOpenImmersion (puncturedAffineLineOpen k).ι
    (affineLineChart k B hk).left.property

/-- The punctured affine line, as an object of a big fppf site containing `Spec k`. -/
noncomputable def puncturedAffineLineChart : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (ObjectProperty.homMk (puncturedAffineLine k).hom :
    B.obj (contains_puncturedAffineLine k B hk) ⟶ B.obj hk)

/-- The scheme over `Spec k` underlying `puncturedAffineLineChart` is the punctured affine line. -/
@[simp]
theorem puncturedAffineLineChart_post :
    (Over.post B.inclusion).obj (puncturedAffineLineChart k B hk) =
      puncturedAffineLine k := rfl

/-- The inclusion of the punctured affine line into the affine line, as a morphism of the
site. -/
noncomputable def puncturedChartInclusion :
    puncturedAffineLineChart k B hk ⟶ affineLineChart k B hk :=
  (Over.post B.inclusion).preimage
    (X := puncturedAffineLineChart k B hk) (Y := affineLineChart k B hk)
    (puncturedAffineLineInclusion k)

/-- The inclusion of the punctured affine line followed by negation of the coordinate, as a
morphism of the site. -/
noncomputable def puncturedChartNeg :
    puncturedAffineLineChart k B hk ⟶ affineLineChart k B hk :=
  (Over.post B.inclusion).preimage
    (X := puncturedAffineLineChart k B hk) (Y := affineLineChart k B hk)
    (puncturedAffineLineInclusion k ≫ affineLineNeg k)

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-- The restricted functor of points of the punctured affine line is the presheaf represented
by its chart in the site. -/
noncomputable def puncturedPointsIso :
    Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (puncturedAffineLine k) ≅
      yoneda.obj (puncturedAffineLineChart k B hk) :=
  Space.pointsYonedaIso (Over.post B.inclusion) (puncturedAffineLineChart k B hk)

/-- **The gluing datum of the covering of Stacks 05ZI.** The two maps from the punctured affine
line to the quotient `X` of Stacks 05Z6, one through the inclusion of the puncture and one
through negation of the coordinate, agree as morphisms of presheaves on the site.

This is the assertion that the two charts of the affine line with doubled origin have the same
image in `X` over the overlap of the charts, which is what makes the covering of Stacks 05ZI
well defined. No hypothesis on the ground field is used. -/
@[stacks 05ZI "a construction input only: the two chart maps of the doubled-origin line agree
over the overlap, which is the remark's `these agree on the overlap by construction of X`. The
morphism `Y ⟶ X` itself is not constructed and neither assertion of the remark is asserted"]
theorem yoneda_puncturedChart_comp_quotientChart :
    yoneda.map (puncturedChartInclusion k B hk) ≫ quotientChart k B hk =
      yoneda.map (puncturedChartNeg k B hk) ≫ quotientChart k B hk :=
  have eI : yoneda.map (puncturedChartInclusion k B hk) ≫
        (affineLinePointsIso k B hk).inv =
      (puncturedPointsIso k B hk).inv ≫
        (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (puncturedAffineLineInclusion k)) :=
    (Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
      (V := puncturedAffineLineChart k B hk) (W := affineLineChart k B hk)
      (puncturedAffineLineInclusion k)).symm
  have eN : yoneda.map (puncturedChartNeg k B hk) ≫
        (affineLinePointsIso k B hk).inv =
      (puncturedPointsIso k B hk).inv ≫
        (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (puncturedAffineLineInclusion k ≫ affineLineNeg k)) :=
    (Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
      (V := puncturedAffineLineChart k B hk) (W := affineLineChart k B hk)
      (puncturedAffineLineInclusion k ≫ affineLineNeg k)).symm
  calc yoneda.map (puncturedChartInclusion k B hk) ≫ quotientChart k B hk
      = (yoneda.map (puncturedChartInclusion k B hk) ≫
          (affineLinePointsIso k B hk).inv) ≫
            Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
              (Over.post B.inclusion) (involutionRelation k) := (Category.assoc _ _ _).symm
    _ = (puncturedPointsIso k B hk).inv ≫
          ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
              (yoneda.map (puncturedAffineLineInclusion k)) ≫
            Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
              (Over.post B.inclusion) (involutionRelation k)) := by
        rw [eI, Category.assoc]
    _ = (puncturedPointsIso k B hk).inv ≫
          ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
              (yoneda.map (puncturedAffineLineInclusion k ≫ affineLineNeg k)) ≫
            Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
              (Over.post B.inclusion) (involutionRelation k)) :=
        congrArg (fun z => (puncturedPointsIso k B hk).inv ≫ z)
          (whiskerLeft_punctured_comp_toQuotientSheaf k
            (BigFppfOver.topology B (Spec (.of k)) hk) (Over.post (X := B.obj hk) B.inclusion))
    _ = (yoneda.map (puncturedChartNeg k B hk) ≫ (affineLinePointsIso k B hk).inv) ≫
          Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
            (Over.post B.inclusion) (involutionRelation k) := by
        rw [eN, Category.assoc]
    _ = yoneda.map (puncturedChartNeg k B hk) ≫ quotientChart k B hk := Category.assoc _ _ _

end AlgebraicGeometry.AffineLineInvolution

namespace AlgebraicGeometry

/-- The generic point of affine `n`-space, the zero ideal of its coordinate ring. -/
noncomputable def affineGenericPoint (k : Type u) [Field k] (n : ℕ) :
    PrimeSpectrum (MvPolynomial (Fin n) k) :=
  ⟨⊥, Ideal.isPrime_bot⟩

/-- In positive dimension the generic point of affine `n`-space lies in the complement of the
origin. -/
theorem affineGenericPoint_mem_puncturedAffineSpace (k : Type u) [Field k] (n : ℕ)
    (hn : 0 < n) :
    affineGenericPoint k n ∈ puncturedAffineSpace k n :=
  TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨0, hn⟩, (PrimeSpectrum.mem_basicOpen _ _).mpr
      fun hmem => MvPolynomial.X_ne_zero _ (Ideal.mem_bot.mp hmem)⟩

/-- **The connectedness input of Stacks 05ZI.** In positive dimension affine `n`-space over a
field with its origin doubled is a connected scheme: its two charts are spectra of a polynomial
ring, hence irreducible, they cover the glued scheme, and their images share the image of the
generic point. -/
@[stacks 05ZI "a construction input only: the doubled-origin affine space is connected. That
`Y ⟶ X` is a nontrivial connected finite etale covering is NOT asserted -- this library has no
notion of a connected algebraic space"]
theorem connectedSpace_affineSpaceWithDoubledZero (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    ConnectedSpace (affineSpaceWithDoubledZero k n) := by
  have hpunct : Set.range ((puncturedAffineSpace k n).ι).base ⊆
      (puncturedAffineSpace k n : Set _) := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  have hcomm : (puncturedAffineSpace k n).ι ≫ chartInclusion k n 0 =
      (puncturedAffineSpace k n).ι ≫ chartInclusion k n 1 :=
    comp_chartInclusion_eq k n _ hpunct
  obtain ⟨x⟩ : Nonempty (puncturedAffineSpace k n).toScheme :=
    ⟨⟨affineGenericPoint k n, affineGenericPoint_mem_puncturedAffineSpace k n hn⟩⟩
  have hinter : (Set.range (chartInclusion k n 0) ∩
      Set.range (chartInclusion k n 1)).Nonempty :=
    ⟨chartInclusion k n 0 ((puncturedAffineSpace k n).ι x), ⟨_, rfl⟩,
      ⟨_, (congrArg (fun g => g x) hcomm).symm⟩⟩
  have hc0 : _root_.IsConnected (Set.range (chartInclusion k n 0)) :=
    isConnected_range (Scheme.Hom.continuous _)
  have hc1 : _root_.IsConnected (Set.range (chartInclusion k n 1)) :=
    isConnected_range (Scheme.Hom.continuous _)
  have huniv : Set.range (chartInclusion k n 0) ∪ Set.range (chartInclusion k n 1) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨⟨i⟩, w, hw⟩ := (doubledZeroGlueData k n).ι_jointly_surjective z
    have hi : (doubledZeroGlueData k n).ι (ULift.up i) w = chartInclusion k n i w := rfl
    rw [hi] at hw
    fin_cases i
    · exact Or.inl ⟨w, hw⟩
    · exact Or.inr ⟨w, hw⟩
  exact connectedSpace_iff_univ.mpr (huniv ▸ hc0.union hinter hc1)

/-! ### The involution of the alternative construction -/

/-- Negation of all the coordinates, as an endomorphism of the coordinate ring of affine
`n`-space. -/
noncomputable def negCoordRingHom (k : Type u) [Field k] (n : ℕ) :
    MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) k :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)
    fun i => -(MvPolynomial.X i : MvPolynomial (Fin n) k)

/-- `negCoordRingHom` fixes the constant polynomials. -/
@[simp]
theorem negCoordRingHom_C (k : Type u) [Field k] (n : ℕ) (a : k) :
    negCoordRingHom k n (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂_C _ _ a

/-- `negCoordRingHom` sends the coordinate `X i` to `-X i`. -/
@[simp]
theorem negCoordRingHom_X (k : Type u) [Field k] (n : ℕ) (i : Fin n) :
    negCoordRingHom k n (MvPolynomial.X i) =
      -(MvPolynomial.X i : MvPolynomial (Fin n) k) :=
  MvPolynomial.eval₂_X _ _ i

/-- Negating all the coordinates twice is the identity of the coordinate ring. -/
theorem negCoordRingHom_comp_self (k : Type u) [Field k] (n : ℕ) :
    (negCoordRingHom k n).comp (negCoordRingHom k n) = RingHom.id _ :=
  MvPolynomial.ringHom_ext (fun a => by simp) fun i => by simp

/-- Negation of the coordinates of affine `n`-space. -/
noncomputable def negAffineSpace (k : Type u) [Field k] (n : ℕ) :
    Spec (.of (MvPolynomial (Fin n) k)) ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
  Spec.map (CommRingCat.ofHom (negCoordRingHom k n))

/-- Negating the coordinates of affine `n`-space is an involution. -/
theorem negAffineSpace_comp_self (k : Type u) [Field k] (n : ℕ) :
    negAffineSpace k n ≫ negAffineSpace k n = 𝟙 _ := by
  rw [negAffineSpace, ← Spec.map_comp, ← CommRingCat.ofHom_comp, negCoordRingHom_comp_self,
    CommRingCat.ofHom_id, Spec.map_id]

/-- Negation of the coordinates preserves the complement of the origin: a coordinate lies in a
prime exactly when its negative does. -/
theorem negAffineSpace_mem_puncturedAffineSpace (k : Type u) [Field k] (n : ℕ)
    {p : Spec (.of (MvPolynomial (Fin n) k))} (hp : p ∈ puncturedAffineSpace k n) :
    negAffineSpace k n p ∈ puncturedAffineSpace k n := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  refine TopologicalSpace.Opens.mem_iSup.mpr
    ⟨i, (PrimeSpectrum.mem_basicOpen _ _).mpr fun hx => (PrimeSpectrum.mem_basicOpen _ _).mp hi ?_⟩
  have hx' : negCoordRingHom k n (MvPolynomial.X i) ∈ p.asIdeal := hx
  rwa [negCoordRingHom_X, Ideal.neg_mem_iff] at hx'

/-- **Stacks 05ZI, the alternative construction.** The endomorphism of affine space with
doubled origin which negates the coordinates and swaps the two charts, packaged with its
restriction to each chart.

The two chart maps agree over the overlap of the charts because negation preserves the
complement of the origin, so `AlgebraicGeometry.comp_chartInclusion_eq` applies. -/
@[stacks 05ZI "a construction input only: the involution of `Y` of the remark's alternative
route, negating the coordinate and swapping the two charts. That the induced action of `{+1,-1}`
is free and that `X` is its quotient are NOT asserted"]
noncomputable def chartSwapNegationData (k : Type u) [Field k] (n : ℕ) :
    { f : affineSpaceWithDoubledZero k n ⟶ affineSpaceWithDoubledZero k n //
      chartInclusion k n 0 ≫ f = negAffineSpace k n ≫ chartInclusion k n 1 ∧
        chartInclusion k n 1 ≫ f = negAffineSpace k n ≫ chartInclusion k n 0 } := by
  classical
  have hcompat : ∀ a : (doubledZeroGlueData k n).toGlueData.J ×
        (doubledZeroGlueData k n).toGlueData.J,
      (doubledZeroGlueData k n).toGlueData.diagram.fst a ≫
          negAffineSpace k n ≫ chartInclusion k n (1 - a.1.down) =
        (doubledZeroGlueData k n).toGlueData.diagram.snd a ≫
          negAffineSpace k n ≫ chartInclusion k n (1 - a.2.down) := by
    rintro ⟨i, j⟩
    change (doubledZeroGlueData k n).toGlueData.f i j ≫
        negAffineSpace k n ≫ chartInclusion k n (1 - i.down) =
      (doubledZeroGlueData k n).toGlueData.t i j ≫
        (doubledZeroGlueData k n).toGlueData.f j i ≫
          negAffineSpace k n ≫ chartInclusion k n (1 - j.down)
    by_cases hij : i = j
    · subst hij
      rw [(doubledZeroGlueData k n).toGlueData.t_id, Category.id_comp]
    · have hrange : Set.range (((doubledZeroGlueData k n).toGlueData.f i j ≫
          negAffineSpace k n)).base ⊆ (puncturedAffineSpace k n : Set _) := by
        rintro z ⟨w, rfl⟩
        refine negAffineSpace_mem_puncturedAffineSpace k n ?_
        have hw : ((doubledZeroGlueData k n).toGlueData.f i j) w ∈
          ((doubledZeroGlueData k n).toGlueData.f i j).opensRange := ⟨w, rfl⟩
        rwa [opensRange_glueData_f k n hij] at hw
      have key := comp_chartInclusion_eq k n
        ((doubledZeroGlueData k n).toGlueData.f i j ≫ negAffineSpace k n) hrange
      conv_rhs => rw [← Category.assoc, glueData_t_comp_f k n hij]
      obtain ⟨i⟩ := i
      obtain ⟨j⟩ := j
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact key.symm
      · exact key
      · exact absurd rfl hij
  refine ⟨Multicoequalizer.desc (doubledZeroGlueData k n).toGlueData.diagram _
    (fun j => negAffineSpace k n ≫ chartInclusion k n (1 - j.down)) hcompat, ?_, ?_⟩
  · exact Multicoequalizer.π_desc (doubledZeroGlueData k n).toGlueData.diagram
      (affineSpaceWithDoubledZero k n)
      (fun j => negAffineSpace k n ≫ chartInclusion k n (1 - j.down)) hcompat (ULift.up 0)
  · exact Multicoequalizer.π_desc (doubledZeroGlueData k n).toGlueData.diagram
      (affineSpaceWithDoubledZero k n)
      (fun j => negAffineSpace k n ≫ chartInclusion k n (1 - j.down)) hcompat (ULift.up 1)

/-- The endomorphism of affine space with doubled origin which negates the coordinates and
swaps the two charts. In dimension one this is the generator of the action of
`G = \{+1, -1\}` which Stacks 05ZI uses for its alternative construction. -/
noncomputable abbrev chartSwapNegation (k : Type u) [Field k] (n : ℕ) :
    affineSpaceWithDoubledZero k n ⟶ affineSpaceWithDoubledZero k n :=
  (chartSwapNegationData k n).val

/-- **Stacks 05ZI, the alternative construction.** Negating the coordinates and swapping the
two charts of affine space with doubled origin is an involution, so it makes the group of
order two act on that scheme. -/
@[stacks 05ZI "a construction input only: that involution is an involution"]
theorem chartSwapNegation_comp_self (k : Type u) [Field k] (n : ℕ) :
    chartSwapNegation k n ≫ chartSwapNegation k n = 𝟙 _ := by
  refine Multicoequalizer.hom_ext _ _ _ fun b => ?_
  obtain ⟨b⟩ := b
  have h0 : chartInclusion k n 0 ≫ chartSwapNegation k n =
    negAffineSpace k n ≫ chartInclusion k n 1 := (chartSwapNegationData k n).property.1
  have h1 : chartInclusion k n 1 ≫ chartSwapNegation k n =
    negAffineSpace k n ≫ chartInclusion k n 0 := (chartSwapNegationData k n).property.2
  fin_cases b
  · show chartInclusion k n 0 ≫ chartSwapNegation k n ≫ chartSwapNegation k n =
      chartInclusion k n 0 ≫ 𝟙 _
    rw [← Category.assoc, h0, Category.assoc, h1, ← Category.assoc,
      negAffineSpace_comp_self, Category.id_comp, Category.comp_id]
  · show chartInclusion k n 1 ≫ chartSwapNegation k n ≫ chartSwapNegation k n =
      chartInclusion k n 1 ≫ 𝟙 _
    rw [← Category.assoc, h1, Category.assoc, h0, ← Category.assoc,
      negAffineSpace_comp_self, Category.id_comp, Category.comp_id]

end AlgebraicGeometry

end

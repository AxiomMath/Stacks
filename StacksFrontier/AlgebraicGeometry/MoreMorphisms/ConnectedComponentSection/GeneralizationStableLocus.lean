module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FromGenericFibreIrreducibility
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.GeneralizationModel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.GeneralizationNoetherian
public import StacksFrontier.Algebra.Category.Ring.FiniteSubalgebras

/-!
# Stability of the locus `X⁰` under generalization

Let `f : X ⟶ Y` be flat and of finite presentation with geometrically reduced fibres and a
specified section `s`, as in Situation 055L. The locus `X⁰`, the union over `y : Y` of the
connected components of the fibres `X_y` containing `s(y)`, is stable under generalization.

This is the content of the proof of Stacks Tag 055Q, and the residual hypothesis
`AlgebraicGeometry.LocusStableUnderGeneralization` of the Stacks 057K chain.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_over_spec`: the case of an
  affine base.
* `AlgebraicGeometry.locusStableUnderGeneralization`:
  `AlgebraicGeometry.LocusStableUnderGeneralization`.
* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes`: the same statement for one
  sectioned situation, the shape in which Tags 055Q and 055R consume it.

## Implementation notes

The three steps of the Stacks proof are: a reduction to a Noetherian base by a limit argument,
performed over an affine base here and supplied by
`AlgebraicGeometry.ConnectedAlongSection.exists_flat_section_model_of_isLimit`; a reduction to a
discrete valuation ring base, which is
`AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_of_isLocallyNoetherian`; and
the discrete valuation ring case,
`AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_over_dvr`. The three are
joined by the base change formula of Stacks Tag 055M.

Over an affine base `Spec A` the limit is the one over the finitely generated `ℤ`-subalgebras of
`A`, indexed by the finite subsets of `A` ordered by inclusion; each such subalgebra is a
Noetherian ring. The general case follows because the statement is local on the target: a
generalization of a point of `Y` lies in every open subset containing that point.

## References

* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
* [Stacks Project, Tag 055M](https://stacks.math.columbia.edu/tag/055M)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

noncomputable section

/-! ### The system of finitely generated subalgebras -/

/-! ### The case of an affine base -/

/-- **Stability of `X⁰` under generalization over an affine base.** For a flat sectioned
morphism of finite presentation with geometrically reduced fibres over `Spec A`, the locus `X⁰`
is stable under generalization. -/
theorem mem_locus_of_specializes_over_spec {X : Scheme.{u}} (A : CommRingCat.{u})
    (f : X ⟶ Spec A) (s : Spec A ⟶ X) (hsec : s ≫ f = 𝟙 (Spec A))
    (hfp : FinitePresentation f) [Flat f] [GeometricallyReduced f] {x x' : X}
    (hx : x ∈ (⟨X, Spec A, f, s, hsec⟩ : ConnectedAlongSection.{u}).locus) (hspec : x' ⤳ x) :
    x' ∈ (⟨X, Spec A, f, s, hsec⟩ : ConnectedAlongSection.{u}).locus := by
  let D : ConnectedAlongSection.{u} := ⟨X, Spec A, f, s, hsec⟩
  let Dg := A.finiteSubalgebras.op ⋙ Scheme.Spec
  let cBase := Scheme.Spec.mapCone A.finiteSubalgebrasCocone.op
  let c : Cone Dg := { pt := Spec A, π := cBase.π }
  have hc : IsLimit c := by
    show IsLimit cBase
    exact isLimitOfPreserves _ A.finiteSubalgebrasIsColimit.op
  have : ∀ i, IsAffine (Dg.obj i) := fun i => inferInstanceAs (IsAffine (Spec _))
  obtain ⟨k, X₀, f₀, s₀, g', hfp₀, hflat₀, hs₀, hpb, hsc⟩ :=
    exists_flat_section_model_of_isLimit Dg c hc f s hsec hfp inferInstance
  let D₀ : ConnectedAlongSection.{u} := ⟨X₀, Dg.obj k, f₀, s₀, hs₀⟩
  -- The stage `k` is the spectrum of a finitely generated `ℤ`-algebra, hence Noetherian.
  have hNoeth : IsNoetherian (Dg.obj k) := by
    have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ ((unop k : Finset A) : Set A)) :=
      (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
    have : IsNoetherianRing (Algebra.adjoin ℤ ((unop k : Finset A) : Set A)) :=
      Algebra.FiniteType.isNoetherianRing ℤ _
    show IsNoetherian (Spec (CommRingCat.of (Algebra.adjoin ℤ ((unop k : Finset A) : Set A))))
    exact AlgebraicGeometry.IsNoetherian.mk
  have : LocallyOfFinitePresentation f₀ := hfp₀.1
  have : QuasiCompact f₀ := hfp₀.2.1
  have : QuasiSeparated f₀ := hfp₀.2.2
  have hln : IsLocallyNoetherian D₀.X := LocallyOfFiniteType.isLocallyNoetherian f₀
  have hflat : Flat D₀.f := hflat₀
  -- The locus downstairs pulls back to the locus upstairs.
  have hloc : D.locus = g' ⁻¹' D₀.locus :=
    locus_eq_preimage_of_isPullback D₀ D g' (c.π.app k) hpb hsc
  -- Geometric reducedness of the one relevant fibre passes to the model.
  have hfib : f₀ (g' x) = c.π.app k (f x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : X ⟶ Dg.obj k => m x) hpb.w
  have hgr : GeometricallyReduced (f₀.fiberToSpecResidueField (D₀.f (g' x))) := by
    have hset := geometricallyReduced_fiber_set_eq_preimage_of_isPullback f₀ f g'
      (c.π.app k) hpb
    have hmem : f x ∈ {y' : ↥(Spec A) | GeometricallyReduced (f.fiberToSpecResidueField y')} :=
      (inferInstance : GeometricallyReduced (f.fiberToSpecResidueField (f x)))
    rw [hset] at hmem
    show GeometricallyReduced (f₀.fiberToSpecResidueField (f₀ (g' x)))
    rwa [hfib]
  -- Apply the locally Noetherian case to the model.
  rw [hloc]
  exact mem_locus_of_specializes_of_isLocallyNoetherian D₀ hfp₀ hgr (by rwa [hloc] at hx)
    (hspec.map g'.continuous)

/-! ### The general case -/

/-- **Stability of `X⁰` under generalization.** For a flat sectioned morphism of finite
presentation with geometrically reduced fibres, the locus `X⁰` of Situation 055L is stable
under generalization. This is the content of the proof of Stacks Tag 055Q. -/
theorem locusStableUnderGeneralization : LocusStableUnderGeneralization.{u} := by
  intro D hfp hflat hgred x hx x' hspec
  have := hflat
  have := hgred
  -- Shrink the target to an affine open containing the image of `x`.
  obtain ⟨i, z, hz⟩ := D.Y.affineCover.exists_eq (D.f x)
  let Rᵢ : CommRingCat.{u} := Classical.choose (Classical.choose_spec (D.Y.local_affine i))
  let g : Spec Rᵢ ⟶ D.Y := D.Y.affineCover.f i
  have hoig : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (D.Y.affineCover.f i))
  let prᵢ : pullback D.f g ⟶ D.X := pullback.fst D.f g
  let fᵢ : pullback D.f g ⟶ Spec Rᵢ := pullback.snd D.f g
  have hcond : (g ≫ D.s) ≫ D.f = 𝟙 (Spec Rᵢ) ≫ g := by
    rw [Category.assoc, D.section_fac, Category.comp_id, Category.id_comp]
  let sᵢ : Spec Rᵢ ⟶ pullback D.f g := pullback.lift (g ≫ D.s) (𝟙 _) hcond
  have hsecᵢ : sᵢ ≫ fᵢ = 𝟙 (Spec Rᵢ) := pullback.lift_snd _ _ _
  let Dᵢ : ConnectedAlongSection.{u} := ⟨pullback D.f g, Spec Rᵢ, fᵢ, sᵢ, hsecᵢ⟩
  have hPB : IsPullback prᵢ fᵢ D.f g := IsPullback.of_hasPullback D.f g
  have hsPB : Dᵢ.s ≫ prᵢ = g ≫ D.s := pullback.lift_fst _ _ _
  have hloc : Dᵢ.locus = prᵢ ⁻¹' D.locus :=
    locus_eq_preimage_of_isPullback D Dᵢ prᵢ g hPB hsPB
  have hoipr : IsOpenImmersion prᵢ := MorphismProperty.of_isPullback hPB.flip hoig
  -- The two points lie in the open subscheme over the affine open.
  have hrange : ∀ y : D.X, D.f y ∈ Set.range g → ∃ w, prᵢ w = y := fun y hy => by
    rwa [← Set.mem_range, IsOpenImmersion.range_pullbackFst g D.f]
  have hmem : ∀ w, w ∈ Dᵢ.locus ↔ prᵢ w ∈ D.locus := fun w => by rw [hloc]; rfl
  obtain ⟨w, hw⟩ := hrange x ⟨z, hz⟩
  obtain ⟨w', hw'⟩ := hrange x' <|
    (hspec.map D.f.continuous).mem_open g.isOpenEmbedding.isOpen_range ⟨z, hz⟩
  have hspecᵢ : w' ⤳ w :=
    (prᵢ.isOpenEmbedding.isEmbedding.isInducing.specializes_iff).mp (by rw [hw, hw']; exact hspec)
  -- The hypotheses pass to the base change.
  have hfpᵢ : FinitePresentation fᵢ := by
    have : LocallyOfFinitePresentation D.f := hfp.1
    have : QuasiCompact D.f := hfp.2.1
    have : QuasiSeparated D.f := hfp.2.2
    exact ⟨MorphismProperty.of_isPullback hPB inferInstance,
      MorphismProperty.of_isPullback hPB inferInstance,
      MorphismProperty.of_isPullback hPB inferInstance⟩
  have : Flat fᵢ := MorphismProperty.of_isPullback hPB inferInstance
  have : GeometricallyReduced fᵢ := MorphismProperty.of_isPullback hPB inferInstance
  have hconcl := mem_locus_of_specializes_over_spec Rᵢ fᵢ sᵢ hsecᵢ hfpᵢ
    ((hmem w).2 (hw ▸ hx)) hspecᵢ
  exact hw' ▸ (hmem w').1 hconcl

end

end ConnectedAlongSection

/-- **Stability of the locus `X⁰` under generalization**, the residual hypothesis of the Stacks
057K chain. This is the content of the proof of Stacks Tag 055Q. -/
alias locusStableUnderGeneralization := ConnectedAlongSection.locusStableUnderGeneralization

/-- Stability of the locus `X⁰` under generalization at a single sectioned situation, the shape
in which Tags 055Q and 055R consume it. -/
theorem ConnectedAlongSection.mem_locus_of_specializes (D : ConnectedAlongSection.{u})
    (hfp : FinitePresentation D.f) [Flat D.f] [GeometricallyReduced D.f] :
    ∀ x ∈ D.locus, ∀ x' : D.X, x' ⤳ x → x' ∈ D.locus :=
  locusStableUnderGeneralization.{u} D hfp

end AlgebraicGeometry

end

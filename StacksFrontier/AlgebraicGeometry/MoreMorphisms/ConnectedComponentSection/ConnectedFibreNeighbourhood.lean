module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.MultisectionDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp

/-!
# Stacks Tag 057I

Let `f : X ⟶ Y` be flat and of finite presentation with geometrically reduced fibres, let
`g : Z ⟶ Y` be finite locally free with a lift `σ : Z ⟶ X`, and let `y : Y` be a point with
nonempty fibre in `Z` whose fibre in `X` is geometrically connected. Then `y` has a
quasi-compact open neighbourhood of its whole fibre in `X` all of whose nonempty fibres are
geometrically connected.

The proof takes the locus `X⁰ ⊆ X ×_Y Z` of fibrewise connected components met by the
tautological section of `X ×_Y Z ⟶ Z`, which is open by Tag 055R and locally constructible by
Tag 055P, intersects it with the preimage of an affine open neighbourhood of `y` to make it
compact, and descends the result along the finite locally free first projection
`X ×_Y Z ⟶ X`. The descent is legitimate because the two tautological sections of the base
change of `f` along `Z ×_Y Z ⟶ Y` select the same fibrewise connected component over a
neighbourhood of `y`.

## Main results

* `ConnectedComponentSection.exists_isCompact_opens_geometricallyConnected_fibers` is Tag 057I,
  granted Tags 055P and 055R.
* `AlgebraicGeometry.ConnectedComponentSection.statement057I` is the same result in the shape of
  `AlgebraicGeometry.Statement057I`, so that it discharges that hypothesis by `exact`.

## Implementation notes

The two inputs which are not yet available are taken as explicit hypotheses
`AlgebraicGeometry.Statement055P` and `AlgebraicGeometry.Statement055R`; everything else is
proved here. Because of those two hypotheses the covering declaration is deliberately left
untagged: it does not yet state Tag 057I unconditionally.

## References

* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms Topology

universe u

namespace AlgebraicGeometry.ConnectedComponentSection

/-- **Stacks Project, Tag 057I**, granted Tags 055P and 055R. A geometrically connected fibre
in a flat, finitely presented family with geometrically reduced fibres and a nonempty finite
locally free multisection has a quasi-compact open neighbourhood in the source whose nonempty
fibres are geometrically connected. -/
theorem exists_isCompact_opens_geometricallyConnected_fibers
    (h055P : Statement055P.{u}) (h055R : Statement055R.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (σ : Z ⟶ X) (hσ : σ ≫ f = g) (y : Y)
    (hfp : FinitePresentation f) (hflat : Flat f) (hflf : IsFiniteLocallyFree g)
    (hZy : Nonempty (g.fiber y))
    (hreduced : ∀ y' : Y, GeometricallyReduced (f.fiberToSpecResidueField y'))
    (hconnected : GeometricallyConnected (f.fiberToSpecResidueField y)) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ (f.fiberι y ⁻¹ᵁ U = ⊤ ∧
      ∀ y' : Y, Nonempty ((U.ι ≫ f).fiber y') →
        GeometricallyConnected ((U.ι ≫ f).fiberToSpecResidueField y')) := by
  have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  have : QuasiCompact f := hfp.quasiCompact
  have : QuasiSeparated f := hfp.quasiSeparated
  have : IsFinite g :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp hflf).1
  have hk₀ : (pullback.fst g g ≫ σ) ≫ f = pullback.fst g g ≫ g := by rw [Category.assoc, hσ]
  have hk₁ : (pullback.snd g g ≫ σ) ≫ f = pullback.fst g g ≫ g := by
    rw [Category.assoc, hσ, pullback.condition]
  obtain ⟨V, hVopen, hyV, hcross⟩ :=
    exists_nhd_cross_section h055R f g y hfp hflat hreduced hconnected hk₀ hk₁
  have hagree : ∀ a : ↥(pullback f (pullback.fst g g ≫ g)),
      (pullback.fst g g ≫ g) ((pullback.snd f (pullback.fst g g ≫ g)) a) ∈ V →
        (a ∈ (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).locus ↔
          a ∈ (sectionedPullback f (pullback.fst g g ≫ g) (pullback.snd g g ≫ σ) hk₁).locus) :=
    fun a ha => locus_congr_of_cross_component (pullback.snd f (pullback.fst g g ≫ g))
      (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).s
      (sectionedPullback f (pullback.fst g g ≫ g) (pullback.snd g g ≫ σ) hk₁).s
      (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
      ((pullback.fst g g ≫ g) ⁻¹' V) (fun w hw => (hcross w hw).1)
      (fun w hw => (hcross w hw).2) a ha
  obtain ⟨_, ⟨V₀, hV₀aff, rfl⟩, hyV₀, hV₀V⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyV hVopen
  let W : (pullback f g : Scheme.{u}).Opens := (pullback.fst f g ≫ f) ⁻¹ᵁ V₀
  have hEcompact : IsCompact ((pullback.fst f g ≫ f) ⁻¹' (V₀ : Set Y)) :=
    QuasiCompact.isCompact_preimage _ V₀.2 hV₀aff.isCompact
  have hWqs : QuasiSeparatedSpace (W : Set ↥(pullback f g)) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ W.2).mp
      ((pullback.fst f g ≫ f).isQuasiSeparated_preimage hV₀aff.isQuasiSeparated)
  have hAcompact : IsCompact ((sectionedPullback f g σ hσ).locus ∩
      (W : Set ↥(pullback f g))) :=
    isCompact_inter_compact_open_of_isLocallyConstructible _ _
      (isLocallyConstructible_locus h055P _ inferInstance inferInstance inferInstance)
      W.2 hEcompact hWqs
  have hcond : ∀ {A B C : Scheme.{u}} (a : A ⟶ C) (b : B ⟶ C) (e : ↥(pullback a b)),
      a (pullback.fst a b e) = b (pullback.snd a b e) := fun a b e => by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun φ : (pullback a b : Scheme.{u}) ⟶ _ => φ e)
        (pullback.condition (f := a) (g := b))
  have hfib : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (b : B) (x : a.fiber b), a (a.fiberι b x) = b :=
    fun a b x => by
      have h : a.fiberι b x ∈ Set.range (a.fiberι b) := ⟨x, rfl⟩
      rw [a.range_fiberι] at h
      simpa using h
  have hV₀mem : ∀ w : ↥(pullback f g), (pullback.fst f g ≫ f) w ∈ (V₀ : Set Y) ↔
      g (pullback.snd f g w) ∈ (V₀ : Set Y) := fun w => by
    rw [Scheme.Hom.comp_apply, hcond]
  have hBcompat : ∀ r : ↥(pullback (pullback.fst f g) (pullback.fst f g)),
      pullback.fst (pullback.fst f g) (pullback.fst f g) r ∈
          (sectionedPullback f g σ hσ).locus ∩ (pullback.fst f g ≫ f) ⁻¹' (V₀ : Set Y) ↔
        pullback.snd (pullback.fst f g) (pullback.fst f g) r ∈
          (sectionedPullback f g σ hσ).locus ∩ (pullback.fst f g ≫ f) ⁻¹' (V₀ : Set Y) := by
    intro r
    have heq : (pullback.fst f g ≫ f) (pullback.fst (pullback.fst f g) (pullback.fst f g) r) =
        (pullback.fst f g ≫ f) (pullback.snd (pullback.fst f g) (pullback.fst f g) r) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg f (hcond (pullback.fst f g) (pullback.fst f g) r)
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← heq]
    by_cases hv : (pullback.fst f g ≫ f) (pullback.fst (pullback.fst f g) (pullback.fst f g) r) ∈ V
    · exact and_congr (locus_compat_of_cross_agree f g σ hσ hk₀ hk₁ V hagree r hv) Iff.rfl
    · exact iff_of_false (fun h => hv (hV₀V h.2)) (fun h => hv (hV₀V h.2))
  have : IsFiniteLocallyFree (pullback.fst f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f g).flip hflf
  obtain ⟨hUopen, hUcompact, hpre⟩ :=
    compact_open_image_of_pullback_compatible_open (pullback.fst f g)
      ((sectionedPullback f g σ hσ).locus ∩ (W : Set ↥(pullback f g)))
      (finiteLocallyFree_isOpenMap_and_isClosedMap (pullback.fst f g)).1
      ((sectionedPullback_locus_isOpen h055R f g σ hσ hfp hflat hreduced).inter W.2) hAcompact
      hBcompat
  have hgc : ∀ U : X.Opens, pullback.fst f g ⁻¹' U =
      (sectionedPullback f g σ hσ).locus ∩ (pullback.fst f g ≫ f) ⁻¹' (V₀ : Set Y) →
      ∀ z : Z, g z ∈ (V₀ : Set Y) →
        GeometricallyConnected ((U.ι ≫ f).fiberToSpecResidueField (g z)) := by
    intro U hU z hz
    have hq : ∀ w : ↥(pullback f g), pullback.snd f g w = z →
        (pullback.fst f g ≫ f) w ∈ (V₀ : Set Y) :=
      fun w hw => (hV₀mem w).2 (by rwa [hw])
    have hO : (pullback.snd f g).fiberι z ⁻¹'
          ((pullback.fst f g ⁻¹ᵁ U : (pullback f g : Scheme.{u}).Opens) : Set ↥(pullback f g)) =
        (pullback.snd f g).fiberι z ⁻¹' (sectionedPullback f g σ hσ).locus := by
      ext w
      show _ ∈ pullback.fst f g ⁻¹' (U : Set X) ↔ _
      rw [hU]
      exact and_iff_left (hq _ (hfib _ z w))
    have hs : (sectionedPullback f g σ hσ).s z ∈
        ((pullback.fst f g ⁻¹ᵁ U : (pullback f g : Scheme.{u}).Opens) : Set ↥(pullback f g)) := by
      show _ ∈ pullback.fst f g ⁻¹' (U : Set X)
      rw [hU]
      refine ⟨((sectionedPullback f g σ hσ).mem_locus _).mpr
        ⟨z, (sectionedPullback f g σ hσ).sectionPoint _,
          (sectionedPullback f g σ hσ).sectionPoint_mem_fiberComponent _,
          (sectionedPullback f g σ hσ).fiberι_sectionPoint _⟩, hq _ ?_⟩
      rw [← Scheme.Hom.comp_apply,
        show (sectionedPullback f g σ hσ).s ≫ pullback.snd f g = 𝟙 Z from
          pullback.lift_snd _ _ _]
      rfl
    have hrange : Set.range ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.fst f g) ⊆
        Set.range U.ι := by
      rintro x ⟨w, rfl⟩
      rw [U.range_ι]
      exact w.property
    have hlocal : IsPullback
        (IsOpenImmersion.lift U.ι ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.fst f g) hrange)
        (pullback.fst f g ⁻¹ᵁ U).ι U.ι (pullback.fst f g) :=
      IsOpenImmersion.isPullback _ _ U.ι _ (IsOpenImmersion.lift_fac _ _ _).symm
        (by simp only [Scheme.Opens.opensRange_ι])
    exact geometricallyConnected_of_pullback_fiber
      (hlocal.flip.paste_horiz (IsPullback.of_hasPullback f g).flip).flip z
      (sectioned_open_fiber_geometricallyConnected (sectionedPullback f g σ hσ) _ z hO hs)
  let U : X.Opens :=
    ⟨pullback.fst f g '' ((sectionedPullback f g σ hσ).locus ∩ (W : Set ↥(pullback f g))), hUopen⟩
  refine ⟨U, hUcompact, ?_, ?_⟩
  · ext x
    show f.fiberι y x ∈ pullback.fst f g '' _ ↔ True
    refine iff_true_intro ?_
    obtain ⟨z⟩ := hZy
    have hx := hfib f y x
    obtain ⟨e, he₀, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f.fiberι y x) (g.fiberι y z) (hx.trans (hfib g y z).symm)
    refine ⟨e, ⟨mem_sectionedPullback_locus_of_fiber f g σ hσ y hconnected e
      (by simpa [Scheme.Hom.comp_apply, he₀] using hx), ?_⟩, he₀⟩
    show (pullback.fst f g ≫ f) e ∈ (V₀ : Set Y)
    simpa [Scheme.Hom.comp_apply, he₀, hx] using hyV₀
  · rintro y' ⟨v⟩
    have hu : U.ι ((U.ι ≫ f).fiberι y' v) ∈ (U : Set X) := by
      rw [← U.range_ι]
      exact ⟨_, rfl⟩
    obtain ⟨e, heB, hepe⟩ : U.ι ((U.ι ≫ f).fiberι y' v) ∈
        pullback.fst f g '' ((sectionedPullback f g σ hσ).locus ∩ (W : Set ↥(pullback f g))) := hu
    have hgz : g (pullback.snd f g e) = y' := by
      rw [← hcond f g e, hepe]
      simpa using hfib (U.ι ≫ f) y' v
    have h := hgc U hpre _ ((hV₀mem e).1 heB.2)
    rwa [hgz] at h

/-- **Stacks Project, Tag 057I**, granted Tags 055P and 055R, in the shape of
`AlgebraicGeometry.Statement057I`. -/
theorem statement057I (h055P : Statement055P.{u}) (h055R : Statement055R.{u}) :
    Statement057I.{u} := by
  intro X Y Z f g σ hσ y hfp hflat hflf hZy hreduced hconnected
  exact exists_isCompact_opens_geometricallyConnected_fibers h055P h055R f g σ hσ y hfp
    hflat hflf hZy hreduced hconnected

end AlgebraicGeometry.ConnectedComponentSection

end

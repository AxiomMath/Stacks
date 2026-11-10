module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.NormalApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreConnectedness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences
public import StacksFrontier.AlgebraicGeometry.Flatness.SectionLocusTopology
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Sectioned smooth families over a limit come from a stage

Let `S = lim Sᵢ` be a cofiltered limit of Noetherian schemes with affine transition morphisms.
A smooth morphism of finite presentation `f : X ⟶ S` with geometrically connected fibres and a
section `σ` is the base change of a smooth morphism of finite presentation `Xᵢ ⟶ Sᵢ` with
geometrically connected fibres and a section compatible with `σ`, for some stage `i`; and an
integer invertible on `S` is invertible on some stage. These are the second paragraph of the
proof of [Stacks, Tag 0EZJ].

## Main results

* `AlgebraicGeometry.GaloisCoverLimits.exists_sectioned_smooth_model`: the descent of the
  sectioned family, with its geometrically connected fibres.
* `AlgebraicGeometry.GaloisCoverLimits.exists_stage_isUnit_natCast`: the descent of the
  invertibility of an integer.

## Implementation notes

The family and its section descend by Tag 01ZM, and smoothness by Tag 0C0C. Geometric
connectedness of the fibres does not descend as such; following the source, the model `Xᵢ` is
replaced by the open subscheme `Xᵢ⁰` of [Stacks, Section 055K], the union of the connected
components of the fibres containing the section. It is open by Tag 055R (the model is flat of
finite presentation with geometrically reduced fibres), its fibres are geometrically connected
because they are connected and have a rational point, and it contains the image of `X` because
the locus `X⁰` of `X` is all of `X` (its fibres being connected) and is the preimage of `Xᵢ⁰`
(Tag 055M).

## References

* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
* [Stacks Project, Tag 055M](https://stacks.math.columbia.edu/tag/055M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace GaloisCoverLimits

open NormalApproximation

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- Base change of a pullback square along `g` at a source of `π₀` which factors through `π₁`,
with the section `b` over `S₁` lying over `g`. -/
private theorem exists_sectioned_pullback {X S S₀ S₁ Y : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) (π₀ : S ⟶ S₀) (π₁ : S ⟶ S₁) (g : S₁ ⟶ S₀) (hπ : π₁ ≫ g = π₀)
    (f₀ : Y ⟶ S₀) (p : X ⟶ Y) (hpb : IsPullback p f f₀ π₀) (b : S₁ ⟶ Y) (hb : b ≫ f₀ = g)
    (hs : σ ≫ p = π₁ ≫ b) :
    ∃ (σ₁ : S₁ ⟶ pullback f₀ g) (p₁ : X ⟶ pullback f₀ g),
      σ₁ ≫ pullback.snd f₀ g = 𝟙 S₁ ∧ σ₁ ≫ pullback.fst f₀ g = b ∧
      p₁ ≫ pullback.fst f₀ g = p ∧ IsPullback p₁ f (pullback.snd f₀ g) π₁ ∧
      σ ≫ p₁ = π₁ ≫ σ₁ := by
  let σ₁ : S₁ ⟶ pullback f₀ g := pullback.lift b (𝟙 _) (by rw [hb, Category.id_comp])
  let p₁ : X ⟶ pullback f₀ g := pullback.lift p (f ≫ π₁) (by rw [Category.assoc, hπ, ← hpb.w])
  have hσ₁f : σ₁ ≫ pullback.fst f₀ g = b := pullback.lift_fst _ _ _
  have hσ₁s : σ₁ ≫ pullback.snd f₀ g = 𝟙 _ := pullback.lift_snd _ _ _
  have hp₁f : p₁ ≫ pullback.fst f₀ g = p := pullback.lift_fst _ _ _
  have hp₁s : p₁ ≫ pullback.snd f₀ g = f ≫ π₁ := pullback.lift_snd _ _ _
  have hp₁ : IsPullback p₁ f (pullback.snd f₀ g) π₁ := by
    have houter : IsPullback (p₁ ≫ pullback.fst f₀ g) f f₀ (π₁ ≫ g) := by
      rwa [hp₁f, hπ]
    exact houter.of_right hp₁s (IsPullback.of_hasPullback _ _)
  refine ⟨σ₁, p₁, hσ₁s, hσ₁f, hp₁f, hp₁, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, hp₁f, hs, Category.assoc, hσ₁f]
  · rw [Category.assoc, hp₁s, ← Category.assoc, hσ, Category.id_comp, Category.assoc, hσ₁s,
      Category.comp_id]

omit [IsCofiltered I] in
/-- A sectioned model at a stage can be moved to any later stage by base change. -/
theorem sectionedModel_baseChange (D : I ⥤ Scheme.{u}) (c : Cone D)
    {X : Scheme.{u}} (f : X ⟶ c.pt) (σ : c.pt ⟶ X) (hσ : σ ≫ f = 𝟙 c.pt)
    {j k : I} (e : k ⟶ j) {Y : Scheme.{u}} (f₀ : Y ⟶ D.obj j) (σ₀ : D.obj j ⟶ Y)
    (p : X ⟶ Y) (hσ₀ : σ₀ ≫ f₀ = 𝟙 (D.obj j)) (hpb : IsPullback p f f₀ (c.π.app j))
    (hs : σ ≫ p = c.π.app j ≫ σ₀) :
    ∃ (σ₁ : D.obj k ⟶ pullback f₀ (D.map e)) (p₁ : X ⟶ pullback f₀ (D.map e)),
      σ₁ ≫ pullback.snd f₀ (D.map e) = 𝟙 (D.obj k) ∧
      σ₁ ≫ pullback.fst f₀ (D.map e) = D.map e ≫ σ₀ ∧
      p₁ ≫ pullback.fst f₀ (D.map e) = p ∧
      IsPullback p₁ f (pullback.snd f₀ (D.map e)) (c.π.app k) ∧
      σ ≫ p₁ = c.π.app k ≫ σ₁ :=
  exists_sectioned_pullback f σ hσ (c.π.app j) (c.π.app k) (D.map e) (c.w e) f₀ p hpb
    (D.map e ≫ σ₀) (by rw [Category.assoc, hσ₀, Category.comp_id])
    (by rw [hs, ← Category.assoc, c.w e])

/-- A morphism of finite presentation to the limit, with a section, is the base change of a
morphism of finite presentation to a stage with a compatible section (Tag 01ZM). -/
theorem exists_sectioned_model (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) (hf : FinitePresentation f)
    (σ : c.pt ⟶ X) (hσ : σ ≫ f = 𝟙 c.pt) :
    ∃ (j : I) (Y : Scheme.{u}) (f₀ : Y ⟶ D.obj j) (σ₀ : D.obj j ⟶ Y) (p : X ⟶ Y),
      FinitePresentation f₀ ∧ σ₀ ≫ f₀ = 𝟙 (D.obj j) ∧
      IsPullback p f f₀ (c.π.app j) ∧ σ ≫ p = c.π.app j ≫ σ₀ := by
  obtain ⟨i, Y₀, hY₀, ⟨e⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk f) hf
  let e' := (Over.forget c.pt).mapIso e
  let p₀ : X ⟶ Y₀.left := e'.hom ≫ pullback.fst Y₀.hom (c.π.app i)
  have he' : e'.hom ≫ pullback.snd Y₀.hom (c.π.app i) = f := Over.w e.hom
  have hp₀ : p₀ ≫ Y₀.hom = f ≫ c.π.app i := by
    change (e'.hom ≫ pullback.fst Y₀.hom (c.π.app i)) ≫ Y₀.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, he']
  have hPB : IsPullback p₀ f Y₀.hom (c.π.app i) :=
    IsPullback.of_iso_pullback ⟨hp₀⟩ e' rfl he'
  have hY₁ : LocallyOfFinitePresentation Y₀.hom := hY₀.1
  have hY₂ : QuasiCompact Y₀.hom := hY₀.2.1
  have hY₃ : QuasiSeparated Y₀.hom := hY₀.2.2
  obtain ⟨j, g, b, hb, hbν⟩ := exists_factor_from_stage D c hc i Y₀.hom
    (σ ≫ p₀) (by rw [Category.assoc, hp₀, ← Category.assoc, hσ, Category.id_comp])
  obtain ⟨σ₀, p, hσ₀s, -, -, hp, hs⟩ := exists_sectioned_pullback f σ hσ (c.π.app i) (c.π.app j)
    (D.map g) (c.w g) Y₀.hom p₀ hPB b hbν hb.symm
  exact ⟨j, pullback Y₀.hom (D.map g), pullback.snd _ _, σ₀, p,
    ⟨inferInstance, inferInstance, inferInstance⟩, hσ₀s, hp, hs⟩

/-- A morphism locally of finite presentation to a stage which becomes smooth over the limit
is smooth after base change to a later stage (Tag 0C0C). -/
theorem exists_smooth_pullback_stage (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ D.obj i) [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (c.π.app i))] :
    ∃ (j : I) (g : j ⟶ i), Smooth (pullback.snd f (D.map g)) := by
  let X₀ : Over (D.obj i) := Over.mk f
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 _)
  let f₀ : X₀ ⟶ Y₀ := Over.homMk f
  have h₁ : CompactSpace X₀.left := inferInstanceAs (CompactSpace X)
  have h₂ : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace X)
  have h₃ : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i))
  have h₄ : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have h₅ : LocallyOfFinitePresentation f₀.left :=
    inferInstanceAs (LocallyOfFinitePresentation f)
  have heq : ∀ {T : Scheme.{u}} (m : T ⟶ D.obj i),
      ((Over.pullback m).map f₀).left ≫ pullback.snd (𝟙 (D.obj i)) m = pullback.snd f m :=
    fun m ↦ Over.w ((Over.pullback m).map f₀)
  have hfpull : Smooth ((Over.pullback (c.π.app i)).map f₀).left := by
    have h₆ : Smooth (((Over.pullback (c.π.app i)).map f₀).left ≫
        pullback.snd (𝟙 (D.obj i)) (c.π.app i)) := by
      rw [heq]
      infer_instance
    have hRI : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_right_of_respectsIso @Smooth _ _).mp h₆
  obtain ⟨j, g, hg⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c i X₀ Y₀ f₀ hc
  refine ⟨j, g, ?_⟩
  rw [← heq]
  infer_instance

/-- A smooth morphism with a section over the limit of Noetherian schemes is the base change of
a smooth morphism of finite presentation with a compatible section over a stage. -/
theorem exists_smooth_sectioned_model (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsNoetherian (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [Smooth f] (hf : FinitePresentation f)
    (σ : c.pt ⟶ X) (hσ : σ ≫ f = 𝟙 c.pt) :
    ∃ (j : I) (Y : Scheme.{u}) (f₀ : Y ⟶ D.obj j) (σ₀ : D.obj j ⟶ Y) (p : X ⟶ Y),
      FinitePresentation f₀ ∧ Smooth f₀ ∧ σ₀ ≫ f₀ = 𝟙 (D.obj j) ∧
      IsPullback p f f₀ (c.π.app j) ∧ σ ≫ p = c.π.app j ≫ σ₀ := by
  obtain ⟨i, Y₀, f₀, σ₀, p₀, hf₀, hσ₀, hpb, hs⟩ := exists_sectioned_model D c hc f hf σ hσ
  have h₁ : LocallyOfFinitePresentation f₀ := hf₀.1
  have h₂ : QuasiCompact f₀ := hf₀.2.1
  have h₃ : QuasiSeparated f₀ := hf₀.2.2
  have h₄ : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have h₅ : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have h₆ : IsNoetherian Y₀ := ⟨⟩
  have h₇ : Smooth (pullback.snd f₀ (c.π.app i)) := by
    have heq : hpb.isoPullback.inv ≫ f = pullback.snd f₀ (c.π.app i) :=
      hpb.isoPullback.inv_comp_eq.mpr hpb.isoPullback_hom_snd.symm
    rw [← heq]
    infer_instance
  obtain ⟨j, g, hg⟩ := exists_smooth_pullback_stage D c hc i f₀
  obtain ⟨σ₁, p, hσ₁, -, -, hp, hs₁⟩ := sectionedModel_baseChange D c f σ hσ g f₀ σ₀ p₀ hσ₀ hpb hs
  exact ⟨j, pullback f₀ (D.map g), pullback.snd f₀ (D.map g), σ₁, p,
    ⟨inferInstance, inferInstance, inferInstance⟩, hg, hσ₁, hp, hs₁⟩

/-- The restriction of a sectioned morphism to the open union `X⁰` of the connected components
of its fibres containing the section has geometrically connected fibres. -/
theorem geometricallyConnected_locus_ι_comp (D : ConnectedAlongSection.{u})
    (ho : IsOpen D.locus) :
    GeometricallyConnected (Scheme.Opens.ι (⟨D.locus, ho⟩ : D.X.Opens) ≫ D.f) := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro y
  exact ConnectedComponentSection.sectioned_open_fiber_geometricallyConnected D _ y rfl
    (ConnectedAlongSection.section_mem_locus D y)

/-- **The sectioned family descends with geometrically connected fibres.** A smooth morphism of
finite presentation with geometrically connected fibres and a section, over the limit of a
cofiltered system of Noetherian schemes with affine transition morphisms, is the base change of
a smooth morphism of finite presentation with geometrically connected fibres and a compatible
section over a stage. -/
theorem exists_sectioned_smooth_model (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsNoetherian (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [Smooth f] [GeometricallyConnected f]
    (hf : FinitePresentation f) (σ : c.pt ⟶ X) (hσ : σ ≫ f = 𝟙 c.pt) :
    ∃ (j : I) (Y : Scheme.{u}) (f₀ : Y ⟶ D.obj j) (σ₀ : D.obj j ⟶ Y) (p : X ⟶ Y),
      FinitePresentation f₀ ∧ Smooth f₀ ∧ GeometricallyConnected f₀ ∧
      σ₀ ≫ f₀ = 𝟙 (D.obj j) ∧ IsPullback p f f₀ (c.π.app j) ∧ σ ≫ p = c.π.app j ≫ σ₀ := by
  obtain ⟨j, Y, f₀, σ₀, p, hf₀, hsm, hσ₀, hpb, hs⟩ :=
    exists_smooth_sectioned_model D c hc f hf σ hσ
  let A : ConnectedAlongSection := ⟨Y, D.obj j, f₀, σ₀, hσ₀⟩
  let B : ConnectedAlongSection := ⟨X, c.pt, f, σ, hσ⟩
  have hA₁ : Smooth A.f := hsm
  have hA₂ : GeometricallyReduced A.f := geometricallyReduced_of_smooth A.f
  have ho : IsOpen A.locus := ConnectedAlongSection.isOpen_locus A hf₀
  let U : Y.Opens := ⟨A.locus, ho⟩
  have hsp : Set.range σ₀ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ConnectedAlongSection.section_mem_locus A y
  have hp : Set.range p ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hl := ConnectedAlongSection.locus_eq_preimage_of_isPullback A B p (c.π.app j) hpb hs
    have hB : B.locus = Set.univ :=
      (ConnectedAlongSection.locus_eq_univ_iff B).2 fun y ↦
        (f.isConnected_preimage_singleton y).isPreconnected
    have hx : x ∈ B.locus := hB ▸ Set.mem_univ x
    rwa [hl] at hx
  let s₁ := IsOpenImmersion.lift U.ι σ₀ hsp
  let p₁ := IsOpenImmersion.lift U.ι p hp
  have hpb₁ : IsPullback p₁ f (U.ι ≫ f₀) (c.π.app j) := by
    simpa using (IsOpenImmersion.isPullback_lift_id p U.ι hp).paste_vert hpb
  have h₁ : LocallyOfFinitePresentation f₀ := hf₀.1
  have h₂ : QuasiCompact f₀ := hf₀.2.1
  have h₃ : QuasiSeparated f₀ := hf₀.2.2
  have h₄ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f₀
  have h₅ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f₀
  have h₆ : IsNoetherian Y := ⟨⟩
  refine ⟨j, U, U.ι ≫ f₀, s₁, p₁, ⟨inferInstance, inferInstance, inferInstance⟩,
    inferInstance, geometricallyConnected_locus_ι_comp A ho, ?_, hpb₁, ?_⟩
  · simp [s₁, ← Category.assoc, hσ₀]
  · apply (cancel_mono U.ι).mp
    simpa [p₁, s₁, Category.assoc] using hs

/-- **An integer invertible on the limit is invertible on a stage.** If `n` is invertible in
every residue field of the limit of a cofiltered system of quasi-compact and quasi-separated
schemes with affine transition morphisms, then it is invertible in every residue field of some
stage below any given stage. -/
theorem exists_stage_isUnit_natCast (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (n : ℕ) (h : ∀ s : c.pt, IsUnit (n : c.pt.residueField s)) (i : I) :
    ∃ (j : I) (_ : j ⟶ i), ∀ t : D.obj j, IsUnit (n : (D.obj j).residueField t) := by
  let U := (D.obj i).basicOpen (n : Γ(D.obj i, ⊤))
  have hr : Set.range (c.π.app i) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    apply ((D.obj i).evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) (c.π.app i s) trivial
      (n : Γ(D.obj i, ⊤))).mp
    have hs := h s
    rw [← map_natCast ((c.π.app i).residueFieldMap s).hom, isUnit_map_iff] at hs
    simpa using isUnit_iff_ne_zero.mp hs
  let a : c.pt ⟶ U := IsOpenImmersion.lift U.ι (c.π.app i) hr
  have ha : a ≫ U.ι = c.π.app i := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨j, e, b, _, hb⟩ := exists_factor_from_stage D c hc i U.ι a ha
  refine ⟨j, e, fun t ↦ ?_⟩
  have ht : (D.map e) t ∈ U := by
    rw [← hb]
    exact (b t).property
  have hu : IsUnit (n : (D.obj i).residueField (D.map e t)) := by
    apply isUnit_iff_ne_zero.mpr
    simpa using ((D.obj i).evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) (D.map e t) trivial
      (n : Γ(D.obj i, ⊤))).mpr ht
  simpa using hu.map ((D.map e).residueFieldMap t).hom

end GaloisCoverLimits

end AlgebraicGeometry

end

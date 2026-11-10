module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionClosedFibreFieldDescent
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothDescent

/-!
# Uniqueness of contractions over a local ring

Let `A` be a local ring and `W` an object of the big fppf site of the integers whose underlying
scheme is `Spec A`, with closed point `s`. Let `X`, `Y₁`, `Y₂` be families of curves over `W`
and `cᵢ : X ⟶ Yᵢ` morphisms over `W`; suppose the closed fibres `Y₁,ₛ ≅ Y₂,ₛ` are identified
compatibly with `c₁,ₛ`, `c₂,ₛ`, and that `c₁,ₛ` (presented by a morphism of schemes) satisfies
`𝒪 ≅ c₁,ₛ,* 𝒪` and `R¹c₁,ₛ,* 𝒪 = 0`. Then `Y₁ ≅ Y₂` over `W`, compatibly with the `cᵢ` and
with the identification of closed fibres.

This is the case of a local base in the proof of [Stacks, Tag 0E89], reduced, as in the source,
to the Noetherian local case
`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isNoetherianRing_of_siteObject` by writing
`A` as a filtered colimit of Noetherian local rings `A_λ` with local transition maps.

## Main results

* `AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isPullback_noetherianStage`: if the data
  over `W` are base changes of data over a Noetherian local stage `Spec A_λ`, along a morphism
  `W ⟶ Spec A_λ` taking the closed point to the closed point, the statement holds.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The closed point of the spectrum of a local ring of the site, as a morphism of the site of
the integers. -/
abbrev closedPointSiteMap (Λ : Type u) [CommRing Λ] [IsLocalRing Λ]
    (hΛ : B.Contains (Spec (.of Λ))) (hκ : B.Contains (Spec (.of (ResidueField Λ)))) :
    integerSiteObject B hZ hκ ⟶ integerSiteObject B hZ hΛ :=
  integerSiteMap B hZ hκ hΛ (Spec.map (CommRingCat.ofHom (residue Λ)))

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯S" => BigFppfOver.toScheme B S hS

/-- **The fibre of a base change over a point is the base change of the fibre.** If `Z` is the
base change of `Z₀` along `p : W ⟶ W₀` and the point `k : K ⟶ W` lies over `k₀ : K₀ ⟶ W₀`
through `m : K ⟶ K₀`, the fibre of `Z` over `k` is the base change along `m` of the fibre of
`Z₀` over `k₀`. -/
theorem isPullback_pullbackMap_fibre_of_isPullback {W W₀ K K₀ : BigFppfOver B S hS} (p : W ⟶ W₀)
    (k : K ⟶ W) (k₀ : K₀ ⟶ W₀) (m : K ⟶ K₀)
    (hkm : yoneda.map k ≫ yoneda.map p = yoneda.map m ≫ yoneda.map k₀)
    {Z Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {h : Z ⟶ yoneda.obj W} {h₀ : Z₀ ⟶ yoneda.obj W₀}
    {q : Z ⟶ Z₀} (sq : IsPullback q h h₀ (yoneda.map p)) :
    IsPullback (pullback.map h (yoneda.map k) h₀ (yoneda.map k₀) q (yoneda.map m) (yoneda.map p)
        sq.w.symm hkm) (pullback.snd h (yoneda.map k)) (pullback.snd h₀ (yoneda.map k₀))
      (yoneda.map m) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback h₀ (yoneda.map k₀))
  have e : pullback.map h (yoneda.map k) h₀ (yoneda.map k₀) q (yoneda.map m) (yoneda.map p)
      sq.w.symm hkm ≫ pullback.fst h₀ (yoneda.map k₀) = pullback.fst h (yoneda.map k) ≫ q := by
    simp
  rw [e, ← hkm]
  exact (IsPullback.of_hasPullback h (yoneda.map k)).paste_horiz sq

/-- **A morphism of the site presenting a morphism between proper spaces is proper.** If `c`
is a morphism over `K` between algebraic spaces proper over `K`, presented by `a : F_X ⟶ F`, then
`a` lies over `K` and is proper on underlying schemes. -/
theorem isProper_toScheme_map_of_presentations {K : BigFppfOver B S hS}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ yoneda.obj K} {g : Y ⟶ yoneda.obj K}
    (hf : IsProper B S hS f) (hg : IsProper B S hS g) {c : X ⟶ Y} (hc : c ≫ g = f)
    {FX F : BigFppfOver B S hS} (eX : yoneda.obj FX ≅ X) (e : yoneda.obj F ≅ Y) (tX : FX ⟶ K)
    (t : F ⟶ K) (heX : eX.hom ≫ f = yoneda.map tX) (he : e.hom ≫ g = yoneda.map t) (a : FX ⟶ F)
    (ha : yoneda.map a ≫ e.hom = eX.hom ≫ c) :
    a ≫ t = tX ∧ _root_.AlgebraicGeometry.IsProper ((𝒯S).map a) := by
  have hat : a ≫ t = tX := yoneda.map_injective (by
    rw [Functor.map_comp, ← he, reassoc_of% ha, hc, heX])
  have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map t) :=
    isProper_toScheme_map_of_iso B S hS e g t he hg
  have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map tX) :=
    isProper_toScheme_map_of_iso B S hS eX f tX heX hf
  have : _root_.AlgebraicGeometry.IsProper ((𝒯S).map a ≫ (𝒯S).map t) := by
    rw [← Functor.map_comp, hat]
    infer_instance
  exact ⟨hat, _root_.AlgebraicGeometry.IsProper.of_comp _ ((𝒯S).map t)⟩

/-- **The base change of an isomorphism along a cartesian square.** An isomorphism `ψ₀` over the
target of a morphism `P` of presheaves, between two presheaves with base changes `Y₁`, `Y₂`
along `P`, induces an isomorphism `ψ : Y₁ ≅ Y₂` over the source compatible with `ψ₀`. -/
theorem exists_iso_of_isPullback_of_iso {T T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : T ⟶ T₀)
    {Y₁ Y₂ Y₁₀ Y₂₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g₁ : Y₁ ⟶ T} {g₂ : Y₂ ⟶ T}
    {g₁₀ : Y₁₀ ⟶ T₀} {g₂₀ : Y₂₀ ⟶ T₀} {q₁ : Y₁ ⟶ Y₁₀} {q₂ : Y₂ ⟶ Y₂₀}
    (sq₁ : IsPullback q₁ g₁ g₁₀ P) (sq₂ : IsPullback q₂ g₂ g₂₀ P) (ψ₀ : Y₁₀ ≅ Y₂₀)
    (hψ₀ : ψ₀.hom ≫ g₂₀ = g₁₀) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ ψ.hom ≫ q₂ = q₁ ≫ ψ₀.hom := by
  have hw₁ : (q₁ ≫ ψ₀.hom) ≫ g₂₀ = g₁ ≫ P := by rw [Category.assoc, hψ₀, sq₁.w]
  have hw₂ : (q₂ ≫ ψ₀.inv) ≫ g₁₀ = g₂ ≫ P := by
    rw [Category.assoc, ← hψ₀, Iso.inv_hom_id_assoc, sq₂.w]
  refine ⟨⟨sq₂.lift (q₁ ≫ ψ₀.hom) g₁ hw₁, sq₁.lift (q₂ ≫ ψ₀.inv) g₂ hw₂, ?_, ?_⟩,
    sq₂.lift_snd _ _ _, sq₂.lift_fst _ _ _⟩
  · apply sq₁.hom_ext <;> simp
  · apply sq₂.hom_ext <;> simp

/-- **Flatness, properness and finite presentation pass to base changes.** -/
theorem isFlat_isProper_isFinitePresentation_of_isPullback
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T T' : BigFppfOver B S hS} {f : X ⟶ yoneda.obj T}
    {f' : X' ⟶ yoneda.obj T'} {q : X' ⟶ X} {m : T' ⟶ T} (sq : IsPullback q f' f (yoneda.map m))
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hfl : IsFlat B S hS f) (hpr : IsProper B S hS f) (hfp : IsFinitePresentation B S hS f) :
    IsFlat B S hS f' ∧ IsProper B S hS f' ∧ IsFinitePresentation B S hS f' := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hT' := isAlgebraicSpace_yoneda B S hS T'
  exact ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_homMk B S hS hX hT' hT hX' sq) hfl,
    isProper_of_isPullback' hX' hX hT' hT sq hpr,
    isFinitePresentation_of_isPullback B S hS hX' hX hT' hT sq hfp⟩

/-- **A bound on the relative dimension descends along a surjective base change**: if the base
change `f'` of `f` along a surjective `m` has relative dimension at most one, so has `f`, every
point of the source of `f` being the image of a point of the source of `f'`. -/
theorem hasRelativeDimensionLE_of_isPullback_of_isSurjective
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T T' : BigFppfOver B S hS} {f : X ⟶ yoneda.obj T}
    {f' : X' ⟶ yoneda.obj T'} {q : X' ⟶ X} {m : T' ⟶ T} (sq : IsPullback q f' f (yoneda.map m))
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hf : IsLocallyOfFiniteType B S hS f) (hm : IsSurjective B S hS (yoneda.map m))
    (hd' : HasRelativeDimensionLE 1 B S hS f') : HasRelativeDimensionLE 1 B S hS f := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hT' := isAlgebraicSpace_yoneda B S hS T'
  have hq : IsSurjective B S hS q := isSurjective_of_isPullback_presheaf hX' hT' hX hT sq.flip hm
  intro x
  obtain ⟨x', rfl⟩ := hq x
  obtain ⟨e, he, h⟩ := hd' x'
  exact ⟨e, he, (hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX hT' hT hf x' e).2 h⟩

end General

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The closed-fibre data of [Stacks, Tag 0E89] descend along a field extension.** Let `X₀`,
`Y₁₀`, `Y₂₀` be families of curves over the spectrum of a field `κ₀` (with `Y₂₀` only proper) and
`cᵢ₀ : X₀ ⟶ Yᵢ₀` morphisms over `Spec κ₀`, and let `X`, `Y₁`, `Y₂`, `cᵢ` be their base changes
along an fpqc covering `m : K ⟶ Spec κ₀` which is flat and surjective on underlying schemes.
If `X` and `Y₁` are presented by schemes on which `c₁` satisfies `𝒪 ≅ c₁,* 𝒪` and
`R¹c₁,* 𝒪 = 0`, and `φ : Y₁ ≅ Y₂` is compatible with the `cᵢ`, then `X₀` and `Y₁₀` are presented
by schemes of dimension at most one on which `c₁₀` satisfies the same, and `φ` descends to an
isomorphism `Y₁₀ ≅ Y₂₀` compatible with the `cᵢ₀`. -/
theorem exists_closedFibreData_of_isPullback_field {κ₀ : Type u} [Field κ₀]
    (hκ₀ : B.Contains (Spec (.of κ₀))) {K : BigFppfOver B integerBase hZ}
    (m : K ⟶ integerSiteObject B hZ hκ₀)
    (hm : IsFpqcCovering B integerBase hZ (fun _ : Unit => yoneda.map m))
    [Flat ((𝒯).map m)] [Surjective ((𝒯).map m)]
    {X₀ Y₁₀ Y₂₀ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX₀ : IsAlgebraicSpace B integerBase hZ X₀) (hY₁₀ : IsAlgebraicSpace B integerBase hZ Y₁₀)
    (hY₂₀ : IsAlgebraicSpace B integerBase hZ Y₂₀)
    (f₀ : X₀ ⟶ yoneda.obj (integerSiteObject B hZ hκ₀))
    (g₁₀ : Y₁₀ ⟶ yoneda.obj (integerSiteObject B hZ hκ₀))
    (g₂₀ : Y₂₀ ⟶ yoneda.obj (integerSiteObject B hZ hκ₀))
    (hfl₀ : IsFlat B integerBase hZ f₀) (hpr₀ : IsProper B integerBase hZ f₀)
    (hfp₀ : IsFinitePresentation B integerBase hZ f₀)
    (hfl₁₀ : IsFlat B integerBase hZ g₁₀) (hpr₁₀ : IsProper B integerBase hZ g₁₀)
    (hfp₁₀ : IsFinitePresentation B integerBase hZ g₁₀) (hpr₂₀ : IsProper B integerBase hZ g₂₀)
    (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀) (hc₁₀ : c₁₀ ≫ g₁₀ = f₀) (hc₂₀ : c₂₀ ≫ g₂₀ = f₀)
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY₁ : IsAlgebraicSpace B integerBase hZ Y₁)
    (hY₂ : IsAlgebraicSpace B integerBase hZ Y₂)
    (f : X ⟶ yoneda.obj K) (g₁ : Y₁ ⟶ yoneda.obj K) (g₂ : Y₂ ⟶ yoneda.obj K)
    (qX : X ⟶ X₀) (q₁ : Y₁ ⟶ Y₁₀) (q₂ : Y₂ ⟶ Y₂₀) (sqX : IsPullback qX f f₀ (yoneda.map m))
    (sq₁ : IsPullback q₁ g₁ g₁₀ (yoneda.map m)) (sq₂ : IsPullback q₂ g₂ g₂₀ (yoneda.map m))
    (hdX : HasRelativeDimensionLE 1 B integerBase hZ f)
    (hd₁ : HasRelativeDimensionLE 1 B integerBase hZ g₁)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = f)
    (hcq₁ : c₁ ≫ q₁ = qX ≫ c₁₀) (hcq₂ : c₂ ≫ q₂ = qX ≫ c₂₀)
    {FX F₁ : BigFppfOver B integerBase hZ} (eX : yoneda.obj FX ≅ X) (e₁ : yoneda.obj F₁ ≅ Y₁)
    (tX : FX ⟶ K) (t₁ : F₁ ⟶ K) (heX : eX.hom ≫ f = yoneda.map tX)
    (he₁ : e₁.hom ≫ g₁ = yoneda.map t₁) (a₁ : FX ⟶ F₁) (ha₁ : yoneda.map a₁ ≫ e₁.hom = eX.hom ≫ c₁)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁)))
    (φ : Y₁ ≅ Y₂) (hφg : φ.hom ≫ g₂ = g₁) (hφc : c₁ ≫ φ.hom = c₂) :
    ∃ (FX₀ F₁₀ : BigFppfOver B integerBase hZ) (tX₀ : FX₀ ⟶ integerSiteObject B hZ hκ₀)
      (t₁₀ : F₁₀ ⟶ integerSiteObject B hZ hκ₀) (eX₀ : yoneda.obj FX₀ ≅ X₀)
      (e₁₀ : yoneda.obj F₁₀ ≅ Y₁₀) (a₁₀ : FX₀ ⟶ F₁₀),
      eX₀.hom ≫ f₀ = yoneda.map tX₀ ∧ e₁₀.hom ≫ g₁₀ = yoneda.map t₁₀ ∧
      topologicalKrullDim ((𝒯).obj FX₀) ≤ 1 ∧ topologicalKrullDim ((𝒯).obj F₁₀) ≤ 1 ∧
      yoneda.map a₁₀ ≫ e₁₀.hom = eX₀.hom ≫ c₁₀ ∧ a₁₀ ≫ t₁₀ = tX₀ ∧
      (∀ y, topologicalKrullDim (((𝒯).map a₁₀).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁₀)) ∧
      IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁₀)) ∧
      ∃ φ₀ : Y₁₀ ≅ Y₂₀, φ₀.hom ≫ g₂₀ = g₁₀ ∧ c₁₀ ≫ φ₀.hom = c₂₀ ∧
        q₁ ≫ φ₀.hom = φ.hom ≫ q₂ := by
  have hK := isAlgebraicSpace_yoneda B integerBase hZ K
  have hK₀ := isAlgebraicSpace_yoneda B integerBase hZ (integerSiteObject B hZ hκ₀)
  have hprX : IsProper B integerBase hZ f := isProper_of_isPullback' hX hX₀ hK hK₀ sqX hpr₀
  have hpr₁ : IsProper B integerBase hZ g₁ := isProper_of_isPullback' hY₁ hY₁₀ hK hK₀ sq₁ hpr₁₀
  have hsurj : IsSurjective B integerBase hZ (yoneda.map m) :=
    isSurjective_yoneda_map B integerBase hZ m inferInstance
  have hd₀ := hasRelativeDimensionLE_of_isPullback_of_isSurjective B integerBase hZ sqX hX₀ hX
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ hfp₀.1) hsurj hdX
  have hd₁₀ := hasRelativeDimensionLE_of_isPullback_of_isSurjective B integerBase hZ sq₁ hY₁₀ hY₁
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ hfp₁₀.1) hsurj hd₁
  -- presentations over `Spec κ₀`
  obtain ⟨FX₀, tX₀, eX₀, heX₀, hdX₀⟩ :=
    exists_presentation_of_curveFamilyConditions_of_field hκ₀ hX₀ f₀ hfl₀ hpr₀ hfp₀ hd₀
  obtain ⟨F₁₀, t₁₀, e₁₀, he₁₀, hd₁₀'⟩ :=
    exists_presentation_of_curveFamilyConditions_of_field hκ₀ hY₁₀ g₁₀ hfl₁₀ hpr₁₀ hfp₁₀ hd₁₀
  let a₁₀ := Yoneda.fullyFaithful.preimage (eX₀.hom ≫ c₁₀ ≫ e₁₀.inv)
  have ha₁₀ : yoneda.map a₁₀ ≫ e₁₀.hom = eX₀.hom ≫ c₁₀ := by simp [a₁₀]
  obtain ⟨hat₁₀, hpa₁₀⟩ := isProper_toScheme_map_of_presentations B integerBase hZ hpr₀ hpr₁₀
    hc₁₀ eX₀ e₁₀ tX₀ t₁₀ heX₀ he₁₀ a₁₀ ha₁₀
  obtain ⟨-, hpa₁⟩ := isProper_toScheme_map_of_presentations B integerBase hZ hprX hpr₁ hc₁ eX e₁
    tX t₁ heX he₁ a₁ ha₁
  have hdim₀ := topologicalKrullDim_fiber_le_one_of_le_one ((𝒯).map a₁₀) hdX₀
  obtain ⟨hR₀, h0₀⟩ := isZero_and_isIso_of_presentations_of_isPullback B integerBase hZ m sqX sq₁
    hc₁₀ hc₁ hcq₁ eX₀ e₁₀ eX e₁ t₁₀ t₁ he₁₀ he₁ a₁₀ a₁ ha₁₀ ha₁ hdim₀ h0 hR
  -- the identification of fibres
  have hqc : IsQuasiCompact B integerBase hZ c₁ :=
    (isProper_of_comp_of_isSeparated B integerBase hZ hX hY₁ hK c₁ g₁ (by rwa [hc₁])
      hpr₁.1).2.1.2
  have hdom := schemeTheoreticImageSubfunctor_eq_top_of_presentation B integerBase hZ hY₁ eX e₁
    a₁ c₁ ha₁ h0
  obtain ⟨φ₀, hφ₀g, hφ₀q, hφ₀c⟩ := exists_iso_desc_of_isFpqcCovering_of_isPullback B integerBase
    hZ m hm hX₀ hY₁₀ hY₂₀ hX hY₁ hY₂ hpr₁₀.1 hpr₂₀.1 sqX sq₁ sq₂ hc₁₀ hc₂₀ hcq₁ hc₁ hqc hdom φ
    hφg (by rw [reassoc_of% hφc, hcq₂])
  exact ⟨FX₀, F₁₀, tX₀, t₁₀, eX₀, e₁₀, a₁₀, heX₀, he₁₀, hdX₀, hd₁₀', ha₁₀, hat₁₀, hdim₀, h0₀,
    hR₀, φ₀, hφ₀g, hφ₀c, hφ₀q⟩

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The Noetherian local case of [Stacks, Tag 0E89], with the closed fibres as fibre
products.** This is
`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isNoetherianRing_of_siteObject` over
`Spec Λ₀` itself, with the closed point `Spec κ(Λ₀) ⟶ Spec Λ₀`, the closed fibres of `X₀`, `Y₁₀`,
`Y₂₀` taken to be the fibre products, those of `X₀` and `Y₁₀` presented by schemes, and the
identification `φ₀` of the closed fibres of `Y₁₀` and `Y₂₀` an isomorphism of fibre products. -/
theorem exists_iso_of_closedFibre_of_isNoetherianRing_of_pullback (Λ₀ : Type u) [CommRing Λ₀]
    [IsLocalRing Λ₀] [IsNoetherianRing Λ₀] (hΛ₀ : B.Contains (Spec (.of Λ₀)))
    (hκ₀ : B.Contains (Spec (.of (ResidueField Λ₀))))
    {X₀ Y₁₀ Y₂₀ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX₀ : IsAlgebraicSpace B integerBase hZ X₀) (hY₁₀ : IsAlgebraicSpace B integerBase hZ Y₁₀)
    (hY₂₀ : IsAlgebraicSpace B integerBase hZ Y₂₀)
    (f₀ : X₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (g₁₀ : Y₁₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (g₂₀ : Y₂₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (hfl₀ : IsFlat B integerBase hZ f₀) (hpr₀ : IsProper B integerBase hZ f₀)
    (hfl₁₀ : IsFlat B integerBase hZ g₁₀) (hpr₁₀ : IsProper B integerBase hZ g₁₀)
    (hfl₂₀ : IsFlat B integerBase hZ g₂₀) (hpr₂₀ : IsProper B integerBase hZ g₂₀)
    (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀) (hc₁₀ : c₁₀ ≫ g₁₀ = f₀) (hc₂₀ : c₂₀ ≫ g₂₀ = f₀)
    {FX₀ F₁₀ : BigFppfOver B integerBase hZ} (tX₀ : FX₀ ⟶ integerSiteObject B hZ hκ₀)
    (t₁₀ : F₁₀ ⟶ integerSiteObject B hZ hκ₀)
    (eX₀ : yoneda.obj FX₀ ≅ pullback f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)))
    (e₁₀ : yoneda.obj F₁₀ ≅ pullback g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)))
    (heX₀ : eX₀.hom ≫ pullback.snd f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) = yoneda.map tX₀)
    (he₁₀ : e₁₀.hom ≫ pullback.snd g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) =
      yoneda.map t₁₀)
    (hdX₀ : topologicalKrullDim ((𝒯).obj FX₀) ≤ 1) (hd₁₀ : topologicalKrullDim ((𝒯).obj F₁₀) ≤ 1)
    (a₁₀ : FX₀ ⟶ F₁₀)
    (ha₁₀ : yoneda.map a₁₀ ≫ e₁₀.hom = eX₀.hom ≫
      pullback.map f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) g₁₀
        (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) c₁₀ (𝟙 _) (𝟙 _) (by simp [hc₁₀]) (by simp))
    (hat₁₀ : a₁₀ ≫ t₁₀ = tX₀)
    (hdim₀ : ∀ y, topologicalKrullDim (((𝒯).map a₁₀).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0₀ : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁₀)))
    (hR₀ : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁₀)))
    (φ₀ : pullback g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) ≅
      pullback g₂₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)))
    (hφ₀g : φ₀.hom ≫ pullback.snd g₂₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) =
      pullback.snd g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)))
    (hφ₀c : pullback.map f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) g₁₀
        (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) c₁₀ (𝟙 _) (𝟙 _) (by simp [hc₁₀]) (by simp) ≫
          φ₀.hom =
      pullback.map f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) g₂₀
        (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) c₂₀ (𝟙 _) (𝟙 _) (by simp [hc₂₀]) (by simp)) :
    ∃ ψ₀ : Y₁₀ ≅ Y₂₀, ψ₀.hom ≫ g₂₀ = g₁₀ ∧ c₁₀ ≫ ψ₀.hom = c₂₀ ∧
      pullback.fst g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) ≫ ψ₀.hom =
        φ₀.hom ≫ pullback.fst g₂₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) := by
  have hι : (Iso.refl (Spec (.of (ResidueField Λ₀)))).hom ≫
      (𝒯).map (closedPointSiteMap Λ₀ hΛ₀ hκ₀) ≫ (Iso.refl (Spec (.of Λ₀))).hom =
        ContractionUniquenessComplete.closedPoint Λ₀ := by
    simp only [Iso.refl_hom, Category.id_comp]
    rfl
  have hi : ∀ {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {F : BigFppfOver B integerBase hZ}
      (g : Y ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
      (t : F ⟶ integerSiteObject B hZ hκ₀)
      (e : yoneda.obj F ≅ pullback g (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀))),
      e.hom ≫ pullback.snd g _ = yoneda.map t →
        IsPullback (e.hom ≫ pullback.fst g _) (yoneda.map t) g
          (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) := fun g t e he =>
    IsPullback.of_iso (IsPullback.of_hasPullback g _) e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp [← he]) (by simp) (by simp)
  have hiX₀ := hi f₀ tX₀ eX₀ heX₀
  have hi₁₀ := hi g₁₀ t₁₀ e₁₀ he₁₀
  have hi₂₀ := hi g₂₀ t₁₀ (e₁₀ ≪≫ φ₀) (by simp [he₁₀, hφ₀g])
  have hia₁ : (eX₀.hom ≫ pullback.fst f₀ _) ≫ c₁₀ =
      yoneda.map a₁₀ ≫ e₁₀.hom ≫ pullback.fst g₁₀ _ := by
    rw [reassoc_of% ha₁₀]
    simp
  have hia₂ : (eX₀.hom ≫ pullback.fst f₀ _) ≫ c₂₀ =
      yoneda.map a₁₀ ≫ e₁₀.hom ≫ φ₀.hom ≫ pullback.fst g₂₀ _ := by
    rw [reassoc_of% ha₁₀, reassoc_of% hφ₀c]
    simp
  obtain ⟨ψ₀, hψ₀g, hψ₀c, hψ₀f⟩ := exists_iso_of_closedFibre_of_isNoetherianRing_of_siteObject B
    integerBase hZ Λ₀ (integerSiteObject B hZ hΛ₀) (Iso.refl (Spec (.of Λ₀))) hX₀ hY₁₀ hY₂₀ f₀
    g₁₀ g₂₀ hpr₀ hpr₁₀ hpr₂₀ hfl₀ hfl₁₀ hfl₂₀ c₁₀ c₂₀ hc₁₀ hc₂₀ (closedPointSiteMap Λ₀ hΛ₀ hκ₀)
    (Iso.refl (Spec (.of (ResidueField Λ₀)))) hι tX₀ t₁₀ t₁₀ _ _ _ hiX₀ hi₁₀ hi₂₀ hdX₀ hd₁₀ hd₁₀
    a₁₀ a₁₀ hat₁₀ hat₁₀ hia₁ hia₂ (Iso.refl _) (by simp) (by simp) hdim₀ h0₀ hR₀
  refine ⟨ψ₀, hψ₀g, hψ₀c, ?_⟩
  simp only [Category.assoc, Iso.trans_hom, Iso.refl_hom] at hψ₀f
  exact (Iso.cancel_iso_hom_left e₁₀ _ _).1 hψ₀f

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The closed-fibre data of [Stacks, Tag 0E89] pass from a point of a base change to the
closed point of a Noetherian local stage.** In the situation of
`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isPullback_noetherianStage`, the fibres over
the closed point of `Spec Λ₀` of `X₀` and `Y₁₀` are presented by schemes of dimension at most one
on which the fibre of `c₁₀` satisfies `𝒪 ≅ c₁₀,* 𝒪` and `R¹c₁₀,* 𝒪 = 0`, and `φ` descends to an
identification of the fibres of `Y₁₀` and `Y₂₀` over the closed point. -/
theorem exists_closedFibreData_of_isPullback_noetherianStage (Λ₀ : Type u) [CommRing Λ₀]
    [IsLocalRing Λ₀] [IsNoetherianRing Λ₀] (hΛ₀ : B.Contains (Spec (.of Λ₀)))
    (hκ₀ : B.Contains (Spec (.of (ResidueField Λ₀))))
    {X₀ Y₁₀ Y₂₀ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX₀ : IsAlgebraicSpace B integerBase hZ X₀) (hY₁₀ : IsAlgebraicSpace B integerBase hZ Y₁₀)
    (hY₂₀ : IsAlgebraicSpace B integerBase hZ Y₂₀)
    (f₀ : X₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (g₁₀ : Y₁₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (g₂₀ : Y₂₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (hfl₀ : IsFlat B integerBase hZ f₀) (hpr₀ : IsProper B integerBase hZ f₀)
    (hfp₀ : IsFinitePresentation B integerBase hZ f₀)
    (hfl₁₀ : IsFlat B integerBase hZ g₁₀) (hpr₁₀ : IsProper B integerBase hZ g₁₀)
    (hfp₁₀ : IsFinitePresentation B integerBase hZ g₁₀) (hpr₂₀ : IsProper B integerBase hZ g₂₀)
    (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀) (hc₁₀ : c₁₀ ≫ g₁₀ = f₀) (hc₂₀ : c₂₀ ≫ g₂₀ = f₀)
    {W : BigFppfOver B integerBase hZ} (p : W ⟶ integerSiteObject B hZ hΛ₀)
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY₁ : IsAlgebraicSpace B integerBase hZ Y₁)
    (hY₂ : IsAlgebraicSpace B integerBase hZ Y₂)
    (fX : X ⟶ yoneda.obj W) (g₁ : Y₁ ⟶ yoneda.obj W) (g₂ : Y₂ ⟶ yoneda.obj W)
    (qX : X ⟶ X₀) (q₁ : Y₁ ⟶ Y₁₀) (q₂ : Y₂ ⟶ Y₂₀) (sqX : IsPullback qX fX f₀ (yoneda.map p))
    (sq₁ : IsPullback q₁ g₁ g₁₀ (yoneda.map p)) (sq₂ : IsPullback q₂ g₂ g₂₀ (yoneda.map p))
    (hdX : HasRelativeDimensionLE 1 B integerBase hZ fX)
    (hd₁ : HasRelativeDimensionLE 1 B integerBase hZ g₁)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX)
    (hcq₁ : c₁ ≫ q₁ = qX ≫ c₁₀) (hcq₂ : c₂ ≫ q₂ = qX ≫ c₂₀)
    {K : BigFppfOver B integerBase hZ} (k : K ⟶ W) (m : K ⟶ integerSiteObject B hZ hκ₀)
    (hkm : yoneda.map k ≫ yoneda.map p = yoneda.map m ≫ yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀))
    (hm : IsFpqcCovering B integerBase hZ (fun _ : Unit => yoneda.map m))
    [Flat ((𝒯).map m)] [Surjective ((𝒯).map m)]
    {FX F₁ : BigFppfOver B integerBase hZ} (eX : yoneda.obj FX ≅ pullback fX (yoneda.map k))
    (e₁ : yoneda.obj F₁ ≅ pullback g₁ (yoneda.map k)) (tX : FX ⟶ K) (t₁ : F₁ ⟶ K)
    (heX : eX.hom ≫ pullback.snd fX (yoneda.map k) = yoneda.map tX)
    (he₁ : e₁.hom ≫ pullback.snd g₁ (yoneda.map k) = yoneda.map t₁) (a₁ : FX ⟶ F₁)
    (ha₁ : yoneda.map a₁ ≫ e₁.hom =
      eX.hom ≫ pullback.map fX (yoneda.map k) g₁ (yoneda.map k) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
        (by simp))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁)))
    (φ : pullback g₁ (yoneda.map k) ≅ pullback g₂ (yoneda.map k))
    (hφ : φ.hom ≫ pullback.snd g₂ (yoneda.map k) = pullback.snd g₁ (yoneda.map k))
    (hφc : pullback.map fX (yoneda.map k) g₁ (yoneda.map k) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
        (by simp) ≫ φ.hom =
      pullback.map fX (yoneda.map k) g₂ (yoneda.map k) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂])
        (by simp)) :
    ∃ (FX₀ F₁₀ : BigFppfOver B integerBase hZ) (tX₀ : FX₀ ⟶ integerSiteObject B hZ hκ₀)
      (t₁₀ : F₁₀ ⟶ integerSiteObject B hZ hκ₀)
      (eX₀ : yoneda.obj FX₀ ≅ pullback f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)))
      (e₁₀ : yoneda.obj F₁₀ ≅ pullback g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)))
      (a₁₀ : FX₀ ⟶ F₁₀),
      eX₀.hom ≫ pullback.snd f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) = yoneda.map tX₀ ∧
      e₁₀.hom ≫ pullback.snd g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) = yoneda.map t₁₀ ∧
      topologicalKrullDim ((𝒯).obj FX₀) ≤ 1 ∧ topologicalKrullDim ((𝒯).obj F₁₀) ≤ 1 ∧
      yoneda.map a₁₀ ≫ e₁₀.hom = eX₀.hom ≫
        pullback.map f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) g₁₀
          (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) c₁₀ (𝟙 _) (𝟙 _) (by simp [hc₁₀])
          (by simp) ∧ a₁₀ ≫ t₁₀ = tX₀ ∧
      (∀ y, topologicalKrullDim (((𝒯).map a₁₀).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁₀)) ∧
      IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁₀)) ∧
      ∃ φ₀ : pullback g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) ≅
          pullback g₂₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)),
        φ₀.hom ≫ pullback.snd g₂₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) =
          pullback.snd g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) ∧
        pullback.map f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) g₁₀
            (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) c₁₀ (𝟙 _) (𝟙 _) (by simp [hc₁₀])
            (by simp) ≫ φ₀.hom =
          pullback.map f₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) g₂₀
            (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) c₂₀ (𝟙 _) (𝟙 _) (by simp [hc₂₀])
            (by simp) ∧
        pullback.map g₁ (yoneda.map k) g₁₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀)) q₁
            (yoneda.map m) (yoneda.map p) sq₁.w.symm hkm ≫
            φ₀.hom =
          φ.hom ≫ pullback.map g₂ (yoneda.map k) g₂₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀))
            q₂ (yoneda.map m) (yoneda.map p) sq₂.w.symm hkm := by
  have hAS : ∀ {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
      {T T' : BigFppfOver B integerBase hZ}
      (g : Y ⟶ yoneda.obj T) (t : T' ⟶ T), IsAlgebraicSpace B integerBase hZ Y →
        IsAlgebraicSpace B integerBase hZ (pullback g (yoneda.map t)) := fun g t hY =>
    isAlgebraicSpace_pullback B integerBase hZ g _ hY (isAlgebraicSpace_yoneda B integerBase hZ _)
      (isAlgebraicSpace_yoneda B integerBase hZ _)
  obtain ⟨hflX₀s, hprX₀s, hfpX₀s⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B
    integerBase hZ (IsPullback.of_hasPullback f₀ _) hX₀
    (hAS f₀ (closedPointSiteMap Λ₀ hΛ₀ hκ₀) hX₀) hfl₀ hpr₀ hfp₀
  obtain ⟨hfl₁₀s, hpr₁₀s, hfp₁₀s⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B
    integerBase hZ (IsPullback.of_hasPullback g₁₀ _) hY₁₀
    (hAS g₁₀ (closedPointSiteMap Λ₀ hΛ₀ hκ₀) hY₁₀) hfl₁₀ hpr₁₀ hfp₁₀
  obtain ⟨hflX, hprX, hfpX⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B integerBase hZ
    sqX hX₀ hX hfl₀ hpr₀ hfp₀
  obtain ⟨hfl₁, hpr₁, hfp₁⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B integerBase hZ
    sq₁ hY₁₀ hY₁ hfl₁₀ hpr₁₀ hfp₁₀
  obtain ⟨-, -, -, hdXs⟩ := curveFamilyConditions_of_isPullback B integerBase hZ
    (IsPullback.of_hasPullback fX (yoneda.map k)) hX (hAS fX k hX) hflX hprX hfpX hdX
  obtain ⟨-, -, -, hd₁s⟩ := curveFamilyConditions_of_isPullback B integerBase hZ
    (IsPullback.of_hasPullback g₁ (yoneda.map k)) hY₁ (hAS g₁ k hY₁) hfl₁ hpr₁ hfp₁ hd₁
  have hpr₂₀s : IsProper B integerBase hZ
      (pullback.snd g₂₀ (yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀))) :=
    isProper_of_isPullback' (hAS g₂₀ (closedPointSiteMap Λ₀ hΛ₀ hκ₀) hY₂₀) hY₂₀
      (isAlgebraicSpace_yoneda B integerBase hZ _)
      (isAlgebraicSpace_yoneda B integerBase hZ _) (IsPullback.of_hasPullback g₂₀ _) hpr₂₀
  have hcq : ∀ {Y Y₀ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj W}
      {g₀ : Y₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀)} {q : Y ⟶ Y₀}
      (sq : IsPullback q g g₀ (yoneda.map p)) (c : X ⟶ Y) (c₀ : X₀ ⟶ Y₀) (hc : c ≫ g = fX)
      (hc₀ : c₀ ≫ g₀ = f₀) (_ : c ≫ q = qX ≫ c₀),
      pullback.map fX (yoneda.map k) g (yoneda.map k) c (𝟙 _) (𝟙 _) (by simp [hc]) (by simp) ≫
        pullback.map g (yoneda.map k) g₀ _ q (yoneda.map m) (yoneda.map p) sq.w.symm hkm =
      pullback.map fX (yoneda.map k) f₀ _ qX (yoneda.map m) (yoneda.map p) sqX.w.symm hkm ≫
        pullback.map f₀ _ g₀ _ c₀ (𝟙 _) (𝟙 _) (by simp [hc₀]) (by simp) := by
    intro Y Y₀ g g₀ q sq c c₀ hc hc₀ hcq
    exact pullback.hom_ext (by simp [hcq]) (by simp)
  exact exists_closedFibreData_of_isPullback_field hκ₀ m hm
      (hAS f₀ _ hX₀) (hAS g₁₀ _ hY₁₀) (hAS g₂₀ _ hY₂₀)
      _ _ _ hflX₀s hprX₀s hfpX₀s hfl₁₀s hpr₁₀s hfp₁₀s hpr₂₀s _ _ (by simp) (by simp)
      (hAS fX _ hX) (hAS g₁ _ hY₁) (hAS g₂ _ hY₂) _ _ _ _ _ _
      (isPullback_pullbackMap_fibre_of_isPullback B integerBase hZ p k _ m hkm sqX)
      (isPullback_pullbackMap_fibre_of_isPullback B integerBase hZ p k _ m hkm sq₁)
      (isPullback_pullbackMap_fibre_of_isPullback B integerBase hZ p k _ m hkm sq₂)
      hdXs hd₁s _ _ (by simp) (hcq sq₁ c₁ c₁₀ hc₁ hc₁₀ hcq₁)
      (hcq sq₂ c₂ c₂₀ hc₂ hc₂₀ hcq₂) eX e₁ tX t₁ heX he₁ a₁ ha₁ h0 hR φ hφ hφc

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E89] for base changes of families over a Noetherian local stage.** Let
`Λ₀` be a Noetherian local ring, `X₀`, `Y₁₀`, `Y₂₀` families of curves over `Spec Λ₀` and
`cᵢ₀ : X₀ ⟶ Yᵢ₀` morphisms over `Spec Λ₀`. Let `p : W ⟶ Spec Λ₀` be a morphism of the site and
`X`, `Y₁`, `Y₂`, `cᵢ` the base changes along `p`. Let `k : K ⟶ W` be a point lying over the closed
point of `Spec Λ₀` through `m : K ⟶ Spec κ(Λ₀)`, with `m` an fpqc covering which is flat and
surjective on underlying schemes. If the fibres of `X` and `Y₁` over `k` are presented by schemes
on which the fibre of `c₁` satisfies `𝒪 ≅ c₁,* 𝒪` and `R¹c₁,* 𝒪 = 0`, and `φ` identifies the
fibres of `Y₁` and `Y₂` over `k` compatibly with the `cᵢ`, then `Y₁ ≅ Y₂` over `W`, compatibly
with the `cᵢ` and with `φ`.

The hypotheses on the fibres over `k` are inherited by the fibres over the closed point of
`Spec Λ₀` (`AlgebraicGeometry.Space.isZero_and_isIso_of_presentations_of_isPullback` and
`AlgebraicGeometry.Space.exists_iso_desc_of_isFpqcCovering_of_isPullback`); there the Noetherian
local case gives an isomorphism `Y₁₀ ≅ Y₂₀`, whose base change along `p` is the isomorphism. -/
theorem exists_iso_of_closedFibre_of_isPullback_noetherianStage (Λ₀ : Type u) [CommRing Λ₀]
    [IsLocalRing Λ₀] [IsNoetherianRing Λ₀] (hΛ₀ : B.Contains (Spec (.of Λ₀)))
    (hκ₀ : B.Contains (Spec (.of (ResidueField Λ₀))))
    {X₀ Y₁₀ Y₂₀ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX₀ : IsAlgebraicSpace B integerBase hZ X₀) (hY₁₀ : IsAlgebraicSpace B integerBase hZ Y₁₀)
    (hY₂₀ : IsAlgebraicSpace B integerBase hZ Y₂₀)
    (f₀ : X₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (g₁₀ : Y₁₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (g₂₀ : Y₂₀ ⟶ yoneda.obj (integerSiteObject B hZ hΛ₀))
    (hfl₀ : IsFlat B integerBase hZ f₀) (hpr₀ : IsProper B integerBase hZ f₀)
    (hfp₀ : IsFinitePresentation B integerBase hZ f₀)
    (hfl₁₀ : IsFlat B integerBase hZ g₁₀) (hpr₁₀ : IsProper B integerBase hZ g₁₀)
    (hfp₁₀ : IsFinitePresentation B integerBase hZ g₁₀)
    (hfl₂₀ : IsFlat B integerBase hZ g₂₀) (hpr₂₀ : IsProper B integerBase hZ g₂₀)
    (c₁₀ : X₀ ⟶ Y₁₀) (c₂₀ : X₀ ⟶ Y₂₀) (hc₁₀ : c₁₀ ≫ g₁₀ = f₀) (hc₂₀ : c₂₀ ≫ g₂₀ = f₀)
    {W : BigFppfOver B integerBase hZ} (p : W ⟶ integerSiteObject B hZ hΛ₀)
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY₁ : IsAlgebraicSpace B integerBase hZ Y₁)
    (hY₂ : IsAlgebraicSpace B integerBase hZ Y₂)
    (fX : X ⟶ yoneda.obj W) (g₁ : Y₁ ⟶ yoneda.obj W) (g₂ : Y₂ ⟶ yoneda.obj W)
    (qX : X ⟶ X₀) (q₁ : Y₁ ⟶ Y₁₀) (q₂ : Y₂ ⟶ Y₂₀) (sqX : IsPullback qX fX f₀ (yoneda.map p))
    (sq₁ : IsPullback q₁ g₁ g₁₀ (yoneda.map p)) (sq₂ : IsPullback q₂ g₂ g₂₀ (yoneda.map p))
    (hdX : HasRelativeDimensionLE 1 B integerBase hZ fX)
    (hd₁ : HasRelativeDimensionLE 1 B integerBase hZ g₁)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = fX) (hc₂ : c₂ ≫ g₂ = fX)
    (hcq₁ : c₁ ≫ q₁ = qX ≫ c₁₀) (hcq₂ : c₂ ≫ q₂ = qX ≫ c₂₀)
    {K : BigFppfOver B integerBase hZ} (k : K ⟶ W) (m : K ⟶ integerSiteObject B hZ hκ₀)
    (hkm : k ≫ p = m ≫ closedPointSiteMap Λ₀ hΛ₀ hκ₀)
    (hm : IsFpqcCovering B integerBase hZ (fun _ : Unit => yoneda.map m))
    [Flat ((𝒯).map m)] [Surjective ((𝒯).map m)]
    {FX F₁ : BigFppfOver B integerBase hZ} (eX : yoneda.obj FX ≅ pullback fX (yoneda.map k))
    (e₁ : yoneda.obj F₁ ≅ pullback g₁ (yoneda.map k)) (tX : FX ⟶ K) (t₁ : F₁ ⟶ K)
    (heX : eX.hom ≫ pullback.snd fX (yoneda.map k) = yoneda.map tX)
    (he₁ : e₁.hom ≫ pullback.snd g₁ (yoneda.map k) = yoneda.map t₁) (a₁ : FX ⟶ F₁)
    (ha₁ : yoneda.map a₁ ≫ e₁.hom =
      eX.hom ≫ pullback.map fX (yoneda.map k) g₁ (yoneda.map k) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
        (by simp))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁)))
    (φ : pullback g₁ (yoneda.map k) ≅ pullback g₂ (yoneda.map k))
    (hφ : φ.hom ≫ pullback.snd g₂ (yoneda.map k) = pullback.snd g₁ (yoneda.map k))
    (hφc : pullback.map fX (yoneda.map k) g₁ (yoneda.map k) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
        (by simp) ≫ φ.hom =
      pullback.map fX (yoneda.map k) g₂ (yoneda.map k) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂])
        (by simp)) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ c₁ ≫ ψ.hom = c₂ ∧
      pullback.fst g₁ (yoneda.map k) ≫ ψ.hom = φ.hom ≫ pullback.fst g₂ (yoneda.map k) := by
  have hkm' : yoneda.map k ≫ yoneda.map p =
      yoneda.map m ≫ yoneda.map (closedPointSiteMap Λ₀ hΛ₀ hκ₀) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hkm]
  obtain ⟨FX₀, F₁₀, tX₀, t₁₀, eX₀, e₁₀, a₁₀, heX₀, he₁₀, hdX₀, hd₁₀', ha₁₀, hat₁₀, hdim₀, h0₀,
      hR₀, φ₀, hφ₀g, hφ₀c, hφ₀q⟩ :=
    exists_closedFibreData_of_isPullback_noetherianStage Λ₀ hΛ₀ hκ₀ hX₀ hY₁₀ hY₂₀ f₀ g₁₀ g₂₀
      hfl₀ hpr₀ hfp₀ hfl₁₀ hpr₁₀ hfp₁₀ hpr₂₀ c₁₀ c₂₀ hc₁₀ hc₂₀ p hX hY₁ hY₂ fX g₁ g₂
      qX q₁ q₂ sqX sq₁ sq₂ hdX hd₁ c₁ c₂ hc₁ hc₂ hcq₁ hcq₂ k m hkm' hm eX e₁ tX t₁ heX
      he₁ a₁ ha₁ h0 hR φ hφ hφc
  obtain ⟨ψ₀, hψ₀g, hψ₀c, hψ₀f⟩ := exists_iso_of_closedFibre_of_isNoetherianRing_of_pullback Λ₀
    hΛ₀ hκ₀ hX₀ hY₁₀ hY₂₀ f₀ g₁₀ g₂₀ hfl₀ hpr₀ hfl₁₀ hpr₁₀ hfl₂₀ hpr₂₀ c₁₀ c₂₀ hc₁₀ hc₂₀ tX₀ t₁₀
    eX₀ e₁₀ heX₀ he₁₀ hdX₀ hd₁₀' a₁₀ ha₁₀ hat₁₀ hdim₀ h0₀ hR₀ φ₀ hφ₀g hφ₀c
  -- the base change along `p`
  obtain ⟨ψ, hψg, hψq⟩ := exists_iso_of_isPullback_of_iso B integerBase hZ _ sq₁ sq₂ ψ₀ hψ₀g
  refine ⟨ψ, hψg, sq₂.hom_ext ?_ ?_, sq₂.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hψq, reassoc_of% hcq₁, hψ₀c, hcq₂]
  · rw [Category.assoc, hψg, hc₁, hc₂]
  · have e₁' : pullback.fst g₁ (yoneda.map k) ≫ q₁ =
        pullback.map g₁ (yoneda.map k) g₁₀ _ q₁ (yoneda.map m) (yoneda.map p) sq₁.w.symm hkm' ≫
          pullback.fst g₁₀ _ := by simp
    have e₂' : pullback.fst g₂ (yoneda.map k) ≫ q₂ =
        pullback.map g₂ (yoneda.map k) g₂₀ _ q₂ (yoneda.map m) (yoneda.map p) sq₂.w.symm hkm' ≫
          pullback.fst g₂₀ _ := by simp
    rw [Category.assoc, hψq, reassoc_of% e₁', hψ₀f, reassoc_of% hφ₀q, Category.assoc, e₂']
  · rw [Category.assoc, hψg, Category.assoc, pullback.condition, pullback.condition,
      reassoc_of% hφ]

end AlgebraicGeometry.Space

end

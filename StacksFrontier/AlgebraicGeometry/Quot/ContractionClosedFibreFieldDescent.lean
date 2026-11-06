module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessNoetherianLocal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ClosedPointBound
import all StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity

/-!
# The closed-fibre hypotheses of Stacks 0E89 along a field extension

The reduction of [Stacks, Tag 0E89] from a local ring to a Noetherian local ring replaces the
base `Spec A` by `Spec A_λ` for a Noetherian local ring `A_λ` with a local map `A_λ ⟶ A`, and the
closed point `s` of `Spec A` by the closed point `s_λ` of `Spec A_λ`. The residue field
`κ(s)` is an extension of `κ(s_λ)`, and the source says that the hypotheses on the closed fibre
"are inherited by `c_{λ, 1, s_λ}` because `{s_λ ⟶ s}` is an fpqc covering". This file proves
that inheritance, with the details the source omits:

* the fibre of a family of curves over the spectrum of a field is presented by a scheme of
  dimension at most one ([Stacks, Tag 0ADD], through
  `AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`);
* `𝒪 ≅ a_* 𝒪` and `R¹a_* 𝒪 = 0` descend along the faithfully flat base change of a field
  extension ([Stacks, Tag 02KH],
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_and_isIso_of_isPullback_of_surjective`);
* an isomorphism of fibres compatible with the `cᵢ` descends along a one-member fpqc covering,
  because `c₁` is scheme-theoretically dominant on the fibre (`𝒪 ≅ c₁,* 𝒪`); this is the descent
  of `Space.exists_iso_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top`.

## Main results

* `AlgebraicGeometry.Space.curveFamilyConditions_of_isPullback`: the four conditions of a family
  of curves pass to base changes.
* `AlgebraicGeometry.Space.exists_presentation_of_curveFamilyConditions_of_field`: the total space
  of a family of curves over a field is presented by a scheme of dimension at most one.
* `AlgebraicGeometry.Space.isZero_and_isIso_of_presentations_of_isPullback`: the descent of the
  two cohomological hypotheses along a flat surjective base change.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_top_of_presentation`: a morphism of
  algebraic spaces presented by a morphism of schemes with `𝒪 ≅ a_* 𝒪` has scheme-theoretic image
  everything.
* `AlgebraicGeometry.Space.exists_iso_desc_of_isFpqcCovering_of_isPullback`: the descent of a
  compatible isomorphism along a one-member fpqc covering, for squares of presheaves.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯S" => BigFppfOver.toScheme B S hS

/-- **The four conditions of a family of curves pass to base changes**: flatness, properness,
finite presentation and relative dimension at most one of `f` give the same for its base change
`f'` along any morphism of the site. -/
theorem curveFamilyConditions_of_isPullback {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T T' : BigFppfOver B S hS} {f : X ⟶ yoneda.obj T} {f' : X' ⟶ yoneda.obj T'}
    {q : X' ⟶ X} {m : T' ⟶ T} (sq : IsPullback q f' f (yoneda.map m))
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hfl : IsFlat B S hS f) (hpr : IsProper B S hS f) (hfp : IsFinitePresentation B S hS f)
    (hd : HasRelativeDimensionLE 1 B S hS f) :
    IsFlat B S hS f' ∧ IsProper B S hS f' ∧ IsFinitePresentation B S hS f' ∧
      HasRelativeDimensionLE 1 B S hS f' := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hT' := isAlgebraicSpace_yoneda B S hS T'
  refine ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_homMk B S hS hX hT' hT hX' sq) hfl,
    isProper_of_isPullback' hX' hX hT' hT sq hpr,
    isFinitePresentation_of_isPullback B S hS hX' hX hT' hT sq hfp, fun x' => ?_⟩
  obtain ⟨e, he, h⟩ := hd (pointsMap B S hS X' q x')
  exact ⟨e, he, (hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX hT' hT
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1) x' e).1 h⟩

/-- A commutative square of the site whose Yoneda image is cartesian is cartesian, as is its image
in schemes. -/
private theorem isPullback_of_isPullback_yoneda_map {W X Y Z : BigFppfOver B S hS} {p : W ⟶ X}
    {q : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}
    (h : IsPullback (yoneda.map p) (yoneda.map q) (yoneda.map r) (yoneda.map s)) :
    IsPullback p q r s ∧ IsPullback ((𝒯S).map p) ((𝒯S).map q) ((𝒯S).map r) ((𝒯S).map s) := by
  have h' : IsPullback p q r s :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using h.w)) h
  have _ : PreservesLimitsOfShape WalkingCospan (𝒯S) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact ⟨h', h'.map (𝒯S)⟩

/-- **A square of represented presheaves which is cartesian up to isomorphisms is a cartesian
square of schemes.** If the presheaves `X, Y, X₀, Y₀` of a cartesian square are, through `eX`,
`e`, `eX₀`, `e₀`, represented by objects of the site, and `a`, `a₀` represent its vertical sides,
then the morphisms representing its horizontal sides make a cartesian square of underlying
schemes. -/
theorem exists_isPullback_toScheme_of_isPullback_of_iso
    {X Y X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {qX : X ⟶ X₀} {c : X ⟶ Y} {c₀ : X₀ ⟶ Y₀}
    {qY : Y ⟶ Y₀} (sq : IsPullback qX c c₀ qY) {FX F FX₀ F₀ : BigFppfOver B S hS}
    (eX : yoneda.obj FX ≅ X) (e : yoneda.obj F ≅ Y) (eX₀ : yoneda.obj FX₀ ≅ X₀)
    (e₀ : yoneda.obj F₀ ≅ Y₀) (a : FX ⟶ F) (a₀ : FX₀ ⟶ F₀) (ha : yoneda.map a ≫ e.hom = eX.hom ≫ c)
    (ha₀ : yoneda.map a₀ ≫ e₀.hom = eX₀.hom ≫ c₀) :
    ∃ (rX : FX ⟶ FX₀) (r : F ⟶ F₀), yoneda.map rX = eX.hom ≫ qX ≫ eX₀.inv ∧
      yoneda.map r = e.hom ≫ qY ≫ e₀.inv ∧ IsPullback rX a a₀ r ∧
      IsPullback ((𝒯S).map rX) ((𝒯S).map a) ((𝒯S).map a₀) ((𝒯S).map r) := by
  set rX := Yoneda.fullyFaithful.preimage (eX.hom ≫ qX ≫ eX₀.inv)
  set r := Yoneda.fullyFaithful.preimage (e.hom ≫ qY ≫ e₀.inv)
  have hrX : yoneda.map rX = eX.hom ≫ qX ≫ eX₀.inv := Functor.FullyFaithful.map_preimage _ _
  have hr : yoneda.map r = e.hom ≫ qY ≫ e₀.inv := Functor.FullyFaithful.map_preimage _ _
  have ha' : yoneda.map a = eX.hom ≫ c ≫ e.inv := by rw [← reassoc_of% ha]; simp
  have ha₀' : yoneda.map a₀ = eX₀.hom ≫ c₀ ≫ e₀.inv := by rw [← reassoc_of% ha₀]; simp
  have h₁ : IsPullback (yoneda.map rX) (yoneda.map a) (yoneda.map a₀) (yoneda.map r) :=
    IsPullback.of_iso sq eX.symm eX₀.symm e.symm e₀.symm (by simp [hrX])
      (by simp [ha']) (by simp [ha₀']) (by simp [hr])
  exact ⟨rX, r, hrX, hr, isPullback_of_isPullback_yoneda_map B S hS h₁⟩

/-- A morphism of the site whose Yoneda image is, up to isomorphism, a proper morphism of
algebraic spaces is proper on underlying schemes. -/
theorem isProper_toScheme_map_of_iso {F K : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : yoneda.obj F ≅ X) (f : X ⟶ yoneda.obj K)
    (t : F ⟶ K) (he : e.hom ≫ f = yoneda.map t) (hf : IsProper B S hS f) :
    _root_.AlgebraicGeometry.IsProper ((𝒯S).map t) := by
  rw [← isProper_yoneda_map_iff, ← he]
  exact (isProper_isIso_comp_iff B S hS e.hom f).2 hf

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **`𝒪 ≅ a_* 𝒪` and `R¹a_* 𝒪 = 0` descend along a flat surjective base change of the base,
read on presentations.** Let `X ⟶ Y` over `K` be the base change along `m : K ⟶ K₀` of
`X₀ ⟶ Y₀` over `K₀`, all four presented by objects of the site, with `a`, `a₀` the morphisms of
the site presenting `c`, `c₀`. If `m` is flat and surjective on underlying schemes, `a₀` is
proper with fibres of dimension at most one and `a` satisfies `𝒪 ≅ a_* 𝒪` and `R¹a_* 𝒪 = 0`,
then so does `a₀`. -/
theorem isZero_and_isIso_of_presentations_of_isPullback {K₀ K : BigFppfOver B S hS} (m : K ⟶ K₀)
    [Flat ((𝒯S).map m)] [Surjective ((𝒯S).map m)]
    {X₀ Y₀ X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : X₀ ⟶ yoneda.obj K₀}
    {g₀ : Y₀ ⟶ yoneda.obj K₀} {f : X ⟶ yoneda.obj K} {g : Y ⟶ yoneda.obj K} {qX : X ⟶ X₀}
    {qY : Y ⟶ Y₀} (sqX : IsPullback qX f f₀ (yoneda.map m))
    (sqY : IsPullback qY g g₀ (yoneda.map m)) {c₀ : X₀ ⟶ Y₀} {c : X ⟶ Y} (hc₀ : c₀ ≫ g₀ = f₀)
    (hc : c ≫ g = f) (hcq : c ≫ qY = qX ≫ c₀) {FX₀ F₀ FX F : BigFppfOver B S hS}
    (eX₀ : yoneda.obj FX₀ ≅ X₀) (e₀ : yoneda.obj F₀ ≅ Y₀) (eX : yoneda.obj FX ≅ X)
    (e : yoneda.obj F ≅ Y) (t₀ : F₀ ⟶ K₀) (t : F ⟶ K) (he₀ : e₀.hom ≫ g₀ = yoneda.map t₀)
    (he : e.hom ≫ g = yoneda.map t) (a₀ : FX₀ ⟶ F₀) (a : FX ⟶ F)
    (ha₀ : yoneda.map a₀ ≫ e₀.hom = eX₀.hom ≫ c₀) (ha : yoneda.map a ≫ e.hom = eX.hom ≫ c)
    [_root_.AlgebraicGeometry.IsProper ((𝒯S).map a₀)]
    (hdim₀ : ∀ y, topologicalKrullDim (((𝒯S).map a₀).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯S).map a)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯S).map a))) :
    IsZero (firstDirectImageStructureSheaf ((𝒯S).map a₀)) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯S).map a₀)) := by
  have sq : IsPullback qX c c₀ qY := by
    refine IsPullback.of_bot ?_ hcq.symm sqY
    rw [hc, hc₀]
    exact sqX
  obtain ⟨rX, r, -, hr, -, H⟩ :=
    exists_isPullback_toScheme_of_isPullback_of_iso B S hS sq eX e eX₀ e₀ a a₀ ha ha₀
  -- `r` is the base change of `m` along `t₀`
  have sqt : IsPullback (yoneda.map r) (yoneda.map t) (yoneda.map t₀) (yoneda.map m) :=
    IsPullback.of_iso sqY e.symm e₀.symm (Iso.refl _) (Iso.refl _) (by simp [hr])
      (by simp [← he]) (by simp [← he₀]) (by simp)
  have sqT := (isPullback_of_isPullback_yoneda_map B S hS sqt).2
  have : Flat ((𝒯S).map r) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) sqT.flip inferInstance
  have : Surjective ((𝒯S).map r) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) sqT.flip
      inferInstance
  exact isZero_and_isIso_of_isPullback_of_surjective H hdim₀ hR h0

/-- **A morphism presented by a morphism of schemes with `𝒪 ≅ a_* 𝒪` has scheme-theoretic image
everything.** The morphism of schemes `a` is scheme-theoretically dominant, its kernel ideal
sheaf being zero, and composing with isomorphisms keeps the scheme-theoretic image everything. -/
theorem schemeTheoreticImageSubfunctor_eq_top_of_presentation {FX F : BigFppfOver B S hS}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (eX : yoneda.obj FX ≅ X) (e : yoneda.obj F ≅ Y) (a : FX ⟶ F) (c : X ⟶ Y)
    (ha : yoneda.map a ≫ e.hom = eX.hom ≫ c) [QuasiCompact ((𝒯S).map a)]
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯S).map a))) :
    schemeTheoreticImageSubfunctor B S hS c = ⊤ := by
  have hdom := isSchemeTheoreticallyDominant_of_isIso_unitToPushforwardUnit ((𝒯S).map a)
  have h₁ : schemeTheoreticImageSubfunctor B S hS (yoneda.map a) = ⊤ :=
    (schemeTheoreticImageSubfunctor_yoneda_eq_top_iff B S hS a).2 hdom
  have h₂ : schemeTheoreticImageSubfunctor B S hS (eX.inv ≫ yoneda.map a) = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_congr_range B S hS _ (yoneda.map a)
      (isAlgebraicSpace_yoneda B S hS F) (by
        rw [Subfunctor.range_comp, (Subfunctor.epi_iff_range_eq_top eX.inv).1
          (@IsIso.epi_of_iso _ _ _ _ eX.inv (Iso.isIso_inv eX)), Subfunctor.image_top])]
    exact h₁
  have hc : c = (eX.inv ≫ yoneda.map a) ≫ e.hom := by
    rw [Category.assoc, ha, Iso.inv_hom_id_assoc]
  rw [hc]
  exact schemeTheoreticImageSubfunctor_comp_eq_top_of_isIso (isAlgebraicSpace_yoneda B S hS F) hY
    _ e.hom h₂

/-- **An isomorphism of base changes compatible with a morphism of full scheme-theoretic image
descends along a one-member fpqc covering**, for cartesian squares of presheaves over a morphism
`m : T' ⟶ T` of the site. This is
`Space.exists_iso_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top` read on
presheaves. -/
theorem exists_iso_desc_of_isFpqcCovering_of_isPullback {T T' : BigFppfOver B S hS} (m : T' ⟶ T)
    (hm : IsFpqcCovering B S hS (fun _ : Unit => yoneda.map m))
    {X Y₁ Y₂ X' Y₁' Y₂' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hY₂ : IsAlgebraicSpace B S hS Y₂)
    (hX' : IsAlgebraicSpace B S hS X') (hY₁' : IsAlgebraicSpace B S hS Y₁')
    (hY₂' : IsAlgebraicSpace B S hS Y₂') {f : X ⟶ yoneda.obj T} {g₁ : Y₁ ⟶ yoneda.obj T}
    {g₂ : Y₂ ⟶ yoneda.obj T} (hg₁ : IsSeparated B S hS g₁) (hg₂ : IsSeparated B S hS g₂)
    {f' : X' ⟶ yoneda.obj T'} {g₁' : Y₁' ⟶ yoneda.obj T'} {g₂' : Y₂' ⟶ yoneda.obj T'}
    {qX : X' ⟶ X} {q₁ : Y₁' ⟶ Y₁} {q₂ : Y₂' ⟶ Y₂} (sqX : IsPullback qX f' f (yoneda.map m))
    (sq₁ : IsPullback q₁ g₁' g₁ (yoneda.map m)) (sq₂ : IsPullback q₂ g₂' g₂ (yoneda.map m))
    {c₁ : X ⟶ Y₁} {c₂ : X ⟶ Y₂} (hc₁ : c₁ ≫ g₁ = f) (hc₂ : c₂ ≫ g₂ = f) {c₁' : X' ⟶ Y₁'}
    (hc₁'q : c₁' ≫ q₁ = qX ≫ c₁) (hc₁'g : c₁' ≫ g₁' = f') (hqc : IsQuasiCompact B S hS c₁')
    (hdom : schemeTheoreticImageSubfunctor B S hS c₁' = ⊤) (φ : Y₁' ≅ Y₂')
    (hφg : φ.hom ≫ g₂' = g₁') (hφc : c₁' ≫ φ.hom ≫ q₂ = qX ≫ c₂) :
    ∃ ψ : Y₁ ≅ Y₂, ψ.hom ≫ g₂ = g₁ ∧ q₁ ≫ ψ.hom = φ.hom ≫ q₂ ∧ c₁ ≫ ψ.hom = c₂ := by
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hT' := isAlgebraicSpace_yoneda B S hS T'
  let φb : (⟨Y₁', hY₁'⟩ : AlgebraicSpaces B S hS) ≅ ⟨Y₂', hY₂'⟩ :=
    (ObjectProperty.fullyFaithfulι _).preimageIso φ
  obtain ⟨ψ, hψg, hψp, hψc⟩ :=
    exists_iso_desc_of_isFpqcCovering_of_schemeTheoreticImageSubfunctor_eq_top
      (T := ⟨yoneda.obj T, hT⟩) (T' := ⟨yoneda.obj T', hT'⟩) (X := ⟨X, hX⟩) (Y₁ := ⟨Y₁, hY₁⟩)
      (Y₂ := ⟨Y₂, hY₂⟩) (X' := ⟨X', hX'⟩) (Y₁' := ⟨Y₁', hY₁'⟩) (Y₂' := ⟨Y₂', hY₂'⟩)
      (π := ObjectProperty.homMk (yoneda.map m)) hm (f := ObjectProperty.homMk f)
      (g₁ := ObjectProperty.homMk g₁) (g₂ := ObjectProperty.homMk g₂) hg₁ hg₂
      (isPullback_homMk B S hS hX hT' hT hX' sqX) (isPullback_homMk B S hS hY₁ hT' hT hY₁' sq₁)
      (isPullback_homMk B S hS hY₂ hT' hT hY₂' sq₂) (c₁ := ObjectProperty.homMk c₁)
      (ObjectProperty.hom_ext _ hc₁) (c₂ := ObjectProperty.homMk c₂)
      (ObjectProperty.hom_ext _ hc₂) (c₁' := ObjectProperty.homMk c₁')
      (ObjectProperty.hom_ext _ hc₁'q) (ObjectProperty.hom_ext _ hc₁'g) hqc hdom φb
      (ObjectProperty.hom_ext _ hφg) (ObjectProperty.hom_ext _ hφc)
  exact ⟨(ObjectProperty.ι _).mapIso ψ, congrArg (fun k => k.hom) hψg,
    congrArg (fun k => k.hom) hψp, congrArg (fun k => k.hom) hψc⟩

/-- The scheme-theoretic fibres of a morphism from a scheme of dimension at most one have
dimension at most one. -/
theorem topologicalKrullDim_fiber_le_one_of_le_one {X Y : Scheme.{u}} (a : X ⟶ Y)
    (hX : topologicalKrullDim X ≤ 1) (y : Y) :
    topologicalKrullDim (a.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
  topologicalKrullDim_fiber_le_of_preimage_subset a y Set.univ (Set.subset_univ _) (by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph]
    exact_mod_cast hX)

end General

section Integers

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **The total space of a family of curves over a field is presented by a scheme of dimension at
most one** ([Stacks, Tag 0ADD]). If `f : X ⟶ Spec K` satisfies the four conditions of a family of
curves, then `X` is represented by an object `F` of the site over `Spec K` whose underlying scheme
has dimension at most one. -/
theorem exists_presentation_of_curveFamilyConditions_of_field {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X)
    (f : X ⟶ yoneda.obj (integerSiteObject B hZ hK)) (hfl : IsFlat B integerBase hZ f)
    (hpr : IsProper B integerBase hZ f) (hfp : IsFinitePresentation B integerBase hZ f)
    (hd : HasRelativeDimensionLE 1 B integerBase hZ f) :
    ∃ (F : BigFppfOver B integerBase hZ) (t : F ⟶ integerSiteObject B hZ hK)
      (e : yoneda.obj F ≅ X), e.hom ≫ f = yoneda.map t ∧ topologicalKrullDim ((𝒯).obj F) ≤ 1 := by
  let C : CurveFamily B hZ :=
    { base := integerSiteObject B hZ hK
      total := ⟨X, hX⟩
      toBase := ObjectProperty.homMk f
      flat := hfl
      proper := hpr
      finitePresentation := hfp
      relativeDimensionLE := hd }
  have hrep : X.IsRepresentable := C.isRepresentable_total_of_base_eq (K := K) rfl
  have hdimF := CurveFamily.dimensionAtPoint_total_le_one_of_base_eq hK C rfl
  refine ⟨X.reprX, Yoneda.fullyFaithful.preimage (X.reprW.hom ≫ f), X.reprW,
    (Functor.FullyFaithful.map_preimage _ _).symm, ?_⟩
  rw [← dimension_yoneda_eq_topologicalKrullDim B integerBase hZ,
    ← dimension_eq_of_iso B integerBase hZ hX (isAlgebraicSpace_yoneda B integerBase hZ _)
      X.reprW.symm]
  exact iSup_le hdimF

end Integers

end AlgebraicGeometry.Space

end

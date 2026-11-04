module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty

/-!
# The normalization of a scheme in a scheme, read as algebraic spaces

Let `f₀ : Y₀ ⟶ X₀` be a quasi-compact quasi-separated morphism of objects of the big fppf site of
`S`, and let `Y₀ ⟶ N₀ ⟶ X₀` be the normalization of the scheme `X₀` in the scheme `Y₀` of
Morphisms, Section 035E (Mathlib's `AlgebraicGeometry.Scheme.Hom.normalization`), read in the
site.  This file shows that the morphisms of algebraic spaces the factorization represents have
the universal property of Stacks 0823, and deduces that **any** factorization of a morphism of
representable algebraic spaces with that universal property is, canonically, the normalization
of schemes.  That is the comparison made by part (2) of Stacks 0ABP, once the normalization of
Definition 0822 is known to have the universal property.

## Main results

* `AlgebraicGeometry.Space.isRelativeNormalization_yoneda_map_of_normalization`: the
  normalization of schemes, read in the site, is a relative normalization in the sense of
  `AlgebraicGeometry.Space.IsRelativeNormalization`.
* `AlgebraicGeometry.Space.IsRelativeNormalization.ofIso`: the universal property transports
  along isomorphisms of the source and of the target.
* `AlgebraicGeometry.Space.IsRelativeNormalization.exists_iso_normalization_of_representable`:
  if `X` and `Y` are representable, by `X₀` and `Y₀`, any relative normalization `Y ⟶ X' ⟶ X`
  of a morphism inducing a quasi-compact quasi-separated `f₀ : Y₀ ⟶ X₀` has `X'` represented by
  an object of the site whose underlying scheme is the normalization of `X₀` in `Y₀`, by an
  isomorphism compatible with both legs of both factorizations.

## Implementation notes

The universal property of the normalization of schemes is Mathlib's
`AlgebraicGeometry.Scheme.Hom.normalizationDesc` (existence) and
`AlgebraicGeometry.Scheme.Hom.normalization.hom_ext` (uniqueness, against an affine morphism).
To use them for an integral morphism `π : Z ⟶ X₀` of algebraic spaces, `Z` is first shown to be
representable: an integral morphism is relatively representable (Stacks 03ZQ,
`AlgebraicGeometry.Space.isIntegralHom_iff_representable`), so its base change along the
identity of the representable target is represented, and that base change is `Z` itself
(`AlgebraicGeometry.Space.isIso_fst_of_isPullback_id`).

## References

* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` is an integral morphism. -/
theorem isIntegralHom_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : IsIntegralHom B S hS e := by
  intro Z hZ g
  refine ⟨Z, 𝟙 Z, g ≫ inv e, ?_, hZ, ?_⟩
  · rw [yoneda.map_id]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- **The normalization of a scheme in a scheme is a relative normalization of the represented
algebraic spaces.**  Let `f₀ : Y₀ ⟶ X₀` be a morphism of the big fppf site of `S` whose
underlying morphism of schemes is quasi-compact and quasi-separated, and let `t : Y₀ ⟶ N₀`,
`ν₀ : N₀ ⟶ X₀` be morphisms of the site whose underlying morphisms of schemes are identified,
by `e`, with the two legs of the normalization of `X₀` in `Y₀` (Stacks 035H).  Then
`yoneda.map t` and `yoneda.map ν₀` have the universal property of Stacks 0823. -/
theorem isRelativeNormalization_yoneda_map_of_normalization {Y₀ X₀ N₀ : BigFppfOver B S hS}
    (f₀ : Y₀ ⟶ X₀) [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)] (t : Y₀ ⟶ N₀) (ν₀ : N₀ ⟶ X₀)
    (e : (BigFppfOver.toScheme B S hS).obj N₀ ≅
      ((BigFppfOver.toScheme B S hS).map f₀).normalization)
    (ht : (BigFppfOver.toScheme B S hS).map t ≫ e.hom =
      ((BigFppfOver.toScheme B S hS).map f₀).toNormalization)
    (hν : e.hom ≫ ((BigFppfOver.toScheme B S hS).map f₀).fromNormalization =
      (BigFppfOver.toScheme B S hS).map ν₀) :
    IsRelativeNormalization B S hS (yoneda.map f₀) (yoneda.map ν₀) (yoneda.map t) := by
  let T := BigFppfOver.toScheme B S hS
  have htν : t ≫ ν₀ = f₀ := T.map_injective (by
    rw [T.map_comp, ← hν, ← Category.assoc, ht, Scheme.Hom.toNormalization_fromNormalization])
  refine ⟨by rw [← yoneda.map_comp, htν], ?_, ?_⟩
  · refine isIntegralHom_yoneda_map B S hS ν₀ ?_
    show _root_.AlgebraicGeometry.IsIntegralHom (T.map ν₀)
    rw [← hν]
    infer_instance
  intro Z hZ π hπ g hg
  obtain ⟨hrep, hint⟩ := (isIntegralHom_iff_representable B S hS π hZ
    (isAlgebraicSpace_yoneda B S hS X₀)).1 hπ
  obtain ⟨Z₀, π₀, i, hpb⟩ := hrep (𝟙 (yoneda.obj X₀))
  have : IsIso i := isIso_fst_of_isPullback_id B S hS hpb
  have hπ₀ : _root_.AlgebraicGeometry.IsIntegralHom (T.map π₀) :=
    hint.property (𝟙 _) i π₀ hpb
  have hiπ : inv i ≫ yoneda.map π₀ = π := by
    rw [IsIso.inv_comp_eq, hpb.w, Category.comp_id]
  have hlift : ∀ {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ Z) (c : A ⟶ X₀),
      a ≫ π = yoneda.map c → ∃ a₀ : A ⟶ Z₀, a = yoneda.map a₀ ≫ i ∧ a₀ ≫ π₀ = c := by
    intro A a c hac
    refine ⟨yoneda.preimage (a ≫ inv i), by simp, yoneda.map_injective ?_⟩
    rw [yoneda.map_comp, yoneda.map_preimage, Category.assoc, hiπ, hac]
  obtain ⟨g₀, hg₀, hg₀π⟩ := hlift g f₀ hg
  let d := (T.map f₀).normalizationDesc (T.map g₀) (T.map π₀) (by rw [← T.map_comp, hg₀π])
  have hdπ : d ≫ T.map π₀ = (T.map f₀).fromNormalization :=
    Scheme.Hom.normalizationDesc_comp _ _ _ _
  have hdt : (T.map f₀).toNormalization ≫ d = T.map g₀ :=
    Scheme.Hom.toNormalization_normalizationDesc _ _ _ _
  obtain ⟨h₀, hh₀⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (e.hom ≫ d) (by
    rw [← toScheme_map_comp_inclusion_hom B S hS π₀, Category.assoc, ← Category.assoc d, hdπ,
      ← Category.assoc, hν, toScheme_map_comp_inclusion_hom])
  have hth₀ : t ≫ h₀ = g₀ := T.map_injective (by
    rw [T.map_comp, hh₀, ← Category.assoc, ht, hdt])
  have hh₀π : h₀ ≫ π₀ = ν₀ := T.map_injective (by
    rw [T.map_comp, hh₀, Category.assoc, hdπ, hν])
  refine ⟨yoneda.map h₀ ≫ i, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← yoneda.map_comp, hth₀, hg₀]
  · rw [Category.assoc, ← hiπ, IsIso.hom_inv_id_assoc, ← yoneda.map_comp, hh₀π]
  · rintro h' ⟨h'1, h'2⟩
    obtain ⟨h'₀, hh'₀, hh'₀π⟩ := hlift h' ν₀ h'2
    have hth'₀ : t ≫ h'₀ = g₀ := yoneda.map_injective ((cancel_mono i).1 (by
      rw [yoneda.map_comp, Category.assoc, ← hh'₀, ← hg₀, h'1]))
    have heq : h'₀ = h₀ := by
      refine T.map_injective ((cancel_epi e.inv).1 ?_)
      rw [hh₀, Iso.inv_hom_id_assoc]
      refine Scheme.Hom.normalization.hom_ext _ _ _ (T.map π₀) ?_ ?_ hdπ
      · rw [← Category.assoc, ← (Iso.eq_comp_inv e).2 ht, ← T.map_comp, hth'₀, hdt]
      · rw [Category.assoc, ← T.map_comp, hh'₀π, Iso.inv_comp_eq, hν]
    rw [hh'₀, heq]

namespace IsRelativeNormalization

variable {B S hS}

/-- **The universal property of Stacks 0823 transports along isomorphisms of the source and of
the target.** -/
theorem ofIso {Y X X' Y₁ X₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : Y ⟶ X} {ν : X' ⟶ X}
    {f' : Y ⟶ X'} (h : IsRelativeNormalization B S hS f ν f') (eY : Y ≅ Y₁) (eX : X ≅ X₁) :
    IsRelativeNormalization B S hS (eY.inv ≫ f ≫ eX.hom) (ν ≫ eX.hom) (eY.inv ≫ f') := by
  refine ⟨by rw [Category.assoc, ← Category.assoc f', h.fac], isIntegralHom_comp B S hS
    h.isIntegralHom (isIntegralHom_of_isIso B S hS eX.hom), ?_⟩
  intro Z hZ π hπ g hg
  have hg' : (eY.hom ≫ g) ≫ π ≫ eX.inv = f := by
    simp [reassoc_of% hg]
  obtain ⟨k, ⟨hk1, hk2⟩, hku⟩ := h.existsUnique_lift hZ (π ≫ eX.inv)
    (isIntegralHom_comp B S hS hπ (isIntegralHom_of_isIso B S hS eX.inv)) (eY.hom ≫ g) hg'
  refine ⟨k, ⟨by rw [Category.assoc, hk1, Iso.inv_hom_id_assoc], by simp [← hk2]⟩, ?_⟩
  rintro k' ⟨hk'1, hk'2⟩
  exact hku k' ⟨by simp [← hk'1], by rw [← Category.assoc, hk'2]; simp⟩

/-- **A relative normalization of a morphism of representable algebraic spaces is the
normalization of schemes.**  Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` with `X`
and `Y` representable, by objects `X₀` and `Y₀` of the site, and let `f₀ : Y₀ ⟶ X₀` be the
induced morphism, assumed quasi-compact and quasi-separated.  If `Y ⟶ X' ⟶ X` has the universal
property of Stacks 0823, then `X'` is represented by an object `N₀` of the site whose underlying
scheme is the normalization of `X₀` in `Y₀` of Stacks 035H, by an isomorphism compatible with
both legs of both factorizations. -/
theorem exists_iso_normalization_of_representable {Y X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : Y ⟶ X} {ν : X' ⟶ X} {f' : Y ⟶ X'} (h : IsRelativeNormalization B S hS f ν f')
    (hX' : IsAlgebraicSpace B S hS X') {X₀ Y₀ : BigFppfOver B S hS}
    (eX : X ≅ yoneda.obj X₀) (eY : Y ≅ yoneda.obj Y₀) (f₀ : Y₀ ⟶ X₀)
    (hf₀ : yoneda.map f₀ = eY.inv ≫ f ≫ eX.hom)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)] :
    ∃ (N₀ : BigFppfOver B S hS) (t : Y₀ ⟶ N₀) (ν₀ : N₀ ⟶ X₀)
      (e : (BigFppfOver.toScheme B S hS).obj N₀ ≅
        ((BigFppfOver.toScheme B S hS).map f₀).normalization)
      (φ : X' ≅ yoneda.obj N₀),
      f' ≫ φ.hom = eY.hom ≫ yoneda.map t ∧
      φ.hom ≫ yoneda.map ν₀ = ν ≫ eX.hom ∧
      (BigFppfOver.toScheme B S hS).map t ≫ e.hom =
        ((BigFppfOver.toScheme B S hS).map f₀).toNormalization ∧
      e.hom ≫ ((BigFppfOver.toScheme B S hS).map f₀).fromNormalization =
        (BigFppfOver.toScheme B S hS).map ν₀ := by
  obtain ⟨N₀, t, ν₀, e, -, -, -, ht, hν⟩ := NormalizationInData.exists_iso_yoneda_of_representable
    B S hS Y₀ X₀ f₀ (NormalizationInData.ofRepresentable B S hS Y₀ X₀ f₀)
  have hN := isRelativeNormalization_yoneda_map_of_normalization B S hS f₀ t ν₀ e ht hν
  have h' := h.ofIso eY eX
  rw [← hf₀] at h'
  obtain ⟨φ, ⟨hφ1, hφ2⟩, -⟩ := h'.existsUnique_iso hN hX' (isAlgebraicSpace_yoneda B S hS N₀)
  refine ⟨N₀, t, ν₀, e, φ, ?_, hφ2, ht, hν⟩
  rw [← hφ1, Category.assoc, Iso.hom_inv_id_assoc]

end IsRelativeNormalization

end AlgebraicGeometry.Space

end

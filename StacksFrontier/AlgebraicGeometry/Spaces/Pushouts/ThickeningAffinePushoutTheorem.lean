module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SchemeChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineEtaleLocalPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineAtlasCartesianCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeAmbient

/-!
# Pushouts of algebraic spaces along a thickening and an affine morphism (Stacks 07VX)

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over `S`.
Given the lifting of étale scheme charts along thickenings
(`AlgebraicGeometry.Space.C1573.SchemeChartLiftProperty`), every such span has a compatible pair of
étale scheme charts, so the pushout `Y' = Y ⨿_X X'` exists, `Y ⟶ Y'` is a thickening, and for
every scheme `W` étale over `Y'` the ring `Γ(W, 𝒪)` is the fibre product of the rings of the
base changes of `W` to `Y` and `X'` over that of its base change to `X`.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pushout of a thickening and an affine morphism of algebraic spaces exists. -/
theorem hasPushout_of_schemeChartLift (hlift : C1573.SchemeChartLiftProperty B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) : HasPushout i f :=
  hasPushout_of_isThickening_of_isAffineHom B S hS
    (C1573.hasThickeningAffineAtlases_of_schemeChartLift B S hS hlift) i f hi hf

/-- The morphism from the affine target into the pushout is a thickening. -/
theorem pushout_inr_isThickening_of_schemeChartLift (hlift : C1573.SchemeChartLiftProperty B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f] :
    IsThickeningHom B S hS (pushout.inr i f) :=
  pushout_inr_isThickening B S hS (C1573.hasThickeningAffineAtlases_of_schemeChartLift B S hS hlift)
    i f hi hf

/-- The structure sheaf of the pushout, section by section on its small étale site: for a scheme
`W` étale over `Y' = Y ⨿_X X'` with base changes `W₁` to `X'`, `W₂` to `Y` and `W₀` to `X`,
`Γ(W, 𝒪) = Γ(W₂, 𝒪) ×_{Γ(W₀, 𝒪)} Γ(W₁, 𝒪)`. -/
theorem pushout_isPullback_appTop_of_schemeChartLift (hlift : C1573.SchemeChartLiftProperty B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f]
    {W W₁ W₂ W₀ : BigFppfOver B S hS} (w : yoneda.obj W ⟶ (pushout i f).1)
    (hwE : IsEtale B S hS w)
    {u₁ : W₁ ⟶ W} {p₁ : yoneda.obj W₁ ⟶ X'.1}
    (h₁ : IsPullback (yoneda.map u₁) p₁ w (pushout.inl i f).hom)
    {u₂ : W₂ ⟶ W} {p₂ : yoneda.obj W₂ ⟶ Y.1}
    (h₂ : IsPullback (yoneda.map u₂) p₂ w (pushout.inr i f).hom)
    {iW : W₀ ⟶ W₁} {fW : W₀ ⟶ W₂} {p₀ : yoneda.obj W₀ ⟶ X.1}
    (h₀₁ : IsPullback (yoneda.map iW) p₀ p₁ i.hom) (h₀₂ : IsPullback (yoneda.map fW) p₀ p₂ f.hom)
    (hw₀ : iW ≫ u₁ = fW ≫ u₂) :
    let Φ := BigFppfOver.toScheme B S hS
    IsPullback ((Φ.map u₂).app ⊤) ((Φ.map u₁).app ⊤) ((Φ.map fW).app ((Φ.map u₂) ⁻¹ᵁ ⊤))
      ((Φ.map iW).app ((Φ.map u₁) ⁻¹ᵁ ⊤) ≫ eqToHom (congrArg (fun O ↦ Γ(Φ.obj W₀, O))
        (congrArg (fun k : Φ.obj W₀ ⟶ Φ.obj W ↦ k ⁻¹ᵁ ⊤)
          (show Φ.map iW ≫ Φ.map u₁ = Φ.map fW ≫ Φ.map u₂ by
            rw [← Φ.map_comp, ← Φ.map_comp, hw₀])))) := by
  intro Φ
  obtain ⟨V, q, hqS, hqE⟩ := Y.property.exists_atlas
  have hr := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.property
    Y.property hf
  have hpbf : IsPullback (hr.1.fst q) (yoneda.map (hr.1.snd q)) f.hom q := hr.1.isPullback q
  have hpE : IsEtale B S hS (hr.1.fst q) :=
    C1573.isEtale_of_isPullback_presheaf B S hS (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS V) Y.property X.property hpbf.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hqE)
  obtain ⟨U', p', k, hp'E, hpbi⟩ := hlift i hi _ (hr.1.fst q) hpE
  obtain ⟨A, E, a, b, hpush, qm, -, hqmS, hqmE, hca, hcb, -⟩ :=
    exists_isPushout_isPullback_charts_of_isPullback B S hS hi hf q (hr.1.fst q) p' k
      (hr.1.snd q) hqS hqE ((isEtale_iff_presheaf_of_yoneda B S hS p').1 hp'E) hpbf hpbi
  let e := hpush.isoPushout
  have hea : a ≫ e.hom = pushout.inl i f := hpush.inl_isoPushout_hom
  have heb : b ≫ e.hom = pushout.inr i f := hpush.inr_isoPushout_hom
  have hca' : IsPullback (yoneda.map A.a) A.p' (qm ≫ e.hom.hom) (pushout.inl i f).hom :=
    IsPullback.of_iso hca (Iso.refl _) (Iso.refl _) (Iso.refl _) ((ObjectProperty.ι _).mapIso e)
      (by simp) (by simp) (by simp) (by
        show a.hom ≫ e.hom.hom = 𝟙 _ ≫ (pushout.inl i f).hom
        rw [Category.id_comp, ← hea]; rfl)
  have hcb' : IsPullback (yoneda.map A.b) A.q (qm ≫ e.hom.hom) (pushout.inr i f).hom :=
    IsPullback.of_iso hcb (Iso.refl _) (Iso.refl _) (Iso.refl _) ((ObjectProperty.ι _).mapIso e)
      (by simp) (by simp) (by simp) (by
        show b.hom ≫ e.hom.hom = 𝟙 _ ≫ (pushout.inr i f).hom
        rw [Category.id_comp, ← heb]; rfl)
  have hqmS' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (qm ≫ e.hom.hom) :=
    MorphismProperty.RespectsIso.postcomp _ _ _ hqmS
  have hqmE' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (qm ≫ e.hom.hom) :=
    MorphismProperty.RespectsIso.postcomp _ _ _ hqmE
  exact isPullback_appTop_of_etale_of_charts B S hS hi hf A (IsPushout.of_hasPushout i f)
    hqmS' hqmE' hca' hcb' w ((isEtale_iff_presheaf_of_yoneda B S hS w).1 hwE) h₁ h₂ h₀₁ h₀₂ hw₀


/-! ### Stacks 07VX -/

/-- Étale scheme charts lift along thickenings of algebraic spaces: Stacks 05ZH with Stacks
05ZR. -/
theorem schemeChartLiftProperty : C1573.SchemeChartLiftProperty B S hS :=
  C1573.schemeChartLiftProperty_of_thickeningRepresentable B S hS
    (fun i hi hX => isRepresentable_of_isThickeningHom_of_isRepresentable B S hS i hi hX)

/-- **Stacks 07VX, existence.** A thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` of
algebraic spaces over `S` have a pushout `Y' = Y ⨿_X X'` in the category of algebraic spaces over
`S`. -/
@[stacks 07VX "existence of the pushout"]
theorem hasPushout_of_isThickeningHom_of_isAffineHom
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) : HasPushout i f :=
  hasPushout_of_schemeChartLift B S hS (schemeChartLiftProperty B S hS) i f hi hf

/-- **Stacks 07VX, `Y' = Y ⨿_X X'` is a thickening of `Y`.** -/
@[stacks 07VX "the pushout is a thickening of Y"]
theorem pushout_inr_isThickeningHom
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f] :
    IsThickeningHom B S hS (pushout.inr i f) :=
  pushout_inr_isThickening_of_schemeChartLift B S hS (schemeChartLiftProperty B S hS) i f hi hf

/-- **Stacks 07VX, the structure sheaf.** `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}` as sheaves on the
small étale site of `Y'`, evaluated on each of its objects: for a scheme `W` étale over `Y'`
with base changes `W₁` to `X'`, `W₂` to `Y` and `W₀` to `X`, the ring `Γ(W, 𝒪)` is the fibre
product of `Γ(W₂, 𝒪)` and `Γ(W₁, 𝒪)` over `Γ(W₀, 𝒪)`.

The objects of the small étale site of `Y'` are the schemes étale over `Y'`, and the sections over
`W` of `𝒪_Y`, `f_*𝒪_X` and `f'_*𝒪_{X'}` are the rings of functions on `W₂`, `W₀` and `W₁`. Limits
of sheaves are computed objectwise, so this objectwise statement is the same as the equality of
sheaves of the source. -/
@[stacks 07VX "the structure sheaf"]
theorem pushout_isPullback_appTop
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f]
    {W W₁ W₂ W₀ : BigFppfOver B S hS} (w : yoneda.obj W ⟶ (pushout i f).1)
    (hwE : IsEtale B S hS w)
    {u₁ : W₁ ⟶ W} {p₁ : yoneda.obj W₁ ⟶ X'.1}
    (h₁ : IsPullback (yoneda.map u₁) p₁ w (pushout.inl i f).hom)
    {u₂ : W₂ ⟶ W} {p₂ : yoneda.obj W₂ ⟶ Y.1}
    (h₂ : IsPullback (yoneda.map u₂) p₂ w (pushout.inr i f).hom)
    {iW : W₀ ⟶ W₁} {fW : W₀ ⟶ W₂} {p₀ : yoneda.obj W₀ ⟶ X.1}
    (h₀₁ : IsPullback (yoneda.map iW) p₀ p₁ i.hom) (h₀₂ : IsPullback (yoneda.map fW) p₀ p₂ f.hom)
    (hw₀ : iW ≫ u₁ = fW ≫ u₂) :
    let Φ := BigFppfOver.toScheme B S hS
    IsPullback ((Φ.map u₂).app ⊤) ((Φ.map u₁).app ⊤) ((Φ.map fW).app ((Φ.map u₂) ⁻¹ᵁ ⊤))
      ((Φ.map iW).app ((Φ.map u₁) ⁻¹ᵁ ⊤) ≫ eqToHom (congrArg (fun O ↦ Γ(Φ.obj W₀, O))
        (congrArg (fun k : Φ.obj W₀ ⟶ Φ.obj W ↦ k ⁻¹ᵁ ⊤)
          (show Φ.map iW ≫ Φ.map u₁ = Φ.map fW ≫ Φ.map u₂ by
            rw [← Φ.map_comp, ← Φ.map_comp, hw₀])))) :=
  pushout_isPullback_appTop_of_schemeChartLift B S hS (schemeChartLiftProperty B S hS) i f hi hf
    w hwE h₁ h₂ h₀₁ h₀₂ hw₀

end AlgebraicGeometry.Space

end

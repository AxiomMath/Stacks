module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.LiftedEtalePresentation
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.Charts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essential surjectivity along integral, universally injective and surjective morphisms

Part of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj`. An integral,
universally injective and surjective morphism restricts to a universal homeomorphism over any chart
of the target; étale schemes lift across it, so every object of the spaces-étale site admits a
lifted étale presentation, and base change is an equivalence of spaces-étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

variable {f : X ⟶ Y} {C : SpacesEtale B S hS X}

/-! ### Integral, universally injective and surjective morphisms -/

/-- An integral, universally injective and surjective morphism `f` of algebraic spaces restricts
over any chart of the target to a universal homeomorphism of schemes: for a morphism `ζ` from an
object `Z` of the site to `Y`, the base change of `f` along `ζ` is represented by an object `J`
of the site, and `j : J ⟶ Z` is a universal homeomorphism of schemes. -/
theorem exists_chart_universalHomeomorphism_of_isIntegralHom_of_universallyInjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hint : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ Y.1) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ X.1),
      IsPullback (yoneda.map j) η ζ f.hom ∧
        _root_.AlgebraicGeometry.UniversalHomeomorphism
          ((BigFppfOver.toScheme B S hS).map j) := by
  have hrep : yoneda.relativelyRepresentable f.hom :=
    relativelyRepresentable_of_isIntegralHom B S hS f hint
  have hUH := presheaf_universalHomeomorphism_of_universalHomeomorphism B S hS hrep
    (universalHomeomorphism_of_isIntegralHom_of_universallyInjective B S hS X.property
      Y.property hint hui hsurj)
  exact ⟨hrep.pullback ζ, hrep.snd ζ, hrep.fst ζ, (hrep.isPullback ζ).flip,
    hUH.property ζ _ _ (hrep.isPullback ζ)⟩

/-- Let `j : W₀ ⟶ W` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is a universal homeomorphism, and let `p` be an étale morphism of schemes from the scheme
underlying an object `U` of the category to the scheme underlying `W₀`. Then the étale lift of
`U` across `j` is itself an object of the category. -/
private theorem exists_bigFppfOver_etale_pullback_iso_of_universalHomeomorphism
    {W₀ W : BigFppfOver B S hS} (j : W₀ ⟶ W)
    (hjUH : _root_.AlgebraicGeometry.UniversalHomeomorphism
      ((BigFppfOver.toScheme B S hS).map j))
    (U : BigFppfOver B S hS)
    (p : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj W₀)
    (hp : _root_.AlgebraicGeometry.Etale p) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ W)
      (_ : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q))
      (e : pullback ((BigFppfOver.toScheme B S hS).map q)
          ((BigFppfOver.toScheme B S hS).map j) ≅ (BigFppfOver.toScheme B S hS).obj U),
      e.hom ≫ p = pullback.snd ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map j) := by
  let : _root_.AlgebraicGeometry.UniversalHomeomorphism
    ((BigFppfOver.toScheme B S hS).map j) := hjUH
  obtain ⟨V₀, q₀, hq₀, e, he⟩ :=
    Stacks.Etale.exists_etale_pullback_iso_of_essSurjAffine
      Stacks.Etale.essSurjAffineEtalePullback
      ((BigFppfOver.toScheme B S hS).map j) ((BigFppfOver.toScheme B S hS).obj U) p hp
  have hV₀ : B.Contains V₀ := by
    have h₁ : (pullback q₀ ((BigFppfOver.toScheme B S hS).map j) : Scheme.{u}) ≃ₜ V₀ :=
      (Stacks.Etale.isHomeomorph_pullbackFst
        ((BigFppfOver.toScheme B S hS).map j) q₀).homeomorph _
    have h₂ : (pullback q₀ ((BigFppfOver.toScheme B S hS).map j) : Scheme.{u}) ≃ₜ
        (BigFppfOver.toScheme B S hS).obj U := Scheme.Hom.homeomorph e.hom
    exact Stacks.Etale.contains_of_etale_of_isHomeomorph B q₀ hq₀ (h₁.symm.trans h₂)
      (Homeomorph.isHomeomorph _) U.left.2 W.left.2
  obtain ⟨q, hqmap⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := BigFppfOver.mk B S hS hV₀ (q₀ ≫ B.inclusion.map W.hom)) (Y := W) q₀ rfl
  refine ⟨BigFppfOver.mk B S hS hV₀ (q₀ ≫ B.inclusion.map W.hom), q, ?_⟩
  rw [hqmap]
  exact ⟨hq₀, e, he⟩

/-- Let `j : J ⟶ Z` be a morphism of objects of the site whose underlying morphism of schemes is a
universal homeomorphism and which exhibits `J` as the base change along `g` of an étale chart `ζ`
of the target, and let `k : U ⟶ J` be étale. Then `U` lifts to an object `V` of the site étale
over `Z`, and the lift is cartesian both over `j` inside the site and over `g` in presheaves. -/
private theorem exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : F ⟶ G} {Z J U : BigFppfOver B S hS}
    (j : J ⟶ Z)
    (hjUH : _root_.AlgebraicGeometry.UniversalHomeomorphism
      ((BigFppfOver.toScheme B S hS).map j))
    (η : yoneda.obj J ⟶ F) (ζ : yoneda.obj Z ⟶ G) (hζ : IsEtale B S hS ζ)
    (hchart : IsPullback (yoneda.map j) η ζ g)
    (k : U ⟶ J)
    (hk : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k)) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ Z) (p : U ⟶ V),
      _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        IsEtale B S hS (yoneda.map q ≫ ζ) ∧
        IsPullback p k q j ∧
        IsPullback (yoneda.map p) (yoneda.map k ≫ η) (yoneda.map q ≫ ζ) g := by
  obtain ⟨V, q, hqE, e, he⟩ :=
    exists_bigFppfOver_etale_pullback_iso_of_universalHomeomorphism B S hS j hjUH U
      ((BigFppfOver.toScheme B S hS).map k) hk
  obtain ⟨p, hsite, hpres⟩ :=
    exists_isPullback_presheaf_of_iso_pullback_toScheme B S hS q j k η ζ hchart e he
  refine ⟨V, q, p, hqE, isEtale_comp B S hS ?_ hζ, hsite, hpres⟩
  exact (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).2
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqE)

/-- If a representable morphism `yoneda.map k` is a base change of an étale morphism of presheaves,
then `k` is étale as a morphism of schemes. -/
private theorem etale_map_of_isPullback_of_presheaf_etale
    {A A' : BigFppfOver B S hS} {C E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : yoneda.obj A ⟶ C}
    {k : A ⟶ A'} {g : C ⟶ E} {h : yoneda.obj A' ⟶ E} (sq : IsPullback p (yoneda.map k) g h)
    (hg : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf g) :
    _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).1
    (etalePresheaf_of_isPullback B S hS sq hg)

/-- For an integral, universally injective and surjective `f` and an object `C` of the
spaces-étale site of `X`, there are objects `V`, `W`, `U`, `R` of the site, structure morphisms
`v`, `w` making `V` and `W` étale over `Y`, a surjective étale chart `c` of `C` by `U` with
kernel pair `(s, t)` by `R`, and projections `a : U ⟶ V`, `b : R ⟶ W` exhibiting `U` and `R` as
the base changes of `V` and of `W` along `f`. -/
theorem exists_liftedEtalePresentation_charts_of_isIntegralHom_of_universallyInjective
    (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (C : SpacesEtale B S hS X) :
    ∃ (V W U R : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y.1) (w : yoneda.obj W ⟶ Y.1)
        (c : yoneda.obj U ⟶ C.1.left.1) (a : U ⟶ V) (b : R ⟶ W) (s t : R ⟶ U),
      IsEtale B S hS v ∧ IsEtale B S hS w ∧ IsEtale B S hS c ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) c ∧
        IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom ∧
        IsPullback (yoneda.map t) (yoneda.map s) c c ∧
        IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w f.hom := by
  obtain ⟨Z, ζ, hζS, hζE⟩ := Y.2.exists_atlas
  have hζI : IsEtale B S hS ζ := isEtale_of_presheaf_etale B S hS hζE
  obtain ⟨J, j, η, hchart, hjUH⟩ :=
    exists_chart_universalHomeomorphism_of_isIntegralHom_of_universallyInjective B S hS f hint
      hui hsurj Z ζ
  have hηE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf η :=
    etalePresheaf_of_isPullback B S hS hchart hζE
  have hηS : (SurjSite B S hS).presheaf η := surjectivePresheaf_of_isPullback B S hS hchart hζS
  obtain ⟨U', c', hc'S, hc'E⟩ := C.1.left.2.exists_atlas
  have hg₀E : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (c' ≫ C.1.hom.hom) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hc'E) C.2)
  obtain ⟨U, κ, m, hUpb⟩ :
      ∃ (U : BigFppfOver B S hS) (κ : yoneda.obj U ⟶ yoneda.obj J) (m : U ⟶ U'),
        IsPullback κ (yoneda.map m) η (c' ≫ C.1.hom.hom) :=
    ⟨_, _, _, hηE.rep.isPullback (c' ≫ C.1.hom.hom)⟩
  obtain ⟨k, hkmap⟩ : ∃ k : U ⟶ J, yoneda.map k = κ :=
    ⟨yoneda.preimage κ, yoneda.map_preimage κ⟩
  rw [← hkmap] at hUpb
  have hmE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m) :=
    etalePresheaf_of_isPullback B S hS hUpb hηE
  have hmS : (SurjSite B S hS).presheaf (yoneda.map m) :=
    surjectivePresheaf_of_isPullback B S hS hUpb hηS
  have hkE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k) :=
    etale_map_of_isPullback_of_presheaf_etale B S hS hUpb.flip hg₀E
  have hcE : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf (yoneda.map m ≫ c') :=
    etaleSite_presheaf_comp B S hS hmE hc'E
  have hcS : (SurjSite B S hS).presheaf (yoneda.map m ≫ c') :=
    surjSite_presheaf_comp B S hS hmS hc'S
  have hcw : yoneda.map k ≫ η = (yoneda.map m ≫ c') ≫ C.1.hom.hom := by
    rw [Category.assoc]; exact hUpb.w
  obtain ⟨R, s₀, t₀, hker⟩ :
      ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) (yoneda.map m ≫ c') (yoneda.map m ≫ c') :=
    ⟨hcE.rep.pullback _, yoneda.preimage (hcE.rep.fst _), hcE.rep.snd _, by
      rw [yoneda.map_preimage]; exact hcE.rep.isPullback _⟩
  have htE : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (s₀ ≫ k)) := by
    rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _
      (etale_map_of_isPullback_of_presheaf_etale B S hS hker.flip hcE) hkE
  obtain ⟨V, q, a, -, hvE, -, hpresA⟩ :=
    exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism B S hS j hjUH η ζ hζI
      hchart k hkE
  obtain ⟨W, qW, b, -, hwE, -, hpresB⟩ :=
    exists_etaleLift_isPullback_of_chart_of_universalHomeomorphism B S hS j hjUH η ζ hζI
      hchart (s₀ ≫ k) htE
  refine ⟨V, W, U, R, yoneda.map q ≫ ζ, yoneda.map qW ≫ ζ, yoneda.map m ≫ c', a, b, t₀, s₀,
    hvE, hwE, isEtale_of_presheaf_etale B S hS hcE, hcS, ?_, hker, ?_⟩
  · rwa [← hcw]
  · rw [Functor.map_comp, Category.assoc, hcw] at hpresB
    simpa only [Category.assoc] using hpresB

/-- Every object of the spaces-étale site of `X` admits a lifted étale presentation across an
integral, universally injective and surjective `f`. -/
theorem nonempty_liftedEtalePresentation_of_isIntegralHom_of_universallyInjective
    (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (C : SpacesEtale B S hS X) :
    Nonempty (LiftedEtalePresentation B S hS f C) := by
  obtain ⟨V, W, U, R, v, w, c, a, b, s, t, hv, hw, hc, hcS, hA, hC, hB⟩ :=
    exists_liftedEtalePresentation_charts_of_isIntegralHom_of_universallyInjective B S hS f
      hint hui hsurj C
  exact nonempty_liftedEtalePresentation_of_charts B S hS f hint hui hsurj C
    hv hw hc hcS hA hC hB

/-- Base change `V ↦ X ×_Y V` is essentially surjective from the spaces-étale site of `Y` to that
of `X` for every integral, universally injective and surjective morphism `f` of algebraic
spaces. -/
theorem essSurj_spacesBaseChange_of_isIntegralHom_of_universallyInjective (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.EssSurj where
  mem_essImage C := by
    obtain ⟨P⟩ := nonempty_liftedEtalePresentation_of_isIntegralHom_of_universallyInjective B S hS
      f hint hui hsurj C
    exact exists_iso_functor_obj_of_liftedEtalePresentation B S hS P

/-- For every integral, universally injective and surjective morphism `f` of algebraic spaces over
`S`, base change `V ↦ X ×_Y V` is an equivalence from the spaces-étale site of `Y` to that of
`X`. -/
@[stacks 05ZH "the equivalence at the tag's own class: integral, universally injective and \
surjective"]
theorem isEquivalence_spacesBaseChange_of_isIntegralHom_of_universallyInjective (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.IsEquivalence :=
  let := full_spacesBaseChange_of_isIntegralHom_of_universallyInjective B S hS f hint hui hsurj
  let := faithful_spacesBaseChange_of_isIntegralHom_of_universallyInjective B S hS f hint hui
    hsurj
  let := essSurj_spacesBaseChange_of_isIntegralHom_of_universallyInjective B S hS f hint
    hui hsurj
  ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Space

end

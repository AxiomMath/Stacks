module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemPresentationCriterion

/-!
# Higher direct images along a limit: the degree zero case

Let `I` be a directed set, let `g_i : X_i ⟶ S_i` be an inverse system of quasi-compact and
quasi-separated morphisms of schemes with affine transition morphisms on both sides, with limit
`g : X ⟶ S`, and let `(F_i, φ_{i'i})` be a system of abelian sheaves on the `X_i` with
`𝓕 = colim f_i⁻¹F_i`. This file proves the degree zero case of [Stacks, Tag 0EYM]:
`g_* 𝓕 = colim_i h_i⁻¹ g_{i, *} F_i`, for the maps of the source (the base change maps followed
by the maps of the system), read in degree zero of the higher direct images.

## Main results

* `Stacks.EtaleCohomology.smallEtaleAdjunctionAb_homEquiv_baseChangeAb` — the adjoint of a base
  change map followed by a direct image.
* `Stacks.EtaleCohomology.pushforward_pushforwardMap_comp_squareIso` — for a commutative cube of
  schemes, the direct image along `γ₀` of the pushed-forward adjoint of a map `φ'⁻¹A ⟶ B`
  corresponds, through the comparisons of composite direct images, to the pushed-forward adjoint
  of its base change map followed by its direct image.
* `Stacks.EtaleCohomology.pushforward_pushforwardMap_comp_squareIso_rightDerived` — the same,
  read through the identification of the direct images with their degree zero right derived
  functors.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_zero` — the degree
  zero case of [Stacks, Tag 0EYM].

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Square

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The adjoint of a base change map followed by a direct image.** For the commutative square
`h ≫ f' = e ≫ g` and a map `ι : e⁻¹A ⟶ B`, the map `A_g ⟶ f'_* h_* B` adjoint to the base change
map `f'⁻¹ g_* A ⟶ h_* e⁻¹ A` followed by `h_* ι` is `g_*` of the adjoint of `ι` followed by the
comparison `g_* e_* ≅ f'_* h_*` of the two composite direct images. -/
theorem smallEtaleAdjunctionAb_homEquiv_baseChangeAb {A : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    {B : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (ι : (smallEtalePullbackAb e).obj A ⟶ B) :
    (smallEtaleAdjunctionAb f').homEquiv _ _
        ((smallEtaleBaseChangeAb f' g h e w).app A ≫ (smallEtalePushforwardAb h).map ι) =
      (smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).homEquiv _ _ ι) ≫
        (smallEtaleSquarePushforwardIso f' g h e w).hom.app B := by
  have hu : (smallEtaleAdjunctionAb f').unit.app ((smallEtalePushforwardAb g).obj A) ≫
      (smallEtalePushforwardAb f').map ((smallEtaleBaseChangeAb f' g h e w).app A) =
      (smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app A) ≫
        (smallEtaleSquarePushforwardIso f' g h e w).hom.app ((smallEtalePullbackAb e).obj A) := by
    have h₀ := unit_mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')
      (TwoSquare.mk _ _ _ _ (smallEtaleBaseChangeAb f' g h e w)) A
    rw [mateEquiv_smallEtaleBaseChangeAb] at h₀
    exact h₀.symm
  have hn : (smallEtalePushforwardAb g).map ((smallEtalePushforwardAb e).map ι) ≫
      (smallEtaleSquarePushforwardIso f' g h e w).hom.app B =
      (smallEtaleSquarePushforwardIso f' g h e w).hom.app ((smallEtalePullbackAb e).obj A) ≫
        (smallEtalePushforwardAb f').map ((smallEtalePushforwardAb h).map ι) :=
    (smallEtaleSquarePushforwardIso f' g h e w).hom.naturality ι
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Category.assoc, hn, ← Category.assoc, ← Category.assoc, hu]

end Square

section Cube

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (γ₀ : X₀ ⟶ S₀) (γ₁ : X₁ ⟶ S₁) (γ₂ : X₂ ⟶ S₂)
  (φ : X₁ ⟶ X₀) (χ : S₁ ⟶ S₀) (φ' : X₂ ⟶ X₁) (χ' : S₂ ⟶ S₁) (φ'' : X₂ ⟶ X₀) (χ'' : S₂ ⟶ S₀)
  (hφ : φ'' = φ' ≫ φ) (hχ : χ'' = χ' ≫ χ) (w₁ : γ₁ ≫ χ = φ ≫ γ₀) (w₂ : γ₂ ≫ χ' = φ' ≫ γ₁)
  (w₃ : γ₂ ≫ χ'' = φ'' ≫ γ₀)

variable {A : Sheaf (smallEtaleTopology X₁) Ab.{u + 1}}
  {B : Sheaf (smallEtaleTopology X₂) Ab.{u + 1}}
  (ι : (smallEtalePullbackAb φ').obj A ⟶ B)

include hφ hχ in
/-- **Base change of a pushed-forward adjoint.** Consider two commutative squares
`γ₁ ≫ χ = φ ≫ γ₀` and `γ₂ ≫ χ' = φ' ≫ γ₁` with composite `γ₂ ≫ χ'' = φ'' ≫ γ₀`, where
`φ'' = φ' ≫ φ` and `χ'' = χ' ≫ χ`, and let `ι : φ'⁻¹A ⟶ B`. The direct image along `γ₀` of
the map `φ_* A ⟶ φ''_* B` given by the adjoint of `ι` corresponds, through the comparisons of the
two squares, to the map `χ_* γ₁_* A ⟶ χ''_* γ₂_* B` given by the adjoint of the base change map
of the square `γ₂ ≫ χ' = φ' ≫ γ₁` followed by `γ₂_* ι`. -/
theorem pushforward_pushforwardMap_comp_squareIso :
    (smallEtalePushforwardAb γ₀).map
          ((smallEtalePushforwardAb φ).map ((smallEtaleAdjunctionAb φ').homEquiv _ _ ι) ≫
            (smallEtalePushforwardAbComp' φ' φ φ'' hφ).hom.app B) ≫
        (smallEtaleSquarePushforwardIso χ'' γ₀ γ₂ φ'' w₃).hom.app B =
      (smallEtaleSquarePushforwardIso χ γ₀ γ₁ φ w₁).hom.app A ≫
        (smallEtalePushforwardAb χ).map ((smallEtaleAdjunctionAb χ').homEquiv _ _
            ((smallEtaleBaseChangeAb χ' γ₁ γ₂ φ' w₂).app A ≫
              (smallEtalePushforwardAb γ₂).map ι)) ≫
          (smallEtalePushforwardAbComp' χ' χ χ'' hχ).hom.app
            ((smallEtalePushforwardAb γ₂).obj B) := by
  subst hφ hχ
  have hP := smallEtaleSquarePushforwardIso_paste_app γ₀ γ₁ γ₂ χ χ' φ φ' w₁ w₂ B
  have hn : (smallEtalePushforwardAb γ₀).map
        ((smallEtalePushforwardAb φ).map ((smallEtaleAdjunctionAb φ').homEquiv _ _ ι)) ≫
        (smallEtaleSquarePushforwardIso χ γ₀ γ₁ φ w₁).hom.app ((smallEtalePushforwardAb φ').obj B) =
      (smallEtaleSquarePushforwardIso χ γ₀ γ₁ φ w₁).hom.app A ≫
        (smallEtalePushforwardAb χ).map
          ((smallEtalePushforwardAb γ₁).map ((smallEtaleAdjunctionAb φ').homEquiv _ _ ι)) :=
    (smallEtaleSquarePushforwardIso χ γ₀ γ₁ φ w₁).hom.naturality
      ((smallEtaleAdjunctionAb φ').homEquiv _ _ ι)
  have hid : (smallEtalePushforwardAb γ₀).map
        ((smallEtalePushforwardAbComp' φ' φ (φ' ≫ φ) rfl).hom.app B) ≫
      (smallEtalePushforwardAb γ₀).map
        ((smallEtalePushforwardAbComp' φ' φ (φ' ≫ φ) rfl).inv.app B) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact (smallEtalePushforwardAb γ₀).map_id _
  rw [smallEtaleAdjunctionAb_homEquiv_baseChangeAb, hP,
    (smallEtalePushforwardAb γ₀).map_comp, Category.assoc, reassoc_of% hid, reassoc_of% hn,
    (smallEtalePushforwardAb χ).map_comp, Category.assoc]

include hφ hχ in
/-- **Base change of a pushed-forward adjoint, in degree zero of the higher direct images.**
`pushforward_pushforwardMap_comp_squareIso` with the base change map of the square
`γ₂ ≫ χ' = φ' ≫ γ₁` replaced by the base change map on higher direct images in degree zero,
`Stacks.EtaleCohomology.higherBaseChangeMapAb`, read through the identifications
`Stacks.EtaleCohomology.LimitHigherDirectImage.directImageZeroIso` of the direct images with
their degree zero right derived functors. -/
theorem pushforward_pushforwardMap_comp_squareIso_rightDerived :
    (smallEtalePushforwardAb γ₀).map
          ((smallEtalePushforwardAb φ).map ((smallEtaleAdjunctionAb φ').homEquiv _ _ ι) ≫
            (smallEtalePushforwardAbComp' φ' φ φ'' hφ).hom.app B) ≫
        (smallEtaleSquarePushforwardIso χ'' γ₀ γ₂ φ'' w₃).hom.app B ≫
          (smallEtalePushforwardAb χ'').map (LimitHigherDirectImage.directImageZeroIso γ₂ B).hom =
      (smallEtaleSquarePushforwardIso χ γ₀ γ₁ φ w₁).hom.app A ≫
        (smallEtalePushforwardAb χ).map (LimitHigherDirectImage.directImageZeroIso γ₁ A).hom ≫
          (smallEtalePushforwardAb χ).map ((smallEtaleAdjunctionAb χ').homEquiv _ _
              ((higherBaseChangeMapAb χ' γ₁ γ₂ φ' w₂ 0).app A ≫
                ((smallEtalePushforwardAb γ₂).rightDerived 0).map ι)) ≫
            (smallEtalePushforwardAbComp' χ' χ χ'' hχ).hom.app
              (((smallEtalePushforwardAb γ₂).rightDerived 0).obj B) := by
  have hbc := map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero χ' γ₁ γ₂ φ' w₂ A
  rw [← LimitHigherDirectImage.directImageZeroIso_hom,
    ← LimitHigherDirectImage.directImageZeroIso_hom] at hbc
  have hadj : (LimitHigherDirectImage.directImageZeroIso γ₁ A).hom ≫
      (smallEtaleAdjunctionAb χ').homEquiv _ _
        ((higherBaseChangeMapAb χ' γ₁ γ₂ φ' w₂ 0).app A ≫
          ((smallEtalePushforwardAb γ₂).rightDerived 0).map ι) =
      (smallEtaleAdjunctionAb χ').homEquiv _ _
          ((smallEtaleBaseChangeAb χ' γ₁ γ₂ φ' w₂).app A ≫ (smallEtalePushforwardAb γ₂).map ι) ≫
        (smallEtalePushforwardAb χ').map (LimitHigherDirectImage.directImageZeroIso γ₂ B).hom := by
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right,
      ← Category.assoc, hbc, Category.assoc, Category.assoc,
      LimitHigherDirectImage.directImageZeroIso_hom_naturality]
  have hn := (smallEtalePushforwardAbComp' χ' χ χ'' hχ).hom.naturality
    (LimitHigherDirectImage.directImageZeroIso γ₂ B).hom
  simp only [Functor.comp_map] at hn
  rw [← (smallEtalePushforwardAb χ).map_comp_assoc, hadj, (smallEtalePushforwardAb χ).map_comp,
    Category.assoc, hn, ← reassoc_of% (pushforward_pushforwardMap_comp_squareIso γ₀ γ₁ γ₂ φ χ φ'
      χ' φ'' χ'' hφ hχ w₁ w₂ w₃ ι)]

end Cube

namespace LimitHigherDirectImage

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS)

include hcX in
/-- **The degree zero case of [Stacks, Tag 0EYM].** Let `g_i : X_i ⟶ S_i` be quasi-compact and
quasi-separated with affine transition morphisms, `g` the limit morphism, and `ι_i : f_i⁻¹F_i ⟶ 𝓕`
present `𝓕 = colim f_i⁻¹F_i`. Then the maps `ψ_i : h_i⁻¹R⁰g_{i, *}F_i ⟶ R⁰g_*𝓕` of
`Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap` present
`R⁰g_*𝓕 = colim h_i⁻¹R⁰g_{i, *}F_i`. -/
theorem isHigherDirectImageColimit_zero (F : EtaleSheafSystem DX Ab.{u + 1})
    {𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : IsPullbackCocone cX F ι) (hpres : IsPullbackColimitPresentation cX 𝓕 F ι) :
    IsHigherDirectImageColimit γ 0 cX cS hcS 𝓕 F ι := by
  let g := limitMorphism γ cX cS hcS
  let F' := higherDirectImageSystem γ 0 F
  let ψ := projectionMap γ cX cS hcS 0 𝓕 F ι
  have hψ : IsPullbackCocone cS F' ψ := fun {i j} a => by
    refine projectionMap_cocone γ 0 cX cS hcS 𝓕 F ι a ?_
    rw [← hι a, Iso.hom_inv_id_app_assoc]
  let Φ : ∀ i₀ : Iᵒᵖ, (smallEtalePushforwardAb (γ.app i₀)).obj
      ((smallEtalePushforwardAb (cX.π.app i₀)).obj 𝓕) ≅
        (smallEtalePushforwardAb (cS.π.app i₀)).obj
          (((smallEtalePushforwardAb g).rightDerived 0).obj 𝓕) := fun i₀ =>
    (smallEtaleSquarePushforwardIso (cS.π.app i₀) (γ.app i₀) g (cX.π.app i₀)
      (limitMorphism_comp_π γ cX cS hcS i₀)).app 𝓕 ≪≫
      (smallEtalePushforwardAb (cS.π.app i₀)).mapIso (directImageZeroIso g 𝓕)
  let Ψ : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀), (smallEtalePushforwardAb (γ.app i₀)).obj
      ((smallEtalePushforwardAb (DX.map a)).obj (F.obj k)) ≅
        (smallEtalePushforwardAb (DS.map a)).obj (F'.obj k) := fun {k i₀} a =>
    (smallEtaleSquarePushforwardIso (DS.map a) (γ.app i₀) (γ.app k) (DX.map a)
      (transition_comm γ a)).app (F.obj k) ≪≫
      (smallEtalePushforwardAb (DS.map a)).mapIso (directImageZeroIso (γ.app k) (F.obj k))
  have hleg : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀),
      (smallEtalePushforwardAb (γ.app i₀)).map (F.pushforwardLeg cX ι a) ≫ (Φ i₀).hom =
        (Ψ a).hom ≫ F'.pushforwardLeg cS ψ a := fun {k i₀} a => by
    have := pushforward_pushforwardMap_comp_squareIso_rightDerived (γ.app i₀) (γ.app k) g
      (DX.map a) (DS.map a) (cX.π.app k) (cS.π.app k) (cX.π.app i₀) (cS.π.app i₀) (cX.w a).symm
      (cS.w a).symm (transition_comm γ a) (limitMorphism_comp_π γ cX cS hcS k)
      (limitMorphism_comp_π γ cX cS hcS i₀) (ι k)
    simp only [Φ, Ψ, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
      EtaleSheafSystem.pushforwardLeg, Functor.map_comp] at this ⊢
    exact this
  have htr : ∀ {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀),
      (smallEtalePushforwardAb (γ.app i₀)).map (F.pushforwardTransition b a) ≫ (Ψ (b ≫ a)).hom =
        (Ψ a).hom ≫ F'.pushforwardTransition b a := fun {l k i₀} b a => by
    have := pushforward_pushforwardMap_comp_squareIso_rightDerived (γ.app i₀) (γ.app k) (γ.app l)
      (DX.map a) (DS.map a) (DX.map b) (DS.map b) (DX.map (b ≫ a)) (DS.map (b ≫ a))
      (DX.map_comp b a) (DS.map_comp b a) (transition_comm γ a) (transition_comm γ b)
      (transition_comm γ (b ≫ a)) (F.map b)
    simp only [Ψ, Iso.trans_hom, Iso.app_hom, Category.assoc,
      EtaleSheafSystem.pushforwardTransition, Functor.map_comp] at this ⊢
    exact this
  have hleg' : ∀ {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) (V₀ : (DS.obj i₀).Etale)
      (y : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (DX.map a)).obj
        ((smallEtaleBaseChange (γ.app i₀)).obj V₀))))),
      (F'.pushforwardLeg cS ψ a).hom.app (op V₀) ((Ψ a).hom.hom.app (op V₀) y) =
        (Φ i₀).hom.hom.app (op V₀)
          ((F.pushforwardLeg cX ι a).hom.app (op ((smallEtaleBaseChange (γ.app i₀)).obj V₀)) y) :=
    fun a V₀ y => (congrArg (fun φ => φ.hom.app (op V₀) y) (hleg a)).symm
  have htr' : ∀ {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀) (V₀ : (DS.obj i₀).Etale)
      (y : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (DX.map a)).obj
        ((smallEtaleBaseChange (γ.app i₀)).obj V₀))))),
      (F'.pushforwardTransition b a).hom.app (op V₀) ((Ψ a).hom.hom.app (op V₀) y) =
        (Ψ (b ≫ a)).hom.hom.app (op V₀)
          ((F.pushforwardTransition b a).hom.app
            (op ((smallEtaleBaseChange (γ.app i₀)).obj V₀)) y) :=
    fun b a V₀ y => (congrArg (fun φ => φ.hom.app (op V₀) y) (htr b a)).symm
  have hinv : ∀ {Z : Scheme.{u}} {P Q : Sheaf (smallEtaleTopology Z) Ab.{u + 1}} (e : P ≅ Q)
      (V : Z.Etaleᵒᵖ)
      (z : ToType (Q.obj.obj V)), e.hom.hom.app V (e.inv.hom.app V z) = z := fun e V z => by
    change (e.inv ≫ e.hom).hom.app V z = z
    rw [Iso.inv_hom_id]
    rfl
  have hinv' : ∀ {Z : Scheme.{u}} {P Q : Sheaf (smallEtaleTopology Z) Ab.{u + 1}} (e : P ≅ Q)
      (V : Z.Etaleᵒᵖ)
      (z : ToType (P.obj.obj V)), e.inv.hom.app V (e.hom.hom.app V z) = z :=
    fun e V z => hinv e.symm V z
  refine EtaleSheafSystem.isPullbackColimitPresentation_of_forall_exists hcS F' ψ hψ ?_ ?_
  · intro i₀ V₀ _ _ s
    let W₀ := (smallEtaleBaseChange (γ.app i₀)).obj V₀
    have : CompactSpace W₀.left :=
      compactSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    have : QuasiSeparatedSpace W₀.left :=
      quasiSeparatedSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    obtain ⟨k, a, y, hy⟩ := F.exists_pushforwardLeg_apply_eq cX hcX ι hι hpres W₀
      ((Φ i₀).inv.hom.app (op V₀) s)
    refine ⟨k, a, (Ψ a).hom.hom.app (op V₀) y, ?_⟩
    refine (hleg' a V₀ y).trans ?_
    change (Φ i₀).hom.hom.app (op V₀) ((F.pushforwardLeg cX ι a).hom.app (op W₀) y) = s
    rw [hy]
    exact hinv (Φ i₀) (op V₀) s
  · intro i₀ V₀ _ _ k a x hx
    let W₀ := (smallEtaleBaseChange (γ.app i₀)).obj V₀
    have : CompactSpace W₀.left :=
      compactSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    have : QuasiSeparatedSpace W₀.left :=
      quasiSeparatedSpace_smallEtaleBaseChange_obj (γ.app i₀) V₀ inferInstance
    let y := (Ψ a).inv.hom.app (op V₀) x
    have hxy : (Ψ a).hom.hom.app (op V₀) y = x := hinv (Ψ a) (op V₀) x
    have h := hleg' a V₀ y
    rw [hxy, hx] at h
    have hy0 : (F.pushforwardLeg cX ι a).hom.app (op W₀) y = 0 := by
      rw [← hinv' (Φ i₀) (op V₀) ((F.pushforwardLeg cX ι a).hom.app (op W₀) y)]
      change (Φ i₀).inv.hom.app (op V₀) ((Φ i₀).hom.hom.app (op V₀)
        ((F.pushforwardLeg cX ι a).hom.app (op W₀) y)) = 0
      rw [← h, map_zero]
    obtain ⟨l, b, hb⟩ := F.exists_pushforwardTransition_apply_eq_zero cX hcX ι hι hpres W₀ a y
      hy0
    refine ⟨l, b, ?_⟩
    have h2 := htr' b a V₀ y
    rw [hxy] at h2
    refine h2.trans ?_
    change (Ψ (b ≫ a)).hom.hom.app (op V₀) ((F.pushforwardTransition b a).hom.app (op W₀) y) = 0
    rw [hb]
    exact map_zero _

end LimitHigherDirectImage

end Stacks.EtaleCohomology

module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeSmoothBaseChange

/-!
# Relative normalization of an affine morphism

For ring maps `ψ : A ⟶ C` and `χ : C ⟶ B` with `ψ` integral and `χ` injective with image the
integral closure of `A` in `B`, the relative normalization of `Spec B ⟶ Spec A` is `Spec C`: the
morphism `normalizationDesc` to `Spec C` is an isomorphism. A version up to isomorphisms of the
source and the intermediate scheme is also given.

## Main results

* `AlgebraicGeometry.TameCovers.isIso_normalizationDesc_specMap`.
* `AlgebraicGeometry.TameCovers.isIso_normalizationDesc_of_iso_specMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TameCovers

/-- **The relative normalization of `Spec B ⟶ Spec A` is `Spec` of the integral closure.** If
`ψ : A ⟶ C` is integral and `χ : C ⟶ B` is injective with every element of `B` integral over `A`
in its image, then the canonical morphism from the relative normalization of `Spec B ⟶ Spec A` to
`Spec C` is an isomorphism. -/
theorem isIso_normalizationDesc_specMap {A C B : CommRingCat.{u}} (ψ : A ⟶ C) (χ : C ⟶ B)
    [IsIntegralHom (Spec.map ψ)] (hχ : Function.Injective χ)
    (hcl : ∀ b : B, (ψ ≫ χ).hom.IsIntegralElem b → ∃ c, χ c = b) :
    IsIso ((Spec.map (ψ ≫ χ)).normalizationDesc (Spec.map χ) (Spec.map ψ)
      (Spec.map_comp ψ χ)) := by
  set p := Spec.map (ψ ≫ χ)
  set n := p.normalizationDesc (Spec.map χ) (Spec.map ψ) (Spec.map_comp ψ χ) with hn
  have : IsAffine p.normalization := isAffine_of_isAffineHom p.fromNormalization
  suffices h : IsIso n.appTop by
    have hnat := Scheme.isoSpec_inv_naturality n
    have : n = p.normalization.isoSpec.hom ≫ (Spec.map n.appTop ≫ (Spec C).isoSpec.inv) := by
      rw [hnat, Iso.hom_inv_id_assoc]
    rw [this]; infer_instance
  let U : (Spec A).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let : Algebra Γ(Spec A, U.1) Γ(Spec B, p ⁻¹ᵁ U.1) := (p.app U.1).hom.toAlgebra
  let O := p.normalizationObjIso U.2
  have hW : p.fromNormalization ⁻¹ᵁ U.1 = ⊤ := Scheme.Hom.preimage_top _
  have hWle : p.fromNormalization ⁻¹ᵁ U.1 ≤ n ⁻¹ᵁ ⊤ := by simp
  let ρ₀ := n.appLE ⊤ (p.fromNormalization ⁻¹ᵁ U.1) hWle
  let ρ := ρ₀ ≫ O.hom
  suffices h : IsIso ρ by
    have hρ₀ : IsIso ρ₀ := by
      rw [show ρ₀ = ρ ≫ O.inv by simp only [ρ, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
      infer_instance
    have hle' : n ⁻¹ᵁ ⊤ ≤ p.fromNormalization ⁻¹ᵁ U.1 := by rw [hW]; exact le_top
    have hiso : IsIso (homOfLE hWle).op :=
      ⟨(homOfLE hle').op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    have : IsIso (p.normalization.presheaf.map (homOfLE hWle).op) :=
      Functor.map_isIso p.normalization.presheaf (homOfLE hWle).op
    have hcomp : ρ₀ = n.appTop ≫ p.normalization.presheaf.map (homOfLE hWle).op := rfl
    rw [hcomp] at hρ₀
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ n.appTop _ this hρ₀
  have hval : ρ ≫
      CommRingCat.ofHom (integralClosure Γ(Spec A, U.1) Γ(Spec B, p ⁻¹ᵁ U.1)).val.toRingHom =
      (Spec.map χ).appLE ⊤ (p ⁻¹ᵁ U.1) (by simp) := by
    simp only [ρ, ρ₀, Category.assoc]
    rw [p.normalizationObjIso_hom_val U.2, Scheme.Hom.appLE_comp_appLE]
    simp only [hn, Scheme.Hom.toNormalization_normalizationDesc]
  have hχle : (Spec.map χ).appLE ⊤ (p ⁻¹ᵁ U.1) (by simp) =
      (Scheme.ΓSpecIso C).hom ≫ χ ≫ (Scheme.ΓSpecIso B).inv := by
    change (Spec.map χ).appLE ⊤ ((Spec.map χ) ⁻¹ᵁ ⊤) le_rfl = _
    rw [Scheme.Hom.appLE_eq_app]
    change (Spec.map χ).appTop = _
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  have hρ : ∀ c, ((ρ c : integralClosure Γ(Spec A, U.1) Γ(Spec B, p ⁻¹ᵁ U.1)) :
      Γ(Spec B, p ⁻¹ᵁ U.1)) = (Scheme.ΓSpecIso B).inv (χ ((Scheme.ΓSpecIso C).hom c)) := by
    intro c
    have := congrArg (fun g => g.hom c) (hval.trans hχle)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun c c' hcc => ?_, fun z => ?_⟩
  · have h1 := congrArg Subtype.val hcc
    change ((ρ c : integralClosure Γ(Spec A, U.1) Γ(Spec B, p ⁻¹ᵁ U.1)) :
      Γ(Spec B, p ⁻¹ᵁ U.1)) = ρ c' at h1
    rw [hρ, hρ] at h1
    exact (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv.injective
      (hχ ((Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.symm.injective h1))
  · let : Algebra A B := (ψ ≫ χ).hom.toAlgebra
    have hint : _root_.IsIntegral A ((Scheme.ΓSpecIso B).hom (z : Γ(Spec B, p ⁻¹ᵁ U.1))) :=
      @IsIntegral.map_of_comp_eq Γ(Spec A, U.1) Γ(Spec B, p ⁻¹ᵁ U.1) A B _ _ _ _
        (p.app U.1).hom.toAlgebra (ψ ≫ χ).hom.toAlgebra (Scheme.ΓSpecIso A).hom.hom
        (Scheme.ΓSpecIso B).hom.hom
        (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (ψ ≫ χ))).symm _ z.2
    obtain ⟨c, hc⟩ := hcl _ hint
    refine ⟨(Scheme.ΓSpecIso C).inv c, Subtype.ext ?_⟩
    change ((ρ _ : integralClosure Γ(Spec A, U.1) Γ(Spec B, p ⁻¹ᵁ U.1)) :
      Γ(Spec B, p ⁻¹ᵁ U.1)) = z
    rw [hρ, Iso.inv_hom_id_apply, hc]
    exact (Scheme.ΓSpecIso B).hom_inv_id_apply _

/-- **Up to isomorphism.** Let `p = h ≫ q : W ⟶ T ⟶ Spec A` with `q` integral, and suppose that,
along isomorphisms `W ≅ Spec B` and `T ≅ Spec C`, the morphisms `h` and `q` are `Spec χ` and
`Spec ψ` for ring maps as in `isIso_normalizationDesc_specMap`. Then the canonical morphism from
the relative normalization of `p` to `T` is an isomorphism. -/
theorem isIso_normalizationDesc_of_iso_specMap {W T : Scheme.{u}} {A C B : CommRingCat.{u}}
    (ψ : A ⟶ C) (χ : C ⟶ B) [IsIntegralHom (Spec.map ψ)] (hχ : Function.Injective χ)
    (hcl : ∀ b : B, (ψ ≫ χ).hom.IsIntegralElem b → ∃ c, χ c = b)
    (u : W ≅ Spec B) (v : T ≅ Spec C) (h : W ⟶ T) (q : T ⟶ Spec A) [IsIntegralHom q]
    (p : W ⟶ Spec A) [QuasiCompact p] [QuasiSeparated p]
    (hh : h ≫ v.hom = u.hom ≫ Spec.map χ) (hq : v.hom ≫ Spec.map ψ = q) (H : p = h ≫ q) :
    IsIso (p.normalizationDesc h q H) := by
  let P := Spec.map (ψ ≫ χ)
  let n₀ := P.normalizationDesc (Spec.map χ) (Spec.map ψ) (Spec.map_comp ψ χ)
  have hn₀ : IsIso n₀ := isIso_normalizationDesc_specMap ψ χ hχ hcl
  have hh' : h = u.hom ≫ Spec.map χ ≫ v.inv := by
    rw [← Category.assoc, ← hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hp : u.hom ≫ P = p ≫ 𝟙 _ := by
    rw [Category.comp_id, H, ← hq, hh']
    simp only [P, Spec.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  let m := Scheme.Hom.normalizationMap P p u.hom (𝟙 _) hp
  have hm : IsIso m := Scheme.Hom.isIso_normalizationMap P p u.hom (𝟙 _) hp
  have heq : p.normalizationDesc h q H = m ≫ n₀ ≫ v.inv := by
    apply Scheme.Hom.normalization.hom_ext (f := p) _ _ q
    · rw [Scheme.Hom.toNormalization_normalizationDesc, ← Category.assoc,
        Scheme.Hom.toNormalization_normalizationMap, Category.assoc, ← Category.assoc _ n₀,
        Scheme.Hom.toNormalization_normalizationDesc, hh']
    · exact Scheme.Hom.normalizationDesc_comp _ _ _ _
    · rw [Category.assoc, Category.assoc, ← hq, Iso.inv_hom_id_assoc,
        Scheme.Hom.normalizationDesc_comp, Scheme.Hom.normalizationMap_fromNormalization,
        Category.comp_id]
  rw [heq]
  infer_instance

end AlgebraicGeometry.TameCovers

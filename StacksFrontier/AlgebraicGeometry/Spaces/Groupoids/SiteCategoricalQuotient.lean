module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct

/-!
# Categorical quotients among the objects of the big fppf site, and uniqueness in algebraic spaces

Let `s, t : R ⟶ U` be two morphisms of the big fppf site of `S` and `φ : U ⟶ M` a morphism which
coequalizes them and through which every morphism out of `U` to an object of the site which
coequalizes them factors uniquely. This file shows that `φ` is then an epimorphism *against
algebraic spaces*: two morphisms `M ⟶ Y` to an algebraic space which agree after `φ` are equal.
This is the uniqueness half of the proof of Stacks 0DUR.

The argument replaces the equalizer of the source with the fibre product of `M ⟶ Y × Y` and the
diagonal of `Y`, which is an object `E` of the site because the diagonal of an algebraic space is
representable. The morphism `φ` factors through `E`, the factorization coequalizes `s` and `t`,
so it descends to `M`, and the descent is a section of `E ⟶ M`; on `E` the two morphisms agree.

## Main definitions

* `AlgebraicGeometry.Space.IsSiteCategoricalQuotient`: the universal property against the objects
  of the site.

## Main results

* `AlgebraicGeometry.Space.IsSiteCategoricalQuotient.of_scheme`: the universal property against
  all schemes gives the one against the objects of the site.
* `AlgebraicGeometry.Space.IsSiteCategoricalQuotient.hom_ext`: uniqueness against algebraic
  spaces.
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism `φ : U ⟶ M` of the big fppf site of `S` is a *categorical quotient of `s, t` among
the objects of the site* when it coequalizes `s` and `t` and every morphism from `U` to an object
of the site which coequalizes them factors uniquely through it. -/
def IsSiteCategoricalQuotient {U R M : BigFppfOver B S hS} (s t : R ⟶ U) (φ : U ⟶ M) : Prop :=
  s ≫ φ = t ≫ φ ∧
    ∀ (E : BigFppfOver B S hS) (ℓ : U ⟶ E), s ≫ ℓ = t ≫ ℓ → ∃! κ : M ⟶ E, φ ≫ κ = ℓ

namespace IsSiteCategoricalQuotient

variable {U R M : BigFppfOver B S hS} {s t : R ⟶ U} {φ : U ⟶ M}

/-- **The universal property against all schemes gives the one against the site.** A morphism
of the site whose underlying morphism of schemes is a categorical quotient of the underlying
morphisms of schemes in the category of all schemes is a categorical quotient among the objects
of the site: the factorization through an object of the site is compatible with the structure
morphisms to `S` by the uniqueness of the factorization of the structure morphism of `U`. -/
theorem of_scheme (hinv : s ≫ φ = t ≫ φ)
    (h : ∀ (E : Scheme.{u}) (ℓ : (BigFppfOver.toScheme B S hS).obj U ⟶ E),
      (BigFppfOver.toScheme B S hS).map s ≫ ℓ = (BigFppfOver.toScheme B S hS).map t ≫ ℓ →
        ∃! κ : (BigFppfOver.toScheme B S hS).obj M ⟶ E,
          (BigFppfOver.toScheme B S hS).map φ ≫ κ = ℓ) :
    IsSiteCategoricalQuotient s t φ := by
  refine ⟨hinv, fun E ℓ hℓ => ?_⟩
  obtain ⟨κ₀, hκ₀, hu⟩ := h _ _ <| by
    simpa only [Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map hℓ
  obtain ⟨κU, -, hU⟩ := h _ (B.inclusion.map U.hom)
    ((BigFppfOver.toScheme_map_comp_hom s).trans (BigFppfOver.toScheme_map_comp_hom t).symm)
  have hκS : κ₀ ≫ B.inclusion.map E.hom = B.inclusion.map M.hom := by
    refine (hU _ ?_).trans (hU _ (BigFppfOver.toScheme_map_comp_hom φ)).symm
    dsimp only
    rw [← Category.assoc, hκ₀, BigFppfOver.toScheme_map_comp_hom ℓ]
  refine ⟨BigFppfOver.homOfCompEq B S hS κ₀ hκS, ?_, fun κ hκ => ?_⟩
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq, hκ₀]
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [BigFppfOver.toScheme_map_homOfCompEq]
    refine hu _ ?_
    dsimp only
    rw [← Functor.map_comp, hκ]

/-- A categorical quotient among the objects of the site is an epimorphism of the site. -/
theorem epi (hφ : IsSiteCategoricalQuotient s t φ) {E : BigFppfOver B S hS} {κ₁ κ₂ : M ⟶ E}
    (h : φ ≫ κ₁ = φ ≫ κ₂) : κ₁ = κ₂ := by
  obtain ⟨κ, -, hu⟩ := hφ.2 E (φ ≫ κ₁) (by rw [← Category.assoc, hφ.1, Category.assoc])
  exact (hu κ₁ rfl).trans (hu κ₂ h.symm).symm

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site needs more heartbeats
/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_SiteCategoricalQuotient
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- **Uniqueness against algebraic spaces.** Two morphisms from the presheaf represented by `M`
to an algebraic space which agree after `φ` are equal, as soon as `φ` is a categorical quotient
among the objects of the site. -/
theorem hom_ext (hφ : IsSiteCategoricalQuotient s t φ) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {h₁ h₂ : yoneda.obj M ⟶ Y}
    (h : yoneda.map φ ≫ h₁ = yoneda.map φ ≫ h₂) : h₁ = h₂ := by
  have hd := hY.diagonal_representable
  let g : yoneda.obj M ⟶ Y ⨯ Y := prod.lift h₁ h₂
  have hi : (yoneda.map φ ≫ h₁) ≫ diag Y = yoneda.map φ ≫ g := by
    ext <;> simp [g, h]
  let ℓ : U ⟶ hd.pullback g := hd.lift (yoneda.map φ ≫ h₁) φ hi
  have hℓs : ℓ ≫ hd.snd g = φ := hd.lift_snd _ _ _
  have hℓf : yoneda.map ℓ ≫ hd.fst g = yoneda.map φ ≫ h₁ := hd.lift_fst _ _ _
  have hinv : s ≫ ℓ = t ≫ ℓ := by
    refine hd.hom_ext ?_ ?_
    · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hℓf,
        ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hφ.1]
    · rw [Category.assoc, Category.assoc, hℓs, hφ.1]
  obtain ⟨κ, hκ, -⟩ := hφ.2 _ ℓ hinv
  have hsec : κ ≫ hd.snd g = 𝟙 M :=
    hφ.epi (by rw [← Category.assoc, hκ, hℓs, Category.comp_id])
  have hw := hd.w g
  have h₁' : yoneda.map (hd.snd g) ≫ h₁ = hd.fst g := by
    simpa [g] using (congrArg (· ≫ prod.fst) hw).symm
  have h₂' : yoneda.map (hd.snd g) ≫ h₂ = hd.fst g := by
    simpa [g] using (congrArg (· ≫ prod.snd) hw).symm
  calc h₁ = yoneda.map (κ ≫ hd.snd g) ≫ h₁ := by rw [hsec, yoneda.map_id, Category.id_comp]
    _ = yoneda.map κ ≫ hd.fst g := by rw [Functor.map_comp, Category.assoc, h₁']
    _ = yoneda.map (κ ≫ hd.snd g) ≫ h₂ := by rw [Functor.map_comp, Category.assoc, h₂']
    _ = h₂ := by rw [hsec, yoneda.map_id, Category.id_comp]

end IsSiteCategoricalQuotient

end AlgebraicGeometry.Space

end

end

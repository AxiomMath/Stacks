module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardSectionRigidity
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackRigidification
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackRestrictIso

/-!
# Isomorphisms of invertible modules normalised along the section

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` with a section
`σ : B ⟶ X`, the standing data of Stacks 0D28.  The proof of Stacks 0D28 normalises every
isomorphism of invertible modules it chooses on a base change `X_V` by its pullback along the
induced section `σ_V : V ⟶ X_V`: given trivialisations `α_i` along the sections of the modules
compared, an isomorphism `φ` is *normalised* when `σ_V^*φ` carries one trivialisation to the
other.  When `𝒪_V ⟶ f_{V, *}𝒪_{X_V}` is an isomorphism, a normalised isomorphism exists as soon
as some isomorphism does, and it is unique: this is the rescaling by `u_{ij}^{-1}` in the source,
and the reason the functions `f_{ijk}` of its cocycle are `1`.

This file sets up that notion and its calculus.  The trivialisations take values in the inverse
images of one fixed module `R` on an algebraic space `Y` (in the application, `𝒪_{X_T}` on the
base change to the target test scheme), along morphisms `r_i` from the test schemes, so that
trivialisations on different test schemes can be compared.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.IsNormalized`: an isomorphism
  `ψ : (X_{a₁})^*L₁ ≅ (X_{a₂})^*L₂` on `X_V` is normalised for trivialisations `α₁`, `α₂` of
  `L₁`, `L₂` along the sections.

## Main results

* `AlgebraicGeometry.Space.PicardSituation.IsNormalized.eq`: two normalised isomorphisms agree.
* `AlgebraicGeometry.Space.PicardSituation.exists_isNormalized`: a normalised isomorphism exists
  as soon as an isomorphism does.
* `AlgebraicGeometry.Space.PicardSituation.IsNormalized.restrict`: the restriction of a
  normalised isomorphism along a morphism of test schemes is normalised.
* `AlgebraicGeometry.Space.PicardSituation.IsNormalized.trans` and
  `AlgebraicGeometry.Space.PicardSituation.IsNormalized.symm`: normalised isomorphisms compose
  and invert.

## References

* [Stacks Project, Tag 0D28](https://stacks.math.columbia.edu/tag/0D28)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- A functor which is bijective on the homomorphisms between two objects in both directions and
injective on their endomorphisms lifts every isomorphism between their images. -/
theorem exists_mapIso_eq (G : C ⥤ D) {P Q : C}
    (h₁ : Function.Surjective (fun φ : P ⟶ Q ↦ G.map φ))
    (h₂ : Function.Surjective (fun φ : Q ⟶ P ↦ G.map φ))
    (h₃ : Function.Injective (fun φ : P ⟶ P ↦ G.map φ))
    (h₄ : Function.Injective (fun φ : Q ⟶ Q ↦ G.map φ)) (τ : G.obj P ≅ G.obj Q) :
    ∃ ψ : P ≅ Q, G.mapIso ψ = τ := by
  obtain ⟨φ, hφ⟩ := h₁ τ.hom
  obtain ⟨φ', hφ'⟩ := h₂ τ.inv
  simp only at hφ hφ'
  refine ⟨⟨φ, φ', h₃ ?_, h₄ ?_⟩, Iso.ext hφ⟩
  · simp only [Functor.map_comp, hφ, hφ', Iso.hom_inv_id, Functor.map_id]
  · simp only [Functor.map_comp, hφ, hφ', Iso.inv_hom_id, Functor.map_id]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.PicardSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)

/-- The section square `g ≫ σ_T = σ_U ≫ X_g`, in the orientation the restrictions use. -/
theorem spaceMap_comp_baseChangeSection {U T : s.SchemesOver} (g : U ⟶ T) :
    spaceMap g ≫ baseChangeSection σ hσ T = baseChangeSection σ hσ U ≫ baseChangeMap s.f g :=
  (baseChangeSection_naturality σ hσ g).symm

/-- The underlying morphism of a composite of test schemes is the composite. -/
theorem spaceMap_comp {V U T : s.SchemesOver} (k : V ⟶ U) (g : U ⟶ T) :
    spaceMap (k ≫ g) = spaceMap k ≫ spaceMap g := by
  simp [spaceMap, CostructuredArrow.comp_left]

variable {Y : AlgebraicSpaces B S hS} (R : Modules.{u, u} B S hS Y.1 Y.2)

/-- **A normalised isomorphism.**  Let `L₁`, `L₂` be modules on the base changes `X_{U₁}`,
`X_{U₂}`, with trivialisations `α_k : σ_{U_k}^*L_k ≅ r_k^*R` along the sections, valued in the
inverse images of a fixed module `R`.  For morphisms of test schemes `a_k : V ⟶ U_k` whose
composites with the `r_k` agree with `w`, an isomorphism `ψ : (X_{a₁})^*L₁ ≅ (X_{a₂})^*L₂` is
*normalised* when `σ_V^*ψ`, followed by the restriction of `α₂`, is the restriction of `α₁`. -/
def IsNormalized {U₁ U₂ V : s.SchemesOver}
    {L₁ : Modules.{u, u} B S hS (s.baseChange U₁).1 (s.baseChange U₁).2}
    {L₂ : Modules.{u, u} B S hS (s.baseChange U₂).1 (s.baseChange U₂).2}
    {r₁ : s.baseSpaceAt U₁ ⟶ Y} {r₂ : s.baseSpaceAt U₂ ⟶ Y}
    (α₁ : (modulePullback B S hS (baseChangeSection σ hσ U₁)).obj L₁ ≅
      (modulePullback B S hS r₁).obj R)
    (α₂ : (modulePullback B S hS (baseChangeSection σ hσ U₂)).obj L₂ ≅
      (modulePullback B S hS r₂).obj R)
    (a₁ : V ⟶ U₁) (a₂ : V ⟶ U₂) (w : s.baseSpaceAt V ⟶ Y) (hw₁ : spaceMap a₁ ≫ r₁ = w)
    (hw₂ : spaceMap a₂ ≫ r₂ = w)
    (ψ : (modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁ ≅
      (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂) : Prop :=
  restrictPullbackIso (baseChangeSection σ hσ V) rfl rfl ψ ≪≫
      restrictPullbackIso (spaceMap a₂) (spaceMap_comp_baseChangeSection σ hσ a₂) hw₂ α₂ =
    restrictPullbackIso (spaceMap a₁) (spaceMap_comp_baseChangeSection σ hσ a₁) hw₁ α₁

variable {R}

section Calculus

variable {U₁ U₂ U₃ V : s.SchemesOver}
    {L₁ : Modules.{u, u} B S hS (s.baseChange U₁).1 (s.baseChange U₁).2}
    {L₂ : Modules.{u, u} B S hS (s.baseChange U₂).1 (s.baseChange U₂).2}
    {L₃ : Modules.{u, u} B S hS (s.baseChange U₃).1 (s.baseChange U₃).2}
    {r₁ : s.baseSpaceAt U₁ ⟶ Y} {r₂ : s.baseSpaceAt U₂ ⟶ Y} {r₃ : s.baseSpaceAt U₃ ⟶ Y}
    {α₁ : (modulePullback B S hS (baseChangeSection σ hσ U₁)).obj L₁ ≅
      (modulePullback B S hS r₁).obj R}
    {α₂ : (modulePullback B S hS (baseChangeSection σ hσ U₂)).obj L₂ ≅
      (modulePullback B S hS r₂).obj R}
    {α₃ : (modulePullback B S hS (baseChangeSection σ hσ U₃)).obj L₃ ≅
      (modulePullback B S hS r₃).obj R}
    {a₁ : V ⟶ U₁} {a₂ : V ⟶ U₂} {a₃ : V ⟶ U₃} {w : s.baseSpaceAt V ⟶ Y}
    {hw₁ : spaceMap a₁ ≫ r₁ = w} {hw₂ : spaceMap a₂ ≫ r₂ = w} {hw₃ : spaceMap a₃ ≫ r₃ = w}

/-- A normalised isomorphism, solved for its restriction along the section. -/
theorem IsNormalized.restrict_eq {ψ : (modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁ ≅
      (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂}
    (h : IsNormalized σ hσ R α₁ α₂ a₁ a₂ w hw₁ hw₂ ψ) :
    restrictPullbackIso (baseChangeSection σ hσ V) rfl rfl ψ =
      restrictPullbackIso (spaceMap a₁) (spaceMap_comp_baseChangeSection σ hσ a₁) hw₁ α₁ ≪≫
        (restrictPullbackIso (spaceMap a₂) (spaceMap_comp_baseChangeSection σ hσ a₂) hw₂
          α₂).symm := by
  rw [← h, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- **Two normalised isomorphisms agree**, when `𝒪_V ⟶ f_{V, *}𝒪_{X_V}` is an isomorphism and
the source is invertible: restriction along the section is injective on their homomorphisms. -/
theorem IsNormalized.eq (hV : IsIso (s.structureSheafMap V))
    (hL : IsInvertibleModule (s.baseChange V)
      ((modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁))
    {ψ ψ' : (modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁ ≅
      (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂}
    (h : IsNormalized σ hσ R α₁ α₂ a₁ a₂ w hw₁ hw₂ ψ)
    (h' : IsNormalized σ hσ R α₁ α₂ a₁ a₂ w hw₁ hw₂ ψ') : ψ = ψ' :=
  restrictPullbackIso_injective (baseChangeSection σ hσ V) rfl rfl
    (bijective_sectionPullback_map σ hσ hV hL ψ).1
    ((h.restrict_eq σ hσ).trans (h'.restrict_eq σ hσ).symm)

/-- **A normalised isomorphism exists as soon as an isomorphism does**, when
`𝒪_V ⟶ f_{V, *}𝒪_{X_V}` is an isomorphism and the two modules are invertible: an isomorphism
of the restrictions along the section lifts. -/
theorem exists_isNormalized (hV : IsIso (s.structureSheafMap V))
    (hL₁ : IsInvertibleModule (s.baseChange V)
      ((modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁))
    (hL₂ : IsInvertibleModule (s.baseChange V)
      ((modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂))
    (ψ₀ : (modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁ ≅
      (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂) :
    ∃ ψ, IsNormalized σ hσ R α₁ α₂ a₁ a₂ w hw₁ hw₂ ψ := by
  set τ := restrictPullbackIso (spaceMap a₁) (spaceMap_comp_baseChangeSection σ hσ a₁) hw₁ α₁ ≪≫
    (restrictPullbackIso (spaceMap a₂) (spaceMap_comp_baseChangeSection σ hσ a₂) hw₂ α₂).symm
  obtain ⟨ψ, hψ⟩ := Functor.exists_mapIso_eq (modulePullback B S hS (baseChangeSection σ hσ V))
    (bijective_sectionPullback_map σ hσ hV hL₁ ψ₀).2
    (bijective_sectionPullback_map σ hσ hV hL₂ ψ₀.symm).2
    (bijective_sectionPullback_map σ hσ hV hL₁ (Iso.refl _)).1
    (bijective_sectionPullback_map σ hσ hV hL₂ (Iso.refl _)).1
    (((modulePullbackTriangle B S hS
        (rfl : baseChangeSection σ hσ V ≫ baseChangeMap s.f a₁ = _)).app L₁).symm ≪≫ τ ≪≫
      (modulePullbackTriangle B S hS
        (rfl : baseChangeSection σ hσ V ≫ baseChangeMap s.f a₂ = _)).app L₂)
  refine ⟨ψ, ?_⟩
  have hr : restrictPullbackIso (baseChangeSection σ hσ V) rfl rfl ψ = τ := by
    rw [restrictPullbackIso, hψ]
    simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]
  rw [IsNormalized, hr, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Restricting the normalising trivialisation along `spaceMap k`, then `spaceMap a₁`, is
restricting it along `spaceMap a₁'`. -/
private theorem restrict_restrict_spaceMap {V₂ : s.SchemesOver} (k : V₂ ⟶ V) {a₁' : V₂ ⟶ U₁}
    (hk : k ≫ a₁ = a₁') (hw₁ : spaceMap a₁ ≫ r₁ = w) {w' : s.baseSpaceAt V₂ ⟶ Y}
    (hw : spaceMap k ≫ w = w')
    (E : spaceMap k ≫ baseChangeSection σ hσ V ≫ baseChangeMap s.f a₁ =
      baseChangeSection σ hσ V₂ ≫ baseChangeMap s.f a₁') :
    restrictPullbackIso (spaceMap k) E hw
      (restrictPullbackIso (spaceMap a₁) (spaceMap_comp_baseChangeSection σ hσ a₁) hw₁ α₁) =
    restrictPullbackIso (spaceMap a₁') (spaceMap_comp_baseChangeSection σ hσ a₁')
      (by rw [← hk, spaceMap_comp, Category.assoc, hw₁, hw]) α₁ := by
  rw [restrictPullbackIso_restrictPullbackIso]
  exact restrictPullbackIso_congr (by rw [← hk, spaceMap_comp]) _ _ _ _ α₁

/-- **Normalised isomorphisms compose.** -/
theorem IsNormalized.trans
    {ψ : (modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁ ≅
      (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂}
    {χ : (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂ ≅
      (modulePullback B S hS (baseChangeMap s.f a₃)).obj L₃}
    (h : IsNormalized σ hσ R α₁ α₂ a₁ a₂ w hw₁ hw₂ ψ)
    (h' : IsNormalized σ hσ R α₂ α₃ a₂ a₃ w hw₂ hw₃ χ) :
    IsNormalized σ hσ R α₁ α₃ a₁ a₃ w hw₁ hw₃ (ψ ≪≫ χ) := by
  rw [IsNormalized, restrictPullbackIso_trans _ rfl rfl rfl, Iso.trans_assoc, h', h]

/-- **Normalised isomorphisms invert.** -/
theorem IsNormalized.symm
    {ψ : (modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁ ≅
      (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂}
    (h : IsNormalized σ hσ R α₁ α₂ a₁ a₂ w hw₁ hw₂ ψ) :
    IsNormalized σ hσ R α₂ α₁ a₂ a₁ w hw₂ hw₁ ψ.symm := by
  rw [IsNormalized, restrictPullbackIso_symm, h.restrict_eq σ hσ]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id,
    Iso.trans_refl]

/-- **The restriction of a normalised isomorphism along a morphism of test schemes is
normalised.** -/
theorem IsNormalized.restrict
    {ψ : (modulePullback B S hS (baseChangeMap s.f a₁)).obj L₁ ≅
      (modulePullback B S hS (baseChangeMap s.f a₂)).obj L₂}
    (h : IsNormalized σ hσ R α₁ α₂ a₁ a₂ w hw₁ hw₂ ψ) {V₂ : s.SchemesOver} (k : V₂ ⟶ V)
    {a₁' : V₂ ⟶ U₁} {a₂' : V₂ ⟶ U₂} (hk₁ : k ≫ a₁ = a₁') (hk₂ : k ≫ a₂ = a₂')
    {w' : s.baseSpaceAt V₂ ⟶ Y} (hw : spaceMap k ≫ w = w') :
    IsNormalized σ hσ R α₁ α₂ a₁' a₂' w'
      (by rw [← hk₁, spaceMap_comp, Category.assoc, hw₁, hw])
      (by rw [← hk₂, spaceMap_comp, Category.assoc, hw₂, hw])
      (restrictPullbackIso (u₂ := baseChangeMap s.f a₁') (v₂ := baseChangeMap s.f a₂')
        (baseChangeMap s.f k) (by rw [← hk₁, baseChangeMap_comp])
        (by rw [← hk₂, baseChangeMap_comp]) ψ) := by
  have hsec := (spaceMap_comp_baseChangeSection σ hσ k).symm
  have hX₁ : baseChangeMap s.f k ≫ baseChangeMap s.f a₁ = baseChangeMap s.f a₁' := by
    rw [← hk₁, baseChangeMap_comp]
  have hX₂ : baseChangeMap s.f k ≫ baseChangeMap s.f a₂ = baseChangeMap s.f a₂' := by
    rw [← hk₂, baseChangeMap_comp]
  have E₁ : spaceMap k ≫ baseChangeSection σ hσ V ≫ baseChangeMap s.f a₁ =
      baseChangeSection σ hσ V₂ ≫ baseChangeMap s.f a₁' := by
    rw [← hX₁, ← Category.assoc, ← hsec, Category.assoc]
  have E₂ : spaceMap k ≫ baseChangeSection σ hσ V ≫ baseChangeMap s.f a₂ =
      baseChangeSection σ hσ V₂ ≫ baseChangeMap s.f a₂' := by
    rw [← hX₂, ← Category.assoc, ← hsec, Category.assoc]
  have step₁ : restrictPullbackIso (baseChangeSection σ hσ V₂) rfl rfl
      (restrictPullbackIso (u₂ := baseChangeMap s.f a₁') (v₂ := baseChangeMap s.f a₂')
        (baseChangeMap s.f k) hX₁ hX₂ ψ) =
      restrictPullbackIso (spaceMap k) E₁ E₂
        (restrictPullbackIso (baseChangeSection σ hσ V) rfl rfl ψ) :=
    restrictPullbackIso_restrictPullbackIso_eq _ _ _ _ _ _ _ _ hsec _ _ _ _ ψ
  rw [IsNormalized, step₁, h.restrict_eq σ hσ, restrictPullbackIso_trans _ E₁ hw E₂,
    restrictPullbackIso_symm, restrict_restrict_spaceMap σ hσ k hk₁ hw₁ hw E₁,
    restrict_restrict_spaceMap σ hσ k hk₂ hw₂ hw E₂, Iso.trans_assoc, Iso.symm_self_id,
    Iso.trans_refl]

end Calculus

end AlgebraicGeometry.Space.PicardSituation

end

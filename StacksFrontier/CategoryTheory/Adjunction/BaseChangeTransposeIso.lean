module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# A comparison map out of an inverse image is an isomorphism exactly when its base change is

Let `L ⊣ Γ` and `L' ⊣ Γ'` be adjunctions `A ⇄ 𝒮` and `A' ⇄ 𝒮'`, let `P ⊣ Pf` be an adjunction
`𝒮 ⇄ 𝒮'` and `ext ⊣ res` an adjunction `A ⇄ A'`, and let `ι : Pf ⋙ Γ ≅ Γ' ⋙ res`. Think of `𝒮`,
`𝒮'` as sheaves of modules on two sites with final objects, `Γ`, `Γ'` as global sections, `L`,
`L'` as the associated modules of Stacks 01I7 (`M ↦ M^~`), `P ⊣ Pf` as inverse and direct image
along a morphism, and `ext ⊣ res` as extension and restriction of scalars along the map of
global rings.

For `M` with `L(Γ M) ≅ M` through the counit and `M'` with `L'(Γ' M') ≅ M'`, a morphism
`c : P M ⟶ M'` is an isomorphism exactly when the base change `ext (Γ M) ⟶ Γ' M'` of the
global-sections component of its transpose is one, provided the unit of `L' ⊣ Γ'` is an
isomorphism at `ext (Γ M)`. This is the formal core of the comparison between the flat base
change property of Stacks 0762 and the base change of global sections along flat morphisms of
affine schemes used in the affine case of Stacks 0765: the composite
`L'(ext Γ M) ≅ P(L Γ M) ≅ P M ⟶ M'` has as transpose that base change, the first isomorphism
being the one between two left adjoints of `Pf ⋙ Γ ≅ Γ' ⋙ res`.

## Main results

* `CategoryTheory.Adjunction.isIso_iff_isIso_baseChangeTranspose`.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A A' 𝒮 𝒮' : Type*} [Category* A] [Category* A'] [Category* 𝒮] [Category* 𝒮']
  {L : A ⥤ 𝒮} {Γ : 𝒮 ⥤ A} (adj : L ⊣ Γ)
  {L' : A' ⥤ 𝒮'} {Γ' : 𝒮' ⥤ A'} (adj' : L' ⊣ Γ')
  {P : 𝒮 ⥤ 𝒮'} {Pf : 𝒮' ⥤ 𝒮} (adjP : P ⊣ Pf)
  {ext : A ⥤ A'} {res : A' ⥤ A} (adjE : ext ⊣ res)
  (ι : Pf ⋙ Γ ≅ Γ' ⋙ res)

/-- The transpose, along `L' ⊣ Γ'` and `ext ⊣ res`, of the composite
`L'(ext Γ M) ≅ P(L Γ M) ⟶ P M ⟶ M'` is the global-sections component of the transpose of `c`
along `P ⊣ Pf`, read through `ι`. -/
theorem homEquiv_homEquiv_baseChangeComposite {M : 𝒮} {M' : 𝒮'} (c : P.obj M ⟶ M') :
    adjE.homEquiv _ _ (adj'.homEquiv _ _
      ((leftAdjointUniq (adjE.comp adj') ((adj.comp adjP).ofNatIsoRight ι)).hom.app (Γ.obj M) ≫
        P.map (adj.counit.app M) ≫ c)) =
      Γ.map (adjP.homEquiv _ _ c) ≫ ι.hom.app M' := by
  have h₁ : ((adjE.comp adj').homEquiv _ _)
      ((leftAdjointUniq (adjE.comp adj') ((adj.comp adjP).ofNatIsoRight ι)).hom.app (Γ.obj M) ≫
        P.map (adj.counit.app M) ≫ c) =
      ((adj.comp adjP).ofNatIsoRight ι).homEquiv _ _ (P.map (adj.counit.app M) ≫ c) := by
    rw [homEquiv_naturality_right, homEquiv_leftAdjointUniq_hom_app, homEquiv_unit]
  rw [comp_homEquiv] at h₁
  refine h₁.trans ?_
  rw [homEquiv_ofNatIsoRight_apply, comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_unit,
    right_triangle_components, Category.id_comp]
  rfl

/-- **A comparison map out of an inverse image is an isomorphism exactly when its base change on
global sections is.** With the notation of the module docstring, if the counit of `L ⊣ Γ` is an
isomorphism at `M`, the counit of `L' ⊣ Γ'` at `M'` and the unit of `L' ⊣ Γ'` at `ext (Γ M)`,
then `c : P M ⟶ M'` is an isomorphism if and only if the transpose along `ext ⊣ res` of
`Γ(c^♭) ≫ ι` is. -/
theorem isIso_iff_isIso_baseChangeTranspose {M : 𝒮} {M' : 𝒮'} (c : P.obj M ⟶ M')
    [IsIso (adj.counit.app M)] [IsIso (adj'.counit.app M')]
    [IsIso (adj'.unit.app (ext.obj (Γ.obj M)))] :
    IsIso c ↔ IsIso ((adjE.homEquiv _ _).symm (Γ.map (adjP.homEquiv _ _ c) ≫ ι.hom.app M')) := by
  let μ := leftAdjointUniq (adjE.comp adj') ((adj.comp adjP).ofNatIsoRight ι)
  let θ := μ.hom.app (Γ.obj M) ≫ P.map (adj.counit.app M) ≫ c
  have key : (adjE.homEquiv _ _).symm (Γ.map (adjP.homEquiv _ _ c) ≫ ι.hom.app M') =
      adj'.homEquiv _ _ θ := by
    rw [Equiv.symm_apply_eq]
    exact (homEquiv_homEquiv_baseChangeComposite adj adj' adjP adjE ι c).symm
  rw [key, homEquiv_unit]
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  have : IsIso θ := by
    rw [← (adj'.homEquiv _ _).symm_apply_apply θ, homEquiv_counit, homEquiv_unit]
    infer_instance
  have : IsIso (P.map (adj.counit.app M) ≫ c) := IsIso.of_isIso_comp_left (μ.hom.app _) _
  exact IsIso.of_isIso_comp_left (P.map (adj.counit.app M)) c

end CategoryTheory.Adjunction

end

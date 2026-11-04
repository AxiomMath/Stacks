module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Transport of a map characterized by a unit equation

Let `T ⊣ Q` be an adjunction and let `Λ_G : T G ⟶ R_j (P_i G)` be a family of maps
characterized by the equation `η^T_G ≫ Q(Λ_G) = η^{P_i}_G ≫ c`, where `η^{P_i}` is the unit of
a second adjunction `P_i ⊣ R_i` and `c : R_i ≅ R_j ⋙ Q`. A map of this shape is determined by the
equation, the adjoint transpose `f ↦ η ≫ Q(f)` being a bijection.

This file proves that such characterized maps are carried to each other by any comparison of two
such situations: given functors `F` relating the categories of a second situation `T' ⊣ Q'`,
`P'_i ⊣ R'_i`, comparisons `β_T : T F ⟶ F T'` and `β_P : P_i F ⟶ F P'_i` whose adjoint transposes
are `F` applied to the units followed by comparisons `τ` of the right adjoints, and a compatibility
of the `τ` with the two identifications `c`, `c'`, the characterized maps `Λ'` and `Λ` correspond:
`β_T ≫ F(Λ') ≫ τ_j = Λ ≫ R_j(β_P)`.

The geometric use is the comparison of the maps of sections along the stages of a limit of
schemes, built from inverse images on two different presentations of the small étale site, with
no comparison of the composition isomorphisms of the inverse images: only the units and the
direct images, which are concrete, enter.

## Main results

* `CategoryTheory.Adjunction.unitCharacterized_transport`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {Ai Aj AX Ci Cj CX : Type*} [Category* Ai] [Category* Aj] [Category* AX]
  [Category* Ci] [Category* Cj] [Category* CX]
  {T : Ai ⥤ Aj} {Q : Aj ⥤ Ai} (adjT : T ⊣ Q)
  {Pi : Ai ⥤ AX} {Ri : AX ⥤ Ai} (adjP : Pi ⊣ Ri) {Rj : AX ⥤ Aj} (c : Ri ⟶ Rj ⋙ Q)
  {T' : Ci ⥤ Cj} {Q' : Cj ⥤ Ci} (adjT' : T' ⊣ Q')
  {Pi' : Ci ⥤ CX} {Ri' : CX ⥤ Ci} (adjP' : Pi' ⊣ Ri') {Rj' : CX ⥤ Cj} (c' : Ri' ⟶ Rj' ⋙ Q')
  (Fi : Ci ⥤ Ai) (Fj : Cj ⥤ Aj) (FX : CX ⥤ AX)
  (τT : Q' ⋙ Fi ⟶ Fj ⋙ Q) (τi : Ri' ⋙ Fi ⟶ FX ⋙ Ri) (τj : Rj' ⋙ Fj ⟶ FX ⋙ Rj)

include adjT in
/-- **Maps characterized by a unit equation correspond under a comparison of adjunctions.** -/
theorem unitCharacterized_transport
    (Λ : ∀ G, T.obj G ⟶ Rj.obj (Pi.obj G))
    (hΛ : ∀ G, adjT.unit.app G ≫ Q.map (Λ G) = adjP.unit.app G ≫ c.app (Pi.obj G))
    (Λ' : ∀ H, T'.obj H ⟶ Rj'.obj (Pi'.obj H))
    (hΛ' : ∀ H, adjT'.unit.app H ≫ Q'.map (Λ' H) = adjP'.unit.app H ≫ c'.app (Pi'.obj H))
    (βT : ∀ H, T.obj (Fi.obj H) ⟶ Fj.obj (T'.obj H))
    (hβT : ∀ H, adjT.unit.app (Fi.obj H) ≫ Q.map (βT H) =
      Fi.map (adjT'.unit.app H) ≫ τT.app (T'.obj H))
    (βP : ∀ H, Pi.obj (Fi.obj H) ⟶ FX.obj (Pi'.obj H))
    (hβP : ∀ H, adjP.unit.app (Fi.obj H) ≫ Ri.map (βP H) =
      Fi.map (adjP'.unit.app H) ≫ τi.app (Pi'.obj H))
    (hc : ∀ K, Fi.map (c'.app K) ≫ τT.app (Rj'.obj K) ≫ Q.map (τj.app K) =
      τi.app K ≫ c.app (FX.obj K))
    (H : Ci) :
    βT H ≫ Fj.map (Λ' H) ≫ τj.app (Pi'.obj H) = Λ (Fi.obj H) ≫ Rj.map (βP H) := by
  apply (adjT.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp]
  have h₁ := τT.naturality (Λ' H)
  have h₂ := c.naturality (βP H)
  simp only [Functor.comp_map] at h₁ h₂
  rw [reassoc_of% hβT, ← reassoc_of% h₁, ← Fi.map_comp_assoc, hΛ', Fi.map_comp, Category.assoc,
    hc, ← reassoc_of% hβP, h₂, reassoc_of% hΛ]

section CompositionIso

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)

/-- **The unit equation characterizing the comparison of left adjoints along a composite.** The
unit of `F₀₁ ⊣ G₁₀`, followed by `G₁₀` applied to the unit of `F₁₂ ⊣ G₂₁` and to the comparison
`F₁₂ F₀₁ ≅ F₀₂`, is the unit of `F₀₂ ⊣ G₂₀` followed by the comparison of the right adjoints. -/
theorem unit_comp_map_leftAdjointCompIso_hom (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) (X : C₀) :
    adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X) ≫
        G₂₁.map ((leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom.app X)) =
      adj₀₂.unit.app X ≫ e.inv.app (F₀₂.obj X) := by
  rw [unit_conjugateEquiv_symm adj₀₂ (adj₀₁.comp adj₁₂) e.inv X, comp_unit_app]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

end CompositionIso

end CategoryTheory.Adjunction

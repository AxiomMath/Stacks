module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Transporting universal arrows along equivalences

A morphism `d : I ⟶ R N` is a *universal arrow* from `I` to a functor `R` when every
`e : I ⟶ R M` factors as `d ≫ R h` for a unique `h : N ⟶ M`. For a left adjoint `L ⊣ R` this
says exactly that the adjoint transpose `L I ⟶ N` of `d` is an isomorphism; the unit of the
adjunction is universal.

This file proves that universality is carried along a square of functors
```
𝒪₀ --R₀--> 𝓡₀
|Φ         |Ψ
v          v
𝒪  --R-->  𝓡
```
commuting up to a natural isomorphism, with `Φ` an equivalence and `Ψ` fully faithful: if
`d₀ : I₀ ⟶ R₀ N₀` is universal, so is `I ≅ Ψ I₀ ⟶ Ψ R₀ N₀ ≅ R Φ N₀`.

## Main results

* `CategoryTheory.Adjunction.isIso_homEquiv_symm_of_bijective`: the transpose of a universal
  arrow is an isomorphism.
* `CategoryTheory.Adjunction.bijective_comp_map_unit`: the unit is universal.
* `CategoryTheory.bijective_comp_map_of_transport`: universality is transported along `Φ`, `Ψ`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Adjunction

variable {𝓡 : Type u₁} [Category.{v₁} 𝓡] {𝒪 : Type u₂} [Category.{v₂} 𝒪]
  {L : 𝓡 ⥤ 𝒪} {R : 𝒪 ⥤ 𝓡} (adj : L ⊣ R)

/-- **The transpose of a universal arrow is an isomorphism.** If every `e : I ⟶ R M` factors
uniquely as `d ≫ R h`, then the adjoint transpose `L I ⟶ N` of `d` is an isomorphism. -/
theorem isIso_homEquiv_symm_of_bijective {I : 𝓡} {N : 𝒪} (d : I ⟶ R.obj N)
    (h : ∀ M : 𝒪, Function.Bijective fun k : N ⟶ M => d ≫ R.map k) :
    IsIso ((adj.homEquiv I N).symm d) := by
  refine isIso_of_coyoneda_map_bijective _ fun M ↦ ?_
  convert (adj.homEquiv I M).symm.bijective.comp (h M) using 1
  exact funext fun k ↦ (adj.homEquiv_naturality_right_symm d k).symm

/-- **The unit is universal.** Every `e : I ⟶ R M` factors as `adj.unit.app I ≫ R h` for a
unique `h : L I ⟶ M`. -/
theorem bijective_comp_map_unit (I : 𝓡) (M : 𝒪) :
    Function.Bijective fun k : L.obj I ⟶ M => adj.unit.app I ≫ R.map k :=
  (adj.homEquiv I M).bijective

end Adjunction

section Transport

variable {𝒪₀ : Type u₁} [Category.{v₁} 𝒪₀] {𝓡₀ : Type u₂} [Category.{v₂} 𝓡₀]
  {𝒪 : Type u₃} [Category.{v₃} 𝒪] {𝓡 : Type u₄} [Category.{v₄} 𝓡]
  {R₀ : 𝒪₀ ⥤ 𝓡₀} {R : 𝒪 ⥤ 𝓡} {Φ : 𝒪₀ ⥤ 𝒪} {Ψ : 𝓡₀ ⥤ 𝓡}
  (β : Φ ⋙ R ≅ R₀ ⋙ Ψ)

/-- Composing on both sides with isomorphisms is a bijection of hom-sets. -/
theorem bijective_comp_comp_of_iso {C : Type u₁} [Category.{v₁} C] {A A' B B' : C}
    (i : A' ≅ A) (j : B ≅ B') : Function.Bijective fun x : A ⟶ B => i.hom ≫ x ≫ j.hom :=
  Function.bijective_iff_has_inverse.2 ⟨fun y ↦ i.inv ≫ y ≫ j.inv, fun x ↦ by simp, fun y ↦ by simp⟩

/-- Universality of an arrow is unchanged by composing the target with an isomorphism. -/
theorem bijective_comp_map_of_iso {I : 𝓡} {N M M' : 𝒪} (d : I ⟶ R.obj N) (i : M ≅ M')
    (h : Function.Bijective fun k : N ⟶ M => d ≫ R.map k) :
    Function.Bijective fun k : N ⟶ M' => d ≫ R.map k := by
  convert ((bijective_comp_comp_of_iso (Iso.refl I) (R.mapIso i)).comp h).comp
    (bijective_comp_comp_of_iso (Iso.refl N) i.symm) using 1
  funext k
  simp only [Function.comp_apply, Iso.refl_hom, Category.id_comp, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, ← R.map_comp, Iso.inv_hom_id, Category.comp_id]

variable [Φ.Full] [Φ.Faithful] [Φ.EssSurj]

/-- **Universal arrows are transported along an equivalence**, with the full faithfulness of `Ψ`
given as data. For a square `Φ ⋙ R ≅ R₀ ⋙ Ψ` with `Φ` an equivalence and `Ψ` fully faithful, if
`d₀ : I₀ ⟶ R₀ N₀` is universal and `I ≅ Ψ I₀`, then `I ≅ Ψ I₀ ⟶ Ψ R₀ N₀ ≅ R Φ N₀` is
universal. -/
theorem bijective_comp_map_of_transport_of_fullyFaithful (hΨ : Ψ.FullyFaithful) {I₀ : 𝓡₀}
    {N₀ : 𝒪₀} (d₀ : I₀ ⟶ R₀.obj N₀)
    (h₀ : ∀ M₀ : 𝒪₀, Function.Bijective fun k : N₀ ⟶ M₀ => d₀ ≫ R₀.map k)
    {I : 𝓡} (e : I ≅ Ψ.obj I₀) (M : 𝒪) :
    Function.Bijective fun k : Φ.obj N₀ ⟶ M =>
      (e.hom ≫ Ψ.map d₀ ≫ β.inv.app N₀) ≫ R.map k := by
  refine bijective_comp_map_of_iso _ (Φ.objObjPreimageIso M) ?_
  set M₀ := Φ.objPreimage M
  have he : (fun k : Φ.obj N₀ ⟶ Φ.obj M₀ => (e.hom ≫ Ψ.map d₀ ≫ β.inv.app N₀) ≫ R.map k) =
      (fun x : Ψ.obj I₀ ⟶ Ψ.obj (R₀.obj M₀) => e.hom ≫ x ≫ β.inv.app M₀) ∘ Ψ.map ∘
        (fun k : N₀ ⟶ M₀ => d₀ ≫ R₀.map k) ∘ Φ.preimage := by
    funext k
    have hn := β.inv.naturality (Φ.preimage k)
    simp only [Functor.comp_map, Functor.map_preimage] at hn
    simp only [Function.comp_apply, Category.assoc, Functor.map_comp]
    rw [← hn]
  rw [he]
  exact (bijective_comp_comp_of_iso e (β.app M₀).symm).comp ((hΨ.map_bijective _ _).comp
    ((h₀ M₀).comp (Function.bijective_iff_has_inverse.2 ⟨Φ.map, Φ.map_preimage, Φ.preimage_map⟩)))

variable [Ψ.Full] [Ψ.Faithful]

/-- **Universal arrows are transported along an equivalence.** For a square `Φ ⋙ R ≅ R₀ ⋙ Ψ`
with `Φ` an equivalence and `Ψ` fully faithful, if `d₀ : I₀ ⟶ R₀ N₀` is universal and
`I ≅ Ψ I₀`, then `I ≅ Ψ I₀ ⟶ Ψ R₀ N₀ ≅ R Φ N₀` is universal. -/
theorem bijective_comp_map_of_transport {I₀ : 𝓡₀} {N₀ : 𝒪₀} (d₀ : I₀ ⟶ R₀.obj N₀)
    (h₀ : ∀ M₀ : 𝒪₀, Function.Bijective fun k : N₀ ⟶ M₀ => d₀ ≫ R₀.map k)
    {I : 𝓡} (e : I ≅ Ψ.obj I₀) (M : 𝒪) :
    Function.Bijective fun k : Φ.obj N₀ ⟶ M =>
      (e.hom ≫ Ψ.map d₀ ≫ β.inv.app N₀) ≫ R.map k :=
  bijective_comp_map_of_transport_of_fullyFaithful β (Functor.FullyFaithful.ofFullyFaithful Ψ) d₀
    h₀ e M

end Transport

end CategoryTheory

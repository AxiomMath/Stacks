module

public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtIdealPowerPullback

/-!
# The induction step of the injectivity chase of Stacks 0G2H

Let `X` be a Noetherian scheme, `𝓘` a quasi-coherent sheaf of ideals and `𝓐`, `𝓖` coherent
`𝒪_X`-modules. The injectivity half of the core case of [Stacks, Tag 0G2H] asserts, in degree `i`,
that a class in `Ext^i_X(𝓐, 𝓖)` vanishing on `U = X ∖ V(𝓘)` already dies on some member `𝓘^n 𝓐`
of the ideal-power filtration of `𝓐`. This file proves the passage from degree `i` to degree
`i + 1`, with the degree-`i` assertion for the class produced by a dimension shift as a hypothesis.

**`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_pos`.** Let
`ξ` be a class in `Ext^{i+1}_X(𝓐, 𝓖)`. Suppose that for every coherent effacement `α : 𝓕'' ⟶ 𝓐`
of `ξ` — that is, every epimorphism from a coherent module with coherent kernel, together with a
class `ξ'` of degree `i` on `ker α` whose boundary is `ξ` — the class `ξ'` dies on some member
`𝓘^m (ker α)` of the ideal-power filtration of `ker α`. Then `ξ` dies on some `𝓘^n 𝓐`.

The proof combines the dimension shift
`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos`, which produces the effacement
`α`, the short exact sequence `S : 0 ⟶ ker α ⟶ 𝓕'' ⟶ 𝓐 ⟶ 0` of coherent modules and the class `ξ'`
with `hS.extClass ∘ ξ' = ξ`; Artin-Rees in the form
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero`, which
converts the vanishing of `ξ'` on `𝓘^m (ker α)` into its vanishing on `𝓘^n 𝓕'' ⊓ ker α` for some
`n ≥ m`; and the pullback of `S` to the ideal powers,
`Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_submoduleι_comp_extClass_comp_eq_zero`, which
turns that into the vanishing of `ξ` on `𝓘^n 𝓐`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_submoduleι_comp_eq_zero_of_pos`: **the
  induction step of the injectivity chase of [Stacks, Tag 0G2H].**

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe w u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- **The induction step of the injectivity chase of [Stacks, Tag 0G2H].** Let `ξ` be a class in
`Ext^{i+1}_X(𝓐, 𝓖)` between coherent modules on a Noetherian scheme. If, for every coherent
effacement `α : 𝓕'' ⟶ 𝓐` of `ξ` and every class `ξ'` of degree `i` on `ker α` with boundary `ξ`,
the class `ξ'` dies on a member of the ideal-power filtration of `ker α`, then `ξ` dies on a
member of the ideal-power filtration of `𝓐`. -/
theorem exists_mk₀_submoduleι_comp_eq_zero_of_pos
    [_root_.AlgebraicGeometry.IsNoetherian X] [HasExt.{w} X.Modules] (I : X.IdealSheafData)
    {A G : X.Modules} [A.IsCoherent] [G.IsCoherent] {i : ℕ} (ξ : Ext.{w} A G (i + 1))
    (h : ∀ (E : X.Modules) (α : E ⟶ A), E.IsCoherent → Epi α → (kerMod α).IsCoherent →
      ∀ (hS : (ShortComplex.mk (kerInclusion α) α (kerInclusion_comp α)).ShortExact)
        (ξ' : Ext.{w} (kerMod α) G i), hS.extClass.comp ξ' (Nat.add_comm 1 i) = ξ →
        ∃ m : ℕ, (Ext.mk₀ (submoduleι
          (Stacks.Algebraization.idealPowerMultiple I m (kerMod α)))).comp ξ' (zero_add i) = 0) :
    ∃ n : ℕ, (Ext.mk₀ (submoduleι
      (Stacks.Algebraization.idealPowerMultiple I n A))).comp ξ (zero_add (i + 1)) = 0 := by
  obtain ⟨E, α, hE, hα, hker, hS, ξ', hξ⟩ :=
    Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos.{w} ξ
  have := hE
  have := hα
  have := hker
  have hEq : E.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent E
  have hAq : A.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent A
  have hkerq : (kerMod α).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (kerMod α)
  obtain ⟨m, hm⟩ := h E α hE hα hker hS ξ' hξ
  obtain ⟨n, _, hn⟩ := exists_mk₀_submoduleHomOfLE_inf_comp_eq_zero.{w} I
    (SheafOfModules.Submodule.ker α) hE hkerq ξ' hm
  refine ⟨n, ?_⟩
  rw [← hξ]
  exact mk₀_submoduleι_comp_extClass_comp_eq_zero I n hEq hAq α hα hS ξ' hn

end Stacks.AlgebraicGeometry.IdealPowerColimit

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SmoothProperPoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyCount

/-!
# Poincaré duality on a dense open in relative dimension zero

Let `k` be separably closed, `ℓ` a prime and `Λ = ℤ/ℓ`. Let `W` be smooth irreducible of relative
dimension zero over `k`, with noetherian underlying space and a compactification `j : W → X̄`,
and let `t : H⁰_c(W) = Ext⁰_X̄(Λ, j_! Λ_W) → Λ` be injective. Then duality holds at
`j_! Λ_W` for `D = j_! Λ_W` and `t`, and `Ext^q_X̄(j_! Λ_W, j_! Λ_W) = 0` for `q > 0`
(`Stacks.EtaleCohomology.exists_dense_isDualityPerfect_of_smoothOfRelativeDimension_zero`, with
the dense open `W` itself): this is the case `e = 0` of
`Stacks.EtaleCohomology.PoincareDualityCore`.

Indeed `W` is a single point, proper over `k`, and
`Ext^q_X̄(j_! Λ_W, j_! Λ_W) = Ext^q_W(Λ_W, Λ_W) = H^q(W, Λ)` (the adjunction `j_! ⊣ j⁻¹`, whose
unit is invertible), which is `Λ` for `q = 0` and vanishes for `q > 0` (Tag 095U in dimension
zero). The only pairing is `H⁰_c(W) × End(j_! Λ_W) → Λ`, `(x, y) ↦ t(x ∘ y)`, injective in `x`
(take `y = 1`, `t` injective) between groups of `ℓ` elements, hence perfect.

This is the base of the induction on the dimension in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.bijective_ext_extensionByZero_of_smoothOfRelativeDimension_zero`.
* `Stacks.EtaleCohomology.exists_dense_isDualityPerfect_of_smoothOfRelativeDimension_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of k)) (jc : CompactificationOf (Over.mk f))

/-- **`Ext^q_W(Λ_W, Λ_W) ≅ Ext^q_X̄(j_! Λ_W, j_! Λ_W)`** for a compactification `j`: the class
`x` goes to the adjoint of `x` followed by the unit `Λ_W → j⁻¹ j_! Λ_W` of `j_! ⊣ j⁻¹`, which is
invertible. -/
theorem bijective_ext_extensionByZero_of_compactification (q : ℕ) :
    Function.Bijective (fun x : Ext (unitSheaf (X := W) ℓ) (unitSheaf (X := W) ℓ) q =>
      Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) jc.immersion)
        (unitSheaf (X := W) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ)) q
        (x.comp (Ext.mk₀ ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) jc.immersion).unit.app
          (unitSheaf (X := W) ℓ))) (add_zero q))) :=
  (Stacks.ExtAdjunction.extMap_bijective (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
      jc.immersion) _ _ q).comp
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) jc.immersion).unit.app
        (unitSheaf (X := W) ℓ)) q)

variable [IsSepClosed k] [SmoothOfRelativeDimension 0 f] [TopologicalSpace.NoetherianSpace W]
  [IrreducibleSpace W]

/-- **Poincaré duality in relative dimension zero** (the case `e = 0` of
`Stacks.EtaleCohomology.PoincareDualityCore`): for `W` smooth irreducible of relative dimension
zero over `k` separably closed, a compactification `j : W → X̄` and an injective trace `t` on
`H⁰_c(W)`, duality holds at `j_! Λ` of the constant sheaf on the dense open `W`, and
`Ext^q_X̄(j_! Λ_W, j_! Λ_W) = 0` for `q > 0`. -/
theorem exists_dense_isDualityPerfect_of_smoothOfRelativeDimension_zero
    (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * 0) →+ ZMod ℓ) (ht : Function.Injective t) :
    ∃ W₀ : W.Opens, Dense (W₀ : Set W) ∧
      Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * 0) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
            (unitSheaf (X := W) ℓ))) ∧
      ∀ q, 2 * 0 < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
        jc.immersion).obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
          (unitSheaf (X := W) ℓ)))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ)) q) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have := isProper_of_smoothOfRelativeDimension_zero f jc
  obtain ⟨w⟩ := IrreducibleSpace.toNonempty (X := W)
  have : Nonempty W := ⟨w⟩
  have hdim : topologicalKrullDim W ≤ (0 : ℕ) :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 0 f).le
  let D := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ)
  have hb := bijective_ext_extensionByZero_of_compactification ℓ f jc
  -- `Ext^q(D, D) = H^q(W, Λ)` vanishes for `q > 0` and has `ℓ` elements for `q = 0`
  have hvan : ∀ q, 0 < q → Subsingleton (Ext D D q) := fun q hq =>
    have := subsingleton_ext_constantModuleSheaf_zmod_of_proper f 0 hdim ℓ
      (unitSheaf (X := W) ℓ) q (by omega)
    (hb q).2.subsingleton
  have hcard0 : Nat.card (Ext D D 0) = ℓ :=
    (Nat.card_eq_of_bijective _ (hb 0)).symm.trans (LevelChange.natCard_ext_zero_unitSheaf ℓ)
  have : Finite (Ext D D 0) := Nat.finite_of_card_ne_zero (by rw [hcard0]; exact hp.ne_zero)
  obtain ⟨eH⟩ := nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero ℓ f jc
  have hPD : Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ) D (2 * 0) t D := by
    intro i j h
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    have hinj : Function.Injective (Ext.dualityPairing (unitSheaf (X := jc.space) ℓ) D (2 * 0) t
        D h) := by
      intro x y hxy
      have e := congrArg (fun φ => φ (Ext.mk₀ (𝟙 D))) hxy
      simp only [Ext.dualityPairing_apply] at e
      rw [Ext.comp_mk₀_id, Ext.comp_mk₀_id] at e
      exact ht e
    have hcardH : Nat.card (Ext D D 0 →+ ZMod ℓ) = ℓ := by
      rw [natCard_addMonoidHom_zmod, hcard0]
    have : Finite (Ext D D 0 →+ ZMod ℓ) :=
      Nat.finite_of_card_ne_zero (by rw [hcardH]; exact hp.ne_zero)
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcardH, Nat.card_congr eH.toEquiv, Nat.card_zmod]
  -- the dense open `W` itself
  have := isIso_etaleModuleExtensionByZeroAdj_counit_app_top (ZMod ℓ) (unitSheaf (X := W) ℓ)
  let e := (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).mapIso
    (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (⊤ : W.Opens).ι).counit.app
      (unitSheaf (X := W) ℓ)))
  refine ⟨⊤, by rw [TopologicalSpace.Opens.coe_top]; exact dense_univ,
    Ext.isDualityPerfect_of_iso e.symm hPD, fun q hq => ?_⟩
  exact @Function.Surjective.subsingleton _ _ _ (hvan q (by omega))
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := D) e.hom q).2

end Stacks.EtaleCohomology

end

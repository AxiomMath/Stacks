module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerNondivisibleReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.UnitSheafRestrictScalarsExt

/-!
# The level comparison of Kummer point classes, from the reduction square

Let `N = ℓʳ⁺¹`, `res` restriction of scalars along `ℤ/N → ℤ/ℓ` and `ρ_Y : Λ_Y ⟶ res Λ'_Y` the
reduction. If the Kummer point classes at the two levels form a commutative square
`η_N ∘ ρ_Y = res(η_ℓ) ∘ ρ_Y` (`Stacks.EtaleCohomology.KummerFlag.KummerPointClassReductionSquare`),
then an `ℓ`-divisible `η_N = ℓ w` gives `res(η_ℓ) ∘ ρ_Y = w ∘ (ℓ ρ_Y) = 0`, `res Λ'_Y` being killed
by `ℓ`, and `η_ℓ = 0` since `y ↦ res(y) ∘ ρ_Y` is injective
(`Stacks.EtaleCohomology.ExtensionTorsor.bijective_mk₀_unitSheafReduction_comp_mapExactFunctor`):
`Stacks.EtaleCohomology.KummerFlag.kummerPointClassLevelReduction_of_reductionSquare`.

## Main definitions

* `Stacks.EtaleCohomology.KummerFlag.KummerPointClassReductionSquare`

## Main results

* `Stacks.EtaleCohomology.ExtensionTorsor.nsmul_unitSheafReduction_eq_zero`
* `Stacks.EtaleCohomology.KummerFlag.kummerPointClassLevelReduction_of_reductionSquare`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

namespace ExtensionTorsor

variable {Y : Scheme.{u}} {N N' : ℕ} (h : N' ∣ N)

/-- **`N'` kills the reduction `Λ_Y ⟶ res Λ'_Y`**, its target being a sheaf of `ℤ/N'`-modules. -/
theorem nsmul_unitSheafReduction_eq_zero : N' • unitSheafReduction Y h = 0 := by
  apply (homUnitSheafEquiv N _).injective
  rw [homUnitSheafEquiv_eq_app N _ (N' • _), homUnitSheafEquiv_eq_app N _ 0]
  have e1 : (N' • unitSheafReduction Y h).hom = N' • (unitSheafReduction Y h).hom :=
    Functor.map_nsmul (sheafToPresheaf _ _)
  rw [e1, NatTrans.app_nsmul]
  have key : ∀ y : (unitSheaf (X := Y) N').obj.obj (op (etaleSiteTerminal Y)), N' • y = 0 :=
    fun y => by rw [← Nat.cast_smul_eq_nsmul (ZMod N'), ZMod.natCast_self, zero_smul]
  exact key _

end ExtensionTorsor

namespace KummerFlag

open ExtensionTorsor

/-- **The reduction square of Kummer point classes.** In the situation of
`Stacks.EtaleCohomology.KummerFlag.KummerPointClassLevelReduction`, the reduction
`Λ_Y ⟶ res Λ'_Y` carries the Kummer point class `η_N` at level `N = ℓʳ⁺¹` (root `ζ`) to the Kummer
point class `η_ℓ` at level `ℓ` (root `ζ^{ℓʳ}`) read with `ℤ/N` coefficients:
`η_N ∘ ρ_Y = res(η_ℓ) ∘ ρ_Y` in `Ext^{2d}_{ℤ/N}(Λ_Y, res Λ'_Y)`. -/
def KummerPointClassReductionSquare (K : Type u) [Field K] (ℓ : ℕ) : Prop :=
  ∀ (Y U O : Scheme.{u}) (fY : Y ⟶ Spec (.of K)) (n : U ⟶ Y) [IsOpenImmersion n]
    (o : O ⟶ Y) [IsOpenImmersion o] [PreconnectedSpace U] {d : ℕ} (D : Fin d → DivisorDatum U)
    [∀ m, PreconnectedSpace (D m).V],
    (∀ y : Y, y ∈ Set.range n.base ∨ y ∈ Set.range o.base) →
    (∀ x : U, n.base x ∈ Set.range o.base → ∃ m, x ∉ Set.range (D m).i.base) → ∀
    (r : ℕ) {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ (ℓ ^ (r + 1)))
    (hN : IsUnit (((ℓ ^ (r + 1) : ℕ)) : K)) (hζ' : IsPrimitiveRoot ζ' ℓ) (hℓ : IsUnit (ℓ : K)),
    ζ ^ (ℓ ^ r) = ζ' →
    ∀ (z : unitSheaf (X := Y) (ℓ ^ (r + 1)) ⟶
        (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).obj
          (flagSheaf (N := ℓ ^ (r + 1)) D)),
      IsAdapted n (flagUnit (N := ℓ ^ (r + 1)) D) z →
    ∀ (z' : unitSheaf (X := Y) ℓ ⟶
        (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) n).obj (flagSheaf (N := ℓ) D)),
      IsAdapted n (flagUnit (N := ℓ) D) z' →
      (kummerPointClass hζ hN fY n D z).comp
          (Ext.mk₀ (unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r)))) (add_zero _) =
        (Ext.mk₀ (unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r)))).comp
          ((kummerPointClass hζ' hℓ fY n D z').mapExactFunctor
            (etaleModuleRestrictScalars
              (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero r)) (ZMod ℓ)) Y))
          (zero_add _)

/-- `x ↦ (n • x) ∘ y` is `x ↦ x ∘ (n • y)`. -/
theorem nsmul_comp_eq_comp_nsmul {C : Type*} [Category C] [Abelian C] [HasExt C] {A B B' : C}
    {p q s : ℕ} (x : Ext A B p) (y : Ext B B' q) (hpq : p + q = s) (m : ℕ) :
    (m • x).comp y hpq = x.comp (m • y) hpq := by
  induction m with
  | zero => rw [zero_smul, zero_smul, Ext.zero_comp, Ext.comp_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, Ext.add_comp, Ext.comp_add, ih]

/-- **The level comparison follows from the reduction square.** -/
theorem kummerPointClassLevelReduction_of_reductionSquare (K : Type u) [Field K] (ℓ : ℕ)
    (hsq : KummerPointClassReductionSquare K ℓ) : KummerPointClassLevelReduction K ℓ := by
  intro Y U O fY n _ o _ _ d D _ hcov hZ r ζ ζ' hζ hN hζ' hℓ hζζ' z hz z' hz' hdiv
  obtain ⟨w, hw⟩ := hdiv
  have hs := hsq Y U O fY n o D hcov hZ r hζ hN hζ' hℓ hζζ' z hz z' hz'
  rw [hw] at hs
  have h0 : (ℓ • w).comp (Ext.mk₀ (unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r))))
      (add_zero _) = 0 := by
    rw [nsmul_comp_eq_comp_nsmul]
    have hmk : ∀ m : ℕ, m • (Ext.mk₀ (unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r)))) =
        Ext.mk₀ (m • unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r))) := by
      intro m
      induction m with
      | zero => rw [zero_smul, zero_smul, Ext.mk₀_zero]
      | succ m ih => rw [succ_nsmul, succ_nsmul, ih, Ext.mk₀_add]
    have : ℓ • (Ext.mk₀ (unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r)))) = 0 := by
      rw [hmk, nsmul_unitSheafReduction_eq_zero, Ext.mk₀_zero]
    rw [this, Ext.comp_zero]
  apply (bijective_mk₀_unitSheafReduction_comp_mapExactFunctor
    (dvd_pow_self ℓ (Nat.succ_ne_zero r)) (2 * d) _).1
  change (Ext.mk₀ (unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r)))).comp
      ((kummerPointClass hζ' hℓ fY n D z').mapExactFunctor _) _ =
    (Ext.mk₀ (unitSheafReduction Y (dvd_pow_self ℓ (Nat.succ_ne_zero r)))).comp
      ((0 : Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) (2 * d)).mapExactFunctor _) _
  rw [← hs, h0]
  have hz0 : (0 : Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) (2 * d)).mapExactFunctor
      (etaleModuleRestrictScalars
        (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero r)) (ZMod ℓ)) Y) = 0 :=
    map_zero (Functor.mapExtAddHom _ _ _ (2 * d))
  rw [hz0, Ext.comp_zero]

end KummerFlag

end Stacks.EtaleCohomology

end

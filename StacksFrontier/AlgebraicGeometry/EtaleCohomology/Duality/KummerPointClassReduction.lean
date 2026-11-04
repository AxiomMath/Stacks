module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagClassReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointClassLevelSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerPointAdapted

/-!
# The reduction square of Kummer point classes

Let `N = ℓʳ⁺¹`, `res` restriction of scalars along `ℤ/N → ℤ/ℓ` and `ρ_Y : Λ_Y ⟶ res Λ'_Y` the
reduction. For a flag `D` of divisor data on an open `n : U ⟶ Y` with preconnected open parts,
whose support is closed in `Y`, and maps `z`, `z'` adapted at the levels `N` and `ℓ`, the Kummer
point classes satisfy `η_N ∘ ρ_Y = res(η_ℓ) ∘ ρ_Y`
(`Stacks.EtaleCohomology.KummerFlag.kummerPointClassReductionSquare`, the statement
`Stacks.EtaleCohomology.KummerFlag.KummerPointClassReductionSquare`).

The proof composes commuting squares of `Ext` classes (`Stacks.ExtReduction.ExtSq`): with
`w = ρ_U` read through `n⁻¹ Λ ≅ Λ` at both levels, the Kummer flag classes form a square through
the reduction `φ` of the flag sheaves
(`Stacks.EtaleCohomology.extSq_kummerFlagClass`); the adjunction `n_! ⊣ n⁻¹` carries it to a
square between the images in `Ext(n_! E_0 ⋯ E_{d-1} Λ_U, Λ_Y)`, `res` commuting with `n_!`
compatibly with the counits; and `z ∘ n_!(φ) = ρ_Y ∘ res(z')` because restriction to `U` is
injective on maps `Λ_Y ⟶ n_!(res E_0 ⋯ E_{d-1} Λ'_U)`, the flag sheaf vanishing on `U ∩ O`.

## Main results

* `Stacks.EtaleCohomology.KummerFlag.kummerPointClassReductionSquare`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor Stacks.ExtReduction

universe u

namespace Stacks.EtaleCohomology.KummerFlag

-- see `Stacks.EtaleCohomology.ExtensionTorsor.kummerUnitClass_comp_unitSheafReduction`
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- **The reduction square of Kummer point classes holds**: `η_N ∘ ρ_Y = res(η_ℓ) ∘ ρ_Y` for
`N = ℓʳ⁺¹`, roots `ζ` and `ζ^{ℓʳ}`, and adapted maps at the two levels. -/
theorem kummerPointClassReductionSquare (K : Type u) [Field K] (ℓ : ℕ) :
    KummerPointClassReductionSquare K ℓ := by
  intro Y U O fY n _ o _ _ d D _ hcov hZ r ζ ζ' hζ hN hζ' hℓ hζζ' z hz z' hz'
  subst hζζ'
  have he : ℓ ^ r * ℓ = ℓ ^ (r + 1) := (pow_succ ℓ r).symm
  let h : ℓ ∣ ℓ ^ (r + 1) := Dvd.intro_left (ℓ ^ r) he
  let RY := etaleModuleRestrictScalars (ZMod.castHom h (ZMod ℓ)) Y
  let RU := etaleModuleRestrictScalars (ZMod.castHom h (ZMod ℓ)) U
  let ρY := unitSheafReduction Y h
  let ι := restrictionUnitSheafIso (N := ℓ ^ (r + 1)) n
  let ι' := restrictionUnitSheafIso (N := ℓ) n
  let nρ := restrictionReduction h n ρY
  let wU : unitSheaf (X := U) (ℓ ^ (r + 1)) ⟶ RU.obj (unitSheaf (X := U) ℓ) :=
    ι.inv ≫ nρ ≫ RU.map ι'.hom
  let F := flagSheaf (N := ℓ ^ (r + 1)) D
  let F' := flagSheaf (N := ℓ) D
  let φ : F ⟶ RU.obj F' := flagSheafReduction h D wU
  let θ := etaleModuleExtensionByZeroRestrictScalars (ZMod.castHom h (ZMod ℓ)) n
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod (ℓ ^ (r + 1))) n
  let adj' := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) n
  -- the flag classes, read through `n⁻¹ Λ ≅ Λ`
  have hrus : ι.inv ≫ nρ = wU ≫ RU.map ι'.inv := by
    simp only [wU, Category.assoc, ← CategoryTheory.Functor.map_comp, ι'.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have hx := (extSq_kummerFlagClass (n ≫ fY) he hζ hζ' hN hℓ D wU).comp (ExtSq.mk₀ hrus)
    (add_zero (2 * d))
  -- the adjunction `n_! ⊣ n⁻¹`
  have hε : (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map nρ ≫
      θ.hom.app ((etaleModuleRestriction.{u, 0} (ZMod ℓ) n).obj (unitSheaf (X := Y) ℓ)) ≫
        RY.map (adj'.counit.app (unitSheaf (X := Y) ℓ)) = adj.counit.app _ ≫ ρY :=
    (congrArg ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map nρ ≫ ·)
      (etaleModuleExtensionByZeroRestrictScalars_counit (ZMod.castHom h (ZMod ℓ)) n
        (unitSheaf (X := Y) ℓ))).trans (adj.counit_naturality ρY)
  have hext := ExtSq.extMap adj adj' θ.hom hx hε
  -- the adapted maps
  have hP : IsZero ((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) (pullback.snd o n)).obj
      (RU.obj F')) := by
    have h0 := isZero_restriction_flagSheaf_of_forall (N := ℓ) D (pullback.snd o n) fun t =>
      hZ _ ⟨(pullback.fst o n).base t, by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]⟩
    exact Functor.map_isZero (etaleModuleRestrictScalars (ZMod.castHom h (ZMod ℓ))
      (pullback o n)) h0
  have := isIso_extensionByZeroToDirectImage_of_isZero (ZMod (ℓ ^ (r + 1))) n o
    (pullback.snd o n) (pullback.fst o n) (IsPullback.of_hasPullback o n) hcov _ hP
  have hb := bijective_etaleModuleRestriction_map_extensionByZero (ZMod (ℓ ^ (r + 1))) n
    (unitSheaf (X := Y) (ℓ ^ (r + 1))) (RU.obj F')
  have hu := etaleModuleExtensionByZeroRestrictScalars_unit (ZMod.castHom h (ZMod ℓ)) n F'
  have hu' : RU.map (adj'.unit.app F') ≫
      (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map (θ.inv.app F') =
        adj.unit.app (RU.obj F') :=
    (congrArg (· ≫ (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map (θ.inv.app F'))
      hu.symm).trans ((Category.assoc _ _ _).trans ((congrArg (adj.unit.app (RU.obj F') ≫ ·)
        (((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map_comp _ _).symm.trans
          ((congrArg (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map
            (θ.hom_inv_id_app F')).trans
              ((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map_id _)))).trans
        (Category.comp_id _)))
  have hφ := flagUnit_comp_flagSheafReduction h D wU
  have hιw : ι.hom ≫ wU = nρ ≫ RU.map ι'.hom := ι.hom_inv_id_assoc _
  have hL : (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map
      (z ≫ (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map φ) =
        nρ ≫ RU.map ι'.hom ≫ RU.map (flagUnit (N := ℓ) D) ≫ adj.unit.app (RU.obj F') := by
    rw [CategoryTheory.Functor.map_comp, hz]
    simp only [Category.assoc]
    rw [adj.unit_naturality, ← Category.assoc (flagUnit D), hφ, Category.assoc,
      ← Category.assoc ι.hom, hιw, Category.assoc]
  have hR : (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map
      (ρY ≫ RY.map z' ≫ θ.inv.app F') =
        nρ ≫ RU.map ι'.hom ≫ RU.map (flagUnit (N := ℓ) D) ≫ adj.unit.app (RU.obj F') := by
    have h1 : (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map
        (ρY ≫ RY.map z' ≫ θ.inv.app F') =
          nρ ≫ RU.map ((etaleModuleRestriction.{u, 0} (ZMod ℓ) n).map z') ≫
            (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map (θ.inv.app F') :=
      ((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map_comp _ _).trans
        (congrArg (nρ ≫ ·) ((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map_comp _ _))
    refine h1.trans ?_
    rw [hz', CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    exact congrArg (nρ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (RU.map ι'.hom ≫ ·)
      ((Category.assoc _ _ _).trans (congrArg (RU.map (flagUnit (N := ℓ) D) ≫ ·) hu'))))
  have key : z ≫ (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map φ =
      ρY ≫ RY.map z' ≫ θ.inv.app F' := hb.1 (hL.trans hR.symm)
  have hzsq : z ≫ ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map φ ≫
      θ.hom.app F') = ρY ≫ RY.map z' := by
    rw [← Category.assoc, key, Category.assoc, Category.assoc, θ.inv_hom_id_app]
    exact Category.comp_id (ρY ≫ RY.map z')
  have hzx : ExtSq RY ρY ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (r + 1))) n).map φ ≫
      θ.hom.app F') (Ext.mk₀ z) (Ext.mk₀ z') := ExtSq.mk₀ hzsq
  show ExtSq RY ρY ρY (kummerPointClass hζ hN fY n D z) (kummerPointClass hζ' hℓ fY n D z')
  unfold kummerPointClass
  exact hzx.comp hext (zero_add _)

end Stacks.EtaleCohomology.KummerFlag

end

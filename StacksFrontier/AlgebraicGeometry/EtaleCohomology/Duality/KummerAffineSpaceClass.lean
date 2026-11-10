module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineCohomology
public import StacksFrontier.RingTheory.Localization.AwayPrimeUnits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kummer classes of coordinates of affine space

Let `K` be an algebraically closed field, `ℓ ≥ 2` invertible in `K` and `ζ` a primitive `ℓ`-th root
of unity. On affine space `𝔸^n_K`:

* `H¹(𝔸^n, ℤ/ℓ) = 0` (`subsingleton_ext_one_unitSheaf_affineSpace`): by the Kummer sequence,
  `Pic(𝔸^n) = 0` and every unit of `K[x_0, …, x_{n-1}]` is a constant, hence an `ℓ`-th power;
* a prime function `f` on an affine scheme all of whose units are `ℓ`-th powers is not an
  `ℓ`-th power up to a unit on `D(f)` (`not_exists_pow_eq_unit_basicOpen`), so its Kummer class in
  `H¹(D(f), ℤ/ℓ)` is nonzero (`kummerUnitClass_ne_zero_of_not_exists_pow`);
* the Kummer divisor class `δ(a)` of a unit `a` on an open `V ⊆ U` is nonzero once `κ(a) ≠ 0` and
  `H¹(U, ℤ/ℓ) = 0` (`kummerDivisorClass_ne_zero`): in the long exact sequence of
  `0 → j_! j⁻¹ Λ → Λ → i_* i⁻¹ Λ → 0` the class of `δ(a)` comes from `j_!(κ(a))`, which can only
  die if it comes from `H¹(U, ℤ/ℓ)`, and `j_!` is injective on `Ext` by the adjunction
  `j_! ⊣ j⁻¹`.

## Main results

* `Stacks.EtaleCohomology.KummerFlag.subsingleton_ext_one_unitSheaf_affineSpace`
* `Stacks.EtaleCohomology.KummerFlag.kummerUnitClass_ne_zero_of_not_exists_pow`
* `Stacks.EtaleCohomology.KummerFlag.kummerDivisorClass_ne_zero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.KummerFlag

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section AffineSpace

variable (K : Type u) [Field K] (n : ℕ)

/-- The global functions of affine `n`-space are the polynomials in `n` variables. -/
def affineSpaceGlobalSectionsEquiv :
    Γ(𝔸(ULift.{u} (Fin n); Spec (.of K)), ⊤) ≃+* MvPolynomial (ULift.{u} (Fin n)) K :=
  ((Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of K)).symm.op) ≪≫
    Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin n)) K))).commRingCatIsoToRingEquiv

/-- `affineSpaceGlobalSectionsEquiv` sends the `j`-th coordinate to the variable `X j`. -/
theorem affineSpaceGlobalSectionsEquiv_coord (j : ULift.{u} (Fin n)) :
    affineSpaceGlobalSectionsEquiv K n (AffineSpace.coord (Spec (.of K)) j) = MvPolynomial.X j := by
  change (Scheme.ΓSpecIso _).hom ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of K)).inv.appTop
    (AffineSpace.coord _ j)) = _
  rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply]

/-- The global functions of affine `n`-space form a domain. -/
instance isDomain_affineSpace_globalSections :
    IsDomain Γ(𝔸(ULift.{u} (Fin n); Spec (.of K)), ⊤) :=
  (affineSpaceGlobalSectionsEquiv K n).toMulEquiv.isDomain _

/-- Each coordinate of affine `n`-space is a prime global function. -/
theorem prime_affineSpace_coord (j : ULift.{u} (Fin n)) :
    Prime (AffineSpace.coord (Spec (.of K)) j : Γ(𝔸(ULift.{u} (Fin n); Spec (.of K)), ⊤)) := by
  rw [← MulEquiv.prime_iff (affineSpaceGlobalSectionsEquiv K n).toMulEquiv]
  change Prime (affineSpaceGlobalSectionsEquiv K n (AffineSpace.coord _ j))
  rw [affineSpaceGlobalSectionsEquiv_coord]
  exact MvPolynomial.X_prime

/-- Every unit of `K[x_0, …, x_{n-1}]` is an `ℓ`-th power, `K` being algebraically closed. -/
theorem exists_pow_eq_units_affineSpace [IsAlgClosed K] {ℓ : ℕ} (hℓ : 0 < ℓ)
    (a : (Γ(𝔸(ULift.{u} (Fin n); Spec (.of K)), ⊤))ˣ) : ∃ b, b ^ ℓ = a := by
  have ha := (Units.map (affineSpaceGlobalSectionsEquiv K n).toMonoidHom a).isUnit
  obtain ⟨c, hc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 ha
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hℓ
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hc.1.ne_zero (by rw [← hd, zero_pow hℓ.ne'])
  let b : (Γ(𝔸(ULift.{u} (Fin n); Spec (.of K)), ⊤))ˣ :=
    (Units.mk0 d hd0).map ((affineSpaceGlobalSectionsEquiv K n).symm.toMonoidHom.comp
      (MvPolynomial.C : K →+* MvPolynomial _ K).toMonoidHom)
  refine ⟨b, Units.ext ?_⟩
  apply (affineSpaceGlobalSectionsEquiv K n).injective
  change affineSpaceGlobalSectionsEquiv K n
      ((affineSpaceGlobalSectionsEquiv K n).symm (MvPolynomial.C d) ^ ℓ) =
    affineSpaceGlobalSectionsEquiv K n a
  rw [map_pow, RingEquiv.apply_symm_apply, ← map_pow, hd]
  exact hc.2.symm

/-- `H¹(𝔸^n, 𝐆_m) = Pic(𝔸^n) = 0`. -/
theorem subsingleton_sheafH_one_multiplicative_affineSpace :
    Subsingleton (Sheaf.H.{u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} 𝔸(ULift.{u} (Fin n); Spec (.of K))) 1) :=
  have : Subsingleton (Stacks.Picard.ofScheme 𝔸(ULift.{u} (Fin n); Spec (.of K))) :=
    Stacks.PicardGroup.subsingleton_of_iso (Scheme.topIso _)
      (Stacks.PicardUFD.subsingleton_picardGroup_open_affineSpace K (ULift.{u} (Fin n)) ⊤)
  (Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u}
    𝔸(ULift.{u} (Fin n); Spec (.of K))).toEquiv.subsingleton

/-- **`H¹(𝔸^n, μ_ℓ) = 0`** for `ℓ` invertible in the algebraically closed field `K`. -/
theorem subsingleton_sheafH_one_rootsOfUnity_affineSpace [IsAlgClosed K] {ℓ : ℕ} (hℓ0 : 0 < ℓ)
    (hℓ : IsUnit (ℓ : K)) :
    Subsingleton (Sheaf.H.{u + 1}
      (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} 𝔸(ULift.{u} (Fin n); Spec (.of K)) ℓ) 1) := by
  have hX := Purity.isUnit_natCast_globalSections_of_over
    (𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K)) hℓ
  have hinj := Stacks.Kummer.injective_sheafH_map_rootsOfUnityι_one.{u + 1, u, u + 1}
    𝔸(ULift.{u} (Fin n); Spec (.of K)) hℓ0.ne' hX
    (Stacks.Kummer.surjective_sheafH_map_powMap_zero.{u + 1, u, u + 1} _ ℓ
      (exists_pow_eq_units_affineSpace K n hℓ0))
  have := subsingleton_sheafH_one_multiplicative_affineSpace K n
  exact hinj.subsingleton

/-- **`H¹(𝔸^n, ℤ/ℓ) = 0`**, as `Ext¹(Λ, Λ)`. -/
theorem subsingleton_ext_one_unitSheaf_affineSpace [IsAlgClosed K] {ℓ : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : IsUnit (ℓ : K)) :
    Subsingleton (Ext (unitSheaf (X := 𝔸(ULift.{u} (Fin n); Spec (.of K))) ℓ)
      (unitSheaf (X := 𝔸(ULift.{u} (Fin n); Spec (.of K))) ℓ) 1) := by
  have hℓ0 : ℓ ≠ 0 := ne_zero_of_isUnit hℓ
  have := subsingleton_sheafH_one_rootsOfUnity_affineSpace K n (Nat.pos_of_ne_zero hℓ0) hℓ
  exact (Stacks.Picard.extRootsOfUnityAddEquiv
    (𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K)) hζ hℓ0 1).toEquiv.subsingleton

end AffineSpace

section NotPow

/-- **A prime function is not an `ℓ`-th power up to a unit on its basic open**, `ℓ ≥ 2`, when every
unit of the affine scheme is an `ℓ`-th power. -/
theorem not_exists_pow_eq_unit_basicOpen {X : Scheme.{u}} [IsAffine X] [IsDomain Γ(X, ⊤)]
    {f : Γ(X, ⊤)} (hf : Prime f) {ℓ : ℕ} (hℓ : 1 < ℓ)
    (hroot : ∀ a : (Γ(X, ⊤))ˣ, ∃ b, b ^ ℓ = a) :
    ¬ ∃ b : (Γ(X.basicOpen f, ⊤))ˣ, b ^ ℓ = (isUnit_ι_appTop_basicOpen f).unit := by
  rintro ⟨b, hb⟩
  let _ : Algebra Γ(X, ⊤) Γ(X.basicOpen f, ⊤) := (X.basicOpen f).ι.appTop.hom.toAlgebra
  have : IsLocalization.Away f Γ(X.basicOpen f, ⊤) := Γ_restrict_isLocalization X f
  have hu : (isUnit_ι_appTop_basicOpen f).unit =
      Stacks.LocalizationAway.awayUnit (p := f) Γ(X.basicOpen f, ⊤) := Units.ext rfl
  obtain ⟨a, m, hm⟩ := Stacks.LocalizationAway.exists_units_eq_mul_zpow hf
    Γ(X.basicOpen f, ⊤) b
  obtain ⟨c, hc⟩ := hroot a
  set w := Stacks.LocalizationAway.awayUnit (p := f) Γ(X.basicOpen f, ⊤)
  set φ := Units.map (algebraMap Γ(X, ⊤) Γ(X.basicOpen f, ⊤) : Γ(X, ⊤) →* Γ(X.basicOpen f, ⊤))
  have hbw : b ^ ℓ = w := hb.trans hu
  have h1 : w = φ a ^ ℓ * w ^ (m * (ℓ : ℤ)) := by
    rw [zpow_mul, zpow_natCast, ← mul_pow, ← hm, hbw]
  have h2 : w ^ ((1 : ℤ) - m * ℓ) = φ (a ^ ℓ) := by
    rw [map_pow, zpow_sub, zpow_one]
    nth_rewrite 1 [h1]
    exact mul_inv_cancel_right _ _
  have h3 := Stacks.LocalizationAway.zpow_eq_zero_of_awayUnit_zpow_eq hf
    Γ(X.basicOpen f, ⊤) (a ^ ℓ) _ h2
  have h4 := Int.eq_one_of_dvd_one (Int.natCast_nonneg ℓ) ⟨m, by linarith⟩
  omega

end NotPow

section Classes

variable {k : Type u} [Field k] {N : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : k))

/-- **The Kummer class of a unit which is not an `N`-th power is nonzero.** -/
@[sga "7 IX 9.4.3" "special case"]
theorem kummerUnitClass_ne_zero_of_not_exists_pow {V : Scheme.{u}} (fV : V ⟶ Spec (.of k))
    (a : (Γ(V, ⊤))ˣ) (ha : ¬ ∃ b : (Γ(V, ⊤))ˣ, b ^ N = a) : kummerUnitClass hζ hN fV a ≠ 0 := by
  intro h0
  have hN0 := ne_zero_of_isUnit hN
  have hδ : Stacks.Kummer.kummerδ.{u + 1, u, u + 1} V hN0
      (Stacks.Kummer.isUnit_natCast_globalSections V N fV hN) 0 (unitH0Class a) = 0 := by
    have := congrArg (Stacks.Picard.extRootsOfUnityAddEquiv fV hζ hN0 1) h0
    rwa [kummerUnitClass, AddEquiv.apply_symm_apply, map_zero] at this
  obtain ⟨y, hy⟩ := (Stacks.Kummer.mem_range_sheafH_map_powMap_iff.{u + 1, u, u + 1} V hN0
    (Stacks.Kummer.isUnit_natCast_globalSections V N fV hN) 0 (unitH0Class a)).2 hδ
  let e := Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} V) (isTerminalEtaleMkId V)
  obtain ⟨b, hb⟩ := Stacks.Kummer.ofUnit_surjective.{u, u + 1} (e y)
  refine ha ⟨b, Stacks.Kummer.ofUnit_injective.{u, u + 1} (X := V) (U := Scheme.Etale.mk (𝟙 V)) ?_⟩
  have e1 := congrArg e hy
  rw [← Sheaf.H.equiv₀_naturality, ← hb, Stacks.Kummer.powMap_app_ofUnit] at e1
  exact e1.trans (AddEquiv.apply_symm_apply e _)

variable {U V W : Scheme.{u}} (fU : U ⟶ Spec (.of k)) (j : V ⟶ U) [IsOpenImmersion j]
  (i : W ⟶ U) [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ)

/-- **The Kummer divisor class is nonzero** when the Kummer class of the unit is nonzero and
`H¹(U, ℤ/N) = 0`. -/
theorem kummerDivisorClass_ne_zero
    (hU : Subsingleton (Ext (unitSheaf (X := U) N) (unitSheaf (X := U) N) 1)) (a : (Γ(V, ⊤))ˣ)
    (hκ : kummerUnitClass hζ hN (j ≫ fU) a ≠ 0) :
    kummerDivisorClass hζ hN fU j i hij a ≠ 0 := by
  intro h0
  have := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
  let adj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j
  let w : Ext ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj (unitSheaf (X := U) N))
      ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj (unitSheaf (X := U) N)) 1 :=
    (Ext.mk₀ (restrictionUnitSheafIso (N := N) j).hom).comp
      ((kummerUnitClass hζ hN (j ≫ fU) a).comp
        (Ext.mk₀ (restrictionUnitSheafIso (N := N) j).inv) (add_zero 1)) (zero_add 1)
  have hS := divisorShortComplex_shortExact (N := N) j i hij
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS (unitSheaf (X := U) N)
    (Stacks.ExtAdjunction.extMap adj _ (unitSheaf (X := U) N) 1 w) (by norm_num) h0
  rw [@Subsingleton.elim _ hU x₂ 0, Ext.comp_zero] at hx₂
  have hw : w = 0 := (Stacks.ExtAdjunction.extMap_bijective adj _ _ 1).1
    (hx₂.symm.trans (map_zero _).symm)
  apply hκ
  have e : kummerUnitClass hζ hN (j ≫ fU) a =
      (Ext.mk₀ (restrictionUnitSheafIso (N := N) j).inv).comp
      (w.comp (Ext.mk₀ (restrictionUnitSheafIso (N := N) j).hom) (add_zero 1)) (zero_add 1) := by
    simp only [w, Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_mk₀_id,
      Ext.mk₀_comp_mk₀_assoc]
  rw [e, hw, Ext.zero_comp, Ext.comp_zero]

end Classes

end Stacks.EtaleCohomology.KummerFlag

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SmoothProperPoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelTraceValues
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCupProductLevel

/-!
# Poincaré duality with `ℤ/ℓⁿ` coefficients on a connected smooth proper variety

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k`, `N = ℓⁿ⁺¹` and `Y`
connected, smooth of relative dimension `d` and proper over `k`. For every injective trace
`t : H^{2d}(Y, ℤ/N) → ℤ/N` and every locally constant sheaf `F` of finite type of
`ℤ/N`-modules the Yoneda pairing

`Ext^i(ℤ/N, F) × Ext^{2d-i}(F, ℤ/N) → H^{2d}(Y, ℤ/N) → ℤ/N`

is perfect (`Stacks.EtaleCohomology.isDualityPerfect_levelPow_of_isFiniteTypeLocallyConstant`).

This is the dévissage `Stacks.EtaleCohomology.LevelChange.isDualityPerfect_of_coextend` along
`0 → F[ℓ] → F → F/F[ℓ] → 0`, with inputs:

* duality with `ℤ/ℓ` coefficients at the lisse sheaf `F[ℓ]`
  (`isDualityPerfect_of_isFiniteTypeLocallyConstant_of_topCohomologyPointClass`), for the trace
  induced by `t` on `H^{2d}(Y, ℤ/ℓ)` through `ℤ/ℓ ≅ ℤ/N[ℓ]`. This trace is injective: it sends
  the class `z` with `π ∘ z = x ∘ π`, for `x` a generator of `H^{2d}(Y, ℤ/N) ≅ ℤ/N` (the
  computation `hA1` of the top cohomology), to `t(ℓⁿ x) ≠ 0`, and `H^{2d}(Y, ℤ/ℓ)` has `ℓ`
  elements; its values lie in `ℤ/ℓ ⊆ ℤ/N`
  (`Stacks.EtaleCohomology.LevelChange.exists_comp_zmodPowEmbedding_eq`);
* the vanishing of `H^{2d+1}(Y, F[ℓ])` (Tag 095U) and of `Ext^{2d+1}(F, ℤ/N)`
  (`Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_pow_right_of_isFiniteTypeLocallyConstant`).

This is the finite-level Poincaré duality of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.injective_of_natCard_eq_prime`.
* `Stacks.EtaleCohomology.isDualityPerfect_levelPow_of_isFiniteTypeLocallyConstant`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- A homomorphism out of a group of prime order which is nonzero somewhere is injective. -/
theorem injective_of_natCard_eq_prime {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H)
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) {x : G} (hx : φ x ≠ 0) :
    Function.Injective φ := by
  have : Fact (Nat.card G).Prime := ⟨hG ▸ hp⟩
  rw [injective_iff_map_eq_zero]
  intro y hy
  rcases φ.ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact (AddSubgroup.mem_bot.1 (h ▸ (AddMonoidHom.mem_ker.2 hy)))
  · exact absurd (AddMonoidHom.mem_ker.1 (h ▸ AddSubgroup.mem_top x)) hx

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [IsAlgClosed k]

/-- **Poincaré duality with `ℤ/ℓⁿ⁺¹` coefficients on a connected smooth proper variety.** Let
`k` be algebraically closed, `ℓ` a prime invertible in `k`, `Y` connected, smooth of relative
dimension `d` and proper over `k`, and `N = ℓⁿ⁺¹`. Given duality on a dense open for good traces
(`hcore`), the computation of the top cohomology with `ℤ/ℓ` coefficients on the class of a point
(`hD1`) and `H^{2d}(Y, ℤ/ℓᵐ⁺¹) ≅ ℤ/ℓᵐ⁺¹` (`hA1`), the Yoneda pairing
`Ext^i(ℤ/N, F) × Ext^{2d-i}(F, ℤ/N) → ℤ/N` is perfect for every injective trace `t` and every
locally constant sheaf `F` of finite type of `ℤ/N`-modules. -/
theorem isDualityPerfect_levelPow_of_isFiniteTypeLocallyConstant (hℓ : IsUnit (ℓ : k))
    (hcore : IsUnit (ℓ : k) → LocalPurity ℓ k → PoincareDualityCore ℓ k)
    (hD1 : TopCohomologyPointClass ℓ k)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsProper f] (d : ℕ)
    [SmoothOfRelativeDimension d f] [ConnectedSpace Y]
    (hA1 : ∀ m : ℕ, Nonempty (Ext (unitSheaf (X := Y) (ℓ ^ (m + 1))) (unitSheaf (ℓ ^ (m + 1)))
      (2 * d) ≃+ ZMod (ℓ ^ (m + 1))))
    (n : ℕ) (t : Ext (unitSheaf (X := Y) (ℓ ^ (n + 1))) (unitSheaf (ℓ ^ (n + 1))) (2 * d) →+
      ZMod (ℓ ^ (n + 1))) (ht : Function.Injective t)
    (F : EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) Y)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      Y.smallEtaleTopology F) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) (ℓ ^ (n + 1))) (unitSheaf (ℓ ^ (n + 1))) (2 * d) t
      F := by
  have hp : ℓ.Prime := Fact.out
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : CompactSpace Y := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian Y := ⟨⟩
  have : IrreducibleSpace Y := irreducibleSpace_of_smooth_of_connectedSpace f
  obtain ⟨y₀⟩ := (‹ConnectedSpace Y›).toNonempty
  have : Nonempty Y := ⟨y₀⟩
  have hdim : topologicalKrullDim Y ≤ d :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d f).le
  have hpurity : LocalPurity ℓ k := Purity.localPurity (k := k) (ℓ := ℓ) hℓ
  have hdv := LevelChange.dvd_pow_self_of_neZero (p := ℓ) (m := n + 1)
  have hD : PowExact ℓ (n + 1) (unitSheaf (X := Y) (ℓ ^ (n + 1))) :=
    powExact_constantSheaf_zmod ℓ (n + 1) Y
  obtain ⟨-, hcard⟩ := natCard_ext_unitSheaf_of_exists_isGoodTrace ℓ hpurity (hcore hℓ hpurity) f
    d (exists_injective_isGoodTrace hℓ hD1 f d)
  let eD := LevelChange.unitSheafCoextendIso Y ℓ (n + 1)
  let t₀ := Ext.transportTrace (LevelChange.levelTrace Y hdv t) (Iso.refl _) eD.symm
  have ht₀ : Function.Injective t₀ := by
    obtain ⟨e⟩ := hA1 n
    let x₀ := e.symm 1
    obtain ⟨z, hz⟩ := (LevelChange.extMap_bijective Y hdv (unitSheaf (X := Y) ℓ) (2 * d)).2
      (x₀.comp (Ext.mk₀ (LevelChange.reduction Y hdv)) (add_zero _))
    refine injective_of_natCard_eq_prime t₀ hp hcard (x := z) ?_
    have hval : t₀ z = t ((ℓ ^ n) • x₀) := by
      have hred := LevelChange.reduction_comp_inclusion Y (LevelChange.pow_pred_mul_self ℓ (n + 1))
      have hinc := LevelChange.map_unitSheafCoextendIso_comp_torsionCounit Y ℓ (n + 1)
      rw [LevelChange.extMap_apply] at hz
      show LevelChange.levelTrace Y hdv t ((Ext.mk₀ (𝟙 _)).comp
        (z.comp (Ext.mk₀ eD.hom) (add_zero _)) (zero_add _)) = _
      rw [LevelChange.levelTrace_apply, Ext.mk₀_id_comp, Stacks.ExtAdjunction.extMap_apply,
        Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
        Ext.mk₀_comp_mk₀]
      congr 1
      rw [hinc, ← Ext.comp_assoc_of_third_deg_zero, hz, Ext.comp_assoc_of_third_deg_zero,
        Ext.mk₀_comp_mk₀, hred, LevelChange.mk₀_nsmul, LevelChange.comp_nsmul, Ext.comp_mk₀_id,
        Nat.add_sub_cancel]
    rw [hval]
    intro h0
    have h1 : (ℓ ^ n) • x₀ = 0 := ht (h0.trans t.map_zero.symm)
    have h2 := congrArg e h1
    rw [map_nsmul, map_zero, AddEquiv.apply_symm_apply, nsmul_eq_mul, mul_one,
      ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd (pow_pos hp.pos _) h2)
      (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self n)))
  have hkill : ∀ {A : EtaleModules.{u, 0} (ZMod ℓ) Y} {j : ℕ} (v : Ext A (unitSheaf (X := Y) ℓ) j),
      ℓ • v = 0 := fun v => LevelChange.nsmul_eq_zero_of_nsmul_id
    (LevelChange.nsmul_id_unitSheaf (X := Y) (N := ℓ)) v
  obtain ⟨t'', ht''⟩ := LevelChange.exists_comp_zmodPowEmbedding_eq ℓ (n + 1) hkill t₀
  have ht''inj : Function.Injective t'' := fun a b hab => ht₀ (by
    rw [← ht'', AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hab])
  refine LevelChange.isDualityPerfect_of_coextend Y hD t
    (fun G => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      Y.smallEtaleTopology G)
    (fun G hG => LevelChange.isFiniteTypeLocallyConstant_cokernel_torsionCounit Y G hG)
    (fun G hG => ?_)
    (fun G _ => subsingleton_ext_unitSheaf_of_proper f d hdim _ _
      (by omega))
    (fun G hG => subsingleton_ext_unitSheaf_pow_right_of_isFiniteTypeLocallyConstant f d hdim G hG
      _ (by omega)) F hF
  refine (Ext.isDualityPerfect_transport_iff (LevelChange.levelTrace Y hdv t) (Iso.refl _)
    eD.symm _).2 ?_
  show Ext.IsDualityPerfect _ _ _ t₀ _
  rw [← ht'']
  refine (Ext.isDualityPerfect_comp_iff_of_injective t'' _
    (LevelChange.injective_zmodPowEmbedding ℓ (n + 1)) _ fun j φ =>
      LevelChange.exists_comp_zmodPowEmbedding_eq ℓ (n + 1) hkill φ).2 ?_
  exact isDualityPerfect_of_isFiniteTypeLocallyConstant_of_topCohomologyPointClass ℓ hℓ hcore hD1
    f d t'' ht''inj _ (LevelChange.isFiniteTypeLocallyConstant_coextend Y G hG)

end Stacks.EtaleCohomology

end

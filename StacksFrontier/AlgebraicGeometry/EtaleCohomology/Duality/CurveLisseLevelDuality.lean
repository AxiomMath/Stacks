module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLisseDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCupProductLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelTorsionLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelTorsionUnitSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelTraceValues
public import StacksFrontier.CategoryTheory.Abelian.PowExactTorsionLift

/-!
# Poincaré duality for lisse `ℤ/ℓᵐ`-sheaves on an open of a smooth proper curve

This file transports Poincaré duality on an open `V` of a smooth proper curve from coefficients
`ℤ/ℓ` (`Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_lisse_of_curve`) to coefficients
`ℤ/ℓᵐ`, along the dévissage `Stacks.EtaleCohomology.LevelChange.isDualityPerfect_of_coextend`. The
first step is that the `ℓ`-torsion of `j_! G` is `j_!` of the `ℓ`-torsion of `G`
(`Stacks.EtaleCohomology.LevelChange.nonempty_coextend_extensionByZero_iso`): extension by zero is
exact and commutes with restriction of scalars, so it carries the `ℓ`-torsion kernel of `G` to an
`ℓ`-torsion kernel of `j_! G`, and restriction of scalars along `ℤ/ℓᵐ ↠ ℤ/ℓ` is fully faithful.

The remaining inputs of the dévissage: the `ℓ`-torsion `G[ℓ]` and the quotient `G / G[ℓ]` of a
lisse `G` are lisse (`Stacks.EtaleCohomology.LevelChange.isFiniteTypeLocallyConstant_coextend`),
`j_!` commutes with `F ↦ F / F[ℓ]`, `(ℤ/ℓᵐ)[ℓ] ≅ ℤ/ℓ`
(`Stacks.EtaleCohomology.LevelChange.unitSheafCoextendIso`), and the level trace of an injective
trace on `H²(Y, ℤ/ℓᵐ)` is injective, by counting in `H²(ℤ/ℓ) → H²(ℤ/ℓᵐ) → H²(ℤ/ℓᵐ⁻¹)`.

## Main results

* `Stacks.EtaleCohomology.LevelChange.nonempty_coextend_extensionByZero_iso`.
* `Stacks.EtaleCohomology.LevelChange.nonempty_cokernel_torsionCounit_extensionByZero_iso`.
* `Stacks.EtaleCohomology.injective_levelTrace_of_curve`.
* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_lisse_zmodPow_of_curve`: Poincaré
  duality for lisse `ℤ/ℓᵐ`-sheaves on an open of a smooth proper curve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u w

namespace Stacks.EtaleCohomology.LevelChange

attribute [local instance] moduleCat_hasLimitsOfSize

variable {p : ℕ} [Fact p.Prime] {m : ℕ} [NeZero m]

/-- Extension by zero carries the `p`-torsion kernel of `G` to a `p`-torsion kernel of `j_! G`. -/
theorem isTorsionKernel_extensionByZero_map_torsionCounit {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (G : EtaleModules.{u, 0} (ZMod (p ^ m)) U) :
    IsTorsionKernel p
      (((etaleModuleExtensionByZeroRestrictScalars
          (ZMod.castHom (dvd_pow_self_of_neZero (p := p) (m := m)) (ZMod p)) j).app
          ((coextend U (dvd_pow_self_of_neZero (p := p) (m := m))).obj G)).inv ≫
        (etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j).map (torsionCounit U G)) := by
  let eR := (etaleModuleExtensionByZeroRestrictScalars
    (ZMod.castHom (dvd_pow_self_of_neZero (p := p) (m := m)) (ZMod p)) j).app
    ((coextend U (dvd_pow_self_of_neZero (p := p) (m := m))).obj G)
  have h := (isTorsionKernel_torsionCounit U G).map
    (etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j)
  exact ⟨mono_comp _ _, by rw [Category.assoc, h.comp_eq_zero, comp_zero],
    fun T t ht => by
      obtain ⟨s, hs⟩ := h.exists_lift t ht
      exact ⟨s ≫ eR.hom, by rw [Category.assoc, eR.hom_inv_id_assoc, hs]⟩⟩

/-- **The `p`-torsion of `j_! G` is `j_!` of the `p`-torsion of `G`**, for an étale `j : U → X` and
a sheaf `G` of `ℤ/pᵐ`-modules on `U`. -/
theorem nonempty_coextend_extensionByZero_iso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (G : EtaleModules.{u, 0} (ZMod (p ^ m)) U) :
    Nonempty ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j).obj G) ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod p) j).obj
        ((coextend U (dvd_pow_self_of_neZero (p := p) (m := m))).obj G)) := by
  have hdv := dvd_pow_self_of_neZero (p := p) (m := m)
  let jm := etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j
  let eR := (etaleModuleExtensionByZeroRestrictScalars (ZMod.castHom hdv (ZMod p)) j).app
    ((coextend U hdv).obj G)
  have h₁ := isTorsionKernel_extensionByZero_map_torsionCounit j G
  have h₂ := isTorsionKernel_torsionCounit X (jm.obj G)
  obtain ⟨s, hs⟩ := h₂.exists_lift (eR.inv ≫ jm.map (torsionCounit U G)) h₁.comp_eq_zero
  have : IsIso s := h₁.isIso_of_comp h₂ s hs
  obtain ⟨s', hs'⟩ := (restrict X hdv).map_surjective (inv s)
  have : IsIso ((restrict X hdv).map s') := by rw [hs']; infer_instance
  have : IsIso s' := isIso_of_fully_faithful (restrict X hdv) s'
  exact ⟨asIso s'⟩

/-- The `p`-torsion of `F ≅ j_! G`, for a finite type locally constant `G`, is `j_!` of a finite
type locally constant sheaf of `ℤ/p`-modules. -/
theorem exists_isFiniteTypeLocallyConstant_coextend_iso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    {G : EtaleModules.{u, 0} (ZMod (p ^ m)) U}
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (p ^ m)) U.smallEtaleTopology G)
    {F : EtaleModules.{u, 0} (ZMod (p ^ m)) X}
    (e : F ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j).obj G) :
    ∃ H : EtaleModules.{u, 0} (ZMod p) U,
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod p) U.smallEtaleTopology H ∧
        Nonempty ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj F ≅
          (etaleModuleExtensionByZero.{u, 0} (ZMod p) j).obj H) := by
  obtain ⟨c⟩ := nonempty_coextend_extensionByZero_iso j G
  exact ⟨_, isFiniteTypeLocallyConstant_coextend _ G hG,
    ⟨(coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).mapIso e ≪≫ c⟩⟩

section Unit

variable (X : Scheme.{u})

/-- **`(ℤ/pᵐ) / (ℤ/pᵐ)[p] ≅ ℤ/pᵐ⁻¹`**: on the flat sheaf `ℤ/pᵐ`, the quotient by the
`p`-torsion is the cokernel of `pᵐ⁻¹`, through the epimorphism `ℤ/pᵐ ↠ (ℤ/pᵐ)[p]` given by
`pᵐ⁻¹`. -/
theorem nonempty_cokernel_torsionCounit_unitSheaf_iso (hdv : p ^ (m - 1) ∣ p ^ m) :
    Nonempty (cokernel (torsionCounit X (unitSheaf (X := X) (p ^ m))) ≅
      (restrict X hdv).obj (unitSheaf (X := X) (p ^ (m - 1)))) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hk : IsTorsionKernel (p ^ 1) (torsionCounit X (unitSheaf (X := X) (p ^ m))) := by
    rw [pow_one]
    exact isTorsionKernel_torsionCounit X _
  have hX := etaleModules_pow_nsmul_id (unitSheaf (X := X) (p ^ m))
  have hc := hk.isColimitTorsionLift hX hm (powExact_constantSheaf_zmod p m X)
  have : Epi (hk.torsionLift hX hm) := epi_of_isColimit_cofork hc
  have hr := (reductionShortComplex_exact X hdv).gIsCokernel
  exact ⟨(cokernelEpiComp (hk.torsionLift hX hm) _).symm ≪≫
    cokernelIsoOfEq (hk.torsionLift_comp hX hm) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hr⟩

end Unit

section Torsion

variable {C : Type*} [Category C] [Abelian C]

/-- A torsion kernel stays one after composing with an isomorphism of its target. -/
theorem isTorsionKernel_comp_iso {n : ℕ} {A X X' : C} {e : A ⟶ X} (h : IsTorsionKernel n e)
    (i : X ≅ X') : IsTorsionKernel n (e ≫ i.hom) := by
  have := h.mono
  refine ⟨mono_comp _ _, ?_, fun T t ht => ?_⟩
  · rw [Category.assoc, Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp i.hom,
      ← Preadditive.nsmul_comp, ← Category.assoc, h.comp_eq_zero, zero_comp]
  · obtain ⟨s, hs⟩ := h.exists_lift (t ≫ i.inv) (by
      rw [Category.assoc, Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp i.inv,
        ← Preadditive.nsmul_comp, ← Category.assoc, ht, zero_comp])
    exact ⟨s, by rw [← Category.assoc, hs, Category.assoc, i.inv_hom_id, Category.comp_id]⟩

/-- Two torsion kernels of the same object have isomorphic cokernels. -/
theorem nonempty_cokernel_iso_of_isTorsionKernel {n : ℕ} {A A' X : C} {e : A ⟶ X}
    {e' : A' ⟶ X} (h : IsTorsionKernel n e) (h' : IsTorsionKernel n e') :
    Nonempty (cokernel e ≅ cokernel e') := by
  obtain ⟨s, hs⟩ := h.exists_lift e' h'.comp_eq_zero
  have := h'.isIso_of_comp h s hs
  exact ⟨(cokernelEpiComp s e).symm ≪≫ cokernelIsoOfEq hs⟩

end Torsion

/-- **`j_!` commutes with `F ↦ F / F[p]`**: for an étale `j : U → X`, a sheaf `G` of
`ℤ/pᵐ`-modules on `U` and `F ≅ j_! G`, the quotient of `F` by its `p`-torsion is `j_!` of the
quotient of `G` by its `p`-torsion. Extension by zero carries the `p`-torsion kernel of `G` to
one of `j_! G` and preserves cokernels. -/
theorem nonempty_cokernel_torsionCounit_extensionByZero_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (G : EtaleModules.{u, 0} (ZMod (p ^ m)) U) {F : EtaleModules.{u, 0} (ZMod (p ^ m)) X}
    (e : F ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j).obj G) :
    Nonempty (cokernel (torsionCounit X F) ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j).obj (cokernel (torsionCounit U G))) := by
  have hdv := dvd_pow_self_of_neZero (p := p) (m := m)
  let jm := etaleModuleExtensionByZero.{u, 0} (ZMod (p ^ m)) j
  let eR := (etaleModuleExtensionByZeroRestrictScalars (ZMod.castHom hdv (ZMod p)) j).app
    ((coextend U hdv).obj G)
  obtain ⟨c⟩ := nonempty_cokernel_iso_of_isTorsionKernel (isTorsionKernel_torsionCounit X F)
    (isTorsionKernel_comp_iso (isTorsionKernel_extensionByZero_map_torsionCounit j G) e.symm)
  exact ⟨c ≪≫ cokernelCompIsIso _ e.inv ≪≫ cokernelEpiComp eR.inv _ ≪≫
    (PreservesCokernel.iso jm _).symm⟩

section Values

/-- **An exact sequence `A → B → C` of finite groups with `#A · #C ≤ #B` starts with an
injection.** -/
theorem injective_of_card_mul_le {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Finite A] [Finite B] [Finite C] (f : A →+ B) (g : B →+ C)
    (hfg : ∀ b, g b = 0 → ∃ a, f a = b) (hcard : Nat.card A * Nat.card C ≤ Nat.card B) :
    Function.Injective f := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have h2 : Nat.card (B ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have h3 : Nat.card g.range ≤ Nat.card C := Finite.card_subtype_le _
  have h4 : Nat.card g.ker ≤ Nat.card f.range :=
    AddSubgroup.card_le_of_le fun b hb => by
      obtain ⟨a, ha⟩ := hfg b hb
      exact ⟨a, ha⟩
  have hC : 0 < Nat.card C := Nat.card_pos
  have h5 : Nat.card A ≤ Nat.card f.range := by
    refine Nat.le_of_mul_le_mul_right ?_ hC
    calc Nat.card A * Nat.card C ≤ Nat.card B := hcard
      _ = Nat.card g.range * Nat.card g.ker := by rw [h1, h2]
      _ ≤ Nat.card C * Nat.card f.range := Nat.mul_le_mul h3 h4
      _ = Nat.card f.range * Nat.card C := mul_comm _ _
  have hb := f.rangeRestrict_surjective.bijective_of_nat_card_le h5
  exact fun x y hxy => hb.1 (Subtype.ext hxy)

/-- Subsingleton `Ext` groups are invariant under isomorphisms of both arguments. -/
theorem subsingleton_ext_of_iso {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    {A A' B B' : C} (e₁ : A ≅ A') (e₂ : B ≅ B') (q : ℕ) [Subsingleton (Ext A' B' q)] :
    Subsingleton (Ext A B q) :=
  ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := B') e₁.inv q).1.comp
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := A) e₂.hom q).1).subsingleton

end Values

end Stacks.EtaleCohomology.LevelChange

namespace Stacks.EtaleCohomology

open LevelChange

variable {ℓ : ℕ} [Fact ℓ.Prime] {m : ℕ} [NeZero m]
  {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

include f in
/-- **The level trace of an injective trace on `H²(Y, ℤ/ℓᵐ)` is injective** on a smooth proper
curve: `H²(Y, ℤ/ℓ) → H²(Y, ℤ/ℓᵐ)`, induced by `ℤ/ℓ = (ℤ/ℓᵐ)[ℓ] ↪ ℤ/ℓᵐ`, is injective, by
counting in the exact sequence `H²(ℤ/ℓ) → H²(ℤ/ℓᵐ) → H²(ℤ/ℓᵐ⁻¹)` of groups of orders `ℓ`,
`ℓᵐ`, `ℓᵐ⁻¹`. -/
theorem injective_levelTrace_of_curve (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := Y) (ℓ ^ m)) (unitSheaf (ℓ ^ m)) 2 →+ ZMod (ℓ ^ m))
    (ht : Function.Injective t) :
    Function.Injective (levelTrace Y (dvd_pow_self_of_neZero (p := ℓ) (m := m)) t) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hdv := dvd_pow_self_of_neZero (p := ℓ) (m := m)
  have hdv' : ℓ ^ (m - 1) ∣ ℓ ^ m := pow_dvd_pow ℓ (Nat.sub_le m 1)
  let Λ := unitSheaf (X := Y) (ℓ ^ m)
  let ε := torsionCounit Y Λ
  let SS := ShortComplex.mk ε (cokernel.π ε) (cokernel.condition ε)
  have hSS : SS.ShortExact := { exact := ShortComplex.exact_cokernel ε }
  have hdiv : ∀ n : ℕ, IsUnit (n : k) → ∀ L : Picard.ofScheme Y,
      Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 0 →
        ∃ M : Picard.ofScheme Y, n • M = L :=
    fun n hn L hL => Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero f _ hn L hL
  have hu : ∀ a : ℕ, IsUnit (((ℓ ^ a : ℕ) : k)) := fun a => by
    simpa using hℓ.pow a
  let eD := (unitSheafCoextendIso Y ℓ m).symm
  obtain ⟨eQ⟩ := nonempty_cokernel_torsionCounit_unitSheaf_iso (p := ℓ) (m := m) Y hdv'
  have hA : Nat.card (Ext Λ SS.X₁ 2) = ℓ :=
    (Nat.card_congr (Equiv.ofBijective _ (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      (X := Λ) ((restrict Y hdv).map eD.hom) 2))).trans
      (natCard_ext_two_restrict f hdv hℓ (hdiv ℓ hℓ))
  have hB : Nat.card (Ext Λ SS.X₂ 2) = ℓ ^ m :=
    Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve f (hu m)
      (hdiv _ (hu m))
  have hC : Nat.card (Ext Λ SS.X₃ 2) = ℓ ^ (m - 1) :=
    (Nat.card_congr (Equiv.ofBijective _ (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      (X := Λ) eQ.hom 2))).trans
      (natCard_ext_two_restrict f hdv' (hu (m - 1)) (hdiv _ (hu (m - 1))))
  have : Finite (Ext Λ SS.X₁ 2) := Nat.finite_of_card_ne_zero (by rw [hA]; exact hp.ne_zero)
  have : Finite (Ext Λ SS.X₂ 2) :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero _ hp.ne_zero)
  have : Finite (Ext Λ SS.X₃ 2) :=
    Nat.finite_of_card_ne_zero (by rw [hC]; exact pow_ne_zero _ hp.ne_zero)
  have hinj : Function.Injective ((Ext.mk₀ ε).postcomp Λ (add_zero 2)) :=
    injective_of_card_mul_le _ ((Ext.mk₀ SS.g).postcomp Λ (add_zero 2))
      (fun b hb => Ext.covariant_sequence_exact₂ Λ hSS b hb)
      (by rw [hA, hB, hC, ← pow_succ', Nat.sub_add_cancel hm])
  have key : ∀ z, levelTrace Y hdv t z =
      t ((LevelChange.extMap Y hdv _ 2 z).comp (Ext.mk₀ ε) (add_zero 2)) := by
    intro z
    rw [levelTrace_apply, Stacks.ExtAdjunction.extMap_apply, LevelChange.extMap_apply,
      Ext.comp_assoc_of_third_deg_zero]
  intro z z' hzz
  rw [key, key] at hzz
  exact (LevelChange.extMap_bijective Y hdv _ 2).1 (hinj (ht hzz))

include f in
/-- **The level trace of an injective trace on `H²(Y, ℤ/ℓᵐ)` factors through `ℤ/ℓ ↪ ℤ/ℓᵐ` by an
injective trace** on `H²(Y, ℤ/ℓ)`, on a smooth proper curve. -/
theorem exists_injective_comp_zmodPowEmbedding_eq_levelTrace (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := Y) (ℓ ^ m)) (unitSheaf (ℓ ^ m)) 2 →+ ZMod (ℓ ^ m))
    (ht : Function.Injective t) :
    ∃ t₁ : Ext (unitSheaf (X := Y) ℓ) (unitSheaf (X := Y) ℓ) 2 →+ ZMod ℓ,
      Function.Injective t₁ ∧ (zmodPowEmbedding ℓ m).comp t₁ =
        Ext.transportTrace (levelTrace Y (dvd_pow_self_of_neZero (p := ℓ) (m := m)) t)
          (Iso.refl _) (unitSheafCoextendIso Y ℓ m).symm := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdv := dvd_pow_self_of_neZero (p := ℓ) (m := m)
  let Λ₁ := unitSheaf (X := Y) ℓ
  let eD := (unitSheafCoextendIso Y ℓ m).symm
  let T := Ext.transportTrace (levelTrace Y hdv t) (Iso.refl Λ₁) eD
  have hT : Function.Injective T :=
    (injective_levelTrace_of_curve f hℓ t ht).comp
      ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
        (Z := (coextend Y hdv).obj (unitSheaf (X := Y) (ℓ ^ m))) (Iso.refl Λ₁).hom 2).1.comp
        (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := Λ₁) eD.inv 2).1)
  obtain ⟨t₁, ht₁⟩ := exists_comp_zmodPowEmbedding_eq ℓ m
    (fun x => nsmul_eq_zero_of_nsmul_id (nsmul_id_unitSheaf (X := Y) (N := ℓ)) x) T
  refine ⟨t₁, fun a b hab => hT ?_, ht₁⟩
  rw [← ht₁, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hab]

include f in
/-- **Poincaré duality for lisse `ℤ/ℓᵐ`-sheaves on an open of a smooth proper curve.** For a
nonempty open `V` of `Y` with finite complement of closed points, every injective trace `t` on
`H²(Y, ℤ/ℓᵐ)` and every finite type locally constant sheaf `G` of `ℤ/ℓᵐ`-modules on `V`, duality
holds on `Y` at `j_! G` with dualizing object `ℤ/ℓᵐ` and `Ext^q_Y(j_! G, ℤ/ℓᵐ) = 0` for `q > 2`.
This is the case `ℤ/ℓ` (`isDualityPerfect_extensionByZero_lisse_of_curve`) pushed through the
dévissage `F ↦ F[ℓ], F / F[ℓ]` (`LevelChange.isDualityPerfect_of_coextend`). -/
theorem isDualityPerfect_extensionByZero_lisse_zmodPow_of_curve (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := Y) (ℓ ^ m)) (unitSheaf (ℓ ^ m)) 2 →+ ZMod (ℓ ^ m))
    (ht : Function.Injective t)
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    (V : Y.Opens) (hV : (V : Set Y) = (↑S : Set Y)ᶜ) [Nonempty V]
    (G : EtaleModules.{u, 0} (ZMod (ℓ ^ m)) V)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ m))
      (V : Scheme).smallEtaleTopology G) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) (ℓ ^ m)) (unitSheaf (ℓ ^ m)) 2 t
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ m)) V.ι).obj G) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ m)) V.ι).obj G)
        (unitSheaf (X := Y) (ℓ ^ m)) q) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdv := dvd_pow_self_of_neZero (p := ℓ) (m := m)
  let jm := etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ m)) V.ι
  let Λ := unitSheaf (X := Y) (ℓ ^ m)
  let Λ₁ := unitSheaf (X := Y) ℓ
  have hD : PowExact ℓ m Λ := powExact_constantSheaf_zmod ℓ m Y
  let eD := (unitSheafCoextendIso Y ℓ m).symm
  let P : ObjectProperty (EtaleModules.{u, 0} (ZMod (ℓ ^ m)) Y) := fun F =>
    ∃ G : EtaleModules.{u, 0} (ZMod (ℓ ^ m)) V, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant
      (ZMod (ℓ ^ m)) (V : Scheme).smallEtaleTopology G ∧ Nonempty (F ≅ jm.obj G)
  have hP : ∀ F, P F → P (cokernel (torsionCounit Y F)) := by
    rintro F ⟨G, hG, ⟨e⟩⟩
    obtain ⟨c⟩ := nonempty_cokernel_torsionCounit_extensionByZero_iso V.ι G e
    exact ⟨_, isFiniteTypeLocallyConstant_cokernel_torsionCounit _ G hG, ⟨c⟩⟩
  let ι := zmodPowEmbedding ℓ m
  have hext : ∀ (A : EtaleModules.{u, 0} (ZMod ℓ) Y) (j : ℕ) (φ : Ext A Λ₁ j →+ ZMod (ℓ ^ m)),
      ∃ ψ : Ext A Λ₁ j →+ ZMod ℓ, ι.comp ψ = φ := fun A j φ =>
    exists_comp_zmodPowEmbedding_eq ℓ m
      (fun x => nsmul_eq_zero_of_nsmul_id (nsmul_id_unitSheaf (X := Y) (N := ℓ)) x) φ
  obtain ⟨t₁, ht₁i, ht₁⟩ := exists_injective_comp_zmodPowEmbedding_eq_levelTrace f hℓ t ht
  have hT1 := fun H hH =>
    isDualityPerfect_extensionByZero_lisse_of_curve f hℓ t₁ ht₁i S hS V hV H hH
  have h₁ : ∀ F, P F → Ext.IsDualityPerfect Λ₁ ((coextend Y hdv).obj Λ) 2
      (levelTrace Y hdv t) ((coextend Y hdv).obj F) := by
    rintro F ⟨G', hG', ⟨e⟩⟩
    obtain ⟨H, hH, ⟨c⟩⟩ := exists_isFiniteTypeLocallyConstant_coextend_iso V.ι hG' e
    refine Ext.isDualityPerfect_of_iso c.symm ?_
    rw [Ext.isDualityPerfect_transport_iff (levelTrace Y hdv t) (Iso.refl Λ₁) eD,
      show Ext.transportTrace (levelTrace Y hdv t) (Iso.refl Λ₁) eD = ι.comp t₁ from ht₁.symm,
      Ext.isDualityPerfect_comp_iff_of_injective t₁ ι (injective_zmodPowEmbedding ℓ m) _
        (hext _)]
    exact (hT1 H hH).1
  have hv : ∀ F, P F → ∀ q, 2 < q → Subsingleton (Ext ((coextend Y hdv).obj F)
      ((coextend Y hdv).obj Λ) q) := by
    rintro F ⟨G', hG', ⟨e⟩⟩ q hq
    obtain ⟨H, hH, ⟨c⟩⟩ := exists_isFiniteTypeLocallyConstant_coextend_iso V.ι hG' e
    have := (hT1 H hH).2 q hq
    exact subsingleton_ext_of_iso c eD q
  have hv₁ : ∀ F, P F → Subsingleton (Ext Λ₁ ((coextend Y hdv).obj F) (2 + 1)) := fun F _ =>
    subsingleton_ext_unitSheaf_of_curve f (IsCurve.topologicalKrullDim_eq_one (f := f)).le _ 3
      (by omega)
  have hG' : P (jm.obj G) := ⟨G, hG, ⟨Iso.refl _⟩⟩
  exact ⟨isDualityPerfect_of_coextend Y hD t P hP h₁ hv₁
      (fun F hF => subsingleton_ext_of_coextend Y hD P hP hv F hF 3 (by omega)) _ hG',
    fun q hq => subsingleton_ext_of_coextend Y hD P hP hv _ hG' q hq⟩

end Stacks.EtaleCohomology

end

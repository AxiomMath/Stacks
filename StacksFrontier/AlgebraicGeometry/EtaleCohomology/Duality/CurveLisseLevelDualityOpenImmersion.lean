module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLisseLevelDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageAlongMorphism
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic

/-!
# Poincaré duality for lisse `ℤ/ℓᵐ`-sheaves along an open immersion into a smooth proper curve

Let `Y` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k`, `V : U ⟶ Y` an open immersion from a nonempty scheme and `G` a locally constant sheaf of
finite type of `ℤ/ℓᵐ`-modules on `U`. Then duality holds on `Y` at `V_! G` with dualizing object
`ℤ/ℓᵐ`, and `Ext^q_Y(V_! G, ℤ/ℓᵐ) = 0` for `q > 2`
(`Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_lisse_zmodPow_of_isOpenImmersion`).

This is `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_lisse_zmodPow_of_curve`, stated
for the open subscheme `W` of `Y` with the finite complement as hypothesis, transported along
`U ≅ W`: the complement of the nonempty open `W` of the integral one-dimensional scheme `Y` is a
finite set of closed points, `V_! G ≅ W_! (W^{-1} V_! G)`, and `W^{-1} V_! G` is the inverse
image of `G` along `W ≅ U`, hence lisse. The open immersion is the form in which the base
change `U_k̄ ⟶ X̄_k̄` of a compactification appears in Poincaré duality on an affine curve over a
finite field, in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleExtensionByZeroAdj_counit_app_of_isIso_ring`.
* `Stacks.EtaleCohomology.nonempty_extensionByZero_iso_opensRange`.
* `Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_lisse_zmodPow_of_isOpenImmersion`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

section Transport

variable (Λ : Type) [Ring Λ]

/-- Restriction along equal étale morphisms `a = b` gives isomorphic sheaves. -/
theorem nonempty_restriction_iso_of_eq {U Y : Scheme.{u}} (a b : U ⟶ Y) [Etale a] [Etale b]
    (h : a = b) (F : EtaleModules.{u, 0} Λ Y) :
    Nonempty ((etaleModuleRestriction.{u, 0} Λ a).obj F ≅
      (etaleModuleRestriction.{u, 0} Λ b).obj F) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- `a_! a^{-1} F ≅ b_! b^{-1} F` for equal étale morphisms `a = b`. -/
theorem nonempty_extensionByZero_restriction_iso_of_eq {U Y : Scheme.{u}} (a b : U ⟶ Y)
    [Etale a] [Etale b] (h : a = b) (F : EtaleModules.{u, 0} Λ Y) :
    Nonempty ((etaleModuleExtensionByZero.{u, 0} Λ a).obj
        ((etaleModuleRestriction.{u, 0} Λ a).obj F) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ b).obj ((etaleModuleRestriction.{u, 0} Λ b).obj F)) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- The counit `φ_! φ^{-1} F → F` is an isomorphism for an isomorphism of schemes `φ`, for
sheaves of modules over any ring. -/
theorem isIso_etaleModuleExtensionByZeroAdj_counit_app_of_isIso_ring {A B : Scheme.{u}}
    (φ : A ⟶ B) [IsIso φ] (F : EtaleModules.{u, 0} Λ B) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ φ).counit.app F) :=
  isIso_of_isIso_etaleModuleInverseImage_family Λ (T := fun _ : PUnit.{u + 1} => A)
    (fun _ => φ) (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit,
      (inv φ).base x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩) _
    fun _ => isIso_etaleModuleInverseImage_map_counit_of_factors Λ φ φ (𝟙 A)
      (Category.id_comp φ) F

/-- **Extension by zero along an open immersion is extension by zero from its image**: for an
open immersion `V : U ⟶ Y` with image `W` and a sheaf `G` on `U`, `V_! G ≅ W_! (W^{-1} V_! G)`. -/
theorem nonempty_extensionByZero_iso_opensRange {U Y : Scheme.{u}} (V : U ⟶ Y)
    [IsOpenImmersion V] (G : EtaleModules.{u, 0} Λ U) :
    Nonempty ((etaleModuleExtensionByZero.{u, 0} Λ V).obj G ≅
      (etaleModuleExtensionByZero.{u, 0} Λ V.opensRange.ι).obj
        ((etaleModuleRestriction.{u, 0} Λ V.opensRange.ι).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ V).obj G))) := by
  let φ := V.isoOpensRange
  let F := (etaleModuleExtensionByZero.{u, 0} Λ V).obj G
  -- `V_! G ≅ V_! V^{-1} F`
  let e₁ : F ≅ (etaleModuleExtensionByZero.{u, 0} Λ V).obj
      ((etaleModuleRestriction.{u, 0} Λ V).obj F) :=
    (etaleModuleExtensionByZero.{u, 0} Λ V).mapIso
      (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ V).unit.app G))
  -- `V_! V^{-1} F ≅ W_! W^{-1} F`, transporting along `V = φ ≫ W`
  obtain ⟨e₂⟩ := nonempty_extensionByZero_restriction_iso_of_eq Λ V (φ.hom ≫ V.opensRange.ι)
    (Scheme.Hom.isoOpensRange_hom_ι V).symm F
  have := isIso_etaleModuleExtensionByZeroAdj_counit_app_of_isIso_ring Λ φ.hom
    ((etaleModuleRestriction.{u, 0} Λ V.opensRange.ι).obj F)
  exact ⟨e₁ ≪≫ e₂ ≪≫
    (etaleModuleExtensionByZero.{u, 0} Λ (φ.hom ≫ V.opensRange.ι)).mapIso
      ((etaleModuleRestrictionCompIso.{u, 0} Λ φ.hom V.opensRange.ι).app F).symm ≪≫
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ φ.hom V.opensRange.ι).app _ ≪≫
    (etaleModuleExtensionByZero.{u, 0} Λ V.opensRange.ι).mapIso
      (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ φ.hom).counit.app _))⟩

end Transport

variable {ℓ : ℕ} [Fact ℓ.Prime] {m : ℕ} [NeZero m]
  {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

include f in
/-- **Poincaré duality for lisse `ℤ/ℓᵐ`-sheaves along an open immersion into a smooth proper
curve.** For an open immersion `V : U ⟶ Y` from a nonempty scheme, every injective trace `t` on
`H²(Y, ℤ/ℓᵐ)` and every finite type locally constant sheaf `G` of `ℤ/ℓᵐ`-modules on `U`, duality
holds on `Y` at `V_! G` with dualizing object `ℤ/ℓᵐ`, and `Ext^q_Y(V_! G, ℤ/ℓᵐ) = 0` for
`q > 2`. -/
theorem isDualityPerfect_extensionByZero_lisse_zmodPow_of_isOpenImmersion (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := Y) (ℓ ^ m)) (unitSheaf (ℓ ^ m)) 2 →+ ZMod (ℓ ^ m))
    (ht : Function.Injective t) {U : Scheme.{u}} (V : U ⟶ Y) [IsOpenImmersion V] [Nonempty U]
    (G : EtaleModules.{u, 0} (ZMod (ℓ ^ m)) U)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ m)) U.smallEtaleTopology G) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) (ℓ ^ m)) (unitSheaf (ℓ ^ m)) 2 t
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ m)) V).obj G) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ m)) V).obj G)
        (unitSheaf (X := Y) (ℓ ^ m)) q) := by
  let W := V.opensRange
  let φ := V.isoOpensRange
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have hdim : topologicalKrullDim Y = 1 := IsCurve.topologicalKrullDim_eq_one (f := f)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨x₀⟩ := ‹Nonempty U›
  have : Nonempty W := ⟨⟨V.base x₀, x₀, rfl⟩⟩
  have hW : W ≠ ⊥ := fun h => by
    have hx : V.base x₀ ∈ W := ⟨x₀, rfl⟩
    rwa [h] at hx
  have hfin := Stacks.AlgebraicGeometry.AmpleDimensionOne.finite_compl_of_ne_bot Y hdim W hW
  have hgen : genericPoint Y ∈ W :=
    ((genericPoint_spec Y).mem_open_set_iff W.2).2 ⟨V.base x₀, Set.mem_univ _, x₀, rfl⟩
  let S := hfin.toFinset
  have hS : ∀ y ∈ S, IsClosed ({y} : Set Y) := fun y hy =>
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint Y hdim
      fun h => by
      rw [Set.Finite.mem_toFinset, h] at hy
      exact hy hgen
  have hVS : (W : Set Y) = (↑S : Set Y)ᶜ := by
    rw [Set.Finite.coe_toFinset, compl_compl]
  -- the restriction to `W` of `V_! G` is lisse
  let F := (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ m)) V).obj G
  let GW := (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ m)) W.ι).obj F
  obtain ⟨eGW⟩ := nonempty_restriction_iso_of_eq (ZMod (ℓ ^ m)) W.ι (φ.inv ≫ V)
    ((Iso.eq_inv_comp φ).2 (Scheme.Hom.isoOpensRange_hom_ι V)) F
  let eGW' : GW ≅ (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ m)) φ.inv).obj G :=
    eGW ≪≫ ((etaleModuleRestrictionCompIso.{u, 0} (ZMod (ℓ ^ m)) φ.inv V).app F).symm ≪≫
      (etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ m)) φ.inv).mapIso
        (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod (ℓ ^ m)) V).unit.app G)).symm ≪≫
      ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod (ℓ ^ m)) φ.inv).app G).symm
  have hGW : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ m))
      (W : Scheme).smallEtaleTopology GW :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ (ZMod (ℓ ^ m)) eGW'.symm
      (lccModules_etaleModuleInverseImage (ℓ ^ m) φ.inv G hG)
  obtain ⟨e⟩ := nonempty_extensionByZero_iso_opensRange (ZMod (ℓ ^ m)) V G
  obtain ⟨h₁, h₂⟩ := isDualityPerfect_extensionByZero_lisse_zmodPow_of_curve f hℓ t ht S hS W hVS
    GW hGW
  exact ⟨Ext.isDualityPerfect_of_iso e.symm h₁, fun q hq =>
    have := h₂ q hq
    LevelChange.subsingleton_ext_of_iso e (Iso.refl _) q⟩

end Stacks.EtaleCohomology

end

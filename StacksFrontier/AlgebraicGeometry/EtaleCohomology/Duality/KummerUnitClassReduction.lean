module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.UnitSheafRestrictScalarsExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityPowMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RootOfUnityTwist
public import StacksFrontier.CategoryTheory.Abelian.ExtTransport

/-!
# Kummer classes under reduction of the level

Let `N = e N'`, `ζ` a primitive `N`-th root of unity and `ζ' = ζ^e`. The `e`-th power maps
`μ_N ⟶ μ_{N'}` and `𝐆_m ⟶ 𝐆_m` and the identity of `𝐆_m` form a morphism from the Kummer sequence
at level `N` to the Kummer sequence at level `N'`, so the Kummer coboundaries are compatible:
`(t ↦ t^e)_* δ_N(a) = δ_{N'}(a)` (`Stacks.Kummer.sheafH_map_rootsOfUnityPowMap_kummerδ`).

Through `μ_N ≅ ℤ/N` (`ζ ↦ 1`) and `μ_{N'} ≅ ℤ/N'` (`ζ' ↦ 1`) the power map `μ_N ⟶ μ_{N'}` is the
reduction `ℤ/N ⟶ ℤ/N'`
(`Stacks.EtaleCohomology.ExtensionTorsor.underlyingMap_unitSheafReduction_comp_iso`). Reading
`ℤ/N'`-cohomology with `ℤ/N` coefficients is compatible with the comparison to abelian sheaf
cohomology (`Stacks.EtaleCohomology.ExtensionTorsor.extForgetSheafH_mk₀_unitSheafReduction_comp`),
so the reduction of the Kummer class `κ_N(a) ∈ H¹(V, ℤ/N)` is the Kummer class `κ_{N'}(a)`:
`ρ_V ∘ κ_N(a) = res(κ_{N'}(a)) ∘ ρ_V` in `Ext¹_{ℤ/N}(Λ_V, res Λ'_V)`
(`Stacks.EtaleCohomology.ExtensionTorsor.kummerUnitClass_comp_unitSheafReduction`).

## Main results

* `Stacks.Kummer.sheafH_map_rootsOfUnityPowMap_kummerδ`
* `Stacks.EtaleCohomology.ExtensionTorsor.extForgetSheafH_mk₀_unitSheafReduction_comp`
* `Stacks.EtaleCohomology.ExtensionTorsor.underlyingMap_unitSheafReduction_comp_iso`
* `Stacks.EtaleCohomology.ExtensionTorsor.kummerUnitClass_comp_unitSheafReduction`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w u v

namespace Stacks.Kummer

variable (X : Scheme.{u}) [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  (e N' N : ℕ) (hN : e * N' = N)

/-- The `e`-th power maps form a morphism from the Kummer sequence at level `N = e N'` to the
Kummer sequence at level `N'`, the identity on the last term. -/
def kummerSequencePowHom : kummerSequence.{u, v} X N ⟶ kummerSequence.{u, v} X N' where
  τ₁ := rootsOfUnityPowMap.{u, v} X e N' N hN
  τ₂ := powMap.{u, v} X e
  τ₃ := 𝟙 _
  comm₁₂ := rootsOfUnityPowMap_comp_ι.{u, v} X e N' N hN
  comm₂₃ := by
    subst hN
    change powMap.{u, v} X e ≫ powMap.{u, v} X N' = powMap.{u, v} X (e * N') ≫ 𝟙 _
    rw [Category.comp_id, powMap, powMap, powMap, Preadditive.nsmul_comp, Category.id_comp,
      mul_smul]

variable {N' N} (hN'0 : N' ≠ 0) (hN0 : N ≠ 0) (hX' : IsUnit ((N' : ℕ) : Γ(X, ⊤)))
  (hX : IsUnit ((N : ℕ) : Γ(X, ⊤)))

/-- **The Kummer coboundary is compatible with the reduction of the level**: the `e`-th power map
`μ_N ⟶ μ_{N'}` carries `δ_N(a)` to `δ_{N'}(a)`. -/
theorem sheafH_map_rootsOfUnityPowMap_kummerδ (q : ℕ)
    (x : Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q) :
    Sheaf.H.map (rootsOfUnityPowMap.{u, v} X e N' N hN) (q + 1) (kummerδ X hN0 hX q x) =
      kummerδ X hN'0 hX' q x := by
  have h := (kummerSequence_shortExact.{u, v} X hN0 hX).extClass_naturality
    (kummerSequence_shortExact.{u, v} X hN'0 hX') (kummerSequencePowHom.{u, v} X e N' N hN)
  have h' : (kummerSequence_shortExact.{u, v} X hN0 hX).extClass.comp
      (Ext.mk₀ (rootsOfUnityPowMap.{u, v} X e N' N hN)) (add_zero 1) =
        (kummerSequence_shortExact.{u, v} X hN'0 hX').extClass :=
    h.trans (Ext.mk₀_id_comp _)
  rw [Sheaf.H.map_apply]
  exact (Ext.comp_assoc x (kummerSequence_shortExact.{u, v} X hN0 hX).extClass
    (Ext.mk₀ (rootsOfUnityPowMap.{u, v} X e N' N hN)) rfl (add_zero 1) rfl).trans
    (congrArg (fun y => x.comp y rfl) h')

end Stacks.Kummer

namespace Stacks.EtaleCohomology.ExtensionTorsor

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {V : Scheme.{u}} {N N' : ℕ} (h : N' ∣ N)

/-- **The reduction `Λ_V ⟶ res Λ'_V` is `1 ↦ 1` on underlying abelian sheaves**: the map
`ℤ_V ⟶ U Λ_V` followed by the reduction is the map `ℤ_V ⟶ U Λ'_V`. -/
theorem etaleModuleUnderlyingAbelianConstantMap_comp_map_unitSheafReduction :
    etaleModuleUnderlyingAbelianConstantMap (ZMod N) V ≫
        (etaleModuleUnderlyingAbelian V (ZMod N)).map (unitSheafReduction V h) =
      etaleModuleUnderlyingAbelianConstantMap (ZMod N') V := by
  have hT := etaleSiteTerminalIsTerminal V
  rw [etaleModuleUnderlyingAbelianConstantMap_comp_map (ZMod N) V hT]
  have h1 := etaleModuleUnderlyingAbelianConstantMap_comp_map (ZMod N') V hT
    (𝟙 (unitSheaf (X := V) N'))
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h1
  rw [h1]
  congr 1
  ext x
  obtain ⟨x⟩ := x
  have hρ := homUnitSheafEquiv_unitSheafReduction (Y := V) h
  simp only [homUnitSheafEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv_apply] at hρ
  show (ConcreteCategory.hom (((etaleModuleConstantAdj (ZMod N) V hT).homEquiv _ _)
      (unitSheafReduction V h))) (x • (1 : ULift.{u + 1} (ZMod N))) =
    (ConcreteCategory.hom (((etaleModuleConstantAdj (ZMod N') V hT).homEquiv _ _)
      (𝟙 (unitSheaf (X := V) N')))) (x • (1 : ULift.{u + 1} (ZMod N')))
  rw [map_zsmul, map_zsmul]
  exact congrArg (_ • ·) hρ

/-- **Reading `ℤ/N'`-cohomology with `ℤ/N` coefficients commutes with the comparison to
abelian sheaf cohomology**: `y ↦ res(y) ∘ ρ_V` followed by `Ext_{ℤ/N}(Λ_V, -) → H(V, U -)` is the
comparison `Ext_{ℤ/N'}(Λ'_V, -) → H(V, U -)`. -/
theorem extForgetSheafH_mk₀_unitSheafReduction_comp (M : EtaleModules.{u, 0} (ZMod N') V) {i : ℕ}
    (y : Ext.{u + 1} (unitSheaf (X := V) N') M i) :
    extForgetSheafH (ZMod N) V ((etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) V).obj M) i
        ((Ext.mk₀ (unitSheafReduction V h)).comp
          (y.mapExactFunctor (etaleModuleRestrictScalars (ZMod.castHom h (ZMod N')) V))
          (zero_add i)) =
      extForgetSheafH (ZMod N') V M i y := by
  rw [extForgetSheafH_apply, extForgetSheafH_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    etaleModuleUnderlyingAbelianConstantMap_comp_map_unitSheafReduction,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  rfl

/-- Maps out of the constant abelian sheaf `ℤ_V` are determined by the image of the section `1`
over the final object. -/
theorem constantAbelianSheaf_hom_ext_of_app_one
    {F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {f g : (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F}
    (hfg : f.hom.app (op (etaleSiteTerminal V))
        ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (etaleSiteTerminal V)) (ULift.up 1)) =
      g.hom.app (op (etaleSiteTerminal V))
        ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op (etaleSiteTerminal V)) (ULift.up 1))) :
    f = g := by
  have hT := etaleSiteTerminalIsTerminal V
  apply (Ext.mk₀_bijective _ _).1
  apply (Sheaf.H.equiv₀ F hT).injective
  rw [sheafH_equiv₀_mk₀_eq_app hT, sheafH_equiv₀_mk₀_eq_app hT]
  exact hfg

/-- The map `ℤ_V ⟶ U Λ_V`, `1 ↦ 1`, is an epimorphism. -/
instance epi_etaleModuleUnderlyingAbelianConstantMap :
    Epi (etaleModuleUnderlyingAbelianConstantMap (ZMod N) V) := by
  have : Epi (uliftIntToULiftHom.{u} (ZMod N)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective y.down
    refine ⟨ULift.up z, ?_⟩
    apply ULift.ext
    change z • (1 : ZMod N) = y.down
    rw [zsmul_one, hz]
  unfold etaleModuleUnderlyingAbelianConstantMap
  infer_instance

/-- Composing with two maps in degree zero is composing with their composite. -/
private theorem comp_mk₀_comp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z T : C} {n : ℕ} (x : Ext X Y n) (f : Y ⟶ Z) (g : Z ⟶ T) :
    (x.comp (Ext.mk₀ f) (add_zero n)).comp (Ext.mk₀ g) (add_zero n) =
      x.comp (Ext.mk₀ (f ≫ g)) (add_zero n) := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

variable {k : Type u} [Field k] (fV : V ⟶ Spec (.of k)) {e : ℕ} (he : e * N' = N) {ζ : k}
  (hζ : IsPrimitiveRoot ζ N) (hζ' : IsPrimitiveRoot (ζ ^ e) N') (hN0 : N ≠ 0) (hN'0 : N' ≠ 0)

/-- **The reduction of constant sheaves is the `e`-th power map on roots of unity**: through
`U Λ_V ≅ μ_N` (`ζ ↦ 1`) and `U Λ'_V ≅ μ_{N'}` (`ζ^e ↦ 1`), the reduction `Λ_V ⟶ Λ'_V` is
`t ↦ t^e`. -/
theorem underlyingMap_unitSheafReduction_comp_iso :
    (etaleModuleUnderlyingAbelian V (ZMod N)).map (unitSheafReduction V (Dvd.intro_left e he)) ≫
        (Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hζ' hN'0).hom =
      (Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hζ hN0).hom ≫
        Stacks.Kummer.rootsOfUnityPowMap.{u, 0} V e N' N he := by
  rw [← cancel_epi (etaleModuleUnderlyingAbelianConstantMap (ZMod N) V),
    ← cancel_mono (Stacks.Kummer.rootsOfUnityι.{u, 0} V N')]
  apply constantAbelianSheaf_hom_ext_of_app_one
  have hL : (etaleModuleUnderlyingAbelianConstantMap (ZMod N) V ≫
      ((etaleModuleUnderlyingAbelian V (ZMod N)).map (unitSheafReduction V (Dvd.intro_left e he)) ≫
        (Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hζ' hN'0).hom)) ≫
          Stacks.Kummer.rootsOfUnityι.{u, 0} V N' =
      (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (uliftIntToULiftHom.{u} (ZMod N')) ≫ Stacks.Kummer.rootSheafHom fV hζ' hN'0 := by
    have hc := congrArg (fun t => t ≫ ((Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hζ'
      hN'0).hom ≫ Stacks.Kummer.rootsOfUnityι.{u, 0} V N'))
        (etaleModuleUnderlyingAbelianConstantMap_comp_map_unitSheafReduction (V := V)
          (Dvd.intro_left e he))
    exact ((Category.assoc _ _ _).trans ((congrArg
      (etaleModuleUnderlyingAbelianConstantMap (ZMod N) V ≫ ·) (Category.assoc _ _ _)).trans
        (Category.assoc _ _ _).symm)).trans
      (hc.trans (constantMap_comp_underlyingIso_comp_ι hζ' hN'0 fV))
  have hR : (etaleModuleUnderlyingAbelianConstantMap (ZMod N) V ≫
      ((Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hζ hN0).hom ≫
        Stacks.Kummer.rootsOfUnityPowMap.{u, 0} V e N' N he)) ≫
          Stacks.Kummer.rootsOfUnityι.{u, 0} V N' =
      ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (uliftIntToULiftHom.{u} (ZMod N)) ≫ Stacks.Kummer.rootSheafHom fV hζ hN0) ≫
        Stacks.Kummer.powMap.{u, 0} V e := by
    rw [← constantMap_comp_underlyingIso_comp_ι hζ hN0 fV]
    simp only [Category.assoc, Stacks.Kummer.rootsOfUnityPowMap_comp_ι]
  rw [hL, hR, rootSheafHom_app_one]
  show _ = (Stacks.Kummer.powMap.{u, 0} V e).hom.app _ (((constantSheaf V.smallEtaleTopology
      AddCommGrpCat.{u + 1}).map (uliftIntToULiftHom.{u} (ZMod N)) ≫
        Stacks.Kummer.rootSheafHom fV hζ hN0).hom.app _ _)
  rw [rootSheafHom_app_one, Stacks.Kummer.powMap_app_ofUnit]
  congr 1
  ext
  simp [Stacks.Kummer.rootOn]

omit hζ hζ' hN0 hN'0 in
/-- **The Kummer class is compatible with the reduction of the level**: for `N = e N'`, `ζ` a
primitive `N`-th root of unity and a unit `a` on `V`, the reduction to `ℤ/N'` of the Kummer class
`κ_N(a)` (root `ζ`) is the Kummer class `κ_{N'}(a)` (root `ζ^e`) read with `ℤ/N` coefficients:
`ρ_V ∘ κ_N(a) = res(κ_{N'}(a)) ∘ ρ_V`. -/
theorem kummerUnitClass_comp_unitSheafReduction {ζ : k} (hζ : IsPrimitiveRoot ζ N)
    (hζ' : IsPrimitiveRoot (ζ ^ e) N') (hN : IsUnit (N : k)) (hN' : IsUnit (N' : k))
    (a : (Γ(V, ⊤))ˣ) :
    (KummerFlag.kummerUnitClass hζ hN fV a).comp
        (Ext.mk₀ (unitSheafReduction V (Dvd.intro_left e he))) (add_zero 1) =
      (Ext.mk₀ (unitSheafReduction V (Dvd.intro_left e he))).comp
        ((KummerFlag.kummerUnitClass hζ' hN' fV a).mapExactFunctor
          (etaleModuleRestrictScalars (ZMod.castHom (Dvd.intro_left e he) (ZMod N')) V))
        (zero_add 1) := by
  have hN0 := KummerFlag.ne_zero_of_isUnit hN
  have hN'0 := KummerFlag.ne_zero_of_isUnit hN'
  let A := Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hζ hN0
  let B := Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hζ' hN'0
  let δN := Stacks.Kummer.kummerδ.{u + 1, u, u + 1} V hN0
    (Stacks.Kummer.isUnit_natCast_globalSections V N fV hN) 0 (KummerFlag.unitH0Class a)
  let δN' := Stacks.Kummer.kummerδ.{u + 1, u, u + 1} V hN'0
    (Stacks.Kummer.isUnit_natCast_globalSections V N' fV hN') 0 (KummerFlag.unitH0Class a)
  have hκ : ∀ {n : ℕ} {ξ : k} (hξ : IsPrimitiveRoot ξ n) (hn : IsUnit (n : k)),
      extForgetSheafH (ZMod n) V _ 1 (KummerFlag.kummerUnitClass hξ hn fV a) =
        (Stacks.Kummer.kummerδ.{u + 1, u, u + 1} V (KummerFlag.ne_zero_of_isUnit hn)
          (Stacks.Kummer.isUnit_natCast_globalSections V n fV hn) 0
            (KummerFlag.unitH0Class a)).comp
          (Ext.mk₀ (Stacks.Kummer.etaleModuleConstantUnderlyingIso fV hξ
            (KummerFlag.ne_zero_of_isUnit hn)).inv) (add_zero 1) := by
    intro n ξ hξ hn
    have h1 := (Stacks.Picard.extRootsOfUnityAddEquiv fV hξ (KummerFlag.ne_zero_of_isUnit hn)
      1).apply_symm_apply (Stacks.Kummer.kummerδ.{u + 1, u, u + 1} V
        (KummerFlag.ne_zero_of_isUnit hn) (Stacks.Kummer.isUnit_natCast_globalSections V n fV hn)
          0 (KummerFlag.unitH0Class a))
    rw [Stacks.Picard.extRootsOfUnityAddEquiv_apply, Sheaf.H.map_apply] at h1
    change (extForgetSheafH (ZMod n) V _ 1 (KummerFlag.kummerUnitClass hξ hn fV a)).comp _ _ =
      _ at h1
    have h2 := congrArg (fun t => t.comp (Ext.mk₀ (Stacks.Kummer.etaleModuleConstantUnderlyingIso
      fV hξ (KummerFlag.ne_zero_of_isUnit hn)).inv) (add_zero 1)) h1
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Ext.comp_mk₀_id] at h2
    exact h2
  have hδ := Stacks.Kummer.sheafH_map_rootsOfUnityPowMap_kummerδ.{u + 1, u, u + 1} V e he hN'0 hN0
    (Stacks.Kummer.isUnit_natCast_globalSections V N' fV hN')
    (Stacks.Kummer.isUnit_natCast_globalSections V N fV hN) 0 (KummerFlag.unitH0Class a)
  rw [Sheaf.H.map_apply] at hδ
  have hsq := underlyingMap_unitSheafReduction_comp_iso fV he hζ hζ' hN0 hN'0
  apply (extForgetSheafH_bijective (ZMod N) V 1 _).1
  rw [extForgetSheafH_comp_mk₀, extForgetSheafH_mk₀_unitSheafReduction_comp, hκ hζ hN, hκ hζ' hN',
    ← hδ]
  apply Stacks.ExtTransport.comp_mk₀_injective B 1
  dsimp only
  refine ((comp_mk₀_comp_mk₀ _ _ _).trans (comp_mk₀_comp_mk₀ _ _ _)).trans
    (Eq.trans ?_ ((comp_mk₀_comp_mk₀ _ _ _).trans (comp_mk₀_comp_mk₀ _ _ _)).symm)
  congr 2
  exact ((congrArg (A.inv ≫ ·) hsq).trans (Iso.inv_hom_id_assoc _ _)).trans
    ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) B.inv_hom_id.symm))

end Stacks.EtaleCohomology.ExtensionTorsor

end

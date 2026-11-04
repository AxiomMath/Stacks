module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RootOfUnityTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstantOverRing

/-!
# The twist of the root of unity over a ring with separated roots of unity

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RootOfUnityTwist` compares pullback on
`Hⁱ(-, μ_n)` and on `Hⁱ(-, ℤ/n)` through `UΛ ≅ μ_n`, `1 ↦ ζ`, for schemes over a field containing
a primitive `n`-th root of unity `ζ`. This file does the same over a commutative ring `k` with
`n` invertible and `ζ ^ n = 1`, `1 - ζ ^ i` a unit for `0 < i < n`, using
`Stacks.Kummer.OverRing.rootsOfUnityConstantIso`.

## Main results

* `Stacks.EtaleCohomology.OverRing.rootsOfUnity_twist`.
* `Stacks.EtaleCohomology.OverRing.rootsOfUnityPullbackMap_extForgetSheafH`: pullback on
  `Hⁱ(-, μ_n)` is `w` times pullback on `Hⁱ(-, ℤ/n)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.OverRing

variable {k : Type u} [CommRing k] {n : ℕ} {ζ : k} (hζ : ζ ^ n = 1) (hn : n ≠ 0)
  (hsep : ∀ i : ℕ, 0 < i → i < n → IsUnit (1 - ζ ^ i)) (hnR : IsUnit (n : k))

/-- **The abelian sheaf underlying the constant sheaf of `ℤ/n`-modules is `μ_n`**, through
`m ↦ ζ^m`, over a ring with separated `n`-th roots of unity. -/
def etaleModuleConstantUnderlyingIso {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) :
    (etaleModuleUnderlyingAbelian X (ZMod n)).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X n :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod n) X.smallEtaleTopology).app _ ≪≫
    Stacks.Kummer.OverRing.rootsOfUnityConstantIso fX hζ hn hsep hnR

/-- The map `ℤ_X ⟶ 𝐆_m` through `UΛ_X ≅ μ_n ⊆ 𝐆_m` is `m ↦ ζ^m`. -/
theorem constantMap_comp_underlyingIso_comp_ι {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) :
    etaleModuleUnderlyingAbelianConstantMap (ZMod n) X ≫
        (etaleModuleConstantUnderlyingIso hζ hn hsep hnR fX).hom ≫
          Stacks.Kummer.rootsOfUnityι.{u, 0} X n =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (uliftIntToULiftHom.{u} (ZMod n)) ≫ Stacks.Kummer.OverRing.rootSheafHom fX hζ hn := by
  simp only [etaleModuleUnderlyingAbelianConstantMap, etaleModuleConstantUnderlyingIso,
    Iso.trans_hom, Iso.app_hom, Stacks.Kummer.OverRing.rootsOfUnityConstantIso, asIso_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc, Stacks.Kummer.OverRing.rootsOfUnityConstantHom_comp_ι]

/-- The value of `m ↦ ζ^m` on the section `1` of `ℤ_X` is `ζ`. -/
theorem rootSheafHom_app_one {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (U : X.Etale) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (uliftIntToULiftHom.{u} (ZMod n)) ≫ Stacks.Kummer.OverRing.rootSheafHom fX hζ hn).hom.app
        (Opposite.op U)
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (Opposite.op U) (ULift.up 1)) =
      Stacks.Kummer.ofUnit.{u, 0} (Stacks.Kummer.OverRing.rootOn fX hζ hn U) := by
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map (uliftIntToULiftHom.{u} (ZMod n))))
    (Opposite.op U)) (ULift.up 1)
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Stacks.Kummer.OverRing.toSheafify_rootSheafHom fX hζ hn) (Opposite.op U))
    ((uliftIntToULiftHom.{u} (ZMod n)) (ULift.up 1))
  have h3 : ((uliftIntToULiftHom.{u} (ZMod n)) (ULift.up 1) : ULift.{u + 1} (ZMod n)).down =
      ((1 : ℤ) : ZMod n) := by
    change (1 : ℤ) • (1 : ZMod n) = _
    simp
  refine (congrArg ((Stacks.Kummer.OverRing.rootSheafHom fX hζ hn).hom.app (Opposite.op U))
    h1.symm).trans (h2.trans ?_)
  change Stacks.Kummer.OverRing.rootHom fX hζ hn U
    ((uliftIntToULiftHom.{u} (ZMod n)) (ULift.up 1) : ULift.{u + 1} (ZMod n)).down = _
  rw [h3, Stacks.Kummer.OverRing.rootHom_intCast, one_zsmul]

/-- The comparison of the images of `ζ`: for `g : Y ⟶ X` with `g ≫ f_X = f_Y ≫ Spec(τ)`, the
image of `ζ` on `X` pulls back to the image of `τ ζ` on `Y`. -/
theorem appTop_structMap_eq {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    (g : Y ⟶ X) (τ : k →+* k) (hg : g ≫ fX = fY ≫ Spec.map (CommRingCat.ofHom τ))
    (m : Scheme.Etale.mk (𝟙 Y) ⟶ (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))) (c : k) :
    m.left.appTop.hom ((pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop.hom
        (Stacks.Kummer.OverRing.structMap fX (Scheme.Etale.mk (𝟙 X)) c)) =
      Stacks.Kummer.OverRing.structMap fY (Scheme.Etale.mk (𝟙 Y)) (τ c) := by
  have h1 : m.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 X)).hom g = 𝟙 Y := by
    have := m.w
    exact this.trans (Category.comp_id _)
  have hm : m.left ≫ pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g = g := by
    have hc := pullback.condition (f := (Scheme.Etale.mk (𝟙 X)).hom) (g := g)
    have hc' : pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g = pullback.snd _ g ≫ g :=
      (Category.comp_id _).symm.trans hc
    exact (congrArg (m.left ≫ ·) hc').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) h1).trans (Category.id_comp g)))
  have key : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop ≫
        (Scheme.Etale.mk (𝟙 X)).hom.appTop) ≫
        (pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop ≫ m.left.appTop =
      CommRingCat.ofHom τ ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop ≫
        (Scheme.Etale.mk (𝟙 Y)).hom.appTop := by
    have e : ∀ {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)),
        f.appTop ≫ (Scheme.Etale.mk (𝟙 Z)).hom.appTop = f.appTop := fun f =>
      (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop (Category.id_comp f))
    have em : (pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop ≫ m.left.appTop = g.appTop :=
      (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop hm)
    have eg : fX.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom τ)).appTop ≫ fY.appTop :=
      (Scheme.Hom.comp_appTop _ _).symm.trans ((congrArg Scheme.Hom.appTop hg).trans
        (Scheme.Hom.comp_appTop _ _))
    simp only [e, em]
    erw [Category.assoc, eg, Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  exact congrArg (fun φ : CommRingCat.of k ⟶ Γ(Y, ⊤) => φ.hom c) key

/-- **The twist of the root of unity under pullback.** Let `g : Y ⟶ X` with
`g ≫ f_X = f_Y ≫ Spec(τ)` for a ring endomorphism `τ` of `k` with `τ ζ = ζ ^ w`. Then the two maps
`ℤ_Y ⟶ μ_n`, through `g^{-1}` of `ℤ_X ⟶ UΛ_X ≅ μ_n` followed by the comparison
`g^{-1} μ_n ⟶ μ_n`, and through `ℤ_Y ⟶ UΛ_Y ≅ μ_n`, differ by the factor `w`. -/
theorem rootsOfUnity_twist {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    (g : Y ⟶ X) (τ : k →+* k) (w : ℕ) (hg : g ≫ fX = fY ≫ Spec.map (CommRingCat.ofHom τ))
    (hτ : τ ζ = ζ ^ w)
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    (etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        (etaleAbelianInverseImage.{u, 0} g).map
          (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X ≫
            (etaleModuleConstantUnderlyingIso hζ hn hsep hnR fX).hom) ≫
        Stacks.Kummer.rootsOfUnityInverseImageComparison.{u, 0} g n =
      (w : ℤ) • (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y ≫
        (etaleModuleConstantUnderlyingIso hζ hn hsep hnR fY).hom) := by
  refine (cancel_mono (Stacks.Kummer.rootsOfUnityι.{u, 0} Y n)).1 ?_
  rw [Category.assoc, Category.assoc,
    Stacks.Kummer.rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, ← Category.assoc
      ((etaleAbelianInverseImage.{u, 0} g).map _), ← Functor.map_comp, Category.assoc,
    constantMap_comp_underlyingIso_comp_ι, Preadditive.zsmul_comp, Category.assoc,
    constantMap_comp_underlyingIso_comp_ι]
  set Φ := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (uliftIntToULiftHom.{u} (ZMod n)) ≫ Stacks.Kummer.OverRing.rootSheafHom fX hζ hn with hΦ
  set hT := isTerminalEtaleMkId Y
  apply (Ext.mk₀_bijective _ _).1
  apply (Sheaf.H.equiv₀ _ hT).injective
  have hL : Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ (etaleAbelianInverseImage.{u, 0} g).map Φ ≫
        Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} g) =
      Sheaf.H.map (Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} g) 0
        (etaleCohomologyRestrictionMap.{u, 0, u + 1} g _ 0 (Ext.mk₀ Φ)) := by
    rw [etaleCohomologyRestrictionMap_apply, Sheaf.H.map_apply, Ext.mapExactFunctor_mk₀,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.assoc]
    rfl
  rw [hL, ← Sheaf.H.equiv₀_naturality, equiv₀_etaleCohomologyRestrictionMap_zero,
    sheafH_equiv₀_mk₀_eq_app (isTerminalEtaleMkId X), hΦ, rootSheafHom_app_one,
    sheafH_equiv₀_mk₀_eq_app]
  set t := (IsTerminal.isTerminalObj (smallEtaleBaseChange g) (Scheme.Etale.mk (𝟙 X))
    (isTerminalEtaleMkId X)).from (Scheme.Etale.mk (𝟙 Y))
  have hnat := ConcreteCategory.congr_hom
    ((Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} g).hom.naturality t.op)
    (((etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} X)).hom.app (Opposite.op (Scheme.Etale.mk (𝟙 X)))
      (Stacks.Kummer.ofUnit (Stacks.Kummer.OverRing.rootOn fX hζ hn (Scheme.Etale.mk (𝟙 X)))))
  refine hnat.trans ((congrArg (fun z => (Stacks.Kummer.multiplicativeSheaf.{u, 0} Y).obj.map
    t.op z)
    (Stacks.Kummer.multiplicativeInverseImageComparison_app_ofUnit.{u, 0} g
      (Scheme.Etale.mk (𝟙 X)) _)).trans (Eq.trans (Stacks.Kummer.map_ofUnit _ _) ?_))
  have hz : ∀ (φ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ Stacks.Kummer.multiplicativeSheaf.{u, 0} Y) (x),
      ((w : ℤ) • φ).hom.app (Opposite.op (Scheme.Etale.mk (𝟙 Y))) x =
        (w : ℤ) • φ.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 Y))) x := by
    intro φ x
    rfl
  refine Eq.trans ?_ (hz _ _).symm
  refine Eq.trans ?_ (congrArg ((w : ℤ) • ·) (rootSheafHom_app_one hζ hn fY _)).symm
  refine Eq.trans ?_ (Stacks.Kummer.zsmul_ofUnit _ _ _).symm
  refine congrArg Stacks.Kummer.ofUnit (Units.ext ?_)
  have := appTop_structMap_eq fX fY g τ hg t ζ
  rw [hτ, map_pow] at this
  exact this

/-- **Pullback on `Hⁱ(-, μ_n)` and on `Hⁱ(-, ℤ/n)` agree up to the twist of the root of unity.**
Identify `Hⁱ(X, ℤ/n) = Ext^i(ℤ/n_X, ℤ/n_X)` with `Hⁱ(X, μ_n)` through `UΛ_X ≅ μ_n`, `1 ↦ ζ`. For
`g : Y ⟶ X` with `g ≫ f_X = f_Y ≫ Spec(τ)` and `τ ζ = ζ ^ w`, the pullback on `Hⁱ(-, μ_n)` of the
class of `e` is `w` times the class of the pullback `g^* e`. -/
theorem rootsOfUnityPullbackMap_extForgetSheafH {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k))
    (fY : Y ⟶ Spec (.of k)) (g : Y ⟶ X) (τ : k →+* k) (w : ℕ)
    (hg : g ≫ fX = fY ≫ Spec.map (CommRingCat.ofHom τ)) (hτ : τ ζ = ζ ^ w)
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] {i : ℕ}
    (e : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology) i) :
    rootsOfUnityPullbackMap.{u, 0, u + 1} g n i
        (Sheaf.H.map (etaleModuleConstantUnderlyingIso hζ hn hsep hnR fX).hom i
          (extForgetSheafH (ZMod n) X _ i e)) =
      (w : ℤ) • Sheaf.H.map (etaleModuleConstantUnderlyingIso hζ hn hsep hnR fY).hom i
        (extForgetSheafH (ZMod n) Y _ i (constantExtRestriction (ZMod n) g i e)) :=
  map_restriction_extForgetSheafH n g _ _ _ _
    (rootsOfUnity_twist hζ hn hsep hnR fX fY g τ w hg hτ) e


end Stacks.EtaleCohomology.OverRing

end

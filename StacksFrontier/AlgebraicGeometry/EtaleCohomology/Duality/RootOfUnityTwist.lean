module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupProductRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DegreeZeroTerminal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomologyNaturality

/-!
# Restriction of `Hⁱ(X, ℤ/n) ≅ Hⁱ(X, μ_n)` and the twist of the root of unity

Let `Λ = ℤ/n`. Through the forgetful functor, `Hⁱ(X, Λ) = Ext^i_Λ(Λ_X, Λ_X)` is the cohomology of
the abelian sheaf `UΛ_X` (`Stacks.EtaleCohomology.extForgetSheafH`, built from operations on `Ext`
classes). Given a map `ι_X : UΛ_X ⟶ F_X` (in the application `UΛ_X ≅ μ_n`, `1 ↦ ζ`) and the same
on `Y`, a morphism `g : Y ⟶ X` and a comparison `g^{-1} F_X ⟶ F_Y`, restriction on
`Hⁱ(-, F)` and restriction of `Ext^i(Λ, Λ)` are intertwined up to the factor `w` by which the
two composites `ℤ_Y ⟶ F_Y` differ (`Stacks.EtaleCohomology.map_restriction_extForgetSheafH`).

## Main results

* `Stacks.EtaleCohomology.map_restriction_extForgetSheafH`: the comparison of restrictions.
* `Stacks.EtaleCohomology.rootsOfUnity_twist`: for `μ_n ≅ ℤ/n` through `ζ` and
  `g ≫ f_X = f_Y ≫ Spec(τ)` with `τ ζ = ζ ^ w`, the twist is `w`.
* `Stacks.EtaleCohomology.rootsOfUnityPullbackMap_extForgetSheafH`: pullback on `Hⁱ(-, μ_n)` is
  `w` times pullback on `Hⁱ(-, ℤ/n)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section ExtZsmul

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt 𝒞]

/-- `Ext.mk₀ f` is the image of `f` under the inverse of `Ext.addEquiv₀`. -/
theorem ext_mk₀_eq_addEquiv₀_symm {A B : 𝒞} (f : A ⟶ B) : Ext.mk₀ f = Ext.addEquiv₀.symm f :=
  Ext.addEquiv₀.symm_apply_eq.2 ((Ext.mk₀_bijective _ _).1 (Ext.mk₀_addEquiv₀_apply _).symm) |>.symm

/-- `Ext.mk₀` commutes with integer multiples. -/
theorem ext_mk₀_zsmul {A B : 𝒞} (f : A ⟶ B) (m : ℤ) : Ext.mk₀ (m • f) = m • Ext.mk₀ f := by
  rw [ext_mk₀_eq_addEquiv₀_symm, ext_mk₀_eq_addEquiv₀_symm, map_zsmul]

/-- The composition of `Ext` classes is `ℤ`-linear in the second variable. -/
theorem ext_comp_zsmul {A B D : 𝒞} {a b c : ℕ} (x : Ext A B a) (y : Ext B D b) (h : a + b = c)
    (m : ℤ) : x.comp (m • y) h = m • x.comp y h :=
  map_zsmul (Ext.bilinearComp A B D a b c h x) m y

/-- The map induced on sheaf cohomology by `m • φ` is `m` times the map induced by `φ`. -/
theorem sheafH_map_zsmul {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat] [HasExt (Sheaf J AddCommGrpCat)]
    {F G : Sheaf J AddCommGrpCat} (φ : F ⟶ G) (m : ℤ) {i : ℕ} (x : Sheaf.H F i) :
    Sheaf.H.map (m • φ) i x = m • Sheaf.H.map φ i x := by
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, ext_mk₀_zsmul, ext_comp_zsmul]

end ExtZsmul

section Restriction

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Restriction of `Hⁱ(X, Λ)` read in `Hⁱ(-, F)` through maps `ι : UΛ ⟶ F`.** If the two
composites `ℤ_Y ⟶ F_Y`, through `g^{-1}(ι_X)` and the comparison `κ : g^{-1} F_X ⟶ F_Y`, and
through `ι_Y`, differ by the factor `w`, then for every `e ∈ Ext^i(Λ_X, Λ_X)`
`κ(g^*(ι_X e)) = w · ι_Y(g^* e)`. -/
theorem map_restriction_extForgetSheafH {FX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {FY : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ιX : (etaleModuleUnderlyingAbelian X (ZMod n)).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology) ⟶ FX)
    (ιY : (etaleModuleUnderlyingAbelian Y (ZMod n)).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) Y.smallEtaleTopology) ⟶ FY)
    (κ : (etaleAbelianInverseImage.{u, 0} g).obj FX ⟶ FY) (w : ℤ)
    (hw : (etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        (etaleAbelianInverseImage.{u, 0} g).map
          (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X ≫ ιX) ≫ κ =
      w • (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y ≫ ιY))
    {i : ℕ}
    (e : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology) i) :
    Sheaf.H.map κ i (etaleCohomologyRestrictionMap.{u, 0, u + 1} g FX i
        (Sheaf.H.map ιX i (extForgetSheafH (ZMod n) X _ i e))) =
      w • Sheaf.H.map ιY i
        (extForgetSheafH (ZMod n) Y _ i (constantExtRestriction (ZMod n) g i e)) := by
  have hfac := etaleModuleUnderlyingAbelianConstantMap_comp_inverseImageConstantIso (ZMod n) g
  have hM : (etaleAbelianInverseImage.{u, 0} g).map ιX ≫ κ =
      w • (((etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) g).hom.app
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n) X.smallEtaleTopology)) ≫
        ((etaleModuleUnderlyingAbelian Y (ZMod n))).map (constantInverseImageIso (ZMod n) g).inv ≫
          ιY) := by
    have hepi : Epi (((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
          (etaleAbelianInverseImage.{u, 0} g).map
            (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X)) := by
      have : Epi (uliftIntToULiftHom.{u} (ZMod n)) := by
        rw [AddCommGrpCat.epi_iff_surjective]
        intro y
        obtain ⟨z, hz⟩ := ZMod.intCast_surjective y.down
        refine ⟨ULift.up z, ULift.ext ?_⟩
        change z • (1 : ZMod n) = y.down
        rw [zsmul_eq_mul, mul_one, hz]
      have : Epi (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X) := by
        change Epi ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (uliftIntToULiftHom.{u} (ZMod n)) ≫ _)
        have : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
          (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
            (etaleSiteTerminalIsTerminal X)).isLeftAdjoint
        infer_instance
      have : (etaleAbelianInverseImage.{u, 0} g).IsLeftAdjoint :=
        (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).isLeftAdjoint
      infer_instance
    refine (cancel_epi (((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ (etaleAbelianInverseImage.{u, 0} g).map
        (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X))).1 ?_
    calc (((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ (etaleAbelianInverseImage.{u, 0} g).map
              (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X)) ≫
          (etaleAbelianInverseImage.{u, 0} g).map ιX ≫ κ =
        ((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ (etaleAbelianInverseImage.{u, 0} g).map
            ((etaleModuleUnderlyingAbelianConstantMap (ZMod n) X) ≫ ιX) ≫ κ := by
          simp only [Functor.map_comp, Category.assoc]
      _ = w • ((etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y) ≫ ιY) := hw
      _ = w • ((((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ (etaleAbelianInverseImage.{u, 0} g).map
              (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X)) ≫
            ((etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) g).hom.app
              (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
                X.smallEtaleTopology)) ≫
            ((etaleModuleUnderlyingAbelian Y (ZMod n))).map
              (constantInverseImageIso (ZMod n) g).inv ≫ ιY) := by
          congr 1
          have h2 : ((etaleAbelianInverseImageConstantIso.{u, 0} g).inv.app
              (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ (etaleAbelianInverseImage.{u, 0} g).map
                (etaleModuleUnderlyingAbelianConstantMap (ZMod n) X) ≫
              ((etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) g).hom.app
                (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod n)
                  X.smallEtaleTopology)) =
              (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y) ≫
                ((etaleModuleUnderlyingAbelian Y (ZMod n))).map
                  (constantInverseImageIso (ZMod n) g).hom := hfac.symm
          rw [Category.assoc, reassoc_of% h2,
            ← ((etaleModuleUnderlyingAbelian Y (ZMod n))).map_comp_assoc, Iso.hom_inv_id,
            ((etaleModuleUnderlyingAbelian Y (ZMod n))).map_id, Category.id_comp]
      _ = _ := (Preadditive.comp_zsmul _ _ _).symm
  rw [Stacks.Kummer.etaleCohomologyRestrictionMap_sheafHMap, ← Sheaf.H.map_comp_apply, hM,
    sheafH_map_zsmul, constantExtRestriction_eq, extForgetSheafH_comp_mk₀,
    extForgetSheafH_etaleModuleExtRestriction]
  congr 1
  rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
  rfl

end Restriction

section Twist

/-- `H⁰(F) ≅ F(T)` on the class of a morphism `f : ℤ ⟶ F` is the value of `f` on the section
`1`. -/
theorem sheafH_equiv₀_mk₀_eq_app {Y : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] {T : Y.Etale}
    (hT : IsTerminal T) {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    Sheaf.H.equiv₀ F hT (Ext.mk₀ f) = f.hom.app (Opposite.op T)
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (Opposite.op T) (ULift.up 1)) := by
  rw [Sheaf.H.equiv₀_mk₀]
  rfl

variable {k : Type u} [Field k] {n : ℕ} {ζ : k} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

/-- The map `ℤ_X ⟶ 𝐆_m` through `UΛ_X ≅ μ_n ⊆ 𝐆_m` is `m ↦ ζ^m`. -/
theorem constantMap_comp_underlyingIso_comp_ι {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) :
    etaleModuleUnderlyingAbelianConstantMap (ZMod n) X ≫
        (Stacks.Kummer.etaleModuleConstantUnderlyingIso fX hζ hn).hom ≫
          Stacks.Kummer.rootsOfUnityι.{u, 0} X n =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (uliftIntToULiftHom.{u} (ZMod n)) ≫ Stacks.Kummer.rootSheafHom fX hζ hn := by
  simp only [etaleModuleUnderlyingAbelianConstantMap,
    Stacks.Kummer.etaleModuleConstantUnderlyingIso, Iso.trans_hom, Iso.app_hom,
    Stacks.Kummer.rootsOfUnityConstantIso, asIso_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    Stacks.Kummer.rootsOfUnityConstantHom_comp_ι]

/-- The value of `m ↦ ζ^m` on the section `1` of `ℤ_X` is `ζ`. -/
theorem rootSheafHom_app_one {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (U : X.Etale) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (uliftIntToULiftHom.{u} (ZMod n)) ≫ Stacks.Kummer.rootSheafHom fX hζ hn).hom.app
        (Opposite.op U)
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (Opposite.op U) (ULift.up 1)) =
      Stacks.Kummer.ofUnit.{u, 0} (Stacks.Kummer.rootOn fX hζ hn U) := by
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map (uliftIntToULiftHom.{u} (ZMod n))))
    (Opposite.op U)) (ULift.up 1)
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Stacks.Kummer.toSheafify_rootSheafHom fX hζ hn) (Opposite.op U))
    ((uliftIntToULiftHom.{u} (ZMod n)) (ULift.up 1))
  have h3 : ((uliftIntToULiftHom.{u} (ZMod n)) (ULift.up 1) : ULift.{u + 1} (ZMod n)).down =
      ((1 : ℤ) : ZMod n) := by
    change (1 : ℤ) • (1 : ZMod n) = _
    simp
  refine (congrArg ((Stacks.Kummer.rootSheafHom fX hζ hn).hom.app (Opposite.op U)) h1.symm).trans
    (h2.trans ?_)
  change Stacks.Kummer.rootHom fX hζ hn U
    ((uliftIntToULiftHom.{u} (ZMod n)) (ULift.up 1) : ULift.{u + 1} (ZMod n)).down = _
  rw [h3, Stacks.Kummer.rootHom_intCast, one_zsmul]

/-- The comparison of the images of `ζ`: for `g : Y ⟶ X` with `g ≫ f_X = f_Y ≫ Spec(τ)`, the
image of `ζ` on `X` pulls back to the image of `τ ζ` on `Y`. -/
theorem appTop_structMap_eq {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    (g : Y ⟶ X) (τ : k →+* k) (hg : g ≫ fX = fY ≫ Spec.map (CommRingCat.ofHom τ))
    (m : Scheme.Etale.mk (𝟙 Y) ⟶ (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))) (c : k) :
    m.left.appTop.hom ((pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop.hom
        (Stacks.Kummer.structMap fX (Scheme.Etale.mk (𝟙 X)) c)) =
      Stacks.Kummer.structMap fY (Scheme.Etale.mk (𝟙 Y)) (τ c) := by
  have h1 : m.left ≫ pullback.snd (Scheme.Etale.mk (𝟙 X)).hom g = 𝟙 Y :=
    m.w.trans (Category.comp_id _)
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
    have eX : fX.appTop ≫ (Scheme.Etale.mk (𝟙 X)).hom.appTop = fX.appTop :=
      (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop (Category.id_comp fX))
    have eY : fY.appTop ≫ (Scheme.Etale.mk (𝟙 Y)).hom.appTop = fY.appTop :=
      (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop (Category.id_comp fY))
    have em : (pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop ≫ m.left.appTop = g.appTop :=
      (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop hm)
    have eg : fX.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom τ)).appTop ≫ fY.appTop :=
      (Scheme.Hom.comp_appTop _ _).symm.trans ((congrArg Scheme.Hom.appTop hg).trans
        (Scheme.Hom.comp_appTop _ _))
    have t1 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop ≫
        (Scheme.Etale.mk (𝟙 X)).hom.appTop) ≫
        (pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop ≫ m.left.appTop =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (fX.appTop ≫ (Scheme.Etale.mk (𝟙 X)).hom.appTop) ≫
          ((pullback.fst (Scheme.Etale.mk (𝟙 X)).hom g).appTop ≫ m.left.appTop) := by
      simp only [Category.assoc]
    refine t1.trans (Eq.trans (congrArg₂ (fun a b => (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      a ≫ b) eX em) (Eq.trans (congrArg ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ·) eg) ?_))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fY.appTop)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ)).symm).trans
        (congrArg ((CommRingCat.ofHom τ ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv) ≫ ·) eY.symm))
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
            (Stacks.Kummer.etaleModuleConstantUnderlyingIso fX hζ hn).hom) ≫
        Stacks.Kummer.rootsOfUnityInverseImageComparison.{u, 0} g n =
      (w : ℤ) • (etaleModuleUnderlyingAbelianConstantMap (ZMod n) Y ≫
        (Stacks.Kummer.etaleModuleConstantUnderlyingIso fY hζ hn).hom) := by
  refine (cancel_mono (Stacks.Kummer.rootsOfUnityι.{u, 0} Y n)).1 ?_
  rw [Category.assoc, Category.assoc,
    Stacks.Kummer.rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, ← Category.assoc
      ((etaleAbelianInverseImage.{u, 0} g).map _), ← Functor.map_comp, Category.assoc,
    constantMap_comp_underlyingIso_comp_ι, Preadditive.zsmul_comp, Category.assoc,
    constantMap_comp_underlyingIso_comp_ι]
  set Φ := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (uliftIntToULiftHom.{u} (ZMod n)) ≫ Stacks.Kummer.rootSheafHom fX hζ hn with hΦ
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
  have hnat := ConcreteCategory.congr_hom
    ((Stacks.Kummer.multiplicativeInverseImageComparison.{u, 0} g).hom.naturality
      ((IsTerminal.isTerminalObj (smallEtaleBaseChange g) (Scheme.Etale.mk (𝟙 X))
        (isTerminalEtaleMkId X)).from (Scheme.Etale.mk (𝟙 Y))).op)
    (((etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} X)).hom.app (Opposite.op (Scheme.Etale.mk (𝟙 X)))
      (Stacks.Kummer.ofUnit (Stacks.Kummer.rootOn fX hζ hn (Scheme.Etale.mk (𝟙 X)))))
  refine hnat.trans ((congrArg (fun z => (Stacks.Kummer.multiplicativeSheaf.{u, 0} Y).obj.map
    ((IsTerminal.isTerminalObj (smallEtaleBaseChange g) (Scheme.Etale.mk (𝟙 X))
        (isTerminalEtaleMkId X)).from (Scheme.Etale.mk (𝟙 Y))).op z)
    (Stacks.Kummer.multiplicativeInverseImageComparison_app_ofUnit.{u, 0} g
      (Scheme.Etale.mk (𝟙 X)) _)).trans (Eq.trans (Stacks.Kummer.map_ofUnit _ _) ?_))
  have hz : ∀ (φ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ Stacks.Kummer.multiplicativeSheaf.{u, 0} Y) (x),
      ((w : ℤ) • φ).hom.app (Opposite.op (Scheme.Etale.mk (𝟙 Y))) x =
        (w : ℤ) • φ.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 Y))) x :=
    fun _ _ => rfl
  refine Eq.trans ?_ (hz _ _).symm
  refine Eq.trans ?_ (congrArg ((w : ℤ) • ·) (rootSheafHom_app_one hζ hn fY _)).symm
  refine Eq.trans ?_ (Stacks.Kummer.zsmul_ofUnit _ _ _).symm
  refine congrArg Stacks.Kummer.ofUnit (Units.ext ?_)
  have := appTop_structMap_eq fX fY g τ hg ((IsTerminal.isTerminalObj (smallEtaleBaseChange g)
    (Scheme.Etale.mk (𝟙 X)) (isTerminalEtaleMkId X)).from (Scheme.Etale.mk (𝟙 Y))) ζ
  rwa [hτ, map_pow] at this

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
        (Sheaf.H.map (Stacks.Kummer.etaleModuleConstantUnderlyingIso fX hζ hn).hom i
          (extForgetSheafH (ZMod n) X _ i e)) =
      (w : ℤ) • Sheaf.H.map (Stacks.Kummer.etaleModuleConstantUnderlyingIso fY hζ hn).hom i
        (extForgetSheafH (ZMod n) Y _ i (constantExtRestriction (ZMod n) g i e)) :=
  map_restriction_extForgetSheafH n g _ _ _ _
    (rootsOfUnity_twist hζ hn fX fY g τ w hg hτ) e

end Twist

end Stacks.EtaleCohomology

end

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative

/-!
# Induction along elementary distinguished squares for derived direct images

Let `x : X ⟶ Z` be a morphism of algebraic spaces over a scheme `S`, with `X` quasi-compact and
quasi-separated. Combining the induction principle of Stacks 08GP with the relative
Mayer–Vietoris triangle of Stacks 08JK gives a statement about derived direct images: given a
triangulated subcategory `P` of `D(𝒪_Z)` and, for each algebraic space `Y`, a class `𝓔_Y` of
objects of `D(𝒪_Y)` stable under étale restriction, if `R(y ≫ x)_* E` lies in `P` for every
affine `Y` étale over `X` and every `E` in `𝓔_Y`, then `Rx_* E` lies in `P` for every `E` in
`𝓔_X`.

## Main results

* `AlgebraicGeometry.Space.restrictPushDerivedUnit` and
  `AlgebraicGeometry.Space.isRightDerivedFunctor_restrictPushDerivedUnit`: for an étale
  `e : U ⟶ W` and a right derived functor `Rg` of `g_*`, the composite of the exact functor
  induced by `e^*` with `Rg` is a right derived functor of `g_* ∘ e^*`.
* `AlgebraicGeometry.Space.prop_derivedPushforward_of_square`: a triangulated subcategory of
  `D(𝒪_Z)` that contains the three restricted derived direct images of `E` across an elementary
  distinguished square contains `Rw E` as well, because the four sit in the relative
  Mayer–Vietoris triangle of Stacks 08JK.
* `AlgebraicGeometry.Space.prop_derivedPushforward_of_affine`: the induction.

## References

* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08JK](https://stacks.math.columbia.edu/tag/08JK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section RestrictPush

variable {U W Z : AlgebraicSpaces B S hS} (e : U ⟶ W) (he : IsEtale B S hS e.hom) (g : U ⟶ Z)
  (Rg : DerivedCategory (Modules.{u, u} B S hS U.1 U.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
  (αg : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rg)

/-- The comparison exhibiting `e^* ⋙ Rg` as a right derived functor of `g_* ∘ e^*`. -/
def restrictPushDerivedUnit :
    (etaleModulePullback.{u, u} B S hS e he ⋙ modulePushforward B S hS g).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ ((etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory ⋙ Rg) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (etaleModulePullback.{u, u} B S hS e he ⋙ modulePushforward B S hS g))
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((etaleModulePullback.{u, u} B S hS e he).mapHomotopyCategory
      (ComplexShape.up ℤ)) αg ≫
    Functor.whiskerRight (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategoryFactorsh.inv
      Rg

/-- For an étale `e` and a right derived functor `Rg` of `g_*`, the functor `e^* ⋙ Rg` is a right
derived functor of `g_* ∘ e^*`, with comparison `AlgebraicGeometry.Space.restrictPushDerivedUnit`.
-/
theorem isRightDerivedFunctor_restrictPushDerivedUnit
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS U.1 U.2) (ComplexShape.up ℤ))] :
    ((etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory ⋙ Rg).IsRightDerivedFunctor
      (restrictPushDerivedUnit B S hS e he g Rg αg)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)) := by
  have := isGrothendieckAbelian_modules B S hS W.1 W.2
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I hI => ?_
  have hI' := isKInjective_etaleModulePullback B S hS e he
    (etaleModuleLowerShriekAdjunction B S hS e he) I hI
  have h2 : IsIso (αg.app (((etaleModulePullback.{u, u} B S hS e he).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
    isIso_app_of_isKInjective_modulePushforward B S hS g DerivedCategory.Qh Rg αg
      (((etaleModulePullback.{u, u} B S hS e he).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) hI'
  simp only [restrictPushDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

end RestrictPush

section Square

/-- **The relative Mayer–Vietoris triangle closes a triangulated subcategory.** Let
`(U ⊆ W, V ⟶ W)` be an elementary distinguished square with intersection `P`, let `w : W ⟶ Z` and
let `Rw`, `Ra`, `Rb`, `Rc` be right derived functors of the direct images along `w` and along its
restrictions to `U`, `V` and `P`. If a triangulated subcategory of `D(𝒪_Z)` contains
`Ra(E|_U)`, `Rb(E|_V)` and `Rc(E|_P)`, it contains `Rw E`: the four objects sit in the
distinguished triangle of Stacks 08JK. -/
theorem prop_derivedPushforward_of_square {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) {Z : AlgebraicSpaces B S hS}
    (w : W ⟶ Z) (P : ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (Rw : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αw : (modulePushforward B S hS w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor αw
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (Ra : DerivedCategory (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αa : (modulePushforward B S hS (edsOpenHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ra)
    [Ra.IsRightDerivedFunctor αa (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (Rb : DerivedCategory
        (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αb : (modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rb)
    [Rb.IsRightDerivedFunctor αb (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (Rc : DerivedCategory
        (Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αc : (modulePushforward B S hS (edsInterHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rc)
    [Rc.IsRightDerivedFunctor αc (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hA : P (Ra.obj ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E)))
    (hB : P (Rb.obj ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)))
    (hC : P (Rc.obj ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E))) :
    P (Rw.obj E) := by
  have hU := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) (edsOpenHom B S hS hsq ≫ w) Ra αa
  have hV := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) (edsEtaleHom B S hS hsq ≫ w) Rb αb
  have hP := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) (edsInterHom B S hS hsq ≫ w) Rc αc
  obtain ⟨fU, fV', gU, gV, δ, hT⟩ :=
    exists_mem_distTriang_edsRelativeMayerVietoris_unconditional B S hS hsq w Rw _ _ _ αw
      (restrictPushDerivedUnit B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
        (edsOpenHom B S hS hsq ≫ w) Ra αa)
      (restrictPushDerivedUnit B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
        (edsEtaleHom B S hS hsq ≫ w) Rb αb)
      (restrictPushDerivedUnit B S hS (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)
        (edsInterHom B S hS hsq ≫ w) Rc αc)
      inferInstance hU hV hP E
  have hmid := P.ext_of_isTriangulatedClosed₂ _ (binaryBiproductTriangle_distinguished _ _) hA hB
  exact P.ext_of_isTriangulatedClosed₁ _ hT hmid hC

end Square

section Induction

/-- **Induction on quasi-compact quasi-separated étale objects for derived direct images.** Let
`x : X ⟶ Z` with `X` quasi-compact and quasi-separated, `P` a triangulated subcategory of
`D(𝒪_Z)`, and `𝓔_Y ⊆ D(𝒪_Y)` classes of objects stable under étale restriction. If for every
affine `Y` étale over `X` along `y`, every right derived functor of `(y ≫ x)_*` carries `𝓔_Y`
into `P`, then every right derived functor of `x_*` carries `𝓔_X` into `P`. This is the
induction principle of Stacks 08GP run with the relative Mayer–Vietoris triangle of Stacks 08JK
(`AlgebraicGeometry.Space.prop_derivedPushforward_of_square`). -/
theorem prop_derivedPushforward_of_affine (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Z : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (x : X ⟶ Z)
    (P : ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (𝓔 : ∀ Y : AlgebraicSpaces B S hS,
      ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)))
    (h𝓔 : ∀ {Y Y' : AlgebraicSpaces B S hS} (e : Y' ⟶ Y) (he : IsEtale B S hS e.hom) E,
      𝓔 Y E → 𝓔 Y' ((etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory.obj E))
    (haff : ∀ (Y : AlgebraicSpaces B S hS) (y : Y ⟶ X), IsEtale B S hS y.hom →
      IsAffineSpace B S hS Y.1 → ∀ E, 𝓔 Y E →
      ∀ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS (y ≫ x)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
        P (R.obj E))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : 𝓔 X E)
    (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (α : (modulePushforward B S hS x).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    P (R.obj E) := by
  let Φ : (Y : AlgebraicSpaces B S hS) → (Y ⟶ Z) → Prop := fun Y m =>
    ∀ E, 𝓔 Y E → ∀ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS m).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
        P (R.obj E)
  have hcongr : ∀ {Y : AlgebraicSpaces B S hS} {m m' : Y ⟶ Z}, m = m' → Φ Y m → Φ Y m' :=
    fun e h => e ▸ h
  have key := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Yp φ => ∀ hY : IsAlgebraicSpace B S hS Yp, IsEtale B S hS φ →
      Φ ⟨Yp, hY⟩ (ObjectProperty.homMk φ ≫ x))
    (fun V hV hY hφ E hE R α hR =>
      haff ⟨V.1.left.1, hY⟩ (ObjectProperty.homMk V.1.hom.hom) hφ hV E hE R α hR)
    (by
      intro W V U f hcomm hsq _ _ _ _ hU hV hInter hY hφ E hE R α hR
      let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hY⟩
      have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 U f := hsq
      let w : W' ⟶ Z := ObjectProperty.homMk W.1.hom.hom ≫ x
      have hUΦ : Φ (edsOpen B S hS hsq') (edsOpenHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ rfl)).trans (Category.assoc _ _ _))
          (hU hsq'.isOpenSubspace.1 (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq') W.2))
      have hVΦ : Φ (edsEtale B S hS hsq') (edsEtaleHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ hcomm.symm)).trans
            (Category.assoc _ _ _))
          (hV hsq'.isAlgebraicSpace V.2)
      have hPΦ : Φ (edsInter B S hS hsq') (edsInterHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm)).trans
            (Category.assoc _ _ _))
          (hInter (edsInter B S hS hsq').2 (by
            simpa only [Category.assoc] using
              isEtale_comp B S hS (f := pullback.fst U.ι f ≫ U.ι)
                (isEtale_edsInterHom B S hS hsq') W.2))
      have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS
        (X := edsOpen B S hS hsq') (Z := Z) (modulePushforward B S hS (edsOpenHom B S hS hsq' ≫ w))
      have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS
        (X := edsEtale B S hS hsq') (Z := Z)
        (modulePushforward B S hS (edsEtaleHom B S hS hsq' ≫ w))
      have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS
        (X := edsInter B S hS hsq') (Z := Z)
        (modulePushforward B S hS (edsInterHom B S hS hsq' ≫ w))
      let Ra := ((modulePushforward B S hS (edsOpenHom B S hS hsq' ≫ w)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      let αa := ((modulePushforward B S hS (edsOpenHom B S hS hsq' ≫ w)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      let Rb := ((modulePushforward B S hS (edsEtaleHom B S hS hsq' ≫ w)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      let αb := ((modulePushforward B S hS (edsEtaleHom B S hS hsq' ≫ w)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      let Rc := ((modulePushforward B S hS (edsInterHom B S hS hsq' ≫ w)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      let αc := ((modulePushforward B S hS (edsInterHom B S hS hsq' ≫ w)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      exact prop_derivedPushforward_of_square B S hS hsq' w P R α Ra αa Rb αb Rc αc E
        (hUΦ _ (h𝓔 _ _ E hE) Ra αa inferInstance)
        (hVΦ _ (h𝓔 _ _ E hE) Rb αb inferInstance)
        (hPΦ _ (h𝓔 _ _ E hE) Rc αc inferInstance))
  exact hcongr (ObjectProperty.hom_ext _ (Category.id_comp _))
    (key X.2 (isEtale_id B S hS X.1)) E hE R α inferInstance

end Induction

end AlgebraicGeometry.Space

end

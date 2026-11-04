module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonZariskiReadingCompat

/-!
# The scheme restriction maps of Stacks 084A on the attached quasi-coherent modules

For a morphism `τ : T' ⟶ T` of the site and a scheme point `f` of an algebraic space `X` at `T`,
the comparison `τ^*(f^*𝒜)_Zar ⟶ ((f ∘ τ)^*𝒜)_Zar` of restricted algebras
(`AlgebraicGeometry.Space.pointComparison`) in degree `n`, carried to the modules attached by
Stacks 03DX (2), is the composition comparison of inverse images of Stacks 03LU.

The proof reflects the equation along the reading on the scheme of `T'`: the readings of the
three factors are the base comparison `AlgebraicGeometry.Space.representedZariskiModulePullbackIso`
and the base identifications of Stacks 03DX (2), and the remaining compatibility is the mate
computation `pullback_map_zariskiReadingIso_hom_comp_homEquiv_symm_of_compat`. Throughout, the
pieces of pulled-back graded algebras are kept in one spelling inside each declaration: unifying
`((gradedPull f).obj 𝒜).piece n` with `(modulePullback f).obj (𝒜.piece n)` under metavariables is
expensive.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `pointComparison_app_eq`: the comparison in one degree is the mate of the identification of the
  Zariski reading of a direct image, followed by the Zariski reading of the transposed restriction
  map.
* `modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_eq_of_compat`: the same statement
  for an arbitrary quasi-coherent module, reflected along the reading on the scheme
  (`QuasiCoherentDescent.bijective_representedZariski_map`).
* `modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_of_compat`: **the
  comparison of restricted algebras, carried to the attached modules, is the composition
  comparison of Stacks 03LU**, granted `ZariskiReadingDirectImageCompat`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (τ : T' ⟶ T)

/-- **The comparison of restricted algebras in one degree is the mate of the identification of
the Zariski reading of a direct image, followed by the Zariski reading of the transposed
restriction map** (which is the composition comparison of Stacks 03LU, by
`AlgebraicGeometry.Space.homEquiv_symm_gradedPullRestrictionApp`). -/
theorem pointComparison_app_eq {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    (pointComparison A τ f f' hf).app n =
      ((Stacks.RingedSpace.pullbackAdjunction
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
            ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app
              ((etalePointAlgebra A T f).piece n)) ≫
          (zariskiDirectImageNatTrans τ).app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj
              ((etalePointAlgebra A T f).piece n))) ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
          (((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv _ _).symm
            (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
              (pointHom_comp τ hf) A n)) := by
  have h6 : (pointComparison A τ f f' hf).app n =
      ((Stacks.RingedSpace.pullbackAdjunction
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
            (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
              (pointHom_comp τ hf) A n) ≫
          (zariskiDirectImageNatTrans τ).app ((etalePointAlgebra A T' f').piece n)) := rfl
  refine h6.trans ?_
  exact Adjunction.homEquiv_symm_map_comp_app_eq
    (etaleModuleAdjunction (representedSpaceMap B S hS τ))
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)))
    (zR := SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T))
    (zR' := SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T'))
    (zariskiDirectImageNatTrans τ) _
    (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
      (pointHom_comp τ hf) A n) rfl

/-- **The reading of the comparisons of restricted modules, at variables.**  For `τ : T' ⟶ T`, a
quasi-coherent `N` on `yoneda.obj T`, a quasi-coherent `N'` on `yoneda.obj T'` and
`m : φ^*N ⟶ N'`, let `p : τ^*(N_Zar) ⟶ N'_Zar` be the mate of the identification of the Zariski
reading of a direct image followed by the reading of `m`.  Then, granted the compatibility
`AlgebraicGeometry.Space.ZariskiReadingDirectImageCompat τ`, the module attached by Stacks 03DX (2)
to `p`, read through the identifications `N ≅ (N_Zar)^a`, `N' ≅ (N'_Zar)^a` and
`φ^*(M^a) ≅ (τ^*M)^a`, is `m`. -/
theorem modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_eq_of_compat
    (hH : ZariskiReadingDirectImageCompat τ)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    (N' : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (hN' : N'.IsQuasicoherentOnSite)
    (m : (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS τ)).toRingedToposModulesHom.pullbackModules.obj N ⟶ N')
    (p : (quasicoherentPullbackObj B S hS τ (zariskiReadingQcoh T N hN)).obj ⟶
      (zariskiReadingQcoh T' N' hN').obj)
    (hp : p = ((Stacks.RingedSpace.pullbackAdjunction
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
            ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
          (zariskiDirectImageNatTrans τ).app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map m) :
    (modulePullback B S hS (representedSpaceMap B S hS τ)).map
        (zariskiReadingQuasicoherentIso T N hN).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS τ (zariskiReadingQcoh T N hN)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
          (ObjectProperty.homMk p)).hom =
      m ≫ (zariskiReadingQuasicoherentIso T' N' hN').hom := by
  have hA : ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS τ
        (relativelyRepresentable_yoneda_map B S hS τ) N hN
  have hinj := (QuasiCoherentDescent.bijective_representedZariski_map B S hS
    ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)
    ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj
      (zariskiReadingQcoh T' N' hN')).obj hA).1
  have hM := ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
    (zariskiReadingQcoh T N hN)).property
  have h1 := (representedZariskiModulePullbackIso_naturality B S hS τ
      (relativelyRepresentable_yoneda_map B S hS τ) hN hM
    (zariskiReadingQuasicoherentIso T N hN).hom).symm
  have h2 := congrArg Iso.hom
    (representedZariski_mapIso_modulePullbackRepresentedQuasicoherentIso B S hS τ
      (zariskiReadingQcoh T N hN))
  have h3 := ((Iso.eq_inv_comp _).1
    (representedZariskiModuleQuasicoherentSchemeIso_naturality B S hS
      (ObjectProperty.homMk p : quasicoherentPullbackObj B S hS τ (zariskiReadingQcoh T N hN) ⟶
        zariskiReadingQcoh T' N' hN'))).symm
  have hB := representedZariski_map_zariskiReadingQuasicoherentIso_hom T N hN
  have hB' := representedZariski_map_zariskiReadingQuasicoherentIso_hom T' N' hN'
  have hUZ := pullback_map_zariskiReadingIso_hom_comp_homEquiv_symm_of_compat τ hH N hN
  have e2a : (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map ((zariskiReadingIso
              T).hom.app N) ≫
      ((Stacks.RingedSpace.pullbackAdjunction
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
            ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
          (zariskiDirectImageNatTrans τ).app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
          τ.left ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj N)
          (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          ((representedModulePullbackIso B S hS τ
            (relativelyRepresentable_yoneda_map B S hS τ)).inv.app N) ≫
        (zariskiReadingIso T').hom.app
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N) := hUZ
  have e2 : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) τ.left)).map ((zariskiReadingIso T).hom.app N) ≫
      ((Stacks.RingedSpace.pullbackAdjunction
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
            ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
          (zariskiDirectImageNatTrans τ).app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) =
      (representedZariskiModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ)
          N hN).hom ≫
        (zariskiReadingIso T').hom.app
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N) := by
    refine e2a.trans ?_
    have e2' : (representedZariskiModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map
        B S hS τ) N hN).hom =
        (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
          τ.left ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj N)
          (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          (((representedModulePullbackIso B S hS τ
            (relativelyRepresentable_yoneda_map B S hS τ)).app N).inv) :=
      representedZariskiModulePullbackIso_hom B S hS τ _ N hN
    rw [← Iso.app_inv, ← Category.assoc, e2']
  have e3 := ((zariskiReadingIso T').hom.naturality m).symm
  have hU : (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) τ.left)).map ((zariskiReadingIso T).app N).hom ≫ p =
      (representedZariskiModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ)
          N hN).hom ≫
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map (m ≫ 𝟙 N') ≫
        ((zariskiReadingIso T').app N').hom := by
    subst hp
    calc _ = ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) τ.left)).map ((zariskiReadingIso T).hom.app N) ≫
          ((Stacks.RingedSpace.pullbackAdjunction
            (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
              ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
            (zariskiDirectImageNatTrans τ).app
              ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N))) ≫
          (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map m :=
              (Category.assoc _ _ _).symm
      _ = ((representedZariskiModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map B S
          hS τ)
            N hN).hom ≫
          (zariskiReadingIso T').hom.app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) ≫
          (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map m := congrArg (·
              ≫ _) e2
      _ = (representedZariskiModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map B S
          hS τ)
            N hN).hom ≫
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map m ≫ (zariskiReadingIso
                  T').hom.app N' :=
        (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e3)
      _ = _ := congrArg (fun k => (representedZariskiModulePullbackIso B S hS τ
          (relativelyRepresentable_yoneda_map B S hS τ) N hN).hom ≫
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse ⋙
            _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map k ≫
            (zariskiReadingIso T').hom.app N') (Category.comp_id m).symm
  have key := Adjunction.comp_comp_eq_of_reading
    ((representedSmallEtaleModuleEquivalence B S hS T').inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) τ.left))
    _ _ _ m (𝟙 N') (zariskiReadingQuasicoherentIso T' N' hN').hom hinj
    (representedZariskiModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ)
      N hN)
    (representedZariskiModulePullbackIso B S hS τ (relativelyRepresentable_yoneda_map B S hS τ)
      _ hM) _ _ _ hB h1
    (representedZariskiModuleQuasicoherentSchemeIso B S hS T'
      (quasicoherentPullbackObj B S hS τ (zariskiReadingQcoh T N hN))) h2
    (representedZariskiModuleQuasicoherentSchemeIso B S hS T' (zariskiReadingQcoh T' N' hN'))
    p h3 _ hB' hU
  have key' : (modulePullback B S hS (representedSpaceMap B S hS τ)).map
        (zariskiReadingQuasicoherentIso T N hN).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS τ (zariskiReadingQcoh T N hN)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
          (ObjectProperty.homMk p)).hom =
      m ≫ 𝟙 N' ≫ (zariskiReadingQuasicoherentIso T' N' hN').hom := key
  exact key'.trans (congrArg (fun k => m ≫ k) (Category.id_comp _))

/-- Bridge K with the transposed restriction map in place of the comparison of Stacks 03LU.
For `τ : T' ⟶ T` of the site and scheme points `f`, `f' = f ∘ τ` of `X`, the comparison
`τ^*(f^*𝒜)_n ⟶ (f'^*𝒜)_n` of restricted algebras (`AlgebraicGeometry.Space.pointComparison`),
carried to the attached modules of Stacks 03DX (2) and read through `N ≅ (N_Zar)^a` at both ends
and through `φ^*(M^a) ≅ (τ^*M)^a`, is the composition comparison `φ^*(f^*𝒜_n) ≅ (φ ≫ f)^*𝒜_n` of
Stacks 03LU followed by the transport along `φ ≫ f = f'`. -/
theorem modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_eq_homEquiv_symm_of_compat
    (hH : ZariskiReadingDirectImageCompat τ) {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    (modulePullback B S hS (representedSpaceMap B S hS τ)).map
        (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS τ
          (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
          (ObjectProperty.homMk ((pointComparison A τ f f' hf).app n) :
            quasicoherentPullbackObj B S hS τ
              (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)) ⟶
            zariskiReadingQcoh T' ((etalePointAlgebra A T' f').piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n))).hom =
      ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv _ _).symm
          (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A n) ≫
          (zariskiReadingQuasicoherentIso T' ((etalePointAlgebra A T' f').piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)).hom := by
  have k := modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_eq_of_compat τ hH
    ((etalePointAlgebra A T f).piece n) (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)
    ((etalePointAlgebra A T' f').piece n) (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)
    (((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv _ _).symm
      (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
        (pointHom_comp τ hf) A n))
    ((pointComparison A τ f f' hf).app n) (pointComparison_app_eq τ A f f' hf n)
  exact k

/-- **Bridge K, granted the compatibility of the comparisons of direct images: the scheme
restriction maps of Stacks 084A are the Zariski readings of the comparisons of Stacks 03LU.**
For `τ : T' ⟶ T` of the site and scheme points `f`, `f' = f ∘ τ` of `X`, the comparison
`τ^*(f^*𝒜)_n ⟶ (f'^*𝒜)_n` of restricted algebras (`AlgebraicGeometry.Space.pointComparison`),
carried to the attached modules of Stacks 03DX (2) and read through `N ≅ (N_Zar)^a` at both ends
and through `φ^*(M^a) ≅ (τ^*M)^a`, is the composition comparison `φ^*(f^*𝒜_n) ≅ (φ ≫ f)^*𝒜_n` of
Stacks 03LU followed by the transport along `φ ≫ f = f'`. -/
theorem modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_of_compat
    (hH : ZariskiReadingDirectImageCompat τ) {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    (modulePullback B S hS (representedSpaceMap B S hS τ)).map
        (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS τ
          (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map
          (ObjectProperty.homMk ((pointComparison A τ f f' hf).app n) :
            quasicoherentPullbackObj B S hS τ
              (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f n)) ⟶
            zariskiReadingQcoh T' ((etalePointAlgebra A T' f').piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n))).hom =
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
          (A.piece n) ≫ pullbackTransport (A.piece n) (pointHom_comp τ hf)) ≫
        (zariskiReadingQuasicoherentIso T' ((etalePointAlgebra A T' f').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)).hom := by
  have ka :=
    modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_eq_homEquiv_symm_of_compat
    τ hH A hA f f' hf n
  have k1 := homEquiv_symm_gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f)
    (pointHom f') (pointHom_comp τ hf) A n
  have s1 : ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv _ _).symm
          (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A n) ≫
        (zariskiReadingQuasicoherentIso T' ((etalePointAlgebra A T' f').piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)).hom =
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
          (A.piece n) ≫ pullbackTransport (A.piece n) (pointHom_comp τ hf)) ≫
        (zariskiReadingQuasicoherentIso T' ((etalePointAlgebra A T' f').piece n)
            (isQuasicoherentOnSite_etalePointAlgebra_piece A hA f' n)).hom := congrArg (· ≫ _) k1
  exact ka.trans s1

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Transpose
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiKernelChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonZariskiReadingCompat

/-!
# The Zariski reading of an adjoint along a morphism of representable algebraic spaces

For a morphism `τ : T' ⟶ T` of the site, the Zariski reading of the adjoint, along the inverse
image of Stacks 03LU, of a map `v : τ^*N ⟶ H` of modules on the represented algebraic spaces is
the adjoint along the morphism of schemes `T' ⟶ T` of the scheme-side reading of `v`.  This is
the represented step of the chart dictionary of Stacks 085L.

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.pushforward_map_homEquiv_comp_zariskiDirectImage`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.C1359Bridge

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (τ : T' ⟶ T)

/-- **The kernel of an adjoint along a morphism of schemes, on sections.**  For `f : Y ⟶ X` and
`g : f^*A ⟶ B`, the adjoint `A ⟶ f_*B` of `g` kills a section `a` of `A` over `U` exactly when `g`
kills the pulled-back section of `a` over `f⁻¹(U)`. -/
theorem homEquiv_val_app_eq_zero_iff_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : X.Modules) (B : Y.Modules) (g : (Scheme.Modules.pullback f).obj A ⟶ B) (U : X.Opens)
    (a : A.val.obj (op U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A B g).val.app (op U) a = 0 ↔
      g.val.app (op (f ⁻¹ᵁ U)) (Scheme.Modules.pullbackSection f A U (f ⁻¹ᵁ U) le_rfl a) = 0 := by
  rw [Scheme.Modules.pullbackSection_homEquiv]
  have h : (homOfLE (le_rfl : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U)).op = 𝟙 (op (f ⁻¹ᵁ U)) := rfl
  rw [h, PresheafOfModules.map_id]
  exact Iff.rfl

/-- A section is killed by a morphism followed by an isomorphism exactly when it is killed by the
morphism. -/
theorem sheafOfModules_comp_iso_hom_val_app_eq_zero_iff {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M H H' : SheafOfModules.{u} R}
    (φ : M ⟶ H) (e : H ≅ H') (W : Cᵒᵖ) (x : M.val.obj W) :
    (φ ≫ e.hom).val.app W x = 0 ↔ φ.val.app W x = 0 := by
  refine ⟨fun h => ?_, fun h => by change e.hom.val.app W (φ.val.app W x) = 0; rw [h, map_zero]⟩
  have h2 : (φ ≫ e.hom ≫ e.inv).val.app W x = 0 := by
    change e.inv.val.app W ((φ ≫ e.hom).val.app W x) = 0
    rw [h, map_zero]
  rwa [e.hom_inv_id, Category.comp_id] at h2

/-- A section is killed by a morphism followed by an invertible morphism exactly when it is killed
by the morphism. -/
theorem sheafOfModules_comp_isIso_val_app_eq_zero_iff {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M H H' : SheafOfModules.{u} R}
    (φ : M ⟶ H) (e : H ⟶ H') [IsIso e] (W : Cᵒᵖ) (x : M.val.obj W) :
    (φ ≫ e).val.app W x = 0 ↔ φ.val.app W x = 0 :=
  sheafOfModules_comp_iso_hom_val_app_eq_zero_iff φ (asIso e) W x

/-- **The Zariski reading of an adjoint along a morphism of representable algebraic spaces is the
scheme adjoint.**  For `τ : T' ⟶ T` of the site, a quasi-coherent `N` on `yoneda.obj T` and
`v : τ^*N ⟶ H`, the Zariski reading of the adjoint of `v`, followed by the identification of the
reading of a direct image, is the adjoint along the morphism of schemes of the comparison
`τ^*(N_{Zar}) ≅ (τ^*N)_{Zar}` followed by the reading of `v`. -/
theorem pushforward_map_homEquiv_comp_zariskiDirectImage
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    {H : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (v : (modulePullback B S hS (representedSpaceMap B S hS τ)).obj N ⟶ H) :
    (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ)).homEquiv N H v) ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
        ((pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ)).inv.app H) ≫
      (zariskiDirectImageNatTrans τ).app H =
    (Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _
      ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((zariskiReadingIso T).app N).inv ≫
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
            (associatedBigEtaleSite B) τ.left
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj N)
            (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)).hom ≫
          (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((representedModulePullbackIso B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ)).inv.app N) ≫
          (zariskiReadingIso T').hom.app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map v) := by
  have hUZ := pullback_map_zariskiReadingIso_hom_comp_homEquiv_symm_of_compat τ
    (zariskiReadingDirectImageCompat τ) N hN
  exact map_homEquiv_comp_eq_homEquiv
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ))
    (etaleModuleAdjunction (representedSpaceMap B S hS τ))
    (pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ))
    (modulePullbackAdjunction_unit_app (representedSpaceMap B S hS τ)) _ _
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)))
    _ ((zariskiReadingIso T).app N) _ hUZ v


/-- **The kernel of an adjoint along a morphism of representable algebraic spaces, read on the
scheme.**  A section of `N` over the self-open of a Zariski open `W` is killed by the adjoint of
`v : τ^*N ⟶ H` exactly when it is killed by the scheme-side adjoint of the reading of `v`. -/
theorem homEquiv_val_app_selfOpens_eq_zero_iff
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    {H : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (v : (modulePullback B S hS (representedSpaceMap B S hS τ)).obj N ⟶ H)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ)).homEquiv N H v).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x = 0 ↔
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _
      ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((zariskiReadingIso T).app N).inv ≫
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
            (associatedBigEtaleSite B) τ.left
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj N)
            (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)).hom ≫
          (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((representedModulePullbackIso B S hS τ
              (relativelyRepresentable_yoneda_map B S hS τ)).inv.app N) ≫
          (zariskiReadingIso T').hom.app
            ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map v)).val.app
          (op W) x = 0 := by
  have h := pushforward_map_homEquiv_comp_zariskiDirectImage τ N hN v
  have hζ : IsIso ((zariskiDirectImageNatTrans τ).app H) := NatIso.isIso_app_of_isIso _ _
  rw [← h]
  exact (sheafOfModules_comp_iso_hom_val_app_eq_zero_iff
    ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
      ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ)).homEquiv N H v))
    ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).mapIso
      ((pushforwardModulesIsoModulePushforward B S hS (representedSpaceMap B S hS τ)).app H).symm ≪≫
      @asIso _ _ _ _ ((zariskiDirectImageNatTrans τ).app H) hζ) (op W) x).symm


/-- **The Zariski reading of `N ≅ (N_Zar)^a`, read back through the base identification, is the
identity.**  For a quasi-coherent `N` on `yoneda.obj T`, the Zariski reading of
`N ≅ (N_Zar)^a`, followed by the identification of the two Zariski readings of `(N_Zar)^a` and
the base identification of Stacks 03DX (2), is the identity of `N_Zar`. -/
theorem pushforward_map_zariskiReadingQuasicoherentIso_hom_comp (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
        (zariskiReadingQuasicoherentIso T N hN).hom ≫
      (zariskiReadingIso T).inv.app
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).obj ≫
      (representedZariskiModuleQuasicoherentSchemeIso B S hS T (zariskiReadingQcoh T N hN)).hom =
    𝟙 _ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (representedZariskiModuleQuasicoherentSchemeIso B S hS T
        (zariskiReadingQcoh T N hN)).hom)
      ((zariskiReadingIso T).inv.naturality (zariskiReadingQuasicoherentIso T N hN).hom)).trans
    ((Category.assoc _ _ _).trans
    ((congrArg ((zariskiReadingIso T).inv.app N ≫ ·)
      (representedZariski_map_zariskiReadingQuasicoherentIso_hom T N hN)).trans
    (Iso.inv_hom_id_app (zariskiReadingIso T) N))))

/-- Cancelling an isomorphism against its inverse at the head of a composite. -/
private theorem trans_trans_symm_trans_cancel {C : Type*} [Category C] {W X Y Z Z' : C}
    (e : W ≅ X) (a : W ≅ Y) (b : Y ≅ Z) (c : Z ≅ Z') :
    e ≪≫ ((e.symm ≪≫ a ≪≫ b) ≪≫ c) = a ≪≫ b ≪≫ c := by
  simp

/-- **The Zariski reading of the inverse image of an attached module, through the base
identifications.**  For `g : V ⟶ U` of the site and `M` quasi-coherent on the scheme of `U`, the
comparison of Stacks 03LU with pullback on schemes, followed by the identification of the two
Zariski readings and the Zariski reading of `g^*(M^a) ≅ (g^*M)^a`, is the pullback of the base
identification of `M` followed by the inverse base identification of `g^*M`. -/
theorem representedZariskiModulePullbackIso_trans_zariskiReadingIso_trans_mapIso
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property ≪≫
      (zariskiReadingIso V).app ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj) ≪≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS V)).mapIso
        (modulePullbackRepresentedQuasicoherentIso B S hS g M) =
    (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) g.left)).mapIso
        (representedZariskiModuleQuasicoherentSchemeIso B S hS U M) ≪≫
      (representedZariskiModuleQuasicoherentSchemeIso B S hS V
        (quasicoherentPullbackObj B S hS g M)).symm ≪≫
      (zariskiReadingIso V).app ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj
        (quasicoherentPullbackObj B S hS g M)).obj := by
  have hn : (zariskiReadingIso V).app ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj) ≪≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS V)).mapIso
        (modulePullbackRepresentedQuasicoherentIso B S hS g M) =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.mapIso
          (modulePullbackRepresentedQuasicoherentIso B S hS g M)) ≪≫
      (zariskiReadingIso V).app ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj
        (quasicoherentPullbackObj B S hS g M)).obj :=
    Iso.ext ((zariskiReadingIso V).hom.naturality
      (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom).symm
  have chart := representedZariski_mapIso_modulePullbackRepresentedQuasicoherentIso B S hS g M
  refine (congrArg (representedZariskiModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property ≪≫ ·)
        hn).trans ?_
  refine (congrArg (fun k => representedZariskiModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property ≪≫ k ≪≫
        (zariskiReadingIso V).app ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj
          (quasicoherentPullbackObj B S hS g M)).obj) chart).trans ?_
  exact trans_trans_symm_trans_cancel _ _ _ _


end AlgebraicGeometry.Space.C1359Bridge

end

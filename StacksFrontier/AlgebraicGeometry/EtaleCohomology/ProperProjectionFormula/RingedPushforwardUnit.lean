module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.DerivedDirectImage

/-!
# The derived-functor units of the two unbounded `Rf_*`, compared

For a morphism of schemes `f : X ⟶ Y` and a commutative ring `Λ`, the unbounded derived direct
image of sheaves of `Λ`-modules on small étale sites,
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`, is identified with the derived
direct image along the morphism of constant ringed topoi through
`Stacks.EtaleCohomology.etaleDerivedPushforwardIso`. This file records how that identification
treats the two derived-functor units `Q(f_* M) ⟶ Rf_*(Q M)`: read through the equivalences of
`Stacks.EtaleCohomology.etaleDerivedEquivalence`, the étale unit at a complex `M` is the
ringed-topos unit at the transported complex.

## Main results

* `map_etaleModuleDerivedDirectImageUnboundedUnit_comp_etaleDerivedPushforwardIso`, in the
  namespace `Stacks.EtaleCohomology`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The étale and ringed-topos derived-functor units of `Rf_*` agree.** For a complex `M` of
sheaves of `Λ`-modules on `X_étale`, `Φ_Y` of the étale unit `Q(f_* M) ⟶ Rf_*(Q M)` followed by
the identification `Φ_Y Rf_* ≅ Rf_* Φ_X` is the comparison of `Φ_Y Q(f_* M)` with the
ringed-topos direct image of the transported complex, followed by the ringed-topos unit and by
`Rf_*` of the comparison of `Q` with `Φ_X`. -/
theorem map_etaleModuleDerivedDirectImageUnboundedUnit_comp_etaleDerivedPushforwardIso
    (M : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app M) ≫
      (etaleDerivedPushforwardIso.{u, r} Λ f).hom.app (DerivedCategory.Q.obj M) =
    ((etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleDerivedPushforwardComparisonIso.{u, r} Λ f).hom.app M) ≫
      (etaleDerivedEquivalence.{u, r} Λ Y).counitIso.hom.app _) ≫
      (etaleRingedDerivedPushforwardUnit.{u, r} Λ f).app
        (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f).map
        ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom.app M) := by
  have h := Functor.rightDerivedNatTrans_app
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
    ((etaleDerivedEquivalence.{u, r} Λ X).functor ⋙ etaleRingedDerivedPushforward.{u, r} Λ f ⋙
      (etaleDerivedEquivalence.{u, r} Λ Y).inverse)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
    (etaleDerivedPushforwardComparisonUnit.{u, r} Λ f)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) (𝟙 _) M
  rw [NatTrans.id_app, Category.id_comp] at h
  have h' : (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app M) ≫
      (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleDerivedPushforwardIsoConj.{u, r} Λ f).hom.app (DerivedCategory.Q.obj M)) =
      (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleDerivedPushforwardComparisonUnit.{u, r} Λ f).app M) := by
    rw [← Functor.map_comp]
    exact congrArg (etaleDerivedEquivalence.{u, r} Λ Y).functor.map h
  simp only [etaleDerivedPushforwardIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  rw [reassoc_of% h']
  simp only [etaleDerivedPushforwardComparisonUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  congr 1
  simp only [Functor.comp_obj, Functor.comp_map, Equivalence.fun_inv_map, Category.assoc,
    Category.comp_id, Iso.inv_hom_id_app_assoc]

/-- **The étale unit of `Rf_*` at a complex `M`, read through the equivalences, is the
ringed-topos unit at any complex `I` isomorphic to the transported complex**, up to the
comparison isomorphisms on both ends. -/
theorem map_etaleModuleDerivedDirectImageUnboundedUnit_eq
    (M : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (I : HomotopyCategory (EtaleRingedModules.{u, r} Λ X) (ComplexShape.up ℤ))
    (γ : ((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M ≅ I) :
    (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app M) =
      ((etaleDerivedEquivalence.{u, r} Λ Y).functor.map
          ((etaleDerivedPushforwardComparisonIso.{u, r} Λ f).hom.app M) ≫
        (etaleDerivedEquivalence.{u, r} Λ Y).counitIso.hom.app _ ≫
        (etaleRingedPushforwardOnHomotopy.{u, r} Λ f).map γ.hom) ≫
      (etaleRingedDerivedPushforwardUnit.{u, r} Λ f).app I ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f).map (DerivedCategory.Qh.map γ.inv ≫
          (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom.app M) ≫
        (etaleDerivedPushforwardIso.{u, r} Λ f).inv.app (DerivedCategory.Q.obj M) := by
  have h := map_etaleModuleDerivedDirectImageUnboundedUnit_comp_etaleDerivedPushforwardIso Λ f M
  have hn : (etaleRingedPushforwardOnHomotopy.{u, r} Λ f).map γ.hom ≫
      (etaleRingedDerivedPushforwardUnit.{u, r} Λ f).app I =
      (etaleRingedDerivedPushforwardUnit.{u, r} Λ f).app _ ≫
        (etaleRingedDerivedPushforward.{u, r} Λ f).map (DerivedCategory.Qh.map γ.hom) :=
    (etaleRingedDerivedPushforwardUnit.{u, r} Λ f).naturality γ.hom
  rw [← Iso.cancel_iso_hom_right _ _
    ((etaleDerivedPushforwardIso.{u, r} Λ f).app (DerivedCategory.Q.obj M)), Iso.app_hom, h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
  rw [← Category.assoc ((etaleRingedPushforwardOnHomotopy.{u, r} Λ f).map γ.hom), hn]
  simp [← Functor.map_comp_assoc]

end Stacks.EtaleCohomology

end

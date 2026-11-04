module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeMateComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RightDerivedTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded

/-!
# The derived base change map at a complex of injectives

For a commutative square `f' ≫ g = g' ≫ f` of schemes and a bounded below complex `J` of injective
sheaves of `Λ`-modules on `X`, invertibility of the derived base change map
`g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` at `J`
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeGeneral`) says that the degreewise base change
map `g^{-1} f_* J ⟶ f'_* (g')^{-1} J`, followed by `f'_*` of any resolution of `(g')^{-1} J` by
injectives, is a quasi-isomorphism: this is `CategoryTheory.Functor.BaseChangeQuasiIsoAt`,
[Stacks, Tag 03UI] (1).

## Main results

* `Stacks.EtaleCohomology.baseChangeQuasiIsoAt_of_isIso_etaleModuleDerivedBaseChange`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme


universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

private lemma isIso_comp_comp_comp_of_isIso {C : Type*} [Category* C] {a b c d e : C}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) (t : d ⟶ e) [IsIso (x ≫ y)] [IsIso z] [IsIso t] :
    IsIso (x ≫ (y ≫ z) ≫ t) := by
  rw [← Category.assoc x, ← Category.assoc]
  infer_instance

/-- A bounded below complex of injectives is K-injective. -/
private lemma isKInjective_of_injective_plus {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex.Plus C) (hK : ∀ n, Injective (K.obj.X n)) : K.obj.IsKInjective := by
  obtain ⟨a, _⟩ := K.property
  have := hK
  exact CochainComplex.isKInjective_of_injective K.obj a

variable (Λ : Type) [Ring Λ] {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (f' : X' ⟶ Y') (w : f' ≫ g = g' ≫ f)

/-- **The derived base change map, invertible at a bounded below complex of injectives, is a
quasi-isomorphism after resolving.** -/
theorem baseChangeQuasiIsoAt_of_isIso_etaleModuleDerivedBaseChange
    (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hJ : ∀ n, Injective (J.obj.X n))
    (hiso : IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, 0} Λ f g g' f' w.symm).app
      (DerivedCategory.Q.obj J.obj))) :
    Functor.BaseChangeQuasiIsoAt (etaleModuleDirectImage.{u, 0} Λ f')
      (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleInverseImage.{u, 0} Λ g)
      (etaleModuleInverseImage.{u, 0} Λ g') (etaleModuleBaseChange Λ f f' g g' w) J := by
  refine Functor.BaseChangeQuasiIsoAt.of_eq _ _ _ _ ?_
    (etaleModuleBaseChange_eq_etaleModuleMateBaseChange Λ f f' g g' w).symm
  intro T ψ hψ hT
  have := isKInjective_of_injective_plus J hJ
  have := isKInjective_of_injective_plus T hT
  have h1 := (isIso_etaleModuleDerivedBaseChange_app_Q_iff.{u, 0} Λ f g g' f' w.symm J.obj).1 hiso
  have h2 : IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (etaleModuleBaseChangeGeneral.{u, 0} Λ f g g' f' w.symm) (ComplexShape.up ℤ)).app J.obj) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app
        (((etaleModuleInverseImage.{u, 0} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          J.obj)) := h1
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ f' T.obj inferInstance
  have : IsIso (DerivedCategory.Q.map ψ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 hψ
  have hnat := (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').naturality ψ.hom
  simp only [Functor.comp_map] at hnat
  have hQ : DerivedCategory.Q.map (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex
      (ComplexShape.up ℤ)).map ψ.hom) =
      ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app _ ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f').map (DerivedCategory.Q.map ψ.hom)) ≫
        inv ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app T.obj) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  show IsIso (DerivedCategory.Q.map (Functor.baseChangeComp _ _ _ _ _ J ψ).hom)
  rw [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  show IsIso (_ ≫ DerivedCategory.Q.map
    (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom))
  rw [hQ]
  exact @isIso_comp_comp_comp_of_isIso _ _ _ _ _ _ _ _ _ _ _ h2 inferInstance inferInstance

end Stacks.EtaleCohomology

end

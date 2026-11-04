module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InverseImageTorsion
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection

/-!
# Lower bounds and torsion along the unbounded direct and inverse images

For a morphism of schemes `f : X ⟶ Y` and a ring `Λ`, on the unbounded derived categories
`D(X_étale, Λ)` of sheaves of `Λ`-modules:

* the derived direct image `Rf_*` carries objects with no cohomology below `a` to objects with no
  cohomology below `a` ([Stacks, Tag 05TC]): such an object is represented by a complex of
  injective sheaves vanishing below `a`, which is K-injective, so `Rf_*` is computed on it
  termwise;
* the inverse image `f^{-1}`, being exact, preserves lower bounds and carries objects with torsion
  cohomology sheaves to objects with torsion cohomology sheaves.

These are the bookkeeping inputs of the proof of [Stacks, Tag 0F14] (1).

## Main results

* `Stacks.EtaleCohomology.isGE_etaleModuleDerivedDirectImageUnbounded_obj`
* `Stacks.EtaleCohomology.isGE_etaleModuleDerivedInverseImage_obj`
* `Stacks.EtaleCohomology.isTorsionEtaleModule_homology_etaleModuleDerivedInverseImage_obj`

## References

* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **The unbounded derived direct image preserves lower bounds** ([Stacks, Tag 05TC]). -/
theorem isGE_etaleModuleDerivedDirectImageUnbounded_obj (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (a : ℤ) (hK : K.IsGE a) :
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj K).IsGE a := by
  have : EnoughInjectives (EtaleModules.{u, r} Λ X) := IsGrothendieckAbelian.enoughInjectives
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  let P : ObjectProperty (EtaleModules.{u, r} Λ X) := Injective
  have : P.ContainsZero := ⟨0, isZero_zero _, inferInstance⟩
  obtain ⟨M, g, hg, hM, _, hge⟩ := CochainComplex.exists_quasiIso_prop_isStrictlyGE P
    (fun X => ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) a L
  have : ∀ n, Injective (M.X n) := hM
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f M
    (CochainComplex.isKInjective_of_injective M a)
  have : CochainComplex.IsStrictlyGE (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (etaleModuleDirectImage.{u, r} Λ f).map_isZero (M.isZero_of_isStrictlyGE a i hi)
  exact DerivedCategory.TStructure.t.isGE_of_iso (X := DerivedCategory.Q.obj
    (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
    (asIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app M) ≪≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).mapIso
        ((asIso (DerivedCategory.Q.map g)).symm ≪≫ e.symm)) a

/-- **The inverse image preserves lower bounds**: it is exact. -/
theorem isGE_etaleModuleDerivedInverseImage_obj (Λ : Type r) [CommRing Λ] {W X : Scheme.{u}}
    (g : W ⟶ X) (K : DerivedCategory (EtaleModules.{u, r} Λ X)) (a : ℤ) (hK : K.IsGE a) :
    ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj K).IsGE a :=
  Functor.isGE_obj_mapDerivedCategory (etaleModuleInverseImage.{u, r} Λ g) K a hK

/-- **The inverse image of an object with torsion cohomology sheaves has torsion cohomology
sheaves**: the inverse image is exact and carries torsion sheaves to torsion sheaves. -/
theorem isTorsionEtaleModule_homology_etaleModuleDerivedInverseImage_obj (Λ : Type) [CommRing Λ]
    {W X : Scheme.{u}} (g : W ⟶ X) (K : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (hK : ∀ n, IsTorsionEtaleModule.{u, 0} Λ X
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ X) n).obj K)) (n : ℤ) :
    IsTorsionEtaleModule.{u, 0} Λ W
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ W) n).obj
        ((etaleModuleDerivedInverseImage.{u, 0} Λ g).obj K)) :=
  IsTorsionEtaleModule.of_iso Λ W
    (((etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryHomologyIso n).app K).symm
    (isTorsionEtaleModule_etaleModuleInverseImage_obj Λ g _ (hK n))

end Stacks.EtaleCohomology

end

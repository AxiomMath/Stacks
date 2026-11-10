module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.GeometricStalkGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactPushforwardTwistTrace

/-!
# The derived stalk at a geometric point as derived global sections of the inverse image

Let `s : Spec Ω ⟶ X` be a geometric point and `C` a bounded below complex of sheaves of
`Λ`-modules on the small étale site of `X`. The derived stalk of `C` at `s` is
`RΓ(Spec Ω, s⁻¹ C)`, computed on the unbounded derived category: global sections over the spectrum
of an algebraically closed field are exact, and are the stalk at the canonical point
([Stacks, Tag 04JN]).

## Main results

* `Stacks.EtaleCohomology.nonempty_derivedEtaleModuleStalkIsoGlobalSectionsInverseImage`

## References

* [Stacks Project, Tag 04JN](https://stacks.math.columbia.edu/tag/04JN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModules_ab5OfSize etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

/-- Global sections over the spectrum of a separably closed field preserve homology, being an
equivalence onto modules. -/
theorem etaleModuleGlobalSections_preservesHomology_of_isSepClosed (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] : (etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω))).PreservesHomology := by
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{max (u + 1) r} Λ)
  infer_instance

/-- **The derived stalk at a geometric point is the derived global sections of the inverse image**
([Stacks, Tag 04JN]), for a bounded below complex of sheaves of `Λ`-modules. -/
theorem nonempty_derivedEtaleModuleStalkIsoGlobalSectionsInverseImage (s : GeometricPoint X.obj)
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ X.obj)) :
    Nonempty ((derivedEtaleModuleStalk.{u, r} B X Λ s).obj (DerivedCategory.Q.obj C.obj) ≅
      (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of s.residueField))).obj
        ((etaleModuleRingDerivedInverseImage.{u, r} Λ s.hom).obj
          (DerivedCategory.Q.obj C.obj))) := by
  let Γ := etaleModuleGlobalSections.{u, r} Λ (Spec (.of s.residueField))
  have := etaleModuleGlobalSections_preservesHomology_of_isSepClosed.{u, r} Λ s.residueField
  have : EnoughInjectives (EtaleModules.{u, r} Λ (Spec (.of s.residueField))) :=
    etaleModules_enoughInjectives.{u, r} Λ _
  let N := (etaleModuleInverseImage.{u, r} Λ s.hom).mapCochainComplexPlus.obj C
  obtain ⟨T, ψ, hψ, hT, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, r} Λ (Spec (.of s.residueField)))) N (𝟙 _)
  obtain ⟨b, _⟩ := T.property
  have := hT
  have : T.obj.IsKInjective := CochainComplex.isKInjective_of_injective T.obj b
  have := isIso_etaleModuleDerivedGlobalSectionsUnboundedUnit_app.{u, r} Λ
    (Spec (.of s.residueField)) T.obj inferInstance
  have : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom) := inferInstance
  have : IsIso (DerivedCategory.Q.map ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have : IsIso (DerivedCategory.Q.map ψ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 hψ
  let e₀ : ((etaleModuleStalk.{u, r} B X Λ s).mapHomologicalComplex (ComplexShape.up ℤ)).obj C.obj ≅
      (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj :=
    (NatIso.mapHomologicalComplex (etaleModuleStalkIsoInverseImageGlobalSections.{u, r} Λ s)
      (ComplexShape.up ℤ)).app C.obj ≪≫
      ((Functor.mapHomologicalComplexCompIso (F := etaleModuleInverseImage.{u, r} Λ s.hom)
        (G := Γ) (Iso.refl _) (ComplexShape.up ℤ)).symm.app C.obj)
  exact ⟨(etaleModuleStalk.{u, r} B X Λ s).mapDerivedCategoryFactors.app C.obj ≪≫
    DerivedCategory.Q.mapIso e₀ ≪≫
    asIso (DerivedCategory.Q.map ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom)) ≪≫
    asIso ((etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ
      (Spec (.of s.residueField))).app T.obj) ≪≫
    (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ (Spec (.of s.residueField))).mapIso
      ((asIso (DerivedCategory.Q.map ψ.hom)).symm ≪≫
        ((etaleModuleInverseImage.{u, r} Λ s.hom).mapDerivedCategoryFactors.app C.obj).symm)⟩

end Stacks.EtaleCohomology

end

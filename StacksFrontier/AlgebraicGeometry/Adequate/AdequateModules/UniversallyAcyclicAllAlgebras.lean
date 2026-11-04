module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.JointAcyclicity
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffinePullbackExtension
public import StacksFrontier.AlgebraicGeometry.Modules.QcohPullbackIsoTarget

/-!
# Universal acyclicity over an affine base is acyclicity of a module extension

Over an affine base `U = Spec A` the remaining input of [Stacks, Tag 06ZR] compares universal
acyclicity of a bounded below complex `K` of quasi-coherent `𝒪_U`-modules with the acyclicity of
a complex of module-valued functors on the `A`-algebras. This module proves that comparison, with
no hypothesis:

**a complex of quasi-coherent `𝒪_{Spec A}`-modules is universally acyclic exactly when the
complex of module-valued functors `C ↦ C ⊗_A Γ(Spec A, K)` is acyclic.**

Three inputs, each proved elsewhere. Universal acyclicity is tested over the spectra,
`Stacks.Adequate.universallyAcyclic_of_spec`, which rests on the affine open covers of
`Stacks.Adequate.universallyAcyclic_of_affine`. Over a spectrum `Spec C` acyclicity of the
pullback is acyclicity of the complex of `C`-modules `C ⊗_A Γ(Spec A, K)`,
`Stacks.Adequate.plus_subcategoryAcyclic_qcohPullback_spec_iff`. And acyclicity of a complex of
module-valued functors is acyclicity over each single algebra,
`Stacks.Homology.plus_acyclic_presheafOfModules_iff`.

## Main results

* `Stacks.Adequate.universallyAcyclic_spec_iff_forall_algebra` — universal acyclicity over
  `Spec A` is acyclicity of `C ⊗_A Γ(Spec A, K)` for every `A`-algebra `C`.
* `Stacks.Adequate.plus_subcategoryAcyclic_moduleExtension_iff_forall_algebra` — acyclicity of
  the complex of module-valued functors is the same family of conditions.
* `Stacks.Adequate.universallyAcyclic_spec_eq_inverseImage_moduleExtension` — **the two object
  properties are equal.**

## Implementation notes

An `A`-algebra is described twice over: as a morphism `φ : A ⟶ C` of `CommRingCat`, which is what
`AlgebraicGeometry.Spec.map` consumes, and as an object of `CommAlgCat A`, which is what the
module-valued functors are indexed by. The two readings are interchanged by
`AlgebraicGeometry.Spec.preimage` in one direction and by `RingHom.toAlgebra` in the other, and
the resulting ring maps agree definitionally, so the family of conditions is literally the same
family in both spellings.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {A : CommRingCat.{u}}

/-- **Universal acyclicity over `Spec A` is acyclicity of `C ⊗_A Γ(Spec A, K)` over every
`A`-algebra `C`.** The pullbacks over the spectra already see universal acyclicity, by
`Stacks.Adequate.universallyAcyclic_of_spec`, and over a spectrum the pullback is the extension
of scalars, by `Stacks.Adequate.plus_subcategoryAcyclic_qcohPullback_spec_iff`. -/
public theorem universallyAcyclic_spec_iff_forall_algebra
    (K : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory) :
    universallyAcyclic (Spec A) K ↔
      ∀ (C : CommRingCat.{u}) (φ : A ⟶ C),
        HomotopyCategory.Plus.subcategoryAcyclic (ModuleCat.{u} ↥C)
          (((tildeEquiv (R := A)).inverse ⋙
            ModuleCat.extendScalars φ.hom).mapHomotopyCategoryPlus.obj K) := by
  constructor
  · intro hK C φ
    exact (plus_subcategoryAcyclic_qcohPullback_spec_iff A C φ K).1
      ((universallyAcyclic_iff K).1 hK _ (Spec.map φ))
  · intro h
    refine universallyAcyclic_of_spec K fun R g => ?_
    rw [← Spec.map_preimage g]
    exact (plus_subcategoryAcyclic_qcohPullback_spec_iff A R (Spec.preimage g) K).2 (h R _)

/-- **Acyclicity of the complex of module-valued functors `C ↦ C ⊗_A Γ(Spec A, K)` is acyclicity
of `C ⊗_A Γ(Spec A, K)` over every `A`-algebra `C`.** Acyclicity of a complex of presheaves of
modules is acyclicity of its complex of sections over every object,
`Stacks.Homology.plus_acyclic_presheafOfModules_iff`, and the sections of the module extension
over an algebra are the extension of scalars,
`AdequateFunctor.moduleExtensionEvaluationIso`. -/
public theorem plus_subcategoryAcyclic_moduleExtension_iff_forall_algebra
    (K : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory) :
    HomotopyCategory.Plus.subcategoryAcyclic
        (AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A)
        (((tildeEquiv (R := A)).inverse ⋙
          AdequateFunctor.moduleExtensionFunctor.{u, u}
            ↥A).mapHomotopyCategoryPlus.obj K) ↔
      ∀ (C : CommRingCat.{u}) (φ : A ⟶ C),
        HomotopyCategory.Plus.subcategoryAcyclic (ModuleCat.{u} ↥C)
          (((tildeEquiv (R := A)).inverse ⋙
            ModuleCat.extendScalars φ.hom).mapHomotopyCategoryPlus.obj K) := by
  have key : ∀ X : ((CommAlgCat.{u} ↥A)ᵒᵖ)ᵒᵖ,
      HomotopyCategory.Plus.subcategoryAcyclic
          (ModuleCat.{u} ↥((AdequateFunctor.algebraRingDiagram.{u} ↥A).obj X))
          ((PresheafOfModules.evaluation.{u} (AdequateFunctor.algebraRingDiagram.{u} ↥A)
            X).mapHomotopyCategoryPlus.obj
              (((tildeEquiv (R := A)).inverse ⋙
                AdequateFunctor.moduleExtensionFunctor.{u, u}
                  ↥A).mapHomotopyCategoryPlus.obj K)) ↔
        HomotopyCategory.Plus.subcategoryAcyclic (ModuleCat.{u} ↥(X.unop.unop))
          (((tildeEquiv (R := A)).inverse ⋙
            ModuleCat.extendScalars
              (algebraMap ↥A ↥(X.unop.unop))).mapHomotopyCategoryPlus.obj K) := by
    intro X
    have e := (Functor.mapHomotopyCategoryPlusCompIso
      (Functor.associator (tildeEquiv (R := A)).inverse
          (AdequateFunctor.moduleExtensionFunctor.{u, u} ↥A)
          (PresheafOfModules.evaluation.{u} (AdequateFunctor.algebraRingDiagram.{u} ↥A) X) ≪≫
        Functor.isoWhiskerLeft (tildeEquiv (R := A)).inverse
          (AdequateFunctor.moduleExtensionEvaluationIso.{u, u, u} ↥A X))).app K
    exact ⟨(HomotopyCategory.Plus.subcategoryAcyclic (ModuleCat.{u} ↥(X.unop.unop))).prop_of_iso e,
      (HomotopyCategory.Plus.subcategoryAcyclic (ModuleCat.{u} ↥(X.unop.unop))).prop_of_iso e.symm⟩
  rw [Stacks.Homology.plus_acyclic_presheafOfModules_iff]
  constructor
  · intro h C φ
    let : Algebra ↥A ↥C := φ.hom.toAlgebra
    exact (key (op (op (CommAlgCat.of ↥A ↥C)))).1 (h _)
  · intro h X
    exact (key X).2 (h (CommRingCat.of ↥(X.unop.unop))
      (CommRingCat.ofHom (algebraMap ↥A ↥(X.unop.unop))))

/-- **Universal acyclicity over `Spec A` is acyclicity of the complex of module-valued functors
`C ↦ C ⊗_A Γ(Spec A, K)`**, as an equality of object properties and with no hypothesis. This is
the remaining input of [Stacks, Tag 06ZR] over an affine base, with the chosen big site nowhere in
it: both sides are conditions on a complex of quasi-coherent `𝒪_{Spec A}`-modules, read on the
one side over every scheme over `Spec A` and on the other over every `A`-algebra.

It is `Stacks.Adequate.universallyAcyclic_spec_iff_forall_algebra` against
`Stacks.Adequate.plus_subcategoryAcyclic_moduleExtension_iff_forall_algebra`, the two sides
having been reduced to the same family of conditions over the `A`-algebras. -/
public theorem universallyAcyclic_spec_eq_inverseImage_moduleExtension :
    universallyAcyclic (Spec A) =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctor.{u, u} ↥A)).inverseImage
        ((tildeEquiv (R := A)).inverse ⋙
          AdequateFunctor.moduleExtensionFunctor.{u, u} ↥A).mapHomotopyCategoryPlus := by
  ext K
  exact (universallyAcyclic_spec_iff_forall_algebra K).trans
    (plus_subcategoryAcyclic_moduleExtension_iff_forall_algebra K).symm

end Stacks.Adequate

end

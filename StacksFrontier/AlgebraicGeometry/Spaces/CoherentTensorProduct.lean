module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentTensorProduct

/-!
# Coherence of a tensor product of modules on an algebraic space

The tensor product `M ⊗_{𝒪_F} N` of two coherent `𝒪_F`-modules on an algebraic space `F` is
coherent. This is the tensor-product clause of Stacks 07UE, here without a local Noetherianity
hypothesis on `F`.

## Main definitions

* `PresheafOfModules.uliftSectionsSelfIso`: raising the universe of the sections of a presheaf
  of modules by a universe they already lie in gives an isomorphic presheaf.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_tensorModule`: the tensor product of two modules
  coherent on the small étale ringed site is coherent on that site.
* `AlgebraicGeometry.Space.isCoherent_tensorModule`: the tensor product of two coherent
  `𝒪_F`-modules is coherent.

## References

* [Stacks Project, Tag 07UE](https://stacks.math.columbia.edu/tag/07UE)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace PresheafOfModules

/-- Raising the universe of the sections of a presheaf of modules `P` by a universe they already
lie in gives a presheaf isomorphic to `P`. -/
noncomputable def uliftSectionsSelfIso {C : Type*} [Category C]
    {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (P : PresheafOfModules.{u} R₀) :
    P.uliftSections.{u} ≅ P :=
  isoMk (fun X ↦ (ULift.moduleEquiv (R := R₀.obj X) (M := P.obj X)).toModuleIso)
    (by intro X Y f; exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

end PresheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The tensor product of two modules coherent on the small étale ringed site of an algebraic
space is coherent on that site. -/
theorem isCoherentOnSite_tensorModule (M N : Modules.{u, u} B S hS F hF)
    [SheafOfModules.IsCoherentOnSite M] [SheafOfModules.IsCoherentOnSite N] :
    SheafOfModules.IsCoherentOnSite (tensorModule B S hS F hF M N) := by
  have := (smallEtaleRingedSite B S hS F hF).hasSheafCompose_forget₂_ringCat
  have := SheafOfModules.isLocallyInjective_id_structure
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  have := SheafOfModules.isLocallySurjective_id_structure
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
    (((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj)).mapIso
        (PresheafOfModules.uliftSectionsSelfIso _)).symm)
    (Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherentOnSite
      (smallEtaleRingedSite B S hS F hF) M N)

/-- The tensor product `AlgebraicGeometry.Space.tensorModule` of two coherent `𝒪_F`-modules on an
algebraic space is coherent. -/
@[stacks 07UE "tensor product"]
theorem isCoherent_tensorModule (M N : Modules.{u, u} B S hS F hF)
    [IsCoherent B S hS F hF M] [IsCoherent B S hS F hF N] :
    IsCoherent B S hS F hF (tensorModule B S hS F hF M N) :=
  have : SheafOfModules.IsCoherentOnSite (tensorModule B S hS F hF M N) :=
    isCoherentOnSite_tensorModule B S hS F hF M N
  isCoherent_of_isCoherentOnSite B S hS F hF (tensorModule B S hS F hF M N)

end AlgebraicGeometry.Space

end

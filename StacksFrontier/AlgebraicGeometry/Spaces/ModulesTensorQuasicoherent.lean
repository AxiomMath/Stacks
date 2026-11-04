module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence

/-!
# Quasi-coherence is stable under the tensor product of `𝒪_F`-modules

Let `F` be an algebraic space. The tensor product of two quasi-coherent `𝒪_F`-modules, formed by
`AlgebraicGeometry.Space.modulesMonoidalCategory`, is quasi-coherent (Stacks 03M1(5)).
Consequently, for a morphism `f : X ⟶ Y` of algebraic spaces, a quasi-coherent `𝒪_X`-module `M` and
a quasi-coherent `𝒪_Y`-module `N`, the module `M ⊗ f^*N` is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Space.tensorModuleIso`: the isomorphism between
  `AlgebraicGeometry.Space.tensorModule B S hS F hF M N` and `M ⊗ N`, at a single module universe.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj`: Stacks 03M1(5), for the
  single-universe tensor product of `𝒪_F`-modules: the tensor product of two quasi-coherent
  `𝒪_F`-modules is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj_modulePullback`: the module `M ⊗ f^*N`
  is quasi-coherent, granted `AlgebraicGeometry.Space.HasLocalInverseImagePresentations B S hS f`.
* `Space.isQuasicoherentOnSite_tensorObj_modulePullback_of_isQuasicoherentOnSite`: the module
  `M ⊗ f^*N` is quasi-coherent for an arbitrary morphism `f` of algebraic spaces.

## Implementation notes

`AlgebraicGeometry.Space.modulesMonoidalCategory` is a local instance, activated here with
`attribute [local instance]`.

`Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf` does not apply directly: its module
universe is `max u v w`, where `u, v` are the object and morphism universes of the ambient site,
and on the small étale site of an algebraic space over `Scheme.{u}` these are `u + 1` and `u`,
while the module universe of the structure sheaf is `u`. Quasi-coherence of `M ⊗ N` is instead
transported from `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule` across
`AlgebraicGeometry.Space.tensorModuleIso`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Tensor

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The tensor product `AlgebraicGeometry.Space.tensorModule B S hS F hF M N`, at a single module
universe `u`, is isomorphic to the tensor product `M ⊗ N` of
`AlgebraicGeometry.Space.modulesMonoidalCategory`.

It is the sheafification of `PresheafOfModules.uliftSectionsSelfIso` on the objectwise tensor
product `M.val ⊗ N.val`, followed by the inverse of
`AlgebraicGeometry.Space.modulesTensorObjIso`. -/
noncomputable def tensorModuleIso (M N : Modules.{u, u} B S hS F hF) :
    tensorModule B S hS F hF M N ≅ M ⊗ N :=
  letI := SheafOfModules.isLocallyInjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
  letI := SheafOfModules.isLocallySurjective_id_structure
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
  ((PresheafOfModules.sheafification
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)).obj)).mapIso
        (PresheafOfModules.uliftSectionsSelfIso (PresheafOfModules.tensorObj M.val N.val))) ≪≫
    (modulesTensorObjIso B S hS F hF M N).symm

/-- **Stacks 03M1(5).** The tensor product of two quasi-coherent `𝒪_F`-modules on an algebraic
space `F`, formed by `AlgebraicGeometry.Space.modulesMonoidalCategory`, is quasi-coherent. -/
theorem isQuasicoherentOnSite_tensorObj (M N : Modules.{u, u} B S hS F hF)
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] :
    (M ⊗ N).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (tensorModuleIso B S hS F hF M N)
    (isQuasicoherentOnSite_tensorModule B S hS F hF M N inferInstance inferInstance)

end Tensor

section Pullback

variable {X Y : AlgebraicSpaces B S hS}

/-- The tensor product of a quasi-coherent `𝒪_X`-module `M` against the pullback `f^*N` of a
quasi-coherent `𝒪_Y`-module `N` along a morphism `f : X ⟶ Y` of algebraic spaces is quasi-coherent,
granted `AlgebraicGeometry.Space.HasLocalInverseImagePresentations B S hS f`. -/
theorem isQuasicoherentOnSite_tensorObj_modulePullback (f : X ⟶ Y)
    (hf : HasLocalInverseImagePresentations B S hS f)
    (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS Y.1 Y.2)
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] :
    (M ⊗ (modulePullback B S hS f).obj N).IsQuasicoherentOnSite :=
  let := isQuasicoherentOnSite_modulePullback B S hS f hf N inferInstance
  isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 M ((modulePullback B S hS f).obj N)

/-- The tensor product of a quasi-coherent `𝒪_X`-module `M` against the pullback `f^*N` of a
quasi-coherent `𝒪_Y`-module `N` along an arbitrary morphism `f : X ⟶ Y` of algebraic spaces is
quasi-coherent. -/
theorem isQuasicoherentOnSite_tensorObj_modulePullback_of_isQuasicoherentOnSite (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS Y.1 Y.2)
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] :
    (M ⊗ (modulePullback B S hS f).obj N).IsQuasicoherentOnSite :=
  let := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f N inferInstance
  isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 M ((modulePullback B S hS f).obj N)

end Pullback

end AlgebraicGeometry.Space

end

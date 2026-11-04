module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentationOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# The tensor product `ℰ ⊗ π_*𝒪_Y` is of finite presentation

Let `π : Y ⟶ X` be a finite morphism of algebraic spaces with `X` locally Noetherian, and let `ℰ`
be a finite locally free `𝒪_X`-module.  Then the tensor product `ℰ ⊗ π_*𝒪_Y`, the source of the
multiplication morphism `AlgebraicGeometry.Space.pushforwardUnitTensorMulHom`, is of finite
presentation.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentationOnSite_sheafTensor_chartBaseChangeStructureModule`:
  for `π` finite onto a locally Noetherian `X` and `ℰ` finite locally free, the tensor product
  `ℰ ⊗ π_*𝒪_Y` is of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image `π_*𝒪_Y` along a finite morphism onto a locally Noetherian algebraic space
is of finite presentation. -/
private theorem isFinitePresentationOnSite_chartBaseChangeStructureModule_of_isFinite
    {X Y : AlgebraicSpaces B S hS} (π : Y ⟶ X) (hπ : IsFinite B S hS π.hom)
    (hπr : yoneda.relativelyRepresentable π.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    (chartBaseChangeStructureModule B S hS π hπr).IsFinitePresentationOnSite := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hX⟩
  let M := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  have hO : M.IsFinitePresentationOnSite := SheafOfModules.isFinitePresentationOnSite_unit
  have hqc := isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS π hπ M inferInstance
  have hft := (isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite B S hS π hπ
    M inferInstance).1 (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ inferInstance)
  exact (isCoherent_iff_isFinitePresentationOnSite B S hS X.1 X.2 _).1
    ((isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2 _).2
      ⟨hqc, Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType _ hft⟩)

/-- For a finite morphism `π : Y ⟶ X` of algebraic
spaces onto a locally Noetherian `X` and a finite locally free `𝒪_X`-module `ℰ`, the tensor
product `ℰ ⊗_{𝒪_X} π_*𝒪_Y` — the source of the multiplication morphism
`AlgebraicGeometry.Space.pushforwardUnitTensorMulHom` — is an `𝒪_X`-module of finite
presentation. -/
theorem isFinitePresentationOnSite_sheafTensor_chartBaseChangeStructureModule
    {X Y : AlgebraicSpaces B S hS} (π : Y ⟶ X) (hπ : IsFinite B S hS π.hom)
    (hπr : yoneda.relativelyRepresentable π.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
      E).obj (chartBaseChangeStructureModule B S hS π hπr)).IsFinitePresentationOnSite :=
  Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentationOnSite
    (smallEtaleRingedSite B S hS X.1 X.2) E _
    (SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hE)
    (isFinitePresentationOnSite_chartBaseChangeStructureModule_of_isFinite B S hS π hπ hπr hX)

end AlgebraicGeometry.Space

end

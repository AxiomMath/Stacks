module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.KunnethOverSeparablyClosedField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.SeparablyClosedFieldTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPushforwardDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.Devissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.Main
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedUnitorCoherenceUnitPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula to a separably closed point, on `D(-_étale, Λ)`

Let `k` be a separably closed field, `f : X ⟶ Spec k` a quasi-compact and quasi-separated
morphism with `cd(f) < ∞`, and `Λ` a torsion ring. For `E ∈ D(X_étale, Λ)` and
`K ∈ D((Spec k)_étale, Λ)`, unbounded, the projection formula map of Cohomology on Sites,
Section 21.50 ([Stacks, Tag 0B56]),

`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)`,

is an isomorphism. Through `D((Spec k)_étale, Λ) = D(Λ)`
(`Stacks.EtaleCohomology.EtaleCoefficients.derivedModulesEquivOfSepClosed`) this is
`RΓ(X, E ⊗^L_Λ K̲) = RΓ(X, E) ⊗^L_Λ K`, the statement of [Stacks, Tag 0F12], read on the
derived categories of `Stacks.EtaleCohomology.EtaleCoefficients`, which are the ones of the
proof of [Stacks, Tag 0F1P].

## The proof

The source's proof of [Stacks, Tag 0F12]: the dévissage of More on Algebra, Remark 15.60.11
([Stacks, Tag 09PB]),
`Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_app_of_coproducts_of_unitShifts`, run on
`D((Spec k)_étale, Λ)` through its equivalence with `D(Λ)`.

1. Both sides commute with direct sums: the derived tensor product in each variable, `f⁻¹` as a
   left adjoint, and `Rf_*` by [Stacks, Tag 0F11] (1)
   (`Stacks.EtaleCohomology.EtaleCoefficients.preservesColimitsOfShape_pushforward`), which is
   where `cd(f) < ∞`, the qcqs hypothesis and the torsion of `Λ` enter.
2. Both sides are exact functors of `K`.
3. The map is invertible at every shift of `Λ̲[0]`, the image of `Λ[0]`
   (`derivedModulesEquivOfSepClosedInverseUnitIso`): tensoring with a shift of the structure sheaf
   is an equivalence on both sides, and `f⁻¹` carries it to the same shift of the structure sheaf,
   so the abstract projection formula applies (`isIso_projectionFormulaMap_unitShift`).

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `derivedModulesEquivOfSepClosedInverseUnitIso` — the equivalence `D(Λ) ≌ D((Spec k)_étale, Λ)`
  carries `Λ[0]` to `Λ̲[0]`.
* `isIso_projectionFormulaMap_unitShift` — the projection formula map along any morphism of
  schemes is invertible at every shift of `Λ̲[0]`.
* `isIso_projectionFormulaMap_of_isSepClosed` — the projection formula to a separably closed
  point, under `cd(f) < ∞` and `Λ` torsion.

## References

* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `DerivedModules`, the derived category of the étale site, is read at the standard model, as in
-- `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap`.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The structure sheaf at a separably closed point -/

section Unit

variable (k : Type u) [Field k] [IsSepClosed k]

/-- **The sections at the point of the structure sheaf are `Λ`**, `k` separably closed: the map
`Λ ⟶ Λ̲(Spec k)` of the constant sheaf of rings is bijective at the terminal object. -/
def modulesEquivOfSepClosedUnitLinearEquiv :
    Λ ≃ₗ[Λ] (modulesEquivOfSepClosed k Λ).functor.obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos Λ (Spec (.of k))).O)) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton Λ _ (show (modulesEquivOfSepClosed k Λ).functor.obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos Λ (Spec (.of k))).O)) from (1 : sepClosedPointRing k Λ))) (by
      have h : ⇑(LinearMap.toSpanSingleton Λ ((modulesEquivOfSepClosed k Λ).functor.obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (ringedTopos Λ (Spec (.of k))).O))) (show (modulesEquivOfSepClosed k Λ).functor.obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                (ringedTopos Λ (Spec (.of k))).O)) from (1 : sepClosedPointRing k Λ))) =
          ⇑(sepClosedPointRingMap k Λ) := by
        funext r
        exact mul_one (sepClosedPointRingMap k Λ r)
      rw [h]
      exact bijective_constantRingSheafMap_app k Λ)

/-- **The equivalence `Mod(Λ) ≌ Mod((Spec k)_étale, Λ̲)` carries `Λ` to `Λ̲`.** -/
def modulesEquivOfSepClosedInverseUnitIso :
    (modulesEquivOfSepClosed k Λ).inverse.obj (ModuleCat.of Λ (Shrink.{u + 1} Λ)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos Λ (Spec (.of k))).O) :=
  (modulesEquivOfSepClosed k Λ).inverse.mapIso
      ((Shrink.linearEquiv.{u + 1} Λ Λ).trans
        (modulesEquivOfSepClosedUnitLinearEquiv Λ k)).toModuleIso ≪≫
    ((modulesEquivOfSepClosed k Λ).unitIso.app _).symm

/-- **The equivalence `D(Λ) ≌ D((Spec k)_étale, Λ)` carries `Λ[0]` to `Λ̲[0]`**, `k` separably
closed. -/
def derivedModulesEquivOfSepClosedInverseUnitIso [HasDerivedCategory (ModuleCat.{u + 1} Λ)] :
    (derivedModulesEquivOfSepClosed k Λ).inverse.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
          (ModuleCat.of Λ (Shrink.{u + 1} Λ))) ≅
      (@DerivedCategory.singleFunctor (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O)) _ _ (_) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (ringedTopos Λ (Spec (.of k))).O)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O))
  ((modulesEquivOfSepClosed k Λ).inverse.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (modulesEquivOfSepClosedInverseUnitIso Λ k)

end Unit

/-! ### The projection formula at the shifts of the structure sheaf -/

section UnitShift

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `f⁻¹(Λ̲[0]⟦m⟧) ≅ Λ̲[0]⟦m⟧`: `f⁻¹` commutes with the shift and carries the structure sheaf to
the structure sheaf. -/
def pullbackUnitShiftIso (m : ℤ) :
    (pullback Λ f).obj ((Stacks.DerivedTensor.RingedSite.unitObject
        ⟨(ringedTopos Λ Y).C, (ringedTopos Λ Y).J, (ringedTopos Λ Y).O⟩)⟦m⟧) ≅
      (Stacks.DerivedTensor.RingedSite.unitObject
        ⟨(ringedTopos Λ X).C, (ringedTopos Λ X).J, (ringedTopos Λ X).O⟩)⟦m⟧ :=
  ((pullback Λ f).commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (Stacks.Sheaves.DerivedPullback.derivedPullbackUnitIso
      (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ f))

/-- **The projection formula map is invertible at every shift of the structure sheaf**, along
any morphism of schemes and for every `E ∈ D(X_étale, Λ)`: tensoring with `Λ̲[0]⟦m⟧` is an
equivalence on both sides, so the abstract projection formula applies. -/
theorem isIso_projectionFormulaMap_unitShift (E : DerivedModules Λ X) (m : ℤ) :
    IsIso (projectionFormulaMap Λ f E ((Stacks.DerivedTensor.RingedSite.unitObject
        ⟨(ringedTopos Λ Y).C, (ringedTopos Λ Y).J, (ringedTopos Λ Y).O⟩)⟦m⟧)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Y).O))
  have hY := Stacks.Cohomology.ProjectionFormulaOfToposHom.isEquivalence_tensorRight_unitShift
    (ringedTopos Λ Y) m
  have hX := Functor.isEquivalence_tensorRightOf_of_iso
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (ringedTopos Λ X).O)
    (pullbackUnitShiftIso Λ f m)
    (Stacks.Cohomology.ProjectionFormulaOfToposHom.isEquivalence_tensorRight_unitShift
      (ringedTopos Λ X) m)
  exact Stacks.ProjectionFormula.isIso_adjunctionTensorMap (adjunction Λ f)
    (Functor.uncurry.obj (tensor Λ Y)) (Functor.uncurry.obj (tensor Λ X))
    (pullbackTensorIso Λ f).hom E _ (fun _ => inferInstance)

end UnitShift

/-! ### The projection formula to a separably closed point -/

section SepClosed

variable (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}

/-- The projection formula map, for fixed `E`, as a natural transformation of functors of
`K ∈ D((Spec k)_étale, Λ)`. -/
def projectionFormulaNatTrans {S : Scheme.{u}} (f : X ⟶ S) (E : DerivedModules Λ X) :
    (tensor Λ S).obj ((pushforward Λ f).obj E) ⟶
      pullback Λ f ⋙ (tensor Λ X).obj E ⋙ pushforward Λ f where
  app := projectionFormulaMap Λ f E
  naturality _ _ φ :=
    Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap_naturality_target
      (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ f) E φ

/-- **The projection formula to a separably closed point**, on `D(-_étale, Λ)`. Let `k` be a
separably closed field, `f : X ⟶ Spec k` a quasi-compact and quasi-separated morphism with
`cd(f) < ∞`, and `Λ` a torsion ring. For every `E ∈ D(X_étale, Λ)` and every
`K ∈ D((Spec k)_étale, Λ) = D(Λ)`, unbounded, the projection formula map
`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` is an isomorphism. This is
`RΓ(X, E ⊗^L_Λ K̲) = RΓ(X, E) ⊗^L_Λ K` of [Stacks, Tag 0F12], with `RΓ` read in
`D((Spec k)_étale, Λ)`. -/
@[sga "4 XVIII 2.13" "special case"]
theorem isIso_projectionFormulaMap_of_isSepClosed (f : X ⟶ Spec (.of k)) [QuasiCompact f]
    [QuasiSeparated f] (hcd : f.etaleCohomologicalDimension < ⊤) (hΛ : AddMonoid.IsTorsion Λ)
    (E : DerivedModules Λ X) (K : DerivedModules Λ (Spec (.of k))) :
    IsIso (projectionFormulaMap Λ f E K) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ (Spec (.of k))).O))
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Λ)
  let := Stacks.EtaleCohomology.ProjectionFormulaConstant.etaleTensorCommShift Λ X E
  have := Stacks.EtaleCohomology.ProjectionFormulaConstant.etaleTensor_isTriangulated Λ X E
  let := Stacks.EtaleCohomology.ProjectionFormulaConstant.etaleTensorCommShift Λ (Spec (.of k))
    ((pushforward Λ f).obj E)
  have := Stacks.EtaleCohomology.ProjectionFormulaConstant.etaleTensor_isTriangulated Λ
    (Spec (.of k)) ((pushforward Λ f).obj E)
  have hF : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((tensor Λ (Spec (.of k))).obj ((pushforward Λ f).obj E)) := fun I =>
    preservesColimitsOfShape_tensor_obj Λ _ I _
  have hG : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (pullback Λ f ⋙ (tensor Λ X).obj E ⋙ pushforward Λ f) := fun I => by
    have := preservesColimitsOfShape_tensor_obj Λ X I E
    have := preservesColimitsOfShape_pushforward Λ f hcd hΛ I
    infer_instance
  let Ψ := (modulesEquivOfSepClosed k Λ).inverse.mapDerivedCategory
  have : Ψ.EssSurj := inferInstanceAs (derivedModulesEquivOfSepClosed k Λ).inverse.EssSurj
  have hΨ : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) Ψ := fun I =>
    inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      (derivedModulesEquivOfSepClosed k Λ).inverse)
  exact Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_app_of_coproducts_of_unitShifts
    (R := Λ) _ _ (projectionFormulaNatTrans Λ f E) Ψ
    (fun n => ((projectionFormulaNatTrans Λ f E).isIso_app_iff_of_iso
      ((shiftFunctor _ n).mapIso (derivedModulesEquivOfSepClosedInverseUnitIso Λ k))).2
        (isIso_projectionFormulaMap_unitShift Λ f E n)) K

end SepClosed

end Stacks.EtaleCohomology.EtaleCoefficients

end

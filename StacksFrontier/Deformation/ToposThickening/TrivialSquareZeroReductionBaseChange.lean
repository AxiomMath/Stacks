module

public import StacksFrontier.Deformation.ToposThickening.DerivedReductionBaseChangeConnecting
public import StacksFrontier.Deformation.ToposThickening.TrivialSquareZeroReduction

/-!
# Base change of the reduction triangles of trivial square-zero extensions

Let `O₀` be a sheaf of commutative rings on a site and `φ : M ⟶ N` a morphism of sheaves of
`O₀`-modules. The induced morphism `O₀[M] ⟶ O₀[N]` of trivial square-zero extensions lies over
`O₀` and carries the ideal `M` to the ideal `N` through `φ`, and derived extension of scalars
along it is a base change between the reduction triangles
`Deformation.ComplexLift.sqZeroExtReduction M` and `Deformation.ComplexLift.sqZeroExtReduction N`,
with the map of ideal parts `- ⊗^L M ⟶ - ⊗^L N` induced by `φ`.

## Main definitions

* `Deformation.ComplexLift.sqZeroExtReductionBaseChange`: the base change between the reduction
  triangles of `O₀[M]` and `O₀[N]`.

## Main results

* `Deformation.ComplexLift.sqZeroExtIdealInclusion_comp_unitToRestrictScalarsUnit`: the map
  `O₀[M] ⟶ O₀[N]` carries the inclusion of the ideal `M` to that of `N` precomposed with `φ`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d d' d₀ u

namespace Deformation.ComplexLift

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ : Sheaf J CommRingCat.{u}}
  {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (φ : M ⟶ N)

/-- The map `O₀[M] ⟶ O₀[N]` carries the inclusion of the ideal `M` to the inclusion of the ideal
`N` precomposed with `φ`. -/
theorem sqZeroExtIdealInclusion_comp_unitToRestrictScalarsUnit :
    sqZeroExtIdealInclusion M ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
        (ringSheafMapOf J (sqZeroExtSheafAnySiteMap φ)) =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J (sqZeroExtSheafAnySiteProj M))).map φ ≫
        (restrictScalarsCompIsoOf (sqZeroExtSheafAnySiteMap φ)
          (sqZeroExtSheafAnySiteMap_comp_proj φ)).inv.app N ≫
        (SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J (sqZeroExtSheafAnySiteMap φ))).map (sqZeroExtIdealInclusion N) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  refine (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app _ U _).trans
    ((sqZeroExtSheafAnySiteMap_idealInclusion M φ U m).trans ?_)
  exact congrArg (fun y ↦ (sqZeroExtIdealInclusion N).val.app U y)
    (restrictScalarsCompIsoOf_inv_app_val_app (sqZeroExtSheafAnySiteMap φ)
      (sqZeroExtSheafAnySiteMap_comp_proj φ) N U _).symm

variable [HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ M)))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite O₀ N)))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **The base change between the reduction triangles of `O₀[M]` and `O₀[N]`** along the map
`O₀[M] ⟶ O₀[N]` induced by `φ : M ⟶ N`: derived extension of scalars, with the map of ideal
parts `- ⊗^L M ⟶ - ⊗^L N` induced by `φ`. -/
def sqZeroExtReductionBaseChange :
    DerivedReductionBaseChange (sqZeroExtReduction.{d, d₀} M) (sqZeroExtReduction.{d', d₀} N) :=
  flatReductionBaseChange.{d, d', d₀} (sqZeroExtSheafAnySiteMap φ)
    (sqZeroExtSheafAnySiteMap_comp_proj φ) φ (sqZeroExtIdealInclusion M)
    (sqZeroExtIdealInclusion_comp M) (shortExact_sqZeroExtIdealSequence M)
    (sqZeroExtIdealInclusion N) (sqZeroExtIdealInclusion_comp N)
    (shortExact_sqZeroExtIdealSequence N)
    (sqZeroExtIdealInclusion_comp_unitToRestrictScalarsUnit φ)

/-- The functor of `sqZeroExtReductionBaseChange φ` is derived extension of scalars along
`O₀[M] ⟶ O₀[N]`. -/
theorem sqZeroExtReductionBaseChange_functor :
    (sqZeroExtReductionBaseChange.{d, d', d₀} φ).functor =
      derivedExtensionOfScalars.{d, d'} (sqZeroExtSheafAnySiteMap φ) := rfl

/-- The map of ideal parts of `sqZeroExtReductionBaseChange φ` is the map `- ⊗^L M ⟶ - ⊗^L N`
induced by `φ`. -/
theorem sqZeroExtReductionBaseChange_idealMap :
    (sqZeroExtReductionBaseChange.{d, d', d₀} φ).idealMap = derivedTensorRightMap.{d₀} φ := rfl

end Deformation.ComplexLift

end

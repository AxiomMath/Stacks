module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyDerived
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTopDegree

/-!
# Part (3) of Stacks 0E1J from cohomology and base change for `Rf_*𝒪_X`

Let `f : X → S` be a family of curves (Stacks 0D4Z) and let `a : X' → X` be a morphism of
families over `h : S' → S`, that is a cartesian square. The source proves part (3) of
Stacks 0E1J, `h^*(R¹f_*𝒪_X) = R¹f'_*𝒪_{X'}`, by reading on `H¹` the base change isomorphism
`Lh^*Rf_*𝒪_X ≅ Rf'_*𝒪_{X'}` of Stacks 0CTM, part (1). Reading it on `H¹` uses that `Rf_*𝒪_X`
has no cohomology above degree `1`, which in the source follows from the local description
`Rf_*𝒪_X = 𝒪_S ⊕ H¹(P)[-1]` (and which is also the vanishing of `R^if_*𝒪_X`, `i ≥ 2`, for a
family whose fibres have dimension at most one): then
`H¹(Lh^*Rf_*𝒪_X) = h^*H¹(Rf_*𝒪_X)` because `Lh^*` is right t-exact
(`AlgebraicGeometry.Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE`).

This file states the two inputs as properties of a family and carries out the deduction.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasDerivedStructureSheafBaseChange`: the base change clause of
  Stacks 0CTM, part (1), at `E = 𝒪_X[0]` and at the cartesian squares of morphisms of families —
  the canonical map `Lh^*Rf_*𝒪_X ⟶ Rf'_*L(h')^*𝒪_X`
  (`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`) is an isomorphism.
* `AlgebraicGeometry.CurveFamily.HasDerivedStructureSheafPushforwardIsLEOne`: `Rf_*𝒪_X` has no
  cohomology above degree `1`.

## Main results

* `AlgebraicGeometry.CurveFamily.firstHigherDirectImageCommutesWithBaseChange_of_derived`:
  part (3) of Stacks 0E1J for a family with both properties.
* `AlgebraicGeometry.CurveFamily.firstHigherDirectImageCommutesWithBaseChange_of_forall_derived`:
  the hypothesis `h3` of the consumers of Stacks 0E1J
  (`AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_h2_h3`), from the two
  properties for every family in `Curves^{h0,1}`.

## Implementation notes

No declaration here carries a `stacks` attribute. The two properties are inputs: the first is an
instance of Stacks 0CTM, part (1) (`f` is proper, flat and of finite presentation, and `𝒪_X[0]`
is perfect), stated with exactly the base change map of the statement of Stacks 0CTM; the second
is the top-degree vanishing for a family of curves. Neither is proved in this development.

The derived categories are those of the standard model, fixed inside the statements by `letI`,
which is the model in which `AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap` and
`AlgebraicGeometry.Space.smallEtaleDerivedModulePushforward` are elaborated.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **The base change clause of Stacks 0CTM, part (1), at `𝒪_X` for a family of curves.** For
every morphism of families `a : F ⟶ X` over `h : S' ⟶ S`, the canonical base change map
`Lh^*Rf_*(𝒪_X[0]) ⟶ Rf'_*L(h')^*(𝒪_X[0])` of the cartesian square is an isomorphism. -/
def HasDerivedStructureSheafBaseChange (X : CurveFamily B hZ) : Prop :=
  ∀ (F : CurveFamily B hZ) (a : F ⟶ X),
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ X.total))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ F.total))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
        (schemeSpace X.base)))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
        (schemeSpace F.base)))
    IsIso (Space.smallEtaleDerivedModuleBaseChangeMap B integerBase hZ X.toBase
      (schemeSpaceMap a.baseMap) F.toBase a.totalMap a.cartesian.w
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ X.total)) 0).obj
        (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B integerBase hZ X.total))))

/-- **`Rf_*𝒪_X` has no cohomology above degree `1`**, for a family of curves `f : X → S`: the
higher direct images `R^if_*𝒪_X` vanish for `i ≥ 2`. -/
def HasDerivedStructureSheafPushforwardIsLEOne (X : CurveFamily B hZ) : Prop :=
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ X.total))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (schemeSpace X.base)))
  ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ X.total)) 0).obj
      (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B integerBase hZ X.total)))).IsLE 1

/-- **Part (3) of Stacks 0E1J from cohomology and base change for `Rf_*𝒪_X`.** If the base change
map `Lh^*Rf_*𝒪_X ⟶ Rf'_*𝒪_{X'}` is an isomorphism for every morphism of families into `X`, and
`Rf_*𝒪_X` has no cohomology above degree `1`, then `h^*(R¹f_*𝒪_X) ≅ R¹f'_*𝒪_{X'}` for every
morphism of families over `h : S' → S`.

The isomorphism is `h^*R¹f_*𝒪_X ≅ h^*H¹(Rf_*𝒪_X) ≅ H¹(Lh^*Rf_*𝒪_X)` (right t-exactness of
`Lh^*`), then `H¹` of the base change isomorphism, then
`H¹(Rf'_*L(h')^*𝒪_X) ≅ H¹(Rf'_*𝒪_{X'}) ≅ R¹f'_*𝒪_{X'}`. -/
theorem firstHigherDirectImageCommutesWithBaseChange_of_derived {X : CurveFamily B hZ}
    (hA : X.HasDerivedStructureSheafBaseChange)
    (hB : X.HasDerivedStructureSheafPushforwardIsLEOne) :
    X.FirstHigherDirectImageCommutesWithBaseChange := by
  intro F a
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ X.total))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ F.total))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (schemeSpace X.base)))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (schemeSpace F.base)))
  have := hA F a
  obtain ⟨e⟩ := Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE
    (schemeSpaceMap a.baseMap) _ 1 hB
  exact ⟨(Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).mapIso
      X.homologyDerivedPushforwardIsoFirstHigherDirectImage.symm ≪≫ e.symm ≪≫
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
        (schemeSpace F.base))) 1).mapIso
      (asIso (Space.smallEtaleDerivedModuleBaseChangeMap B integerBase hZ X.toBase
        (schemeSpaceMap a.baseMap) F.toBase a.totalMap a.cartesian.w
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ X.total))
            0).obj
          (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B integerBase hZ X.total)))) ≪≫
        (Space.smallEtaleDerivedModulePushforward B integerBase hZ F.toBase).mapIso
          (Space.smallEtaleDerivedModulePullbackUnitIso a.totalMap)) ≪≫
    F.homologyDerivedPushforwardIsoFirstHigherDirectImage⟩

/-- **The input `h3` of the consumers of Stacks 0E1J, from cohomology and base change for
`Rf_*𝒪_X`.** If every family in `Curves^{h0,1}` has the base change clause of Stacks 0CTM,
part (1), at `𝒪_X`, and `Rf_*𝒪_X` has no cohomology above degree `1`, then part (3) of
Stacks 0E1J holds for every such family. -/
theorem firstHigherDirectImageCommutesWithBaseChange_of_forall_derived
    (hA : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasDerivedStructureSheafBaseChange)
    (hB : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasDerivedStructureSheafPushforwardIsLEOne) :
    ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange :=
  fun X hX => firstHigherDirectImageCommutesWithBaseChange_of_derived (hA X hX) (hB X hX)

end CurveFamily

end AlgebraicGeometry

end

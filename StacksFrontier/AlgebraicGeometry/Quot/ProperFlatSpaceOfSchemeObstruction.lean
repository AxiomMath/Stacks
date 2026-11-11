module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatUnobstructedVersalDeformation
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceOfSchemeCotangent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceOfSchemeDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleExt
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentExtUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent

/-!
# The obstruction space of a smooth proper scheme over a field

Let `f : X ⟶ Spec k` be a smooth proper morphism and `x₀` the object of
`Spaces'_{fp, flat, proper}` over `Spec k` it defines
(`AlgebraicGeometry.ProperFlatSpaceOfScheme.point`). The obstruction space of the deformation
theory of `x₀` (Remark 0D1P) is `T²(k) = Ext²_{𝒪_X}(L_{X/k}, 𝒪_X ⊗_k k)`, formed with the full
cotangent complex on the `Type u` model of the small étale site of `X`
(`AlgebraicGeometry.Space.cotangentExtTwo`). This file shows that it vanishes as soon as the
Zariski group `Ext²_{𝒪_X}(Ω_{X/k}, 𝒪_X)` does.

The comparison is the chain

`T²(k) = Ext²(L_{X/k}, 𝒪_X) = Ext²(Ω_{X/k}^a[0], 𝒪_X^a) = Ext²_{𝒪_X}(Ω_{X/k}, 𝒪_X)`:

* `X` being smooth over `k`, `L_{X/k}` on the model has cohomology in degree `0` only (Stacks 08R5
  on the affine étale charts), so it is its `H⁰` placed in degree `0`;
* `H⁰(L_{X/k})` is the sheaf of differentials, which is the étale module associated with the
  Zariski `Ω_{X/k}` (Stacks 04CS), and `𝒪_X ⊗_k k = 𝒪_X` is the module associated with `𝒪_X`;
* the associated-module functor is bijective on `Ext` groups into a quasi-coherent module
  (`AlgebraicGeometry.Space.bijective_mapExtAddHom_representedAssociatedModule`), and so is the
  passage to the model of the small étale site.

## Main results

* `AlgebraicGeometry.Space.subsingleton_cotangentExtFunctor_obj_of_iso`: `T^i(M)` vanishes when
  `L_{X/Y}` is a module `A` in degree `0`, `𝒪_X ⊗_R M ≅ C` and `Ext^i(A, C) = 0`.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.subsingleton_cotangentExtTwo_point`:
  `T²_{X/k}(k) = 0` when `Ext²_{𝒪_X}(Ω_{X/k}, 𝒪_X) = 0`.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08R5](https://stacks.math.columbia.edu/tag/08R5)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

attribute [-instance] AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)
  [HasDerivedCategory (modelModules X)]

/-- **`T^i(M)` vanishes when `Ext^i(A, C)` does**, for `L_{X/Y} ≅ A[0]` on the model and
`𝒪_X ⊗_R M ≅ C`: `T^i(M)` is the group of morphisms `L_{X/Y} ⟶ (𝒪_X ⊗_R M)[0]⟦i⟧` of the derived
category, which the two isomorphisms identify with `Ext^i(A, C)`. -/
theorem subsingleton_cotangentExtFunctor_obj_of_iso (i : ℕ) (M : ModuleCat.{u} R)
    (A C : modelModules X)
    (eL : (modelRingedToposHom f).cotangentComplexDerived ≅
      (DerivedCategory.singleFunctor _ 0).obj A)
    (eM : (modelTensorFunctor φ).obj M ≅ C)
    (h : Subsingleton (Ext.{u} A C i)) :
    Subsingleton ((cotangentExtFunctor f φ i).obj M) := by
  refine (cotangentExtFunctorObjEquiv f φ i M).toEquiv.subsingleton_congr.2 ?_
  refine (Iso.homCongr eL ((shiftFunctor _ (i : ℤ)).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso eM))).subsingleton_congr.2 ?_
  exact (Ext.homEquiv (X := A) (Y := C) (n := i)).symm.subsingleton

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.ProperFlatSpaceOfScheme

open ProperFlatSpaceDeformation

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}}

/-- **The obstruction space of a smooth proper scheme over a field vanishes when
`Ext²_{𝒪_X}(Ω_{X/k}, 𝒪_X)` does.** For `f : X ⟶ Spec k` smooth and proper, the group
`T²_{X/k}(k) = Ext²(L_{X/k}, 𝒪_X ⊗_k k)` of Remark 0D1P at the point `x₀` of
`Spaces'_{fp, flat, proper}` given by `X`, formed with the cotangent complex on the model of the
small étale site, is zero as soon as the Ext group of the Zariski sheaf of relative
differentials into the structure sheaf is. -/
theorem subsingleton_cotangentExtTwo_point (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [HasDerivedCategory (Space.modelModules (point B k hk f).obj.obj.left)]
    (h : Subsingleton (Abelian.Ext (Scheme.Hom.relativeDifferentials f)
      (SheafOfModules.unit X.ringCatSheaf) 2)) :
    Subsingleton ((Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap (point B k hk f)
        (obj_eq_specialFibre (point B k hk f) (projection_point B k hk f)))
      (Space.ProperFlatLift.chartBaseRingHom (point B k hk f)
        (obj_eq_specialFibre (point B k hk f) (projection_point B k hk f)))).obj
          (ModuleCat.of k k)) := by
  let x₀ := point B k hk f
  let hx := obj_eq_specialFibre x₀ (projection_point B k hk f)
  let U := siteObj B k hk f
  let hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk U
  let L := Space.representedAssociatedModule B (Spec (.of k)) hk U hU
  let E := (Space.modelModulesEquiv B (Spec (.of k)) hk x₀.obj.obj.left).functor
  let Ω := Scheme.Hom.relativeDifferentials f
  let O := SheafOfModules.unit X.ringCatSheaf
  have h₂ : Subsingleton (Ext.{u} (E.obj (L.obj Ω)) (E.obj (L.obj O)) 2) :=
    Space.subsingleton_ext_modelModulesEquiv_representedAssociatedModule B (Spec (.of k)) hk U
      Ω O inferInstance 2 h
  refine Space.subsingleton_cotangentExtFunctor_obj_of_iso _ _ 2 _
    (E.obj (L.obj Ω)) (E.obj (L.obj O))
    (cotangentComplexDerivedIsoChartStructureMapPoint B k hk f ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (cotangentHomologyZeroChartStructureMapPointIso B k hk f))
    (Stacks.Cohomology.SiteModules.baseRingTensorSelfIso.{u, u}
        (Space.ProperFlatLift.chartBaseRingHom x₀ hx) ≪≫
      (Space.modelModulesEquivUnitIso B (Spec (.of k)) hk x₀.obj.obj.left).symm ≪≫
      E.mapIso (Space.representedAssociatedModuleObjUnitIso B (Spec (.of k)) hk U hU).symm) h₂

end AlgebraicGeometry.ProperFlatSpaceOfScheme

end

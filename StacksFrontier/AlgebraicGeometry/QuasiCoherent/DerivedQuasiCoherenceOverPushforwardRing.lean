module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DerivedPushforwardOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RestrictScalarsHomology
import StacksCore.Tactic.StacksAttribute

/-!
# `D⁺_QCoh` over `f_* 𝒪_Y` is detected by restriction of scalars

Let `f : Y ⟶ X` be an affine morphism of schemes.  Restriction of scalars along
`𝒪_X ⟶ f_* 𝒪_Y` is exact and faithful, so the functor it induces on the unbounded derived
categories commutes with cohomology and reflects vanishing.  Since an `f_* 𝒪_Y`-module is
quasi-coherent over `f_* 𝒪_Y` exactly when it is quasi-coherent over `𝒪_X`, an object of
`D(f_* 𝒪_Y)` lies in `D⁺_QCoh(f_* 𝒪_Y)` as soon as its scalar restriction lies in
`D⁺_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.isBoundedBelow_of_isBoundedBelow_scalarRestriction`: cohomological
  boundedness below descends from the scalar restriction, for an arbitrary morphism.
* `AlgebraicGeometry.derivedCategoryB_of_derivedCategoryB_scalarRestriction`: quasi-coherence of
  the cohomology sheaves descends from the scalar restriction, for an affine morphism.
* `AlgebraicGeometry.derivedCategoryBPlus_of_derivedCategoryBPlus_scalarRestriction`: both at
  once — an object of `D(f_* 𝒪_Y)` whose scalar restriction lies in `D⁺_QCoh(𝒪_X)` lies in
  `D⁺_QCoh(f_* 𝒪_Y)`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 0AX2](https://stacks.math.columbia.edu/tag/0AX2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.DerivedAffinePushforward

universe w u

namespace AlgebraicGeometry

variable {Y X : Scheme.{u}} (f : Y ⟶ X)
  [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf))]

/-- Cohomological boundedness below descends through restriction of scalars: if the scalar
restriction to `𝒪_X` of an object of `D(f_* 𝒪_Y)` is bounded below, then so is the object.
No hypothesis on `f` is needed. -/
theorem isBoundedBelow_of_isBoundedBelow_scalarRestriction
    (G : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf)))
    (hG : DerivedCategoryB.IsBoundedBelow ((scalarRestriction f).mapDerivedCategory.obj G)) :
    DerivedCategoryB.IsBoundedBelow G := by
  obtain ⟨n₀, hn₀⟩ := hG
  refine ⟨n₀, fun n hn ↦ ?_⟩
  refine Stacks.SheafOfModules.ChangeOfRings.isZero_of_isZero_restrictScalars
    f.toRingCatSheafHom ?_
  exact (hn₀ n hn).of_iso (((scalarRestriction f).mapDerivedCategoryHomologyIso n).app G).symm

/-- Quasi-coherence of the cohomology sheaves descends through restriction of scalars, for an
affine morphism `f`: if the cohomology sheaves of the scalar restriction to `𝒪_X` of an object
`G` of `D(f_* 𝒪_Y)` are quasi-coherent over `𝒪_X`, then the cohomology sheaves of `G` are
quasi-coherent over `f_* 𝒪_Y`. -/
theorem derivedCategoryB_of_derivedCategoryB_scalarRestriction [IsAffineHom f]
    (G : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf)))
    (hG : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((scalarRestriction f).mapDerivedCategory.obj G)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf)) G := fun n ↦
  (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff f _).1
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((scalarRestriction f).mapDerivedCategoryHomologyIso n).app G) (hG n))

/-- `D⁺_QCoh(f_* 𝒪_Y)` is detected by restriction of scalars: for an affine morphism
`f : Y ⟶ X`, an object of `D(f_* 𝒪_Y)` whose scalar restriction to `𝒪_X` is bounded below with
quasi-coherent cohomology sheaves is itself bounded below with cohomology sheaves that are
quasi-coherent over `f_* 𝒪_Y`. -/
theorem derivedCategoryBPlus_of_derivedCategoryBPlus_scalarRestriction [IsAffineHom f]
    (G : DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base Y.ringCatSheaf)))
    (hG : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((scalarRestriction f).mapDerivedCategory.obj G)) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (pushforwardRing f.base Y.ringCatSheaf)) G :=
  ⟨isBoundedBelow_of_isBoundedBelow_scalarRestriction f G hG.1,
    derivedCategoryB_of_derivedCategoryB_scalarRestriction f G hG.2⟩

end AlgebraicGeometry

end

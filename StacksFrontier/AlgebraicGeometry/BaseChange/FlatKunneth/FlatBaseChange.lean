module

public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesBaseChange

/-!
# Base change for the direct image of a quasi-coherent module flat over the base

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, and let `ℱ` be a
quasi-coherent `𝒪_X`-module flat over `S`.  Then the composition

`Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ ⟶ Rf'_*(g')^*ℱ`

of the derived base-change map of [Stacks, Tag 08HY] with the derived-to-ordinary comparison is an
isomorphism.  This is [Stacks, Tag 0A1D] at `E = 𝒪_X`, with the tensor factor cancelled.

`VanishingHigherDirectImages.isIso_derivedBaseChangeComp_single_of_isFlatOver`
proves the same for `ℱ` of finite presentation; finite presentation enters that proof only to
make the terms of `ℱ[0]` quasi-coherent, so the argument goes through verbatim for a
quasi-coherent `ℱ`, which is what the Künneth formula of [Stacks, Tag 0FU4] needs.

## Main results

* `AlgebraicGeometry.FlatKunneth.isIso_derivedBaseChangeComp_single_of_isQuasicoherent`: the
  display above.

## References

* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans)

universe u

namespace AlgebraicGeometry.FlatKunneth

attribute [local instance 10000] HasDerivedCategory.standard

/-- The terms of a quasi-coherent module placed in degree zero are quasi-coherent. -/
theorem isQuasicoherent_singleDegreeComplex_X {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (i : ℤ) :
    ((ProperFlatBaseChange.singleDegreeComplex M).X i).IsQuasicoherent := by
  by_cases hi : i = 0
  · subst hi
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).symm inferInstance
  · have := isFinitePresentation_of_isZero _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
    exact isQuasicoherent_of_isFinitePresentation _

/-- **Flat base change for a quasi-coherent module.**  For a cartesian square of schemes with `f`
quasi-compact and quasi-separated and a quasi-coherent `𝒪_X`-module `ℱ` flat over `S`, the
composition

`Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ ⟶ Rf'_*(g')^*ℱ`

of the derived base-change map of [Stacks, Tag 08HY] with the derived-to-ordinary comparison is
an isomorphism.  The proof is that of
`VanishingHigherDirectImages.isIso_derivedBaseChangeComp_single_of_isFlatOver`:
the chart form of [Stacks, Tag 0A1D] at `P = 𝒪_X[0]`, whose chart hypothesis is the K-flatness of
the sections of `ℱ` over affine charts, and `Tot(𝒪_X[0] ⊗ ℱ[0]) ≅ ℱ[0]`. -/
theorem isIso_derivedBaseChangeComp_single_of_isQuasicoherent {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w)
        (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F)) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app
          (ProperFlatBaseChange.singleDegreeComplex F))) := by
  have hGqcoh : ∀ n : ℤ,
      ((ProperFlatBaseChange.singleDegreeComplex F).X n).IsQuasicoherent := fun n =>
    isQuasicoherent_singleDegreeComplex_X F n
  have hchart := isIso_derivedBaseChangeComp_totalTensor_of_charts hsq
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)))
    (ProperFlatBaseChange.singleDegreeComplex F)
    (Stacks.SheafOfModules.isKFlat_single_unit X.toRingedSpace.sheaf)
    (fun n => Stacks.Blowup.isQuasicoherent_homology_Q_single X _
      (isQuasicoherent_of_isFinitePresentation
        (_root_.SheafOfModules.unit X.ringCatSheaf)) n)
    hGqcoh
    (fun U V hU hV hUV => kFlat_sectionsComplex_pullback_fromSpec f hU hV hUV
      (ProperFlatBaseChange.singleDegreeComplex F)
      ((CochainComplex.minus_iff _).2 ⟨0, inferInstance⟩) hGqcoh
      (ProperFlatBaseChange.isFlatOver_singleDegreeComplex f F hflat))
  refine (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff_of_iso
    g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) ?_).1 hchart
  exact Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.toRingedSpace.sheaf _ _ ≪≫
    Stacks.SheafOfModules.tensorComplexUnitIso X.toRingedSpace.sheaf _

end AlgebraicGeometry.FlatKunneth

end

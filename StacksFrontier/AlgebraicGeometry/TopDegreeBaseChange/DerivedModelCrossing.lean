module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor

/-!
# The top-degree pullback comparison for base change

In a top-degree base-change situation ([Stacks, Tag 0EX3]), the unbounded derived pushforward
`Rf'_*(F'[0])` has no cohomology above `d`, and consequently
`h^* R^d f'_* F' ≅ H^d(Lh^* Rf'_* F')`.

## Main results

* `isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus`: for an additive `F : A ⥤ B` between
  abelian categories with `A` having enough injectives, and any functor `R` on the unbounded
  derived categories carrying a comparison from `F` that is invertible at the K-injective
  complexes, the degree-`i` cohomology of `R(M[0])` vanishes as soon as `R^i F(M)` does.
* `isLE_derivedPushforward_singleFunctor`: for a morphism of ringed spaces, `Rf_*(M[0])` has no
  cohomology above `d` as soon as `R^i f_* M = 0` for `i > d`.
* `isLE_derivedPushforward_baseChange`: in a top-degree base-change situation, `Rf'_*(F'[0])` has
  no cohomology above `d`.
* `topDirectImagePullbackIso`: the comparison `h^* R^d f'_* F' ≅ H^d(Lh^* Rf'_* F')`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
-/

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard

section Generic

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

/-- **The two models of a right derived functor agree on the vanishing of the cohomology of a
single object.** Let `F : A ⥤ B` be additive with `A` having enough injectives, and let `R` be any
functor of the unbounded derived categories receiving a comparison `β` from degreewise `F` which
is invertible at every K-injective complex. If the `i`-th right derived functor of `F` in the
bounded below sense kills `M`, then the degree-`i` cohomology of `R(M[0])` vanishes. -/
theorem isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus (F : A ⥤ B) [F.Additive]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hβ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (M : A) (i : ℤ) (h : IsZero ((F.rightDerivedPlus i).obj M)) :
    IsZero ((homologyFunctor B i).obj (R.obj ((singleFunctor A 0).obj M))) := by
  have hE : ((DerivedCategory.Plus.singleFunctor A 0).obj M).obj.IsGE 0 := by
    change ((singleFunctor A 0).obj M).IsGE 0
    infer_instance
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus F R β hβ
    ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0 hE
  exact IsZero.of_iso h ((homologyFunctor B i).mapIso e)

end Generic

/-- **`Rf_*(M[0])` has no cohomology above `d` as soon as the higher direct images of `M` vanish
above `d`.** Here `f : X ⟶ Y` is a morphism of ringed spaces and `Rf_*` is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f`. -/
theorem isLE_derivedPushforward_singleFunctor {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing X)) (d : ℤ)
    (hvan : ∀ i : ℤ, d < i → IsZero (((modulePushforward f).rightDerivedPlus i).obj M)) :
    TStructure.t.IsLE ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj
      ((singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) d := by
  refine (DerivedCategory.isLE_iff _ _).2 ?_
  intro i hi
  exact isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus (modulePushforward f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit f)
    (fun I hI =>
      isIso_derivedPushforwardUnit_app_of_isKInjective f I hI)
    M i (hvan i hi)

/-- In a top-degree base-change situation, `Rf'_*(F'[0])` has no cohomology above `d`. -/
theorem isLE_derivedPushforward_baseChange
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] :
    TStructure.t.IsLE
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        S.f'.toLRSHom.toShHom).obj
        ((singleFunctor S.X'.Modules 0).obj F')) (S.d : ℤ) :=
  isLE_derivedPushforward_singleFunctor S.f'.toLRSHom.toShHom F' (S.d : ℤ)
    (fun i hi => isZero_rightDerivedPlus_pushforward_baseChange S i hi F')

/-- **Pullback of the top higher direct image.** In a top-degree base-change situation, for
`h : Y'' ⟶ Y'`,

> `h^* R^d f'_* F' ≅ H^d(Lh^* Rf'_* F')`. -/
def topDirectImagePullbackIso
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    {Y'' : Scheme.{u}} (h : Y'' ⟶ S.Y') :
    (Scheme.Modules.pullback h).obj
      ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          S.f'.toLRSHom.toShHom).obj
          ((singleFunctor S.X'.Modules 0).obj F'))) ≅
      (homologyFunctor Y''.Modules (S.d : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            S.f'.toLRSHom.toShHom).obj
            ((singleFunctor S.X'.Modules 0).obj F'))) :=
  topDirectImagePullbackIso_of_isLE S F' h (isLE_derivedPushforward_baseChange S F')

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

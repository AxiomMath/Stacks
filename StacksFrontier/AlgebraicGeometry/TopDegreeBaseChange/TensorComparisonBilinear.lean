module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonSections
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Additivity of the local tensor comparison of [Stacks, Tag 0EX3] (b)

The canonical map of conclusion (b) of [Stacks, Tag 0EX3] is, by the sheafification adjunction
of [Stacks, Tag 01CB], a bilinear family on sections, whose value over an open `U` is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorSection` read at the top
open of `U`. This file proves that the `ℤ`-indexed right derived functors of an additive functor
are additive in non-negative degrees, that the conjugated derived pushforward is additive, and
that the family is additive in the section of `G`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.additive_rightDerivedPlus_natDegree`: **the
  `ℤ`-indexed right derived functors `CategoryTheory.Functor.rightDerivedPlus` of an additive
  functor are additive in a non-negative degree**, and
  `...additive_rightDerivedPlus_pushforward_morphismRestrict` its instance at the pushforward
  along `f ∣_ U`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.conjugateRestrict_add`: **the degree-`n` right
  derived pushforward along `f ∣_ U`, conjugated by the restriction comparison of
  [Stacks, Tag 01E5], is additive**, for an arbitrary module downstairs.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.add_of_eq_conjugateRestrict`: and hence so is
  any family of morphisms over `U` that is pointwise equal to the conjugate of an additive
  family over `f⁻¹(U)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorSection_eq`: the value of
  `higherDirectImageTensorSection`, recorded propositionally.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorSection_add`:
  **biadditivity of the bilinear family in the section of `G`**.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

/-- **The `ℤ`-indexed right derived functors of an additive functor are additive, in a
non-negative degree.** -/
theorem additive_rightDerivedPlus_natDegree {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (R : C ⥤ D) [R.Additive] [EnoughInjectives C] (i : ℕ) :
    (R.rightDerivedPlus (i : ℤ)).Additive :=
  Functor.additive_of_iso (Stacks.DerivedIndexing.rightDerivedIso R i)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (n : ℕ)
  (U : Y.Opens)

/-- **The degree-`n` right derived pushforward along a restricted morphism of schemes is
additive.** -/
theorem additive_rightDerivedPlus_pushforward_morphismRestrict :
    ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).Additive :=
  additive_rightDerivedPlus_natDegree (Scheme.Modules.pushforward (f ∣_ U)) n

/-- **Additivity of the degree-`n` right derived pushforward along `f ∣_ U`, conjugated by the
restriction comparison of [Stacks, Tag 01E5].** -/
theorem conjugateRestrict_add (H : X.Modules)
    (α β : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj H) :
    (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n F).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map (α + β) ≫
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n H).hom =
      ((SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n F).inv ≫
          ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map α ≫
            (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n H).hom) +
        ((SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n F).inv ≫
          ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map β ≫
            (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n H).hom) :=
  have := additive_rightDerivedPlus_pushforward_morphismRestrict f n U
  comp_map_add_comp ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)) α β _ _

/-- **A family of morphisms over `U` which is the conjugate of an additive family of morphisms
over `f⁻¹(U)` is additive.** -/
theorem add_of_eq_conjugateRestrict (H : X.Modules) {M : Type*} [Add M]
    (ψ : M → ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj H))
    (hψ : ∀ m m' : M, ψ (m + m') = ψ m + ψ m')
    (g : M → ((Scheme.Modules.restrictFunctor U.ι).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj H)))
    (hg : ∀ m : M, g m =
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n F).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map (ψ m) ≫
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n H).hom)
    (m m' : M) : g (m + m') = g m + g m' := by
  rw [hg, hg, hg, hψ]
  exact conjugateRestrict_add f F n U H (ψ m) (ψ m')

/-- **The value of `higherDirectImageTensorSection`, recorded propositionally.** -/
theorem higherDirectImageTensorSection_eq (s : Γ(G, U)) :
    higherDirectImageTensorSection f F G n U s =
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n F).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map
          (tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U)
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U s)) ≫
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f U n
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
                ((Scheme.Modules.pullback f).obj G)))).hom := by
  refine (higherDirectImageTensorSection.eq_1 f F G n U s).trans ?_
  refine congrArg (fun g => _ ≫ _ ≫ g) ?_
  rfl

/-- **Additivity of the bilinear family in the section of `G`.** Tensoring with the pullback of a
section of `G` over `U`, taking the degree-`n` higher direct image and transporting back along the
restriction comparison of [Stacks, Tag 01E5] is additive in that section. The sum on the right
is formed in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling of the two
restricted modules. -/
theorem higherDirectImageTensorSection_add (s s' : Γ(G, U)) :
    higherDirectImageTensorSection f F G n U (s + s') =
      @HAdd.hAdd ((Scheme.Modules.restrictFunctor U.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F) ⟶
        (Scheme.Modules.restrictFunctor U.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
              X.toRingedSpace.IsSheaf⟩).obj F).obj ((Scheme.Modules.pullback f).obj G)))) _ _ _
        (higherDirectImageTensorSection f F G n U s)
        (higherDirectImageTensorSection f F G n U s') := by
  exact add_of_eq_conjugateRestrict f F n U _ _ (tensorLocalSection_unit_add f F G U)
    _ (higherDirectImageTensorSection_eq f F G n U) s s'

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

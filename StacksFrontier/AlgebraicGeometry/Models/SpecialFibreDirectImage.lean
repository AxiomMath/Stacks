module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Direct images of the structure sheaf on a divisor, from the total space

Let `f : W ⟶ X` be a quasi-compact quasi-separated morphism of schemes and let `i : W' ⟶ W`,
`j : X' ⟶ X` be closed immersions with a morphism `f' : W' ⟶ X'` such that `f' ≫ j = i ≫ f`.
Suppose that `W'` is cut out by a function: there is a short exact sequence
`0 ⟶ 𝒪_W --a--> 𝒪_W ⟶ i_*𝒪_{W'} ⟶ 0`. This is the situation of the special fibres of schemes
flat over a discrete valuation ring, `a` being multiplication by a uniformizer.

* If `R¹f_*𝒪_W = 0` and `R²f_*𝒪_W = 0`, then `R¹f'_*𝒪_{W'} = 0`: the long exact sequence of
  `f_*` puts `R¹f_*(i_*𝒪_{W'})` between two zeros, `i` is affine so that
  `R¹f_*(i_*𝒪_{W'}) = R¹(i ≫ f)_*𝒪_{W'}`, and vanishing descends along the affine second leg
  `j` of `f' ≫ j`.

## Main results

* `Stacks.Models.rightDerivedCompIsoOfIsZero`: Leray for an acyclic first factor.
* `Stacks.Models.isZero_rightDerived_one_of_shortExact`: `R¹f'_*𝒪_{W'} = 0`.

## References

* [Stacks Project, Tag 0E7F](https://stacks.math.columbia.edu/tag/0E7F)
* [Stacks Project, Tag 0E7I](https://stacks.math.columbia.edu/tag/0E7I)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace


universe u

namespace Stacks.Models

/-- **Leray when the first factor is acyclic on the module**: if `Rⁱc₁_*F = 0` for `i > 0`, then
`Rⁿ(c₁ ≫ c₂)_*F ≅ Rⁿc₂_*(c₁_*F)`. -/
def rightDerivedCompIsoOfIsZero {X Y Z : Scheme.{u}} (c₁ : X ⟶ Y) (c₂ : Y ⟶ Z)
    [QuasiCompact c₁] [QuasiSeparated c₁] [CompactSpace Y] (F : X.Modules)
    (hR₁ : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c₁).rightDerived i).obj F))
    (n : ℕ) :
    ((Scheme.Modules.pushforward (c₁ ≫ c₂)).rightDerived n).obj F ≅
      ((Scheme.Modules.pushforward c₂).rightDerived n).obj
        ((Scheme.Modules.pushforward c₁).obj F) :=
  ((Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso (c₁ ≫ c₂) 0 n n
      (by simp)).app F).symm ≪≫
    (DerivedCategory.homologyFunctor Z.Modules n).mapIso
      ((Stacks.Duality.derivedPushforwardCompIso c₁ c₂).symm.app _ ≪≫
        (Stacks.Duality.derivedPushforward c₂).mapIso
          (Stacks.Duality.nonempty_derivedPushforward_iso_of_isZero c₁ F
            ((Scheme.Modules.pushforward c₁).obj F) hR₁ (Iso.refl _)).some) ≪≫
    (Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso c₂ 0 n n
      (by simp)).app ((Scheme.Modules.pushforward c₁).obj F)

variable {W X W' X' : Scheme.{u}} (f : W ⟶ X) (i : W' ⟶ W) (j : X' ⟶ X) (f' : W' ⟶ X')
  [IsClosedImmersion i] [IsClosedImmersion j] [QuasiCompact f] [QuasiSeparated f]
  [QuasiCompact f'] [QuasiSeparated f'] (hcomm : f' ≫ j = i ≫ f)

omit [QuasiCompact f] [QuasiSeparated f] in
include hcomm in
/-- **`R¹f'_*𝒪_{W'} = 0` from the total space.** -/
theorem isZero_rightDerived_one_of_shortExact [CompactSpace W]
    (a : SheafOfModules.unit W.ringCatSheaf ⟶ SheafOfModules.unit W.ringCatSheaf)
    (ha : a ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom = 0)
    (hS : (ShortComplex.mk a _ ha).ShortExact)
    (hR1 : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit W.ringCatSheaf)))
    (hR2 : IsZero (((Scheme.Modules.pushforward f).rightDerived 2).obj
      (SheafOfModules.unit W.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward f').rightDerived 1).obj
      (SheafOfModules.unit W'.ringCatSheaf)) := by
  have h₁ : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W'.ringCatSheaf))) :=
    ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
      (Scheme.Modules.pushforward f)).exact_δ₁ hS 1).isZero_of_both_zeros
      (hR1.eq_of_src _ _) (hR2.eq_of_tgt _ _)
  have : (SheafOfModules.unit W'.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  exact Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward_of_comp_eq_of_isAffineHom
    f' j (i ≫ f) hcomm _ 1 (h₁.of_iso (rightDerivedCompIsoOfIsZero i f
      (SheafOfModules.unit W'.ringCatSheaf)
      (Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward i _) 1))

end Stacks.Models

end

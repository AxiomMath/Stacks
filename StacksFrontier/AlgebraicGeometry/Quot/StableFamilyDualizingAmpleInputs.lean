module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmple
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Quot.ExtendsFibreIsoNearPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmpleOfGenus

/-!
# Ampleness of the dualizing sheaf near a fibre without rational tails or bridges

Let `f : X → S` be a prestable family of curves whose fibres have genus `g ≥ 2`, and let `ω` be an
invertible module on `X` restricting on every fibre to that fibre's dualizing sheaf. For `s ∈ S`,
the fibre `X_s` has no rational tail and no rational bridge if and only if there is an open
`U ∋ s` such that `ω` is ample on `f⁻¹(U)` relative to `U`.

## Main results

* `AlgebraicGeometry.CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple`:
  the equivalence above.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- Let `f : X → S` be a prestable family of curves whose fibres have genus `g ≥ 2`, let `ω` be an
invertible module on `X` restricting on every fibre to its dualizing sheaf, and let `s ∈ S`. The
following are equivalent:

1. the fibre `X_s` (presented by a scheme of the site) has no rational tail and no rational
   bridge;
2. there is an open `U ∋ s` of `S` such that `ω` is ample on `f⁻¹(U)` relative to `U`. -/
theorem hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple
    (X : CurveFamily B hZ) (hX : IsPrestableCurveFamily B hZ X) (g : ℕ)
    (hgen : X.HasFibreGenus B hZ g) (hg : 2 ≤ g)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.obj X.total.property)
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω)
    (hω : X.IsDualizingOnFibres B hZ ω)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    (∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ X.residuePoint B hZ s)
        (q : yoneda.obj V ⟶ X.total.obj),
        X.IsFibrePresentation B hZ s v q ∧
          HasNoRationalTailNoRationalBridge
            (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
            (X.fibreMap B hZ s v)) ↔
      ∃ U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens, s ∈ U ∧
        ∀ ⦃X₁ : AlgebraicSpaces B integerBase hZ⦄ (p₁ : X₁ ⟶ X.total)
          (f₁ : X₁ ⟶ schemeSpace (Space.openSub X.base U)),
          IsPullback p₁ f₁ X.toBase (schemeSpaceMap (Space.openSubHom X.base U)) →
            Space.IsRelativelyAmple B integerBase hZ f₁
              ((Space.modulePullback B integerBase hZ p₁).obj ω) :=
  hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of
    isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hd hn C hC)
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hd hn C hC)
    (fun _ _ _ hf _ hL => Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper
      B integerBase hZ hf hL)
    (prestableFibreReading B hZ) X hX g hgen hg ω hωinv hω s

end CurveFamily

end AlgebraicGeometry

end

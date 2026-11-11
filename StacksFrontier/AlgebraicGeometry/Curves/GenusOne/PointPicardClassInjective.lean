module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointPicardClass
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.Surjectivity
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ZeroSchemeCoordinates
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapDivisorLift
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank

/-!
# On a curve of genus one, distinct points have distinct Picard classes

Let `X` be a smooth proper curve of genus one over an algebraically closed field `k`. Then the
map `X(k) → Pic(X)`, `x ↦ [𝒪_X(x)]`, is injective.

The invertible module `𝒪_X(x)` has degree `1 > 2g - 2 = 0`, so by Riemann–Roch
`dim_k H⁰(X, 𝒪_X(x)) = 1 + 1 - g = 1`. If `𝒪_X(x) ≅ 𝒪_X(y)`, the image of the canonical section
`1_x` and the canonical section `1_y` are two nonzero global sections of `𝒪_X(y)`, hence differ by
a nonzero scalar; sections differing by a unit have the same zero scheme, and the zero scheme of
`1_D` is `D`. So the reduced points `x` and `y` coincide.

## Main results

* `AlgebraicGeometry.IsCurve.eq_of_pointPicardClass_eq`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.Divisors (divisorSheaf divisorSheafGlobalSection IsEffectiveCartierDivisor)

universe u

namespace AlgebraicGeometry.IsCurve

/-- **On a curve of genus one, `x ↦ [𝒪_X(x)]` is injective on closed points.** Let `X` be a
smooth proper curve of genus one over an algebraically closed field `k`. If two closed points
`x, y` have the same class `[𝒪_X(x)] = [𝒪_X(y)]` in `Pic(X)`, then `x = y`. -/
theorem eq_of_pointPicardClass_eq (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] (hg : genus f = 1)
    {x y : X} (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X))
    (h : pointPicardClass k f hx = pointPicardClass k f hy) : x = y := by
  have : Nonempty X := ⟨x⟩
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  -- the reduced points, as divisors
  have hclx : Closeds.closure ({x} : Set X) = ⟨{x}, hx⟩ := Closeds.ext hx.closure_eq
  have hcly : Closeds.closure ({y} : Set X) = ⟨{y}, hy⟩ := Closeds.ext hy.closure_eq
  set Dx := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hDx
  set Dy := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds X) with hDy
  have hEx : IsEffectiveCartierDivisor Dx := by
    have := isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k f hx
    rw [hclx] at this
    exact this
  have hEy : IsEffectiveCartierDivisor Dy := by
    have := isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k f hy
    rw [hcly] at this
    exact this
  -- the two invertible sheaves are isomorphic
  have hpic : Stacks.Divisors.picardClass Dx = Stacks.Divisors.picardClass Dy := by
    have h1 : pointPicardClass k f hx = Stacks.Divisors.picardClass Dx := by
      letI := isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k f hx
      exact Stacks.Divisors.picardClass_congr (congrArg _ hclx)
    have h2 : pointPicardClass k f hy = Stacks.Divisors.picardClass Dy := by
      letI := isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k f hy
      exact Stacks.Divisors.picardClass_congr (congrArg _ hcly)
    rw [← h1, ← h2, h]
  obtain ⟨e⟩ : Nonempty (divisorSheaf Dx ≅ divisorSheaf Dy) :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hpic
  -- `dim_k H⁰(X, 𝒪_X(y)) = 1`
  have hinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (divisorSheaf Dy) :=
    Stacks.Divisors.isInvertible_divisorSheaf Dy
  have hdeg : invertibleCurveDegree k f hdim (divisorSheaf Dy) = 1 := by
    have h1 := invertibleCurveDegree_modulesInvertibleSheaf_vanishingIdeal_singleton f hdim hy
    have h2 := finrank_residueField_of_isClosed f y hy
    exact h1.trans (by exact_mod_cast h2)
  have hfin : Module.finrank k ((restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj (divisorSheaf Dy))) =
        1 := by
    have hrr :=
      finrank_cohomologyOverField_zero_eq_of_two_mul_genus_sub_two_lt_invertibleCurveDegree k f hdim
        (divisorSheaf Dy) (by rw [hdeg, hg]; norm_num)
    rw [hdeg, hg] at hrr
    rw [← (cohomologyOverFieldZeroLinearIso k f (divisorSheaf Dy)).toLinearEquiv.finrank_eq]
    exact_mod_cast (by simpa using hrr : (Module.finrank k _ : ℤ) = 1)
  -- the two sections
  set t : Γ(divisorSheaf Dy, ⊤) := e.hom.app ⊤ (divisorSheafGlobalSection Dx)
  set s : Γ(divisorSheaf Dy, ⊤) := divisorSheafGlobalSection Dy
  have hzt : Stacks.Divisors.zeroScheme X (divisorSheaf Dy) t = Dx :=
    (Stacks.AbelMap.zeroScheme_hom_app e _).trans (Stacks.Divisors.zeroScheme_canonicalSection Dx)
  have hzs : Stacks.Divisors.zeroScheme X (divisorSheaf Dy) s = Dy :=
    Stacks.Divisors.zeroScheme_canonicalSection Dy
  have hne : ∀ (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
      (r : Γ(divisorSheaf Dy, ⊤)),
      Stacks.Divisors.zeroScheme X (divisorSheaf Dy) r = D → r ≠ 0 := by
    rintro D hD r hr rfl
    have h0 : Stacks.Divisors.zeroScheme X (divisorSheaf Dy) 0 = ⊥ :=
      Stacks.LinearSystemScheme.zeroScheme_zero _
    exact Stacks.AbelMap.ne_bot_of_isEffectiveCartierDivisor D hD (hr.symm.trans h0)
  have hs0 : (show (restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj (divisorSheaf Dy))
      from s) ≠ 0 := hne Dy hEy s hzs
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hs0).1 hfin
    (show (restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj (divisorSheaf Dy))
      from t)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne Dx hEx t hzt (hc.symm.trans (zero_smul k _))
  have hct : t = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c • s := hc.symm
  have hunit : IsUnit (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c) :=
    (IsUnit.mk0 c hc0).map _
  have hu : Stacks.Divisors.zeroScheme X (divisorSheaf Dy)
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c • s) =
      Stacks.Divisors.zeroScheme X (divisorSheaf Dy) s :=
    Stacks.LinearSystemScheme.zeroScheme_unit_smul _ _ hunit
  have hD : Dx = Dy := hzt.symm.trans ((congrArg _ hct).trans (hu.trans hzs))
  have hsupp := congrArg (fun D : X.IdealSheafData => (D.support : Set X)) hD
  simp only [hDx, hDy, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hsupp
  have hxy : ({x} : Set X) = {y} := hsupp
  exact Set.singleton_eq_singleton_iff.mp hxy

end AlgebraicGeometry.IsCurve

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.CurveTrace
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardDegree
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleCohomology
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The degree on the Picard group of a smooth proper curve is onto

Let `X` be a smooth proper curve over an algebraically closed field `k`. A closed point `y` of
`X` has a regular, hence discrete valuation, local ring, so the reduced closed subscheme on `y`
is an effective Cartier divisor ([Stacks, Tag 0B8Y]); it is integral and proper over `k`, so its
ring of global functions is `k` and its degree is one
(`Stacks.Picard.picardDegree_divisorPicardClass`). Hence the degree `Pic(X) → ℤ` is onto.

This is one of the two inputs of the trace map `H²(X, μ_n) ≅ ℤ/n`
(`Stacks.Kummer.curveTrace`); the other is the `n`-divisibility of `Pic⁰(X)`, the kernel of the
degree, which comes from the Jacobian (an abelian variety over an algebraically closed field is
divisible). That second input is carried as the hypothesis `hdiv` below, in exactly the shape
`Stacks.Kummer.curveTrace` consumes it.

## Main results

* `Stacks.Picard.picardDegree_surjective`: the degree on `Pic(X)` is onto.
* `Stacks.Kummer.natCard_sheafH_two_rootsOfUnity_of_smoothProperCurve`: `#H²(X, μ_n) = n`,
  given the divisibility of `Pic⁰(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A closed point of a smooth proper curve over an algebraically closed field has degree
one**: the reduced closed subscheme on it is an effective Cartier divisor whose class has
degree `1`. -/
theorem exists_picardDegree_eq_one [IsAlgClosed k] [IsCurve k f] [Smooth f] [IsProper f] :
    ∃ z : ofScheme X,
      picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le z = 1 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨y, -, hy⟩ := IsClosed.exists_closed_singleton (X := X) isClosed_univ Set.univ_nonempty
  have hreg : IsRegularLocalRing (X.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth_over_field f y
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : TopologicalSpace.Closeds X)
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    ((isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve k f hy).out 1 4).1 hreg
  have : IsIntegral D.subscheme := isIntegral_subscheme_vanishingIdeal hy
  refine ⟨Stacks.Divisors.picardClass D, ?_⟩
  rw [picardDegree_divisorPicardClass f _ D]
  exact_mod_cast finrank_globalSections_eq_one k (D.subschemeι ≫ f)

/-- **The degree on the Picard group of a smooth proper curve over an algebraically closed field
is onto.** -/
theorem picardDegree_surjective [IsAlgClosed k] [IsCurve k f] [Smooth f] [IsProper f] :
    Function.Surjective (picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le) := by
  obtain ⟨z, hz⟩ := exists_picardDegree_eq_one f
  intro m
  exact ⟨m • z, by rw [map_zsmul, hz, smul_eq_mul, mul_one]⟩

end Stacks.Picard

namespace Stacks.Kummer

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] {n : ℕ} (hn : IsUnit (n : k))

include hn in
/-- **`#H²(X, μ_n) = n`** for a smooth proper curve over an algebraically closed field, given
that `Pic⁰(X)`, the kernel of the degree, is `n`-divisible. -/
theorem natCard_sheafH_two_rootsOfUnity_of_smoothProperCurve
    (hdiv : ∀ L : Picard.ofScheme X,
      Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 0 →
        ∃ M : Picard.ofScheme X, n • M = L) :
    Nat.card (Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2) = n :=
  natCard_sheafH_two_rootsOfUnity_of_degree f hn _ (Picard.picardDegree_surjective f) hdiv

include hn in
/-- **`#H²(X, ℤ/n) = n`** for a smooth proper curve over an algebraically closed field, with
`H²(X, ℤ/n) = Ext²(ℤ/n_X, ℤ/n_X)` computed in sheaves of `ℤ/n`-modules, given that `Pic⁰(X)` is
`n`-divisible. -/
theorem natCard_ext_two_constantModuleSheaf_of_smoothProperCurve
    (hdiv : ∀ L : Picard.ofScheme X,
      Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 0 →
        ∃ M : Picard.ofScheme X, n • M = L) :
    Nat.card ((CategoryTheory.Abelian.extFunctorObj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology) 2).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology)) = n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : NeZero (n : k) := ⟨hn.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k n
  rw [Nat.card_congr (extConstantAddEquivSheafHRootsOfUnity f hζ hn0 2).toEquiv]
  exact natCard_sheafH_two_rootsOfUnity_of_smoothProperCurve f hn hdiv

include f hn in
omit [IsProper f] in
/-- **`Hᵠ(X, ℤ/n) = 0` for `q ≥ 3`** on a smooth curve over an algebraically closed field, with
`Hᵠ(X, ℤ/n) = Extᵠ(ℤ/n_X, ℤ/n_X)` computed in sheaves of `ℤ/n`-modules. -/
theorem subsingleton_ext_constantModuleSheaf_of_smoothCurve (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton ((CategoryTheory.Abelian.extFunctorObj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology) q).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : NeZero (n : k) := ⟨hn.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k n
  exact @Equiv.subsingleton _ _ (extConstantAddEquivSheafHRootsOfUnity f hζ hn0 q).toEquiv
    (subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve f hn q hq)

end Stacks.Kummer

end

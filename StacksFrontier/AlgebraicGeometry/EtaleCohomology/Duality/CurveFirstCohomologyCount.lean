module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnityFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardTorsionRank

/-!
# `#H¹(X, ℤ/n) = n^{2g}` for a smooth proper curve

For a smooth proper curve `X` of genus `g` over an algebraically closed field `k` and `n`
invertible in `k`, `H¹(X, ℤ/n) = Ext¹(ℤ/n_X, ℤ/n_X)` (computed in sheaves of `ℤ/n`-modules) has
`n^{2g}` elements: it is `H¹(X, μ_n)` through a primitive `n`-th root of unity, which is
`Pic(X)[n]` ([Stacks, Tag 03RQ]), of order `n^{2g}`
(`Stacks.Picard.natCard_torsionBy_eq_pow_genus`).

## Main results

* `Stacks.Kummer.natCard_ext_one_constantModuleSheaf_of_smoothProperCurve`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Kummer

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] {n : ℕ} (hn : IsUnit (n : k))

include hn in
/-- **`#H¹(X, ℤ/n) = n^{2g}`** for a smooth proper curve of genus `g` over an algebraically closed
field, with `H¹(X, ℤ/n) = Ext¹(ℤ/n_X, ℤ/n_X)` computed in sheaves of `ℤ/n`-modules. -/
theorem natCard_ext_one_constantModuleSheaf_of_smoothProperCurve :
    Nat.card ((CategoryTheory.Abelian.extFunctorObj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology) 1).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n)
          X.smallEtaleTopology)) = n ^ (2 * genus f) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : NeZero (n : k) := ⟨hn.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  have : IsProjectiveVariety k f := (isProjectiveVariety_iff_isProjectiveMorphism k f).2
    (isProjectiveMorphism_of_isProper_of_isCurve k f)
  rw [Nat.card_congr (extConstantAddEquivSheafHRootsOfUnity f hζ hn0 1).toEquiv,
    Nat.card_congr (h1RootsOfUnityAddEquivPicardTorsion_of_isCurve.{u + 1, 0, u} X n hn0
      (isUnit_natCast_globalSections X n f hn) f hn).toEquiv]
  exact Stacks.Picard.natCard_torsionBy_eq_pow_genus f n hn

end Stacks.Kummer

end

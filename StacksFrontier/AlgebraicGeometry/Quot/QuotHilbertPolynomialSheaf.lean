/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorAffineLocal
public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveStepOne

/-!
# `Quot^P_{F/X/B}` is a sheaf when the Quot presheaf is

The condition cutting out `Quot^P_{F/X/B}` inside the Quot presheaf
(`AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot`) is a condition on the points of
the test scheme: `P(n) = χ(X_t, 𝒬_t ⊗ L_t^{⊗ n})` for every point `t`. It is local for the fppf
topology: a covering sieve of a test scheme `T` contains, through every point `t` of `T`, a
morphism `U ⟶ T` hitting `t`, and the twisted Euler characteristic of the pullback of `𝒬` to `U`
at a point `t'` over `t` is that of `𝒬` at `t` (flat base change of cohomology,
`AlgebraicGeometry.Space.CoherentHom.twistedEuler_eq`). Hence `Quot^P_{F/X/B}` is an fppf sheaf
whenever the Quot presheaf is (Stacks 09TT).

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isSheaf_hilbertPolynomialQuot`.

## References

* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- **`Quot^P_{F/X/B}` is an fppf sheaf when the Quot presheaf is** (Stacks 09TT for the
subfunctor of Remark 0DP6 at `E_n = L^{⊗ n}`): the Hilbert polynomial condition is checked on
points, and every point of a test scheme is hit by a member of any covering sieve. -/
theorem isSheaf_hilbertPolynomialQuot (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) D.quotSitePresheaf) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (D.hilbertPolynomialQuot L P).toFunctor := by
  let : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
  refine D.isSheaf_toFunctor_of_isSheaf _ hP fun T x hx ↦ ?_
  refine (D.mem_hilbertPolynomialQuot_iff L P x).2 fun t n ↦ ?_
  obtain ⟨V, v, -, hv, -, -, y, hy⟩ :=
    BigFppfOver.exists_affine_mem_of_mem_topology B S hS hx t
  have h₁ := (D.mem_hilbertPolynomialQuot_iff L P (T := Opposite.op V)
    (D.quotSitePresheaf.map v.op x)).1 hv y n
  have h₂ := @CoherentHom.twistedEuler_eq B S hS D.toCoherentSituation _ _ L this
    (x.cohHomBaseChange v) y n
  have hmap : D.quotSitePresheaf.map v.op x = x.baseChange v := rfl
  rw [hmap] at h₁
  have hy' : (x.cohHomBaseChange v).baseScheme y = t := hy
  rw [hy'] at h₂
  exact h₁.trans h₂

end AlgebraicGeometry.Space.QuotSituation

end

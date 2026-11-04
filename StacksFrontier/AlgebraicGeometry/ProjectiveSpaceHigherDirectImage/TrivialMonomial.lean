module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MonomialPairing

/-!
# Multiplication by the trivial monomial is the identity

The monomial of the zero multidegree is the constant `1`, and multiplication by `1` on a twist
`𝒪(d)` of projective space is the identity: on every localized fibre the multiplication map is
the localization of `LinearMap.mulLeft 1`, which is the identity linear map. Over an arbitrary
base the same holds for
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverMulMonomial`, the twists of
`ℙⁿ_S` and the multiplications between them being inverse images of those of the integral model.

This is the entry of the duality pairing of the degree-`n` row of [Stacks, Tag 01XW] at the
complementary degree zero: there the only multidegree is the zero one, so the pairing is the
trace isomorphism itself.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftIntOf_one`: **multiplication by `1` on a
  twist of `Proj 𝒮` is the identity.**
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverMulMonomial_zero`:
  **multiplication by the monomial of the zero multidegree on `ℙⁿ_S` is the identity.**

## Implementation notes

`TopCat.Sheaf` and `CategoryTheory.sheafCompose` are made reducible for implicit arguments and
`AlgebraicGeometry.ProjectiveSpectrum.top` reducible for instances, as in
`StacksFrontier/AlgebraicGeometry/ProjKoszulComplex/TwistStalk.lean`, where the companion
composition law for these multiplication maps is proved the same way: without them the
extensionality of a morphism of sheaves of modules on `Proj` does not elaborate within the
heartbeat budget.

No `stacks` attribute is attached: nothing here is a clause of a tag.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- Multiplication by `1` in a localization is the identity. -/
private theorem map_mulLeft_one {A : Type u} [CommRing A] {P : Submonoid A}
    (z : Localization P) : LocalizedModule.map P (LinearMap.mulLeft A 1) z = z := by
  induction z using Localization.induction_on with
  | H y =>
    show LocalizedModule.map P (LinearMap.mulLeft A 1) (LocalizedModule.mk y.1 y.2) = _
    rw [LocalizedModule.map_mk]
    simp only [LinearMap.mulLeft_apply, one_mul]
    rfl

/-- **Multiplication by the constant `1` on a twist of `Proj 𝒮` is the identity**: on every
localized fibre it is the localization of multiplication by `1`. -/
theorem twistMulLeftIntOf_one {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S]
    [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℤ) (he : ((0 : ℕ) : ℤ) + d = d) :
    twistMulLeftIntOf 𝒮 (⟨1, SetLike.one_mem_graded 𝒮⟩ : 𝒮 0) d d he =
      𝟙 (twistingSheaf 𝒮 d) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext y
  exact Subtype.ext (funext fun p => map_mulLeft_one (y.1 p))

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Multiplication by the monomial of the zero multidegree on `ℙⁿ_S` is the identity.** -/
theorem twistOverMulMonomial_zero (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (b : MonomialIndex.{u} n 0) (h : (0 : ℤ) + d = d) :
    twistOverMulMonomial n S b d d h = 𝟙 _ := by
  have hb : b.1 = 0 := (Finsupp.degree_eq_zero_iff b.1).1 (by exact_mod_cast b.2)
  have hmon : coordMonomial b = 1 := by
    rw [coordMonomial, hb, Finsupp.equivMapDomain_zero, MvPolynomial.monomial_zero', map_one]
  rw [twistOverMulMonomial, twistOverMulLeft_congr n S _
      (⟨1, SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))⟩ : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0)
      hmon d d _ (by omega), twistOverMulLeft,
    AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftIntOf_one
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d (by omega)]
  exact (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).map_id _

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end

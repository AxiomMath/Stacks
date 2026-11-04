module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaMultiplicativity

/-!
# The comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` in every integer degree

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring and `U_d ⊆ Proj 𝒮` the degree `d` open of
Stacks Tag 01N5.  On `U_d` the twist `𝒪_{U_d}(d)` is invertible, so its tensor powers
`Stacks.Ample.tensorPowModule` are defined for every *integer* exponent, and every `d`-divisible
twist `𝒪_{U_d}(dn)` is defined for every integer `n` as well.  The comparison
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` between the two families is
nevertheless built by structural recursion on a *natural* number: its source and target are
indexed by `ℤ`, but the recursion that produces it climbs from the exponent `0` upwards one step
at a time, so it says nothing in a negative degree.

This file removes that restriction.  What makes it possible is that both families are families of
*invertible* modules with a multiplication: `Stacks.Ample.tensorPowModuleAddIso` and
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` are isomorphisms in arbitrary
integer degrees, so `𝒪_{U_d}(d)^{⊗ (-n)}` is a tensor inverse of `𝒪_{U_d}(d)^{⊗ n}` and
`𝒪_{U_d}(-dn)` is a tensor inverse of `𝒪_{U_d}(dn)`.  Tensor inverses are unique up to
isomorphism, and the comparison in the degree `-n` is the one the comparison in the degree `n`
induces on the inverses.

## Main definitions

* `Stacks.Monoidal.isoOfTensorInverse`: **tensor inverses are unique up to isomorphism.** If
  `A ≅ B` and `A ⊗ X ≅ 𝟙` and `Y ⊗ B ≅ 𝟙` in a monoidal category, then `X ≅ Y`.  Nothing here
  mentions sheaves.
* `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleInvIso` and `twistInvIso`: the two inverse
  laws, `L ^⊗ n ⊗ L ^⊗ (-n) ≅ 𝒪_{U_d}` and `𝒪_{U_d}(-dn) ⊗ 𝒪_{U_d}(dn) ≅ 𝒪_{U_d}`.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaNegNat`: the comparison in the degree `-m` for a
  natural number `m`.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt`: **the comparison
  `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` for an arbitrary integer `n`.**

## Main results

* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_natCast`: in a nonnegative degree `thetaInt` is
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta`, so it is an extension of the
  comparison already built and not a second comparison.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_neg_natCast_succ`: in a negative degree it is
  `thetaNegNat`.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_inv_law`: **the comparison in the degrees `n` and
  `-n` carries the inverse law of the tensor powers to the inverse law of the twists**, which is
  the identity that characterises the extension.

## Implementation notes

`isoOfTensorInverse` is the usual three-line argument
`X ≅ 𝟙 ⊗ X ≅ (Y ⊗ B) ⊗ X ≅ (Y ⊗ A) ⊗ X ≅ Y ⊗ (A ⊗ X) ≅ Y ⊗ 𝟙 ≅ Y`.  It needs the two inverse
laws in *opposite* orders — `A ⊗ X` and `Y ⊗ B` — which is why both of them are stated below in
the order the argument consumes rather than in one uniform order; the addition law and the
canonical multiplication are isomorphisms in every pair of integer degrees, so either order is
available.

`thetaInt` is defined by a match on the two constructors of `ℤ`, as
`Stacks.TensorPowers.intTensorPow` is: the nonnegative branch is `theta` and the negative branch
is `thetaNegNat`, and no transport along an equality of integers appears in either, because
`Int.negSucc m` is the degree `-((m + 1 : ℕ) : ℤ)` definitionally.

The monoidal structure is `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`, the strict structure
of Stacks Tag 01CA on `X.Modules`, brought in as a local instance exactly as in
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaMultiplicativity.lean`: there is no global
monoidal instance at `(Proj.degreeOpen 𝒮 d).toScheme.Modules`.

## References

* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.Ample
open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.RelativeVeryAmple

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Tensor inverses are unique up to isomorphism.** If `A` and `B` are isomorphic, `X` is a
tensor inverse of `A` on the right and `Y` is a tensor inverse of `B` on the left, then `X` and
`Y` are isomorphic:

`X ≅ 𝟙 ⊗ X ≅ (Y ⊗ B) ⊗ X ≅ (Y ⊗ A) ⊗ X ≅ Y ⊗ (A ⊗ X) ≅ Y ⊗ 𝟙 ≅ Y`. -/
def isoOfTensorInverse {A B X Y : C} (e : A ≅ B) (hx : A ⊗ X ≅ 𝟙_ C) (hy : Y ⊗ B ≅ 𝟙_ C) :
    X ≅ Y :=
  (λ_ X).symm ≪≫ whiskerRightIso (hy.symm ≪≫ whiskerLeftIso Y e.symm) X ≪≫
    α_ Y A X ≪≫ whiskerLeftIso Y hx ≪≫ ρ_ Y

/-- The forward map of `Stacks.Monoidal.isoOfTensorInverse`, unfolded into its six factors. -/
theorem isoOfTensorInverse_hom {A B X Y : C} (e : A ≅ B) (hx : A ⊗ X ≅ 𝟙_ C)
    (hy : Y ⊗ B ≅ 𝟙_ C) :
    (isoOfTensorInverse e hx hy).hom =
      (λ_ X).inv ≫ (hy.inv ≫ Y ◁ e.inv) ▷ X ≫ (α_ Y A X).hom ≫ Y ◁ hx.hom ≫ (ρ_ Y).hom :=
  rfl

end Stacks.Monoidal

namespace Stacks.AlgebraicGeometry.ThetaMul

open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen

attribute [local instance] schemeMonoidal strictSchemeMonoidal

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-! ### The two inverse laws -/

/-- **The tensor powers of `𝒪_{U_d}(d)` in the degrees `n` and `-n` are tensor inverses**,
`𝒪_{U_d}(d)^{⊗ n} ⊗ 𝒪_{U_d}(d)^{⊗ (-n)} ≅ 𝒪_{U_d}`.  This is the addition law
`Stacks.Ample.tensorPowModuleAddIso` of Stacks Tag 01CU at the bidegree `(n, -n)`, reindexed to
the degree `0`, where the power is the structure sheaf. -/
def tensorPowModuleInvIso (n : ℤ) :
    tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) n ⊗
        tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) (-n) ≅
      𝟙_ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.Modules :=
  tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) n (-n) ≪≫
    tensorPowModuleCongr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
      (show n + -n = 0 from by ring) ≪≫
    tensorPowModuleZeroIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))

/-- **The `d`-divisible twists in the degrees `-dn` and `dn` are tensor inverses**,
`𝒪_{U_d}(-dn) ⊗ 𝒪_{U_d}(dn) ≅ 𝒪_{U_d}`.  This is the canonical multiplication isomorphism
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` at the bidegree `(-n, n)`,
carried to the degree `0`, where the twist is the structure sheaf by
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit`. -/
def twistInvIso (n : ℤ) :
    twist 𝒮 d ((d : ℤ) * (-n)) ⊗ twist 𝒮 d ((d : ℤ) * n) ≅
      𝟙_ (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.Modules :=
  twistMulIso 𝒮 d (-n) n ≪≫
    eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) * (-n + n) = 0 from by ring)) ≪≫
    twistZeroIsoUnit 𝒮 d

/-! ### The comparison in a negative degree -/

/-- **The comparison `𝒪_{U_d}(d)^{⊗ (-m)} ≅ 𝒪_{U_d}(-dm)` in the degree `-m` for a natural
number `m`**: the isomorphism that the comparison
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` in the degree `m` induces on the
tensor inverses, by `Stacks.Monoidal.isoOfTensorInverse`. -/
def thetaNegNat (m : ℕ) :
    tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
        (-(m : ℤ)) ≅
      twist 𝒮 d ((d : ℤ) * (-(m : ℤ))) :=
  Stacks.Monoidal.isoOfTensorInverse (theta 𝒮 d m) (tensorPowModuleInvIso 𝒮 d (m : ℤ))
    (twistInvIso 𝒮 d (m : ℤ))

/-- **The comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` in every integer degree `n`.**  In a
nonnegative degree it is `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta`, which is
built by recursion upwards from the degree `0`; in a negative degree it is `thetaNegNat`, the
comparison induced on the tensor inverses. -/
def thetaInt : (n : ℤ) →
    tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) n ≅
      twist 𝒮 d ((d : ℤ) * n)
  | .ofNat m => theta 𝒮 d m
  | .negSucc m => thetaNegNat 𝒮 d (m + 1)

/-- In a nonnegative degree the integer comparison is the comparison built by recursion. -/
theorem thetaInt_natCast (m : ℕ) : thetaInt 𝒮 d (m : ℤ) = theta 𝒮 d m := rfl

/-- In a negative degree the integer comparison is the comparison induced on the tensor
inverses. -/
theorem thetaInt_neg_natCast_succ (m : ℕ) :
    thetaInt 𝒮 d (-((m : ℤ) + 1)) = thetaNegNat 𝒮 d (m + 1) := rfl

/-- The integer comparison in the degree `0` is the comparison in the degree `0`. -/
theorem thetaInt_zero : thetaInt 𝒮 d 0 = theta 𝒮 d 0 := rfl

/-- The integer comparison in the degree `1` is the canonical identification of the first tensor
power, by `Stacks.AlgebraicGeometry.ThetaMul.theta_one_eq`. -/
theorem thetaInt_one : thetaInt 𝒮 d 1 = twistOneIso 𝒮 d := theta_one_eq 𝒮 d

/-- **The negative half of the comparison, unfolded.**  In the degree `-m` the forward map is the
inverse law of the twists run backwards, the comparison in the degree `m` run backwards on the
second factor, and the inverse law of the tensor powers run forwards, all between two unitors. -/
theorem thetaNegNat_hom (m : ℕ) :
    (thetaNegNat 𝒮 d m).hom =
      (λ_ (tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) (-(m : ℤ)))).inv ≫
        ((twistInvIso 𝒮 d (m : ℤ)).inv ≫
            twist 𝒮 d ((d : ℤ) * (-(m : ℤ))) ◁ (theta 𝒮 d m).inv) ▷
          tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
            (twist 𝒮 d (d : ℤ)) (-(m : ℤ)) ≫
          (α_ _ _ _).hom ≫
            twist 𝒮 d ((d : ℤ) * (-(m : ℤ))) ◁ (tensorPowModuleInvIso 𝒮 d (m : ℤ)).hom ≫
              (ρ_ (twist 𝒮 d ((d : ℤ) * (-(m : ℤ))))).hom :=
  Stacks.Monoidal.isoOfTensorInverse_hom (theta 𝒮 d m) (tensorPowModuleInvIso 𝒮 d (m : ℤ))
    (twistInvIso 𝒮 d (m : ℤ))

end Stacks.AlgebraicGeometry.ThetaMul

end

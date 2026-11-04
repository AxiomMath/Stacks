module

public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafSum
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsionExponent
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf

/-!
# The Picard class of an effective Cartier divisor

Let `X` be a scheme. An effective Cartier divisor `D` on `X` has an invertible sheaf
`𝒪_X(D) = SheafHom(ℐ_D, 𝒪_X)`, so it has a class in the Picard group `Pic(X)` of isomorphism
classes of invertible `𝒪_X`-modules under tensor product. This file shows that
`D ↦ [𝒪_X(D)]` is additive: the sum of two effective Cartier divisors — the *product* `D * D'`
of their ideal sheaves — goes to the sum of their classes, the empty divisor `⊤` goes to `0`,
and the `n`-fold sum `D ^ n` goes to `n • [𝒪_X(D)]`. Dually `[𝒪_X(-D)] = -[𝒪_X(D)]`, and the
conormal sheaf `𝒞_{D/X}` of `D` has, as an invertible module on the closed subscheme `D`, the
class obtained by pulling `[𝒪_X(-D)]` back along `D ⟶ X`.

**Beware the notation.** On `AlgebraicGeometry.Scheme.IdealSheafData` the sum of divisors is the
product `*` of ideal sheaves and the `n`-fold sum is the power `^`; Mathlib's `Add` on
`IdealSheafData` is `⊔`, which is scheme-theoretic intersection and is *not* divisor addition.
Every statement below is phrased in `*` and `^`, as in
`StacksFrontier/AlgebraicGeometry/DivisorSum/Basic.lean`.

## Main definitions

* `Stacks.Divisors.picardClass`: the class of `𝒪_X(D)` in `Pic(X)`.
* `Stacks.Divisors.negativeTwistPicardClass`: the class of `𝒪_X(-D) = ℐ_D` in `Pic(X)`.
* `Stacks.Divisors.invertibleSheafTopIsoUnit`: the identification `𝒪_X(∅) ≅ 𝒪_X` of the
  invertible sheaf of the empty divisor with the structure sheaf.

## Main results

* `Stacks.Divisors.picardClass_mul`: `[𝒪_X(D + D')] = [𝒪_X(D)] + [𝒪_X(D')]`, i.e. the Picard
  class is additive in the divisor.
* `Stacks.Divisors.picardClass_top`: the empty divisor has class `0`.
* `Stacks.Divisors.picardClass_pow`: `[𝒪_X(nD)] = n • [𝒪_X(D)]`.
* `Stacks.Divisors.negativeTwistPicardClass_eq_neg`: `[𝒪_X(-D)] = -[𝒪_X(D)]`.
* `Stacks.Divisors.picardClass_immersionConormalSheaf`: the class of the conormal sheaf
  `𝒞_{D/X}` on the subscheme `D` is the pullback of `[𝒪_X(-D)]` along `D ⟶ X`.

## Implementation notes

**Which Picard group.** `Stacks.SheafOfModules.PicardGroup`, through its scheme-level
abbreviation `Stacks.Picard.ofScheme`. Of the library's three Picard-group developments it is
the only one carrying both `Stacks.SheafOfModules.picardClass_tensorSheaf` (addition is tensor
product) and a pullback homomorphism (`Stacks.Picard.pullbackClass`), and both are needed here
— the first for every
statement, the second for the conormal sheaf.

**Reconciling the spellings.** Three families meet here and each writes the structure sheaf of
rings differently: the divisor sheaves `Stacks.Divisors.invertibleSheaf'` and
`Stacks.Divisors.negativeTwist'` are indexed by
`structureSheafRing X.toRingedSpace`, their
invertibility by its `.property`; `Stacks.Picard.ofScheme` is indexed by
`Stacks.RingedSpace.structureIsSheaf X.toRingedSpace`; and
`Stacks.Divisors.invertibleSheafSumIso` is stated with the tensor product
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X.toRingedSpace` while
`Stacks.SheafOfModules.picardClass_tensorSheaf` wants
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf hO`. All of these are
definitionally equal and all of them elaborate against each other, but none of them is found by
`rw` or by `simp`, whose motives are checked syntactically. The whole file therefore uses the
one move documented at `StacksFrontier/AlgebraicGeometry/CurveDegreeTensor/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/PicardGroup/Scheme.lean`: **rebind with a declared type**. Each
imported iso or invertibility fact is `have`-bound at the spelling the Picard-group API wants
(see `Stacks.Divisors.isInvertible_invertibleSheaf_picard` and the `have e : …` lines in the
proofs), after which the Picard lemmas apply with no rewriting at all. No transport lemma, no
`eqToIso` and no `conv` is needed, and in particular the two `tensorPower` constants never have
to be compared: the proof of `Stacks.Divisors.picardClass_pow` is an induction on `*` through
`Stacks.Divisors.picardClass_mul` rather than an appeal to
`Stacks.Picard.classOf_tensorPower`.

**Instances for the divisor operations.** `AlgebraicGeometry.isEffectiveCartierDivisor_mul`,
`Stacks.Divisors.isEffectiveCartierDivisor_pow` and
`Stacks.Divisors.isEffectiveCartierDivisor_top` are theorems taking their hypotheses
explicitly, but
`Stacks.Divisors.picardClass (D * D')` cannot even be *stated* without
`IsEffectiveCartierDivisor (D * D')` in scope. They are therefore re-registered here as
instances `Stacks.Divisors.IsEffectiveCartierDivisor.mul`, `.pow` and `.top`, which is what lets
every statement below be written as an equation between Picard classes of divisors rather than
as an equation with invertibility hypotheses attached.

**The empty divisor.** `Stacks.Divisors.picardClass_top` is proved from additivity alone:
`⊤ * ⊤ = ⊤`, so the class of `⊤` is its own double and hence `0`. The isomorphism
`𝒪_X(∅) ≅ 𝒪_X` is then recovered from `Stacks.SheafOfModules.picardClass_eq_iff`, under which
equality of Picard classes *is* isomorphism of invertible modules; the isomorphism so obtained
is a choice, since the Picard group remembers only the isomorphism class.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02OP](https://stacks.math.columbia.edu/tag/02OP)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (IsInvertible)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D D' : X.IdealSheafData)

/-! ### The effective-Cartier property of the divisor operations, as instances -/

/-- The empty closed subscheme, the zero of the monoid of effective Cartier divisors, is an
effective Cartier divisor. -/
instance IsEffectiveCartierDivisor.top : IsEffectiveCartierDivisor (⊤ : X.IdealSheafData) :=
  isEffectiveCartierDivisor_top

/-- The sum `D + D'` of two effective Cartier divisors, the closed subscheme cut out by the
product `ℐ_D ℐ_{D'}` of their ideal sheaves, is an effective Cartier divisor. -/
instance IsEffectiveCartierDivisor.mul [h : IsEffectiveCartierDivisor D]
    [h' : IsEffectiveCartierDivisor D'] : IsEffectiveCartierDivisor (D * D') :=
  isEffectiveCartierDivisor_mul D D' h h'

/-- The `n`-fold sum `nD` of an effective Cartier divisor is an effective Cartier divisor. -/
instance IsEffectiveCartierDivisor.pow [h : IsEffectiveCartierDivisor D] (n : ℕ) :
    IsEffectiveCartierDivisor (D ^ n) :=
  isEffectiveCartierDivisor_pow h n

/-! ### The Picard class of a divisor -/

/-- The sheaf `𝒪_X(D)` of an effective Cartier divisor is invertible, at the index that the
Picard group of `Stacks.Picard.ofScheme` is written over. -/
theorem isInvertible_invertibleSheaf_picard [IsEffectiveCartierDivisor D] :
    IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) (invertibleSheaf' D) :=
  isTensorInvertible_invertibleSheaf D

/-- The ideal sheaf `𝒪_X(-D) = ℐ_D` of an effective Cartier divisor is invertible, at the index
that the Picard group of `Stacks.Picard.ofScheme` is written over. -/
theorem isInvertible_negativeTwist_picard [IsEffectiveCartierDivisor D] :
    IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) (negativeTwist' D) :=
  isTensorInvertible_negativeTwist D

/-- **The class of an effective Cartier divisor in the Picard group**: the class of its
invertible sheaf `𝒪_X(D)`. -/
abbrev picardClass [IsEffectiveCartierDivisor D] : Stacks.Picard.ofScheme X :=
  Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace)
    (invertibleSheaf' D) (isInvertible_invertibleSheaf_picard D)

/-- The class in the Picard group of the ideal sheaf `𝒪_X(-D) = ℐ_D` of an effective Cartier
divisor. -/
abbrev negativeTwistPicardClass [IsEffectiveCartierDivisor D] : Stacks.Picard.ofScheme X :=
  Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) (negativeTwist' D)
    (isInvertible_negativeTwist_picard D)

/-- Equal divisors have equal Picard classes. -/
theorem picardClass_congr {E E' : X.IdealSheafData} (h : E = E')
    [IsEffectiveCartierDivisor E] [IsEffectiveCartierDivisor E'] :
    picardClass E = picardClass E' := by
  subst h
  rfl

/-- A module isomorphic to the tensor product of two invertible modules has the sum of their
Picard classes. -/
private theorem picardClass_eq_add_of_iso
    (L N P : _root_.SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.presheaf (structureIsSheaf X.toRingedSpace)))
    (hL : IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L)
    (hN : IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) N)
    (hP : IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) P)
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (structureIsSheaf X.toRingedSpace)⟩).obj L).obj N ≅ P) :
    Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) P hP =
      Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL +
      Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) N hN :=
  (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e.symm⟩ |>.trans
    (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ L N hL hN
      (Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _)).symm

/-- **The Picard class is additive in the divisor.** The sum `D + D'` of two effective Cartier
divisors is cut out by the product of their ideal sheaves, and `𝒪_X(D + D')` is the tensor
product `𝒪_X(D) ⊗ 𝒪_X(D')` (Tag 02OP), which is addition of Picard classes (Tag 01CX). -/
theorem picardClass_mul [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    picardClass (D * D') = picardClass D + picardClass D' :=
  picardClass_eq_add_of_iso _ _ _ _ _ _ (invertibleSheafSumIso D D')

/-- **The empty divisor has Picard class `0`.** The empty divisor is the unit of the monoid of
effective Cartier divisors, so its class is its own double. -/
theorem picardClass_top : picardClass (⊤ : X.IdealSheafData) = 0 := by
  have hmul : picardClass ((⊤ : X.IdealSheafData) * ⊤) =
      picardClass (⊤ : X.IdealSheafData) + picardClass (⊤ : X.IdealSheafData) :=
    picardClass_mul ⊤ ⊤
  have htop : ((⊤ : X.IdealSheafData) * ⊤) = ⊤ := by
    rw [← Scheme.IdealSheafData.one_eq_top, one_mul]
  have hself : picardClass (⊤ : X.IdealSheafData) =
      picardClass (⊤ : X.IdealSheafData) + picardClass (⊤ : X.IdealSheafData) :=
    (picardClass_congr htop).symm.trans hmul
  have hzero : picardClass (⊤ : X.IdealSheafData) + 0 =
      picardClass (⊤ : X.IdealSheafData) + picardClass (⊤ : X.IdealSheafData) := by
    rw [add_zero]
    exact hself
  exact (add_left_cancel hzero).symm

/-- **The invertible sheaf of the empty divisor is the structure sheaf**, `𝒪_X(∅) ≅ 𝒪_X`. The
empty divisor has Picard class `0`, and equality of Picard classes is isomorphism of invertible
modules. -/
def invertibleSheafTopIsoUnit :
    invertibleSheaf' (⊤ : X.IdealSheafData) ≅
      _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  ((Stacks.SheafOfModules.picardClass_eq_iff X.presheaf
      (structureIsSheaf X.toRingedSpace) _ _ _ _).1
    ((picardClass_top (X := X)).trans
      (Stacks.SheafOfModules.picardClass_zero X.presheaf
        (structureIsSheaf X.toRingedSpace)).symm)).some

/-- **The `n`-fold sum of an effective Cartier divisor has `n` times its Picard class**,
`[𝒪_X(nD)] = n • [𝒪_X(D)]`: an induction on `n` through additivity, the base case being the
empty divisor. -/
theorem picardClass_pow [IsEffectiveCartierDivisor D] (n : ℕ) :
    picardClass (D ^ n) = (n : ℤ) • picardClass D := by
  induction n with
  | zero =>
      have h0 : D ^ 0 = ⊤ := (pow_zero D).trans Scheme.IdealSheafData.one_eq_top
      rw [picardClass_congr h0, picardClass_top, Nat.cast_zero, zero_zsmul]
  | succ n ih =>
      have hsucc : D ^ (n + 1) = D ^ n * D := pow_succ D n
      rw [picardClass_congr hsucc, picardClass_mul (D ^ n) D, ih, Nat.cast_add, Nat.cast_one,
        add_zsmul, one_zsmul]

/-- **The ideal sheaf of an effective Cartier divisor has the negative Picard class of its
invertible sheaf**, `[𝒪_X(-D)] = -[𝒪_X(D)]`: the evaluation pairing `𝒪_X(D) ⊗ ℐ_D ≅ 𝒪_X`
trivializes the tensor product, and addition of Picard classes is tensor product. -/
theorem negativeTwistPicardClass_eq_neg [IsEffectiveCartierDivisor D] :
    negativeTwistPicardClass D = -picardClass D := by
  refine eq_neg_of_add_eq_zero_right ?_
  have := isTensorInvertible_negativeTwist D
  exact (picardClass_eq_add_of_iso _ _ _ _ _ _
    (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D))).symm.trans
    (Stacks.SheafOfModules.picardClass_zero X.presheaf (structureIsSheaf X.toRingedSpace))

/-! ### The conormal sheaf of a divisor -/

/-- **The conormal sheaf `𝒞_{D/X}` of an effective Cartier divisor is invertible** on the
closed subscheme `D`: it is the restriction `ℐ_D|_D` of the ideal sheaf (Tag 0B3P), and the
pullback of an invertible module is invertible. -/
theorem isInvertible_immersionConormalSheaf [IsEffectiveCartierDivisor D] :
    IsInvertible D.subscheme.presheaf (structureIsSheaf D.subscheme.toRingedSpace)
      (Stacks.Thickenings.immersionConormalSheaf D.subschemeι) := by
  have hpull : IsInvertible D.subscheme.presheaf (structureIsSheaf D.subscheme.toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor D.subschemeι.toLRSHom.toShHom).obj
        (negativeTwist' D)) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of D.subschemeι.toLRSHom.toShHom
      (negativeTwist' D) (isInvertible_negativeTwist_picard D)
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (conormalSheafIsoNegativeTwist D).symm

/-- **The Picard class of the conormal sheaf of an effective Cartier divisor** is the pullback
along `D ⟶ X` of the class of `𝒪_X(-D)`: the conormal sheaf is the restriction `ℐ_D|_D` of the
ideal sheaf (Tag 0B3P), and pullback on Picard groups is computed on representatives. -/
theorem picardClass_immersionConormalSheaf [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.picardClass D.subscheme.presheaf
        (structureIsSheaf D.subscheme.toRingedSpace)
        (Stacks.Thickenings.immersionConormalSheaf D.subschemeι)
        (isInvertible_immersionConormalSheaf D) =
      Stacks.Picard.schemePullbackClass D.subschemeι (negativeTwistPicardClass D) := by
  have hN : IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) (negativeTwist' D) :=
    isInvertible_negativeTwist_picard D
  refine Eq.trans ?_ (Stacks.Picard.pullbackClass_classOf D.subschemeι.toLRSHom.toShHom
    (negativeTwist' D) hN).symm
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨conormalSheafIsoNegativeTwist D⟩

end Stacks.Divisors

end

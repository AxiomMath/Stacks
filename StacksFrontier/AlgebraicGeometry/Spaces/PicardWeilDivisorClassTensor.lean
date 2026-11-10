module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorGenericCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassCanonical

/-!
# Stacks 0EPV at the canonical choices, from a product of the chosen sections

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S` and let `ℒ`
and `𝒩` be invertible `𝒪_X`-modules.  The field `exists_ord_sub_eq_tensorModule` of
`AlgebraicGeometry.Space.PicardDivisorData` asks that the Weil divisor of the chosen regular
meromorphic section of `ℒ ⊗ 𝒩` and the sum of the Weil divisors of the chosen sections of `ℒ`
and of `𝒩` differ coefficientwise by the divisor of an invertible rational function.  This file
proves it from **one** input: a regular meromorphic section `p` of `ℒ ⊗ 𝒩` whose coefficient of
Stacks 0EPR at the generic point of every prime divisor is a *unit times* the product of the
coefficients of the chosen sections of `ℒ` and of `𝒩`.

Both discrepancies between such a `p` and the data the construction uses are absorbed here, and
they are absorbed for different reasons:

* the *generator* chosen at `ξ` for `ℒ ⊗ 𝒩` and the one built from the generators chosen for `ℒ`
  and for `𝒩` differ by a unit of `𝒪_{U, u}`, whose order of vanishing is zero — this is why the
  hypothesis asks only for the coefficient identity up to a unit, and
  `AlgebraicGeometry.Space.orderOfVanishingSection_unit_smul` is what discards it;
* the *section* `p` and the chosen regular meromorphic section of `ℒ ⊗ 𝒩` differ by an
  invertible rational function on `X`, by Stacks 0EPT in the form
  `AlgebraicGeometry.Space.exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord` —
  and that function is exactly the `f` the conclusion produces.

So nothing about the *choices* of the construction is owed, and the product section itself is
available: it is the chartwise product
`AlgebraicGeometry.Space.meromorphicSectionTensorMul` of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionTensorMultiplication.lean` amalgamated
over an affine covering
(`AlgebraicGeometry.Space.meromorphicSectionTensor`), together with the reading of its
coefficient at `ξ` against the generator chosen there
(`PrimeDivisor.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor`).
That is `AlgebraicGeometry.Space.hasCanonicalTensorProductSection` below, which closes the last
field of `AlgebraicGeometry.Space.canonicalPicardDivisorData`.

## Main definitions

* `AlgebraicGeometry.Space.HasCanonicalTensorProductSection`: for every pair of invertible
  `𝒪_X`-modules, there is a regular meromorphic section of their tensor product whose
  coefficient at the generic point of every prime divisor is a unit times the product of the
  coefficients of the chosen sections.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_tensorModule_of_exists_product`:
  **Stacks 0EPV in the form the construction of Stacks 0EPW uses**, at the canonical choices and
  from the existence of such a `p`.
* `canonicalTensorDivisorIdentity_of_exists_product`: the field
  `exists_ord_sub_eq_tensorModule` of `canonicalPicardDivisorData`, from the same input for every
  pair of invertible modules.
* `hasCanonicalTensorProductSection`: such product sections exist on a decent, locally
  Noetherian, integral algebraic space.
* `locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily`: the second set of
  Stacks 0EPS at the ratio family of Stacks 0EPR, for an arbitrary regular meromorphic section on
  a decent, locally Noetherian, integral algebraic space.
* `exists_divisorOfSection_canonicalLocalRatioFamily_picardTensorModule_eq_add`:
  **Stacks 0EPV's identity in `Div(X)`**, `div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)`, for arbitrary
  regular meromorphic sections `s` of `ℒ` and `t` of `𝒩` and for their product `st`.

In the namespace `AlgebraicGeometry.Space.PrimeDivisor`:

* `orderOfVanishingSection_canonicalLocalRatio_mul_of_genericStalkCoefficient_eq_unit_mul`:
  the order of vanishing of such a `p` along a prime divisor is the sum of the orders of
  vanishing of the chosen sections of `ℒ` and of `𝒩`.
* `orderOfVanishingSection_canonicalLocalRatio_eq_add_of_genericStalkCoefficient_eq_unit_mul`:
  the same addition of orders of vanishing for arbitrary regular meromorphic sections `s` of `ℒ`
  and `t` of `𝒩`.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hNinv : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (hInt : IsIntegralSpace B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- The generic Henselian local rings of the prime divisors are nontrivial, Noetherian and of
Krull dimension at most one. -/
private theorem genericHenselianLocalRing_instances (hInt : IsIntegralSpace B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :
    (∀ W : PrimeDivisor B S hS X, Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)) ∧
      (∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)) ∧
      ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) :=
  ⟨fun W => W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth,
    fun W => W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth,
    fun W => W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth⟩

/-- The order of vanishing of a product section, read through the canonical ratios, is the sum
of the orders of vanishing of the factors. -/
private theorem orderOfVanishingSection_canonicalLocalRatio_eq_add_aux
    (Z : PrimeDivisor B S hS X)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (p : MeromorphicSection.{u, u} B S hS X hX (picardTensorModule B S hS hX L N))
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX N t)
    (hp : IsRegularMeromorphicSection.{u, u} B S hS X hX
      (picardTensorModule B S hS hX L N) p)
    (w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec)))
    (hw : IsUnit w)
    (hcoeff : Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) p =
        algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) w *
          (Z.genericStalkCoefficient B S hS hX hdec L hL s *
            Z.genericStalkCoefficient B S hS hX hdec N hNinv t)) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    orderOfVanishingSection.{u, u} B S hS hX hdec Z (picardTensorModule B S hS hX L N) p
        (Z.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec Z L s
          (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) +
        orderOfVanishingSection.{u, u} B S hS hX hdec Z N t
          (Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth) := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances B S hS hX hdec hInt hNoeth
  have hunit : IsUnit (Z.genericStalkSectionsToHenselian B S hS hX hdec w) :=
    hw.map (Z.genericStalkSectionsToHenselian B S hS hX hdec)
  have hstep : (Z.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth p :
            Z.genericTotalFractionRing B S hS hX hdec) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (Z.genericTotalFractionRing B S hS hX hdec)
          (Z.genericStalkSectionsToHenselian B S hS hX hdec w) *
        ((fun _ : MeromorphicSection.{u, u} B S hS X hX
              (picardTensorModule B S hS hX L N) =>
            Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s *
              Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t) p :
          Z.genericTotalFractionRing B S hS hX hdec) := by
    rw [Z.coe_canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth p hp,
      Units.val_mul,
      Z.coe_canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s hs,
      Z.coe_canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t ht,
      PrimeDivisor.canonicalGenericRatio, PrimeDivisor.canonicalGenericRatio,
      PrimeDivisor.canonicalGenericRatio, hcoeff, map_mul, map_mul,
      Z.genericStalkMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hNoeth w]
  refine Eq.trans (orderOfVanishingSection_unit_smul.{u, u} B S hS hX hdec Z
    (picardTensorModule B S hS hX L N) p
    (fun _ : MeromorphicSection.{u, u} B S hS X hX
        (picardTensorModule B S hS hX L N) =>
      Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s *
        Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t)
    (Z.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
      (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth)
    hunit hstep) ?_
  exact orderOfVanishingSection_mul.{u, u} B S hS hX hdec Z L N
    (picardTensorModule B S hS hX L N) s t p
    (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth)
    (Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth)
    (fun _ : MeromorphicSection.{u, u} B S hS X hX
        (picardTensorModule B S hS hX L N) =>
      Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth s *
        Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t)
    (Units.val_mul _ _)

namespace PrimeDivisor

include hInt hNoeth in
/-- **The order of vanishing of a product section is the sum of the orders of vanishing.**  Let
`p` be a regular meromorphic section of `ℒ ⊗ 𝒩` whose coefficient of Stacks 0EPR at the generic
point `ξ` of a prime divisor is a unit of `𝒪_{U, u}` times the product of the coefficients of the
chosen sections of `ℒ` and of `𝒩`.  Then `ord_{Z, ℒ⊗𝒩}(p) = ord_{Z, ℒ}(s_ℒ) + ord_{Z, 𝒩}(s_𝒩)`. -/
theorem orderOfVanishingSection_canonicalLocalRatio_mul_of_genericStalkCoefficient_eq_unit_mul
    (Z : PrimeDivisor B S hS X)
    (p : MeromorphicSection.{u, u} B S hS X hX (picardTensorModule B S hS hX L N))
    (hp : IsRegularMeromorphicSection.{u, u} B S hS X hX
      (picardTensorModule B S hS hX L N) p)
    (w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec)))
    (hw : IsUnit w)
    (hcoeff : Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) p =
        algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) w *
          (Z.genericStalkCoefficient B S hS hX hdec L hL
              (regularMeromorphicSection B S hS hX hInt hNoeth L hL) *
            Z.genericStalkCoefficient B S hS hX hdec N hNinv
              (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv))) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    orderOfVanishingSection.{u, u} B S hS hX hdec Z (picardTensorModule B S hS hX L N) p
        (Z.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec Z L
          (regularMeromorphicSection B S hS hX hInt hNoeth L hL)
          (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) +
        orderOfVanishingSection.{u, u} B S hS hX hdec Z N
          (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)
          (Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth) := by
  exact orderOfVanishingSection_canonicalLocalRatio_eq_add_aux B S hS hX hdec L N hL hNinv hInt
    hNoeth Z _ _ p
    (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth L hL)
    (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)
    hp w hw hcoeff

end PrimeDivisor

/-- **The product section that Stacks 0EPV at the canonical choices still needs.**  For every
pair of invertible `𝒪_X`-modules a regular meromorphic section `p` of `ℒ ⊗ 𝒩` whose coefficient
of Stacks 0EPR at the generic point of every prime divisor is a unit of `𝒪_{U, u}` times the
product of the coefficients of the chosen sections of `ℒ` and of `𝒩`.

This is the whole of what the field `exists_ord_sub_eq_tensorModule` of
`AlgebraicGeometry.Space.PicardDivisorData` still owes at the canonical choices: it is turned
into that field by
`AlgebraicGeometry.Space.canonicalTensorDivisorIdentity_of_exists_product`, and
`AlgebraicGeometry.Space.canonicalPicardDivisorData` then needs nothing beyond
`AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart`.

The unit is there because the generator chosen at `ξ` for `ℒ ⊗ 𝒩` and the product of the
generators chosen for `ℒ` and for `𝒩` are two free generators of one invertible module, so they
differ by a unit (`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_smul_genericStalkGenerator`);
asking for the identity on the nose would be asking the choices of
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkTrivialisation` to be made compatibly, which
they are not. -/
def HasCanonicalTensorProductSection : Prop :=
  ∀ (P Q : Modules.{u, u} B S hS X hX) (hP : IsInvertibleModule (B := B) ⟨X, hX⟩ P)
    (hQ : IsInvertibleModule (B := B) ⟨X, hX⟩ Q),
    ∃ p : MeromorphicSection.{u, u} B S hS X hX (picardTensorModule B S hS hX P Q),
      IsRegularMeromorphicSection.{u, u} B S hS X hX
          (picardTensorModule B S hS hX P Q) p ∧
        ∀ W : PrimeDivisor B S hS X,
          ∃ w : (structurePresheaf B S hS (W.genericStalkSpace B S hS hX hdec).1).obj
            (op (W.genericStalkChart B S hS hX hdec)),
            IsUnit w ∧
              W.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX P Q)
                  (isInvertibleModule_picardTensorModule B S hS hX P Q hP hQ) p =
                algebraMap ((structurePresheaf B S hS
                      (W.genericStalkSpace B S hS hX hdec).1).obj
                    (op (W.genericStalkChart B S hS hX hdec)))
                  ((meromorphicFunctionSheaf B S hS (W.genericStalkSpace B S hS hX hdec).1
                    (W.genericStalkSpace B S hS hX hdec).2).obj.obj
                      (op (W.genericStalkChart B S hS hX hdec))) w *
                  (W.genericStalkCoefficient B S hS hX hdec P hP
                      (regularMeromorphicSection B S hS hX hInt hNoeth P hP) *
                    W.genericStalkCoefficient B S hS hX hdec Q hQ
                      (regularMeromorphicSection B S hS hX hInt hNoeth Q hQ))

include hInt hNoeth in
/-- **Stacks 0EPV in the form the construction of Stacks 0EPW uses, at the canonical choices and
from a product of the chosen sections.**  Given a regular meromorphic section `p` of `ℒ ⊗ 𝒩`
whose coefficient of Stacks 0EPR at the generic point of every prime divisor is a unit times the
product of the coefficients of the chosen sections of `ℒ` and of `𝒩`, the Weil divisor of the
chosen regular meromorphic section of `ℒ ⊗ 𝒩` and the sum of the Weil divisors of the chosen
sections of `ℒ` and of `𝒩` differ coefficientwise by the divisor of an invertible rational
function on `X`.

The orders of vanishing of `p` already add
(`orderOfVanishingSection_canonicalLocalRatio_mul_of_genericStalkCoefficient_eq_unit_mul`),
and `p` and the chosen regular meromorphic section of `ℒ ⊗ 𝒩` are two regular meromorphic
sections of one invertible module, so Stacks 0EPT in the form
`AlgebraicGeometry.Space.exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord`
produces the rational function. -/
theorem
    exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_tensorModule_of_exists_product
    (hprod : ∃ p : MeromorphicSection.{u, u} B S hS X hX
        (picardTensorModule B S hS hX L N),
      IsRegularMeromorphicSection.{u, u} B S hS X hX
          (picardTensorModule B S hS hX L N) p ∧
        ∀ W : PrimeDivisor B S hS X,
          ∃ w : (structurePresheaf B S hS (W.genericStalkSpace B S hS hX hdec).1).obj
            (op (W.genericStalkChart B S hS hX hdec)),
            IsUnit w ∧
              W.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
                  (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) p =
                algebraMap ((structurePresheaf B S hS
                      (W.genericStalkSpace B S hS hX hdec).1).obj
                    (op (W.genericStalkChart B S hS hX hdec)))
                  ((meromorphicFunctionSheaf B S hS (W.genericStalkSpace B S hS hX hdec).1
                    (W.genericStalkSpace B S hS hX hdec).2).obj.obj
                      (op (W.genericStalkChart B S hS hX hdec))) w *
                  (W.genericStalkCoefficient B S hS hX hdec L hL
                      (regularMeromorphicSection B S hS hX hInt hNoeth L hL) *
                    W.genericStalkCoefficient B S hS hX hdec N hNinv
                      (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv))) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, u} B S hS hX hdec (picardTensorModule B S hS hX L N)
            (regularMeromorphicSection B S hS hX hInt hNoeth _
              (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv))
            (canonicalLocalRatioFamily B S hS hX hdec _
              (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth) W -
          (divisorCoefficients.{u, u} B S hS hX hdec L
              (regularMeromorphicSection B S hS hX hInt hNoeth L hL)
              (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hNoeth) W +
            divisorCoefficients.{u, u} B S hS hX hdec N
              (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)
              (canonicalLocalRatioFamily B S hS hX hdec N hNinv hInt hNoeth) W) =
        (genericFractionEmbedding B S hS hX hdec hInt hNoeth).ord f W := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances B S hS hX hdec hInt hNoeth
  obtain ⟨p, hp, hcoeff⟩ := hprod
  obtain ⟨f, hf⟩ := exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord B S hS hX
    hdec hInt hNoeth (picardTensorModule B S hS hX L N)
    (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
    (regularMeromorphicSection B S hS hX hInt hNoeth _
      (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)) p
    (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth _
      (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)) hp
  refine ⟨f, fun W => ?_⟩
  obtain ⟨w, hw, hwc⟩ := hcoeff W
  have hsum : orderOfVanishingSection.{u, u} B S hS hX hdec W
        (picardTensorModule B S hS hX L N) p
        (W.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec W L
          (regularMeromorphicSection B S hS hX hInt hNoeth L hL)
          (W.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) +
        orderOfVanishingSection.{u, u} B S hS hX hdec W N
          (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)
          (W.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth) :=
    W.orderOfVanishingSection_canonicalLocalRatio_mul_of_genericStalkCoefficient_eq_unit_mul
      B S hS hX hdec L N hL hNinv hInt hNoeth p hp w hw hwc
  have hfW : orderOfVanishingSection.{u, u} B S hS hX hdec W
          (picardTensorModule B S hS hX L N)
          (regularMeromorphicSection B S hS hX hInt hNoeth _
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv))
          (W.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec W
            (picardTensorModule B S hS hX L N) p
            (W.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
              (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth) +
          (genericFractionEmbedding B S hS hX hdec hInt hNoeth).ord f W := hf W
  simp only [divisorCoefficients, canonicalLocalRatioFamily]
  omega

include hInt hNoeth in
/-- **The field `exists_ord_sub_eq_tensorModule` of the canonical data, from the product
sections.**  This is
`exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_tensorModule_of_exists_product`
read at every pair of invertible `𝒪_X`-modules at once, which is exactly
`AlgebraicGeometry.Space.CanonicalTensorDivisorIdentity`; with it and
`AlgebraicGeometry.Space.CanonicalRatioIsUnitOnGeneratingChart` the data
`AlgebraicGeometry.Space.canonicalPicardDivisorData` of Stacks 0EPW is complete. -/
theorem canonicalTensorDivisorIdentity_of_exists_product
    (hprod : HasCanonicalTensorProductSection B S hS hX hdec hInt hNoeth) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    CanonicalTensorDivisorIdentity B S hS hX hdec hInt hNoeth := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances B S hS hX hdec hInt hNoeth
  exact fun P Q hP hQ =>
    exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_tensorModule_of_exists_product
      B S hS hX hdec P Q hP hQ hInt hNoeth (hprod P Q hP hQ)

include hInt hNoeth in
/-- **The product sections of Stacks 0EPV at the canonical choices exist**, on a decent, locally
Noetherian, integral algebraic space — with no hypothesis.  This is the named `Prop`
`AlgebraicGeometry.Space.HasCanonicalTensorProductSection`, the last thing the data
`AlgebraicGeometry.Space.canonicalPicardDivisorData` of Stacks 0EPW still owed.

The section is the global product `s_ℒ ⊗ s_𝒩` of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionTensorGlobal.lean`; it is regular by
`AlgebraicGeometry.Space.isRegularMeromorphicSection_meromorphicSectionTensor` and its coefficient
of Stacks 0EPR at the generic point of a prime divisor is a unit times the product of the
coefficients by
`PrimeDivisor.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor`.

The two hypotheses (a) and (b) of Stacks 0EN6 that the construction of the product needs are
`X`'s own: (a) holds because an integral algebraic space is reduced, and (b) because a locally
Noetherian one has locally finite irreducible components. -/
theorem hasCanonicalTensorProductSection :
    HasCanonicalTensorProductSection B S hS hX hdec hInt hNoeth := by
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hNoeth
  intro P Q hP hQ
  exact ⟨meromorphicSectionTensor B S hS hX hwa hfin P Q
      (regularMeromorphicSection B S hS hX hInt hNoeth P hP)
      (regularMeromorphicSection B S hS hX hInt hNoeth Q hQ)
      (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) P hP)
      (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) Q hQ),
    isRegularMeromorphicSection_meromorphicSectionTensor B S hS hX hwa hfin P Q
      (regularMeromorphicSection B S hS hX hInt hNoeth P hP)
      (regularMeromorphicSection B S hS hX hInt hNoeth Q hQ)
      (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) P hP)
      (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) Q hQ)
      hP hQ
      (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth P hP)
      (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth Q hQ),
    fun W => W.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor B S hS hX hdec
      hInt hNoeth hwa hfin P Q hP hQ
      (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) P hP)
      (isQuasicoherentOnSite_of_isInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) Q hQ)
      (regularMeromorphicSection B S hS hX hInt hNoeth P hP)
      (regularMeromorphicSection B S hS hX hInt hNoeth Q hQ)
      (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth P hP)
      (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth Q hQ)⟩

/-! ### Stacks 0EPV in `Div(X)`, at arbitrary regular meromorphic sections -/

namespace PrimeDivisor

include hInt hNoeth in
/-- **The order of vanishing of a product section is the sum of the orders of vanishing, at
arbitrary regular meromorphic sections.**  Let `s` be a regular meromorphic section of `ℒ`, let
`t` be one of `𝒩`, and let `p` be one of `ℒ ⊗ 𝒩` whose coefficient of Stacks 0EPR at the generic
point `ξ` of a prime divisor is a unit of `𝒪_{U, u}` times the product of the coefficients of
`s` and of `t`.  Then `ord_{Z, ℒ⊗𝒩}(p) = ord_{Z, ℒ}(s) + ord_{Z, 𝒩}(t)`.

`orderOfVanishingSection_canonicalLocalRatio_mul_of_genericStalkCoefficient_eq_unit_mul`
is this at the two sections the construction chooses, which is all that the field
`exists_ord_sub_eq_tensorModule` of `AlgebraicGeometry.Space.PicardDivisorData` needs; the
source of Stacks 0EPV quantifies over `s` and `t`, so the identity in `Div(X)` below needs this
form.  The proof is the same: the unit drops out, its image in `𝒪^h_{X, ξ}` being a unit there
and the order of vanishing read through two ratios differing by such a unit being the same
(`AlgebraicGeometry.Space.orderOfVanishingSection_unit_smul`), and what is left is the order of
vanishing read through the *product* of the two ratios, which is the sum of the two orders
(`AlgebraicGeometry.Space.orderOfVanishingSection_mul`). -/
theorem orderOfVanishingSection_canonicalLocalRatio_eq_add_of_genericStalkCoefficient_eq_unit_mul
    (Z : PrimeDivisor B S hS X)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (p : MeromorphicSection.{u, u} B S hS X hX (picardTensorModule B S hS hX L N))
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX N t)
    (hp : IsRegularMeromorphicSection.{u, u} B S hS X hX
      (picardTensorModule B S hS hX L N) p)
    (w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec)))
    (hw : IsUnit w)
    (hcoeff : Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) p =
        algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) w *
          (Z.genericStalkCoefficient B S hS hX hdec L hL s *
            Z.genericStalkCoefficient B S hS hX hdec N hNinv t)) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    orderOfVanishingSection.{u, u} B S hS hX hdec Z (picardTensorModule B S hS hX L N) p
        (Z.canonicalLocalRatio B S hS hX hdec (picardTensorModule B S hS hX L N)
          (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec Z L s
          (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) +
        orderOfVanishingSection.{u, u} B S hS hX hdec Z N t
          (Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth) := by
  exact orderOfVanishingSection_canonicalLocalRatio_eq_add_aux B S hS hX hdec L N hL hNinv hInt
    hNoeth Z s t p hs ht hp w hw hcoeff

end PrimeDivisor

include hInt hNoeth in
/-- **The second set of Stacks 0EPS at the ratio family of Stacks 0EPR, for an arbitrary regular
meromorphic section.**  On a decent, locally Noetherian, integral algebraic space the prime
divisors at which `ord_{Z, ℳ}(s)` is nonzero are locally finite in `|X|`, for every invertible
`𝒪_X`-module `ℳ` and every regular meromorphic section `s` of it, the order of vanishing being
read through the canonical ratio `s / s_ξ`.  Nothing is assumed beyond `X` itself.

This is what makes `div_ℳ(s)` an element of `Div(X)` at the canonical ratio family.  It is
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero` at the generating locus of
`s`, which is open and nonempty
(`AlgebraicGeometry.Space.isOpen_generatingLocus`,
`AlgebraicGeometry.Space.nonempty_generatingLocus_of_isRegularMeromorphicSection`); at the
generic point of a prime divisor lying in a chart over which `s` generates `ℳ` the coefficient
of Stacks 0EPR is a unit
(`PrimeDivisor.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_generatesOnChart`),
and the order of vanishing at a unit coefficient is zero
(`AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_coefficient`).

`AlgebraicGeometry.Space.exists_isOpen_nonempty_genericPoint_mem_compl_of_isUnit` together with
`AlgebraicGeometry.Space.canonicalRatioIsUnitOnGeneratingChart` is the same statement at the
section `AlgebraicGeometry.Space.regularMeromorphicSection` that the construction of Stacks
0EPW chooses, which is the form the field `generating` of
`AlgebraicGeometry.Space.PicardDivisorData` takes. -/
theorem locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily
    (M : Modules.{u, u} B S hS X hX) (hM : IsInvertibleModule (B := B) ⟨X, hX⟩ M)
    (s : MeromorphicSection.{u, u} B S hS X hX M)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX M s) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    LocallyFinite fun W : PrimeDivisor B S hS X =>
      if divisorCoefficients.{u, u} B S hS hX hdec M s
          (canonicalLocalRatioFamily B S hS hX hdec M hM hInt hNoeth) W = 0 then ∅
      else W.support B S hS X := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances B S hS hX hdec hInt hNoeth
  refine locallyFinite_divisorCoefficients_ne_zero.{u, u} B S hS hX hdec hNoeth
    hInt.irreducibleSpace M s (canonicalLocalRatioFamily B S hS hX hdec M hM hInt hNoeth)
    (generatingLocus B S hS hX M s) (isOpen_generatingLocus B S hS hX M s)
    (nonempty_generatingLocus_of_isRegularMeromorphicSection B S hS hX M
      hInt.hasEtaleLocalProperty_isReduced hInt.irreducibleSpace.toNonempty hM s hs)
    fun W hW => ?_
  by_contra hmem
  obtain ⟨V, hrange, hgen⟩ := not_not.1 hmem
  obtain ⟨w, hw, hwc⟩ :=
    W.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_generatesOnChart B S hS hX hdec
      hInt hNoeth M hM s V hrange hgen
  exact hW (orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_coefficient B S hS hX hdec
    hInt hNoeth W M hM s hs hw hwc)

include hInt hNoeth in
/-- **Stacks 0EPV's identity in `Div(X)`.**  Let `X` be a decent, locally Noetherian, integral
algebraic space over `S`, let `ℒ` and `𝒩` be invertible `𝒪_X`-modules, let `s` be a regular
meromorphic section of `ℒ` and let `t` be one of `𝒩`.  Then there is a regular meromorphic
section `st` of `ℒ ⊗ 𝒩` which is the product of `s` and of `t` — its coefficient of Stacks 0EPR
at the generic point of every prime divisor is the product of the coefficients of `s` and of
`t`, up to a unit of `𝒪_{U, u}` — and the Weil divisors read through the ratio families of
Stacks 0EPR satisfy

`div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)`

as an identity of elements of `Div(X)`, on the nose and not merely up to the divisor of a
rational function.  Nothing is assumed beyond `X` itself.

This is the source's statement: the existence of the product section is its first clause and is
asserted here too, the identity in `Div(X)` its second, and `s` and `t` range over all regular
meromorphic sections as they do there.  The unit in the product clause is unavoidable and is
harmless: the generator chosen at `ξ` for `ℒ ⊗ 𝒩` and the product of the generators chosen for
`ℒ` and for `𝒩` are two free generators of one invertible module, so they differ by a unit
(`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_smul_genericStalkGenerator`) whose order of
vanishing is zero — the source's own computation `st/(s_ξ t_ξ) = (s/s_ξ)(t/t_ξ)` holds up to
exactly that unit, and it is discarded by
`orderOfVanishingSection_canonicalLocalRatio_eq_add_of_genericStalkCoefficient_eq_unit_mul`.

The product section is the chartwise product
`AlgebraicGeometry.Space.meromorphicSectionTensorMul` amalgamated over an affine covering,
`AlgebraicGeometry.Space.meromorphicSectionTensor`, and the local finiteness that makes each of
the three divisors an element of `Div(X)` is
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily`.

`AlgebraicGeometry.Space.PicardDivisorData.divisor_picardTensorModule` is the same identity for
the sections and ratio families that an arbitrary
`AlgebraicGeometry.Space.PicardDivisorData` chooses, where the chosen section of `ℒ ⊗ 𝒩` has no
relation to the chosen sections of `ℒ` and of `𝒩` and the ratio identity has to be supplied; at
the canonical choices and for the product section, as here, it is proved. -/
@[stacks 0EPV "the identity div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t) in Div(X), read through the
  ratio families of Stacks 0EPR, for arbitrary regular meromorphic sections s of ℒ and t of 𝒩
  and for their product st, whose existence is the source's first clause and is asserted here
  too; nothing is assumed beyond X being decent, locally Noetherian and integral. The source's
  computation st/(s_ξ t_ξ) = (s/s_ξ)(t/t_ξ) holds up to a unit of 𝒪_{U,u}, the discrepancy
  between the generator chosen at ξ for ℒ⊗𝒩 and the product of those chosen for ℒ and for 𝒩,
  and that unit has order of vanishing zero. The whole lemma for nonzero sections, with the
  in-particular clause in the canonical Cl(X), is
  exists_ne_zero_weilDivisorOfSection_meromorphicSectionTensor_eq_add"]
theorem exists_divisorOfSection_canonicalLocalRatioFamily_picardTensorModule_eq_add
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX N t) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    ∃ (st : MeromorphicSection.{u, u} B S hS X hX (picardTensorModule B S hS hX L N))
      (_ : IsRegularMeromorphicSection.{u, u} B S hS X hX
        (picardTensorModule B S hS hX L N) st),
      (∀ W : PrimeDivisor B S hS X,
          ∃ w : (structurePresheaf B S hS (W.genericStalkSpace B S hS hX hdec).1).obj
            (op (W.genericStalkChart B S hS hX hdec)),
            IsUnit w ∧
              W.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
                  (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) st =
                algebraMap ((structurePresheaf B S hS
                      (W.genericStalkSpace B S hS hX hdec).1).obj
                    (op (W.genericStalkChart B S hS hX hdec)))
                  ((meromorphicFunctionSheaf B S hS (W.genericStalkSpace B S hS hX hdec).1
                    (W.genericStalkSpace B S hS hX hdec).2).obj.obj
                      (op (W.genericStalkChart B S hS hX hdec))) w *
                  (W.genericStalkCoefficient B S hS hX hdec L hL s *
                    W.genericStalkCoefficient B S hS hX hdec N hNinv t)) ∧
        ∃ (hfinst : LocallyFinite fun W : PrimeDivisor B S hS X =>
              if divisorCoefficients.{u, u} B S hS hX hdec
                  (picardTensorModule B S hS hX L N) st
                  (canonicalLocalRatioFamily B S hS hX hdec
                    (picardTensorModule B S hS hX L N)
                    (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
                    hInt hNoeth) W = 0 then ∅
              else W.support B S hS X)
          (hfins : LocallyFinite fun W : PrimeDivisor B S hS X =>
              if divisorCoefficients.{u, u} B S hS hX hdec L s
                  (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hNoeth) W = 0 then ∅
              else W.support B S hS X)
          (hfint : LocallyFinite fun W : PrimeDivisor B S hS X =>
              if divisorCoefficients.{u, u} B S hS hX hdec N t
                  (canonicalLocalRatioFamily B S hS hX hdec N hNinv hInt hNoeth) W = 0 then ∅
              else W.support B S hS X),
          divisorOfSection.{u, u} B S hS hX hdec (picardTensorModule B S hS hX L N) st
                (canonicalLocalRatioFamily B S hS hX hdec (picardTensorModule B S hS hX L N)
                  (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) hInt hNoeth)
                hfinst =
            divisorOfSection.{u, u} B S hS hX hdec L s
                (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hNoeth) hfins +
              divisorOfSection.{u, u} B S hS hX hdec N t
                (canonicalLocalRatioFamily B S hS hX hdec N hNinv hInt hNoeth) hfint := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances B S hS hX hdec hInt hNoeth
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz
  have hcomp := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hNoeth
  have hLqc := isQuasicoherentOnSite_of_isInvertibleModule
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) L hL
  have hNqc := isQuasicoherentOnSite_of_isInvertibleModule
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) N hNinv
  have hstreg := isRegularMeromorphicSection_meromorphicSectionTensor B S hS hX hwa hcomp L N
    s t hLqc hNqc hL hNinv hs ht
  refine ⟨meromorphicSectionTensor B S hS hX hwa hcomp L N s t hLqc hNqc, hstreg,
    fun W => W.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor B S hS hX hdec
      hInt hNoeth hwa hcomp L N hL hNinv hLqc hNqc s t hs ht,
    locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily B S hS hX hdec hInt
      hNoeth (picardTensorModule B S hS hX L N)
      (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv) _ hstreg,
    locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily B S hS hX hdec hInt
      hNoeth L hL s hs,
    locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily B S hS hX hdec hInt
      hNoeth N hNinv t ht, ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  obtain ⟨w, hw, hwc⟩ := Z.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor
    B S hS hX hdec hInt hNoeth hwa hcomp L N hL hNinv hLqc hNqc s t hs ht
  exact Z.orderOfVanishingSection_canonicalLocalRatio_eq_add_of_genericStalkCoefficient_eq_unit_mul
    B S hS hX hdec L N hL hNinv hInt hNoeth s t _ hs ht hstreg w hw hwc

end AlgebraicGeometry.Space

end

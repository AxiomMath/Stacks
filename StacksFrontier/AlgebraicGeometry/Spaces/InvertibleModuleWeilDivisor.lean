module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassTensor

/-!
# The Weil divisor of a nonzero meromorphic section of an invertible module

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let `ℒ` be an
invertible `𝒪_X`-module. For a nonzero meromorphic section `s` of `ℒ` the *Weil divisor
associated to `s`* is

`div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z] ∈ Div(X)`,

the sum over the prime divisors of `X`, which is part (1) of Stacks 0EPU. This file defines it
with no data beyond `X`, `ℒ` and `s`: the order of vanishing is read through the canonical ratio
`s / s_ξ` of Stacks 0EPR, and the local finiteness that makes the sum a Weil divisor is Stacks
0EPS, proved and not assumed.

## Main definitions

* `AlgebraicGeometry.Space.weilDivisorOfSection` is **Stacks 0EPU, part (1)**: `div_ℒ(s)`.

## Main results

* `AlgebraicGeometry.Space.exists_meromorphicSection_ne_zero`: an invertible module on a locally
  Noetherian integral algebraic space has a nonzero meromorphic section.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_of_ne_zero`: on a locally Noetherian
  integral algebraic space a nonzero meromorphic section of an invertible module is regular,
  the identification "regular (i.e., nonzero)" that the source makes in Stacks 0EPS.
* `AlgebraicGeometry.Space.locallyFinite_ord_ne_zero_of_ne_zero`: the second set of Stacks 0EPS
  for a nonzero meromorphic section — the prime divisors with `ord_{Z,ℒ}(s) ≠ 0` are locally
  finite.
* `AlgebraicGeometry.Space.coe_weilDivisorOfSection`: the coefficient of `div_ℒ(s)` at a prime
  divisor `Z` is `ord_{Z,ℒ}(s)`.

## Implementation notes

Decency of `X`, which the order of vanishing is stated under, is part of integrality
(`AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace`) and is not a separate argument. The
three ring-theoretic properties of `𝒪^h_{X,ξ}` that the order of vanishing needs are the
conclusions of Stacks 0ENK, supplied inside the definitions.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-! ### Nonzero meromorphic sections are regular -/

include hInt hN in
/-- On a locally Noetherian integral algebraic space the ring `Γ(X, 𝒦_X)` of global meromorphic
functions is a field: it is the function field `R(X)` by the third conclusion of Stacks 0ENA. -/
theorem isField_globalMeromorphicFunctions :
    IsField (↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) := by
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  have hmono := IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
    ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩
  obtain ⟨eR, -⟩ := exists_ringEquiv_rationalFunctions_meromorphicFunction
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) hwa hfin hmono
  exact MulEquiv.isField (isField_rationalFunctions B S hS hX hInt) eR.symm.toMulEquiv

include hInt hN in
/-- **A regular meromorphic section is nonzero** on a locally Noetherian integral algebraic
space: multiplication by the zero section kills `1`, and `Γ(X, 𝒦_X)` is a field, so nontrivial. -/
theorem ne_zero_of_isRegularMeromorphicSection (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) : s ≠ 0 := by
  intro h0
  have h1 : (1 : ↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) =
        0 := by
    refine Subtype.ext (funext fun W => hs W.unop ?_)
    show (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj W) • s.eval W =
      (0 : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj W) • s.eval W
    rw [h0]
    simp
  obtain ⟨p, q, hpq⟩ := (isField_globalMeromorphicFunctions B S hS hX hInt hN).exists_pair_ne
  exact hpq (by rw [← one_mul p, ← one_mul q, h1, zero_mul, zero_mul])

include hInt hN in
/-- **An invertible module on a locally Noetherian integral algebraic space has a nonzero
meromorphic section**, that is `Γ(X, 𝒦_X(ℒ)) ≠ 0`: the regular meromorphic section of Stacks
0EPQ is one. -/
theorem exists_meromorphicSection_ne_zero (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    ∃ s : MeromorphicSection.{u, u} B S hS X hX L, s ≠ 0 :=
  ⟨regularMeromorphicSection B S hS hX hInt hN L hL,
    ne_zero_of_isRegularMeromorphicSection B S hS hX hInt hN L _
      (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hN L hL)⟩

include hInt hN in
/-- **A nonzero meromorphic section of an invertible module on a locally Noetherian integral
algebraic space is regular.** This is the identification "regular (i.e., nonzero)" of Stacks
0EPS.

The trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks 0EPQ writes `s` and a regular meromorphic section
`s₀` (Stacks 0EPQ) as `a · t` and `b · t` for global meromorphic functions `a`, `b`; both are
nonzero, hence units of the field `Γ(X, 𝒦_X) = R(X)`, so `s = (a b⁻¹) · s₀` with `a b⁻¹` a unit,
and multiplication by `s` is multiplication by the regular `s₀` after an invertible factor. -/
theorem isRegularMeromorphicSection_of_ne_zero
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (hs : s ≠ 0) :
    IsRegularMeromorphicSection.{u, u} B S hS X hX L s := by
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  have hmono := IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
    ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩
  obtain ⟨e⟩ := nonempty_iso_meromorphicUnitModule_of_isTrivialAtCodimensionZeroPoints B S hS hX
    hwa hfin hmono L hL
  let := (isField_globalMeromorphicFunctions B S hS hX hInt hN).toField
  have hlin : ∀ (a : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))
      (x : (meromorphicUnitModule B S hS X hX).sections),
      SheafOfModules.sectionsMap e.hom (a • x) = a • SheafOfModules.sectionsMap e.hom x :=
    fun a x => ((Stacks.Cohomology.SiteModules.globalSectionsFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O)).map e.hom).hom.map_smul a x
  have hround : ∀ x : MeromorphicSection.{u, u} B S hS X hX L,
      SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap e.inv x) = x := fun x =>
    Subtype.ext (funext fun V =>
      congrArg (fun φ : meromorphicSectionSheaf.{u, u} B S hS X hX L ⟶
          meromorphicSectionSheaf.{u, u} B S hS X hX L =>
        PresheafOfModules.Hom.app φ.val V (x.eval V)) e.inv_hom_id)
  set s₀ := regularMeromorphicSection B S hS hX hInt hN L hL
  have hs₀ : IsRegularMeromorphicSection.{u, u} B S hS X hX L s₀ :=
    isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hN L hL
  have hrep : ∀ t : MeromorphicSection.{u, u} B S hS X hX L,
      ∃ a : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)),
        t = a • SheafOfModules.sectionsMap e.hom (meromorphicUnitSection B S hS X hX) := fun t => by
    obtain ⟨a, ha, -⟩ := existsUnique_smul_meromorphicUnitSection B S hS hX
      (SheafOfModules.sectionsMap e.inv t)
    exact ⟨a, by rw [← hlin, ha, hround]⟩
  obtain ⟨a, hsa⟩ := hrep s
  obtain ⟨b, hsb⟩ := hrep s₀
  have hb0 : b ≠ 0 := fun h =>
    ne_zero_of_isRegularMeromorphicSection B S hS hX hInt hN L s₀ hs₀
      (by rw [hsb, h, zero_smul])
  have ha0 : a ≠ 0 := fun h => hs (by rw [hsa, h, zero_smul])
  obtain ⟨ua, hua⟩ := ha0.isUnit
  obtain ⟨ub, hub⟩ := hb0.isUnit
  set c := ua * ub⁻¹
  have hsc : s = (c : ↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) •
        s₀ := by
    rw [hsa, hsb, ← hua, ← hub, smul_smul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  intro V r r' hrr
  have hcV : ∀ x : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj (op V),
      x * (c : ↥(RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj))).1 (op V) *
        ((c⁻¹ : (↥(RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj)))ˣ) : ↥(RingCat.sectionsSubring
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (meromorphicRingedSite B S hS X hX).O).obj))).1 (op V) = x := by
    intro x
    rw [mul_assoc]
    have := congrFun (congrArg Subtype.val c.mul_inv) (op V)
    exact (congrArg (x * ·) this).trans (mul_one x)
  have hev : ∀ x : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj (op V),
      x • s.eval (op V) = (x * (c : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj))).1 (op V)) • s₀.eval (op V) := by
    intro x
    rw [hsc, mul_smul]
    rfl
  have key := hs₀ V ((hev r).symm.trans (hrr.trans (hev r')))
  rw [← hcV r, ← hcV r']
  exact congrArg (· * _) key

/-! ### The Weil divisor `div_ℒ(s)` -/

include hInt hN in
/-- **The second set of Stacks 0EPS, for a nonzero meromorphic section.** On a locally
Noetherian integral algebraic space the prime divisors `Z` with `ord_{Z,ℒ}(s) ≠ 0` are locally
finite in `|X|`, for every invertible `𝒪_X`-module `ℒ` and every nonzero meromorphic section `s`
of `ℒ`, the order of vanishing being that of Stacks 0EPR at the canonical ratio `s / s_ξ`.

This is
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily`
at the regular section `s`, regularity being
`AlgebraicGeometry.Space.isRegularMeromorphicSection_of_ne_zero`. -/
theorem locallyFinite_ord_ne_zero_of_ne_zero
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (hs : s ≠ 0) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
    LocallyFinite fun W : PrimeDivisor B S hS X =>
      if divisorCoefficients.{u, u} B S hS hX hInt.isDecentSpace L s
          (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN) W = 0 then ∅
      else W.support B S hS X :=
  locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily B S hS hX
    hInt.isDecentSpace hInt hN L hL s
    (isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN L hL s hs)

/-- **Stacks 0EPU, part (1).** The *Weil divisor associated to a nonzero meromorphic section*
`s` of an invertible `𝒪_X`-module `ℒ` on a locally Noetherian integral algebraic space:

`div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z] ∈ Div(X)`,

the sum over the prime divisors of `X`. The coefficient `ord_{Z,ℒ}(s)` is the order of vanishing
of Stacks 0EPR at the canonical ratio `s / s_ξ`
(`AlgebraicGeometry.Space.canonicalLocalRatioFamily`), and the sum is a Weil divisor by Stacks
0EPS, which is `AlgebraicGeometry.Space.locallyFinite_ord_ne_zero_of_ne_zero`. Nothing beyond
`X`, `ℒ` and `s` enters. -/
@[stacks 0EPU "part (1): div_ℒ(s) = ∑ ord_{Z,ℒ}(s)[Z] ∈ Div(X) for a nonzero meromorphic section \
s of an invertible module, at the canonical ratio s/s_ξ of Stacks 0EPR, with the local finiteness \
of Stacks 0EPS proved"]
def weilDivisorOfSection
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (hs : s ≠ 0) : ↥(WeilDivisor B S hS X) :=
  haveI : ∀ W : PrimeDivisor B S hS X,
      Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
    W.nontrivial_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
  haveI : ∀ W : PrimeDivisor B S hS X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
  haveI : ∀ W : PrimeDivisor B S hS X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
    W.krullDimLE_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
  divisorOfSection.{u, u} B S hS hX hInt.isDecentSpace L s
    (canonicalLocalRatioFamily B S hS hX hInt.isDecentSpace L hL hInt hN)
    (locallyFinite_ord_ne_zero_of_ne_zero B S hS hX hInt hN L hL s hs)

/-- The coefficient of `div_ℒ(s)` at a prime divisor `Z` is `ord_{Z,ℒ}(s)`, the order of
vanishing of Stacks 0EPR at the canonical ratio `s / s_ξ`. -/
theorem coe_weilDivisorOfSection
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s : MeromorphicSection.{u, u} B S hS X hX L) (hs : s ≠ 0) (Z : PrimeDivisor B S hS X) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hInt.isDecentSpace) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hInt.isDecentSpace hInt hN
    (weilDivisorOfSection B S hS hX hInt hN L hL s hs : PrimeDivisor B S hS X → ℤ) Z =
      orderOfVanishingSection.{u, u} B S hS hX hInt.isDecentSpace Z L s
        (Z.canonicalLocalRatio B S hS hX hInt.isDecentSpace L hL hInt hN) :=
  rfl

end AlgebraicGeometry.Space

end

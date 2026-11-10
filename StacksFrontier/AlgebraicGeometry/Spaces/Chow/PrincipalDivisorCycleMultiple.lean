module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums

/-!
# Integer multiples of principal divisors

In Situation 0EDT let `W/B` be good.  A `k`-cycle on `W` is a *principal divisor* when it is
`div(f)` for a unit `f` of the ring of rational functions, read through a family of embeddings
`R(W) → Q(𝒪^h_{W,ξ})` as in Stacks 0ENK; that is
`AlgebraicGeometry.Space.IsPrincipalDivisorCycle`.  **An integer multiple of a principal divisor
is a principal divisor**, because `a · div(f) = div(f^a)`, and that is what this file proves.

It is needed wherever a cycle identity of the chapter produces a principal divisor *with a
multiplicity*.  The case at hand is the passage from Stacks 0EQA to the rational equivalence
which Stacks 0EQB uses: Stacks 0EQA states

`f^* div_Y(g) = ∑ m_{X', X} (X' → X)_* div_{X'}(g ∘ f|_{X'})`

over the irreducible components `X'` of `X`, and the summand on `X'` is the multiplicity
`m_{X', X}` times a principal divisor, not a principal divisor.  Part (2) of Stacks 0EQ6 asks
for principal divisors, so the multiplicities have to be absorbed, which
`AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul` does.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.ord_zpow_of_ringHom`: `ord_Z(f^a) = a · ord_Z(f)` for a
  unit `f` of the ring of rational functions read through an arbitrary ring homomorphism into
  the total fraction ring at the generic point of `Z`.
* `AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul`: an integer multiple of a principal
  divisor cycle is a principal divisor cycle.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_cycleFamilySum_zsmul`: a locally
  finite sum `∑ a_l (U_l → X)_* div_l` of integer multiples of pushed-forward principal
  divisors, over integral closed subspaces of δ-dimension `k + 1` lying in a subset `T`, is
  rationally equivalent to zero within `T`.

## Implementation notes

`AlgebraicGeometry.Space.GenericFractionEmbedding.ord_zpow` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection` is this computation for the
*canonical* embedding family of Stacks 0ENK, as a family indexed by all prime divisors at once.
`AlgebraicGeometry.Space.IsPrincipalDivisorCycle` quantifies over an arbitrary embedding family,
so the computation is redone here at one prime divisor and one ring homomorphism; the argument is
the same, the order of vanishing being a monoid homomorphism from the units of the ring of
rational functions to `Multiplicative ℤ`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The order of vanishing of an integer power -/

section OrdZpow

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hdec : IsDecentSpace B S hS Y) (Z : PrimeDivisor B S hS Y)
    [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hY hdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hY hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hY hdec)]

/-- The order of vanishing along a prime divisor, as a monoid homomorphism from the units of the
ring of rational functions to `Multiplicative ℤ`: it is zero at `1` and additive, by
`AlgebraicGeometry.Space.PrimeDivisor.ord_one` and
`AlgebraicGeometry.Space.PrimeDivisor.ord_mul`. -/
def PrimeDivisor.ordUnitsHom
    (emb : rationalFunctions B S hS hY →+* Z.genericTotalFractionRing B S hS hY hdec) :
    (rationalFunctions B S hS hY)ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd
    (Z.ord B S hS hY hdec (emb (u : rationalFunctions B S hS hY)) (u.isUnit.map emb))
  map_one' := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd (0 : ℤ)
    refine congrArg Multiplicative.ofAdd ?_
    rw [PrimeDivisor.ord_congr B S hS hY hdec Z _ isUnit_one
      (by rw [Units.val_one, map_one])]
    exact PrimeDivisor.ord_one B S hS hY hdec Z
  map_mul' u u' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd ?_
    rw [PrimeDivisor.ord_congr B S hS hY hdec Z _
      ((u.isUnit.map emb).mul (u'.isUnit.map emb)) (by rw [Units.val_mul, map_mul])]
    exact PrimeDivisor.ord_mul B S hS hY hdec Z _ _ _ _

/-- **The order of vanishing of an integer power.** For a unit `f` of the ring of rational
functions read into the total fraction ring at the generic point of a prime divisor `Z` through
a ring homomorphism, `ord_Z(f^a) = a · ord_Z(f)`.

`AlgebraicGeometry.Space.GenericFractionEmbedding.ord_zpow` is this for the canonical embedding
family of Stacks 0ENK; the statement is given here for one homomorphism, which is all the
proof of `AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul` uses. -/
theorem PrimeDivisor.ord_zpow_of_ringHom
    (emb : rationalFunctions B S hS hY →+* Z.genericTotalFractionRing B S hS hY hdec)
    (g : (rationalFunctions B S hS hY)ˣ) (a : ℤ) :
    Z.ord B S hS hY hdec
        (emb ((g ^ a : (rationalFunctions B S hS hY)ˣ) : rationalFunctions B S hS hY))
        ((g ^ a).isUnit.map emb) =
      a • Z.ord B S hS hY hdec (emb (g : rationalFunctions B S hS hY)) (g.isUnit.map emb) :=
  congrArg Multiplicative.toAdd (map_zpow (PrimeDivisor.ordUnitsHom B S hS hY hdec Z emb) g a)

end OrdZpow

/-! ### An integer multiple of a principal divisor -/

section Zsmul

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **An integer multiple of a principal divisor is a principal divisor**: `a · div(f)` is
`div(f^a)`, the power being taken in the units of the ring of rational functions and the
embeddings of Stacks 0ENK being the same family.

This is what absorbs the multiplicities `m_{X', X}` of Stacks 0EQA into the summands of a
rational equivalence, part (2) of Stacks 0EQ6 asking for principal divisors and not for integer
multiples of them. -/
theorem isPrincipalDivisorCycle_zsmul (sY : Y ⟶ D.space) (k : ℤ) {c : CycleGroup D sY k}
    (h : IsPrincipalDivisorCycle D sY k c) (a : ℤ) :
    IsPrincipalDivisorCycle D sY k (a • c) := by
  obtain ⟨hY, hint, g, heq⟩ := h
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  have hdec := hint.isDecentSpace
  set emb := E.emb
  refine ⟨hY, hint, g ^ a, ?_⟩
  have hcoe : ((a • c : CycleGroup D sY k) :
      IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
      a • (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) := rfl
  rw [hcoe, heq]
  funext Z
  change a • principalDivisorCycleCoefficients D sY hY hdec emb _ _ Z = _
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z) = 1
  · simp only [principalDivisorCycleCoefficients, dite_eq_left hcod]
    exact (PrimeDivisor.ord_zpow_of_ringHom D.site D.base D.base_mem hY.1 hdec
      (Z.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)
      (emb (Z.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)) g a).symm
  · simp only [principalDivisorCycleCoefficients, dite_eq_right hcod, smul_zero]

end Zsmul

/-! ### A locally finite sum of multiples of principal divisors -/

section Family

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **A locally finite sum of integer multiples of pushed-forward principal divisors is
rationally equivalent to zero**, within any subset of `|X|` containing the family.

This is the shape in which Stacks 0EQA delivers the flat pullback of a principal divisor: a sum
over the irreducible components `U_l` of integer multiples `a_l · div_l` of principal divisors,
pushed forward.  The multiplicities are absorbed by
`AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul`, after which the family is a presenting
family in the sense of part (2) of Stacks 0EQ6 and of its refinement
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin`. -/
theorem isRationallyEquivalentToZeroWithin_cycleFamilySum_zsmul (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) {K : Type v}
    (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hUfin : LocallyFinite fun l : K =>
      subspacePointSet D.site D.base D.base_mem X (U l).subspace)
    (a : K → ℤ) (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k)
    (hdim : ∀ l, deltaDimension D sX (U l) = k + 1)
    (hprin : ∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) k (e l))
    (T : Set (points D.site D.base D.base_mem X))
    (hsub : ∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆ T) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k
      (cycleFamilySum D sX hX U hUfin k fun l => a l • e l) T :=
  ⟨K, U, hUfin, (fun l => a l • e l), hsub, hdim,
    fun l => isPrincipalDivisorCycle_zsmul D ((U l).subspace.ι ≫ sX) k (hprin l) (a l), rfl⟩

end Family

end AlgebraicGeometry.Space

end

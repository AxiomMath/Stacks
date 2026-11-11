module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection

/-!
# The divisor associated to an invertible sheaf on an integral algebraic space

In Situation 0EDT let `X/B` be good, let `X` be integral with `n = dim_δ(X)` and let `ℒ` be an
`𝒪_X`-module. For a nonzero meromorphic section `s` of `ℒ` the *Weil divisor associated to `s`*
is `div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z]`, the sum being over the prime divisors `Z ⊆ X`; it is an
`(n-1)`-cycle, because a prime divisor of `X` has δ-dimension `n - 1`. The *Weil divisor
associated to `ℒ`* is the class

  `c₁(ℒ) ∩ [X] = [div_ℒ(s)] ∈ CH_{n-1}(X)`,

which does not depend on the chosen section: two nonzero meromorphic sections differ by a
rational function `f`, so their divisors differ by the principal divisor `div(f)`, which is
rationally equivalent to zero.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.toIntegralClosedSubspace` and
  `AlgebraicGeometry.Space.IntegralClosedSubspace.toPrimeDivisor`: the bijection between the
  prime divisors of `X` and the integral closed subspaces of `X` whose point set has
  codimension one in `|X|`.
* `AlgebraicGeometry.Space.divisorCycleCoefficients`: the coefficients of `div_ℒ(s)` indexed by
  the integral closed subspaces of `X`, so that the Weil divisor of Stacks 0EPU becomes a
  candidate cycle in the sense of Stacks 0EDZ.
* `AlgebraicGeometry.Space.divisorCycleOfSection` and
  `AlgebraicGeometry.Space.divisorCycleOfSectionOfGenerating`: `div_ℒ(s)` as an element of
  `Z_{n-1}(X)`, for an arbitrary `𝒪_X`-module and an arbitrary ratio family; Stacks 0EQE,
  part (1), for an invertible `ℒ` and the generators of Stacks 0EPR is
  `AlgebraicGeometry.Space.sectionWeilDivisor`.
* `AlgebraicGeometry.Space.principalDivisorCycleCoefficients`: the coefficients of the
  principal divisor `div(f)` of a rational function, through the embeddings of `R(X)` into the
  total fraction rings at the generic points of the prime divisors.
* `AlgebraicGeometry.Space.firstChernClassCapFundamental`: the class of `div_ℒ(s)` in a Chow
  target `AlgebraicGeometry.Space.ChowTarget`; Stacks 0EQE, part (2), in the Chow group
  `AlgebraicGeometry.Space.chowGroup` of Stacks 0EQ6 is
  `AlgebraicGeometry.Space.weilDivisorOfInvertibleSheaf`.

## Main results

* `AlgebraicGeometry.Space.divisorCycleCoefficients_mem_cyclesOfDimension`: the coefficients of
  `div_ℒ(s)` form an `(n-1)`-cycle. Local finiteness is transported from Stacks 0EPS and the
  δ-dimension of every prime divisor is `n - 1` by Stacks 0EPZ.
* `AlgebraicGeometry.Space.divisorCycleCoefficients_sub_divisorCycleCoefficients`: the
  difference of the divisors of two nonzero meromorphic sections is the principal divisor of
  their ratio. This is Stacks 0EPT, read coefficientwise.
* `AlgebraicGeometry.Space.firstChernClassCapFundamental_eq`: the class of `div_ℒ(s)` in a Chow
  target is independent of the chosen section, given that `div(f)` is one of the target's
  principal divisors; in `AlgebraicGeometry.Space.chowGroup` this is
  `AlgebraicGeometry.Space.chowClass_sectionWeilDivisor`.

## Implementation notes

The Weil divisors of Stacks 0EPU are coefficient families on
`AlgebraicGeometry.Space.PrimeDivisor`, while the cycles of Stacks 0EDZ are coefficient
families on `AlgebraicGeometry.Space.IntegralClosedSubspace`, so part (1) of the source is a
bridge between the two indexings. A prime divisor is an integral closed subspace together with
the *proposition* that its generic point has codimension one, so the two types are related by
an injection with an explicitly constructed inverse on the subspaces of codimension one; that
inverse has a real body, the generic point it needs being the image of the generic point of the
subspace. The coefficient at an integral closed subspace of codimension other than one is zero,
as the source's sum is over prime divisors only.

That a prime divisor has δ-dimension `n - 1` is Stacks 0EPZ, available as the three-clause
`AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace`; its dimension-function
hypotheses `d` and `hd` are the assertion of Stacks 0EDN which Situation 0EDT invokes, and are
carried here as they are carried there.

Nonzeroness — regularity — of the meromorphic section is carried, as in
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection`, by the ratio family `ratio`
taking values in the *units* of the total fraction rings at the generic points of the prime
divisors; this is where the source uses it. The source states the definitions for an invertible
`ℒ`, and invertibility is never used, exactly as for Stacks 0EPR and 0EPU, so they are stated
for an arbitrary `𝒪_X`-module. Decency of `|X|` follows from goodness, through
`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.isDecentSpace_of_isGood`; it is carried as
the argument `hdec` only because the order of vanishing is phrased through it.

The class of `div_ℒ(s)` is formed here in an arbitrary Chow target
`AlgebraicGeometry.Space.ChowTarget`, with the embeddings `R(X) → Q(𝒪^h_{X,ξ})` as the parameter
`emb`; that `div(f)` is one of the target's principal divisors is an argument of
`AlgebraicGeometry.Space.firstChernClassCapFundamental_eq`. Stacks 0EQE itself, for an invertible
`ℒ`, the generators of Stacks 0EPR, the canonical embeddings of Stacks 0ENK
(`AlgebraicGeometry.Space.genericFractionEmbedding`) and the Chow group
`AlgebraicGeometry.Space.chowGroup` of Stacks 0EQ6, is
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.WeilDivisorOfInvertibleSheaf`, which builds on the
coefficient families of this file; the principal divisor of Stacks 0ENP is in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisor`.

## References

* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u z w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Prime divisors and integral closed subspaces of codimension one -/

section Bridge

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}


/-- The integral closed subspace underlying a prime divisor. -/
def PrimeDivisor.toIntegralClosedSubspace (Z : PrimeDivisor B S hS X) :
    IntegralClosedSubspace B S hS X :=
  ⟨Z.subspace, Z.closed, Z.integral⟩

@[simp]
theorem PrimeDivisor.subspace_toIntegralClosedSubspace (Z : PrimeDivisor B S hS X) :
    (Z.toIntegralClosedSubspace B S hS).subspace = Z.subspace :=
  rfl

/-- Distinct prime divisors have distinct underlying integral closed subspaces. -/
theorem PrimeDivisor.injective_toIntegralClosedSubspace :
    Function.Injective (PrimeDivisor.toIntegralClosedSubspace B S hS (X := X)) := fun _ _ h =>
  PrimeDivisor.eq_of_subspace_eq B S hS (congrArg IntegralClosedSubspace.subspace h)

/-- The point set of the integral closed subspace underlying a prime divisor has codimension
one in `|X|`, this being the defining property of a prime divisor. -/
theorem PrimeDivisor.codimension_integralClosedSubspaceSupport
    (hX : IsAlgebraicSpace B S hS X) (Z : PrimeDivisor B S hS X) :
    codimension (integralClosedSubspaceSupport B S hS hX
      (Z.toIntegralClosedSubspace B S hS)) = 1 := by
  obtain ⟨ξ, hgen, hcod⟩ := Z.codimension_one
  have he : integralClosedSubspaceSupport B S hS hX (Z.toIntegralClosedSubspace B S hS) =
      IrreducibleCloseds.closureSingleton ξ := IrreducibleCloseds.ext hgen.symm
  rw [he]
  exact hcod

/-- An integral closed subspace whose point set has codimension one in `|X|` is a prime
divisor: a generic point of its point set is the image of its own generic point. -/
def IntegralClosedSubspace.toPrimeDivisor (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X)
    (h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1) :
    PrimeDivisor B S hS X :=
  ⟨Z.subspace, Z.isClosedSubspace, Z.isIntegralSpace,
    ⟨pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS),
      isGenericPoint_pointsMap_genericPoint B S hS hX Z, by
        have he : integralClosedSubspaceSupport B S hS hX Z =
            IrreducibleCloseds.closureSingleton
              (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS)) :=
          IrreducibleCloseds.ext (isGenericPoint_pointsMap_genericPoint B S hS hX Z).symm
        rw [← he]
        exact h⟩⟩

@[simp]
theorem IntegralClosedSubspace.subspace_toPrimeDivisor (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X)
    (h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1) :
    (Z.toPrimeDivisor B S hS hX h).subspace = Z.subspace :=
  rfl

@[simp]
theorem IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor
    (hX : IsAlgebraicSpace B S hS X) (Z : IntegralClosedSubspace B S hS X)
    (h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1) :
    (Z.toPrimeDivisor B S hS hX h).toIntegralClosedSubspace B S hS = Z :=
  IntegralClosedSubspace.ext rfl

/-- Any prime divisor with the same underlying subfunctor as an integral closed subspace of
codimension one is the one constructed from it. -/
theorem IntegralClosedSubspace.toPrimeDivisor_eq (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X)
    (h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1)
    (W : PrimeDivisor B S hS X) (hW : W.subspace = Z.subspace) :
    Z.toPrimeDivisor B S hS hX h = W :=
  PrimeDivisor.eq_of_subspace_eq B S hS hW.symm

/-- An integral closed subspace of `X` underlies a prime divisor exactly when its point set has
codimension one in `|X|`. -/
theorem exists_primeDivisor_subspace_eq_iff (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X) :
    (∃ W : PrimeDivisor B S hS X, W.subspace = Z.subspace) ↔
      codimension (integralClosedSubspaceSupport B S hS hX Z) = 1 := by
  constructor
  · rintro ⟨W, hW⟩
    have hcod := W.codimension_integralClosedSubspaceSupport B S hS hX
    rwa [show W.toIntegralClosedSubspace B S hS = Z from IntegralClosedSubspace.ext hW] at hcod
  · exact fun h => ⟨Z.toPrimeDivisor B S hS hX h, rfl⟩

end Bridge

/-! ### The Weil divisor of a meromorphic section as a cycle -/

section DivisorCycle

variable (D : BaseSpaceDimensionSituation.{u})
variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
variable (sX : X ⟶ D.space) (hX : D.IsGood sX)
variable (hdec : IsDecentSpace D.site D.base D.base_mem X)
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable (L : Modules.{u, max u z} D.site D.base D.base_mem X hX.1)

/-- The coefficients of the Weil divisor `div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z]` of a nonzero
meromorphic section `s` of `ℒ`, indexed by the integral closed subspaces of `X`: the coefficient
at `Z` is `ord_{Z,ℒ}(s)` when `Z` is a prime divisor, that is when its point set has codimension
one in `|X|`, and is zero otherwise. -/
def divisorCycleCoefficients (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 then
    divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio
      (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 h)
  else 0

/-- At an integral closed subspace of codimension one the coefficient of `div_ℒ(s)` is the
order of vanishing of `s` along the corresponding prime divisor. -/
theorem divisorCycleCoefficients_of_codimension_eq_one
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1) :
    divisorCycleCoefficients D sX hX hdec L s ratio Z =
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio
        (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 h) :=
  dite_eq_left h

/-- At an integral closed subspace which is not a prime divisor the coefficient of `div_ℒ(s)`
is zero. -/
theorem divisorCycleCoefficients_of_codimension_ne_one
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) ≠ 1) :
    divisorCycleCoefficients D sX hX hdec L s ratio Z = 0 :=
  dite_eq_right h

/-- The coefficient of `div_ℒ(s)` at the integral closed subspace underlying a prime divisor
`W` is `ord_{W,ℒ}(s)`; in particular it does not depend on which prime divisor with that
subspace is used. -/
@[simp]
theorem divisorCycleCoefficients_toIntegralClosedSubspace
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (W : PrimeDivisor D.site D.base D.base_mem X) :
    divisorCycleCoefficients D sX hX hdec L s ratio
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W := by
  rw [divisorCycleCoefficients_of_codimension_eq_one D sX hX hdec L s ratio
    (W.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1)]
  exact congrArg _ (IntegralClosedSubspace.toPrimeDivisor_eq D.site D.base D.base_mem hX.1 _ _ W
    rfl)

/-- The prime divisors with a nonzero order of vanishing and the integral closed subspaces with
a nonzero `div_ℒ(s)`-coefficient have the same point sets, so local finiteness of the family of
Stacks 0EPS gives local finiteness of the family indexed by integral closed subspaces. -/
theorem locallyFinite_divisorCycleCoefficients_ne_zero
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X) :
    LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if divisorCycleCoefficients D sX hX hdec L s ratio Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  intro x
  obtain ⟨V, hV, hVfin⟩ := hfin x
  refine ⟨V, hV, Set.Finite.subset
    (hVfin.image (PrimeDivisor.toIntegralClosedSubspace D.site D.base D.base_mem)) ?_⟩
  rintro Z ⟨p, hpZ, hpV⟩
  by_cases hne : divisorCycleCoefficients D sX hX hdec L s ratio Z = 0
  · simp [hne] at hpZ
  have hpZ' : p ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := by
    simpa [hne] using hpZ
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 := by
    by_contra hc
    exact hne (divisorCycleCoefficients_of_codimension_ne_one D sX hX hdec L s ratio hc)
  have hWne : divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio
      (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod) ≠ 0 := by
    rw [← divisorCycleCoefficients_toIntegralClosedSubspace D sX hX hdec L s ratio,
      IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor]
    exact hne
  exact ⟨Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod,
    ⟨p, by simpa [hWne] using hpZ', hpV⟩,
    IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
      hX.1 Z hcod⟩

/-- The coefficients of `div_ℒ(s)` form an `(n-1)`-cycle on `X`:
their support is locally finite by Stacks 0EPS, and an integral closed subspace carrying a
nonzero coefficient is a prime divisor, hence has δ-dimension `n - 1` by Stacks 0EPZ. -/
theorem divisorCycleCoefficients_mem_cyclesOfDimension
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    divisorCycleCoefficients D sX hX hdec L s ratio ∈ cyclesOfDimension D sX (n - 1) := by
  refine ⟨locallyFinite_divisorCycleCoefficients_ne_zero D sX hX hdec L s ratio hfin,
    fun Z hZ => ?_⟩
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 := by
    by_contra hc
    exact hZ (divisorCycleCoefficients_of_codimension_ne_one D sX hX hdec L s ratio hc)
  exact ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint d hd hn Z).out 2 3).mp hcod

/-- The Weil divisor `div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z]` of Stacks 0EPU of a meromorphic section
`s` of an `𝒪_X`-module `ℒ`, read at a ratio family `ratio`, as an element of `Z_{n-1}(X)` once
its support is locally finite: it is an `(n-1)`-cycle because a prime divisor of an integral
good algebraic space of δ-dimension `n` has δ-dimension `n - 1` by Stacks 0EPZ.
`AlgebraicGeometry.Space.divisorCycleOfSectionOfGenerating` gets the local finiteness from a
nonempty open subspace over which `s` generates `ℒ`. Stacks 0EQE, part (1), is
`AlgebraicGeometry.Space.sectionWeilDivisor`. -/
def divisorCycleOfSection (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    CycleGroup D sX (n - 1) :=
  ⟨divisorCycleCoefficients D sX hX hdec L s ratio,
    divisorCycleCoefficients_mem_cyclesOfDimension D sX hX hdec L s ratio hfin hint d hd
      hn⟩

/-- The coefficient of `div_ℒ(s)` at an integral closed subspace of `X`. -/
@[simp]
theorem divisorCycleOfSection_coe
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    (divisorCycleOfSection D sX hX hdec L s ratio hfin hint d hd hn).1 =
      divisorCycleCoefficients D sX hX hdec L s ratio :=
  rfl

/-- The Weil divisor `div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z]` of a meromorphic section `s` of `ℒ` as
an element of `Z_{n-1}(X)`, with the local finiteness of its support supplied by Stacks 0EPS
from a nonempty open subset of `|X|` containing the generic point of no prime divisor along
which `s` has nonzero order — the open subspace over which `s` generates `ℒ`. -/
def divisorCycleOfSectionOfGenerating
    (hN : HasEtaleLocalProperty D.site D.base D.base_mem X
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (U : Set (points D.site D.base D.base_mem X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hgen : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W ≠ 0 →
        W.genericPoint D.site D.base D.base_mem X ∈ Uᶜ)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    CycleGroup D sX (n - 1) :=
  divisorCycleOfSection D sX hX hdec L s ratio
    (locallyFinite_divisorCoefficients_ne_zero.{u, z} D.site D.base D.base_mem hX.1 hdec hN
      hint.2.2 L s ratio U hUopen hUne hgen) hint d hd hn

/-! ### Independence of the chosen section -/

/-- The coefficients of the principal divisor `div(f)` of a rational function `f` on `X`,
indexed by the integral closed subspaces of `X`: the coefficient at a prime divisor `Z` is the
order of vanishing `ord_Z(f)` of the image of `f` in the total fraction ring at the generic
point of `Z`, and the coefficient at a subspace which is not a prime divisor is zero.

The family of embeddings is the parameter `emb`; for the canonical embeddings of Stacks 0ENK,
`AlgebraicGeometry.Space.genericFractionEmbedding`, the family is
`AlgebraicGeometry.Space.canonicalPrincipalCycleCoefficients`. -/
def principalDivisorCycleCoefficients
    (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      rationalFunctions D.site D.base D.base_mem hX.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)
    (f : rationalFunctions D.site D.base D.base_mem hX.1)
    (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (emb W f))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 then
    (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 h).ord D.site D.base D.base_mem hX.1 hdec
      (emb (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 h) f)
      (hf (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 h))
  else 0

/-- **Stacks 0EPT, as an identity of cycle coefficients.** If the ratios of two nonzero
meromorphic sections `s` and `s'` of `ℒ` differ, at the generic point of every prime divisor, by
the image of a rational function `f`, then `div_ℒ(s) - div_ℒ(s') = div(f)` coefficientwise. -/
theorem divisorCycleCoefficients_sub_divisorCycleCoefficients
    (s s' : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      rationalFunctions D.site D.base D.base_mem hX.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)
    (f : rationalFunctions D.site D.base D.base_mem hX.1)
    (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (emb W f))
    (hratio : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      ((ratio W s : W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)) =
        emb W f * (ratio W s' : W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    divisorCycleCoefficients D sX hX hdec L s ratio Z -
        divisorCycleCoefficients D sX hX hdec L s' ratio Z =
      principalDivisorCycleCoefficients D sX hX hdec emb f hf Z := by
  by_cases h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1
  · rw [divisorCycleCoefficients_of_codimension_eq_one D sX hX hdec L s ratio h,
      divisorCycleCoefficients_of_codimension_eq_one D sX hX hdec L s' ratio h,
      show principalDivisorCycleCoefficients D sX hX hdec emb f hf Z = _ from dite_eq_left h]
    dsimp only [divisorCoefficients]
    rw [orderOfVanishingSection_eq_add_ord.{u, z} D.site D.base D.base_mem hX.1 hdec _ L s s' _
      (emb _) f (hf _) (hratio _)]
    ring
  · rw [divisorCycleCoefficients_of_codimension_ne_one D sX hX hdec L s ratio h,
      divisorCycleCoefficients_of_codimension_ne_one D sX hX hdec L s' ratio h,
      show principalDivisorCycleCoefficients D sX hX hdec emb f hf Z = 0 from dite_eq_right h,
      sub_zero]

section Class

variable {CH : Type w} [AddCommGroup CH] {n : ℤ}

/-- The class `[div_ℒ(s)]` of the Weil divisor of a meromorphic section `s` of `ℒ` in a Chow
target `chow`. Its independence of the chosen section is
`AlgebraicGeometry.Space.firstChernClassCapFundamental_eq`. Stacks 0EQE, part (2), the class
`c₁(ℒ) ∩ [X]` in the Chow group `AlgebraicGeometry.Space.chowGroup` of Stacks 0EQ6, is
`AlgebraicGeometry.Space.weilDivisorOfInvertibleSheaf`. -/
def firstChernClassCapFundamental
    (chow : ChowTarget.{u, w, v} D sX hX (n - 1) CH)
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x)
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) : CH :=
  chow.cls (divisorCycleOfSection D sX hX hdec L s ratio hfin hint d hd hn)

/-- The class of `div_ℒ(s)` in a Chow target does not depend on the chosen meromorphic section
of `ℒ`.

If the ratios of `s` and `s'` at the generic points of the prime divisors differ by the image of
a rational function `f`, then `div_ℒ(s) - div_ℒ(s') = div(f)` by Stacks 0EPT, and `div(f)` is
rationally equivalent to zero by Stacks 0EQ6: it is the one-member family `∑ (i_j)_* div(f_j)`
of part (1), taken on `X` itself, once it is one of the principal divisors of `chow`. In the
Chow group `AlgebraicGeometry.Space.chowGroup` this is
`AlgebraicGeometry.Space.chowClass_sectionWeilDivisor`. -/
theorem firstChernClassCapFundamental_eq
    (chow : ChowTarget.{u, w, v} D sX hX (n - 1) CH)
    (s s' : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hfin' : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s' ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x)
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      rationalFunctions D.site D.base D.base_mem hX.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)
    (f : rationalFunctions D.site D.base D.base_mem hX.1)
    (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (emb W f))
    (hratio : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      ((ratio W s : W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)) =
        emb W f * (ratio W s' : W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec))
    (hprincipal : ∃ (Y : IntegralClosedSubspace D.site D.base D.base_mem X)
      (c : CycleGroup D (Y.subspace.ι ≫ sX) (n - 1)), c ∈ chow.principalDivisors Y ∧
        ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
          (integralClosedSubspacePushforward D sX hX Y (n - 1) c).1 Z =
            principalDivisorCycleCoefficients D sX hX hdec emb f hf Z) :
    firstChernClassCapFundamental D sX hX hdec L chow s ratio hfin hint d hd hn =
      firstChernClassCapFundamental D sX hX hdec L chow s' ratio hfin' hint d hd hn := by
  obtain ⟨Y, c, hc, hcoeff⟩ := hprincipal
  have hYfin : LocallyFinite fun _ : PUnit.{v + 1} =>
      subspacePointSet D.site D.base D.base_mem X Y.subspace :=
    fun _ => ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩
  have hsum : divisorCycleOfSection D sX hX hdec L s ratio hfin hint d hd hn -
      divisorCycleOfSection D sX hX hdec L s' ratio hfin' hint d hd hn =
      cycleFamilySum D sX hX (fun _ : PUnit.{v + 1} => Y) hYfin (n - 1) fun _ => c := by
    refine Subtype.ext (funext fun Z => ?_)
    rw [cycleFamilySum_apply, finsum_unique, hcoeff Z,
      ← divisorCycleCoefficients_sub_divisorCycleCoefficients D sX hX hdec L s s' ratio emb f hf
        hratio Z]
    rfl
  have hzero := chow.cls_cycleFamilySum_eq_zero (fun _ : PUnit.{v + 1} => Y) hYfin
    (fun _ => c) fun _ => hc
  rw [← hsum, map_sub] at hzero
  exact sub_eq_zero.mp hzero

end Class

end DivisorCycle

end AlgebraicGeometry.Space

end

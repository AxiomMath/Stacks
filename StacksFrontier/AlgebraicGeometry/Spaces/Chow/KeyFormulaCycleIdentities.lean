module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFamilySums
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor

/-!
# The cycle identities of the situation preceding the key formula

In Situation 0EDT let `X/B` be good, let `X` be integral with `dim_δ(X) = n`, let `ℒ` and `𝒩` be
invertible `𝒪_X`-modules and let `s`, `t` be nonzero meromorphic sections of `ℒ`, `𝒩`.  Section
0EQU chooses a locally finite family of prime divisors `Z_i ⊆ X`, `i ∈ I`, containing every prime
divisor along which `s` or `t` fails to generate, picks generators `s_i` of `ℒ_{ξ_i}` and `t_i` of
`𝒩_{ξ_i}` at the generic point `ξ_i` of `Z_i`, writes `s = f_i s_i` and `t = g_i t_i` with `f_i`,
`g_i` units of `Q(B_i)`, `B_i = 𝒪^h_{X, ξ_i}`, and records the two identities

* `c₁(𝒩) ∩ div_ℒ(s) = ∑_i ord_{B_i}(f_i) · (Z_i → X)_* div_{𝒩|Z_i}(t_i|Z_i)`,
* `c₁(ℒ) ∩ div_𝒩(t) = ∑_i ord_{B_i}(g_i) · (Z_i → X)_* div_{ℒ|Z_i}(s_i|Z_i)`,

in `Z_{n-2}(X)`.  The *key formula*, Stacks 0EQV, is the assertion that the difference of those
two cycles is the locally finite sum `∑_i (Z_i → X)_* div(∂_{B_i}(f_i, g_i))` of the principal
divisors of the tame symbols.

This module proves the two identities and the resulting description of the first cycle of the key
formula, and states the key formula itself.

## What is proved and what is not

The two identities above are *re-indexings*: by Stacks 0EQJ the cap product with `c₁(𝒩)` is the
coefficientwise extension `∑_W α(W) · (W → X)_*(c₁(𝒩|_W) ∩ [W])` over all integral closed
subspaces `W ⊆ X`, and by Stacks 0EQE the cycle `div_ℒ(s)` has coefficient `ord_{Z,ℒ}(s)` at a
prime divisor `Z` and zero elsewhere; so the identity says that this sum over all of `X` may be
rewritten as the sum over the chosen family, which is legitimate exactly because the family
contains every prime divisor with `ord_{Z,ℒ}(s) ≠ 0` and is locally finite.  That is
`AlgebraicGeometry.Space.firstChernCapCycleMap_eq_cycleFamilySum`, proved here for an arbitrary
`(k+1)`-cycle, and
`AlgebraicGeometry.Space.firstChernCapCycleMap_divisorCycleAt_eq_cycleFamilySum`, its
specialization to `div_ℒ(s)`, for an arbitrary component rule of Stacks 0EQJ.  The instance of
the latter in which the component cycle is the Weil divisor `div_{𝒩|Z_i}(t_i|Z_i)` of Stacks 0EQE
part (1) on `Z_i`, which is the form Section 0EQU displays, is in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor`.

The key formula itself is proved elsewhere, at the canonical choices and for the constructed
tame-symbol sum: `AlgebraicGeometry.Space.keyFormula_of_ne_zero` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline`.  What this module states
and leaves open is the *predicate* `AlgebraicGeometry.Space.KeyFormula`, which quantifies the
component rules of Stacks 0EQJ and the principal divisors of the tame symbols, read
coefficientwise by `AlgebraicGeometry.Space.keyFormula_iff_forall`; at that generality it is not
a theorem of this library.

## The carried constructions, and why

The component cycle `c₁(ℒ|_W) ∩ [W]` of an integral closed subspace `W ⊆ X` is here the
parameter `AlgebraicGeometry.Space.FirstChernComponentCycleRule` of Stacks 0EQJ, and nothing
below uses any property of it.  At `W = Z_i` the source's value is `div_{ℒ|Z_i}(s_i|Z_i)`, the
Weil divisor of Stacks 0EQE part (1) on `Z_i`;
`AlgebraicGeometry.Space.componentDivisorCycleRule` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor` builds that rule, and
`AlgebraicGeometry.Space.firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum` is the
instance of the cycle identity below for it, which is the form Section 0EQU displays and which
carries the tag.

One quantity of Section 0EQU is a parameter of the *predicate* below, so that the predicate can
be stated before that quantity is built.

* The principal divisor `div(∂_{B_i}(f_i, g_i))` on `Z_i` is the field `tame` of the statement of
  the key formula.  It is constructed, not missing: it is
  `AlgebraicGeometry.Space.PrimeDivisor.keyFormulaTameCycle` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaStatement`, and the sum
  `∑_i (Z_i → X)_* div(∂_{B_i}(f_i, g_i))` over the family is
  `AlgebraicGeometry.Space.keyFormulaTameSum` there, which is the right-hand side of the proved
  key formula `AlgebraicGeometry.Space.keyFormula_of_ne_zero`.

The orders `ord_{B_i}(f_i)` and `ord_{B_i}(g_i)` are **not** parameters: they are the orders of
vanishing `ord_{Z_i,ℒ}(s)` and `ord_{Z_i,𝒩}(t)` of Stacks 0EPR, which the source identifies with
them, in the form `AlgebraicGeometry.Space.orderOfVanishingSection`.  The family of generators at
the generic points enters them only through the `ratio` parameter of Stacks 0EPR, and
`AlgebraicGeometry.Space.orderOfVanishingSection_unit_smul` says the orders do not depend on it.
The pushforwards `(Z_i → X)_*` and the locally finite sums are not parameters either: they are
`AlgebraicGeometry.Space.integralClosedSubspacePushforward` and
`AlgebraicGeometry.Space.cycleFamilySum` of Stacks 0EQ6 part (1).

## Main definitions

* `AlgebraicGeometry.Space.divisorCycleAt`: the cycle `div_ℒ(s)` of Stacks 0EQE part (1), graded
  by an integer `k + 1` equal to `n - 1`, so that the cap product of Stacks 0EQJ applies to it.
* `AlgebraicGeometry.Space.keyFormulaDivisorTerm`: the `i`-th term
  `ord_{B_i}(f_i) div_{𝒩|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{ℒ|Z_i}(s_i|Z_i)` of the first cycle
  of the key formula, as a `k`-cycle on `Z_i`.
* `AlgebraicGeometry.Space.KeyFormula`: **Stacks 0EQV**, the key formula.

## Main results

* `AlgebraicGeometry.Space.firstChernCapCycleMap_eq_cycleFamilySum`: the cap product of Stacks
  0EQJ on a `(k+1)`-cycle carried by a locally finite family of integral closed subspaces of
  δ-dimension `k + 1` is the sum of Stacks 0EQ6 part (1) over that family.
* `AlgebraicGeometry.Space.firstChernCapCycleMap_divisorCycleAt_eq_cycleFamilySum`: the two cycle
  identities of Section 0EQU, both instances of one statement, for an arbitrary component rule of
  Stacks 0EQJ.  The instance of it in which the component cycle is the Weil divisor
  `div_{𝒩|Z_i}(t_i|Z_i)` of Stacks 0EQE part (1) on `Z_i` is
  `AlgebraicGeometry.Space.firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor`, and that is what
  carries the tag.
* `AlgebraicGeometry.Space.firstChernCap_sub_firstChernCap_eq_cycleFamilySum`: the first cycle of
  the key formula is the difference `c₁(𝒩) ∩ div_ℒ(s) - c₁(ℒ) ∩ div_𝒩(t)`.
* `AlgebraicGeometry.Space.cycleFamilySum_sub`: the sum of Stacks 0EQ6 part (1) is additive in the
  family of summands.
* `AlgebraicGeometry.Space.deltaDimension_toIntegralClosedSubspace`: a prime divisor of `X` has
  δ-dimension `n - 1`, by Stacks 0EPZ; this discharges the hypothesis `hdim` below.
* `AlgebraicGeometry.Space.keyFormula_iff_forall`: the key formula read coefficientwise.

## Implementation notes

`AlgebraicGeometry.Space.divisorCycleAt` repeats
`AlgebraicGeometry.Space.divisorCycleOfSection` of Stacks 0EQE part (1) with its grading given by
a parameter `k` and an equation `k + 1 = n - 1`, rather than by the expression `n - 1`.  This is
needed because the cap product of Stacks 0EQJ is a map `Z_{k+1}(X) ⟶ Z_k(X)` and the two gradings
`n - 1` and `(n - 2) + 1` are equal but not syntactically so; no mathematics is added.

The hypothesis `hdim` giving the δ-dimension of the members of the family is explicit rather than
derived inside the statements, because the component rule of Stacks 0EQJ takes the δ-dimension of
its argument as an argument.  It is a theorem, not a gap:
`AlgebraicGeometry.Space.deltaDimension_toIntegralClosedSubspace` proves it from Stacks 0EPZ,
whose own carried hypotheses `d` and `hd` — the dimension-function property of `δ_{X/B}`, Stacks
0EDN — are the ones already carried by Stacks 0EQE in this library.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u z v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Additivity of the locally finite sum of Stacks 0EQ6 part (1) -/

section FamilySum

variable (D : BaseSpaceDimensionSituation.{u})
variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
variable {J : Type v}

/-- The sum `∑ (i_j)_* c_j` of Stacks 0EQ6 part (1) is additive in the family of summands: a
difference of families goes to the difference of the sums.

Coefficientwise this is the distributivity of a locally finite sum over a difference, and it needs
the finiteness of the two supports, which is
`AlgebraicGeometry.Space.finite_support_cycleFamilyCoeff`. -/
theorem cycleFamilySum_sub (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (k : ℤ) (a b : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k) :
    cycleFamilySum D sX hX W hWfin k (fun j => a j - b j) =
      cycleFamilySum D sX hX W hWfin k a - cycleFamilySum D sX hX W hWfin k b := by
  refine Subtype.ext (funext fun Y => ?_)
  have hsub : ((cycleFamilySum D sX hX W hWfin k a - cycleFamilySum D sX hX W hWfin k b).1 Y) =
      (cycleFamilySum D sX hX W hWfin k a).1 Y -
        (cycleFamilySum D sX hX W hWfin k b).1 Y := by
    simp
  rw [hsub, cycleFamilySum_apply, cycleFamilySum_apply, cycleFamilySum_apply,
    ← finsum_sub_distrib (finite_support_cycleFamilyCoeff D sX hX W hWfin k a Y)
      (finite_support_cycleFamilyCoeff D sX hX W hWfin k b Y)]
  refine finsum_congr fun j => ?_
  rw [map_sub]
  simp

end FamilySum

/-! ### The cap product over a locally finite family carrying the cycle -/

section Reindex

variable (D : BaseSpaceDimensionSituation.{u})
variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
variable (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
variable (chern : FirstChernComponentCycleRule D sX k)
variable {I : Type v}

/-- The cap product of Stacks 0EQJ, at the level of cycles, evaluated on a `(k+1)`-cycle `α`
carried by a locally finite family `{Z_i}` of integral closed subspaces of δ-dimension `k + 1`:
it is the sum `∑_i α(Z_i) · (Z_i → X)_*(c₁(ℒ|_{Z_i}) ∩ [Z_i])` of Stacks 0EQ6 part (1) over the
family.

Only the hypothesis `hcover`, that every subspace occurring in `α` is a member of the family, and
injectivity of the family are used to re-index the defining sum; local finiteness is what makes
the sum over the family a cycle. -/
theorem firstChernCapCycleMap_eq_cycleFamilySum
    (α : CycleGroup D sX (k + 1))
    (Z : I → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZinj : Function.Injective Z)
    (hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Z i).subspace)
    (hdim : ∀ i, deltaDimension D sX (Z i) = k + 1)
    (hcover : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 W ≠ 0 → ∃ i, Z i = W) :
    firstChernCapCycleMap D sX hX k chern α =
      cycleFamilySum D sX hX Z hZfin k (fun i => α.1 (Z i) • chern (Z i) (hdim i)) := by
  refine Subtype.ext (funext fun Y => ?_)
  rw [firstChernCapCycleMap_apply, cycleFamilySum_apply]
  have hsupp : ∀ W ∈ Function.support
      (fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
        α.1 W * (firstChernComponentCycle D sX hX k chern W).1 Y),
      W ∈ Set.range Z ↔ W ∈ Set.univ := by
    intro W hW
    simp only [Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := hcover W (left_ne_zero_of_mul (Function.mem_support.1 hW))
    exact ⟨i, hi⟩
  rw [← finsum_mem_univ (fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α.1 W * (firstChernComponentCycle D sX hX k chern W).1 Y),
    ← finsum_mem_inter_support_eq' _ (Set.range Z) Set.univ hsupp, finsum_mem_range hZinj]
  refine finsum_congr fun i => ?_
  rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k chern (hdim i), map_zsmul]
  simp

end Reindex

/-! ### The cycle identities of Section 0EQU -/

section CycleIdentities

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

/-- **Stacks 0EPZ.** A prime divisor of an integral good algebraic space of δ-dimension `n` has
δ-dimension `n - 1`.  This discharges the hypothesis `hdim` of the statements below; the
dimension-function hypotheses `d` and `hd` are those carried by Stacks 0EPZ. -/
theorem deltaDimension_toIntegralClosedSubspace
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Z : PrimeDivisor D.site D.base D.base_mem X) :
    deltaDimension D sX (Z.toIntegralClosedSubspace D.site D.base D.base_mem) = n - 1 :=
  ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint d hd hn
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem)).out 2 3).mp
    (Z.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1)

variable (L : Modules.{u, max u z} D.site D.base D.base_mem X hX.1)

/-- **Stacks 0EQE, part (1), re-graded.** The cycle `div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z]` of a
nonzero meromorphic section `s` of `ℒ`, as an element of `Z_{k+1}(X)` for an integer `k` with
`k + 1 = n - 1`.

This is `AlgebraicGeometry.Space.divisorCycleOfSection` with its grading named, so that the cap
product `Z_{k+1}(X) ⟶ Z_k(X)` of Stacks 0EQJ applies to it; the two gradings `n - 1` and
`(n - 2) + 1` are equal but not syntactically equal. -/
def divisorCycleAt (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    {k : ℤ} (hk : k + 1 = n - 1) :
    CycleGroup D sX (k + 1) :=
  ⟨divisorCycleCoefficients D sX hX hdec L s ratio, by
    rw [hk]
    exact divisorCycleCoefficients_mem_cyclesOfDimension D sX hX hdec L s ratio hfin hint d hd
      hn⟩

/-- The coefficient of the re-graded `div_ℒ(s)` at an integral closed subspace of `X`. -/
@[simp]
theorem divisorCycleAt_coe (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    {k : ℤ} (hk : k + 1 = n - 1) :
    (divisorCycleAt.{u, z} D sX hX hdec L s ratio hfin hint d hd hn hk).1 =
      divisorCycleCoefficients D sX hX hdec L s ratio :=
  rfl

/-- **Either cycle identity of the section preceding the key formula, for an arbitrary component
rule.**  In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = n`, let `ℒ` be an
`𝒪_X`-module with a nonzero meromorphic section `s`, and let `{Z_i}`, `i ∈ I`, be an injective
locally finite family of prime divisors of `X` containing every prime divisor along which `s` has
nonzero order of vanishing.  Then

`c₁(𝒩) ∩ div_ℒ(s) = ∑_i ord_{Z_i,ℒ}(s) · (Z_i → X)_*(c₁(𝒩|_{Z_i}) ∩ [Z_i])`

in `Z_{n-2}(X)`.  The two identities displayed in Section 0EQU before the key formula are the two
instances of this statement: the first is the one above, and the second is obtained by exchanging
`(ℒ, s)` with `(𝒩, t)` and `𝒩` with `ℒ`, that is by using the component rule of `ℒ` and the
divisor of `t`.

The orders `ord_{Z_i,ℒ}(s)` are those of Stacks 0EPR, which the source identifies with its
`ord_{B_i}(f_i)`, and they depend on the `ratio` parameter of Stacks 0EPR only through its value
at the generic points, not at all by
`AlgebraicGeometry.Space.orderOfVanishingSection_unit_smul`.  The δ-dimension hypothesis `hdim` is
Stacks 0EPZ, proved as
`AlgebraicGeometry.Space.deltaDimension_toIntegralClosedSubspace`.

The component cycle `c₁(𝒩|_{Z_i}) ∩ [Z_i]`, which the source writes `div_{𝒩|Z_i}(t_i|Z_i)`, is
here the arbitrary component rule `chern` of Stacks 0EQJ: nothing below uses any property of it.
`AlgebraicGeometry.Space.firstChernCapCycleMap_divisorCycleAt_eq_componentDivisorSum` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor` is the instance of this
statement in which that cycle is the Weil divisor `div_{𝒩|Z_i}(t_i|Z_i)` of Stacks 0EQE part (1)
on `Z_i`; that is the form Section 0EQU displays, and it carries the tag.

The key formula itself, Stacks 0EQV, **is** proved, at the canonical choices and for the
constructed tame-symbol sum:
`AlgebraicGeometry.Space.keyFormula_of_ne_zero` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline`, from which Section 0EQU's
`c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in `CH_{n-2}(X)` follows as
`AlgebraicGeometry.Space.canonicalFirstChernCap_divisor_comm`.  What is left open is only the
predicate `AlgebraicGeometry.Space.KeyFormula` below, which quantifies the component rules and
the tame-symbol divisors and so cannot be discharged at that generality. -/
@[stacks 0EQV "the situation above, not the lemma: either cycle identity of Section 0EQU, \
c_1(N) ∩ div_L(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i) in Z_{n-2}(X), for an \
arbitrary component rule chern of Stacks 0EQJ, of which it uses no property; hdim is Stacks \
0EPZ. DISCHARGED ELSEWHERE: the instance at the registered cap product — the component cycle \
canonicalFirstChernRule at the canonical choices, in CH_{n-2}(X) — is \
canonicalFirstChernCap_canonicalDivisorCycleAt, and the key formula itself is proved \
unconditionally as keyFormula_of_ne_zero; neither carries a free component rule"]
theorem firstChernCapCycleMap_divisorCycleAt_eq_cycleFamilySum
    {k : ℤ} (chern : FirstChernComponentCycleRule D sX k) {I : Type v}
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hk : k + 1 = n - 1)
    (Z : I → PrimeDivisor D.site D.base D.base_mem X)
    (hZinj : Function.Injective Z)
    (hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Z i).subspace)
    (hdim : ∀ i, deltaDimension D sX
      ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1)
    (hcover : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio W ≠ 0 →
        ∃ i, Z i = W) :
    firstChernCapCycleMap D sX hX k chern
        (divisorCycleAt.{u, z} D sX hX hdec L s ratio hfin hint d hd hn hk) =
      cycleFamilySum D sX hX
        (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k
        (fun i => orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec (Z i) L s
          (ratio (Z i)) •
            chern ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) (hdim i)) := by
  have hinj : Function.Injective
      fun i : I => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem :=
    (PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem).comp hZinj
  have hcover' : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      (divisorCycleAt.{u, z} D sX hX hdec L s ratio hfin hint d hd hn hk).1 W ≠ 0 →
        ∃ i, (Z i).toIntegralClosedSubspace D.site D.base D.base_mem = W := by
    intro W hW
    rw [divisorCycleAt_coe] at hW
    have hcod : codimension
        (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 W) = 1 := by
      by_contra hc
      exact hW (divisorCycleCoefficients_of_codimension_ne_one D sX hX hdec L s ratio hc)
    have hne : divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratio
        (W.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod) ≠ 0 := by
      rwa [divisorCycleCoefficients_of_codimension_eq_one D sX hX hdec L s ratio hcod] at hW
    obtain ⟨i, hi⟩ := hcover _ hne
    exact ⟨i, by
      rw [hi, IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor]⟩
  rw [firstChernCapCycleMap_eq_cycleFamilySum D sX hX k chern _
    (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hinj hZfin hdim hcover']
  refine congrArg _ (funext fun i => ?_)
  rw [divisorCycleAt_coe, divisorCycleCoefficients_toIntegralClosedSubspace]
  rfl

end CycleIdentities

/-! ### The key formula -/

section KeyFormulaStatement

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
variable (L N : Modules.{u, max u z} D.site D.base D.base_mem X hX.1)
variable {k : ℤ} (chernL chernN : FirstChernComponentCycleRule D sX k)
variable {I : Type v} (Z : I → PrimeDivisor D.site D.base D.base_mem X)

/-- The `i`-th term
`ord_{B_i}(f_i) div_{𝒩|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{ℒ|Z_i}(s_i|Z_i)`
of the first cycle of the key formula, as a `k`-cycle on `Z_i`.

The two orders are the orders of vanishing of Stacks 0EPR, which the source identifies with
`ord_{B_i}(f_i)` and `ord_{B_i}(g_i)`.  The two restricted divisors are the component cycles
`c₁(𝒩|_{Z_i}) ∩ [Z_i]` and `c₁(ℒ|_{Z_i}) ∩ [Z_i]` of Stacks 0EQJ, carried as the parameters
`chernN` and `chernL`. -/
def keyFormulaDivisorTerm
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (t : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 N)
    (ratioL : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (ratioN : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec N)
    (hdim : ∀ i, deltaDimension D sX
      ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1)
    (i : I) :
    CycleGroup D
      (((Z i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫ sX) k :=
  orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec (Z i) L s (ratioL (Z i)) •
      chernN ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) (hdim i) -
    orderOfVanishingSection.{u, z} D.site D.base D.base_mem hX.1 hdec (Z i) N t (ratioN (Z i)) •
      chernL ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) (hdim i)

/-- **Stacks 0EQV, the key formula.** In the situation of Section 0EQU the cycle

`∑_i (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{ℒ|Z_i}(s_i|Z_i))`

is equal to the cycle `∑_i (Z_i → X)_* div(∂_{B_i}(f_i, g_i))`, both in `Z_{n-2}(X)`.

The family `tame` is `div(∂_{B_i}(f_i, g_i))`, the principal divisor on `Z_i` of the tame symbol
of Chow Homology, Section 0EAH on the reduced Noetherian local ring of dimension one
`B_i = 𝒪^h_{X,ξ_i}`.  It is carried: this library has the tame symbol only for a local domain
with a module-finite integral closure, and the principal divisor cycle of a rational function on
an algebraic space only coefficientwise.

**This predicate quantifies the component rules and the family `tame`, and at that generality it
is not a theorem of this library.**  The key formula at the canonical choices, with the component
cycles and the tame-symbol divisors constructed, is
`AlgebraicGeometry.Space.keyFormula_of_ne_zero`. -/
def KeyFormula
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (t : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 N)
    (ratioL : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (ratioN : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec N)
    (hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Z i).subspace)
    (hdim : ∀ i, deltaDimension D sX
      ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1)
    (tame : ∀ i, CycleGroup D
      (((Z i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫ sX) k) : Prop :=
  cycleFamilySum D sX hX
      (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k
      (keyFormulaDivisorTerm.{u, z} D sX hX hdec L N chernL chernN Z s t ratioL ratioN hdim) =
    cycleFamilySum D sX hX
      (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k tame

/-- The key formula read coefficientwise: it holds exactly when, at every integral closed
subspace `Y ⊆ X`, the two coefficient families agree.

The coefficient family of the sum of Stacks 0EQ6 part (1) is
`AlgebraicGeometry.Space.cycleFamilySumCoeff`, whose value at `Y` is by definition the locally
finite sum `∑ᶠ i, ((Z_i → X)_* c_i)(Y)` of the coefficients of the pushed-forward terms there;
`AlgebraicGeometry.Space.cycleFamilySum_apply` displays it. -/
theorem keyFormula_iff_forall
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (t : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 N)
    (ratioL : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (ratioN : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec N)
    (hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Z i).subspace)
    (hdim : ∀ i, deltaDimension D sX
      ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1)
    (tame : ∀ i, CycleGroup D
      (((Z i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫ sX) k) :
    KeyFormula.{u, z} D sX hX hdec L N chernL chernN Z s t ratioL ratioN hZfin hdim tame ↔
      ∀ Y : IntegralClosedSubspace D.site D.base D.base_mem X,
        cycleFamilySumCoeff D sX hX
            (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) k
            (keyFormulaDivisorTerm.{u, z} D sX hX hdec L N chernL chernN Z s t ratioL ratioN
              hdim) Y =
          cycleFamilySumCoeff D sX hX
            (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) k tame Y :=
  ⟨fun h Y => congrFun (congrArg Subtype.val h) Y, fun h => Subtype.ext (funext h)⟩

/-- The first cycle of the key formula is the difference of the two cap products of Section
0EQU: with the family `{Z_i}` containing every prime divisor along which `s` or `t` has nonzero
order of vanishing,

`c₁(𝒩) ∩ div_ℒ(s) - c₁(ℒ) ∩ div_𝒩(t)
  = ∑_i (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{ℒ|Z_i}(s_i|Z_i))`

in `Z_{n-2}(X)`.  It is the two cycle identities of Section 0EQU together with additivity of the
locally finite sum of Stacks 0EQ6 part (1).

The two restricted divisors `div_{𝒩|Z_i}(t_i|Z_i)` and `div_{ℒ|Z_i}(s_i|Z_i)` are the component
cycles carried as the parameters `chernN` and `chernL` of Stacks 0EQJ, standing in for Stacks 0EQE
on `Z_i`; the two orders are those of Stacks 0EPR, which the source identifies with
`ord_{B_i}(f_i)` and `ord_{B_i}(g_i)`; the δ-dimension hypothesis `hdim` is Stacks 0EPZ, proved as
`AlgebraicGeometry.Space.deltaDimension_toIntegralClosedSubspace`.

The key formula itself — the equality of this cycle with `∑_i (Z_i → X)_* div(∂_{B_i}(f_i, g_i))`
— **is** proved at the canonical choices, as
`AlgebraicGeometry.Space.keyFormula_of_ne_zero`; only the predicate
`AlgebraicGeometry.Space.KeyFormula`, which quantifies the component rules and the tame-symbol
divisors, is left open. -/
@[stacks 0EQV "the situation above, not the lemma: the FIRST cycle of the key formula equals \
c_1(N) ∩ div_L(s) - c_1(L) ∩ div_N(t), from the two cycle identities of Section 0EQU, for \
arbitrary component rules chernN and chernL of Stacks 0EQJ, of which no property is used; hdim \
is Stacks 0EPZ. DISCHARGED ELSEWHERE: the key formula itself is proved unconditionally, at the \
canonical choices and for the constructed tame-symbol sum, as keyFormula_of_ne_zero, and its \
Section 0EQU consequence in CH_{n-2}(X) as canonicalFirstChernCap_divisor_comm"]
theorem firstChernCap_sub_firstChernCap_eq_cycleFamilySum
    (s : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 L)
    (t : MeromorphicSection.{u, z} D.site D.base D.base_mem X hX.1 N)
    (ratioL : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec L)
    (ratioN : LocalRatioFamily.{u, z} D.site D.base D.base_mem hX.1 hdec N)
    (hfinL : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratioL W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hfinN : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec N t ratioN W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (dim : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, dim x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hk : k + 1 = n - 1)
    (hZinj : Function.Injective Z)
    (hZfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X (Z i).subspace)
    (hdim : ∀ i, deltaDimension D sX
      ((Z i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1)
    (hcoverL : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec L s ratioL W ≠ 0 →
        ∃ i, Z i = W)
    (hcoverN : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, z} D.site D.base D.base_mem hX.1 hdec N t ratioN W ≠ 0 →
        ∃ i, Z i = W) :
    firstChernCapCycleMap D sX hX k chernN
        (divisorCycleAt.{u, z} D sX hX hdec L s ratioL hfinL hint dim hd hn hk) -
      firstChernCapCycleMap D sX hX k chernL
        (divisorCycleAt.{u, z} D sX hX hdec N t ratioN hfinN hint dim hd hn hk) =
      cycleFamilySum D sX hX
        (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k
        (keyFormulaDivisorTerm.{u, z} D sX hX hdec L N chernL chernN Z s t ratioL ratioN hdim) := by
  rw [firstChernCapCycleMap_divisorCycleAt_eq_cycleFamilySum.{u, z} D sX hX hdec L chernN s ratioL
      hfinL hint dim hd hn hk Z hZinj hZfin hdim hcoverL,
    firstChernCapCycleMap_divisorCycleAt_eq_cycleFamilySum.{u, z} D sX hX hdec N chernL t ratioN
      hfinN hint dim hd hn hk Z hZinj hZfin hdim hcoverN,
    ← cycleFamilySum_sub D sX hX
      (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k]
  exact congrArg
    (cycleFamilySum D sX hX
      (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k)
    (funext fun _ => rfl)

end KeyFormulaStatement

end AlgebraicGeometry.Space

end

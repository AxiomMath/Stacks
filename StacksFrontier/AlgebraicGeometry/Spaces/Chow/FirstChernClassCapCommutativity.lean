module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCycleIdentities
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence

/-!
# Commutativity of the two first Chern class cap products in the Chow group

In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = n`, let `ℒ` and `𝒩` be
invertible `𝒪_X`-modules, let `s` and `t` be nonzero meromorphic sections of `ℒ` and `𝒩` and set
`α = div_ℒ(s)`, `β = div_𝒩(t)`.  Stacks 0EQX asserts

`c₁(𝒩) ∩ α = c₁(ℒ) ∩ β`  in  `CH_{n-2}(X)`,

and its proof is one step.  By the two cycle identities of Section 0EQU the difference
`c₁(𝒩) ∩ α - c₁(ℒ) ∩ β` is the first cycle of the key formula; the key formula, Stacks 0EQV,
rewrites that cycle as the locally finite sum `∑_i (Z_i → X)_* div(∂_{B_i}(f_i, g_i))` of the
principal divisors of the tame symbols on the prime divisors `Z_i`, and a locally finite sum of
principal divisors on integral closed subspaces of δ-dimension `n - 1` is rationally equivalent
to zero.

This module carries out that step inside the Chow group `CH_{n-2}(X)` of Stacks 0EQ6: the
difference of the two classes is the class of the first cycle of the key formula, so the equality
of Stacks 0EQX holds exactly when that cycle is rationally equivalent to zero.

## Main results

* `AlgebraicGeometry.Space.chowClass_firstChernCapCycleMap_sub`: in `CH_{n-2}(X)` the difference
  of the two classes `c₁(𝒩) ∩ div_ℒ(s)` and `c₁(ℒ) ∩ div_𝒩(t)` is the class of the first cycle of
  the key formula.
* `AlgebraicGeometry.Space.firstChernClassCap_comm_iff_isRationallyEquivalentToZero`: the
  equality `c₁(𝒩) ∩ α = c₁(ℒ) ∩ β` in `CH_{n-2}(X)` holds if and only if the first cycle of the
  key formula is rationally equivalent to zero, for an arbitrary component rule of Stacks 0EQJ.

## What is proved here and where Stacks 0EQX itself is

Everything below is proved from the hypotheses of Stacks 0EQX itself, with no input beyond what
the library already has.  The two ingredients are
`AlgebraicGeometry.Space.firstChernCap_sub_firstChernCap_eq_cycleFamilySum`, the two cycle
identities of Section 0EQU, and the Chow group of Stacks 0EQ6 constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence`, whose class map is
`AlgebraicGeometry.Space.chowClass` and which is presented to the cap product of Stacks 0EQJ as
`AlgebraicGeometry.Space.chowTarget`.

The equality of Stacks 0EQX **is** proved, unconditionally and at the hypotheses of 0EQX, as
`AlgebraicGeometry.Space.canonicalFirstChernCap_divisor_comm` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline`, which carries the tag: the
key formula of Stacks 0EQV is proved there too, as
`AlgebraicGeometry.Space.keyFormula_of_ne_zero`, at the canonical choices and for the constructed
tame-symbol sum.  What is left open is only the *predicate*
`AlgebraicGeometry.Space.KeyFormula` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCycleIdentities`, which quantifies the
component rules of Stacks 0EQJ and the principal divisors of the tame symbols and so cannot be
discharged at that generality; the equivalence below is stated at the same generality and is what
turns that predicate into the equality.  Given it, the right hand side of the equivalence is
immediate from `AlgebraicGeometry.Space.chowClass_cycleFamilySum_eq_zero`, since the source's
tame symbol divisors `div(∂_{B_i}(f_i, g_i))` are principal divisors on the `Z_i` and the `Z_i`
have δ-dimension `n - 1`.

The equivalence is stated for an arbitrary component rule of Stacks 0EQJ, the component cycle
`c₁(ℒ|_W) ∩ [W]` of Stacks 0EQE on an integral closed subspace `W ⊆ X`.  This is a generalization
and not a weakening: it is an equivalence for *every* rule, so substituting the component cycle
of Stacks 0EQE — which is constructed, as
`AlgebraicGeometry.Space.canonicalFirstChernRule` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap` — reads as the assertion that
the conclusion of Stacks 0EQX is equivalent to the vanishing in `CH_{n-2}(X)` of the class of the
first cycle of its key formula.  At that rule the equality itself is the theorem
`AlgebraicGeometry.Space.canonicalFirstChernCap_divisor_comm`.

## References

* [Stacks Project, Tag 0EQX](https://stacks.math.columbia.edu/tag/0EQX)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Commutativity

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
variable (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
variable {k : ℤ} (chernL chernN : FirstChernComponentCycleRule D sX k)
variable {I : Type v} (Z : I → PrimeDivisor D.site D.base D.base_mem X)

/-- In `CH_{n-2}(X)` the difference of the classes of `c₁(𝒩) ∩ div_ℒ(s)` and `c₁(ℒ) ∩ div_𝒩(t)`
is the class of the first cycle

`∑_i (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{ℒ|Z_i}(s_i|Z_i))`

of the key formula, for a locally finite injective family `{Z_i}` of prime divisors of `X`
containing every prime divisor along which `s` or `t` has nonzero order of vanishing. -/
theorem chowClass_firstChernCapCycleMap_sub
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ratioL : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdec L)
    (ratioN : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdec N)
    (hfinL : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec L s ratioL W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hfinN : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec N t ratioN W = 0 then ∅
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
      divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec L s ratioL W ≠ 0 →
        ∃ i, Z i = W)
    (hcoverN : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec N t ratioN W ≠ 0 →
        ∃ i, Z i = W) :
    chowClass.{v} D sX hX k
          (firstChernCapCycleMap D sX hX k chernN
            (divisorCycleAt.{u, u} D sX hX hdec L s ratioL hfinL hint dim hd hn hk)) -
        chowClass.{v} D sX hX k
          (firstChernCapCycleMap D sX hX k chernL
            (divisorCycleAt.{u, u} D sX hX hdec N t ratioN hfinN hint dim hd hn hk)) =
      chowClass.{v} D sX hX k
        (cycleFamilySum D sX hX
          (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k
          (keyFormulaDivisorTerm.{u, u} D sX hX hdec L N chernL chernN Z s t ratioL ratioN
            hdim)) := by
  rw [← map_sub, firstChernCap_sub_firstChernCap_eq_cycleFamilySum.{u, u} D sX hX hdec L N
    chernL chernN Z s t ratioL ratioN hfinL hfinN hint dim hd hn hk hZinj hZfin hdim hcoverL
    hcoverN]

/-- **The conclusion of Stacks 0EQX, reduced to the key formula of Stacks 0EQV, for an arbitrary
component rule.**  In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = n`, let `ℒ`
and `𝒩` be invertible with nonzero meromorphic sections `s` and `t`, and set `α = div_ℒ(s)`,
`β = div_𝒩(t)`.  Then

`c₁(𝒩) ∩ α = c₁(ℒ) ∩ β` in `CH_{n-2}(X)`

holds if and only if the first cycle of the key formula of Section 0EQU is rationally equivalent
to zero, where that cycle is
`∑_i (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{ℒ|Z_i}(s_i|Z_i))`.

This is an equivalence, so it does not by itself prove the equality; what proves it is the key
formula, which gives the right hand side.  **Stacks 0EQX itself is proved**, unconditionally and
at its own hypotheses, by `AlgebraicGeometry.Space.canonicalFirstChernCap_divisor_comm` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline`, which is where the tag's
mathematical content lives.  What this statement adds is the generality: the component cycle
`c₁(ℒ|_W) ∩ [W]` of Stacks 0EQE is the explicit parameter `chern` of Stacks 0EQJ and the
equivalence holds for every value of it, so it is the form that converts the open predicate
`AlgebraicGeometry.Space.KeyFormula` — the key formula quantified over component rules and
tame-symbol divisors — into the equality at that generality.  `CH_{n-2}(X)` is the Chow group of
Stacks 0EQ6 constructed in `AlgebraicGeometry.Space.chowGroup`. -/
@[stacks 0EQX "not the lemma itself but its equivalence form: the equality \
c_1(N) ∩ div_L(s) = c_1(L) ∩ div_N(t) in CH_{n-2}(X) is shown to hold if and only if the first \
cycle of the key formula 0EQV is rationally equivalent to zero, for an arbitrary component rule \
chern of 0EQJ. The lemma's own statement is PROVED ELSEWHERE, unconditionally and at the \
hypotheses of 0EQX: canonicalFirstChernCap_divisor_comm of \
StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline, at the canonical component \
rule and the canonical divisors, registered under 0EQX as well. The equivalence is kept for its \
generality in chern, at which the key formula is the open predicate KeyFormula"]
theorem firstChernClassCap_comm_iff_isRationallyEquivalentToZero
    (hL : IsInvertibleSheaf D sX hX L) (hN : IsInvertibleSheaf D sX hX N)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ratioL : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdec L)
    (ratioN : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdec N)
    (hfinL : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec L s ratioL W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hfinN : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec N t ratioN W = 0 then ∅
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
      divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec L s ratioL W ≠ 0 →
        ∃ i, Z i = W)
    (hcoverN : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec N t ratioN W ≠ 0 →
        ∃ i, Z i = W) :
    firstChernClassCap D sX hX N k hN chernN (chowTarget.{v} D sX hX k)
          (divisorCycleAt.{u, u} D sX hX hdec L s ratioL hfinL hint dim hd hn hk) =
        firstChernClassCap D sX hX L k hL chernL (chowTarget.{v} D sX hX k)
          (divisorCycleAt.{u, u} D sX hX hdec N t ratioN hfinN hint dim hd hn hk) ↔
      IsRationallyEquivalentToZero.{v} D sX hX k
        (cycleFamilySum D sX hX
          (fun i => (Z i).toIntegralClosedSubspace D.site D.base D.base_mem) hZfin k
          (keyFormulaDivisorTerm.{u, u} D sX hX hdec L N chernL chernN Z s t ratioL ratioN
            hdim)) := by
  rw [← sub_eq_zero, ← chowClass_eq_zero_iff.{v} D sX hX k,
    ← chowClass_firstChernCapCycleMap_sub.{u, v} D sX hX hdec L N chernL chernN Z s t ratioL
      ratioN hfinL hfinN hint dim hd hn hk hZinj hZfin hdim hcoverL hcoverN]
  exact Iff.rfl

end Commutativity

end AlgebraicGeometry.Space

end

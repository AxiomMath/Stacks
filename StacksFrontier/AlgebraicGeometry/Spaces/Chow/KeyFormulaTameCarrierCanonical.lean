module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaTameCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical

/-!
# The carrier of the rational equivalence of the key formula, at the canonical embeddings

In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n = k + 2`, let `ℒ`, `𝒩` be
invertible `𝒪_X`-modules with regular meromorphic sections `s`, `t`, and let `{Z_i}` be an
injective locally finite family of prime divisors outside of which `s` and `t` generate.
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaTameCarrier` exhibits the first cycle of the
key formula of Stacks 0EQV as rationally equivalent to zero *within* the members at which the
ratio `f_i` is not `1`, so that the rational equivalence can be read on a subset of `|X|` — for
`ℒ = 𝒪_X(D)` with `s` its canonical section, on the effective Cartier divisor `D`.

It does so for `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin`, in which the
embedding `R(Z_i) → Q(𝒪^h_{Z_i,ξ})` of Stacks 0ENK on each summand is quantified existentially
with no compatibility condition between the summands.  This file states the same at the canonical
embeddings, that is for
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical`, which is the reading whose
quotient `AlgebraicGeometry.Space.chowGroupCanonical` is the source's `CH_k(X)`.

## Main results

* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_keyFormulaDivisorSum`: the
  first cycle of the key formula is rationally equivalent to zero at the canonical embeddings
  within any set containing the members at which the chosen generator of `ℒ_{ξ_i}` does not
  already have `s` for its generic value.

## Implementation notes

The proof is that of the coarse statement with one term replaced.  The summand on `Z_i` is
`AlgebraicGeometry.Space.PrimeDivisor.keyFormulaTameCycle`, which is by construction
`AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt` of the rational function
`∂_{B_i}(f_i, g_i)`, so its principal-divisor witness is the function itself and the embedding it
is read at is already the canonical one.  Where the coarse statement invokes
`AlgebraicGeometry.Space.isPrincipalDivisorCycle_canonicalPrincipalDivisorCycleAt`, which forgets
that embedding, this one invokes
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt`, which
keeps it.  Nothing else changes: the index type, the local finiteness, the containment in the
carrier, the δ-dimensions and the identification of the cycle with the sum are all independent of
the reading of `div(f)`.

The hypotheses are exactly those of the coarse statement — no hypothesis is added and none is
dropped — so whatever discharges them there discharges them here.  In particular `hcov` and
`hinj` are the hypotheses of the key formula
`AlgebraicGeometry.Space.keyFormulaDivisorSum_eq_keyFormulaTameSum` itself, and `hP` is the
source's own choice "`s_i = s` whenever `Z_i ⊄ D`".

No tag is registered here: this is a step inside the proof of Stacks 0ER9, not a statement of it,
and the key formula it rests on carries its own registration of Stacks 0EQV.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Carrier

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)
    {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    {I : Type v} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)

include hint hn in
/-- **The first cycle of the key formula is rationally equivalent to zero at the canonical
embeddings within the union of the members at which `f_i ≠ 1`.**  Stacks 0EQV presents that cycle
as the locally finite sum of the principal divisors `div(∂_{B_i}(f_i, g_i))` on the `Z_i`; the
members whose chosen generator `s_i = v_i s_{ξ_i}` has `s` for its generic value contribute
nothing, so the family of Stacks 0EQ6 part (2) presenting the rational equivalence can be taken
among the remaining members.  Each of those has δ-dimension `k + 1` by Stacks 0EPZ, and each
summand is a principal divisor **at the canonical embeddings** of Stacks 0ENK.

This is
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum` with the
reading of `div(f)` on the summands replaced by the canonical one, which is what the identity of
Stacks 0ER9 needs in order to be an identity in `AlgebraicGeometry.Space.chowGroupCanonical`
rather than in the coarser quotient; the module docstring says which single term of the proof had
to change. -/
theorem isRationallyEquivalentToZeroWithinCanonical_keyFormulaDivisorSum
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)
    (P : I → Prop)
    (hP : ∀ i, ¬ P i → (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) L hL hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s =
      algebraMap ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        ((Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (v i : ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))))
    (T : Set (points D.site D.base D.base_mem X))
    (hT : ∀ i, P i → subspacePointSet D.site D.base D.base_mem X
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace ⊆ T) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k
      (keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w) T := by
  refine ⟨{i : I // P i},
    fun j => (Zf j.1).toIntegralClosedSubspace D.site D.base D.base_mem,
    hfin.comp_injective Subtype.val_injective,
    fun j => (Zf j.1).keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn (v j.1) (w j.1),
    fun j => hT j.1 j.2,
    fun j => (deltaDimension_toIntegralClosedSubspace D sX hX hint
      (deltaDimensionFunction D sX hX) (deltaDimensionFunction_apply D sX hX) hn
      (Zf j.1)).trans (add_sub_cancel_right _ _),
    fun j => isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt D _
      (isGood_integralClosedSubspace D sX hX _)
      ((Zf j.1).toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _ _, ?_⟩
  rw [keyFormulaDivisorSum_eq_keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf v w
      hfin hinj hcov,
    keyFormulaTameSum_eq_cycleFamilySum_subtype D sX hX hint L hL s hs N hN t ht hn Zf hfin
      v w P hP]

end Carrier

end AlgebraicGeometry.Space

end

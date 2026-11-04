module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalence

/-!
# The cap product against rational equivalence at the canonical embeddings

In Situation 0EDT let `X/B` be good and let `𝒩` be invertible.  Stacks 0EQY is the assertion that
the cap product of Stacks 0EQJ factors through rational equivalence, so that it descends to

`c₁(𝒩) ∩ - : CH_{k+1}(X) ⟶ CH_k(X)`.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalence` carries out the
reassembly half over `AlgebraicGeometry.Space.chowGroup`, the quotient by the cycles rationally
equivalent to zero in the reading in which the embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK
are quantified existentially.  Its implementation notes record why the remaining summand half
cannot be discharged in that reading: the reduction of a summand to a difference of Weil
divisors runs through
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul`,
whose hypothesis holds only at the canonical embedding.

This file is the same reassembly over `AlgebraicGeometry.Space.chowGroupCanonical` at **both**
ends: the cycle rationally equivalent to zero is one of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`, so its summands arrive as
`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood` — which is what
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`
asks for — and the conclusion is in `AlgebraicGeometry.Space.chowGroupCanonical` as well.  A map
`chowGroupCanonical (k+1) →+ chowGroup k` would be provable but would weaken the conclusion, and
is not what the source states.

## Main results

* `isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_pushforwardDivisor`:
  the cap product of a cycle rationally equivalent to zero at the canonical embeddings is
  rationally equivalent to zero at the canonical embeddings, **given** the summand hypothesis.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonicalChowMap_of_pushforwardDivisor`: the
  descended operation `CH_{k+1}(X) ⟶ CH_k(X)` at the canonical embeddings on both sides, given
  the same hypothesis.

## Implementation notes

### What the summand hypothesis still waits on

The hypothesis `hdiv` below is the summand half of the proof of Stacks 0EQY, now stated entirely
at the canonical embeddings, and it is spelled out rather than named so that nothing here is a
predicate standing in for an unproved tag.  No tag is registered.

On the subspace `V` itself the vanishing it needs is available:
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`
of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPrincipalDivisorCanonical` gives
`c₁(𝒩|_V) ∩ d = 0` in the Chow group of `V` at the canonical embeddings, for exactly the
predicate `hdiv` receives.  What is missing is the step that carries that presentation out to
`X`, and of the two things that step needs the first is done.

**The transport of `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood` along an isomorphism
of good integral algebraic spaces does not go through the naturality of
the canonical embedding of Stacks 0ENK under an isomorphism** — the commuting of the square
formed
by `AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing` at a prime
divisor and at its image,
`AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIso` and
`AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRingEquivOfIso`.  That square is
**not** what the transport needs: the predicate asks only for an
identity of orders of vanishing, which
`AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_ord_of_isEtale` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor` supplies for any étale
morphism, both sides read at `AlgebraicGeometry.Space.genericFractionEmbedding`, by computing them
on one affine étale chart; an isomorphism is étale.  The transport is therefore proved,
unconditionally, as
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodIsoTransport`, and with it
the pushforward of the rational equivalence along the closed immersion `i_V` is
`exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrierCanonical`,
also unconditional, which returns a presenting family carried by `|V|` with the summands in the
canonical reading — the first of `hdiv`'s two families, exactly as `hdiv` asks for it.

What `hdiv` still waits on is the **second** family, the one measuring the difference between
capping on `X` and capping on `V`.  Reindexing the defining sum of the cap product along
`AlgebraicGeometry.Space.integralClosedSubspaceImage`
(`AlgebraicGeometry.Space.firstChernCapCycleMap_integralClosedSubspacePushforward_apply`) and
regrouping `(i_V)_*(i_{T₀})_*` as `(i_{i_V(T₀)})_*`
(`AlgebraicGeometry.Space.integralClosedSubspacePushforward_comp_pushforward`) leaves one
statement, and it is the only one left:

> For `V ⊆ X` an integral closed subspace of a good `X/B`, `𝒩` an invertible `𝒪_X`-module, `T₀ ⊆ V`
> an integral closed subspace whose image `i_V(T₀) ⊆ X` has δ-dimension `k + 1`, and `a : ℤ`, the
> cycle
> `a • (c₁(𝒩|_{i_V(T₀)}) ∩ [i_V(T₀)] - (i_V(T₀) ≅ T₀)_*(c₁((𝒩|_V)|_{T₀}) ∩ [T₀]))`
> is a principal divisor on `i_V(T₀)` in the canonical reading of part (1) of Stacks 0EQ6.

Both cycles are Weil divisors of Stacks 0EQE of **independently chosen** regular meromorphic
sections (`AlgebraicGeometry.Space.componentMeromorphicSection`, an `Exists.choose` on each of the
two spaces) of two invertible modules matched by
`AlgebraicGeometry.Space.integralClosedSubspaceRestrictPushforwardIso`, so the statement is Stacks
0EPT once the two are brought onto one space; the inputs for that are
`AlgebraicGeometry.Space.canonicalDivisorCycleAt_pushforwardOfIso`,
`AlgebraicGeometry.Space.canonicalDivisorCycleAt_sectionsMap_iso` and
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub`.  On top
of it `hdiv` needs only bookkeeping: that `{|i_V(T₀)| : d(T₀) ≠ 0}` is locally finite, which is
local finiteness of the support of the cycle `d` pushed along a closed embedding, and the
concatenation of the two families, which is Stacks 0EQ8.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k)

/-- The cap product with the first Chern class of a `(k+1)`-cycle rationally equivalent to zero
at the canonical embeddings of Stacks 0ENK is rationally equivalent to zero at the canonical
embeddings, **given** that the cap product of the pushforward `(i_V)_* div(g)` of a principal
divisor from an integral closed subspace `V ⊆ X` of δ-dimension `k + 2` is presented as a sum of
principal divisors — all read at the canonical embeddings — over a locally finite family of
integral closed subspaces of `X` of δ-dimension `k + 1` whose point sets lie in `|V|`.

What is proved is the reassembly:
`AlgebraicGeometry.Space.firstChernCapCycleMap_cycleFamilySum_apply` turns the cap product of the
presenting sum into the locally finite sum of the cap products of its summands, the combined family
indexed by `Σ j, K j` is locally finite by Stacks 0EQ8, since each of its members lies in the
corresponding `|W_j|`, and the identity of coefficients is the reindexing of a sum over that sigma
type as an iterated sum. This is the proof of
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_firstChernCapCycleMap_of_pushforwardDivisor`
with both readings of rational equivalence replaced by the canonical one. -/
theorem isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_pushforwardDivisor
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX V) V.isIntegralSpace (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycleOfGood D ((U l).subspace.ι ≫ sX)
                  (isGood_integralClosedSubspace D sX hX (U l)) (U l).isIntegralSpace k (e l)) ∧
                  firstChernCapCycleMap D sX hX k chern
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e)
    {α : CycleGroup D sX (k + 1)}
    (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX (k + 1) α) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX k
      (firstChernCapCycleMap D sX hX k chern α) := by
  obtain ⟨J, W, hWfin, c, hdim, hprin, hsum⟩ := hα
  choose K U hUfin e hsub hUdim hUprin heq using
    fun j : J => hdiv (W j) (hdim j) (c j) (hprin j)
  have hVfin : LocallyFinite fun s : (j : J) × K j =>
      subspacePointSet D.site D.base D.base_mem X (U s.1 s.2).subspace :=
    locallyFinite_sigma_of_subset hWfin hUfin hsub
  refine ⟨(j : J) × K j, fun s => U s.1 s.2, hVfin, fun s => e s.1 s.2,
    fun s => hUdim s.1 s.2, fun s => hUprin s.1 s.2, Subtype.ext (funext fun T => ?_)⟩
  have hterm : ∀ j : J, (firstChernCapCycleMap D sX hX k chern
      (integralClosedSubspacePushforward D sX hX (W j) (k + 1) (c j))).1 T =
        ∑ᶠ l : K j,
          (integralClosedSubspacePushforward D sX hX (U j l) k (e j l)).1 T := fun j => by
    rw [heq j]
    exact cycleFamilySum_apply D sX hX (U j) (hUfin j) k (e j) T
  rw [hsum, firstChernCapCycleMap_cycleFamilySum_apply D sX hX k chern W hWfin c T,
    finsum_congr hterm]
  exact (Stacks.Chow.finsum_sigma (fun s : (j : J) × K j =>
    (integralClosedSubspacePushforward D sX hX (U s.1 s.2) k (e s.1 s.2)).1 T)
    (finite_support_cycleFamilyCoeff D sX hX (fun s : (j : J) × K j => U s.1 s.2) hVfin k
      (fun s => e s.1 s.2) T)).symm

/-- The class at the canonical embeddings of the cap product of a `(k+1)`-cycle rationally
equivalent to zero at the canonical embeddings vanishes, **given the summand hypothesis** of
`isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_pushforwardDivisor`.
This is the hypothesis of `AlgebraicGeometry.Space.chowGroupCanonicalLift`. -/
theorem chowClassCanonical_firstChernCapCycleMap_eq_zero_of_pushforwardDivisor
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX V) V.isIntegralSpace (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycleOfGood D ((U l).subspace.ι ≫ sX)
                  (isGood_integralClosedSubspace D sX hX (U l)) (U l).isIntegralSpace k (e l)) ∧
                  firstChernCapCycleMap D sX hX k chern
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e)
    (α : CycleGroup D sX (k + 1))
    (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX (k + 1) α) :
    chowClassCanonical.{v} D sX hX k (firstChernCapCycleMap D sX hX k chern α) = 0 :=
  (chowClassCanonical_eq_zero_iff.{v} D sX hX k _).2
    (isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_pushforwardDivisor.{v} D sX hX
      k chern hdiv hα)

/-! ### The descent at the canonical embeddings on both sides -/

section Canonical

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQY at the canonical embeddings, given the summand hypothesis.**  The cap product
`c₁(𝒩) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)` of Stacks 0EQJ descends to

`c₁(𝒩) ∩ - : CH_{k+1}(X) ⟶ CH_k(X)`,

with `CH_*(X)` the Chow group `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6 read at
the canonical embeddings of Stacks 0ENK **on both sides** — the source's group, and the one whose
summands the vanishing of
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`
applies to.

The descent is `AlgebraicGeometry.Space.chowGroupCanonicalLift`, and the hypothesis it needs is
`AlgebraicGeometry.Space.chowClassCanonical_firstChernCapCycleMap_eq_zero_of_pushforwardDivisor`
at the canonical component rule of Stacks 0EQJ.  This is not a registration of Stacks 0EQY; see
the module docstring for the one statement that is left. -/
def canonicalFirstChernCapCanonicalChowMap_of_pushforwardDivisor
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX V) V.isIntegralSpace (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycleOfGood D ((U l).subspace.ι ≫ sX)
                  (isGood_integralClosedSubspace D sX hX (U l)) (U l).isIntegralSpace k (e l)) ∧
                  firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e) :
    chowGroupCanonical.{v} D sX hX (k + 1) →+ chowGroupCanonical.{v} D sX hX k :=
  chowGroupCanonicalLift D sX hX (k + 1) (canonicalFirstChernCapCanonical.{v} D sX hX N hN k)
    (chowClassCanonical_firstChernCapCycleMap_eq_zero_of_pushforwardDivisor.{v} D sX hX k
      (canonicalFirstChernRule D sX hX N hN k) hdiv)

/-- The descended operation agrees with the cap product of Stacks 0EQJ on the class of a cycle,
which is what makes it a factorization through rational equivalence. -/
theorem canonicalFirstChernCapCanonicalChowMap_of_pushforwardDivisor_chowClassCanonical
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX V) V.isIntegralSpace (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem X (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
                subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D sX (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycleOfGood D ((U l).subspace.ι ≫ sX)
                  (isGood_integralClosedSubspace D sX hX (U l)) (U l).isIntegralSpace k (e l)) ∧
                  firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
                      (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
                    cycleFamilySum D sX hX U hUfin k e)
    (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapCanonicalChowMap_of_pushforwardDivisor.{v} D sX hX k N hN hdiv
        (chowClassCanonical.{v} D sX hX (k + 1) α) =
      canonicalFirstChernCapCanonical.{v} D sX hX N hN k α :=
  rfl

end Canonical

end AlgebraicGeometry.Space

end

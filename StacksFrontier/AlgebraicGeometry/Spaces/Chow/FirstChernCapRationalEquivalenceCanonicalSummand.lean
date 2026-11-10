module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrierCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPrincipalDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPushforwardReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernRuleSubspaceImagePrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical

/-!
# Stacks 0EQY: the cap product with the first Chern class factors through rational equivalence

In Situation 0EDT let `X/B` be good and let `𝒩` be an invertible `𝒪_X`-module.  Stacks 0EQY is
the assertion that the cap product `c₁(𝒩) ∩ - : Z_{k+1}(X) ⟶ Z_k(X)` of Stacks 0EQJ carries a
cycle rationally equivalent to zero to a cycle rationally equivalent to zero, so that it descends
to

`c₁(𝒩) ∩ - : CH_{k+1}(X) ⟶ CH_k(X)`.

Both Chow groups are `AlgebraicGeometry.Space.chowGroupCanonical`, the quotient of Stacks 0EQ6
read at the canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK — the source's own group,
since part (2) of Stacks 0EQ6 asks for summands `div(f_j)` with `f_j ∈ R(W_j)^*` and `div` is a
function of `f_j` alone.  A conclusion in the coarser `AlgebraicGeometry.Space.chowGroup`, where
that family of embeddings is quantified existentially with no compatibility condition between the
summands, would be a weaker statement, and there is no way back:
`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood.isPrincipalDivisorCycle` runs one way only.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonical` carries out
the reassembly over the presenting family of the rational equivalence, leaving one hypothesis
`hdiv`: that the cap product of the pushforward `(i_V)_* d` of a principal divisor cycle `d` from
an integral closed subspace `V ⊆ X` of δ-dimension `k + 2` is itself presented, inside `|V|`, as
a locally finite sum of principal divisors at the canonical embeddings.  This file proves `hdiv`,
and with it the tag.

## Main results

* `AlgebraicGeometry.Space.firstChernCapCycleMap_integralClosedSubspacePushforward_eq_add`: the
  cap product over `(i_V)_* d` split into `(i_V)_*(c₁(𝒩|_V) ∩ d)` plus a locally finite family
  supported on the images of the subspaces occurring in `d`.  For arbitrary component rules.
* The theorem of section `Tag` whose name ends in `_integralClosedSubspacePushforward`: the
  summand statement `hdiv`, unconditional.
* `isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule`:
  **Stacks 0EQY** at the level of cycles.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonicalChowMap`: **Stacks 0EQY** — the
  descended operation `CH_{k+1}(X) ⟶ CH_k(X)`, together with
  `AlgebraicGeometry.Space.canonicalFirstChernCapCanonicalChowMap_chowClassCanonical`, which says
  that it agrees with the cap product of Stacks 0EQJ on the class of a cycle.

## Implementation notes

### The proof of the summand statement

Write `i_V : V ⟶ X` for the inclusion, `𝒩|_V` for the restriction and `d ∈ Z_{k+1}(V)` for the
principal divisor cycle.  The coefficient of `c₁(𝒩) ∩ (i_V)_* d` at an integral closed subspace
`T ⊆ X` is

`∑_{T₀ ⊆ V} d(T₀) · (c₁(𝒩) ∩ [i_V(T₀)])(T)`

by `AlgebraicGeometry.Space.firstChernCapCycleMap_integralClosedSubspacePushforward_apply`, the
sum running over the integral closed subspaces of `V`, with `i_V(T₀)` the image
`AlgebraicGeometry.Space.integralClosedSubspaceImage`.  Each term is split as

`d(T₀) · ((i_V)_*(c₁(𝒩|_V) ∩ [T₀]))(T) + d(T₀) · (c₁(𝒩) ∩ [i_V(T₀)] - (i_V)_*(c₁(𝒩|_V) ∩ [T₀]))(T)`

and the two sums are separated by `finsum_add_distrib`.  The sum of the first halves is the
coefficient of `(i_V)_*(c₁(𝒩|_V) ∩ d)` at `T`: at `T = i_V(T')` because a pushforward reads off
coefficients at images, and off the image of `V` because then both sides vanish.  That cycle is
rationally equivalent to zero within `|V|`, by
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`
on `V` — which is where `d` being a principal divisor at the canonical embeddings is used, and
the only place — followed by
`exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward`. The
second sum is the family `AlgebraicGeometry.Space.subspaceImageChernDifference` below, indexed
by the support of `d`: its member at `T₀` is a principal divisor at the canonical embeddings on
`i_V(T₀)` by
`isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_pushforwardCycleTransport` (Stacks
0EPT, once both component cycles are read on one space), its members have δ-dimension
`k + 1` by `AlgebraicGeometry.Space.deltaDimension_integralClosedSubspaceImage` and point sets
inside `|V|`, and the family is locally finite because `d` is a cycle.  The two presenting
families are concatenated by
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical.add`, which is Stacks 0EQ8
for a two-element index type.

The splitting itself asks nothing of the component rules and nothing of `d` beyond its being a
cycle, so it is proved here for arbitrary rules on `X` and on `V`; only the two facts about the
members — that they are principal divisors, and that the first family exists — are special to
`AlgebraicGeometry.Space.canonicalFirstChernRule`.

### Corrections to notes in this tree

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalFunctionsTransport` say, under what that file
does not do, that the multiplicity `m = 1` is unavailable and that the order of vanishing at a
prime divisor and at its image under an isomorphism are therefore not yet identified.  That is
**false**: `AlgebraicGeometry.Space.PrimeDivisor.ord_pushforwardOfIso` and
`AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_ord_of_isEtale` identify them, and the second
is what `AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso`
rests on — a lemma used twice in the chain above, so the proof below depends on the
identification the note calls unavailable.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums` carries the carrier layer
only at the coarse `AlgebraicGeometry.Space.IsPrincipalDivisorCycle`, so neither
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_finsum` nor
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_finsum` can be used here; the canonical
counterpart is in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical`.

### The universe of the index type

The presenting families are indexed by types of integral closed subspaces, which live one
universe above the site's, so the Chow groups here are
`AlgebraicGeometry.Space.chowGroupCanonical.{u + 1}`.  That is the universe in which the vanishing
input `canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood` is stated, and
the one in which `AlgebraicGeometry.Space.canonicalFirstChernCap_eq_chowClass_cycleFamilySum`
presents a cap product as a sum of Stacks 0EQ6, part (1).

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Two pieces of `finsum` algebra -/

section Finsum

variable {ι : Type*} (w f g : ι → ℤ)

/-- A point of the support of a family of weighted differences lies in the support of the
weight. -/
private theorem weight_ne_zero_of_mem_support_weight_mul_sub {x : ι}
    (hx : x ∈ Function.support fun i : ι => w i * f i - w i * g i) : w x ≠ 0 := fun h0 =>
  Function.mem_support.1 hx (by rw [h0, zero_mul, zero_mul, sub_zero])

/-- A sum of weighted differences over the support of the weight is the sum over everything,
every term off the support of the weight being zero. -/
theorem finsum_subtype_support_weight_mul_sub :
    (∑ᶠ j : {i : ι // w i ≠ 0}, (w j.1 * f j.1 - w j.1 * g j.1)) =
      ∑ᶠ i : ι, (w i * f i - w i * g i) := by
  classical
  have hmem : ∀ x ∈ Function.support fun i : ι => w i * f i - w i * g i,
      x ∈ (Set.univ : Set ι) ↔
        x ∈ Set.range (Subtype.val : {i : ι // w i ≠ 0} → ι) := by
    intro x hx
    exact ⟨fun _ => ⟨⟨x, weight_ne_zero_of_mem_support_weight_mul_sub w f g hx⟩, rfl⟩,
      fun _ => Set.mem_univ x⟩
  rw [← finsum_mem_range (f := fun i : ι => w i * f i - w i * g i) Subtype.val_injective,
    ← finsum_mem_inter_support_eq' (fun i : ι => w i * f i - w i * g i) Set.univ _ hmem,
    finsum_mem_univ]

/-- A family of weighted differences has finite support as soon as its restriction to the support
of the weight does. -/
theorem hasFiniteSupport_weight_mul_sub_of_subtype
    (h : (Function.support fun j : {i : ι // w i ≠ 0} =>
      w j.1 * f j.1 - w j.1 * g j.1).Finite) :
    Function.HasFiniteSupport fun i : ι => w i * f i - w i * g i := by
  refine (h.image Subtype.val).subset fun x hx => ?_
  exact ⟨⟨x, weight_ne_zero_of_mem_support_weight_mul_sub w f g hx⟩, hx, rfl⟩

end Finsum

/-! ### Concatenating two rational equivalences with a common carrier -/

section Add

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α β : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}

/-- **Stacks 0EQ8 for two summands, at the canonical embeddings, with a common carrier.**  The
sum of two cycles each rationally equivalent to zero within a subset `T` of `|X|` is rationally
equivalent to zero within `T`, via the disjoint union of the two presenting families: the
disjoint union of two locally finite families is locally finite, and the coefficient of the
combined sum splits by `Stacks.Chow.finsum_sum_elim`, the two partial sums having finite support
at each integral closed subspace because each family is locally finite.

This is `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_add` with the carrier
carried along, and it is the concatenation step in the proof of Stacks 0EQY. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.add
    (hα : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T)
    (hβ : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k β T) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k (α + β) T := by
  obtain ⟨J, W, hWfin, c, hWsub, hWdim, hWprin, hWsum⟩ := hα
  obtain ⟨K, U, hUfin, e, hUsub, hUdim, hUprin, hUsum⟩ := hβ
  have hfin : LocallyFinite fun s : J ⊕ K =>
      subspacePointSet D.site D.base D.base_mem X (Sum.elim W U s).subspace := by
    have hsets : (fun s : J ⊕ K =>
        subspacePointSet D.site D.base D.base_mem X (Sum.elim W U s).subspace) =
        Sum.elim (fun j => subspacePointSet D.site D.base D.base_mem X (W j).subspace)
          (fun l => subspacePointSet D.site D.base D.base_mem X (U l).subspace) :=
      funext fun s => by cases s <;> rfl
    rw [hsets]
    exact hWfin.sumElim hUfin
  refine ⟨J ⊕ K, Sum.elim W U, hfin,
    (fun s => match s with | .inl j => c j | .inr l => e l),
    (fun s => match s with | .inl j => hWsub j | .inr l => hUsub l),
    (fun s => match s with | .inl j => hWdim j | .inr l => hUdim l),
    (fun s => match s with | .inl j => hWprin j | .inr l => hUprin l), ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  have hsplit : (fun s : J ⊕ K => (integralClosedSubspacePushforward D sX hX
        (Sum.elim W U s) k (match s with | .inl j => c j | .inr l => e l)).1 Z) =
      Sum.elim (fun j => (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z)
        (fun l => (integralClosedSubspacePushforward D sX hX (U l) k (e l)).1 Z) :=
    funext fun s => by cases s <;> rfl
  change (α + β).1 Z = _
  rw [cycleFamilySum_apply, hsplit, Stacks.Chow.finsum_sum_elim _ _
      (finite_support_cycleFamilyCoeff D sX hX W hWfin k c Z)
      (finite_support_cycleFamilyCoeff D sX hX U hUfin k e Z), hWsum, hUsum]
  change (cycleFamilySum D sX hX W hWfin k c).1 Z + (cycleFamilySum D sX hX U hUfin k e).1 Z = _
  rw [cycleFamilySum_apply, cycleFamilySum_apply]

end Add

/-! ### The case the reduction produces: a principal divisor on an integral space -/

section Integral

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ)

/-- **`c₁(𝒩) ∩ div(f)` is rationally equivalent to zero at the canonical embeddings**, for `X/B`
good and integral with `dim_δ(X) = k + 2` and `div(f)` a principal divisor cycle in the canonical
reading of part (1) of Stacks 0EQ6.

This is
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`
read through `AlgebraicGeometry.Space.chowClassCanonical_eq_zero_iff`, with the δ-dimension
written as `k + 2` rather than as an `n` with `k = n - 2`.  That is the form the reduction of
Stacks 0EQY produces it in, the subspace carrying the principal divisor having δ-dimension one
more than the dimension of the cycle. -/
theorem isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_isPrincipalDivisorCycleOfGood
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (d : CycleGroup D sX (k + 1))
    (hd : IsPrincipalDivisorCycleOfGood D sX hX hint (k + 1) d) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) d) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, k = m - 2 := ⟨k + 2, by ring⟩
  rw [show m - 2 + 1 + 1 = m from by ring] at hdim
  exact (chowClassCanonical_eq_zero_iff.{u + 1} D sX hX (m - 2) _).1
    (canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood D sX hX hint N hN
      hdim d hd)

end Integral

/-! ### The cap product over a cycle pushed forward from an integral closed subspace -/

section Split

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hVg : D.IsGood (V.subspace.ι ≫ sX))
    (chernX : FirstChernComponentCycleRule D sX k)
    (chernV : FirstChernComponentCycleRule D (V.subspace.ι ≫ sX) k)
    (d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1))

/-- The coefficient, at the image of `T' ⊆ V`, of a cycle pushed forward from `V`. -/
theorem integralClosedSubspacePushforward_apply_integralClosedSubspaceImage
    (c : CycleGroup D (V.subspace.ι ≫ sX) k) (T' : IntegralClosedSubspace D.site D.base D.base_mem
        V.subspace.toFunctor) :
    (integralClosedSubspacePushforward D sX hX V k c).1
        (integralClosedSubspaceImage D sX hX V T') = c.1 T' :=
  integralClosedSubspacePushforward_apply_pushforward D sX hX V c T'

/-- A cycle pushed forward from `V` has coefficient zero at an integral closed subspace of `X`
which is not the image of one of `V`. -/
theorem integralClosedSubspacePushforward_apply_eq_zero_of_forall_ne_image
    (c : CycleGroup D (V.subspace.ι ≫ sX) k) (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor,
        integralClosedSubspaceImage D sX hX V T' ≠ T) :
    (integralClosedSubspacePushforward D sX hX V k c).1 T = 0 :=
  integralClosedSubspacePushforward_apply_of_forall_ne D sX hX V c T hT

/-- Pushing a cycle on `T₀ ⊆ V` to the image `i_V(T₀) ⊆ X` and then to `X` is pushing it to `V`
and then to `X`.  This is
`AlgebraicGeometry.Space.integralClosedSubspacePushforward_comp_pushforward` with the image
written as `AlgebraicGeometry.Space.integralClosedSubspaceImage`. -/
theorem integralClosedSubspacePushforward_pushforwardCycleTransport (T₀ : IntegralClosedSubspace
    D.site D.base D.base_mem V.subspace.toFunctor)
    (c : CycleGroup D (T₀.subspace.ι ≫ (V.subspace.ι ≫ sX)) k) :
    integralClosedSubspacePushforward D sX hX (integralClosedSubspaceImage D sX hX V T₀) k
        (IntegralClosedSubspace.pushforwardCycleTransport D sX hX V.isClosedSubspace.1
          V.isClosedSubspace.2 T₀ k c) =
      integralClosedSubspacePushforward D sX hX V k
        (integralClosedSubspacePushforward D (V.subspace.ι ≫ sX) hVg T₀ k c) :=
  (integralClosedSubspacePushforward_comp_pushforward D sX hX V T₀ k c).symm

/-- **The member at `T₀` of the second presenting family of the summand statement of
Stacks 0EQY.**  For `T₀ ⊆ V` with `d(T₀) ≠ 0` — so that `dim_δ(T₀) = k + 1`, and the image
`i_V(T₀) ⊆ X` has δ-dimension `k + 1` as well — it is `d(T₀)` times the difference between the
component cycle of Stacks 0EQJ attached to `i_V(T₀)` on `X` and the one attached to `T₀` on `V`,
carried to the image.

For the canonical rules of `AlgebraicGeometry.Space.canonicalFirstChernRule` the two differ
because each is the Weil divisor of Stacks 0EQE of a regular meromorphic section chosen
independently on the two spaces, and their difference is a principal divisor on `i_V(T₀)` by
Stacks 0EPT; see
`isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_pushforwardCycleTransport`. -/
def subspaceImageChernDifference (j : {T₀ : IntegralClosedSubspace D.site D.base D.base_mem
    V.subspace.toFunctor // d.1 T₀ ≠ 0}) :
    CycleGroup D ((integralClosedSubspaceImage D sX hX V j.1).subspace.ι ≫ sX) k :=
  d.1 j.1 • (chernX (integralClosedSubspaceImage D sX hX V j.1)
        ((deltaDimension_integralClosedSubspaceImage D sX hX V j.1).trans (d.2.2 j.1 j.2)) -
      IntegralClosedSubspace.pushforwardCycleTransport D sX hX V.isClosedSubspace.1
        V.isClosedSubspace.2 j.1 k (chernV j.1 (d.2.2 j.1 j.2)))

/-- The second presenting family is locally finite: it is the family of images of the integral
closed subspaces at which `d` has a nonzero coefficient, which is locally finite because `d` is a
cycle, and taking images along the closed immersion `i_V` preserves local finiteness. -/
theorem locallyFinite_subspaceImageChernDifference :
    LocallyFinite fun j : {T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor
        // d.1 T₀ ≠ 0} =>
      subspacePointSet D.site D.base D.base_mem X
        (integralClosedSubspaceImage D sX hX V j.1).subspace :=
  locallyFinite_subspacePointSet_integralClosedSubspaceImage D sX hX V Subtype.val
    (locallyFinite_cycleSupport d)

/-- The member at `T₀` of the second presenting family, pushed out to `X`, is `d(T₀)` times the
difference of the two component cycles of Stacks 0EQJ which the defining sum of the cap product
over `(i_V)_* d` involves: the one on `X` at `i_V(T₀)`, and the one on `V` at `T₀` pushed out
to `X`. -/
theorem integralClosedSubspacePushforward_subspaceImageChernDifference
    (j : {T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor // d.1 T₀ ≠
        0}) :
    integralClosedSubspacePushforward D sX hX (integralClosedSubspaceImage D sX hX V j.1) k
        (subspaceImageChernDifference D sX hX k V chernX chernV d j) =
      d.1 j.1 • (firstChernComponentCycle D sX hX k chernX
            (integralClosedSubspaceImage D sX hX V j.1) -
          integralClosedSubspacePushforward D sX hX V k
            (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV j.1)) := by
  rw [subspaceImageChernDifference, map_zsmul, map_sub,
    firstChernComponentCycle_of_deltaDimension_eq D sX hX k chernX
      ((deltaDimension_integralClosedSubspaceImage D sX hX V j.1).trans (d.2.2 j.1 j.2)),
    firstChernComponentCycle_of_deltaDimension_eq D (V.subspace.ι ≫ sX) hVg k chernV (d.2.2 j.1
        j.2),
    integralClosedSubspacePushforward_pushforwardCycleTransport D sX hX k V hVg j.1
      (chernV j.1 (d.2.2 j.1 j.2))]

/-- **The cap product over a cycle pushed forward from an integral closed subspace, split into
its two presentable halves.**  For `V ⊆ X` an integral closed subspace of a good `X/B`, component
rules on `X` and on `V`, and `d ∈ Z_{k+1}(V)`,

`c₁ ∩ (i_V)_* d = (i_V)_*(c₁|_V ∩ d) + ∑_{T₀} d(T₀) · (c₁ ∩ [i_V(T₀)] - (i_V)_*(c₁|_V ∩ [T₀]))`,

the sum running over the integral closed subspaces of `V` at which `d` has a nonzero
coefficient.

Nothing is assumed of the rules and nothing of `d` beyond its being a cycle: this is the
coefficient bookkeeping of the proof of Stacks 0EQY and it contains no geometry.  The two sides
are compared at a fixed `T ⊆ X`; the left one is a sum over the integral closed subspaces of `V`
by `AlgebraicGeometry.Space.firstChernCapCycleMap_integralClosedSubspacePushforward_apply`, each
term splits as a difference, and the two sums are separated by `finsum_add_distrib`. -/
theorem firstChernCapCycleMap_integralClosedSubspacePushforward_eq_add :
    firstChernCapCycleMap D sX hX k chernX
        (integralClosedSubspacePushforward D sX hX V (k + 1) d) =
      integralClosedSubspacePushforward D sX hX V k
          (firstChernCapCycleMap D (V.subspace.ι ≫ sX) hVg k chernV d) +
        cycleFamilySum D sX hX
          (fun j : {T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor // d.1
              T₀ ≠ 0} => integralClosedSubspaceImage D sX hX V j.1)
          (locallyFinite_subspaceImageChernDifference D sX hX k V d) k
          (subspaceImageChernDifference D sX hX k V chernX chernV d) := by
  classical
  refine Subtype.ext (funext fun T => ?_)
  have hadd : ∀ c c' : CycleGroup D sX k, (c + c').1 T = c.1 T + c'.1 T := fun _ _ => rfl
  have hsmul : ∀ (a : ℤ) (c c' : CycleGroup D sX k),
      (a • (c - c')).1 T = a * c.1 T - a * c'.1 T := fun a c c' => by
    simp [Pi.smul_apply, mul_sub]
  -- the member of the second family at `T₀`, read off at `T`
  have hFd : ∀ j : {T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor // d.1
      T₀ ≠ 0},
      (integralClosedSubspacePushforward D sX hX (integralClosedSubspaceImage D sX hX V j.1) k
          (subspaceImageChernDifference D sX hX k V chernX chernV d j)).1 T =
        d.1 j.1 * (firstChernComponentCycle D sX hX k chernX
            (integralClosedSubspaceImage D sX hX V j.1)).1 T -
          d.1 j.1 * (integralClosedSubspacePushforward D sX hX V k
            (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV j.1)).1 T := fun j => by
    rw [integralClosedSubspacePushforward_subspaceImageChernDifference D sX hX k V hVg chernX
      chernV d j]
    exact hsmul _ _ _
  -- the sum of the first halves is the coefficient of `(i_V)_*(c₁|_V ∩ d)` at `T`
  have hhalf : Function.HasFiniteSupport (fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem
      V.subspace.toFunctor =>
        d.1 T₀ * (integralClosedSubspacePushforward D sX hX V k
          (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀)).1 T) ∧
      (integralClosedSubspacePushforward D sX hX V k
          (firstChernCapCycleMap D (V.subspace.ι ≫ sX) hVg k chernV d)).1 T =
        ∑ᶠ T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor, d.1 T₀ *
            (integralClosedSubspacePushforward D sX hX V k
          (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀)).1 T := by
    by_cases hex : ∃ T' : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor,
        integralClosedSubspaceImage D sX hX V T' = T
    · obtain ⟨T', rfl⟩ := hex
      have heq : (fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor =>
          d.1 T₀ *
            (integralClosedSubspacePushforward D sX hX V k
              (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀)).1
                (integralClosedSubspaceImage D sX hX V T')) =
          fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor =>
            d.1 T₀ * (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀).1 T' :=
        funext fun T₀ => by
          rw [integralClosedSubspacePushforward_apply_integralClosedSubspaceImage D sX hX k V
            (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀) T']
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact hasFiniteSupport_firstChernCapCoeff D (V.subspace.ι ≫ sX) hVg k chernV d T'
      · rw [heq, integralClosedSubspacePushforward_apply_integralClosedSubspaceImage D sX hX k V
          (firstChernCapCycleMap D (V.subspace.ι ≫ sX) hVg k chernV d) T',
              firstChernCapCycleMap_apply]
    · have hne : ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor,
        integralClosedSubspaceImage D sX hX V T' ≠ T :=
        fun T' h => hex ⟨T', h⟩
      have heq : (fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor =>
          d.1 T₀ *
            (integralClosedSubspacePushforward D sX hX V k
              (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀)).1 T) =
          fun _ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor => (0 : ℤ) :=
        funext fun T₀ => by
          rw [integralClosedSubspacePushforward_apply_eq_zero_of_forall_ne_image D sX hX k V
            (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀) T hne, mul_zero]
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact Set.Finite.subset Set.finite_empty (by simp [Function.support])
      · rw [heq, integralClosedSubspacePushforward_apply_eq_zero_of_forall_ne_image D sX hX k V
          (firstChernCapCycleMap D (V.subspace.ι ≫ sX) hVg k chernV d) T hne, finsum_zero]
  obtain ⟨hhalffin, hhalfsum⟩ := hhalf
  -- the second family has finite support at `T`
  have hdifffin : Function.HasFiniteSupport fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem
      V.subspace.toFunctor =>
      d.1 T₀ * (firstChernComponentCycle D sX hX k chernX
          (integralClosedSubspaceImage D sX hX V T₀)).1 T -
        d.1 T₀ * (integralClosedSubspacePushforward D sX hX V k
          (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀)).1 T := by
    refine hasFiniteSupport_weight_mul_sub_of_subtype d.1
      (fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor =>
          (firstChernComponentCycle D sX hX k chernX
        (integralClosedSubspaceImage D sX hX V T₀)).1 T)
      (fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor =>
          (integralClosedSubspacePushforward D sX hX V k
        (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀)).1 T)
      ((finite_support_cycleFamilyCoeff D sX hX
        (fun j : {T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor // d.1
            T₀ ≠ 0} => integralClosedSubspaceImage D sX hX V j.1)
        (locallyFinite_subspaceImageChernDifference D sX hX k V d) k
        (subspaceImageChernDifference D sX hX k V chernX chernV d) T).subset fun j hj => ?_)
    rw [Function.mem_support, hFd j]
    exact hj
  rw [firstChernCapCycleMap_integralClosedSubspacePushforward_apply D sX hX V k chernX d T, hadd,
    cycleFamilySum_apply, finsum_congr hFd,
    finsum_subtype_support_weight_mul_sub d.1
      (fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor =>
          (firstChernComponentCycle D sX hX k chernX
        (integralClosedSubspaceImage D sX hX V T₀)).1 T)
      (fun T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor =>
          (integralClosedSubspacePushforward D sX hX V k
        (firstChernComponentCycle D (V.subspace.ι ≫ sX) hVg k chernV T₀)).1 T),
    hhalfsum, ← finsum_add_distrib hhalffin hdifffin]
  exact finsum_congr fun T₀ => by ring

end Split

/-! ### Stacks 0EQY -/

section Tag

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **The summand statement of Stacks 0EQY, unconditional.**  For `V ⊆ X` an integral closed
subspace of δ-dimension `k + 2` of a good `X/B`, `𝒩` an invertible `𝒪_X`-module and
`d ∈ Z_{k+1}(V)` a principal divisor cycle in the canonical reading of part (1) of Stacks 0EQ6,
the cap product `c₁(𝒩) ∩ (i_V)_* d` is rationally equivalent to zero at the canonical embeddings
of Stacks 0ENK, by a presenting family whose members have point sets inside `|V|`.

This is exactly the hypothesis `hdiv` of
`isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_pushforwardDivisor` at the
canonical component rule of Stacks 0EQJ: the definition of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical` unfolds to it.

The splitting is
`AlgebraicGeometry.Space.firstChernCapCycleMap_integralClosedSubspacePushforward_eq_add`; the
first family is the one
`exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward` returns
for `(i_V)_*(c₁(𝒩|_V) ∩ d)`, which is a pushforward of a cycle rationally equivalent to zero on
`V`; the second is
`AlgebraicGeometry.Space.subspaceImageChernDifference`; and the concatenation is
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical.add`. -/
theorem
isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_integralClosedSubspacePushforward
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (d : CycleGroup D (V.subspace.ι ≫ sX) (k + 1)) (hV : deltaDimension D sX V = k + 1 + 1)
    (hd : IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX
        V) V.isIntegralSpace (k + 1) d) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
        (integralClosedSubspacePushforward D sX hX V (k + 1) d))
      (subspacePointSet D.site D.base D.base_mem X V.subspace) := by
  rw [firstChernCapCycleMap_integralClosedSubspacePushforward_eq_add D sX hX k V
    (isGood_integralClosedSubspace D sX hX V) (canonicalFirstChernRule D sX hX N hN k)
    (canonicalFirstChernRule D (V.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX V)
        (integralClosedSubspaceRestrict D sX hX N V)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) k) d]
  refine IsRationallyEquivalentToZeroWithinCanonical.add ?_ ?_
  · have h :=
      isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_isPrincipalDivisorCycleOfGood
        D (V.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX V) V.isIntegralSpace
        (integralClosedSubspaceRestrict D sX hX N V)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) k
        (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX V, hV]) d hd
    obtain ⟨K, U, hUfin, e, hsub, hdim, hprin, heq⟩ :=
      exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward.{u +
          1}
        D sX hX V.subspace V.isClosedSubspace k h
    exact ⟨K, U, hUfin, e, hsub, hdim, hprin, heq⟩
  · refine ⟨{T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor // d.1 T₀ ≠
      0},
      (fun j => integralClosedSubspaceImage D sX hX V j.1),
      locallyFinite_subspaceImageChernDifference D sX hX k V d,
      subspaceImageChernDifference D sX hX k V (canonicalFirstChernRule D sX hX N hN k)
        (canonicalFirstChernRule D (V.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX V)
            (integralClosedSubspaceRestrict D sX hX N V)
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) k) d,
      (fun j => subspacePointSet_integralClosedSubspaceImage_subset D sX hX V j.1),
      (fun j => (deltaDimension_integralClosedSubspaceImage D sX hX V j.1).trans
        (d.2.2 j.1 j.2)), fun j => ?_, rfl⟩
    exact isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_pushforwardCycleTransport
      D sX hX V j.1 N hN k
      ((deltaDimension_integralClosedSubspaceImage D sX hX V j.1).trans (d.2.2 j.1 j.2))
      (d.1 j.1)

/-- **Stacks 0EQY at the level of cycles.**  For `X/B` good and `𝒩` an invertible `𝒪_X`-module,
the cap product `c₁(𝒩) ∩ - : Z_{k+1}(X) ⟶ Z_k(X)` of Stacks 0EQJ carries a `(k+1)`-cycle
rationally equivalent to zero to a `k`-cycle rationally equivalent to zero, both in the sense of
part (2) of Stacks 0EQ6 read at the canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK.

Nothing is assumed.  The reassembly over the presenting family of the rational equivalence is
`isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_pushforwardDivisor`, and the
summand statement it asks for is the previous theorem. -/
@[stacks 0EQY "the cap product with the first Chern class is compatible with rational \
equivalence, at the level of cycles: it carries a cycle rationally equivalent to zero to a cycle \
rationally equivalent to zero, both read at the canonical embeddings of Stacks 0ENK"]
theorem isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule
    {α : CycleGroup D sX (k + 1)}
    (hα : IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX (k + 1) α) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) α) :=
  isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_of_pushforwardDivisor.{u + 1} D sX hX
    k (canonicalFirstChernRule D sX hX N hN k)
    (fun V hV d hd =>
isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_integralClosedSubspacePushforward
        D sX hX k N hN V d hV hd) hα

/-- **Stacks 0EQY.**  The cap product of Stacks 0EQJ descends to

`c₁(𝒩) ∩ - : CH_{k+1}(X) ⟶ CH_k(X)`,

with `CH_*(X)` the Chow group `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6 at the
canonical embeddings of Stacks 0ENK on both sides.

The descent is `AlgebraicGeometry.Space.chowGroupCanonicalLift` and the hypothesis it needs is
the previous theorem. -/
@[stacks 0EQY "the descended operation CH_{k+1}(X) -> CH_k(X), the Chow groups being those of \
Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK on both sides"]
def canonicalFirstChernCapCanonicalChowMap :
    chowGroupCanonical.{u + 1} D sX hX (k + 1) →+ chowGroupCanonical.{u + 1} D sX hX k :=
  canonicalFirstChernCapCanonicalChowMap_of_pushforwardDivisor.{u + 1} D sX hX k N hN
    (fun V hV d hd =>
isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_integralClosedSubspacePushforward
        D sX hX k N hN V d hV hd)

/-- **Stacks 0EQY.**  The descended operation agrees with the cap product of Stacks 0EQJ on the
class of a cycle, which is what it means for the cap product to factor through rational
equivalence. -/
@[stacks 0EQY "the descended operation agrees with the cap product of Stacks 0EQJ on the class \
of a cycle, which is the factorization through rational equivalence"]
theorem canonicalFirstChernCapCanonicalChowMap_chowClassCanonical
    (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapCanonicalChowMap D sX hX k N hN
        (chowClassCanonical.{u + 1} D sX hX (k + 1) α) =
      canonicalFirstChernCapCanonical.{u + 1} D sX hX N hN k α :=
  rfl

end Tag

end AlgebraicGeometry.Space

end

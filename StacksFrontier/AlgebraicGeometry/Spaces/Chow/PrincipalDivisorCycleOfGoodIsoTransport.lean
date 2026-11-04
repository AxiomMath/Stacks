module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# A principal divisor at the canonical embeddings is carried by an isomorphism

In Situation 0EDT let `e : X ≅ Y` be an isomorphism over the base of good integral algebraic
spaces and let `c ∈ Z_k(X)` be a principal divisor in the *canonical* reading of part (1) of
Stacks 0EQ6 — the one in which the embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK are the
canonical ones of `AlgebraicGeometry.Space.genericFractionEmbedding` rather than quantified
existentially, namely `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`.  Then
`e_*c ∈ Z_k(Y)` is a principal divisor in that same reading.

This is the transport the reduction step of Stacks 0EQY needs, at the embeddings the factoring
statement has to be read at.
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleIsoTransport` proves the same for
`AlgebraicGeometry.Space.IsPrincipalDivisorCycle`, where the family of embeddings is quantified and
so may simply be carried across; here there is nothing to carry, the embeddings on both sides being
fixed, and the content is an identity between the order of vanishing along a prime divisor of `X`
at the canonical embedding of `X` and the order of vanishing along its image at the canonical
embedding of `Y`.

## Main results

* `AlgebraicGeometry.Space.ord_rationalFunctionsRingEquivOfIso_eq_ord_pushforwardOfIso`: at the
  canonical embeddings of Stacks 0ENK, the order of vanishing along a prime divisor `Z` of `X` of
  the function field element corresponding to `g ∈ R(Y)^*` equals the order of vanishing of `g`
  along the image of `Z`.  Unconditional.
* `AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso`: the
  pushforward along an isomorphism of good integral algebraic spaces over the base of a principal
  divisor cycle at the canonical embeddings is a principal divisor cycle at the canonical
  embeddings.  Unconditional.

## Implementation notes

### A correction to two notes in the tree

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonical` name as
the one statement this transport is waiting on the naturality of the canonical embedding of
Stacks 0ENK under an isomorphism, i.e. the commuting of the square formed by
`AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing` at `Z` and at
its image, `AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIso` and
`AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRingEquivOfIso`.  **That statement is
not needed, and the transport does not go through it.**  What the predicate asks of a cycle is an
identity of *orders of vanishing*, and that identity is already available without the henselian
local rings at all: `AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_ord_of_isEtale` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor` proves it for an
arbitrary étale morphism, both sides being read at
`AlgebraicGeometry.Space.genericFractionEmbedding`, by computing them on one affine étale chart;
an isomorphism is étale by `AlgebraicGeometry.Space.isEtale_of_isIso`.

The same correction applies to the paragraph "What this file does *not* do" in the implementation
notes of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalFunctionsTransport`, which says that
because the homomorphism `φ : 𝒪^h_{V',ξ'} → 𝒪^h_{V,ξ}` of
`AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_naturality` is only existentially
quantified, "`m = 1` is not available and the orders of vanishing on the two sides are not yet
identified".  The orders of vanishing *are* identified, in two independent ways: by the chart
route just described, and through
`AlgebraicGeometry.Space.PrimeDivisor.ord_pushforwardOfIso`, which carries the order of vanishing
along the ring isomorphism of the two henselian local rings that an isomorphism of spaces
induces.  Neither needs a multiplicity.  (Those are base files, so the notes are left in place.)

### Why the identity cannot be stated as a transport of the embedding

`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood` fixes the embeddings on both sides, so
the witnessing rational function is the only thing the transport may choose; it is the given one
read in `R(Y)` through `AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIso`.  The
coefficients then agree because of the order-of-vanishing identity above, because the prime
divisor attached to the image of a subspace of codimension one is the image of the prime divisor
attached to it (`AlgebraicGeometry.Space.IntegralClosedSubspace.toPrimeDivisor_equivOfIso`), and
because a coefficient away from codimension one is zero on both sides, an isomorphism not
changing the codimension of a point set.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Ord

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))

/-- **The order of vanishing at the canonical embeddings of Stacks 0ENK is carried by an
isomorphism of integral algebraic spaces.**  For `e : X ≅ Y` an isomorphism of decent, locally
Noetherian, integral algebraic spaces over `S`, `Z` a prime divisor of `X` with image
`AlgebraicGeometry.Space.PrimeDivisor.pushforwardOfIso` in `Y`, and `g ∈ R(Y)^*`,

`ord_Z(g ∘ e) = ord_{e(Z)}(g)`,

both orders of vanishing being taken at the canonical embeddings
`AlgebraicGeometry.Space.genericFractionEmbedding`, and `g ∘ e` being the image of `g` under the
transport `AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIso` of the ring of rational
functions.

This is `AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_ord_of_isEtale` at an isomorphism,
which is étale by `AlgebraicGeometry.Space.isEtale_of_isIso`; the generic point of the image of a
prime divisor is the image of its generic point by
`AlgebraicGeometry.Space.PrimeDivisor.genericPoint_pushforwardOfIso`. -/
theorem ord_rationalFunctionsRingEquivOfIso_eq_ord_pushforwardOfIso (e : X ≅ Y)
    (Z : PrimeDivisor B S hS X) (g : (rationalFunctions B S hS hY)ˣ) :
    (genericFractionEmbedding B S hS hX hintX.isDecentSpace hintX hNX).ord
        (Units.map (rationalFunctionsRingEquivOfIso B S hS hX hY hintX hintY e).toMonoidHom g)
        Z =
      (genericFractionEmbedding B S hS hY hintY.isDecentSpace hintY hNY).ord g
        (Z.pushforwardOfIso B S hS hX hY hintY.isDecentSpace e) :=
  ord_rationalFunctionMap_eq_ord_of_isEtale B S hS hX hY hintX.isDecentSpace
    hintY.isDecentSpace hintX hintY hNX hNY (isEtale_of_isIso B S hS e.hom)
    (pointsMap_genericPoint_of_isIso B S hS hX hY hintX hintY e.hom) Z
    (Z.pushforwardOfIso B S hS hX hY hintY.isDecentSpace e)
    (Z.genericPoint_pushforwardOfIso B S hS hX hY hintY.isDecentSpace e).symm g

end Ord

/-! ### The transport of a principal divisor at the canonical embeddings -/

section PrincipalDivisor

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (e : X ≅ Y)

/-- **A principal divisor at the canonical embeddings is carried by an isomorphism of good
integral spaces.**  For `e : X ≅ Y` an isomorphism over the base of good integral algebraic
spaces and `c ∈ Z_k(X)` a principal divisor in the canonical reading of part (1) of Stacks 0EQ6,
the pushforward `e_*c ∈ Z_k(Y)` is a principal divisor in the canonical reading.

The witnessing rational function is the given one read in `R(Y)` through
`AlgebraicGeometry.Space.rationalFunctionsRingEquivOfIso`; nothing else is left to choose, the
embeddings being fixed on both sides.  The coefficients agree by
`AlgebraicGeometry.Space.ord_rationalFunctionsRingEquivOfIso_eq_ord_pushforwardOfIso`. -/
theorem isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso
    (hcomp : e.hom ≫ sY = sX) (k : ℤ) {c : CycleGroup D sX k}
    (hc : IsPrincipalDivisorCycleOfGood D sX hX hintX k c) :
    IsPrincipalDivisorCycleOfGood D sY hY hintY k
      (cycleGroupClosedPushforward D hY.1 hX.1 (isDecentSpace_of_isGood D sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sY hY.2.2 sX hcomp k c) := by
  classical
  set EX := genericFractionEmbedding D.site D.base D.base_mem hX.1 hintX.isDecentSpace hintX
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) with hEX
  set EY := genericFractionEmbedding D.site D.base D.base_mem hY.1 hintY.isDecentSpace hintY
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) with hEY
  let := EX.nontrivial
  let := EX.isNoetherianRing
  let := EX.krullDimLE
  let := EY.nontrivial
  let := EY.isNoetherianRing
  let := EY.krullDimLE
  obtain ⟨f, hf, heq⟩ := hc
  set eR := rationalFunctionsRingEquivOfIso D.site D.base D.base_mem hX.1 hY.1 hintX hintY e
    with heR
  refine ⟨eR.symm f, hf.map eR.symm, ?_⟩
  have hkey : ∀ (Z₀ : PrimeDivisor D.site D.base D.base_mem X)
      (Z' : PrimeDivisor D.site D.base D.base_mem Y)
      (_ : Z' = Z₀.pushforwardOfIso D.site D.base D.base_mem hX.1 hY.1 hintY.isDecentSpace e)
      (hu : IsUnit (EY.emb Z' (eR.symm f))) (hu₀ : IsUnit (EX.emb Z₀ f)),
      Z₀.ord D.site D.base D.base_mem hX.1 hintX.isDecentSpace (EX.emb Z₀ f) hu₀ =
        Z'.ord D.site D.base D.base_mem hY.1 hintY.isDecentSpace (EY.emb Z' (eR.symm f)) hu := by
    intro Z₀ Z' hZ' hu hu₀
    subst hZ'
    have h := ord_rationalFunctionsRingEquivOfIso_eq_ord_pushforwardOfIso D.site D.base D.base_mem
      hX.1 hY.1 hintX hintY (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) e Z₀ (hf.map eR.symm).unit
    rw [← hEX, ← hEY, ← heR] at h
    refine Eq.trans (PrimeDivisor.ord_congr D.site D.base D.base_mem hX.1 hintX.isDecentSpace _
      hu₀ _ (congrArg (EX.emb Z₀) (eR.apply_symm_apply f).symm))
      (h.trans (PrimeDivisor.ord_congr D.site D.base D.base_mem hY.1 hintY.isDecentSpace _ _ hu
        rfl))
  funext T
  obtain ⟨T₀, rfl⟩ := IntegralClosedSubspace.surjective_pushforward_of_iso D.site D.base
    D.base_mem hX.1 hY.1 hintX.isDecentSpace hintY.isDecentSpace e T
  show cycleClosedPushforward D hY.1 hX.1 (isDecentSpace_of_isGood D sY hY)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) c.1 _ = _
  rw [cycleClosedPushforward_apply_pushforward, congrFun heq T₀]
  have hcodeq := codimension_integralClosedSubspaceSupport_pushforward_of_iso D.site D.base
    D.base_mem hX.1 hY.1 hintY.isDecentSpace e T₀
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 T₀) = 1
  · have hcod' := hcodeq.trans hcod
    simp only [principalDivisorCycleCoefficients, dif_pos hcod, dif_pos hcod']
    exact hkey _ _ (IntegralClosedSubspace.toPrimeDivisor_equivOfIso D.site D.base D.base_mem
      hX.1 hY.1 hintX.isDecentSpace hintY.isDecentSpace e T₀ hcod hcod') _ _
  · have hcod' := hcodeq ▸ hcod
    simp only [principalDivisorCycleCoefficients, dif_neg hcod, dif_neg hcod']

include hintX hintY in
/-- **A principal divisor is carried by an isomorphism of good integral spaces.**  For
`e : X ≅ Y` an isomorphism over the base of good integral algebraic spaces and `c ∈ Z_k(X)` a
principal divisor in the sense of part (1) of Stacks 0EQ6, the pushforward `e_*c ∈ Z_k(Y)` is a
principal divisor.

`AlgebraicGeometry.Space.IsPrincipalDivisorCycle` reads `div(f)` at the canonical embeddings of
Stacks 0ENK, so this is
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso`. -/
theorem isPrincipalDivisorCycle_cycleGroupClosedPushforward_of_iso (hcomp : e.hom ≫ sY = sX)
    (k : ℤ) {c : CycleGroup D sX k} (hc : IsPrincipalDivisorCycle D sX k c) :
    IsPrincipalDivisorCycle D sY k
      (cycleGroupClosedPushforward D hY.1 hX.1 (isDecentSpace_of_isGood D sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sY hY.2.2 sX hcomp k c) := by
  obtain ⟨_, _, f, heq⟩ := hc
  exact (isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D sX hX sY hY hintX
    hintY e hcomp k ⟨f, f.isUnit, heq⟩).isPrincipalDivisorCycle

end PrincipalDivisor

end AlgebraicGeometry.Space

end

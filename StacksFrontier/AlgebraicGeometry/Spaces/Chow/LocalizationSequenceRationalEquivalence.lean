module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenComplementRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding

/-!
# The localization sequence for the cycles of an algebraic space

In the situation of Stacks 0EDT let `X/B` be good, let `U ⊆ X` be an open subspace and let
`i : Y ⟶ X` be the inclusion of a closed subspace whose point set is the complement of `|U|`.
Two `k`-cycles on `X` whose restrictions to `U` are rationally equivalent differ, up to rational
equivalence on `X`, by a cycle pushed forward from `Y`: this is the first assertion of Stacks 0EQ7.
The second, that `CH_k(Y) → CH_k(X) → CH_k(U) → 0` is an exact complex, and the registration of
the tag are in `StacksFrontier/AlgebraicGeometry/Spaces/Chow/ChowLocalizationSequence.lean`.

The source's proof writes the rational equivalence on `U` as `∑_n (i_n)_* div_{W_n}(f_n)` over a
locally finite family of integral closed subspaces `W_n ⊆ U` of δ-dimension `k + 1`, replaces
each `W_n` by the integral closed subspace `W'_n ⊆ X` on the closure of its image and forms
`δ = ∑_n (i'_n)_* div_{W'_n}(f_n)` on `X`. Everything in that proof except the formation of the
individual summand `div_{W'_n}(f_n)` is already in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/OpenComplementRationalEquivalence.lean`; this file
supplies the summand and concludes.

## Main definitions

* `AlgebraicGeometry.Space.embTransportOfGenericPointEq` and
  `AlgebraicGeometry.Space.embLiftOfOpenImmersion`: the embeddings
  `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK on the prime divisors of `X`, transported from the given
  ones on an open subspace `U ⊆ X` at the prime divisors whose generic point lies in `|U|` and
  taken from a given family `emb0` elsewhere. The lifting step below does not use them: a
  principal divisor is read at the canonical embeddings of Stacks 0ENK on both sides.
* `AlgebraicGeometry.Space.closureSubspace`: the integral closed subspace on the closure of the
  image of an integral closed subspace of an open subspace, with the decency of the ambient
  space read off its goodness.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.exists_closureImage_eq` and
  `AlgebraicGeometry.Space.PrimeDivisor.injective_closureImage`: a prime divisor whose generic
  point lies in the image of an open immersion is the one on the closure of the image of a prime
  divisor of the source, and this correspondence is injective.
* `AlgebraicGeometry.Space.embLiftOfOpenImmersion_closureImage_apply`: the chosen embedding at a
  prime divisor on the closure of an image is the transported one, which is the compatibility
  hypothesis of
  `AlgebraicGeometry.Space.principalDivisorCycleCoefficients_closureImage`.
* `AlgebraicGeometry.Space.principalDivisorCycleCoefficients_closureImage_of_ord_eq`: the
  coefficients of two principal divisors agree along the closure of the image as soon as their
  orders of vanishing agree at corresponding prime divisors.
* `AlgebraicGeometry.Space.locallyFinite_primeDivisorCoefficients_of_isOpenImmersion`: a
  coefficient family on the prime divisors of `X` which agrees with one of locally finite
  support along the closures of the images of the prime divisors of a nonempty open subspace has
  locally finite support.
* `AlgebraicGeometry.Space.exists_isPrincipalDivisorCycle_closureImage`: the lifting step of
  Stacks 0EQ7 — a principal divisor on an integral closed subspace `W ⊆ U` of δ-dimension
  `k + 1` is the coefficientwise restriction of a principal divisor on `W'`. It is stated for an
  immersion `j : U ⟶ X` along which the comparison `W ⟶ W'` is an open immersion, so that it
  serves both an open immersion and the inclusion of a closed subspace.
* `AlgebraicGeometry.Space.exists_rationallyEquivalent_add_cycleGroupClosedPushforward_of_restrict`
  is the first assertion of Stacks 0EQ7, for any closed immersion `i : Y ⟶ X` and open immersion
  `j : U ⟶ X` with complementary images.

## Implementation notes

### Nothing is carried

Stacks 0ENK is used, both assertions of it, and neither is carried. A principal divisor is read,
on `W` and on `W'` alike, through the canonical data of that lemma,
`AlgebraicGeometry.Space.genericFractionEmbedding`: the henselian local rings at the generic
points of prime divisors are nontrivial Noetherian of dimension at most one, and the function
field embeds in their total rings of fractions by the canonical map. `W'` is integral by
definition and locally Noetherian because it is locally of finite type over the locally
Noetherian base of Situation 0EDT
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isGood`).

Since the embeddings on both sides are fixed, the only choice in the lifting step is the rational
function on `W'`: it is the preimage of the given `f` under the isomorphism of function fields
`R(W') → R(W)` that the open immersion `m : W ⟶ W'` induces
(`AlgebraicGeometry.Space.rationalFunctionMap_bijective_of_mono`). The coefficients of the lifted
principal divisor agree with the original ones because the order of vanishing of Stacks 0ENK is
compatible with open immersions,
`AlgebraicGeometry.Space.genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion`,
at the prime divisors of `W'` whose generic point lies in `|W|`; at the other prime divisors of
`W'` — exactly the ones contributing the correction term `i_*γ` — nothing about the coefficients
is needed.

The dimension function of Stacks 0EDN on `W'`, through which Stacks 0EPZ sees that a prime
divisor of `W'` has δ-dimension `k` when `W'` has δ-dimension `k + 1`, is
`AlgebraicGeometry.Space.exists_dimensionFunction_deltaValue_of_isGood` applied to the good space
`W'`; it is not a hypothesis.

### The choice of embedding is made without a transport of types

This concerns `AlgebraicGeometry.Space.embLiftOfOpenImmersion`, which the lifting step no longer
uses. It is defined by cases on whether the generic point
of a prime divisor `Z` of `X` is the image of the generic point of a prime divisor of `U`, and
not on whether `Z` is the prime divisor on the closure of the image of one. The two conditions are
equivalent, by
`AlgebraicGeometry.Space.PrimeDivisor.pointsMap_genericPoint_closureImage` and
`AlgebraicGeometry.Space.PrimeDivisor.exists_closureImage_eq`, but only the first keeps the
target `Q(𝒪^h_{X, ξ_Z})` of the chosen homomorphism *syntactically independent* of the chosen
preimage: that ring depends on `Z` only through its generic point. Defining the function by cases
on the shape of `Z` instead forces an `Eq.rec` over the ring, and the resulting proof terms are
large enough that the kernel does not check them.

The comparison the two cases are glued by is the composite of
`AlgebraicGeometry.Space.henselianLocalRingRingEquivOfIsOpenImmersion` with
`AlgebraicGeometry.Space.henselianLocalRingCongr`, which is by definition
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRingRingEquivClosureImage` at the
point equality of
`AlgebraicGeometry.Space.PrimeDivisor.pointsMap_genericPoint_closureImage`; that is why the
characterization `AlgebraicGeometry.Space.embLiftOfOpenImmersion_closureImage_apply` is literally
the compatibility hypothesis that
`AlgebraicGeometry.Space.principalDivisorCycleCoefficients_closureImage` asks for.

### Local finiteness splits in two

The support of the lifted principal divisor is locally finite for two different reasons. At the
prime divisors of `W'` whose generic point lies in the open part the coefficients are those of
the original cycle, so local finiteness is transported by
`AlgebraicGeometry.Space.locallyFinite_of_isOpenEmbedding_extend`, local Noetherianity of `|W'|`
supplying the quasi-compact neighbourhoods it needs. At the prime divisors whose generic point
misses the open part nothing is known about the coefficients, and local finiteness holds for all
of them at once: this is Stacks 0EPS,
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`, applied to the
nonempty open `|W| ⊆ |W'|`.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Order

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section PrimeDivisorClosureImage

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A prime divisor of `X` whose generic point lies in the image of an open immersion
`j : U ⟶ X` is the one on the closure of the image of a prime divisor of `U`. -/
theorem PrimeDivisor.exists_closureImage_eq
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hUdec : IsDecentSpace D.site D.base D.base_mem U) {j : U ⟶ X}
    (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (hZ : Z.genericPoint D.site D.base D.base_mem X ∈
      Set.range (pointsMap D.site D.base D.base_mem U j)) :
    ∃ Z' : PrimeDivisor D.site D.base D.base_mem U,
      Z'.closureImage D.site D.base D.base_mem hX hU hXdec hj = Z := by
  have hmem : Z.genericPoint D.site D.base D.base_mem X ∈
      Z.support D.site D.base D.base_mem X := by
    rw [← Z.isGenericPoint_genericPoint D.site D.base D.base_mem X]
    exact subset_closure rfl
  obtain ⟨A, hA⟩ := IntegralClosedSubspace.exists_closureImage_eq D hX hU hXdec hUdec hj
    (Z.toIntegralClosedSubspace D.site D.base D.base_mem) ⟨_, hmem, hZ⟩
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hU A) = 1 := by
    rw [← IntegralClosedSubspace.codimension_integralClosedSubspaceSupport_closureImage
      D.site D.base D.base_mem hX hU hXdec hj A, hA]
    exact Z.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hX
  refine ⟨A.toPrimeDivisor D.site D.base D.base_mem hU hcod,
    PrimeDivisor.eq_of_subspace_eq D.site D.base D.base_mem ?_⟩
  show (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec j
      ((A.toPrimeDivisor D.site D.base D.base_mem hU hcod).toIntegralClosedSubspace
        D.site D.base D.base_mem)).subspace = Z.subspace
  rw [IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor, hA]
  rfl

/-- Taking the prime divisor on the closure of the image along an immersion is injective. -/
theorem PrimeDivisor.injective_closureImage
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {j : U ⟶ X}
    (hj : IsOpenImmersion D.site D.base D.base_mem j) :
    Function.Injective
      (PrimeDivisor.closureImage D.site D.base D.base_mem (X := X) (U := U) hX hU hXdec hj) := by
  intro Z₁ Z₂ h
  have himm : IsImmersion D.site D.base D.base_mem j :=
    isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj
  have h' : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec j
        (Z₁.toIntegralClosedSubspace D.site D.base D.base_mem) =
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec j
        (Z₂.toIntegralClosedSubspace D.site D.base D.base_mem) :=
    IntegralClosedSubspace.ext (congrArg PrimeDivisor.subspace h)
  exact PrimeDivisor.eq_of_subspace_eq D.site D.base D.base_mem
    (congrArg IntegralClosedSubspace.subspace
      (IntegralClosedSubspace.injective_closureImage D hX hU hXdec himm h'))

/-- The integral closed subspace of the prime divisor on the closure of the image of `Z` is the
closure of the image of that of `Z`. -/
private theorem closureImage_toIntegralClosedSubspace_eq
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {j : U ⟶ X}
    (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (Z : PrimeDivisor D.site D.base D.base_mem U) :
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec j
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      (Z.closureImage D.site D.base D.base_mem hX hU hXdec hj).toIntegralClosedSubspace
        D.site D.base D.base_mem :=
  (IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
    hX _ _).symm

section EmbLift

variable (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hUdec : IsDecentSpace D.site D.base D.base_mem U)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (e : rationalFunctions D.site D.base D.base_mem hU ≃+*
      rationalFunctions D.site D.base D.base_mem hX)
    (embU : ∀ Z : PrimeDivisor D.site D.base D.base_mem U,
      rationalFunctions D.site D.base D.base_mem hU →+*
        Z.genericTotalFractionRing D.site D.base D.base_mem hU hUdec)

/-- The embedding of Stacks 0ENK on `U` at a prime divisor `Z'` of `U`, transported to the
prime divisor of `X` whose generic point is the image of that of `Z'`: read a rational function
of `X` as one of `U`, embed it at `Z'`, and carry it over along the comparison of henselian
local rings of `AlgebraicGeometry.Space.henselianLocalRingRingEquivOfIsOpenImmersion` followed
by the identification along the equality of points.

The composite of those two ring isomorphisms is by definition
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRingRingEquivClosureImage` when the
point equality is the one of
`AlgebraicGeometry.Space.PrimeDivisor.pointsMap_genericPoint_closureImage`. -/
noncomputable def embTransportOfGenericPointEq
    {Z : PrimeDivisor D.site D.base D.base_mem X}
    (Z' : PrimeDivisor D.site D.base D.base_mem U)
    (h : pointsMap D.site D.base D.base_mem U j (Z'.genericPoint D.site D.base D.base_mem U) =
      Z.genericPoint D.site D.base D.base_mem X) :
    rationalFunctions D.site D.base D.base_mem hX →+*
      Z.genericTotalFractionRing D.site D.base D.base_mem hX hXdec :=
  (IsFractionRing.ringEquivOfRingEquiv
      ((henselianLocalRingRingEquivOfIsOpenImmersion D.site D.base D.base_mem hX hU hXdec hUdec
            hj (Z'.genericPoint D.site D.base D.base_mem U)).trans
        (henselianLocalRingCongr D.site D.base D.base_mem hX hXdec h)) :
      Z'.genericTotalFractionRing D.site D.base D.base_mem hU hUdec ≃+*
        Z.genericTotalFractionRing D.site D.base D.base_mem hX hXdec).toRingHom.comp
    ((embU Z').comp e.symm.toRingHom)

/-- The transported embedding does not depend on which prime divisor of `U` it is transported
from: the map on points of an open immersion is injective and a prime divisor is determined by
its generic point. -/
theorem embTransportOfGenericPointEq_congr
    {Z : PrimeDivisor D.site D.base D.base_mem X}
    {Z₀ Z₁ : PrimeDivisor D.site D.base D.base_mem U}
    (h₀ : pointsMap D.site D.base D.base_mem U j (Z₀.genericPoint D.site D.base D.base_mem U) =
      Z.genericPoint D.site D.base D.base_mem X)
    (h₁ : pointsMap D.site D.base D.base_mem U j (Z₁.genericPoint D.site D.base D.base_mem U) =
      Z.genericPoint D.site D.base D.base_mem X) :
    embTransportOfGenericPointEq D hX hU hXdec hUdec hj e embU Z₀ h₀ =
      embTransportOfGenericPointEq D hX hU hXdec hUdec hj e embU Z₁ h₁ := by
  have hinj : Function.Injective (pointsMap D.site D.base D.base_mem U j) :=
    (isEmbedding_pointsMap_of_isImmersion D.site D.base D.base_mem hX j
      (isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj)).injective
  have hZ : Z₀ = Z₁ :=
    PrimeDivisor.eq_of_genericPoint_eq D.site D.base D.base_mem hU (hinj (h₀.trans h₁.symm))
  subst hZ
  rfl

variable (emb0 : ∀ Z : PrimeDivisor D.site D.base D.base_mem X,
  rationalFunctions D.site D.base D.base_mem hX →+*
    Z.genericTotalFractionRing D.site D.base D.base_mem hX hXdec)

open Classical in
/-- The embeddings of Stacks 0ENK on the prime divisors of `X`: at a prime divisor whose generic
point lies in the image of `j` the one transported from `U`, and the given one elsewhere. -/
noncomputable def embLiftOfOpenImmersion (Z : PrimeDivisor D.site D.base D.base_mem X) :
    rationalFunctions D.site D.base D.base_mem hX →+*
      Z.genericTotalFractionRing D.site D.base D.base_mem hX hXdec :=
  if h : ∃ Z' : PrimeDivisor D.site D.base D.base_mem U,
      pointsMap D.site D.base D.base_mem U j (Z'.genericPoint D.site D.base D.base_mem U) =
        Z.genericPoint D.site D.base D.base_mem X then
    embTransportOfGenericPointEq D hX hU hXdec hUdec hj e embU h.choose h.choose_spec
  else emb0 Z

/-- At a prime divisor whose generic point is the image of the generic point of a prime divisor
of `U`, the chosen embedding is the transported one. -/
theorem embLiftOfOpenImmersion_eq_transport
    {Z : PrimeDivisor D.site D.base D.base_mem X}
    (Z' : PrimeDivisor D.site D.base D.base_mem U)
    (h : pointsMap D.site D.base D.base_mem U j (Z'.genericPoint D.site D.base D.base_mem U) =
      Z.genericPoint D.site D.base D.base_mem X) :
    embLiftOfOpenImmersion D hX hU hXdec hUdec hj e embU emb0 Z =
      embTransportOfGenericPointEq D hX hU hXdec hUdec hj e embU Z' h := by
  have hex : ∃ Z₀ : PrimeDivisor D.site D.base D.base_mem U,
      pointsMap D.site D.base D.base_mem U j (Z₀.genericPoint D.site D.base D.base_mem U) =
        Z.genericPoint D.site D.base D.base_mem X := ⟨Z', h⟩
  rw [show embLiftOfOpenImmersion D hX hU hXdec hUdec hj e embU emb0 Z =
      embTransportOfGenericPointEq D hX hU hXdec hUdec hj e embU hex.choose hex.choose_spec from
    dif_pos hex]
  exact embTransportOfGenericPointEq_congr D hX hU hXdec hUdec hj e embU hex.choose_spec h

/-- The embedding chosen at the prime divisor on the closure of the image of `Z'` carries a
rational function over exactly as the comparison of Stacks 0EQ7 does: this is the compatibility
hypothesis of
`AlgebraicGeometry.Space.principalDivisorCycleCoefficients_closureImage`. -/
theorem embLiftOfOpenImmersion_closureImage_apply
    (Z' : PrimeDivisor D.site D.base D.base_mem U)
    (f : rationalFunctions D.site D.base D.base_mem hU) :
    embLiftOfOpenImmersion D hX hU hXdec hUdec hj e embU emb0
        (Z'.closureImage D.site D.base D.base_mem hX hU hXdec hj) (e f) =
      (IsFractionRing.ringEquivOfRingEquiv
        (Z'.genericHenselianLocalRingRingEquivClosureImage D.site D.base D.base_mem hX hU hXdec
          hUdec hj) :
        Z'.genericTotalFractionRing D.site D.base D.base_mem hU hUdec ≃+*
          (Z'.closureImage D.site D.base D.base_mem hX hU hXdec hj).genericTotalFractionRing
            D.site D.base D.base_mem hX hXdec) (embU Z' f) := by
  rw [embLiftOfOpenImmersion_eq_transport D hX hU hXdec hUdec hj e embU emb0 Z'
    (Z'.pointsMap_genericPoint_closureImage D.site D.base D.base_mem hX hU hXdec hj)]
  show _ = _
  simp only [embTransportOfGenericPointEq, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  rfl

end EmbLift

end PrimeDivisorClosureImage

/-! ### Local finiteness of a lifted divisor -/

section LocallyFiniteLift

variable (D : BaseSpaceDimensionSituation.{u})
    {C A : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Local finiteness of a coefficient family lifted along an open immersion.** Let
`m : A ⟶ C` be an open immersion of algebraic spaces with `C` locally Noetherian, decent and
irreducible and `A` nonempty. A family of coefficients on the prime divisors of `C` whose
values at the prime divisors on the closures of the images of the prime divisors of `A` are
those of a family with locally finite support on `A` has locally finite support.

The prime divisors of `C` whose generic point misses `|A|` are locally finite by Stacks 0EPS,
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`, whatever their
coefficients; those whose generic point lies in `|A|` come from prime divisors of `A` by
`AlgebraicGeometry.Space.PrimeDivisor.exists_closureImage_eq`, and taking closures of images
transports local finiteness by
`AlgebraicGeometry.Space.locallyFinite_of_isOpenEmbedding_extend`. -/
theorem locallyFinite_primeDivisorCoefficients_of_isOpenImmersion
    (hC : IsAlgebraicSpace D.site D.base D.base_mem C)
    (hA : IsAlgebraicSpace D.site D.base D.base_mem A)
    (hCdec : IsDecentSpace D.site D.base D.base_mem C)
    (hAdec : IsDecentSpace D.site D.base D.base_mem A)
    {m : A ⟶ C} (hmopen : IsOpenImmersion D.site D.base D.base_mem m)
    (hN : HasEtaleLocalProperty D.site D.base D.base_mem C
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hCirr : IrreducibleSpace (points D.site D.base D.base_mem C))
    (hAne : Nonempty (points D.site D.base D.base_mem A))
    (coeff : PrimeDivisor D.site D.base D.base_mem C → ℤ)
    (src : PrimeDivisor D.site D.base D.base_mem A → ℤ)
    (hagree : ∀ Z : PrimeDivisor D.site D.base D.base_mem A,
      coeff (Z.closureImage D.site D.base D.base_mem hC hA hCdec hmopen) = src Z)
    (hsrcfin : LocallyFinite fun Z : PrimeDivisor D.site D.base D.base_mem A =>
      if src Z = 0 then ∅ else Z.support D.site D.base D.base_mem A) :
    LocallyFinite fun Z : PrimeDivisor D.site D.base D.base_mem C =>
      if coeff Z = 0 then ∅ else Z.support D.site D.base D.base_mem C := by
  classical
  have hOopen : IsOpen (Set.range (pointsMap D.site D.base D.base_mem A m)) :=
    isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem m hmopen
  have hOne : (Set.range (pointsMap D.site D.base D.base_mem A m)).Nonempty :=
    ⟨_, hAne.some, rfl⟩
  -- the prime divisors whose generic point misses the open part, by Stacks 0EPS
  have hLF₁ : LocallyFinite fun Z : PrimeDivisor D.site D.base D.base_mem C =>
      if coeff Z ≠ 0 ∧ Z.genericPoint D.site D.base D.base_mem C ∉
          Set.range (pointsMap D.site D.base D.base_mem A m) then
        Z.support D.site D.base D.base_mem C
      else ∅ :=
    locallyFinite_primeDivisor_of_genericPoint_notMem D.site D.base D.base_mem hC hN hCirr _ _
      hOopen hOne fun _ hZ => hZ.2
  -- the prime divisors whose generic point lies in the open part, by transport
  have hLF₂ : LocallyFinite fun Z : PrimeDivisor D.site D.base D.base_mem C =>
      if coeff Z ≠ 0 ∧ Z.genericPoint D.site D.base D.base_mem C ∈
          Set.range (pointsMap D.site D.base D.base_mem A m) then
        Z.support D.site D.base D.base_mem C
      else ∅ := by
    refine locallyFinite_of_isOpenEmbedding_extend
      (isLocallyNoetherianSpace_of_isLocallyNoetherian D.site D.base D.base_mem C hC hN)
      (isOpenEmbedding_pointsMap_of_isOpenImmersion D hC hmopen)
      (e := fun Z : PrimeDivisor D.site D.base D.base_mem A =>
        Z.closureImage D.site D.base D.base_mem hC hA hCdec hmopen)
      (f := fun Z : PrimeDivisor D.site D.base D.base_mem A =>
        if src Z = 0 then ∅ else Z.support D.site D.base D.base_mem A)
      (fun Z hZ => ?_) (fun Z => ?_) hsrcfin
    · refine if_neg fun hc => ?_
      obtain ⟨Z₀, hZ₀⟩ :=
        PrimeDivisor.exists_closureImage_eq D hC hA hCdec hAdec hmopen Z hc.2
      exact hZ Z₀ hZ₀
    · have hsupp : (Z.closureImage D.site D.base D.base_mem hC hA hCdec hmopen).support
          D.site D.base D.base_mem C =
          closure (pointsMap D.site D.base D.base_mem A m ''
            Z.support D.site D.base D.base_mem A) := by
        show subspacePointSet D.site D.base D.base_mem C
            (Z.closureImage D.site D.base D.base_mem hC hA hCdec hmopen).subspace = _
        rw [PrimeDivisor.subspace_closureImage,
          IntegralClosedSubspace.subspacePointSet_closureImage]
        rfl
      by_cases hc : coeff (Z.closureImage D.site D.base D.base_mem hC hA hCdec hmopen) ≠ 0 ∧
          (Z.closureImage D.site D.base D.base_mem hC hA hCdec hmopen).genericPoint
            D.site D.base D.base_mem C ∈ Set.range (pointsMap D.site D.base D.base_mem A m)
      · rw [if_pos hc, if_neg (by rw [← hagree Z]; exact hc.1), hsupp]
      · rw [if_neg hc]
        exact Set.empty_subset _
  -- the whole family is covered by the two halves
  intro x
  obtain ⟨t₁, ht₁, hfin₁⟩ := hLF₁ x
  obtain ⟨t₂, ht₂, hfin₂⟩ := hLF₂ x
  refine ⟨t₁ ∩ t₂, Filter.inter_mem ht₁ ht₂, (hfin₁.union hfin₂).subset ?_⟩
  rintro Z ⟨p, hp, hpt₁, hpt₂⟩
  have hz : coeff Z ≠ 0 := fun hz => by simp [hz] at hp
  have hp' : p ∈ Z.support D.site D.base D.base_mem C := by simpa [hz] using hp
  by_cases hO : Z.genericPoint D.site D.base D.base_mem C ∈
      Set.range (pointsMap D.site D.base D.base_mem A m)
  · exact Or.inr ⟨p, by simp [hz, hO, hp'], hpt₂⟩
  · exact Or.inl ⟨p, by simp [hz, hO, hp'], hpt₁⟩

end LocallyFiniteLift

/-! ### Principal divisors along an open immersion, from the orders of vanishing -/

section PrincipalDivisorOrdComparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hUdec : IsDecentSpace D.site D.base D.base_mem U)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hXdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem U,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hU.1 hUdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem U,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hU.1 hUdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem U,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hU.1 hUdec)]
    (embX : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      rationalFunctions D.site D.base D.base_mem hX.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hXdec)
    (fX : rationalFunctions D.site D.base D.base_mem hX.1)
    (hfX : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (embX W fX))
    (embU : ∀ W : PrimeDivisor D.site D.base D.base_mem U,
      rationalFunctions D.site D.base D.base_mem hU.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hU.1 hUdec)
    (fU : rationalFunctions D.site D.base D.base_mem hU.1)
    (hfU : ∀ W : PrimeDivisor D.site D.base D.base_mem U, IsUnit (embU W fU))

/-- **The coefficient families of `div(f_X)` and `div(f_U)` agree along the closure of the
image, from the orders of vanishing.** If the order of vanishing of `f_X` along the prime
divisor of `X` on the closure of the image of each prime divisor `Z` of `U` is that of `f_U`
along `Z`, then the coefficient of `div(f_X)` at the closure of the image of any integral closed
subspace `V` of `U` is the coefficient of `div(f_U)` at `V`; off the prime divisors both vanish,
codimension being unchanged by the closure of the image. -/
theorem principalDivisorCycleCoefficients_closureImage_of_ord_eq
    (hord : ∀ Z : PrimeDivisor D.site D.base D.base_mem U,
      (Z.closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hj).ord D.site D.base D.base_mem
          hX.1 hXdec (embX (Z.closureImage D.site D.base D.base_mem hX.1 hU.1 hXdec hj) fX)
          (hfX _) =
        Z.ord D.site D.base D.base_mem hU.1 hUdec (embU Z fU) (hfU Z))
    (V : IntegralClosedSubspace D.site D.base D.base_mem U) :
    principalDivisorCycleCoefficients D sX hX hXdec embX fX hfX
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j V) =
      principalDivisorCycleCoefficients D sU hU hUdec embU fU hfU V := by
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hU.1 V) = 1
  · have hV : (V.toPrimeDivisor D.site D.base D.base_mem hU.1 hcod).toIntegralClosedSubspace
        D.site D.base D.base_mem = V :=
      IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
        hU.1 V hcod
    rw [← hV]
    set Z := V.toPrimeDivisor D.site D.base D.base_mem hU.1 hcod
    rw [closureImage_toIntegralClosedSubspace_eq D hX.1 hU.1 hXdec hj,
      principalDivisorCycleCoefficients_toIntegralClosedSubspace,
      principalDivisorCycleCoefficients_toIntegralClosedSubspace,
      principalDivisorCoefficients_apply, principalDivisorCoefficients_apply]
    exact hord Z
  · rw [principalDivisorCycleCoefficients_of_codimension_ne_one D sU hU hUdec embU fU hfU hcod,
      principalDivisorCycleCoefficients_of_codimension_ne_one D sX hX hXdec embX fX hfX ?_]
    rw [IntegralClosedSubspace.codimension_integralClosedSubspaceSupport_closureImage
      D.site D.base D.base_mem hX.1 hU.1 hXdec hj V]
    exact hcod

end PrincipalDivisorOrdComparison

/-! ### Lifting a principal divisor along the closure of the image -/

section ClosureSubspace

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The integral closed subspace of `X` on the closure of the image of an integral closed
subspace of `U` along `j : U ⟶ X`, with the decency of `X` read off its goodness. -/
noncomputable abbrev closureSubspace (sX : X ⟶ D.space) (hX : D.IsGood sX) (j : U ⟶ X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U) :
    IntegralClosedSubspace D.site D.base D.base_mem X :=
  IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) j W

end ClosureSubspace

section Lift

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {j : U ⟶ X} (himm : IsImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)

include hU himm hjc in
/-- **The lifting step of Stacks 0EQ7.** Let `j : U ⟶ X` be an immersion over the base, let
`W ⊆ U` be an integral closed subspace of δ-dimension `k + 1`, let `W' ⊆ X` be the integral closed
subspace on the closure of its image and suppose the comparison morphism `m : W ⟶ W'` is an open
immersion (it is when `j` is an open immersion, and it is an isomorphism when `j` is the
inclusion of a closed subspace). A principal divisor on `W` is the coefficientwise restriction,
along `m`, of a principal divisor on `W'`.

Both principal divisors are read at the canonical embeddings of Stacks 0ENK. The rational
function on `W'` is the preimage of the given one under the isomorphism of function fields that
`m` induces, `AlgebraicGeometry.Space.rationalFunctionMap_bijective_of_mono`, and the coefficients
agree at the prime divisors of `W'` meeting `|W|` because the order of vanishing is compatible
with the open immersion `m`,
`AlgebraicGeometry.Space.genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion`,
through `AlgebraicGeometry.Space.principalDivisorCycleCoefficients_closureImage_of_ord_eq`.
Nothing about the embedding is assumed. The lifted coefficient family is a cycle: its support is
locally finite by
`AlgebraicGeometry.Space.locallyFinite_primeDivisorCoefficients_of_isOpenImmersion`, and a prime
divisor of `W'` has δ-dimension `k` by Stacks 0EPZ, `W'` having δ-dimension `k + 1` because
taking the closure of the image leaves the δ-dimension alone. -/
theorem exists_isPrincipalDivisorCycle_closureImage (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U)
    (c : CycleGroup D (W.subspace.ι ≫ sU) k)
    (m : W.subspace.toFunctor ⟶ (closureSubspace D sX hX j W).subspace.toFunctor)
    (hmopen : IsOpenImmersion D.site D.base D.base_mem m)
    (hdim : deltaDimension D sU W = k + 1)
    (hprin : IsPrincipalDivisorCycle D (W.subspace.ι ≫ sU) k c) :
    ∃ c' : CycleGroup D ((closureSubspace D sX hX j W).subspace.ι ≫ sX) k,
      IsPrincipalDivisorCycle D ((closureSubspace D sX hX j W).subspace.ι ≫ sX) k c' ∧
        ∀ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
          c'.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
            (closureSubspace D sX hX j W).isClosedSubspace.1
            (closureSubspace D sX hX j W).isIntegralSpace.2.1 m V) = c.1 V := by
  classical
  have hW'good : D.IsGood ((closureSubspace D sX hX j W).subspace.ι ≫ sX) :=
    isGood_integralClosedSubspace D sX hX (closureSubspace D sX hX j W)
  obtain ⟨hWg, hWint, f, heq⟩ := hprin
  have hWd : IsDecentSpace D.site D.base D.base_mem W.subspace.toFunctor := hWint.isDecentSpace
  have hN' : HasEtaleLocalProperty D.site D.base D.base_mem
      (closureSubspace D sX hX j W).subspace.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D
      ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'good
  have hN : HasEtaleLocalProperty D.site D.base D.base_mem W.subspace.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ sU) hWg
  -- the canonical embeddings of Stacks 0ENK on `W` and on `W'`
  let EW := genericFractionEmbedding D.site D.base D.base_mem hWg.1 hWd hWint hN
  let EX := genericFractionEmbedding D.site D.base D.base_mem
    (closureSubspace D sX hX j W).isClosedSubspace.1
    (closureSubspace D sX hX j W).isIntegralSpace.isDecentSpace
    (closureSubspace D sX hX j W).isIntegralSpace hN'
  let := EW.nontrivial
  let := EW.isNoetherianRing
  let := EW.krullDimLE
  let := EX.nontrivial
  let := EX.isNoetherianRing
  let := EX.krullDimLE
  -- the function field of `W'` is that of `W`, along `m`
  have hgen := pointsMap_genericPoint_of_isOpenImmersion D.site D.base D.base_mem hWg.1
    (closureSubspace D sX hX j W).isClosedSubspace.1 hWint
    (closureSubspace D sX hX j W).isIntegralSpace hmopen
  have : Mono m := mono_of_isOpenImmersion D.site D.base D.base_mem m hmopen
  obtain ⟨g, hg⟩ : ∃ g : (rationalFunctions D.site D.base D.base_mem
      (closureSubspace D sX hX j W).isClosedSubspace.1)ˣ,
      Units.map (rationalFunctionMap D.site D.base D.base_mem hWg.1
        (closureSubspace D sX hX j W).isClosedSubspace.1 hWint
        (closureSubspace D sX hX j W).isIntegralSpace m hgen :
          rationalFunctions D.site D.base D.base_mem
              (closureSubspace D sX hX j W).isClosedSubspace.1 →*
            rationalFunctions D.site D.base D.base_mem hWg.1) g = f := by
    let eF := RingEquiv.ofBijective _ (rationalFunctionMap_bijective_of_mono D.site D.base
      D.base_mem hWg.1 (closureSubspace D sX hX j W).isClosedSubspace.1 hWint
      (closureSubspace D sX hX j W).isIntegralSpace m hgen)
    exact ⟨Units.map (eF.symm : rationalFunctions D.site D.base D.base_mem hWg.1 →*
      rationalFunctions D.site D.base D.base_mem
        (closureSubspace D sX hX j W).isClosedSubspace.1) f,
      Units.ext (eF.apply_symm_apply _)⟩
  let fX : rationalFunctions D.site D.base D.base_mem
      (closureSubspace D sX hX j W).isClosedSubspace.1 := g
  let embX := EX.emb
  have hfunits : ∀ Z : PrimeDivisor D.site D.base D.base_mem
      (closureSubspace D sX hX j W).subspace.toFunctor, IsUnit (embX Z fX) :=
    fun Z => g.isUnit.map (embX Z)
  -- the orders of vanishing agree along the comparison
  have hord : ∀ Z : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      EX.ord g (Z.closureImage D.site D.base D.base_mem
          (closureSubspace D sX hX j W).isClosedSubspace.1 W.isClosedSubspace.1
          (closureSubspace D sX hX j W).isIntegralSpace.2.1 hmopen) = EW.ord f Z := by
    intro Z
    rw [← hg]
    exact (genericFractionEmbedding_ord_rationalFunctionMap_of_isOpenImmersion D.site D.base
      D.base_mem hWg.1
      (closureSubspace D sX hX j W).isClosedSubspace.1 hWint
      (closureSubspace D sX hX j W).isIntegralSpace
      hN hN' m
      hmopen hgen Z _ (Z.pointsMap_genericPoint_closureImage D.site D.base D.base_mem
        (closureSubspace D sX hX j W).isClosedSubspace.1 W.isClosedSubspace.1
        (closureSubspace D sX hX j W).isIntegralSpace.2.1 hmopen) g).symm
  -- the coefficients agree along the comparison
  have hcoeff : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
      principalDivisorCycleCoefficients D ((closureSubspace D sX hX j W).subspace.ι ≫ sX)
          hW'good (closureSubspace D sX hX j W).isIntegralSpace.2.1 embX fX hfunits
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
            (closureSubspace D sX hX j W).isClosedSubspace.1
            (closureSubspace D sX hX j W).isIntegralSpace.2.1 m V) = c.1 V := by
    intro V
    rw [principalDivisorCycleCoefficients_closureImage_of_ord_eq D
      ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'good (W.subspace.ι ≫ sU) hWg
      (closureSubspace D sX hX j W).isIntegralSpace.2.1 hWd hmopen embX fX hfunits EW.emb
      (f : rationalFunctions D.site D.base D.base_mem hWg.1) (fun Z => f.isUnit.map (EW.emb Z))
      hord V, ← heq]
  -- the δ-dimension of `W'`
  have hn : deltaDimensionClosed D ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'good
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX (closureSubspace D sX hX j W),
      show closureSubspace D sX hX j W = IntegralClosedSubspace.closureImage D.site D.base
          D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) j W from rfl,
      IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hU.1
        (D.isDecentSpace_of_isGood sX hX) himm W, hjc, hdim]
  -- local finiteness: Stacks 0EPS off `|W|`, transport from `W` on `|W|`
  have hagree : ∀ Z : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      (Z.closureImage D.site D.base D.base_mem
            (closureSubspace D sX hX j W).isClosedSubspace.1 W.isClosedSubspace.1
            (closureSubspace D sX hX j W).isIntegralSpace.2.1 hmopen).ord
          D.site D.base D.base_mem (closureSubspace D sX hX j W).isClosedSubspace.1
          (closureSubspace D sX hX j W).isIntegralSpace.2.1
          (embX (Z.closureImage D.site D.base D.base_mem
            (closureSubspace D sX hX j W).isClosedSubspace.1 W.isClosedSubspace.1
            (closureSubspace D sX hX j W).isIntegralSpace.2.1 hmopen) fX)
          (hfunits (Z.closureImage D.site D.base D.base_mem
            (closureSubspace D sX hX j W).isClosedSubspace.1 W.isClosedSubspace.1
            (closureSubspace D sX hX j W).isIntegralSpace.2.1 hmopen)) =
        c.1 (Z.toIntegralClosedSubspace D.site D.base D.base_mem) := by
    intro Z
    rw [← principalDivisorCoefficients_apply,
      ← principalDivisorCycleCoefficients_toIntegralClosedSubspace D
        ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'good
        (closureSubspace D sX hX j W).isIntegralSpace.2.1 embX fX hfunits
        (Z.closureImage D.site D.base D.base_mem
          (closureSubspace D sX hX j W).isClosedSubspace.1 W.isClosedSubspace.1
          (closureSubspace D sX hX j W).isIntegralSpace.2.1 hmopen),
      ← closureImage_toIntegralClosedSubspace_eq D (closureSubspace D sX hX j W).isClosedSubspace.1
        W.isClosedSubspace.1 (closureSubspace D sX hX j W).isIntegralSpace.2.1 hmopen Z]
    exact hcoeff _
  have hsrcfin : LocallyFinite
      fun Z : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor =>
        if c.1 (Z.toIntegralClosedSubspace D.site D.base D.base_mem) = 0 then ∅
        else Z.support D.site D.base D.base_mem W.subspace.toFunctor :=
    c.2.1.comp_injective
      (PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem)
  have hAne : Nonempty (points D.site D.base D.base_mem W.subspace.toFunctor) := by
    have := W.isIntegralSpace.2.2
    infer_instance
  have hfin := locallyFinite_primeDivisorCoefficients_of_isOpenImmersion D
    (closureSubspace D sX hX j W).isClosedSubspace.1 W.isClosedSubspace.1
    (closureSubspace D sX hX j W).isIntegralSpace.2.1 hWd hmopen hN'
    (closureSubspace D sX hX j W).isIntegralSpace.2.2 hAne
    (fun P => P.ord D.site D.base D.base_mem
      (closureSubspace D sX hX j W).isClosedSubspace.1
      (closureSubspace D sX hX j W).isIntegralSpace.2.1 (embX P fX) (hfunits P))
    _ hagree hsrcfin
  obtain ⟨dim, dim_eq⟩ := exists_dimensionFunction_deltaValue_of_isGood D
    ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'good
  have hmem := principalDivisorCycleCoefficients_mem_cyclesOfDimension D
    ((closureSubspace D sX hX j W).subspace.ι ≫ sX) hW'good
    (closureSubspace D sX hX j W).isIntegralSpace.2.1 embX fX hfunits hfin
    (closureSubspace D sX hX j W).isIntegralSpace dim dim_eq hn
  exact ⟨⟨principalDivisorCycleCoefficients D ((closureSubspace D sX hX j W).subspace.ι ≫ sX)
      hW'good (closureSubspace D sX hX j W).isIntegralSpace.2.1 embX fX hfunits,
      by simpa only [add_sub_cancel_right] using hmem⟩,
    ⟨hW'good, (closureSubspace D sX hX j W).isIntegralSpace, g, rfl⟩, hcoeff⟩

end Lift

/-! ### The localization sequence -/

section Localization

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- **Stacks 0EQ7, the first assertion.** In Situation 0EDT let `X/B` be good, let `j : U ⟶ X`
be an open immersion and `i : Y ⟶ X` a closed immersion over the base whose images in `|X|` are
complementary. Let `k ∈ ℤ` and let `α, β ∈ Z_k(X)`. If `α|_U ∼_rat β|_U` then there is a
`k`-cycle `γ ∈ Z_k(Y)` with `α ∼_rat β + i_*γ`.

The source's proof writes `α|_U - β|_U = ∑_n (i_n)_* div_{W_n}(f_n)` with `{W_n ⊆ U}` locally
finite of δ-dimension `k + 1`, replaces each `W_n` by the integral closed subspace `W'_n ⊆ X` on
the closure of its image, and forms `δ = ∑_n (i'_n)_* div_{W'_n}(f_n) ∈ Z_k(X)`, which is
rationally equivalent to zero and satisfies `(α - β - δ)|_U = 0`; Stacks 0EP9 then writes
`α - β - δ = i_*γ`. The lifting of one principal divisor is
`AlgebraicGeometry.Space.exists_isPrincipalDivisorCycle_closureImage`, local finiteness of
`{W'_n}` is `AlgebraicGeometry.Space.locallyFinite_subspacePointSet_closureImage`, the
comparison of the restrictions is
`AlgebraicGeometry.Space.cycleGroupRestrict_cycleFamilySum_closureImage`, and Stacks 0EP9 is
`AlgebraicGeometry.Space.cycleGroupRestrict_eq_zero_iff`.

The tag is registered on `AlgebraicGeometry.Space.chowGroup_localization`, which states both
assertions for an open and a closed subspace of `X`, whose goodness over the base is proved
there rather than assumed as `hY` and `hU` are here. -/
theorem exists_rationallyEquivalent_add_cycleGroupClosedPushforward_of_restrict
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {i : Y ⟶ X} (hi : IsClosedImmersion D.site D.base D.base_mem i) (hic : i ≫ sX = sY)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)
    (hcomplement : Set.range (pointsMap D.site D.base D.base_mem Y i) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ) (k : ℤ)
    (α β : CycleGroup D sX k)
    (h : RationallyEquivalent.{v} D sU hU k
      (cycleGroupRestrict D sX hX sU hU hj hjc k α)
      (cycleGroupRestrict D sX hX sU hU hj hjc k β)) :
    ∃ γ : CycleGroup D sY k,
      RationallyEquivalent.{v} D sX hX k α
        (β + cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hi sX
          hX.2.2 sY hic k γ) :=
  exists_rationallyEquivalent_of_restrict_of_lift.{v} D sX hX sY hY sU hU hi hic hj hjc
    hcomplement k
    (fun W c m hm hdim hprin =>
      exists_isPrincipalDivisorCycle_closureImage D sX hX sU hU
        (isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj) hjc k W c m
        (IntegralClosedSubspace.isOpenImmersion_of_comp_ι_eq_closureImage D.site D.base
          D.base_mem hX.1 hU.1 (D.isDecentSpace_of_isGood sX hX) hj W hm) hdim hprin)
    α β h

end Localization

end AlgebraicGeometry.Space

end

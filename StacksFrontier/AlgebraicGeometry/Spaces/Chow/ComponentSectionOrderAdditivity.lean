module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentGenericFractionRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentHenselianIdealRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentPrimeDivisorOverGenericPoint

/-!
# Additivity over the irreducible components of the order of vanishing of a chart section

Let `Y` be an algebraic space, good over the base of Situation 0EDT, let `Z` be a prime
divisor of `Y` with generic point `ξ` and write `A = 𝒪^h_{Y, ξ}` for the henselian local ring of
Stacks 0ENK there.  The numerical additivity of the order of vanishing over the irreducible
components of `|Y|` through `ξ` is
`AlgebraicGeometry.Space.exists_natCast_ord_sub_eq_finsum_components_mul_of_isGood`:

  `ord_A(a) - ord_A(b) = ∑_i m_{Y_i, Y} · (ord_{A ⧸ I i}(a) - ord_{A ⧸ I i}(b))`.

That identity is about a ring and says nothing about a *function*.  Its ideals `I i` come with
isomorphisms `A ⧸ I i ≅ 𝒪^h_{Y_i, ξ_i}`, but produced existentially with no recorded behaviour,
so its terms are orders of vanishing in a ring merely isomorphic to the henselian local ring of
a component, by an isomorphism of which nothing is known.

This file replaces those terms by orders of vanishing of an actual element of `𝒪^h_{Y_i, ξ_i}`.
For a *global section* `s` of the generic chart `V` of `Z`, the class of its image in `A` goes to
the image in `𝒪^h_{Y_i, ξ_i}` of its restriction `j_i^♯ s` to a chart `U_i` of the `i`-th
component — by `exists_ringEquiv_henselianLocalRing_quotient_sectionsToHenselianLocalRing`,
whose ideal at the base-change chart is the ideal of the additivity on the nose — so

  `ord_A(σ_V s) - ord_A(σ_V t)
      = ∑_i m_{Y_i, Y} · (ord_{𝒪^h_{Y_i, ξ_i}}(σ_{U_i}(j_i^♯ s))
          - ord_{𝒪^h_{Y_i, ξ_i}}(σ_{U_i}(j_i^♯ t)))`,

`σ` being the canonical maps of Stacks 0EMY on global sections of a chart.  Both sides are now
orders of vanishing of elements named by `s` and `t`, and the identity is the one the cycle-level
forms of Stacks 0EQ2, Stacks 0EQA and Stacks 0EQQ assert at a prime divisor.

## Main results

* `AlgebraicGeometry.Space.exists_natCast_ord_sub_eq_finsum_components_mul_sections`:
  **the additivity, with the component terms read as orders of vanishing of the restrictions of
  two global sections of the generic chart.**  The charts `U_i` of the components and the
  morphisms `j_i : U_i ⟶ V` carry the distinguished point to the distinguished point, are
  surjective on Zariski stalks, commute with the inclusions of the components, and are affine
  when `V` is.  The images of the two restricted sections are nonzerodivisors.

## Implementation notes

The identity is stated at `Ring.ord`, not at `AlgebraicGeometry.Space.PrimeDivisor.ord`: the
latter is the order of vanishing of a *unit of the total ring of fractions* and so carries
`Nontrivial`, `IsNoetherianRing` and `Ring.KrullDimLE 1` as instance arguments, which cannot be
supplied for the henselian local ring of a component inside the existential that produces that
component's prime divisor.  With those instances in scope both sides convert by
`AlgebraicGeometry.Space.PrimeDivisor.ord_mk'`, whose two hypotheses are exactly the
nonzerodivisor conjuncts of the statement.

Nothing here asks `Y` to be reduced, or integral, or `s` and `t` to come from a function: the
multiplicities `m_{Y_i, Y}` of Stacks 0EE9 are `1` for every component exactly when `Y` is
generically reduced, so the interesting case of all three tags is a non-reduced `Y` and a
statement carrying reducedness of the ambient chart would be vacuous there.

The nonzerodivisor property of the restricted sections is proved from the ring-theoretic side.  A
nonzerodivisor of `A` of finite colength lies in no branch of `A`, hence in no minimal prime of
the reduced one-dimensional ring `A ⧸ I i`, hence is a nonzerodivisor there.

The ideals are not quantified existentially in the proof: they are the formula in the chosen
points `w i` of the base changes `V ×_Y Y_i`, because the compatibility on sections mentions the
chart `V ×_Y Y_i` and the restriction map, both of which are formulas in `w i`.  The *statement*
quantifies an opaque pair `(U_i, j_i)` instead of naming the base-change chart, which is both
cheaper to elaborate and strictly more general.

The source has no numbered result here: this is the step inside the proofs of Stacks 0EQ2,
Stacks 0EQA and Stacks 0EQQ at which an order of vanishing on `Y` is written as the weighted sum
of the orders of vanishing on the irreducible components of `Y`.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **A nonzerodivisor of a one-dimensional local ring stays a nonzerodivisor on a
one-dimensional reduced quotient.** If `A` is a local ring of Krull dimension one and `A ⧸ I`
is reduced of Krull dimension one, the image in `A ⧸ I` of a nonzerodivisor of `A` is a
nonzerodivisor. -/
private theorem mem_nonZeroDivisors_quotient_of_ringKrullDim_eq_one {A : Type*} [CommRing A]
    [IsLocalRing A] (hdim : ringKrullDim A = 1) (I : Ideal A)
    (hredI : _root_.IsReduced (A ⧸ I)) (hdimI : ringKrullDim (A ⧸ I) = 1) {a : A} (ha : a ∈ A⁰) :
    Ideal.Quotient.mk I a ∈ (A ⧸ I)⁰ := by
  let := hredI
  refine Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes (Ideal.Quotient.mk I)
    (fun q hq => ?_) ha
  have hq' : Ideal.comap (Ideal.Quotient.mk I) q ∈ I.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q, hq, rfl⟩
  rw [Ideal.minimalPrimes_eq_setOf_mem_minimalPrimes_of_ringKrullDim_eq_one hdim I hdimI] at hq'
  exact hq'.1

section SectionAdditivity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (sY : Y ⟶ D.space) (hYg : D.IsGood sY)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    (Z : PrimeDivisor D.site D.base D.base_mem Y)

include hY hYg hYdec in
/-- **The additivity of the order of vanishing over the irreducible components, for two global
sections of the generic chart.** Let `Y` be an algebraic space which is good over the base of
Situation 0EDT, let `Z` be a prime divisor of `Y` with generic point `ξ`, and assume every
irreducible component of `|Y|` through `ξ` has δ-dimension `dim_δ(Z) + 1`. Write
`A = 𝒪^h_{Y, ξ}` for the henselian local ring of Stacks 0ENK there, `V` for the generic chart of
`Z` and `σ_V : Γ(V, 𝒪_V) → A` for the canonical map of Stacks 0EMY on global sections. Let `s`,
`t` be global sections of `𝒪_V` whose images in `A` are nonzerodivisors. Then there are, for each
irreducible component `Y_i` of `|Y|` through `ξ`,

* a prime divisor `Z_i` of `Y_i` whose generic point `ξ_i` lies over `ξ`,
* an elementary étale neighborhood `U_i` of `ξ_i`, affine when `V` is, and a morphism
  `j_i : U_i ⟶ V` over the inclusion `Y_i ⟶ Y` carrying the distinguished point to the
  distinguished point and surjective on Zariski stalks,

such that the restrictions `j_i^♯ s`, `j_i^♯ t` have nonzerodivisor images in `𝒪^h_{Y_i, ξ_i}`
and

  `ord_A(σ_V s) - ord_A(σ_V t)
      = ∑_i m_{Y_i, Y} · (ord_{𝒪^h_{Y_i, ξ_i}}(σ_{U_i}(j_i^♯ s))
          - ord_{𝒪^h_{Y_i, ξ_i}}(σ_{U_i}(j_i^♯ t)))`,

`m_{Y_i, Y}` being the multiplicity of Stacks 0EE9 of the `i`-th component. -/
theorem exists_natCast_ord_sub_eq_finsum_components_mul_sections
    (hdim : ∀ W : irreducibleComponents (points D.site D.base D.base_mem Y),
      Z.genericPoint D.site D.base D.base_mem Y ∈
          (W : Set (points D.site D.base D.base_mem Y)) →
        deltaDimension D sY
            (integralClosedSubspaceOfComponent D.site D.base D.base_mem hY hYdec W) =
          deltaDimension D sY (Z.toIntegralClosedSubspace D.site D.base D.base_mem) + 1)
    (s t : Γ((Z.genericChart D.site D.base D.base_mem hY hYdec).scheme.left.1, ⊤))
    (hs : Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY hYdec s ∈
      (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))⁰)
    (ht : Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY hYdec t ∈
      (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))⁰) :
    ∃ (Zc : ∀ i : Z.genericComponentIndex D Y hY hYdec,
          PrimeDivisor D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor)
        (_ : ∀ i, pointsMap D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.ι
            ((Zc i).genericPoint D.site D.base D.base_mem
              (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor) =
          Z.genericPoint D.site D.base D.base_mem Y)
        (U : ∀ i, ElementaryEtaleNeighborhood D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            ((Zc i).genericPoint D.site D.base D.base_mem
              (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor))
        (j : ∀ i, (U i).scheme ⟶
          (Z.genericChart D.site D.base D.base_mem hY hYdec).scheme)
        (hj : ∀ i, (j i).left.1 (U i).point =
          (Z.genericChart D.site D.base D.base_mem hY hYdec).point),
      (∀ i, Function.Surjective
          (((Z.genericChart D.site D.base D.base_mem hY
                hYdec).scheme.left.1.presheaf.stalkCongr (.of_eq (hj i).symm)).hom ≫
            (j i).left.1.stalkMap (U i).point).hom) ∧
      (∀ i, yoneda.map (j i) ≫
            (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace =
          (U i).toSpace ≫ (Z.genericComponentSubspace D Y hY hYdec i).subspace.ι) ∧
      (∀ i, IsAffine (U i).scheme.left.1) ∧
      (∀ i, (Zc i).neighborhoodSectionsToGenericHenselianLocalRing D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace) (U i)
            (((j i).left.1.appTop).hom s) ∈
          (↥((Zc i).genericHenselianLocalRing D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)))⁰) ∧
      (∀ i, (Zc i).neighborhoodSectionsToGenericHenselianLocalRing D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace) (U i)
            (((j i).left.1.appTop).hom t) ∈
          (↥((Zc i).genericHenselianLocalRing D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)))⁰) ∧
      ((Ring.ord ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
            (Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY
              hYdec s)).toNat : ℤ) -
          ((Ring.ord ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)
            (Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY
              hYdec t)).toNat : ℤ) =
        ∑ᶠ i : Z.genericComponentIndex D Y hY hYdec,
          irreducibleComponentMultiplicity D Y hY hYdec i.1 *
            (((Ring.ord ↥((Zc i).genericHenselianLocalRing D.site D.base D.base_mem
                  (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
                  ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace))
                ((Zc i).neighborhoodSectionsToGenericHenselianLocalRing D.site D.base D.base_mem
                  (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
                  ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
                  (U i) (((j i).left.1.appTop).hom s))).toNat : ℤ) -
              ((Ring.ord ↥((Zc i).genericHenselianLocalRing D.site D.base D.base_mem
                  (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
                  ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace))
                ((Zc i).neighborhoodSectionsToGenericHenselianLocalRing D.site D.base D.base_mem
                  (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
                  ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
                  (U i) (((j i).left.1.appTop).hom t))).toNat : ℤ)) := by
  classical
  let : IsLocalRing ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) :=
    henselianLocalRing_isLocalRing D.site D.base D.base_mem Y hY
      (Z.genericPoint D.site D.base D.base_mem Y) hYdec
  obtain ⟨hdimA, hnoethA⟩ :=
    PrimeDivisor.ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing D.site D.base
      D.base_mem hY hYdec (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hYg) Z
  let := hnoethA
  let : Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) :=
    Ring.krullDimLE_iff.mpr (by rw [hdimA]; norm_num)
  let := Z.isLocalRing_genericEtaleChartStalk D Y hY hYdec
  let := Z.genericEtaleChartStalkAlgebra D Y hY hYdec
  let := Z.flat_genericEtaleChartStalk D Y hY hYdec
  have hmem : ∀ i : Z.genericComponentIndex D Y hY hYdec,
      Z.genericPoint D.site D.base D.base_mem Y ∈
        (i.1 : Set (points D.site D.base D.base_mem Y)) := by
    intro i
    exact (Z.chartSchemeToPoints_genericEtaleChart_point D.site D.base D.base_mem hY
      hYdec).subst
      (motive := fun p => p ∈ (i.1 : Set (points D.site D.base D.base_mem Y))) i.2
  have hNc : ∀ i : Z.genericComponentIndex D Y hY hYdec,
      HasEtaleLocalProperty D.site D.base D.base_mem
        (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor
        (fun T : Scheme.{u} => IsLocallyNoetherian T) := fun i =>
    hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D
      ((Z.genericComponentSubspace D Y hY hYdec i).subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hYg (Z.genericComponentSubspace D Y hY hYdec i))
  choose Zc hZc using fun i : Z.genericComponentIndex D Y hY hYdec =>
    exists_primeDivisor_pointsMap_genericPoint_eq_of_deltaDimension D sY hYg hYdec Z i.1
      (hmem i) (hdim i.1 (hmem i))
  choose w hw hpw using fun i : Z.genericComponentIndex D Y hY hYdec =>
    exists_point_closedImmersionBaseChangeNeighborhood D.site D.base D.base_mem hY
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
      ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
      (Z.genericComponentSubspace D Y hY hYdec i).subspace.ι
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2
      ((Zc i).genericPoint D.site D.base D.base_mem
        (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor)
      (Z.genericPoint D.site D.base D.base_mem Y) (hZc i)
      (Z.genericChart D.site D.base D.base_mem hY hYdec)
  have hsurj : ∀ i : Z.genericComponentIndex D Y hY hYdec, Function.Surjective
      (((Z.genericChart D.site D.base D.base_mem hY
            hYdec).scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
        ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
          (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace).left.1.stalkMap
            (w i)).hom := by
    intro i
    have hb : Function.Bijective
        (((Z.genericChart D.site D.base D.base_mem hY
            hYdec).scheme.left.1.presheaf.stalkCongr
          (Inseparable.of_eq (hpw i).symm)).hom : _ ⟶ _).hom :=
      ConcreteCategory.bijective_of_isIso _
    rw [CommRingCat.hom_comp]
    exact (surjective_stalkMap_rep_snd D.site D.base D.base_mem
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2
      (Z.genericChart D.site D.base D.base_mem hY hYdec) (w i)).comp hb.2
  choose e he using fun i : Z.genericComponentIndex D Y hY hYdec =>
    exists_ringEquiv_henselianLocalRing_quotient_sectionsToHenselianLocalRing D.site D.base
      D.base_mem hY hYdec (Z.genericPoint D.site D.base D.base_mem Y)
      (Z.genericChart D.site D.base D.base_mem hY hYdec)
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
      ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
      (closedImmersionBaseChangeNeighborhood D.site D.base D.base_mem
        (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
        (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2
        (Z.genericChart D.site D.base D.base_mem hY hYdec) (w i) (hw i) (hpw i))
      ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
        (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace)
      (hpw i) (hsurj i)
  have hsec : ∀ (i : Z.genericComponentIndex D Y hY hYdec)
      (a : Γ((Z.genericChart D.site D.base D.base_mem hY hYdec).scheme.left.1, ⊤)),
      e i (Ideal.Quotient.mk _
          (Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY hYdec a)) =
        (Zc i).neighborhoodSectionsToGenericHenselianLocalRing D.site D.base D.base_mem
          (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
          ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
          (closedImmersionBaseChangeNeighborhood D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2
            (Z.genericChart D.site D.base D.base_mem hY hYdec) (w i) (hw i) (hpw i))
          ((((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
            (Z.genericChart D.site D.base D.base_mem hY
              hYdec).toSpace).left.1.appTop).hom a) := fun i a => he i a
  have hordi := fun (i : Z.genericComponentIndex D Y hY hYdec)
      (a : Γ((Z.genericChart D.site D.base D.base_mem hY hYdec).scheme.left.1, ⊤)) =>
    (Ring.ord_ringEquiv (e i) (Ideal.Quotient.mk _
        (Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY
          hYdec a))).trans (congrArg (Ring.ord _) (hsec i a))
  have hred : ∀ i : Z.genericComponentIndex D Y hY hYdec,
      _root_.IsReduced (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸
        (RingHom.ker (((Z.genericChart D.site D.base D.base_mem hY
              hYdec).scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
            ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
              (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace).left.1.stalkMap
                (w i)).hom).map
          (stalkToHenselianLocalRing D.site D.base D.base_mem Y hY
            (Z.genericPoint D.site D.base D.base_mem Y) hYdec
            (Z.genericChart D.site D.base D.base_mem hY hYdec))) := by
    intro i
    have := PrimeDivisor.isReduced_genericHenselianLocalRing D.site D.base D.base_mem
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
      ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
      (Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace (hNc i) (Zc i)
    exact isReduced_of_injective (e i).toRingHom (e i).injective
  have hdimI : ∀ i : Z.genericComponentIndex D Y hY hYdec,
      ringKrullDim (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸
        (RingHom.ker (((Z.genericChart D.site D.base D.base_mem hY
              hYdec).scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
            ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
              (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace).left.1.stalkMap
                (w i)).hom).map
          (stalkToHenselianLocalRing D.site D.base D.base_mem Y hY
            (Z.genericPoint D.site D.base D.base_mem Y) hYdec
            (Z.genericChart D.site D.base D.base_mem hY hYdec))) = 1 := fun i =>
    (ringKrullDim_eq_of_ringEquiv (e i)).trans
      (PrimeDivisor.ringKrullDim_genericHenselianLocalRing_eq_one D.site D.base D.base_mem
        (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
        ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
        (Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace (hNc i) (Zc i))
  have hinc := (componentIdealFamily_ringEquiv_stalkToHenselianLocalRing_le_iff D.site D.base
    D.base_mem hY hYdec (Z.genericPoint D.site D.base D.base_mem Y)
    (Z.genericChart D.site D.base D.base_mem hY hYdec)
    (fun i : Z.genericComponentIndex D Y hY hYdec =>
      (Z.genericComponentSubspace D Y hY hYdec i).subspace)
    (fun i => (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace)
    (fun i => (Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
    (fun i => by
      rw [subspacePointSet_integralClosedSubspaceOfComponent]
      exact i.1.2)
    (fun i => (Zc i).genericPoint D.site D.base D.base_mem
      (Z.genericComponentSubspace D Y hY hYdec i).subspace.toFunctor) w hw hpw).2
  have hnzq : ∀ (i : Z.genericComponentIndex D Y hY hYdec)
      (a : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec)),
      a ∈ (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))⁰ →
      Ideal.Quotient.mk
          ((RingHom.ker (((Z.genericChart D.site D.base D.base_mem hY
                hYdec).scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
              ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
                (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace).left.1.stalkMap
                  (w i)).hom).map
            (stalkToHenselianLocalRing D.site D.base D.base_mem Y hY
              (Z.genericPoint D.site D.base D.base_mem Y) hYdec
              (Z.genericChart D.site D.base D.base_mem hY hYdec))) a ∈
        (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec) ⧸
          (RingHom.ker (((Z.genericChart D.site D.base D.base_mem hY
                hYdec).scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
              ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
                (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace).left.1.stalkMap
                  (w i)).hom).map
            (stalkToHenselianLocalRing D.site D.base D.base_mem Y hY
              (Z.genericPoint D.site D.base D.base_mem Y) hYdec
              (Z.genericChart D.site D.base D.base_mem hY hYdec)))⁰ := by
    intro i a ha
    exact mem_nonZeroDivisors_quotient_of_ringKrullDim_eq_one hdimA _ (hred i) (hdimI i) ha
  have hnzrw : ∀ (i : Z.genericComponentIndex D Y hY hYdec)
      (a : Γ((Z.genericChart D.site D.base D.base_mem hY hYdec).scheme.left.1, ⊤)),
      Z.chartSectionsToGenericHenselianLocalRing D.site D.base D.base_mem hY hYdec a ∈
          (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))⁰ →
      (Zc i).neighborhoodSectionsToGenericHenselianLocalRing D.site D.base D.base_mem
          (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
          ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)
          (closedImmersionBaseChangeNeighborhood D.site D.base D.base_mem
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
            (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2
            (Z.genericChart D.site D.base D.base_mem hY hYdec) (w i) (hw i) (hpw i))
          ((((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
            (Z.genericChart D.site D.base D.base_mem hY
              hYdec).toSpace).left.1.appTop).hom a) ∈
        (↥((Zc i).genericHenselianLocalRing D.site D.base D.base_mem
          (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
          ((Z.genericComponentSubspace D Y hY hYdec i).isIntegralSpace.isDecentSpace)))⁰ := by
    intro i a ha
    rw [← hsec i a, ← MulEquivClass.map_nonZeroDivisors (e i)]
    exact ⟨_, hnzq i _ ha, rfl⟩
  refine ⟨Zc, hZc, fun i => closedImmersionBaseChangeNeighborhood D.site D.base D.base_mem
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.1
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2
      (Z.genericChart D.site D.base D.base_mem hY hYdec) (w i) (hw i) (hpw i),
    fun i => (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
      (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace,
    hpw, hsurj,
    fun i => ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.w
      (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace).symm,
    fun i => isAffine_closedImmersionBaseChangeNeighborhood D.site D.base D.base_mem hY
      (Z.genericChart D.site D.base D.base_mem hY hYdec)
      (Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace (Zc i) (w i) (hw i) (hpw i),
    fun i => hnzrw i s hs, fun i => hnzrw i t ht, ?_⟩
  refine (natCast_ord_sub_eq_finsum_components_mul_of_le_iff _ _
    (isRegular_iff_mem_nonZeroDivisors.mpr hs).left
    (isRegular_iff_mem_nonZeroDivisors.mpr ht).left hdimA
    (by simpa only [Ring.ord] using Ring.ord_ne_top hs)
    (by simpa only [Ring.ord] using Ring.ord_ne_top ht)
    (fun i => (RingHom.ker (((Z.genericChart D.site D.base D.base_mem hY
          hYdec).scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
        ((Z.genericComponentSubspace D Y hY hYdec i).isClosedSubspace.2.rep.snd
          (Z.genericChart D.site D.base D.base_mem hY hYdec).toSpace).left.1.stalkMap
            (w i)).hom).map
      (stalkToHenselianLocalRing D.site D.base D.base_mem Y hY
        (Z.genericPoint D.site D.base D.base_mem Y) hYdec
        (Z.genericChart D.site D.base D.base_mem hY hYdec))) hred hdimI
    (componentOfFlatBranch D.site D.base D.base_mem hY hYdec
      (Z.genericEtaleChart D.site D.base D.base_mem hY hYdec)
      (Z.genericChart D.site D.base D.base_mem hY hYdec).point
      ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hY hYdec))
    (fun i q => (hinc i q).trans ?_)
    (fun i => irreducibleComponentMultiplicity D Y hY hYdec i.1)
    (fun q => PrimeDivisor.natCast_length_localizationAtPrime_eq_multiplicity D Y hY hYdec Z
      q)).trans ?_
  · rw [subspacePointSet_integralClosedSubspaceOfComponent]
    exact ⟨fun h => Subtype.ext (Subtype.ext h), fun h => congrArg (fun W => (W.1 :
      irreducibleComponents (points D.site D.base D.base_mem Y)).1) h⟩
  · refine finsum_congr fun i => ?_
    exact congrArg₂ (fun m n : ℤ => irreducibleComponentMultiplicity D Y hY hYdec i.1 * (m - n))
      (congrArg (fun k : ℕ∞ => (k.toNat : ℤ)) (hordi i s))
      (congrArg (fun k : ℕ∞ => (k.toNat : ℤ)) (hordi i t))

end SectionAdditivity

end AlgebraicGeometry.Space

end

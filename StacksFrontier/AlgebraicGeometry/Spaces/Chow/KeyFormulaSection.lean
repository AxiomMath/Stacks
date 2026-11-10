module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCycleIdentities
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder

/-!
# The situation of Section 0EQU, at the canonical choices

In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n`, let `ℒ` and `𝒩` be
invertible `𝒪_X`-modules with nonzero (equivalently regular) meromorphic sections `s` and `t`.
Section 0EQU takes a locally finite family `{Z_i}` of prime divisors such that `s` generates
`ℒ_ξ` and `t` generates `𝒩_ξ` at the generic point `ξ` of every prime divisor not in the family,
picks generators `s_i ∈ ℒ_{ξ_i}`, writes `s = f_i s_i` in `Q(B_i)`, `B_i = 𝒪^h_{X,ξ_i}`, and
records

1. `div_ℒ(s) = ∑ ord_{Z_i,ℒ}(s) [Z_i]`,
2. `ord_{Z_i,ℒ}(s) = ord_{B_i}(f_i)`,
3. `c₁(𝒩) ∩ div_ℒ(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{𝒩|_{Z_i}}(t_i|_{Z_i})` in `CH_{n-2}(X)`,

and symmetrically with the roles of `(ℒ, s)` and `(𝒩, t)` exchanged.

## The encoding of the generators

The module `ℒ_ξ` of the source is free of rank one over `B = 𝒪^h_{X,ξ}`, with the canonical
generator `s_ξ` of Stacks 0EPR against which the ratio `s / s_ξ` is
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`.  Every generator of `ℒ_ξ` is
`v · s_ξ` for exactly one unit `v ∈ B^*`, so a generator `s_i` is recorded here by the unit
`v_i`, and `s = f_i s_i` reads `f_i · v_i = s / s_ξ` in `Q(B)`.  "`s` generates `ℒ_ξ`" reads
`s / s_ξ ∈ B^*`, which is `AlgebraicGeometry.Space.PrimeDivisor.SectionGenerates`.

## Main results

* `AlgebraicGeometry.Space.orderOfVanishingSection_canonical_eq_ord`: claim (2).
* `AlgebraicGeometry.Space.canonicalDivisorCycle_apply_family` and
  `AlgebraicGeometry.Space.canonicalDivisorCycle_apply_eq_zero_of_notMem`: claim (1).
* `AlgebraicGeometry.Space.canonicalFirstChernCap_canonicalDivisorCycleAt`: claim (3), for an
  arbitrary regular meromorphic section of `𝒩|_{Z_i}` in place of `t_i|_{Z_i}` — the class in
  `CH_{n-2}(X)` does not depend on that section.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)

/-- **"`s` generates `ℒ_ξ`"** at the generic point `ξ` of a prime divisor `Z`, for a meromorphic
section `s` of an invertible module on a good integral algebraic space: the ratio `s / s_ξ` of
`s` against the canonical generator `s_ξ` of `ℒ_ξ` (Stacks 0EPR) is the image of a unit of
`𝒪^h_{X,ξ}`. -/
def PrimeDivisor.SectionGenerates (Z : PrimeDivisor D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L) : Prop :=
  ∃ w : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)), IsUnit w ∧
    Z.canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) L hL
        hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s =
      algebraMap _ (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)) w

/-- At the generic point of every prime divisor the Henselian local ring is nontrivial,
Noetherian and of Krull dimension at most one. -/
private theorem genericHenselianLocalRing_instances
    (hint : IsIntegralSpace D.site D.base D.base_mem X) :
    (∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX))) ∧
    (∀ W : PrimeDivisor D.site D.base D.base_mem X,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX))) ∧
    (∀ W : PrimeDivisor D.site D.base D.base_mem X,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX))) :=
  ⟨fun W => W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX),
    fun W => W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX),
    fun W => W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)⟩

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)

include hs in
/-- **Section 0EQU, claim (2): `ord_{Z,ℒ}(s) = ord_B(f)`.**  For a generator `v · s_ξ` of `ℒ_ξ`
(`v` a unit of `B = 𝒪^h_{X,ξ}`) and `f ∈ Q(B)` with `s = f · (v s_ξ)`, the order of vanishing of
Stacks 0EPR of `s` along `Z` is `ord_B(f)`. -/
theorem orderOfVanishingSection_canonical_eq_ord (Z : PrimeDivisor D.site D.base D.base_mem X)
    (v : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))
    (hv : IsUnit v) (f : Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX))
    (hf : f * algebraMap _ _ v =
      Z.canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) L
        hL hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s) :
    haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
      W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
      W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
      W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    ∃ hfu : IsUnit f,
      orderOfVanishingSection.{u, u} D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX) Z L s
          (Z.canonicalLocalRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
            L hL hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) =
        Z.ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) f hfu := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances D sX hX hint
  have hρ := Z.isUnit_canonicalGenericRatio D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) L hL hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s hs
  have hvu : IsUnit (algebraMap _ (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)) v) := hv.map _
  have hfu : IsUnit f := isUnit_of_mul_isUnit_left (hf ▸ hρ)
  refine ⟨hfu, ?_⟩
  unfold orderOfVanishingSection
  rw [Z.ord_congr D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) _ (hfu.mul hvu)
    ((Z.coe_canonicalLocalRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
      L hL hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s hs).trans hf.symm),
    Z.ord_mul D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) f _ hfu hvu,
    Z.ord_algebraMap D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) v
      (hv.mem_nonZeroDivisors), Stacks.Chow.ord_eq_zero_of_isUnit hv]
  simp

/-! ### Claim (1): `div_ℒ(s)` is carried by the family -/

section ClaimOne

variable {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))

/-- The coefficient of `div_ℒ(s)` at a prime divisor is the order of vanishing of Stacks 0EPR
at the canonical ratio. -/
theorem canonicalDivisorCycle_apply_primeDivisor (Z : PrimeDivisor D.site D.base D.base_mem X) :
    (canonicalDivisorCycle D sX hX hint L hL s hs hn).1
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
        W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX) hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
        W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX) hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
      haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
        W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX) hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
      orderOfVanishingSection.{u, u} D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX) Z L s
          (Z.canonicalLocalRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
            L hL hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances D sX hX hint
  exact divisorCycleCoefficients_toIntegralClosedSubspace D sX hX _ L s _ Z

/-- **Section 0EQU, claim (1), away from the family.** If `s` generates `ℒ_ξ` at the generic
point of every prime divisor outside the family `{Z_i}`, the coefficient of `div_ℒ(s)` at every
integral closed subspace outside the family is zero, so that `div_ℒ(s) = ∑ ord_{Z_i,ℒ}(s) [Z_i]`
(the coefficients at the members being given by
`AlgebraicGeometry.Space.canonicalDivisorCycle_apply_primeDivisor` and claim (2)). -/
theorem canonicalDivisorCycle_apply_eq_zero_of_notMem {I : Type v}
    (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : ∀ i, (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem ≠ W) :
    (canonicalDivisorCycle D sX hX hint L hL s hs hn).1 W = 0 := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances D sX hX hint
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 W) = 1
  · refine (divisorCycleCoefficients_of_codimension_eq_one D sX hX _ L s _ hcod).trans ?_
    have hP : ∀ i, Zf i ≠ W.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod := by
      intro i hi
      exact hW i (by rw [hi, IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor])
    obtain ⟨w, hw, hwr⟩ := hcov _ hP
    exact orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit D.site D.base D.base_mem
      hX.1 (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) _ L hL s hs hw hwr
  · exact divisorCycleCoefficients_of_codimension_ne_one D sX hX _ L s _ hcod

end ClaimOne

/-! ### The order of vanishing of a power -/

/-- The order of vanishing of an integer power of an invertible rational function is that
multiple of its order of vanishing. -/
theorem GenericFractionEmbedding.ord_zpow {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {hdec : IsDecentSpace B S hS Y} (E : GenericFractionEmbedding B S hS hY hdec)
    (g : (rationalFunctions B S hS hY)ˣ) (a : ℤ) : E.ord (g ^ a) = a • E.ord g := by
  have h1 : E.ord 1 = 0 := by
    have h := E.ord_mul 1 1
    rw [mul_one] at h
    funext W
    have hW := congrFun h W
    simp only [Pi.add_apply, Pi.zero_apply] at hW ⊢
    omega
  let φ : (rationalFunctions B S hS hY)ˣ →* Multiplicative (PrimeDivisor B S hS Y → ℤ) :=
    { toFun := fun g => Multiplicative.ofAdd (E.ord g)
      map_one' := by rw [h1]; rfl
      map_mul' := fun g g' => by rw [E.ord_mul]; rfl }
  exact congrArg Multiplicative.toAdd (map_zpow φ g a)

/-! ### Claim (3): `c₁(𝒩) ∩ div_ℒ(s)` over the family -/

section ClaimThree

/-- Two regular meromorphic sections of an invertible module on a good integral algebraic space
have Weil divisors differing by a principal divisor, and so does any integer multiple of the
difference: `a · (div_ℳ(τ) - div_ℳ(τ')) = div(g^a)` for the rational function `g = τ / τ'`
(Stacks 0EPT). -/
theorem isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (τ τ' : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ)
    (hτ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ') {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) (a : ℤ) :
    IsPrincipalDivisorCycle D sY k (a • (canonicalDivisorCycleAt D sY hY hintY M hM τ hτ hk -
      canonicalDivisorCycleAt D sY hY hintY M hM τ' hτ' hk)) := by
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1
    (isDecentSpace_of_isGood D sY hY) hintY hNY
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨g, hg⟩ := exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord
    D.site D.base D.base_mem hY.1 (isDecentSpace_of_isGood D sY hY) hintY hNY M hM τ τ' hτ hτ'
  refine ⟨hY, hintY, g ^ a, ?_⟩
  funext W
  change a • ((canonicalDivisorCycle D sY hY hintY M hM τ hτ hk).1 W -
      (canonicalDivisorCycle D sY hY hintY M hM τ' hτ' hk).1 W) = _
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 W) = 1
  · rw [show (canonicalDivisorCycle D sY hY hintY M hM τ hτ hk).1 W = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ M τ _ hcod,
      show (canonicalDivisorCycle D sY hY hintY M hM τ' hτ' hk).1 W = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ M τ' _ hcod]
    unfold divisorCoefficients
    rw [hg, add_sub_cancel_left]
    simp only [principalDivisorCycleCoefficients, dite_eq_left hcod]
    have hz := congrFun (E.ord_zpow g a) (W.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)
    exact hz.symm
  · rw [show (canonicalDivisorCycle D sY hY hintY M hM τ hτ hk).1 W = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ M τ _ hcod,
      show (canonicalDivisorCycle D sY hY hintY M hM τ' hτ' hk).1 W = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ M τ' _ hcod]
    simp only [principalDivisorCycleCoefficients, dite_eq_right hcod, sub_self, smul_zero]

include hint in
/-- A prime divisor of a good integral algebraic space of δ-dimension `k + 2`, viewed as a good
integral algebraic space itself, has δ-dimension `k + 1` (Stacks 0EPZ). -/
theorem deltaDimensionClosed_univ_toIntegralClosedSubspace {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (Z : PrimeDivisor D.site D.base D.base_mem X) :
    deltaDimensionClosed D ((Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX _) Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
  rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX,
    deltaDimension_toIntegralClosedSubspace D sX hX hint (deltaDimensionFunction D sX hX)
      (deltaDimensionFunction_apply D sX hX) hn Z, add_sub_cancel_right]

/-- **Section 0EQU, claim (3).** In Situation 0EDT let `X/B` be good, `X` integral with
`dim_δ(X) = n = k + 2`, let `ℒ`, `𝒩` be invertible with `s` a regular meromorphic section of
`ℒ`, and let `{Z_i}` be a locally finite family of prime divisors such that `s` generates `ℒ_ξ`
at the generic point of every prime divisor outside it.  For generators `s_i = v_i s_{ξ_i}` of
`ℒ_{ξ_i}` write `s = f_i s_i`, `f_i ∈ Q(B_i)^*`.  Then for any regular meromorphic sections
`τ_i` of `𝒩|_{Z_i}` — in particular for the source's `t_i|_{Z_i}` —

`c₁(𝒩) ∩ div_ℒ(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{𝒩|_{Z_i}}(τ_i)`  in `CH_{n-2}(X)`.

The cap product is the one of Stacks 0EQJ at the canonical choices,
`AlgebraicGeometry.Space.canonicalFirstChernCap`, the divisors are those of Stacks 0EQE at the
canonical ratios, and `CH_{n-2}(X)` is the Chow group of Stacks 0EQ6.  The second identity of
the section is this one with `(ℒ, s)` and `(𝒩, t)` exchanged. -/
@[stacks 0EQU "the cycle identities of the section, in CH_{n-2}(X) as the source states them: \
c_1(N) ∩ div_L(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i), with everything at the \
canonical choices (the cap product, the divisors and the ratios s = f_i s_i are constructed, not \
carried) and for an arbitrary regular meromorphic section of N|Z_i in place of t_i|Z_i; the \
second identity is the same statement with (L, s) and (N, t) exchanged. Claims (1)-(2) of the \
section are canonicalDivisorCycle_apply_eq_zero_of_notMem, \
canonicalDivisorCycle_apply_primeDivisor \
and orderOfVanishingSection_canonical_eq_ord"]
theorem canonicalFirstChernCap_canonicalDivisorCycleAt
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    {I : Type v} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hinj : Function.Injective Zf)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s)
    {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (v : ∀ i, ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))
    (hv : ∀ i, IsUnit (v i))
    (f : ∀ i, ((Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX))ˣ)
    (hf : ∀ i, (f i : (Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)) * algebraMap _ _ (v i) =
      (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) L hL hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s)
    (τ : ∀ i, MeromorphicSection.{u, u} D.site D.base D.base_mem
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX _).1
      (integralClosedSubspaceRestrict D sX hX N
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)))
    (hτ : ∀ i, IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _
      (isGood_integralClosedSubspace D sX hX _).1 _ (τ i)) :
    haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
      W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
      W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
      W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    canonicalFirstChernCap.{u, v} D sX hX N hN k
        (canonicalDivisorCycleAt D sX hX hint L hL s hs hn) =
      chowClass.{v} D sX hX k (cycleFamilySum D sX hX
        (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin k
        (fun i => (Zf i).ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
            (f i : (Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
              (isDecentSpace_of_isGood D sX hX)) (f i).isUnit •
          canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX _)
            ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
            (integralClosedSubspaceRestrict D sX hX N
              ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem))
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN _) (τ i) (hτ i)
            (deltaDimensionClosed_univ_toIntegralClosedSubspace D sX hX hint hn (Zf i)))) := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances D sX hX hint
  have hdim : ∀ i, deltaDimension D sX
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1 := fun i =>
    (deltaDimension_toIntegralClosedSubspace D sX hX hint (deltaDimensionFunction D sX hX)
      (deltaDimensionFunction_apply D sX hX) hn (Zf i)).trans (add_sub_cancel_right _ _)
  have hinj' : Function.Injective
      fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem :=
    (PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem).comp hinj
  have hcover : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      (canonicalDivisorCycleAt D sX hX hint L hL s hs hn).1 W ≠ 0 →
        ∃ i, (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem = W := by
    intro W hW
    by_contra h
    push Not at h
    exact hW (canonicalDivisorCycle_apply_eq_zero_of_notMem D sX hX hint L hL s hs hn Zf hcov W h)
  unfold canonicalFirstChernCap
  rw [AddMonoidHom.comp_apply,
    firstChernCapCycleMap_eq_cycleFamilySum D sX hX k _ _ _ hinj' hfin hdim hcover,
    ← sub_eq_zero, ← map_sub, ← cycleFamilySum_sub]
  refine chowClass_cycleFamilySum_eq_zero.{v} D sX hX k
    (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin _ hdim fun i => ?_
  have hα : (canonicalDivisorCycleAt D sX hX hint L hL s hs hn).1
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) =
      (Zf i).ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        (f i : (Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)) (f i).isUnit := by
    rw [canonicalDivisorCycleAt_coe, canonicalDivisorCycle_apply_primeDivisor]
    obtain ⟨hfu, h⟩ := orderOfVanishingSection_canonical_eq_ord D sX hX hint L hL s hs (Zf i)
      (v i) (hv i) _ (hf i)
    exact h
  rw [hα, ← smul_sub]
  exact isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub D _
    (isGood_integralClosedSubspace D sX hX _)
    ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN _) _ _ _ _ _ _

end ClaimThree

/-! ### The family exists -/

section Existence

/-- `s` generates `ℒ_ξ` at the generic point of every prime divisor whose generic point lies in
the generating locus of `s`: there the coefficient of Stacks 0EPR is the image of a unit of
`𝒪_{U,u}`, and that unit maps to a unit of `𝒪^h_{X,ξ}`. -/
theorem PrimeDivisor.sectionGenerates_of_mem_generatingLocus
    (W : PrimeDivisor D.site D.base D.base_mem X)
    (hW : W.genericPoint D.site D.base D.base_mem X ∈
      generatingLocus D.site D.base D.base_mem hX.1 L s) :
    W.SectionGenerates D sX hX hint L hL s := by
  obtain ⟨V, hrange, hgen⟩ := hW
  obtain ⟨w, hw, hwc⟩ :=
    W.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_generatesOnChart D.site D.base
      D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L hL s V hrange hgen
  refine ⟨W.genericStalkSectionsToHenselian D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) w, hw.map _, ?_⟩
  rw [PrimeDivisor.canonicalGenericRatio, hwc,
    W.genericStalkMeromorphicToGeneric_algebraMap D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) w]

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)

include hs ht in
/-- **Section 0EQU: the family exists** ("Such a set exists by Spaces over Fields, Lemma 0EPS").
The prime divisors at whose generic point `s` fails to generate `ℒ_ξ` or `t` fails to generate
`𝒩_ξ` form a locally finite family; it is the smallest family the section may be taken over. -/
@[stacks 0EQU "existence of the family {Z_i}: the prime divisors at whose generic point s or t \
fails to generate form a locally finite family (by 0EPS)"]
theorem locallyFinite_primeDivisor_not_sectionGenerates :
    LocallyFinite fun W : {W : PrimeDivisor D.site D.base D.base_mem X //
        ¬ (W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)} =>
      W.1.support D.site D.base D.base_mem X := by
  classical
  have hirr := hint.irreducibleSpace
  have hUs := nonempty_generatingLocus_of_isRegularMeromorphicSection D.site D.base D.base_mem
    hX.1 L hint.hasEtaleLocalProperty_isReduced hint.irreducibleSpace.toNonempty hL s hs
  have hUt := nonempty_generatingLocus_of_isRegularMeromorphicSection D.site D.base D.base_mem
    hX.1 N hint.hasEtaleLocalProperty_isReduced hint.irreducibleSpace.toNonempty hN t ht
  have hopen_s := isOpen_generatingLocus D.site D.base D.base_mem hX.1 L s
  have hopen_t := isOpen_generatingLocus D.site D.base D.base_mem hX.1 N t
  have hne : (generatingLocus D.site D.base D.base_mem hX.1 L s ∩
      generatingLocus D.site D.base D.base_mem hX.1 N t).Nonempty :=
    nonempty_preirreducible_inter hopen_s hopen_t hUs hUt
  have h := locallyFinite_primeDivisor_of_genericPoint_notMem D.site D.base D.base_mem hX.1
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) hirr
    (fun W => ¬ (W.SectionGenerates D sX hX hint L hL s ∧
      W.SectionGenerates D sX hX hint N hN t)) _ (hopen_s.inter hopen_t) hne
    (fun W hW hmem => hW ⟨W.sectionGenerates_of_mem_generatingLocus D sX hX hint L hL s hmem.1,
      W.sectionGenerates_of_mem_generatingLocus D sX hX hint N hN t hmem.2⟩)
  refine (h.comp_injective Subtype.val_injective).subset fun W => ?_
  simp only [Function.comp_apply, ite_eq_left W.2, subset_refl]

end Existence

end AlgebraicGeometry.Space

end

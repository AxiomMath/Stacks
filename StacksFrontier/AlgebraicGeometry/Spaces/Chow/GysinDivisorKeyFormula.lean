module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GlobalSectionGenericRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaTameCarrierCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.SectionGeneratesOffZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusFirstChernCapPushforward

/-!
# Stacks 0ER9: `i^*div_𝒩(t) = c₁(𝒩) ∩ [D]_{n-1}` in `CH_{n-2}(D)`

In Situation 0EDT let `X/B` be good, `X` integral with `n = dim_δ(X)`, let `ℒ` be an invertible
`𝒪_X`-module with a nonzero global section `σ` and let `i : D = Z(σ) → X` be the closed immersion
of its vanishing locus (Stacks 0845) — the effective Cartier divisor of the source, presented as
the pair `(ℒ, σ) = (𝒪_X(D), s)` the source immediately passes to.  Let `𝒩` be invertible with a
nonzero meromorphic section `t`.  Then

`i^*div_𝒩(t) = c₁(𝒩) ∩ [D]_{n-1}`  in  `CH_{n-2}(D)`.

## The two sides, and why they are compared on `D`

Both sides are already available **as cycles on `X`**, with nothing assumed:

* `AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap` is
  `i_*(i^*α) = c₁(ℒ) ∩ α` at the component rule
  `AlgebraicGeometry.Space.restrictedSectionChernRule`, whose value off `D` is *forced* to be
  `div_{ℒ|_W}(σ|_W)`;
* `cycleGroupClosedPushforward_firstChernCapCycleMap_vanishingLocusTopCycleAt`
  is `i_*(c₁(𝒩) ∩ [D]_{n-1}) = c₁(𝒩) ∩ div_ℒ(σ)`.

So the difference of the pushforwards is the first cycle of the key formula of Stacks 0EQV, and
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_keyFormulaDivisorSum` says
that cycle is rationally equivalent to zero **within the members at which the chosen generator of
`ℒ_{ξ_i}` is not already `σ`** — which by Stacks 0845 are exactly the members contained in `D`.
The descent of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical`
then turns that into a rational equivalence of the two cycles **on `D`**, which is the source's
own closing sentence and the reason the lemma is an identity in `CH_{n-2}(D)` and not merely in
`CH_{n-2}(X)`.

The matching must therefore be *exact at the level of cycles* with the source's own choice
`s_i = σ` at every `Z_i ⊄ D`: replacing `div_{ℒ|_W}(σ|_W)` by the divisor of some other generator
at such a `W` changes the cycle by a principal divisor **supported outside `|D|`**, which no
rational equivalence on `D` can absorb.  That choice is available because `σ` generates `ℒ_ξ` at
the generic point of every prime divisor not contained in `Z(σ)`
(`AlgebraicGeometry.Space.PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_not_le`), and
the generator it delivers to `Z_i` is the honest restriction `σ|_{Z_i}`
(`PrimeDivisor.henselianUnitRestriction_eq_globalSectionMeromorphic_restrict`).

## Main definitions

* `AlgebraicGeometry.Space.generatorChernRule`: the component rule of Stacks 0EQJ determined by a
  family of units `u_Z` of `𝒪^h_{X,ξ_Z}`, with value `div_{ℒ|_Z}((u_Z · s_{ξ_Z})|_Z)` at a prime
  divisor `Z` — the source's "pick generators `s_i` of `ℒ_{ξ_i}`", made at every prime divisor at
  once.
* `AlgebraicGeometry.Space.sectionGeneratorUnit`: the unit of `𝒪^h_{X,ξ_Z}` with `σ = u_Z s_{ξ_Z}`
  at a prime divisor `Z ⊄ Z(σ)`, and `1` elsewhere: the source's choice "`s_i = s` if
  `Z_i ⊄ D`".

## Main results

* `AlgebraicGeometry.Space.restrictedSectionChernRule_generatorChernRule`: off `D` the rule
  forced by the Gysin map is the generator rule of `AlgebraicGeometry.Space.sectionGeneratorUnit`.
* `AlgebraicGeometry.Space.firstChernCapCycleMap_generatorChernRule_sub_eq_keyFormulaDivisorSum`:
  the difference of the two cap products *is* the first cycle of the key formula, as cycles.
* `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_canonicalDivisorCycleAt`:
  **Stacks 0ER9.**

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))

/-! ### The component rule given by a family of generators -/

section GeneratorRule

/-- The Weil divisor of Stacks 0EQE at the canonical ratios depends on the meromorphic section
only through the section itself: the regularity hypothesis is a proposition. -/
theorem canonicalDivisorCycleAt_congr_section
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    {a b : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M}
    (ha : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M a)
    (hb : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M b) {m : ℤ}
    (hm : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((m + 1 : ℤ) : EInt))
    (hab : a = b) :
    canonicalDivisorCycleAt D sY hY hintY M hM a ha hm =
      canonicalDivisorCycleAt D sY hY hintY M hM b hb hm := by
  subst hab
  rfl

/-- A family of units of the henselian local rings `𝒪^h_{X,ξ_Z}` at the generic points of the
prime divisors of `X`: the source's choice of generators `s_i = v_i s_{ξ_i}` of `ℒ_{ξ_i}`, made at
every prime divisor at once.  Every generator of `ℒ_{ξ}` is `v · s_ξ` for a unique unit `v`. -/
abbrev GenericUnitFamily : Type (u + 1) :=
  ∀ Z : PrimeDivisor D.site D.base D.base_mem X,
    (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ

include hint hn in
/-- An integral closed subspace of δ-dimension `k + 1` of a good integral algebraic space of
δ-dimension `k + 2` has codimension one, hence is a prime divisor (Stacks 0EPZ). -/
theorem codimension_integralClosedSubspaceSupport_eq_one
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = k + 1) :
    codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 W) = 1 :=
  ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint (deltaDimensionFunction D sX hX)
      (deltaDimensionFunction_apply D sX hX) hn W).out 3 2).mp
    (hW.trans (add_sub_cancel_right (k + 1) 1).symm)

/-- **The component rule of Stacks 0EQJ given by a family of generators.**  At an integral closed
subspace `W ⊆ X` of δ-dimension `k + 1` — a prime divisor `Z`, by Stacks 0EPZ — the value is the
Weil divisor `div_{ℒ|_Z}((u_Z · s_{ξ_Z})|_Z)` of Stacks 0EQE of the restriction to `Z` of the
generator of `ℒ_{ξ_Z}` named by the unit `u_Z`, that is
`AlgebraicGeometry.Space.PrimeDivisor.restrictedGeneratorDivisor`. -/
def generatorChernRule (u : GenericUnitFamily D sX hX) :
    FirstChernComponentCycleRule D sX k := fun W _ =>
  if hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 W) = 1 then
    (W.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod).restrictedGeneratorDivisor D sX hX hint
      L hL hn (u _)
  else 0

/-- **The value of `AlgebraicGeometry.Space.generatorChernRule` at a prime divisor.**  At the
integral closed subspace underlying a prime divisor `Z` the rule is
`div_{ℒ|_Z}((u_Z · s_{ξ_Z})|_Z)`. -/
theorem generatorChernRule_toIntegralClosedSubspace (u : GenericUnitFamily D sX hX)
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (hW : deltaDimension D sX (Z.toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1) :
    generatorChernRule D sX hX hint L hL hn u
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) hW =
      Z.restrictedGeneratorDivisor D sX hX hint L hL hn (u Z) := by
  have hcod := Z.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
  have key : ∀ P : PrimeDivisor D.site D.base D.base_mem X, P = Z →
      HEq (P.restrictedGeneratorDivisor D sX hX hint L hL hn (u P))
        (Z.restrictedGeneratorDivisor D sX hX hint L hL hn (u Z)) := by
    rintro P rfl
    exact HEq.rfl
  rw [generatorChernRule]
  exact (dite_eq_left hcod).trans
    (eq_of_heq (key _ (IntegralClosedSubspace.toPrimeDivisor_eq D.site D.base D.base_mem hX.1
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem) hcod Z rfl)))

end GeneratorRule

/-! ### The source's choice `s_i = σ` off the vanishing locus -/

section GeneratorUnit

variable (σ : L.sections)

/-- **The source's choice "`s_i = s` whenever `Z_i ⊄ D`".**  At a prime divisor `Z` not contained
in the vanishing locus `D = Z(σ)` of a global section `σ` of an invertible `ℒ`, the section `σ`
generates `ℒ_{ξ_Z}`
(`AlgebraicGeometry.Space.PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_not_le`), so
`σ = u · s_{ξ_Z}` for a unit `u` of `𝒪^h_{X,ξ_Z}`; this is that unit, and `1` at the prime
divisors contained in `D`, where the source leaves the choice free. -/
def sectionGeneratorUnit : GenericUnitFamily D sX hX := fun Z =>
  if hZ : Z.subspace ≤ (vanishingLocus D sX hX L σ).1 then 1
  else (Z.sectionGenerates_globalSectionMeromorphic_of_not_le D sX hX hint L hL σ
    hZ).choose_spec.1.unit

/-- **`σ = u_Z · s_{ξ_Z}` at every prime divisor not contained in `Z(σ)`.**  The defining
property of `AlgebraicGeometry.Space.sectionGeneratorUnit`: the ratio `σ / s_{ξ_Z}` of Stacks
0EPR is the image of that unit. -/
theorem canonicalGenericRatio_globalSectionMeromorphic_sectionGeneratorUnit
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (hZ : ¬ Z.subspace ≤ (vanishingLocus D sX hX L σ).1) :
    Z.canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) L hL
        hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) =
      algebraMap ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        ((sectionGeneratorUnit D sX hX hint L hL σ Z :
          ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX)))) := by
  rw [sectionGeneratorUnit, dite_eq_right hZ, IsUnit.unit_spec]
  exact (Z.sectionGenerates_globalSectionMeromorphic_of_not_le D sX hX hint L hL σ
    hZ).choose_spec.2

include hint hn in
/-- **Off `D` the rule the Gysin map forces is the generator rule.**  The component rule
`AlgebraicGeometry.Space.restrictedSectionChernRule` through which
`i_*(i^*α) = c₁(ℒ) ∩ α` is read takes at every `W ⊄ D` the Weil divisor `div_{ℒ|_W}(σ|_W)` of the
*restricted global section*, which is exactly the divisor of the generator named by
`AlgebraicGeometry.Space.sectionGeneratorUnit`
(`PrimeDivisor.henselianUnitRestriction_eq_globalSectionMeromorphic_restrict`);
at every `W ⊆ D` the rule is the free clause (1)(b) of Definition 0ER1, taken to be the same
generator rule.  So the two rules agree everywhere. -/
theorem restrictedSectionChernRule_generatorChernRule
    (hLs : IsInvertibleSheaf D sX hX L) :
    restrictedSectionChernRule D sX hX L σ hLs k
        (generatorChernRule D sX hX hint L hL hn (sectionGeneratorUnit D sX hX hint L hL σ)) =
      generatorChernRule D sX hX hint L hL hn (sectionGeneratorUnit D sX hX hint L hL σ) := by
  funext W hW
  by_cases hWE : W.subspace ≤ (vanishingLocus D sX hX L σ).1
  · exact restrictedSectionChernRule_of_le D sX hX L σ hLs k _ hW hWE
  have hcod := codimension_integralClosedSubspaceSupport_eq_one D sX hX hint hn hW
  have hZ : ¬ (W.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod).subspace ≤
      (vanishingLocus D sX hX L σ).1 := hWE
  have hsec := PrimeDivisor.henselianUnitRestriction_eq_globalSectionMeromorphic_restrict
      D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) hint
      (W.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod) L hL σ _
      (canonicalGenericRatio_globalSectionMeromorphic_sectionGeneratorUnit D sX hX hint L hL σ _
        hZ)
  rw [generatorChernRule]
  refine Eq.trans ?_ (dite_eq_left hcod).symm
  rw [restrictedSectionChernRule, dite_eq_right hWE]
  exact canonicalDivisorCycleAt_congr_section D _ _ _ _ _ _ _ hsec.symm

end GeneratorUnit

/-! ### The difference of the two cap products is the first cycle of the key formula -/

section KeyFormula

variable (σ : L.sections) (hσ : σ ≠ 0)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)
    {I : Type v} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)

include hint hn in
/-- Every member of a family of prime divisors has δ-dimension `k + 1` (Stacks 0EPZ). -/
theorem deltaDimension_toIntegralClosedSubspace_eq (i : I) :
    deltaDimension D sX ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1 :=
  (deltaDimension_toIntegralClosedSubspace D sX hX hint (deltaDimensionFunction D sX hX)
    (deltaDimensionFunction_apply D sX hX) hn (Zf i)).trans (add_sub_cancel_right _ _)

include hint hn in
/-- The coefficient of `div_ℒ(s)` at a member of the family is `ord_{B_i}(f_i)` for the ratio
`f_i = s / (v_i s_{ξ_i})`: Section 0EQU, claims (1) and (2). -/
theorem canonicalDivisorCycleAt_apply_eq_ord_sectionRatio
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)
    (u : GenericUnitFamily D sX hX) (Z : PrimeDivisor D.site D.base D.base_mem X) :
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
    (canonicalDivisorCycleAt D sX hX hint L hL s hs hn).1
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      Z.ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        (Z.sectionRatio D sX hX hint L hL s hs (u Z) :
          Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
            (isDecentSpace_of_isGood D sX hX)) (Units.isUnit _) := by
  have := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  have := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  have := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  rw [canonicalDivisorCycleAt_coe, canonicalDivisorCycle_apply_primeDivisor]
  exact (orderOfVanishingSection_canonical_eq_ord D sX hX hint L hL s hs Z (u Z)
    (Units.isUnit _) _ (Z.sectionRatio_mul D sX hX hint L hL s hs (u Z))).choose_spec

include hint hn hσ ht in
/-- **The difference of the two cap products is the first cycle of the key formula, as cycles.**
In Situation 0EDT let `X/B` be good and integral of δ-dimension `k + 2`, let `ℒ`, `𝒩` be
invertible with `σ ∈ Γ(X, ℒ)` nonzero and `t` a regular meromorphic section of `𝒩`, and let
`{Z_i}` be an injective locally finite family of prime divisors outside of which `σ` generates
`ℒ_ξ` and `t` generates `𝒩_ξ`.  For families of units `v`, `w` naming generators `s_Z = v_Z s_ξ`
of `ℒ_ξ` and `t_Z = w_Z t_ξ` of `𝒩_ξ`,

`c₁(𝒩) ∩ div_ℒ(σ) - c₁(ℒ) ∩ div_𝒩(t) = ∑ (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|_{Z_i}}(t_i|_{Z_i})
  - ord_{B_i}(g_i) div_{ℒ|_{Z_i}}(s_i|_{Z_i}))`

in `Z_k(X)`, the cap products being those of Stacks 0EQJ at the generator rules
`AlgebraicGeometry.Space.generatorChernRule` of `w` and `v`. -/
theorem firstChernCapCycleMap_generatorChernRule_sub_eq_keyFormulaDivisorSum
    (hinj : Function.Injective Zf)
    (hcovL : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ))
    (hcovN : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint N hN t)
    (v w : GenericUnitFamily D sX hX) :
    firstChernCapCycleMap D sX hX k (generatorChernRule D sX hX hint N hN hn w)
          (canonicalDivisorCycleAt D sX hX hint L hL
            (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ)
            (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
              (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ)) hn) -
        firstChernCapCycleMap D sX hX k (generatorChernRule D sX hX hint L hL hn v)
          (canonicalDivisorCycleAt D sX hX hint N hN t ht hn) =
      keyFormulaDivisorSum D sX hX hint L hL
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ)
        (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
          (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ))
        N hN t ht hn Zf hfin (fun i => v (Zf i)) (fun i => w (Zf i)) := by
  set hsr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
    (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ) with hsrdef
  have hdim := deltaDimension_toIntegralClosedSubspace_eq D sX hX hint hn Zf
  have hinj' : Function.Injective
      fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem :=
    (PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem).comp hinj
  have hcover : ∀ {M : Modules.{u, u} D.site D.base D.base_mem X hX.1}
      (hM : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ M)
      {s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M}
      (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M s),
      (∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
        W.SectionGenerates D sX hX hint M hM s) →
      ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        (canonicalDivisorCycleAt D sX hX hint M hM s hs hn).1 W ≠ 0 →
          ∃ i, (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem = W :=
    @fun _ hM _ hs hcov W hW => Classical.byContradiction fun h =>
      hW (canonicalDivisorCycle_apply_eq_zero_of_notMem D sX hX hint _ hM _ hs hn Zf hcov W
        (not_exists.mp h))
  rw [firstChernCapCycleMap_eq_cycleFamilySum D sX hX k
      (generatorChernRule D sX hX hint N hN hn w) _ _ hinj' hfin hdim (hcover hL hsr hcovL),
    firstChernCapCycleMap_eq_cycleFamilySum D sX hX k
      (generatorChernRule D sX hX hint L hL hn v) _ _ hinj' hfin hdim (hcover hN ht hcovN),
    ← cycleFamilySum_sub, keyFormulaDivisorSum]
  refine congrArg (cycleFamilySum D sX hX
    (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin k) (funext fun i => ?_)
  rw [generatorChernRule_toIntegralClosedSubspace D sX hX hint N hN hn w (Zf i) (hdim i),
    generatorChernRule_toIntegralClosedSubspace D sX hX hint L hL hn v (Zf i) (hdim i),
    canonicalDivisorCycleAt_apply_eq_ord_sectionRatio D sX hX hint L hL hn _ hsr v (Zf i),
    canonicalDivisorCycleAt_apply_eq_ord_sectionRatio D sX hX hint N hN hn t ht w (Zf i)]
  rfl

include hint hn hσ ht hfin in
/-- **Stacks 0ER9 with the family `{Z_i}` of Section 0EQU supplied.**  The two sides of
Stacks 0ER9 — the refined Gysin map of Stacks 0ER1 applied to `div_𝒩(t)`, and the cap product of
Stacks 0EQJ of `c₁(𝒩)` with `[D]_{n-1}` formed on `D` — have the same class in `CH_{n-2}(D)`. -/
theorem chowClassCanonical_gysinCycleMap_eq_of_family
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL
          (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) ∧
        W.SectionGenerates D sX hX hint N hN t)
    (w : GenericUnitFamily D sX hX) :
    chowClassCanonical.{v} D ((vanishingLocus D sX hX L σ).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L σ) k
        (gysinCycleMap D sX (vanishingLocus D sX hX L σ) (isGood_vanishingLocus D sX hX L σ) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L σ)
            (isGood_vanishingLocus D sX hX L σ) k
            (generatorChernRule D sX hX hint L hL hn (sectionGeneratorUnit D sX hX hint L hL σ)))
          (canonicalDivisorCycleAt D sX hX hint N hN t ht hn)) =
      chowClassCanonical.{v} D ((vanishingLocus D sX hX L σ).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L σ) k
        (firstChernCapCycleMap D ((vanishingLocus D sX hX L σ).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L σ) k
          (closedSubspaceChernRule D sX hX (vanishingLocus D sX hX L σ).1
            (vanishingLocus D sX hX L σ).2 k (generatorChernRule D sX hX hint N hN hn w))
          (vanishingLocusTopCycleAt D sX hX hint L hL hσ hn)) := by
  rw [eq_comm, ← sub_eq_zero, ← map_sub, chowClassCanonical_eq_zero_iff]
  refine isRationallyEquivalentToZeroCanonical_of_withinCanonical_cycleGroupClosedPushforward
    D sX hX (vanishingLocus D sX hX L σ).1 (vanishingLocus D sX hX L σ).2 k ?_
  rw [map_sub, cycleGroupClosedPushforward_firstChernCapCycleMap_vanishingLocusTopCycleAt D sX hX
      hint L hL hσ hn (generatorChernRule D sX hX hint N hN hn w),
    cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D sX hX L σ hL k
      (generatorChernRule D sX hX hint L hL hn (sectionGeneratorUnit D sX hX hint L hL σ))
      (canonicalDivisorCycleAt D sX hX hint N hN t ht hn),
    restrictedSectionChernRule_generatorChernRule D sX hX hint L hL hn σ hL,
    firstChernCapCycleMap_generatorChernRule_sub_eq_keyFormulaDivisorSum D sX hX hint L hL
      hn σ hσ N hN t ht Zf hfin hinj (fun W hW => (hcov W hW).1) (fun W hW => (hcov W hW).2)
      (sectionGeneratorUnit D sX hX hint L hL σ) w]
  exact isRationallyEquivalentToZeroWithinCanonical_keyFormulaDivisorSum D sX hX hint L hL
    (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) _ N hN t ht hn Zf hfin _ _ hinj
    hcov (fun i => (Zf i).subspace ≤ (vanishingLocus D sX hX L σ).1)
    (fun i hi => canonicalGenericRatio_globalSectionMeromorphic_sectionGeneratorUnit D sX hX hint
      L hL σ (Zf i) hi)
    (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L σ).1)
    fun _ hi => subspacePointSet_mono_of_le D hi

end KeyFormula

/-! ### Stacks 0ER9 -/

section Statement

variable (σ : L.sections) (hσ : σ ≠ 0)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)

include hint hn hσ in
/-- **Stacks 0ER9 (Lemma 82.23.1).**  In Situation 0EDT let `X/B` be good, `X` integral with
`n = dim_δ(X) = k + 2`, let `ℒ` be an invertible `𝒪_X`-module with a nonzero global section `σ`
and let `i : D = Z(σ) → X` be the closed immersion of its vanishing locus (Stacks 0845) — the
effective Cartier divisor of the source, presented by the pair `(𝒪_X(D), s)` the source
immediately passes to.  Let `𝒩` be an invertible `𝒪_X`-module and let `t` be a nonzero
meromorphic section of `𝒩`.  Then

`i^*div_𝒩(t) = c₁(𝒩) ∩ [D]_{n-1}`  in  `CH_{n-2}(D)`,

the Chow group being `AlgebraicGeometry.Space.chowGroupCanonical`, which is the source's
`CH_{n-2}(D)`: the embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK presenting the rational
equivalences are the canonical ones.

The refined Gysin map is the one of Stacks 0ER1, `AlgebraicGeometry.Space.gysinCycleMap` at the
component rule `AlgebraicGeometry.Space.canonicalGysinComponentRule`, whose free clause (1)(b) is
here the generator rule of the source's own choice `s_i = σ` off `D`; the cap product is the one
of Stacks 0EQJ formed on `D` at the generator rule of an arbitrary family of generators `t_W` of
the `𝒩_{ξ_W}`, which is the choice Section 0EQU leaves free; `[D]_{n-1}` is the cycle of
Stacks 0EE9; and `div_𝒩(t)` is the Weil divisor of Stacks 0EQE at the canonical ratios of
Stacks 0EPR.  Regularity of `t` is derived from `t ≠ 0` rather than assumed. -/
@[stacks 0ER9 "i^*div_N(t) = c_1(N) ∩ [D]_{n-1} in CH_{n-2}(D), at the hypotheses of 0ER9 \
itself: X good and integral of δ-dimension n, i : D → X the effective Cartier divisor presented \
by an invertible L with a nonzero global section σ (so D = Z(σ), as in the proof's own 'Set L = \
O_X(D)'), N invertible and t a nonzero meromorphic section of N. The Gysin map is 0ER1's, the \
cap product 0EQJ's formed on D, [D]_{n-1} is 0EE9's and div_N(t) is 0EQE's at the canonical \
ratios of 0EPR; CH_{n-2}(D) is chowGroupCanonical, the quotient by the rational equivalences of \
0EQ6 read at the canonical 0ENK embeddings. Unconditional: the family {Z_i} is constructed by \
0EPS, the choice s_i = σ off D by 0845, and the rational equivalence is the key formula 0EQV \
carried inside |D| and descended along i"]
theorem chowClassCanonical_gysinCycleMap_canonicalDivisorCycleAt
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N) (ht : t ≠ 0)
    (w : GenericUnitFamily D sX hX) :
    chowClassCanonical.{u + 1} D ((vanishingLocus D sX hX L σ).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L σ) k
        (gysinCycleMap D sX (vanishingLocus D sX hX L σ) (isGood_vanishingLocus D sX hX L σ) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L σ)
            (isGood_vanishingLocus D sX hX L σ) k
            (generatorChernRule D sX hX hint L hL hn (sectionGeneratorUnit D sX hX hint L hL σ)))
          (canonicalDivisorCycleAt D sX hX hint N hN t
            (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht) hn)) =
      chowClassCanonical.{u + 1} D ((vanishingLocus D sX hX L σ).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L σ) k
        (firstChernCapCycleMap D ((vanishingLocus D sX hX L σ).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L σ) k
          (closedSubspaceChernRule D sX hX (vanishingLocus D sX hX L σ).1
            (vanishingLocus D sX hX L σ).2 k (generatorChernRule D sX hX hint N hN hn w))
          (vanishingLocusTopCycleAt D sX hX hint L hL hσ hn)) := by
  have hsr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
    (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ)
  have htr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht
  have hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      (∀ i : {W : PrimeDivisor D.site D.base D.base_mem X //
          ¬ (W.SectionGenerates D sX hX hint L hL
              (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) ∧
            W.SectionGenerates D sX hX hint N hN t)},
        (i : PrimeDivisor D.site D.base D.base_mem X) ≠ W) →
        W.SectionGenerates D sX hX hint L hL
            (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) ∧
          W.SectionGenerates D sX hX hint N hN t := fun W hW =>
    Classical.byContradiction fun h => hW ⟨W, h⟩ rfl
  exact chowClassCanonical_gysinCycleMap_eq_of_family D sX hX hint L hL hn σ hσ N hN t
    htr Subtype.val
    (locallyFinite_primeDivisor_not_sectionGenerates D sX hX hint L hL _ hsr N hN t htr)
    Subtype.val_injective hcov w

end Statement

end AlgebraicGeometry.Space

end

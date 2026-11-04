module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.KrullDimOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCoefficients

/-!
# The data of the key formula, Stacks 0EQV

In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n`, let `ℒ`, `𝒩` be invertible
`𝒪_X`-modules with nonzero (regular) meromorphic sections `s`, `t`, and let `{Z_i}` be a locally
finite family of prime divisors outside of which `s` and `t` generate.  For each `i` the source
picks generators `s_i ∈ ℒ_{ξ_i}`, `t_i ∈ 𝒩_{ξ_i}` over `B_i = 𝒪^h_{X,ξ_i}` and writes
`s = f_i s_i`, `t = g_i t_i` with `f_i, g_i ∈ Q(B_i)^*`.  The key formula asserts

`∑ (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|_{Z_i}}(t_i|_{Z_i})
    - ord_{B_i}(g_i) div_{ℒ|_{Z_i}}(s_i|_{Z_i}))
  = ∑ (Z_i → X)_* div(∂_{B_i}(f_i, g_i))`.

This file builds the ingredients of both sides at the canonical choices.

* A generator of `ℒ_ξ` is `v · s_ξ` for a unique unit `v ∈ B^*`, `s_ξ` being the generator of
  Stacks 0EPR; the ratio `s / s_ξ` is `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio`,
  so `f = (s / s_ξ) · v⁻¹`: `AlgebraicGeometry.Space.PrimeDivisor.sectionRatio`.
* `s_i|_{Z_i} = (v s_ξ)|_{Z_i}` is `AlgebraicGeometry.Space.PrimeDivisor.henselianUnitRestriction`,
  the meromorphic section of `ℒ|_{Z_i}` with value the residue of `v` at the generic point.
* `∂_{B}(f, g)` is the tame symbol of Stacks 0EAH on the one-dimensional Noetherian local ring
  `B` (`Stacks.Chow.tameSymbolOfKrullDimOne`), read in `R(Z)^*` through `κ(B) = κ(ξ) = R(Z)`
  (`AlgebraicGeometry.Space.PrimeDivisor.henselianResidueFieldEquivFunctionField`):
  `AlgebraicGeometry.Space.PrimeDivisor.keyFormulaTameSymbol`.
* The two cycles on `Z` are `AlgebraicGeometry.Space.PrimeDivisor.keyFormulaDivisorCycle` and
  `AlgebraicGeometry.Space.PrimeDivisor.keyFormulaTameCycle`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (Z : PrimeDivisor D.site D.base D.base_mem X)

/-- The henselian local ring `B = 𝒪^h_{X,ξ}` at the generic point of a prime divisor is local. -/
theorem PrimeDivisor.isLocalRing_genericHenselianLocalRing :
    IsLocalRing ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)) :=
  henselianLocalRing_isLocalRing D.site D.base D.base_mem X hX.1 (Z.genericPoint _ _ _ X) _


include hint in
/-- `B = 𝒪^h_{X,ξ}` is Noetherian (Stacks 0ENK). -/
theorem PrimeDivisor.isNoetherianRing_genericHenselianLocalRing_of_isGood :
    IsNoetherianRing ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)) :=
  Z.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1 _ hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)

/-- **The ratio `f` with `s = f · (v s_ξ)`**, for a regular meromorphic section `s` of `ℒ` and the
generator `v · s_ξ` of `ℒ_ξ` given by a unit `v` of `B = 𝒪^h_{X,ξ}`: the unit
`(s / s_ξ) · v⁻¹` of `Q(B)`. -/
def PrimeDivisor.sectionRatio
    (v : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX))ˣ :=
  (Z.isUnit_canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
      L hL hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s hs).unit *
    (Units.map (algebraMap ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX))
      (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX))).toMonoidHom v)⁻¹

/-- The defining equation of `AlgebraicGeometry.Space.PrimeDivisor.sectionRatio`:
`s / s_ξ = f · v`, that is `s = f · (v s_ξ)`. -/
theorem PrimeDivisor.sectionRatio_mul
    (v : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    (Z.sectionRatio D sX hX hint L hL s hs v : Z.genericTotalFractionRing D.site D.base
        D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)) *
      algebraMap ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (v : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))) =
      Z.canonicalGenericRatio D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        L hL hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s := by
  simp [PrimeDivisor.sectionRatio, mul_assoc, ← map_mul]

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)

include hint in
/-- **`∂_B(f, g) ∈ κ(ξ)^* = R(Z)^*`**, the tame symbol of Stacks 0EAH on the one-dimensional
Noetherian local ring `B = 𝒪^h_{X,ξ}` of the ratios `f = s / (v s_ξ)` and `g = t / (w t_ξ)`,
read as an invertible rational function on `Z` through the canonical identification
`κ(B) = κ(ξ) = R(Z)` (Decent Spaces 0EN0). -/
def PrimeDivisor.keyFormulaTameSymbol
    (v w : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    (rationalFunctions D.site D.base D.base_mem Z.closed.1)ˣ :=
  haveI := Z.isLocalRing_genericHenselianLocalRing D sX hX
  haveI := Z.isNoetherianRing_genericHenselianLocalRing_of_isGood D sX hX hint
  Units.map (Z.henselianResidueFieldEquivFunctionField D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)).toRingHom.toMonoidHom
    (Stacks.Chow.tameSymbolOfKrullDimOne
      (Z.ringKrullDim_genericHenselianLocalRing_eq_one D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX))
      (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX))
      (Z.sectionRatio D sX hX hint L hL s hs v) (Z.sectionRatio D sX hX hint N hN t ht w))

variable {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))

/-- **`div_{ℒ|_Z}((v s_ξ)|_Z) ∈ Z_k(Z)`**, the Weil divisor on the prime divisor `Z` (of
δ-dimension `k + 1`) of the restriction to `Z` of the generator `v · s_ξ` of `ℒ_ξ`, at the
canonical choices (Stacks 0EQE on `Z`). -/
def PrimeDivisor.restrictedGeneratorDivisor
    (v : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    CycleGroup D ((Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫ sX) k :=
  canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX _)
    (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
    (Z.restrictModule D.site D.base D.base_mem hX.1 L)
    (Z.isInvertibleModule_restrictModule D.site D.base D.base_mem hX.1 L hL)
    (Z.henselianUnitRestriction D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L hL v)
    (Z.isRegularMeromorphicSection_henselianUnitRestriction D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L hL v)
    (deltaDimensionClosed_univ_toIntegralClosedSubspace D sX hX hint hn Z)

/-- **`div(∂_B(f, g)) ∈ Z_k(Z)`**, the principal divisor on `Z` of the tame symbol
`AlgebraicGeometry.Space.PrimeDivisor.keyFormulaTameSymbol` (Stacks 0EQ1 on `Z`). -/
def PrimeDivisor.keyFormulaTameCycle
    (v w : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    CycleGroup D ((Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫ sX) k :=
  canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX _)
    (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace
    (Z.keyFormulaTameSymbol D sX hX hint L hL s hs N hN t ht v w)
    (deltaDimensionClosed_univ_toIntegralClosedSubspace D sX hX hint hn Z)

/-- **The `i`-th term of the first cycle of the key formula**,
`ord_B(f) div_{𝒩|_Z}((w t_ξ)|_Z) - ord_B(g) div_{ℒ|_Z}((v s_ξ)|_Z) ∈ Z_k(Z)`. -/
def PrimeDivisor.keyFormulaDivisorCycle
    (v w : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    CycleGroup D ((Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι ≫ sX) k :=
  haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.isNoetherianRing_genericHenselianLocalRing_of_isGood D sX hX hint
  haveI := Z.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  haveI := Z.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  Z.ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
      (Z.sectionRatio D sX hX hint L hL s hs v : _) (Units.isUnit _) •
    Z.restrictedGeneratorDivisor D sX hX hint N hN hn w -
  Z.ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
      (Z.sectionRatio D sX hX hint N hN t ht w : _) (Units.isUnit _) •
    Z.restrictedGeneratorDivisor D sX hX hint L hL hn v

/-! ### The two cycles of the key formula -/

section Cycles

variable {I : Type*} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)

/-- **The first cycle of the key formula**,
`∑ (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|_{Z_i}}(t_i|_{Z_i})
    - ord_{B_i}(g_i) div_{ℒ|_{Z_i}}(s_i|_{Z_i}))`
in `Z_k(X)`, `k = n - 2`, for the generators `s_i = v_i s_{ξ_i}`, `t_i = w_i t_{ξ_i}`. -/
def keyFormulaDivisorSum : CycleGroup D sX k :=
  cycleFamilySum D sX hX (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin k
    fun i => (Zf i).keyFormulaDivisorCycle D sX hX hint L hL s hs N hN t ht hn (v i) (w i)

/-- **The second cycle of the key formula**, `∑ (Z_i → X)_* div(∂_{B_i}(f_i, g_i))` in `Z_k(X)`. -/
def keyFormulaTameSum : CycleGroup D sX k :=
  cycleFamilySum D sX hX (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin k
    fun i => (Zf i).keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn (v i) (w i)

end Cycles

end AlgebraicGeometry.Space

end

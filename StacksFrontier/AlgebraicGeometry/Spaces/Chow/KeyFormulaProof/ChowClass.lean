module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaStatement

/-!
# From the key formula to the commutativity of the two cap products

In Situation 0EDT let `X/B` be good, integral with `dim_δ(X) = n = k + 2`, let `ℒ`, `𝒩` be
invertible with regular meromorphic sections `s`, `t`, and let `{Z_i}` be a locally finite family
of prime divisors outside of which `s` and `t` generate.  Section 0EQU writes

* `c₁(𝒩) ∩ div_ℒ(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{𝒩|_{Z_i}}(t_i|_{Z_i})`,
* `c₁(ℒ) ∩ div_𝒩(t) = ∑ ord_{B_i}(g_i) (Z_i → X)_* div_{ℒ|_{Z_i}}(s_i|_{Z_i})`,

in `CH_{n-2}(X)` (`AlgebraicGeometry.Space.canonicalFirstChernCap_canonicalDivisorCycleAt`), so
the difference of the two classes is the class of the first cycle of the key formula.  The key
formula, Stacks 0EQV, identifies that cycle with a locally finite sum of principal divisors on the
`Z_i`, whose class vanishes; hence `c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in `CH_{n-2}(X)`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isPrincipalDivisorCycle_keyFormulaTameCycle`: the
  divisor of the tame symbol on `Z_i` is a principal divisor.
* `AlgebraicGeometry.Space.chowClass_keyFormulaTameSum_eq_zero`: the second cycle of the key
  formula is rationally equivalent to zero.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_comm_of_keyFormula`: the commutativity of the
  two cap products in `CH_{n-2}(X)`, from the key formula for one family.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

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
    {k : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))

/-- The canonical principal divisor of an invertible rational function is a principal divisor in
the sense of rational equivalence (Stacks 0EQ6). -/
theorem isPrincipalDivisorCycle_canonicalPrincipalDivisorCycleAt
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    IsPrincipalDivisorCycle D sY k (canonicalPrincipalDivisorCycleAt D sY hY hintY f hk) :=
  ⟨hY, hintY, f, rfl⟩

variable {I : Type v} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)

/-- **The second cycle of the key formula is rationally equivalent to zero**: it is a locally
finite sum of principal divisors on integral closed subspaces of δ-dimension `k + 1`. -/
theorem chowClass_keyFormulaTameSum_eq_zero :
    chowClass.{v} D sX hX k
      (keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w) = 0 :=
  chowClass_cycleFamilySum_eq_zero.{v} D sX hX k _ hfin _
    (fun i => (deltaDimension_toIntegralClosedSubspace D sX hX hint (deltaDimensionFunction D sX hX)
      (deltaDimensionFunction_apply D sX hX) hn (Zf i)).trans (add_sub_cancel_right _ _))
    fun i => isPrincipalDivisorCycle_canonicalPrincipalDivisorCycleAt D _
      (isGood_integralClosedSubspace D sX hX _)
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _ _

/-- **The commutativity of the two cap products, from the key formula.** If the key formula holds
for one family `{Z_i}` as in Section 0EQU (with generators `v_i s_{ξ_i}`, `w_i t_{ξ_i}`), then
`c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in `CH_{n-2}(X)`. -/
theorem canonicalFirstChernCap_comm_of_keyFormula
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)
    (hkey : keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w =
      keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w) :
    canonicalFirstChernCap.{u, v} D sX hX N hN k
        (canonicalDivisorCycleAt D sX hX hint L hL s hs hn) =
      canonicalFirstChernCap.{u, v} D sX hX L hL k
        (canonicalDivisorCycleAt D sX hX hint N hN t ht hn) := by
  rw [canonicalFirstChernCap_canonicalDivisorCycleAt D sX hX hint L hL s hs N hN Zf hinj hfin
      (fun W hW => (hcov W hW).1) hn (fun i => (v i : _)) (fun i => (v i).isUnit)
      (fun i => (Zf i).sectionRatio D sX hX hint L hL s hs (v i))
      (fun i => (Zf i).sectionRatio_mul D sX hX hint L hL s hs (v i))
      (fun i => (Zf i).henselianUnitRestriction D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) N hN (w i))
      (fun i => (Zf i).isRegularMeromorphicSection_henselianUnitRestriction D.site D.base
        D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) N hN (w i)),
    canonicalFirstChernCap_canonicalDivisorCycleAt D sX hX hint N hN t ht L hL Zf hinj hfin
      (fun W hW => (hcov W hW).2) hn (fun i => (w i : _)) (fun i => (w i).isUnit)
      (fun i => (Zf i).sectionRatio D sX hX hint N hN t ht (w i))
      (fun i => (Zf i).sectionRatio_mul D sX hX hint N hN t ht (w i))
      (fun i => (Zf i).henselianUnitRestriction D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L hL (v i))
      (fun i => (Zf i).isRegularMeromorphicSection_henselianUnitRestriction D.site D.base
        D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L hL (v i)),
    ← sub_eq_zero, ← map_sub, ← cycleFamilySum_sub]
  have h : cycleFamilySum D sX hX
      (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin k
      (fun i => (Zf i).keyFormulaDivisorCycle D sX hX hint L hL s hs N hN t ht hn (v i) (w i)) =
    keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w := rfl
  refine Eq.trans ?_ ((congrArg (chowClass.{v} D sX hX k) (h.trans hkey)).trans
    (chowClass_keyFormulaTameSum_eq_zero D sX hX hint L hL s hs N hN t ht hn Zf hfin v w))
  rfl

end AlgebraicGeometry.Space

end

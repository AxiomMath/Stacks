module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.UnitRestrictionReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Final

/-!
# The key formula for algebraic spaces, Stacks 0EQV

The key formula of Stacks 0EQV, for an injective locally finite family of prime divisors `Z_i`
of a good integral algebraic space `X` outside of which the regular meromorphic sections `s`, `t`
of the invertible modules `ℒ`, `𝒩` generate, and units `v_i`, `w_i` of the henselian local rings
`𝒪^h_{X, ξ_i}`:

`∑ (Z_i → X)_*(ord_{B_i}(f_i) div(t_i|_{Z_i}) - ord_{B_i}(g_i) div(s_i|_{Z_i})) =
  ∑ (Z_i → X)_* div(∂_{B_i}(f_i, g_i))`

in `Z_k(X)`.  It is
`AlgebraicGeometry.Space.keyFormulaDivisorSum_eq_keyFormulaTameSum_of_unitRestrictionReading`
with the reading of the restricted generators (G2) supplied by
`AlgebraicGeometry.Space.PrimeDivisor.unitRestrictionReading`.

## Main results

* `AlgebraicGeometry.Space.keyFormulaDivisorSum_eq_keyFormulaTameSum`: Stacks 0EQV.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology chartMeromorphicFunctionAlgebra

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
    {I : Type*} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)

/-- **Stacks 0EQV, the key formula.** In the situation of Stacks 0EQU, for an injective locally
finite family of prime divisors `Z_i` outside of which `s` and `t` generate `ℒ` and `𝒩`, and
units `v_i`, `w_i` of `𝒪^h_{X, ξ_i}`,

`∑ (Z_i → X)_*(ord_{B_i}(f_i) div(t_i|_{Z_i}) - ord_{B_i}(g_i) div(s_i|_{Z_i})) =
  ∑ (Z_i → X)_* div(∂_{B_i}(f_i, g_i))`

in `Z_k(X)`. -/
theorem keyFormulaDivisorSum_eq_keyFormulaTameSum
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t) :
    keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w =
      keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w := by
  have key := fun M hM i u V hV e hc hf ↦ (Zf i).unitRestrictionReading D.site D.base
    D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V hV M hM e hc hf
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
      (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
        D.base_mem)))
    ((Zf i).isAffine_chartScheme_baseChangeChart D.site D.base D.base_mem hX.1 V hV) u
  exact keyFormulaDivisorSum_eq_keyFormulaTameSum_of_unitRestrictionReading D sX hX hint L hL s hs
    N hN t ht hn Zf v w hfin hinj hcov (fun i ↦ key L hL i (v i)) (fun i ↦ key N hN i (w i))

end AlgebraicGeometry.Space

end

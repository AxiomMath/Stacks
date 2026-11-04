module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline

/-!
# Section 0EQU and Stacks 0EQX in the Chow group at the canonical embeddings

In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = n`, let `ℒ`, `𝒩` be invertible
with nonzero meromorphic sections `s`, `t`.  Section 0EQU displays

* `c₁(𝒩) ∩ div_ℒ(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{𝒩|_{Z_i}}(t_i|_{Z_i})`,

and Stacks 0EQX concludes `c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)`, both "in `CH_{n-2}(X)`".  Here
the class is taken in `AlgebraicGeometry.Space.chowGroupCanonical`, the quotient of `Z_{n-2}(X)`
by the cycles the source displays, whose summands are principal divisors at the canonical
embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK, rather than in
`AlgebraicGeometry.Space.chowGroup`, the quotient in the reading in which those embeddings are
quantified existentially.

## Main results

* `AlgebraicGeometry.Space.chowClassCanonical_keyFormulaTameSum_eq_zero`: the second cycle of the
  key formula is rationally equivalent to zero at the canonical embeddings.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_canonicalDivisorCycleAt`: **Section
  0EQU, claim (3)**, in `CH_{n-2}(X)` at the canonical embeddings.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_comm_of_keyFormula`: the
  commutativity of the two cap products from the key formula for one family.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_divisor_comm`: **Stacks 0EQX** in
  `CH_{n-2}(X)` at the canonical embeddings.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EQX](https://stacks.math.columbia.edu/tag/0EQX)
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

/-- A prime divisor of `X` has `δ`-dimension one less than `X`. -/
private theorem deltaDimension_toIntegralClosedSubspace_eq_add_one
    (hint : IsIntegralSpace D.site D.base D.base_mem X) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (W : PrimeDivisor D.site D.base D.base_mem X) :
    deltaDimension D sX (W.toIntegralClosedSubspace D.site D.base D.base_mem) = k + 1 :=
  (deltaDimension_toIntegralClosedSubspace D sX hX hint (deltaDimensionFunction D sX hX)
    (deltaDimensionFunction_apply D sX hX) hn W).trans (add_sub_cancel_right _ _)

/-! ### Section 0EQU, claim (3), at the canonical embeddings -/

section ClaimThree

/-- **Section 0EQU, claim (3), in the Chow group at the canonical embeddings of Stacks 0ENK.**
In the situation of `AlgebraicGeometry.Space.canonicalFirstChernCap_canonicalDivisorCycleAt`,

`c₁(𝒩) ∩ div_ℒ(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{𝒩|_{Z_i}}(τ_i)`

holds in `CH_{n-2}(X)` with `CH_{n-2}(X)` the Chow group
`AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6 read at the canonical embeddings. -/
theorem canonicalFirstChernCapCanonical_canonicalDivisorCycleAt
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
    canonicalFirstChernCapCanonical.{v} D sX hX N hN k
        (canonicalDivisorCycleAt D sX hX hint L hL s hs hn) =
      chowClassCanonical.{v} D sX hX k (cycleFamilySum D sX hX
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
  have hdim := fun i => deltaDimension_toIntegralClosedSubspace_eq_add_one D sX hX hint hn (Zf i)
  have hinj' : Function.Injective
      fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem :=
    (PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem).comp hinj
  have hcover : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      (canonicalDivisorCycleAt D sX hX hint L hL s hs hn).1 W ≠ 0 →
        ∃ i, (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem = W := by
    intro W hW
    by_contra h
    exact hW (canonicalDivisorCycle_apply_eq_zero_of_notMem D sX hX hint L hL s hs hn Zf hcov W
      (not_exists.mp h))
  unfold canonicalFirstChernCapCanonical
  rw [AddMonoidHom.comp_apply,
    firstChernCapCycleMap_eq_cycleFamilySum D sX hX k _ _ _ hinj' hfin hdim hcover,
    ← sub_eq_zero, ← map_sub, ← cycleFamilySum_sub]
  refine chowClassCanonical_cycleFamilySum_eq_zero.{v} D sX hX k
    (fun i => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hfin _ hdim fun i => ?_
  have hα : (canonicalDivisorCycleAt D sX hX hint L hL s hs hn).1
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) =
      (Zf i).ord D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        (f i : (Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)) (f i).isUnit := by
    rw [canonicalDivisorCycleAt_coe, canonicalDivisorCycle_apply_primeDivisor]
    exact (orderOfVanishingSection_canonical_eq_ord D sX hX hint L hL s hs (Zf i) (v i) (hv i) _
      (hf i)).2
  rw [hα, ← smul_sub]
  exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D _
    (isGood_integralClosedSubspace D sX hX _)
    ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN _) _ _ _ _ _ _

end ClaimThree

/-! ### The key formula and Stacks 0EQX at the canonical embeddings -/

section KeyFormula

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)
    {k : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    {I : Type v} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)

/-- **The second cycle of the key formula is rationally equivalent to zero at the canonical
embeddings** of Stacks 0ENK. -/
theorem chowClassCanonical_keyFormulaTameSum_eq_zero :
    chowClassCanonical.{v} D sX hX k
      (keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w) = 0 :=
  chowClassCanonical_cycleFamilySum_eq_zero.{v} D sX hX k _ hfin _
    (fun i => deltaDimension_toIntegralClosedSubspace_eq_add_one D sX hX hint hn (Zf i))
    fun i => isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt D _
      (isGood_integralClosedSubspace D sX hX _)
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _ _

/-- **The commutativity of the two cap products at the canonical embeddings, from the key
formula.**  If the key formula holds for one family `{Z_i}` as in Section 0EQU (with generators
`v_i s_{ξ_i}`, `w_i t_{ξ_i}`), then `c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in `CH_{n-2}(X)`, the
Chow group being the one at the canonical embeddings. -/
theorem canonicalFirstChernCapCanonical_comm_of_keyFormula
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)
    (hkey : keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w =
      keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w) :
    canonicalFirstChernCapCanonical.{v} D sX hX N hN k
        (canonicalDivisorCycleAt D sX hX hint L hL s hs hn) =
      canonicalFirstChernCapCanonical.{v} D sX hX L hL k
        (canonicalDivisorCycleAt D sX hX hint N hN t ht hn) := by
  rw [canonicalFirstChernCapCanonical_canonicalDivisorCycleAt D sX hX hint L hL s hs N hN Zf hinj
      hfin (fun W hW => (hcov W hW).1) hn (fun i => (v i : _)) (fun i => (v i).isUnit)
      (fun i => (Zf i).sectionRatio D sX hX hint L hL s hs (v i))
      (fun i => (Zf i).sectionRatio_mul D sX hX hint L hL s hs (v i))
      (fun i => (Zf i).henselianUnitRestriction D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) N hN (w i))
      (fun i => (Zf i).isRegularMeromorphicSection_henselianUnitRestriction D.site D.base
        D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) N hN (w i)),
    canonicalFirstChernCapCanonical_canonicalDivisorCycleAt D sX hX hint N hN t ht L hL Zf hinj
      hfin (fun W hW => (hcov W hW).2) hn (fun i => (w i : _)) (fun i => (w i).isUnit)
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
  refine Eq.trans ?_ ((congrArg (chowClassCanonical.{v} D sX hX k) (h.trans hkey)).trans
    (chowClassCanonical_keyFormulaTameSum_eq_zero D sX hX hint L hL s hs N hN t ht hn Zf hfin v w))
  rfl

end KeyFormula

/-! ### Stacks 0EQX at the canonical embeddings -/

section Headline

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)

/-- **Stacks 0EQX in the Chow group at the canonical embeddings of Stacks 0ENK.**  For `X/B` good
and integral with `dim_δ(X) = n`, `ℒ` and `𝒩` invertible and `s`, `t` nonzero meromorphic
sections of `ℒ`, `𝒩`,

`c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)`  in  `CH_{n-2}(X)`,

the Chow group being `AlgebraicGeometry.Space.chowGroupCanonical`. -/
theorem canonicalFirstChernCapCanonical_divisor_comm (hs0 : s ≠ 0)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N) (ht0 : t ≠ 0)
    {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX N hN (n - 2)
        (canonicalDivisorCycleAt D sX hX hint L hL s
          (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL hs0)
          (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) =
      canonicalFirstChernCapCanonical.{u + 1} D sX hX L hL (n - 2)
        (canonicalDivisorCycleAt D sX hX hint N hN t
          (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht0)
          (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) := by
  have hsr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL hs0
  have htr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht0
  have hn' := deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn
  let I := {W : PrimeDivisor D.site D.base D.base_mem X //
    ¬ (W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)}
  have hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        (((i : PrimeDivisor D.site D.base D.base_mem X)).toIntegralClosedSubspace D.site D.base
          D.base_mem).subspace :=
    locallyFinite_primeDivisor_not_sectionGenerates D sX hX hint L hL s hsr N hN t htr
  have hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      (∀ i : I, (i : PrimeDivisor D.site D.base D.base_mem X) ≠ W) →
        W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t :=
    fun W hW => Classical.byContradiction fun h => hW ⟨W, h⟩ rfl
  exact canonicalFirstChernCapCanonical_comm_of_keyFormula D sX hX hint L hL s hsr N hN t htr hn'
    (Subtype.val : I → PrimeDivisor D.site D.base D.base_mem X) hfin (fun _ => 1) (fun _ => 1)
    Subtype.val_injective hcov
    (keyFormulaDivisorSum_eq_keyFormulaTameSum D sX hX hint L hL s hsr N hN t htr hn'
      Subtype.val (fun _ => 1) (fun _ => 1) hfin Subtype.val_injective hcov)

end Headline

end AlgebraicGeometry.Space

end

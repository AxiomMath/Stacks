module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.ChowClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums

/-!
# The carrier of the rational equivalence of the key formula

In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n = k + 2`, let `ℒ`, `𝒩` be
invertible `𝒪_X`-modules with nonzero (regular) meromorphic sections `s`, `t`, and let `{Z_i}` be
an injective locally finite family of prime divisors outside of which `s` and `t` generate.  The
key formula, Stacks 0EQV (`AlgebraicGeometry.Space.keyFormulaDivisorSum_eq_keyFormulaTameSum`),
exhibits the cycle

`∑_i (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|_{Z_i}}(t_i|_{Z_i})
    - ord_{B_i}(g_i) div_{ℒ|_{Z_i}}(s_i|_{Z_i}))`

as the locally finite sum `∑_i (Z_i → X)_* div(∂_{B_i}(f_i, g_i))` of principal divisors on the
`Z_i`.  Where the chosen generator `s_i = v_i s_{ξ_i}` of `ℒ_{ξ_i}` already has `s` for its
generic value — that is, where `v_i` witnesses `s / s_{ξ_i} ∈ B_i^*` — the ratio `f_i` is `1`, so
the tame symbol `∂_{B_i}(1, g_i)` is trivial and the `i`-th principal divisor is the zero cycle.

The rational equivalence to zero of the first cycle is therefore **witnessed inside the union of
the members at which the generator is not so normalized**.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.sectionRatio_eq_one`: **`f_i = 1`** when the unit `v_i`
  recording the generator `s_i = v_i s_{ξ_i}` is the ratio `s / s_{ξ_i}` itself.
* `AlgebraicGeometry.Space.PrimeDivisor.keyFormulaTameSymbol_eq_one`: **`∂_{B_i}(1, g_i) = 1`**,
  Stacks 0EAI and 0EAJ in the form `Stacks.Chow.TameSymbol.one_left`.
* `AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt_one`: the principal divisor of the
  constant rational function `1` is the zero cycle.
* `AlgebraicGeometry.Space.PrimeDivisor.keyFormulaTameCycle_eq_zero`: **the `i`-th summand of
  the second cycle of the key formula vanishes** where `f_i = 1`.
* `AlgebraicGeometry.Space.cycleFamilySum_eq_cycleFamilySum_subtype`: the sum of Stacks 0EQ6
  part (1) over a family whose terms vanish outside a subtype is the sum over that subtype.
* `AlgebraicGeometry.Space.keyFormulaTameSum_eq_cycleFamilySum_subtype`: the second cycle of the
  key formula is the sum over the members at which `f_i ≠ 1`.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum`: **the first
  cycle of the key formula is rationally equivalent to zero within any set containing the members
  at which `f_i ≠ 1`.**
* `exists_isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum_of_sectionGenerates`: the same
  for a choice of generators, wherever `s` generates `ℒ_{ξ_i}` off a set of members.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The ratio at a normalized generator -/

section Ratio

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)

include hint in
/-- **`f = 1` when the chosen generator of `ℒ_ξ` has `s` for its generic value.**  Section 0EQU
records a generator `s_ξ'` of `ℒ_ξ` by the unit `v` of `B = 𝒪^h_{X,ξ}` with `s_ξ' = v s_ξ`, and
writes `s = f s_ξ'`, so that `f v = s / s_ξ` in `Q(B)`.  If `v` is itself the ratio `s / s_ξ`,
then `f = 1`. -/
theorem PrimeDivisor.sectionRatio_eq_one
    (v : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)
    (hv : Z.canonicalGenericRatio D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) L hL hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s =
      algebraMap ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (v : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) :
    Z.sectionRatio D sX hX hint L hL s hs v = 1 := by
  have hmul := Z.sectionRatio_mul D sX hX hint L hL s hs v
  rw [hv] at hmul
  have hu : IsUnit (algebraMap ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX))
      (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX))
      (v : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)))) := v.isUnit.map _
  exact Units.val_eq_one.mp (hu.mul_left_inj.mp (hmul.trans (one_mul _).symm))

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)

include hint in
/-- **`∂_B(1, g) = 1`.**  Where the chosen generator `v s_ξ` of `ℒ_ξ` has `s` for its generic
value, the tame symbol `∂_B(f, g)` of the key formula, read in `R(Z)^*`, is `1`. -/
theorem PrimeDivisor.keyFormulaTameSymbol_eq_one
    (v w : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)
    (hv : Z.canonicalGenericRatio D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) L hL hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s =
      algebraMap ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (v : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) :
    Z.keyFormulaTameSymbol D sX hX hint L hL s hs N hN t ht v w = 1 := by
  have := Z.isLocalRing_genericHenselianLocalRing D sX hX
  have := Z.isNoetherianRing_genericHenselianLocalRing_of_isGood D sX hX hint
  rw [PrimeDivisor.keyFormulaTameSymbol,
    Z.sectionRatio_eq_one D sX hX hint L hL s hs v hv,
    Stacks.Chow.TameSymbol.one_left, map_one]

end Ratio

/-! ### The principal divisor of the constant function `1` -/

section PrincipalOne

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

include hintY in
/-- **The principal divisor of the constant rational function `1` is the zero cycle.** -/
theorem canonicalPrincipalDivisorCycleAt_one {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalPrincipalDivisorCycleAt D sY hY hintY 1 hk = 0 := by
  refine Subtype.ext (funext fun P => ?_)
  change (canonicalPrincipalDivisorCycleAt D sY hY hintY 1 hk).1 P = 0
  by_cases hP : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 P) = 1
  · rw [canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one D sY hY hintY 1 hk P hP]
    exact congrFun (genericFractionEmbedding D.site D.base D.base_mem hY.1
      hintY.isDecentSpace hintY
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)).ord_one _
  · unfold canonicalPrincipalDivisorCycleAt
    simp only
    rw [principalDivisorCycleCoefficients, dite_eq_right hP]

end PrincipalOne

/-! ### The vanishing of the tame cycle at a normalized member -/

section TameCycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)
    {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))

include hint in
/-- **The `i`-th summand of the second cycle of the key formula vanishes where `f_i = 1`**, that
is, where the chosen generator `v s_ξ` of `ℒ_ξ` has `s` for its generic value. -/
theorem PrimeDivisor.keyFormulaTameCycle_eq_zero
    (v w : (↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)
    (hv : Z.canonicalGenericRatio D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) L hL hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s =
      algebraMap ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (Z.genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (v : ↥(Z.genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) :
    Z.keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn v w = 0 := by
  rw [PrimeDivisor.keyFormulaTameCycle,
    Z.keyFormulaTameSymbol_eq_one D sX hX hint L hL s hs N hN t ht v w hv]
  exact canonicalPrincipalDivisorCycleAt_one D _ (isGood_integralClosedSubspace D sX hX _)
    (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _

end TameCycle

/-! ### Restricting a locally finite sum to a subtype -/

section Restrict

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The sum of Stacks 0EQ6 part (1) over a family whose terms vanish outside a subtype is the
sum over that subtype.** -/
theorem cycleFamilySum_eq_cycleFamilySum_subtype (sX : X ⟶ D.space) (hX : D.IsGood sX)
    {J : Type v} (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (k : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k) (P : J → Prop)
    (hvanish : ∀ j, ¬ P j → c j = 0) :
    cycleFamilySum D sX hX W hWfin k c =
      cycleFamilySum D sX hX (fun j : {j : J // P j} => W j.1)
        (hWfin.comp_injective Subtype.val_injective) k (fun j => c j.1) := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [cycleFamilySum_apply, cycleFamilySum_apply]
  set h : J → ℤ :=
    fun j => (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z with hh
  have hzero : ∀ j, ¬ P j → h j = 0 := by
    intro j hj
    rw [hh]
    simp only
    rw [hvanish j hj, map_zero]
    rfl
  have hsupp : Function.support h ⊆ Set.range (Subtype.val : {j : J // P j} → J) :=
    fun j hj => Classical.byContradiction fun hmem => hj (hzero j fun hP => hmem ⟨⟨j, hP⟩, rfl⟩)
  exact (finsum_mem_univ h).symm.trans <| (finsum_mem_inter_support_eq' h _ _
    fun j hj => iff_of_true trivial (hsupp hj)).trans (finsum_mem_range Subtype.val_injective)

end Restrict

/-! ### The carrier of the rational equivalence -/

section Carrier

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
    {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    {I : Type v} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)

include hint hn in
/-- **The second cycle of the key formula is carried by the members at which `f_i ≠ 1`**: it is
the sum over the members whose chosen generator does not have `s` for its generic value. -/
theorem keyFormulaTameSum_eq_cycleFamilySum_subtype (P : I → Prop)
    (hP : ∀ i, ¬ P i → (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) L hL hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s =
      algebraMap ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        ((Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (v i : ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX)))) :
    keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w =
      cycleFamilySum D sX hX
        (fun j : {i : I // P i} =>
          (Zf j.1).toIntegralClosedSubspace D.site D.base D.base_mem)
        (hfin.comp_injective Subtype.val_injective) k
        (fun j => (Zf j.1).keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn
          (v j.1) (w j.1)) :=
  cycleFamilySum_eq_cycleFamilySum_subtype D sX hX _ hfin k _ P fun i hi =>
    (Zf i).keyFormulaTameCycle_eq_zero D sX hX hint L hL s hs N hN t ht hn (v i) (w i) (hP i hi)

include hint hn in
/-- **The first cycle of the key formula is rationally equivalent to zero within the union of the
members at which `f_i ≠ 1`**: if `T` contains every member `Z_i` whose chosen generator
`s_i = v_i s_{ξ_i}` does not have `s` for its generic value, the first cycle is rationally
equivalent to zero within `T`. -/
theorem isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)
    (P : I → Prop)
    (hP : ∀ i, ¬ P i → (Zf i).canonicalGenericRatio D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) L hL hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) s =
      algebraMap ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        ((Zf i).genericTotalFractionRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))
        (v i : ↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
          (isDecentSpace_of_isGood D sX hX))))
    (T : Set (points D.site D.base D.base_mem X))
    (hT : ∀ i, P i → subspacePointSet D.site D.base D.base_mem X
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace ⊆ T) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k
      (keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w) T := by
  refine ⟨{i : I // P i},
    fun j => (Zf j.1).toIntegralClosedSubspace D.site D.base D.base_mem,
    hfin.comp_injective Subtype.val_injective,
    fun j => (Zf j.1).keyFormulaTameCycle D sX hX hint L hL s hs N hN t ht hn (v j.1) (w j.1),
    fun j => hT j.1 j.2,
    fun j => (deltaDimension_toIntegralClosedSubspace D sX hX hint
      (deltaDimensionFunction D sX hX) (deltaDimensionFunction_apply D sX hX) hn
      (Zf j.1)).trans (add_sub_cancel_right _ _),
    fun j => isPrincipalDivisorCycle_canonicalPrincipalDivisorCycleAt D _
      (isGood_integralClosedSubspace D sX hX _)
      ((Zf j.1).toIntegralClosedSubspace D.site D.base D.base_mem).isIntegralSpace _ _, ?_⟩
  rw [keyFormulaDivisorSum_eq_keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf v w
      hfin hinj hcov,
    keyFormulaTameSum_eq_cycleFamilySum_subtype D sX hX hint L hL s hs N hN t ht hn Zf hfin
      v w P hP]

include hint hn in
/-- **The carrier statement where `s` generates.**  If `s` generates `ℒ_{ξ_i}` at every member
`Z_i` outside a set of members, then there is a choice of generators `v_i` for which, for *every*
choice of the generators `w_i` of `𝒩_{ξ_i}`, the first cycle of the key formula is rationally
equivalent to zero within any set `T` containing those members. -/
theorem exists_isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum_of_sectionGenerates
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)
    (P : I → Prop)
    (hgen : ∀ i, ¬ P i → (Zf i).SectionGenerates D sX hX hint L hL s)
    (T : Set (points D.site D.base D.base_mem X))
    (hT : ∀ i, P i → subspacePointSet D.site D.base D.base_mem X
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace ⊆ T) :
    ∃ g : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX)))ˣ,
      ∀ wN, IsRationallyEquivalentToZeroWithin.{v} D sX hX k
        (keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin g wN) T := by
  classical
  refine ⟨fun i => if hi : P i then 1 else (hgen i hi).choose_spec.1.unit, fun wN => ?_⟩
  refine isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht
    hn Zf hfin _ wN hinj hcov P (fun i hi => ?_) T hT
  rw [dite_eq_right hi, IsUnit.unit_spec]
  exact (hgen i hi).choose_spec.2

end Carrier

end AlgebraicGeometry.Space

end

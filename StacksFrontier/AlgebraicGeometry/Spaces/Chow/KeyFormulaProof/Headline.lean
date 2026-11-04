module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.ChowClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleWeilDivisor

/-!
# The key formula of Section 0EQU: `c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)`

In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n`, let `ℒ`, `𝒩` be invertible
`𝒪_X`-modules and let `s`, `t` be nonzero meromorphic sections of `ℒ`, `𝒩`.  Section 0EQU chooses
the locally finite family `{Z_i}` of prime divisors outside of which `s` and `t` generate (it
exists by Stacks 0EPS, `AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_sectionGenerates`),
writes the two cap products as sums over the family
(`AlgebraicGeometry.Space.canonicalFirstChernCap_canonicalDivisorCycleAt`), and proves the key
formula, Stacks 0EQV (`AlgebraicGeometry.Space.keyFormulaDivisorSum_eq_keyFormulaTameSum`),
which identifies their difference with a sum of principal divisors on the `Z_i`.  Hence

`c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in `CH_{n-2}(X)`.

Everything is at the canonical choices: the divisors `div_ℒ(s)`, `div_𝒩(t)` of Stacks 0EQE at
the canonical ratios of Stacks 0EPR (`AlgebraicGeometry.Space.canonicalDivisorCycleAt`), the cap
products of Stacks 0EQJ (`AlgebraicGeometry.Space.canonicalFirstChernCap`) and the Chow group of
Stacks 0EQ6.

## Main results

* `AlgebraicGeometry.Space.keyFormula_of_ne_zero`: **Stacks 0EQV** for nonzero meromorphic
  sections.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_divisor_comm`: **Section 0EQU**,
  `c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in `CH_{n-2}(X)`.

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
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)

include hint in
/-- A nonzero meromorphic section of an invertible module on a good integral algebraic space is
regular. -/
theorem isRegularMeromorphicSection_of_ne_zero_of_isGood
    (M : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ M)
    {s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M} (hs : s ≠ 0) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 M s :=
  isRegularMeromorphicSection_of_ne_zero D.site D.base D.base_mem hX.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) M hM s hs

/-- `dim_δ(X) = n` read as `dim_δ(X) = (n - 2) + 1 + 1`, the grading of the cap products into
`CH_{n-2}(X)`. -/
theorem deltaDimensionClosed_eq_sub_two_add_one_add_one {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((n - 2 + 1 + 1 : ℤ) : EInt) := by
  rw [hn]
  congr 1
  ring

/-- **Stacks 0EQV, the key formula, for nonzero meromorphic sections.** In Situation 0EDT let
`X/B` be good, `X` integral with `dim_δ(X) = n`, let `ℒ`, `𝒩` be invertible with nonzero
meromorphic sections `s`, `t`, let `{Z_i}` be an injective locally finite family of prime divisors
outside of which `s` generates `ℒ_ξ` and `t` generates `𝒩_ξ`, and let `s_i = v_i s_{ξ_i}`,
`t_i = w_i t_{ξ_i}` be generators of `ℒ_{ξ_i}`, `𝒩_{ξ_i}` (`v_i`, `w_i` units of
`B_i = 𝒪^h_{X,ξ_i}`; every generator is of this form for a unique unit), so that `s = f_i s_i`,
`t = g_i t_i` with `f_i, g_i ∈ Q(B_i)^*`.  Then

`∑ (Z_i → X)_*(ord_{B_i}(f_i) div_{𝒩|_{Z_i}}(t_i|_{Z_i})
    - ord_{B_i}(g_i) div_{ℒ|_{Z_i}}(s_i|_{Z_i}))
  = ∑ (Z_i → X)_* div(∂_{B_i}(f_i, g_i))`

in `Z_{n-2}(X)`, with `t_i|_{Z_i}` the image of `t_i` in the fibre `𝒩_{ξ_i} ⊗ κ(ξ_i)` read as a
meromorphic section of `𝒩|_{Z_i}`, and `∂_{B_i}` the tame symbol of Stacks 0EAH read in
`κ(ξ_i)^* = R(Z_i)^*`. -/
@[stacks 0EQV]
theorem keyFormula_of_ne_zero
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L) (hs : s ≠ 0)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N) (ht : t ≠ 0)
    {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    {I : Type*} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ) :
    keyFormulaDivisorSum D sX hX hint L hL s
        (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL hs) N hN t
        (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht)
        (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn) Zf hfin v w =
      keyFormulaTameSum D sX hX hint L hL s
        (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL hs) N hN t
        (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht)
        (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn) Zf hfin v w :=
  keyFormulaDivisorSum_eq_keyFormulaTameSum D sX hX hint L hL s _ N hN t _ _ Zf v w hfin hinj
    hcov

/-- **Section 0EQU, the key formula: `c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in `CH_{n-2}(X)`.**
In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n`, let `ℒ` and `𝒩` be
invertible `𝒪_X`-modules, and let `s`, `t` be nonzero meromorphic sections of `ℒ`, `𝒩`.  Then
`c₁(𝒩) ∩ div_ℒ(s) = c₁(ℒ) ∩ div_𝒩(t)` in the Chow group `CH_{n-2}(X)` of Stacks 0EQ6, the cap
products being those of Stacks 0EQJ and the divisors those of Stacks 0EQE, all at the canonical
choices.

The proof is the section's: the family `{Z_i}` of prime divisors where `s` or `t` fails to
generate is locally finite (Stacks 0EPS), the two cap products are the sums over it of
`ord_{B_i}(f_i) (Z_i → X)_* div(t_i|_{Z_i})` and `ord_{B_i}(g_i) (Z_i → X)_* div(s_i|_{Z_i})`, and
the key formula (Stacks 0EQV) makes their difference a locally finite sum of principal divisors of
tame symbols on the `Z_i`. -/
@[stacks 0EQU "the key formula of the section, c_1(N) ∩ div_L(s) = c_1(L) ∩ div_N(t) in \
CH_{n-2}(X), at the section's hypotheses; Lemma 0EQV is keyFormula_of_ne_zero",
  stacks 0EQX "Lemma 82.21.1 itself: for X good and integral with δ-dimension n, L and N \
invertible and s, t nonzero meromorphic sections, c_1(N) ∩ div_L(s) = c_1(L) ∩ div_N(t) in \
CH_{n-2}(X). Unconditional at the source's hypotheses: integrality and goodness are the \
section variables, regularity of s and t is derived from s ≠ 0, t ≠ 0 rather than assumed, and \
the cap product of 0EQJ, the divisors of 0EQE and the Chow group of 0EQ6 are the constructed \
ones, not carried"]
theorem canonicalFirstChernCap_divisor_comm
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L) (hs : s ≠ 0)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N) (ht : t ≠ 0)
    {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    canonicalFirstChernCap.{u, u + 1} D sX hX N hN (n - 2)
        (canonicalDivisorCycleAt D sX hX hint L hL s
          (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL hs)
          (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) =
      canonicalFirstChernCap.{u, u + 1} D sX hX L hL (n - 2)
        (canonicalDivisorCycleAt D sX hX hint N hN t
          (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht)
          (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) := by
  have hsr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL hs
  have htr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint N hN ht
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
  exact canonicalFirstChernCap_comm_of_keyFormula D sX hX hint L hL s hsr N hN t htr hn'
    (Subtype.val : I → PrimeDivisor D.site D.base D.base_mem X) hfin (fun _ => 1) (fun _ => 1)
    Subtype.val_injective hcov
    (keyFormulaDivisorSum_eq_keyFormulaTameSum D sX hX hint L hL s hsr N hN t htr hn'
      Subtype.val (fun _ => 1) (fun _ => 1) hfin Subtype.val_injective hcov)

end AlgebraicGeometry.Space

end

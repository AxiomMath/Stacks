module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DivisorTracePushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExceptionalProjectionPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcess
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernPerfectPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleDegreeZero
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DivisorSelfIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExceptionalNormalBundle

/-!
# `j_*1 = γ([E])` for the exceptional divisor of a blowing up in codimension `≥ 2`, without (A9)

The proof of [Stacks, Tag 0FIT] uses axiom (A9) at one step only: "`j_*(1) = γ([E])` by (A9)",
for the exceptional divisor `j : E ⟶ X'` of the blowing up `b : X' ⟶ X` in a smooth centre
`Z ⊂ X`. This file proves that step from (A1)–(A8) when the centre has codimension `r ≥ 2`.

The argument works on the actual data:

1. *Duality and (A4).* The functional `a ↦ ∫_{X'} a ∪ γ([E])` vanishes on the kernel of `j^*`.
   By (A4), `a ∪ c₁^H(𝒪_{X'}(E)) = 0` when `j^*a = 0`, and `γ([E]) = c₁^H(𝒪_{X'}(E))`. With the
   perfect pairings of Lemma 0FIJ / Remark 0FIK, `j_*` is the transpose of `j^*`, so
   `γ([E]) = j_*β` for some `β ∈ H^0(E)`
   (`Stacks.WeilCohomology.WeilData.exists_pushforward_eq_of_pairingTw_eq_zero`).
2. *Self-intersection.* `j^*j_*x = j^*γ([E]) ∪ x` (`WeilChernData.pullTw_pushforward_divisor`), and
   at `x = β` this gives `j^*γ([E]) ∪ (1 - β) = 0`.
3. *Nondegeneracy.* Under the identification `E ≅ 𝐏(𝒞)` of Tag 0FUT, `j^*γ([E])` is
   `-c₁^H(𝒪(1)) + p^*w` (`WeilChernData.exists_iso_bundle_exceptionalObj_c₁`), and
   `H^0(𝐏(𝒞)) = p^*H^0(Z)` by (A8) (`WeilChernData.exists_pull_bundleProj_grade_zero`). Since
   `r ≥ 2`, `ξ = c₁^H(𝒪(1))` is one of the free generators in the projective bundle formula (A3),
   so `(-ξ + p^*w) ∪ p^*z = 0` forces `z = 0`
   (`Stacks.WeilCohomology.FirstChernClassData.eq_zero_of_mul_pull_bundleProj_eq_zero`). Hence
   `β = 1`.

## Main results

* `Stacks.WeilCohomology.WeilData.exists_pushforward_eq_of_pairingTw_eq_zero`
* `Stacks.WeilCohomology.FirstChernClassData.eq_zero_of_mul_pull_bundleProj_eq_zero`
* `Stacks.WeilCohomology.WeilChernData.cycleClass_exceptional_eq_pushforward_unitTw_of_lt`

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- **Classes orthogonal to `ker f^*` are pushforwards.** Under the perfect pairings of axiom (A),
a class `c ∈ H^{j'}(Y)(t')` whose pairing with every `b ∈ ker(f^*)` vanishes lies in the image of
`f_*`: the pushforward is the transpose of `f^*`, and over a field the image of a transpose is the
annihilator of the kernel. -/
theorem exists_pushforward_eq_of_pairingTw_eq_zero (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (j t j' t' : ℤ)
    (hj : j' + 2 * d = j + 2 * e) (ht : t' + d = t + e) (c : W.Tw Y j' t')
    (hc : ∀ b : W.Tw Y (2 * d - j) (d - t), W.pullTw f _ _ b = 0 →
      W.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega) b c = 0) :
    ∃ a, W.pushforward hA f hX hY j t j' t' hj ht a = c := by
  have hpX := hA.pairingTw X d hX (2 * d - j) j (by omega) (d - t) t (by omega)
  have hpY := hA.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega)
  set pX := W.pairingTw X d hX (2 * d - j) j (by omega) (d - t) t (by omega)
  set pY := W.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega)
  set g := W.pullTw f (2 * d - j) (d - t)
  have hφ : pY.flip c ∈ LinearMap.range g.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro b hb
    exact hc b (LinearMap.mem_ker.mp hb)
  obtain ⟨ψ, hψ⟩ := hφ
  obtain ⟨a, ha⟩ := (LinearMap.IsPerfPair.bijective_right pX).surjective ψ
  refine ⟨a, (LinearMap.IsPerfPair.bijective_right pY).injective (LinearMap.ext fun b ↦ ?_)⟩
  have hb := LinearMap.congr_fun hψ b
  rw [LinearMap.dualMap_apply] at hb
  rw [LinearMap.flip_apply, LinearMap.flip_apply,
    ← W.pushforward_trace hA f hX hY j t j' t' hj ht b a]
  exact (LinearMap.congr_fun ha (g b)).trans hb

end WeilData

namespace FirstChernClassData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- **Multiplication by `-ξ + p^*w` is injective on `p^*H^*(X)` for a bundle of rank `≥ 2`.**
Let `p : P = 𝐏(ℰ) ⟶ X` with `ℰ` of rank `r + 1 ≥ 2` and `ξ = c₁^H(𝒪_P(1))` in coordinates.
If `(-ξ + p^*w) ∪ p^*z = 0`, then `z = 0`: the left side is the image of `(wz, -z, 0, …, 0)` under
the projective bundle formula (A3), which is injective. -/
theorem eq_zero_of_mul_pull_bundleProj_eq_zero (hA3 : 𝔇.ProjectiveBundleAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (hr : 1 ≤ r) (w z : 𝔇.H X)
    (h : (-𝔇.bundleClassU X E r + 𝔇.pull (bundleProj X E r) w) *
      𝔇.pull (bundleProj X E r) z = 0) : z = 0 := by
  classical
  set i₀ : Fin (r + 1) := ⟨0, by omega⟩
  set i₁ : Fin (r + 1) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set a : Fin (r + 1) → 𝔇.H X := fun i ↦ if i = i₀ then w * z else if i = i₁ then -z else 0
  have hsum : (∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) *
      𝔇.pull (bundleProj X E r) (a i)) =
      ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) *
        𝔇.pull (bundleProj X E r) ((0 : Fin (r + 1) → 𝔇.H X) i) := by
    rw [Fintype.sum_eq_add i₀ i₁ h01 fun x hx ↦ by simp [a, hx.1, hx.2]]
    simp only [a, ite_eq_left rfl, ite_eq_right h01.symm, ite_true,
      Pi.zero_apply, map_zero, mul_zero,
      Finset.sum_const_zero, map_mul, map_neg, i₀, i₁, pow_zero, pow_one, one_mul, mul_neg]
    rw [← h, add_mul, neg_mul, add_comm]
  have := congrFun ((𝔇.bijective_bundleFormulaU hA3 X E r).injective hsum) i₁
  simpa [a, ite_eq_right h01.symm] using this

end FirstChernClassData

namespace WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **`j_*1 = γ([E])` in codimension `≥ 2`, under (A8).** Let `i : Z ⟶ X` be a closed immersion
of nonempty smooth projective schemes, equidimensional of dimensions `e` and `d + 1` with
`e + 1 < d + 1` (codimension `≥ 2`), and let `j : E ⟶ X'` be the exceptional divisor of the blowing
up in `Z`. Then `γ([E]) = j_*1` in `H^2(X')(1)`. This replaces the use of (A9) in the proof of
Tag 0FIT. -/
theorem cycleClass_exceptional_eq_pushforward_unitTw_of_lt (hA8 : 𝔚.GlobalSections)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {e d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X (d + 1))
    (he : e + 1 < d + 1) :
    haveI := hZ.nonempty
    𝔚.toWeilData.cycleClass (blowupObj i) 1
        (closedSubschemeClass (blowupObj i).obj.hom (exceptionalHom i).hom.left 1) =
      𝔚.toWeilData.pushforward 𝔚.perfectPairing (exceptionalHom i)
        (isNonemptyEquidimensional_exceptionalObj i hX.relativeDimension
          (isNowhereDense_range_of_relativeDimension i hX.relativeDimension hZ.relativeDimension
            (by omega)))
        (isNonemptyEquidimensional_blowupObj i hX
          (isNowhereDense_range_of_relativeDimension i hX.relativeDimension hZ.relativeDimension
            (by omega))) 0 0 (2 * 1) 1 (by push_cast; ring)
        (by push_cast; ring) (𝔚.toWeilData.unitTw (exceptionalObj i) 0 0 rfl) := by
  have := hZ.nonempty
  have hnd := isNowhereDense_range_of_relativeDimension i hX.relativeDimension
    hZ.relativeDimension (by omega)
  have hE := isNonemptyEquidimensional_exceptionalObj i hX.relativeDimension hnd
  have hX' := isNonemptyEquidimensional_blowupObj i hX hnd
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalDivisor i) :=
    isEffectiveCartierDivisor_exceptionalIdeal i
  have hiso : IsIso (exceptionalToSubscheme i) := inferInstance
  set W := 𝔚.toWeilData with hW
  set j := exceptionalHom i with hj
  set g := W.cycleClass (blowupObj i) 1
    (closedSubschemeClass (blowupObj i).obj.hom j.hom.left 1) with hg
  set cE := 𝔚.κ (blowupObj i) 1 (𝔚.c₁ (blowupObj i) (picardClassOf _
    (Stacks.Divisors.divisorSheaf (exceptionalDivisor i))
    (Stacks.Divisors.isInvertible_divisorSheaf (exceptionalDivisor i)))) with hcE
  -- `γ([E])` in coordinates is `c₁^H(𝒪_{X'}(E))`
  have hgκ : (W.twCoord (blowupObj i) (2 * 1) 1 g : W.H (blowupObj i)) = cE := by
    refine (𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass
      𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace (blowupObj i) 1 _).trans
      (congrArg (𝔚.κ (blowupObj i) 1) ?_)
    exact (congrArg (𝔚.γ (blowupObj i) 1) (closedSubschemeClass_exceptionalHom i 1)).trans
      (𝔚.isCohomologicalChernCharacter.codimensionCycleClass_divisor 𝔚.coproduct
        𝔚.projectiveBundle (blowupObj i) (exceptionalDivisor i))
  -- (A4): `a ∪ c₁^H(𝒪_{X'}(E)) = 0` when `j^*a = 0`
  have hA4 : ∀ a : 𝔚.H (blowupObj i), 𝔚.pull j a = 0 → a * cE = 0 := by
    intro a ha
    have h4 := 𝔚.divisor (blowupObj i) (exceptionalObj i) j (exceptionalDivisor i) hD
      (@asIso _ _ _ _ (exceptionalToSubscheme i) hiso) (exceptionalToSubscheme_subschemeι i) a ha
    have h4' := congrArg (𝔚.κ (blowupObj i) 1) h4
    rw [map_zero] at h4'
    rw [hcE, ← h4']
    exact (tateTwistCoordinates_tateCupLeft 𝔚.coord (𝔚.cup (blowupObj i)) 1 a _).symm
  -- Step 1: `γ([E]) = j_*β` for some `β ∈ H^0(E)`
  obtain ⟨β, hβ⟩ := W.exists_pushforward_eq_of_pairingTw_eq_zero 𝔚.perfectPairing j hE hX'
    0 0 (2 * 1) 1 (by push_cast; ring) (by push_cast; ring) g fun b hb ↦ by
      have hcup : W.cupTw (blowupObj i) (2 * ((d + 1 - 1 : ℕ) : ℤ) - 0) (2 * 1)
          (2 * ((d + 1 : ℕ) : ℤ)) (by omega) (((d + 1 - 1 : ℕ) : ℤ) - 0) 1 ((d + 1 : ℕ) : ℤ)
          (by omega) b g = 0 := by
        apply (W.twCoord (blowupObj i) _ _).injective
        rw [WeilData.twCoord_cupTw, map_zero]
        refine Subtype.ext ?_
        rw [WeilData.coe_cup, hgκ]
        refine hA4 _ ?_
        have := congrArg Subtype.val (congrArg (W.twCoord (exceptionalObj i) _ _) hb)
        rw [WeilData.twCoord_pullTw, map_zero, WeilData.coe_pullDeg] at this
        exact this
      rw [WeilData.pairingTw, LinearMap.compr₂_apply, hcup, map_zero]
  -- Step 2: `j^*γ([E]) = j^*γ([E]) ∪ β`, by the self-intersection formula
  have h1 := 𝔚.pullTw_pushforward_divisor j hE hX' 0 0 β
  have hβ0 : W.pushforward 𝔚.perfectPairing j hE hX' 0 0 (0 + 2 * 1) (0 + 1)
      (by push_cast; ring) (by push_cast; ring) β = g := hβ
  rw [hβ0] at h1
  set b₀ : 𝔚.H (exceptionalObj i) := (W.twCoord (exceptionalObj i) 0 0 β).1 with hb₀
  have h1' : W.pullTw j (2 * 1) 1 g = W.cupTw (exceptionalObj i) (2 * 1) 0 (2 * 1) (by ring) 1 0 1
      (by ring) (W.pullTw j (2 * 1) 1 g) β := h1
  have h2 : 𝔚.pull j cE = 𝔚.pull j cE * b₀ := by
    have := congrArg Subtype.val (congrArg (W.twCoord (exceptionalObj i) (2 * 1) 1) h1')
    rw [WeilData.twCoord_cupTw, WeilData.coe_cup, WeilData.twCoord_pullTw,
      WeilData.coe_pullDeg, hgκ] at this
    exact this
  have hb₀mem : b₀ ∈ 𝔚.grade (exceptionalObj i) 0 := (W.twCoord (exceptionalObj i) 0 0 β).2
  -- Step 3: `β = 1`, by (A3) on `E ≅ 𝐏(𝒞)` and (A8)
  obtain ⟨M, hM, φ, ψ, hφψ, -, -, w, hw⟩ :=
    𝔚.exists_iso_bundle_exceptionalObj_c₁ i hX.relativeDimension hZ.relativeDimension (by omega)
  set p := SmoothProjectiveScheme.bundleProj Z M (d + 1 - e - 1)
  have hu : 𝔚.pull ψ (𝔚.pull j cE) =
      -𝔚.bundleClassU Z M (d + 1 - e - 1) + 𝔚.pull p (𝔚.κ Z 1 w) := by
    have := congrArg (𝔚.κ (SmoothProjectiveScheme.bundle Z M (d + 1 - e - 1)) 1) hw
    rw [FirstChernClassData.κ_pullTw, map_add, map_neg, FirstChernClassData.κ_pullTw,
      𝔚.pull_comp, AlgHom.comp_apply] at this
    exact this
  have hy : 𝔚.pull ψ (1 - b₀) ∈ 𝔚.grade (SmoothProjectiveScheme.bundle Z M (d + 1 - e - 1)) 0 :=
    𝔚.pull_grade ψ 0 _ (Submodule.sub_mem _ SetLike.GradedOne.one_mem hb₀mem)
  obtain ⟨z, -, hz⟩ := 𝔚.exists_pull_bundleProj_grade_zero hA8 Z M (d + 1 - e - 1) _ hy
  have hzero : z = 0 := by
    refine 𝔚.eq_zero_of_mul_pull_bundleProj_eq_zero 𝔚.projectiveBundle Z M (d + 1 - e - 1)
      (by omega) (𝔚.κ Z 1 w) z ?_
    rw [← hu, hz, ← map_mul, mul_sub, mul_one, ← h2, sub_self, map_zero]
  have hb1 : b₀ = 1 := by
    have h0 : 𝔚.pull ψ (1 - b₀) = 0 := by rw [← hz, hzero, map_zero]
    have h' := congrArg (𝔚.pull φ) h0
    rw [map_zero, ← AlgHom.comp_apply, ← 𝔚.pull_comp, hφψ, 𝔚.pull_id, AlgHom.id_apply] at h'
    exact (sub_eq_zero.mp h').symm
  have hβ1 : β = W.unitTw (exceptionalObj i) 0 0 rfl := by
    apply (W.twCoord (exceptionalObj i) 0 0).injective
    refine Subtype.ext ?_
    rw [WeilData.coe_twCoord_unitTw]
    exact hb1
  rw [← hβ, hβ1]

end WeilChernData

end Stacks.WeilCohomology

end

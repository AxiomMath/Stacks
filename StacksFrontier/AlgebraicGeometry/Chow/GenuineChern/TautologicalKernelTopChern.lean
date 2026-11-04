module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernClassDual
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.TopChernCap
public import StacksFrontier.AlgebraicGeometry.Modules.AffineDualSheaf

/-!
# The top Chern class of the dual tautological kernel pushes forward to the identity

Let `π : P ⟶ U` be flat, proper, of relative dimension `n`, and a projective tower of fibre
dimension `n` with twist `ℳ` locally on `U` (for instance the projective bundle of a finite
locally free module of rank `n + 1` with `𝒪(1)`, `Stacks.Chow.isLocallyProjectiveTower_bundle`).
Let `𝒞` be finite locally free of rank `n + 1` on `U`, and let

  `0 ⟶ ℱ ⟶ π^*𝒞 ⟶ ℳ ⟶ 0`

be a short exact sequence, so that `ℱ` has rank `n`. Then for every `β ∈ A_m(U)`

  `π_*(c_n(ℱ^∨) ∩ π^*β) = β`.

This is the computation the proof of [Stacks, Tag 0FIH] omits ("the degree of
`(-1)^{r-1} c_{r-1}(ℱ) ∩ [E]` on the fibres of `π` is `1`"), for `π : E ⟶ Z` the exceptional
divisor of a blowing up in a centre of codimension `r = n + 1`.

## The proof

Dualizing gives `0 ⟶ ℳ^∨ ⟶ (π^*𝒞)^∨ ⟶ ℱ^∨ ⟶ 0` (Stacks 0FV8's exactness of duality), and the
Whitney formula of Stacks 02UI with the invertible sub-module `ℳ^∨`, whose first Chern class is
`-ξ` for `ξ = c₁(ℳ)` (Stacks 02SP), gives

  `c_{j+1}(ℱ^∨) ∩ x = c_{j+1}((π^*𝒞)^∨) ∩ x + ξ ∩ c_j(ℱ^∨) ∩ x`.

By induction on `j`, `π_*(ξ^s ∩ c_j(ℱ^∨) ∩ π^*β) = β` whenever `s + j = n`: for `j = 0` this is
the top case of Stacks 02TW, and in the inductive step the new summand is
`ξ^s ∩ π^*(c_{j+1}(𝒞^∨) ∩ β)` (Stacks 02U8, `(π^*𝒞)^∨ = π^*(𝒞^∨)`), which pushes forward to zero
by the vanishing half of Stacks 02TW since `s < n`. The case `j = n`, `s = 0` is the claim.

## Main results

* `Stacks.Chow.GenuineChern.chernFamily_dualKernel_succ` — the recursion above.
* `Stacks.Chow.GenuineChern.pushforward_chernFamily_dualKernel_bundlePullback` — the claim.

## References

* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- The first Chern class cap of an invertible module on Chow groups is the cap operation of the
operator `Stacks.Chow.invCap`. -/
theorem firstChernClassCapChow_eq_invCap {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (k : ℤ) (x : chowGroup C q (k + 1)) :
    firstChernClassCapChow C k q L x = (invCap C q L).capOnChow C q k x := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [firstChernClassCapChow_mk, invCap_capOnChow_mk]

section Kernel

variable {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (S : ShortComplex P.Modules) (hS : S.ShortExact) (n : ℕ)
  [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ n]
  [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1)]
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property S.X₃]

include hS in
/-- **The recursion for the Chern classes of the dual kernel.** For a short exact sequence
`0 ⟶ ℱ ⟶ 𝒢 ⟶ ℳ ⟶ 0` with `ℱ` of rank `n`, `𝒢` of rank `n + 1` and `ℳ` invertible,

  `c_{j+1}(ℱ^∨) ∩ x = c_{j+1}(𝒢^∨) ∩ x + c₁(ℳ) ∩ c_j(ℱ^∨) ∩ x`:

the Whitney formula of Stacks 02UI for the dual sequence `0 ⟶ ℳ^∨ ⟶ 𝒢^∨ ⟶ ℱ^∨ ⟶ 0`, with
`c₁(ℳ^∨) = -c₁(ℳ)` (Stacks 02SP). -/
theorem chernFamily_dualKernel_succ (k : ℤ) (j : ℕ) (x : chowGroup C sP k) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      S.X₁ n hF
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      S.X₂ (n + 1) hG
    chernFamily C sP (dualSheaf S.X₁) n k (j + 1) x =
      chernFamily C sP (dualSheaf S.X₂) (n + 1) k (j + 1) x +
        (invCap C sP S.X₃).capOnChow C sP (k - ((j + 1 : ℕ) : ℤ))
          (chowGroupCast C sP (by push_cast; ring)
            (chernFamily C sP (dualSheaf S.X₁) n k j x)) := by
  have hFd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    S.X₁ n hF
  have hGd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    S.X₂ (n + 1) hG
  have hO : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible S.X₃
  have hOd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    S.X₃ 1 hO
  have := isFiniteLocallyFree_of_rank S.X₁ n
  have := isFiniteLocallyFree_of_rank S.X₂ (n + 1)
  have := isFiniteLocallyFree_of_rank S.X₃ 1
  obtain ⟨w', hSEd⟩ := Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact
    S.f S.g S.zero hS.mono_f hS.epi_g hS.exact
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree S.X₁)
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree S.X₂)
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree S.X₃)
  have hGd' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf S.X₂) (1 + n) := rank_of_iso (Iso.refl _) (by omega) hGd
  -- Stacks 02UI on the dual sequence
  have hW : chernFamily C sP (dualSheaf S.X₂) (1 + n) =
      chernFamily C sP (dualSheaf S.X₃) 1 * chernFamily C sP (dualSheaf S.X₁) n :=
    @chernFamily_eq_mul_of_shortExact C P sP inferInstance
      (ShortComplex.mk (dualMap S.g) (dualMap S.f) w') hSEd 1 n hOd hFd
  have hcongr : chernFamily C sP (dualSheaf S.X₂) (1 + n) =
      chernFamily C sP (dualSheaf S.X₂) (n + 1) :=
    chernFamily_congr C sP (dualSheaf S.X₂) (n + 1) (Iso.refl _) (Nat.add_comm 1 n)
  rw [← hcongr, hW, chernFamily_rankOne_mul_apply_succ, capTo_chernFamily_rankOne]
  have := isInvertible_of_rank_one (dualSheaf S.X₃)
  rw [firstChernClassCapChow_eq_invCap, invCap_capOnChow_dualSheaf]
  abel

end Kernel

section Pushforward

variable {U P : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [Flat π]
  [IsProper π] (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (𝒞 : U.Modules)
  [h𝒞 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 (n + 1)]
  (S : ShortComplex P.Modules) (hS : S.ShortExact)
  [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ n]
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property S.X₃]
  (e₂ : S.X₂ ≅ (Scheme.Modules.pullback π).obj 𝒞)
  (htower : IsLocallyProjectiveTower n π S.X₃)

/-- The dual of the middle term is the pullback of the dual: `𝒢^∨ ≅ (π^*𝒞)^∨ ≅ π^*(𝒞^∨)`
(Tag 0GMX's dual base change). -/
def dualMiddleIso :
    dualSheaf S.X₂ ≅ (Scheme.Modules.pullback π).obj (dualSheaf 𝒞) :=
  haveI := isFiniteLocallyFree_of_rank 𝒞 (n + 1)
  (AlgebraicGeometry.dualIso e₂).symm ≪≫
    (@asIso _ _ _ _ (pullbackDualMap π 𝒞) (pullbackDualMap_isIso π 𝒞 inferInstance)).symm

include hS e₂ htower in
/-- **The induction of the computation.** For `s + j = n`,
`π_*(c₁(ℳ)^s ∩ c_j(ℱ^∨) ∩ π^*β) = β`. -/
theorem pushforward_capPow_chernFamily_dualKernel (m : ℤ) (β : chowGroup C sU m) :
    ∀ (j s : ℕ) (hjs : s + j = n),
      haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
        S.X₁ n hF
      properChowPushforward C sP sU π hsP m
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m)
          (capPow C sP (invCap C sP S.X₃) s (m + n - j) m (by omega)
            (chernFamily C sP (dualSheaf S.X₁) n (m + n) j
              (bundlePullback C sU sP π hsP n hπ m β))) = β := by
  have hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1) :=
    rank_of_iso e₂.symm rfl (isFiniteLocallyFreeOfRank_pullback π 𝒞 (n + 1))
  intro j
  induction j with
  | zero =>
    intro s hs
    obtain rfl : s = n := by omega
    rw [chernFamily_apply_zero, gradedCap_one_apply_zero]
    refine Eq.trans ?_ (htower.bundleProjection_self C sU sP hsP hπ m β)
    simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
    congr 1
    exact eq_of_heq (capPow_heq C sP _ _ _ rfl (by simp) rfl (gradedDegreeCast_heq _ _))
  | succ j ih =>
    intro s hs
    rw [chernFamily_dualKernel_succ C sP S hS n, map_add, map_add]
    -- the new summand vanishes, by the vanishing half of Stacks 02TW
    have hint := intertwines_chernFamily C sU (dualSheaf 𝒞) (n + 1) sP π hsP n hπ
      (dualSheaf S.X₂) (dualMiddleIso π n 𝒞 S e₂) m (j + 1) β
    have hb : properChowPushforward C sP sU π hsP m
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m)
          (capPow C sP (invCap C sP S.X₃) s (m + n - ((j + 1 : ℕ) : ℤ)) m (by omega)
            (chernFamily C sP (dualSheaf S.X₂) (n + 1) (m + n) (j + 1)
              (bundlePullback C sU sP π hsP n hπ m β))) = 0 := by
      refine Eq.trans ?_ (bundleProjection_eq_zero_of_lt C sU sP π hsP n hπ (invCap C sP S.X₃) s
        (by omega) (m - ((j + 1 : ℕ) : ℤ)) m (by push_cast; omega)
        (chernFamily C sU (dualSheaf 𝒞) (n + 1) m (j + 1) β))
      simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
      congr 1
      refine eq_of_heq (capPow_heq C sP _ _ _ rfl (by omega) rfl ?_)
      refine HEq.trans ?_ (heq_of_eq hint).symm
      exact (gradedDegreeCast_heq _ _).symm
    rw [hb, zero_add]
    refine Eq.trans ?_ (ih (s + 1) (by omega))
    congr 1
    rw [capPow_succ_apply]
    refine eq_of_heq (capPow_heq C sP _ _ _ rfl (by push_cast; ring) rfl ?_)
    refine heq_apply_of_degree C sP sP (fun d => d + 1) (fun d => d)
      (fun d => (invCap C sP S.X₃).capOnChow C sP d) (by push_cast; ring) ?_
    exact (chowGroupCast_heq C sP _ _).trans (chowGroupCast_heq C sP _ _).symm

include hS e₂ htower in
/-- **The top Chern class of the dual tautological kernel pushes forward to the identity.** Let
`π : P ⟶ U` be flat, proper, of relative dimension `n` and a projective tower of fibre dimension
`n` with twist `ℳ` locally on `U`, let `𝒞` be finite locally free of rank `n + 1` on `U` and let
`0 ⟶ ℱ ⟶ π^*𝒞 ⟶ ℳ ⟶ 0` be short exact, with `ℱ` of rank `n`. Then for every `β ∈ A_m(U)`

  `π_*(c_n(ℱ^∨) ∩ π^*β) = β`. -/
theorem pushforward_chernFamily_dualKernel_bundlePullback (m : ℤ) (β : chowGroup C sU m) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      S.X₁ n hF
    properChowPushforward C sP sU π hsP m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m)
        (chowGroupCast C sP (by ring)
          (chernFamily C sP (dualSheaf S.X₁) n (m + n) n
            (bundlePullback C sU sP π hsP n hπ m β))) = β :=
  pushforward_capPow_chernFamily_dualKernel C sU sP π hsP n hπ 𝒞 S hS e₂ htower m β n 0
    (by omega)

end Pushforward

end Stacks.Chow.GenuineChern

end

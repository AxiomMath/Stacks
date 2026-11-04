module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TopChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRuleNaturality
public import StacksCore.Tactic.StacksAttribute

/-!
# The class of a subbundle, in arbitrary rank

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules, of
arbitrary (possibly nonconstant) ranks. **Stacks 0FAA** asserts

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`

for `α ∈ A_k(X)`, where `i : N' ⟶ N` is the closed embedding of the vector bundles
`N' = Spec_X(Sym((𝒩')^∨))`, `N = Spec_X(Sym(𝒩^∨))` and `p'`, `p` are their projections. Here
`c_top(ℰ)` is the class of Stacks 0FA4, assembled from the classes `c_r(ℰ|_{X_r})` on the rank loci
`X_r` of `ℰ`, and the formula is, by that very definition, a statement about the open and closed
loci `X_{a,b} = {rank 𝒩' = a} ∩ {rank ℰ = b}` of `X`, on which the ranks are constant and both
sides live in a single Chow group `A_{k+a}`.

This file proves it in that form. On `X_{a,b}` the degree `p` part of `c_top(ℰ)` caps by
`c_b(ℰ|_{X_{a,b}}) ∩ -` if `p = b` and by zero otherwise
(`Stacks.Chow.idRule_topChernClassComponent_of_le`,
`Stacks.Chow.idRule_topChernClassComponent_of_le_of_ne`), and the formula on `X_{a,b}` is the
constant-rank case `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_chernCap` applied to
the restricted sequence.

## Main results

* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_topChernClass` — **Stacks 0FAA**:
  on every `X_{a,b}`, `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`, the components of `c_top(ℰ)` of degree
  `p ≠ b` capping to zero there.
* `Stacks.Chow.idRule_topChernClassComponent_of_le` — on an open subscheme of the rank-`b` locus
  of `ℰ`, `c_top(ℰ)_b` caps by `c_b(ℰ|_U) ∩ -`.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Two cap products with the Chern classes of isomorphic modules, over equal structure
morphisms, at heterogeneously equal arguments, are heterogeneously equal. -/
theorem chernCap_heq_of_iso (C : ChowSituation.{u}) {T : Scheme.{u}} {q q' : T ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') {F F' : T.Modules} (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r] (e : F ≅ F')
    (k : ℤ) (i : Fin (r + 1)) {x : chowGroup C q k} {x' : chowGroup C q' k} (hx : x ≍ x') :
    GenuineChern.chernCap C r q F k i x ≍ GenuineChern.chernCap C r q' F' k i x' := by
  subst hq
  cases hx
  exact heq_of_eq (GenuineChern.chernCap_congr C q r e k i x)

/-- The zero classes of the Chow groups of two equal structure morphisms are heterogeneously
equal. -/
theorem zero_heq_zero_of_eq (C : ChowSituation.{u}) {T : Scheme.{u}} {q q' : T ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') (k : ℤ) :
    (0 : chowGroup C q k) ≍ (0 : chowGroup C q' k) := by
  subst hq
  rfl

/-- **Capping commutes with restriction to an open subscheme.** For `c ∈ A^p(X)`, `α ∈ A_k(X)` and
an open `U ⊆ X`, the restriction of `c ∩ α` to `U` is `c ∩ α|_U`: axiom (2) of Stacks 0B76 for the
open immersion `U ⟶ X`, which is flat of relative dimension zero. -/
theorem chowGroupRestrict_chowCohomologyCap (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) (U : X.Opens) (k : ℤ)
    (α : chowGroup C sX k) :
    chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - p)
        (chowCohomologyCap C (gysinSystemOfInvertible C) sX p c k α) =
      c.idRule C sX (gysinSystemOfInvertible C) U.ι k
        (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k α) := by
  have hr : AlgebraicGeometry.RelativeDimension U.ι 0 := relativeDimension_of_isOpenImmersion U.ι
  set α₁ := chowGroupCongr C (Category.id_comp sX).symm k α
  have hfs : pullback.fst (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) (𝟙 X) := by
    simpa using pullback.condition (f := 𝟙 X) (g := 𝟙 X)
  have hcap : chowCohomologyCap C (gysinSystemOfInvertible C) sX p c k α ≍
      c.idRule C sX (gysinSystemOfInvertible C) (𝟙 X) k α₁ := by
    simp only [chowCohomologyCap, BivariantClass.idRule_apply, pullbackSndPush,
      AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
    rw [chowPushforwardOfIso_congr C _ _ _ _ hfs rfl
      (by rw [← hfs])]
    exact chowPushforwardOfIso_heq _ _ _ rfl (Category.id_comp sX).symm rfl HEq.rfl
  have hfac1 := flatPullbackDescends C (U.ι ≫ sX) sX U.ι rfl 0 hr (k - p)
  have hfac2 := flatPullbackDescends C (U.ι ≫ sX) sX U.ι rfl 0 hr k
  have hfacp := flatPullbackDescends C ((U.ι ≫ 𝟙 X) ≫ sX) (𝟙 X ≫ sX) U.ι
    (by simp) 0 hr (k - p)
  have hfac := flatPullbackDescends C ((U.ι ≫ 𝟙 X) ≫ sX) (𝟙 X ≫ sX) U.ι
    (by simp) 0 hr k
  have hα : flatPullbackChow C ((U.ι ≫ 𝟙 X) ≫ sX) (𝟙 X ≫ sX) U.ι (by simp) 0 hr
      k hfac α₁ ≍ chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k α :=
    (flatPullbackChow_heq_congr_base C (by simp) (by simp) rfl _ _ rfl hr hr rfl hfac hfac2 α₁ α
      (chowGroupCongr_heq C _ k α)).trans
      (heq_chowGroupRestrict_flatPullbackChow C sX (U.ι ≫ sX) U.ι rfl hr k hfac2 α).symm
  refine eq_of_heq ?_
  refine (heq_chowGroupRestrict_flatPullbackChow C sX (U.ι ≫ sX) U.ι rfl hr (k - p) hfac1
    _).trans ?_
  refine (flatPullbackChow_heq_congr_base C (by simp) (by simp) rfl _ _ rfl hr hr rfl hfac1 hfacp
    _ _ hcap).trans ?_
  refine (BivariantClass.idRule_flatNaturality C sX (gysinSystemOfInvertible C) c (𝟙 X) U.ι 0 hr
    k hfac hfacp α₁).symm.trans ?_
  exact IdentityCapRule.heq_congr C sX _ (Category.comp_id _) (by simp) hα

section TopChernCap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- Restriction to a rank locus in the sense of Stacks 0FDZ is restriction along the inclusion of
that locus in the sense of Stacks 0B7F. -/
theorem rankLocusRestriction_eq_chowCohomologyRestriction {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) (r : ℕ) :
    rankLocusRestriction C (gysinSystemOfInvertible C) sX E
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p c r =
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c :=
  (chowCohomologyRestriction_eq_pieceIdentityCongr (rankLociFamily E) c (ULift.up r)).symm

/-- On a test scheme `j : T ⟶ X_r` of the rank-`r` locus, `c_top(ℰ)_p` caps as the `r`-th member
of its family on the rank loci. -/
theorem idRule_topChernClassComponent_comp_heq (p : ℤ) (r : ℕ) {T : Scheme.{u}}
    (j : T ⟶ (rankLocus E r : Scheme.{u})) [LocallyOfFiniteType j] (k : ℤ)
    (β : chowGroup C ((j ≫ (rankLocus E r).ι) ≫ sX) k)
    (β' : chowGroup C (j ≫ ((rankLocus E r).ι ≫ sX)) k) (hβ : β' ≍ β) :
    (topChernClassComponent C sX E p).idRule C sX (gysinSystemOfInvertible C)
        (j ≫ (rankLocus E r).ι) k β ≍
      (rankLocusTopChernFamily C sX E p r).idRule C ((rankLocus E r).ι ≫ sX)
        (gysinSystemOfInvertible C) j k β' := by
  rw [← rankLocusRestriction_topChernClassComponent C sX E p r,
    rankLocusRestriction_eq_chowCohomologyRestriction]
  exact (BivariantClass.idRule_chowCohomologyRestriction_heq (rankLocus E r).ι
    (topChernClassComponent C sX E p) j k β' β hβ).symm

/-- On an open `U` contained in the rank-`b` locus of `ℰ`, `c_top(ℰ)_p` caps over `U` as the
`b`-th member of its family on the rank loci, over the factorization `U ⟶ X_b ⟶ X`. -/
private theorem idRule_topChernClassComponent_heq_homOfLE (p : ℤ) (b : ℕ) (U : X.Opens)
    (hU : U ≤ rankLocus E b) (k : ℤ) (β : chowGroup C (U.ι ≫ sX) k) :
    (topChernClassComponent C sX E p).idRule C sX (gysinSystemOfInvertible C) U.ι k β ≍
      (rankLocusTopChernFamily C sX E p b).idRule C ((rankLocus E b).ι ≫ sX)
        (gysinSystemOfInvertible C) (X.homOfLE hU) k
        (chowGroupCongr C (by rw [← Category.assoc, X.homOfLE_ι hU]) k β) := by
  have hj : X.homOfLE hU ≫ (rankLocus E b).ι = U.ι := X.homOfLE_ι hU
  have hs : U.ι ≫ sX = X.homOfLE hU ≫ ((rankLocus E b).ι ≫ sX) := by
    rw [← Category.assoc, hj]
  have hs' : U.ι ≫ sX = (X.homOfLE hU ≫ (rankLocus E b).ι) ≫ sX := by rw [hj]
  exact (IdentityCapRule.heq_congr C sX _ hj.symm rfl
    (chowGroupCongr_heq C hs' k β).symm).trans
    (idRule_topChernClassComponent_comp_heq C sX E p b (X.homOfLE hU) k _
      (chowGroupCongr C hs k β)
      ((chowGroupCongr_heq C hs k β).trans (chowGroupCongr_heq C hs' k β).symm))

/-- **The top Chern class on a locus of constant rank.** On an open `U` contained in the rank-`b`
locus of `ℰ`, the degree `b` part of `c_top(ℰ)` caps by `c_b(ℰ|_U) ∩ -`. -/
theorem idRule_topChernClassComponent_of_le (b : ℕ) (U : X.Opens) (hU : U ≤ rankLocus E b)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj E) b]
    (k : ℤ) (β : chowGroup C (U.ι ≫ sX) k) :
    (topChernClassComponent C sX E b).idRule C sX (gysinSystemOfInvertible C) U.ι k β ≍
      GenuineChern.chernCap C b (U.ι ≫ sX) ((Scheme.Modules.pullback U.ι).obj E) k
        (Fin.last b) β := by
  have hj : X.homOfLE hU ≫ (rankLocus E b).ι = U.ι := X.homOfLE_ι hU
  have hs : U.ι ≫ sX = X.homOfLE hU ≫ ((rankLocus E b).ι ≫ sX) := by
    rw [← Category.assoc, hj]
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E b
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (X.homOfLE hU)).obj
        ((Scheme.Modules.pullback (rankLocus E b).ι).obj E)) b :=
    GenuineChern.isFiniteLocallyFreeOfRank_pullback _ _ b
  refine (idRule_topChernClassComponent_heq_homOfLE C sX E b b U hU k β).trans ?_
  rw [rankLocusTopChernFamily_self]
  refine (heq_of_eq (GenuineChern.idRule_chernClass C ((rankLocus E b).ι ≫ sX)
    ((Scheme.Modules.pullback (rankLocus E b).ι).obj E) b (Fin.last b) (X.homOfLE hU) k
    (chowGroupCongr C hs k β))).trans ?_
  let e : (Scheme.Modules.pullback (X.homOfLE hU)).obj
        ((Scheme.Modules.pullback (rankLocus E b).ι).obj E) ≅
      (Scheme.Modules.pullback U.ι).obj E :=
    (Scheme.Modules.pullbackComp (X.homOfLE hU) (rankLocus E b).ι).app E ≪≫
      eqToIso (congrArg (fun g ↦ (Scheme.Modules.pullback g).obj E) hj)
  exact chernCap_heq_of_iso C hs.symm b e k (Fin.last b) (chowGroupCongr_heq C hs k β)

/-- On an open `U` contained in the rank-`b` locus of `ℰ`, the parts of `c_top(ℰ)` of degree
`p ≠ b` cap to zero. -/
theorem idRule_topChernClassComponent_of_le_of_ne (b : ℕ) (U : X.Opens)
    (hU : U ≤ rankLocus E b) {p : ℤ} (hp : p ≠ b) (k : ℤ) (β : chowGroup C (U.ι ≫ sX) k) :
    (topChernClassComponent C sX E p).idRule C sX (gysinSystemOfInvertible C) U.ι k β = 0 := by
  have hs : U.ι ≫ sX = X.homOfLE hU ≫ ((rankLocus E b).ι ≫ sX) := by
    rw [← Category.assoc, X.homOfLE_ι hU]
  have h := idRule_topChernClassComponent_heq_homOfLE C sX E p b U hU k β
  rw [rankLocusTopChernFamily_of_ne C sX E (Ne.symm hp), BivariantClass.idRule_zero] at h
  exact eq_of_heq (h.trans (zero_heq_zero_of_eq C hs.symm (k - p)))

/-- The degree `p` part `c_top(ℰ)_p ∈ A^p(X)` of the top Chern class `c_top(ℰ) ∈ A^*(X)^∧` of
Stacks 0FA4: the `p`-th coordinate of the completed class in `∏_p A^p(X)`. -/
def topChernClassCompletedComponent (p : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)
    (topChernClassCompleted C sX E).1 p

/-- The degree `p` part of the completed top Chern class `c_top(ℰ) ∈ A^*(X)^∧` is the degree `p`
part `topChernClassComponent` of the top Chern class. -/
theorem topChernClassCompletedComponent_eq (p : ℤ) :
    topChernClassCompletedComponent C sX E p = topChernClassComponent C sX E p :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  congrFun (completedBivariantSequenceOfInvertible_topChernClassCompleted C sX E) p

end TopChernCap

/-! ### Stacks 0FAA -/

section Subbundle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
include w in
/-- The restricted maps of a complex compose to zero. -/
theorem pullback_map_comp_pullback_map_eq_zero {Y : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.Modules.pullback g).map inc ≫ (Scheme.Modules.pullback g).map pr = 0 := by
  rw [← Functor.map_comp, w, Functor.map_zero]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
include hseq in
/-- The restriction of the short exact sequence to an open subscheme is short exact. -/
theorem shortExact_pullback_map (U : X.Opens) :
    (ShortComplex.mk ((Scheme.Modules.pullback U.ι).map inc)
      ((Scheme.Modules.pullback U.ι).map pr)
      (pullback_map_comp_pullback_map_eq_zero N' N E inc pr w U.ι)).ShortExact :=
  GenuineChern.shortExact_map_pullback U.ι _ hseq

/-- **Stacks 0FAA on an open of constant ranks.** Let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact
sequence of finite locally free `𝒪_X`-modules, of arbitrary ranks, and let `α ∈ A_k(X)`. Let
`U ⊆ X` be open with `𝒩'` of constant rank `a` and `ℰ` of constant rank `b` on `U` — for
instance the open and closed locus
`X_{a,b} = Stacks.Chow.jointRankLocus 𝒩' ℰ (a, b)`; these loci decompose `X`
(`Stacks.Chow.isClopenDecomposition_jointRankLocus`). With `i : N'_U ⟶ N_U` the closed embedding
of the vector bundles `N'_U = Spec_U(Sym((𝒩'|_U)^∨))`, `N_U = Spec_U(Sym((𝒩|_U)^∨))` and `p'`,
`p` their projections,

  `i_*(p')^*(α|_U) = p^*((c_top(ℰ)_b ∩ α)|_U)`   and   `(c_top(ℰ)_q ∩ α)|_U = 0`  for  `q ≠ b`,

where `c_top(ℰ)_q` is the degree `q` part of the top Chern class `c_top(ℰ) ∈ A^*(X)^∧` of
Stacks 0FA4 and `c ∩ α` is `Stacks.Chow.chowCohomologyCap`. So
`i_*(p')^*α = p^*(c_top(ℰ) ∩ α)` on every such `U`. The two sides of the first
equality lie in `A_{k+a}(N_U)` and `A_{(k-b)+(a+b)}(N_U)`. -/
theorem subbundleEmbedding_pushforward_flatPullback_eq_topChernClass (U : X.Opens) (a b : ℕ)
    (hN' : U ≤ rankLocus N' a) (hE : U ≤ rankLocus E b) (k : ℤ) (α : chowGroup C sX k) :
    haveI := isFiniteLocallyFreeOfRank_of_le_rankLocus hN'
    haveI := isFiniteLocallyFreeOfRank_of_le_rankLocus hE
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact _ _ _
      ((Scheme.Modules.pullback U.ι).map inc) ((Scheme.Modules.pullback U.ι).map pr)
      (pullback_map_comp_pullback_map_eq_zero N' N E inc pr w U.ι)
      (shortExact_pullback_map N' N E inc pr w hseq U)
    haveI := isFiniteLocallyFreeOfRank_middle _ _ _ a b
      ((Scheme.Modules.pullback U.ι).map inc) ((Scheme.Modules.pullback U.ι).map pr)
      (pullback_map_comp_pullback_map_eq_zero N' N E inc pr w U.ι)
      (shortExact_pullback_map N' N E inc pr w hseq U)
    (chowPushforwardOfIsClosedImmersion C
        (dualVectorBundleToBase ((Scheme.Modules.pullback U.ι).obj N') ≫ (U.ι ≫ sX))
        (dualVectorBundleToBase ((Scheme.Modules.pullback U.ι).obj N) ≫ (U.ι ≫ sX))
        (subbundleEmbedding _ _ ((Scheme.Modules.pullback U.ι).map inc))
        (subbundleEmbedding_comp_base _ _ (U.ι ≫ sX) ((Scheme.Modules.pullback U.ι).map inc))
        (k + a)
        (dualBundlePullback C (U.ι ≫ sX) ((Scheme.Modules.pullback U.ι).obj N') a k
          (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k α)) ≍
      dualBundlePullback C (U.ι ≫ sX) ((Scheme.Modules.pullback U.ι).obj N) (a + b) (k - b)
        (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - b)
          (chowCohomologyCap C (gysinSystemOfInvertible C) sX b
            (topChernClassCompletedComponent C sX E b) k α))) ∧
    ∀ q : ℤ, q ≠ b →
      chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - q)
          (chowCohomologyCap C (gysinSystemOfInvertible C) sX q
            (topChernClassCompletedComponent C sX E q) k α) = 0 := by
  have := isFiniteLocallyFreeOfRank_of_le_rankLocus hN'
  have := isFiniteLocallyFreeOfRank_of_le_rankLocus hE
  set αU := chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k α
  refine ⟨?_, fun q hq ↦ ?_⟩
  · refine (subbundleEmbedding_pushforward_flatPullback_eq_chernCap C (U.ι ≫ sX) _ _ _ a b
      ((Scheme.Modules.pullback U.ι).map inc) ((Scheme.Modules.pullback U.ι).map pr)
      (pullback_map_comp_pullback_map_eq_zero N' N E inc pr w _)
      (shortExact_pullback_map N' N E inc pr w hseq _) k αU).trans (heq_of_eq ?_)
    rw [chowGroupRestrict_chowCohomologyCap, topChernClassCompletedComponent_eq]
    exact congrArg _ (eq_of_heq (idRule_topChernClassComponent_of_le C sX E b U hE k αU)).symm
  · rw [chowGroupRestrict_chowCohomologyCap, topChernClassCompletedComponent_eq]
    exact idRule_topChernClassComponent_of_le_of_ne C sX E b U hE hq k αU

end Subbundle

end Stacks.Chow

end

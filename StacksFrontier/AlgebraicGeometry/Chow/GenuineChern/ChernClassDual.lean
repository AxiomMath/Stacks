module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassDual
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PowerSumShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapSignScale
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of the dual of a finite locally free module: Stacks 0FA5

Let `X` be locally of finite type over the base of chapter 42 and let `ℰ` be a finite locally
free `𝒪_X`-module of rank `r`. [Stacks, Tag 0FA5] is the sign rule

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`.

`Stacks.Chow.GenuineChern.chernClass_dualSheaf` states it as an equality in `A^i(X)`, the group of
bivariant classes of degree `i` for `𝟙 X` of [Stacks, Tag 0B76], between the `i`-th Chern class of
`ℰ^∨` and `(-1)^i` times that of `ℰ`, for the classes `Stacks.Chow.GenuineChern.chernClass` of
[Stacks, Tag 0B7H]; the only hypothesis is that `ℰ` has rank `r`.

## The proof

The source reduces to a module with a filtration by invertible quotients, dualises the
filtration, and finishes by a formal computation. Here the induction is on the rank rather than on
a filtration:

* the content is the identity
  `Stacks.Chow.GenuineChern.chernFamily_dualSheaf` between *graded cap families*: the total Chern
  class of `ℰ^∨` is the `(-1)^i`-scaling `Stacks.Chow.capFamilySignScale` of the total Chern class
  of `ℰ`, in the ring `Stacks.Chow.GradedCapFamily`;
* in rank `0` both sides are `1`, and in rank `1` the identity is the first Chern class of a dual
  invertible module, `Stacks.Chow.GenuineChern.chernCap_one_dualSheaf`, which is the two clauses
  of [Stacks, Tag 02SP];
* in rank `r + 1` the projective bundle `π : 𝐏(ℰ) ⟶ X` carries the tautological sequence
  `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` with `ℱ` finite locally free of rank `r`
  (`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible`). Its
  dual `0 ⟶ 𝒪(1)^∨ ⟶ (π^*ℰ)^∨ ⟶ ℱ^∨ ⟶ 0` is short exact
  (`Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact`, Tag 0FV8's exactness
  of duality), so the Whitney sum formula of [Stacks, Tag 02UI]
  (`Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact`, unconditional) computes both total
  Chern classes on the bundle; the rank-one case and the inductive hypothesis turn the dual one
  into the scaling of the other, the two factors being interchanged, which is legitimate because
  the total Chern classes of two modules commute ([Stacks, Tag 02UA],
  `Stacks.Chow.GenuineChern.commute_chernFamily`);
* the identity descends from `𝐏(ℰ)` to `X` because `π^*` is injective on Chow groups (the top half
  of [Stacks, Tag 02TW], `Stacks.Chow.GenuineChern.pullback_injective`) and intertwines the total
  Chern class of a module with that of its pullback ([Stacks, Tag 02U8],
  `Stacks.Chow.GenuineChern.intertwines_chernFamily`); the dual of a pullback is the pullback of
  the dual by the base-change isomorphism of [Stacks, Tag 0GMX],
  `Stacks.Chow.pullbackDualMap_isIso`.

Finally the identity of bivariant classes follows from the cap-product one because a class
satisfying the characterization of Tag 0B7H is unique
(`Stacks.Chow.eq_of_isChernClassBivariant`): the cap operation of `(-1)^i c_i(ℰ)` on a test scheme
`g : T ⟶ X` is `(-1)^i` times `c_i(g^*ℰ) ∩ -`, which is `c_i(g^*(ℰ^∨)) ∩ -` by the cap-product
identity applied to `g^*ℰ` and the base-change isomorphism.

## Relation to the other renderings of the sign rule

The attribute here is an *additional* carrier of Tag 0FA5. The one that already stood,
`Stacks.Chow.chernClassCapExt_eq_zsmul_of_dualFiltration`, stays: it states the rule in the cycle
vocabulary of `Stacks.Chow.chernClassCapExt` and the elementary symmetric operations
`Stacks.Chow.elemSymmChernCap`, degreewise
against a fixed cycle and for the Chern class cap products of Stacks 02U0 presented as carried
data, and it carries the two filtrations and six further hypotheses.
`Stacks.Chow.HasDualChernSignRule`
states the rule as a `Prop` on a carried `Stacks.Chow.TotalChernClassSeries` — the form Stacks 0FAB
consumes — and carries no attribute.

None of the three is an instance of either other: they speak about three different renderings of
`c_i` in this repository, and the Chern classes `Stacks.Chow.GenuineChern.chernClass` of Stacks
0B7H that this file is stated at are the bivariant one.

## Main results

* `Stacks.Chow.GenuineChern.chernFamily_dualSheaf` — the total Chern class of the dual is the
  `(-1)^i`-scaling of the total Chern class.
* `Stacks.Chow.GenuineChern.chernCap_dualSheaf` — the same, componentwise on cap products.
* `Stacks.Chow.GenuineChern.chernClass_dualSheaf` — **Stacks 0FA5**, as an identity of bivariant
  classes in `A^i(X)`.

## References

* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-! ### The rank-one case -/

/-- **Stacks 0FA5 in rank one**, on total Chern classes: for `ℒ` of rank one the total Chern
class of `ℒ^∨` is the `(-1)^i`-scaling of that of `ℒ`.

In index `0` both sides are the identity, in index `1` the identity is
`Stacks.Chow.GenuineChern.chernCap_one_dualSheaf` — the two clauses of Stacks 02SP — and above
index `1` both sides vanish. -/
theorem chernFamily_dualSheaf_one {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (L : T.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf L 1 hL
    chernFamily C q (dualSheaf L) 1 = capFamilySignScale (chernFamily C q L 1) := by
  have :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf L 1 hL
  have := isInvertible_of_rank_one L
  funext k i
  refine AddMonoidHom.ext fun α => ?_
  rw [capFamilySignScale_apply]
  rcases i with _ | i
  · rw [pow_zero, one_smul, chernFamily_apply_zero C q (dualSheaf L) 1 k,
      chernFamily_apply_zero C q L 1 k]
  · rcases i with _ | i
    · rw [chernFamily_apply_of_le C q (dualSheaf L) 1 k le_rfl,
        chernFamily_apply_of_le C q L 1 k le_rfl, pow_one, neg_one_zsmul]
      exact chernCap_one_dualSheaf C q L k α
    · rw [chernFamily_apply_of_gt C q (dualSheaf L) 1 k (by omega),
        chernFamily_apply_of_gt C q L 1 k (by omega)]
      simp

/-! ### Stacks 0FA5 on total Chern classes, by induction on the rank -/

/-- **The tautological sequence of the projective bundle.** For `ℰ` finite locally free of rank
`n + 2`, there is a short exact sequence `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` on `𝐏(ℰ)` with `ℱ` finite
locally free of rank `n + 1`. Only the existence of the sequence is used, so the tautological map
is taken opaquely and `ℱ` is its kernel. -/
private theorem exists_shortExact_bundleTwist {T : Scheme.{u}} (E : T.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [E.IsQuasicoherent]
    [hπA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1)] :
    ∃ (F : (bundle E).Modules) (f : F ⟶ (Scheme.Modules.pullback (bundleProj E)).obj E)
      (g : (Scheme.Modules.pullback (bundleProj E)).obj E ⟶ bundleTwist E) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1) := by
  obtain ⟨τ, hτ⟩ : ∃ τ : (Scheme.Modules.pullback (bundleProj E)).obj E ⟶ bundleTwist E,
      Epi τ :=
    ⟨Stacks.ProjectiveBundleSplitting.tautologicalMap E (bundlePieces E),
      Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E (bundlePieces E)⟩
  have := hτ
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).presheaf
      (bundle E).ringCatSheaf.2 (bundleTwist E) := isInvertible_bundleTwist E
  exact ⟨kernel τ, kernel.ι τ, τ, kernel.condition τ,
    { exact := ShortComplex.exact_kernel τ },
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
      τ hτ hLinv (n + 1) hπA⟩

/-- **The sign rule on the projective bundle of `ℰ`.** Given a short exact sequence
`0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` on `𝐏(ℰ)` with `ℱ` of rank `n + 1` and the sign rule in rank `n + 1`,
the total Chern class of `(π^*ℰ)^∨` is the `(-1)^i`-scaling of that of `π^*ℰ`.

Both total Chern classes are computed by the Whitney sum formula of Stacks 02UI, the dual sequence
being short exact; the rank-one case and the hypothesis `ih` turn the one into the scaling of the
other, the two factors commuting by Stacks 02UA. -/
private theorem chernFamily_dualSheaf_bundle {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (E : T.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [Flat (bundleProj E)] [LocallyOfFiniteType (bundleProj E)]
    [hπA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1)]
    (F : (bundle E).Modules) (f : F ⟶ (Scheme.Modules.pullback (bundleProj E)).obj E)
    (g : (Scheme.Modules.pullback (bundleProj E)).obj E ⟶ bundleTwist E) (w : f ≫ g = 0)
    (hSE : (ShortComplex.mk f g w).ShortExact)
    [hrF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)]
    (ih : ∀ {T' : Scheme.{u}} (q' : T' ⟶ C.S) [LocallyOfFiniteType q'] (G : T'.Modules)
      [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (n + 1)],
      haveI :=
        Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf G (n + 1) hG
      chernFamily C q' (dualSheaf G) (n + 1) = capFamilySignScale (chernFamily C q' G (n + 1))) :
    haveI :=
      Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
        ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1) hπA
    chernFamily C (bundleProj E ≫ q)
        (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (n + 1 + 1) =
      capFamilySignScale (chernFamily C (bundleProj E ≫ q)
        ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1)) := by
  have hO : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (bundleTwist E) 1 := by
    have : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).sheaf.obj
        (bundle E).ringCatSheaf.property (bundleTwist E) := isInvertible_bundleTwist E
    exact isFiniteLocallyFreeOfRank_one_of_isInvertible _
  -- Stacks 02UI on the tautological sequence; the rank instances are supplied by hand,
  -- instance search not reducing the projection `(ShortComplex.mk ..).X₁` of a literal
  have hWup : chernFamily C (bundleProj E ≫ q)
        ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1) =
      chernFamily C (bundleProj E ≫ q) F (n + 1) *
        chernFamily C (bundleProj E ≫ q) (bundleTwist E) 1 :=
    @chernFamily_eq_mul_of_shortExact C (bundle E) (bundleProj E ≫ q) inferInstance
      (ShortComplex.mk f g w) hSE (n + 1) 1 hrF hO
  -- the dual sequence `0 ⟶ 𝒪(1)^∨ ⟶ (π^*ℰ)^∨ ⟶ ℱ^∨ ⟶ 0`
  have := isFiniteLocallyFree_of_rank F (n + 1)
  have := isFiniteLocallyFree_of_rank
    ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1)
  have := isFiniteLocallyFree_of_rank (bundleTwist E) 1
  obtain ⟨w', hSEd⟩ := Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact
    f g w hSE.mono_f hSE.epi_g hSE.exact
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree F)
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree
      ((Scheme.Modules.pullback (bundleProj E)).obj E))
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree (bundleTwist E))
  have hFd :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      F (n + 1) hrF
  have hOd :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      (bundleTwist E) 1 hO
  have hπAd :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1) hπA
  have hπAd' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (1 + (n + 1)) :=
    rank_of_iso (Iso.refl _) (by omega) hπAd
  -- Stacks 02UI on the dual sequence
  have hWdup : chernFamily C (bundleProj E ≫ q)
        (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (1 + (n + 1)) =
      chernFamily C (bundleProj E ≫ q) (dualSheaf (bundleTwist E)) 1 *
        chernFamily C (bundleProj E ≫ q) (dualSheaf F) (n + 1) :=
    @chernFamily_eq_mul_of_shortExact C (bundle E) (bundleProj E ≫ q) inferInstance
      (ShortComplex.mk (dualMap g) (dualMap f) w') hSEd 1 (n + 1) hOd hFd
  have hcongr1 : chernFamily C (bundleProj E ≫ q)
        (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (1 + (n + 1)) =
      chernFamily C (bundleProj E ≫ q)
        (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (n + 1 + 1) :=
    chernFamily_congr C (bundleProj E ≫ q)
      (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (n + 1 + 1)
      (Iso.refl _) (by omega)
  rw [← hcongr1, hWdup, chernFamily_dualSheaf_one C (bundleProj E ≫ q) (bundleTwist E),
    ih (bundleProj E ≫ q) F, ← capFamilySignScale_mul,
    (commute_chernFamily C (bundleProj E ≫ q) (bundleTwist E) 1 F (n + 1)).eq, ← hWup]

/-- **Stacks 0FA5 on total Chern classes.** For every finite locally free module `ℰ` of rank `r`
on a scheme locally of finite type over the base, the total Chern class of `ℰ^∨` is the
`(-1)^i`-scaling of the total Chern class of `ℰ`, as graded cap families on the Chow groups.

The induction is on `r`, with the scheme quantified over because the inductive step passes to the
projective bundle of `ℰ`. Rank `0` is `c = 1` on both sides, rank `1` is
`Stacks.Chow.GenuineChern.chernFamily_dualSheaf_one`, and the step is the tautological sequence of
`𝐏(ℰ)`, its dual, the Whitney sum formula of Stacks 02UI on both, and descent along the injective
flat pullback. -/
theorem chernFamily_dualSheaf :
    ∀ (r : ℕ) {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (E : T.Modules)
      [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r],
      haveI :=
        Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf E r hE
      chernFamily C q (dualSheaf E) r = capFamilySignScale (chernFamily C q E r) := by
  intro r
  induction r with
  | zero =>
    intro T q _ E hE
    have :=
      Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf E 0 hE
    rw [chernFamily_of_rank_zero C q (dualSheaf E), chernFamily_of_rank_zero C q E,
      capFamilySignScale_one]
  | succ m ih =>
    rcases m with _ | n
    · intro T q _ L _
      exact chernFamily_dualSheaf_one C q L
    · intro T q _ E hE
      have hED :=
        Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf E
          (n + 1 + 1) hE
      have hlf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
        isFiniteLocallyFree_of_rank E (n + 1 + 1)
      have := flat_bundleProj E (n + 1)
      have := locallyOfFiniteType_bundleProj E (n + 1)
      have : E.IsQuasicoherent :=
        Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
      have hd := relativeDimension_bundleProj E (n + 1)
      have hπA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1) :=
        isFiniteLocallyFreeOfRank_pullback _ E _
      -- the tautological sequence `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` on `𝐏(ℰ)`
      obtain ⟨F, f, g, w, hSE, hrF⟩ := exists_shortExact_bundleTwist E n
      have := hrF
      have hπAd :=
        Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
          ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1 + 1) hπA
      -- the identity on the bundle
      have hup := chernFamily_dualSheaf_bundle C q E n F f g w hSE ih
      -- the dual of the pullback is the pullback of the dual, Tag 0GMX
      have hπD : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (bundleProj E)).obj (dualSheaf E)) (n + 1 + 1) :=
        isFiniteLocallyFreeOfRank_pullback _ (dualSheaf E) _
      let eπ : (Scheme.Modules.pullback (bundleProj E)).obj (dualSheaf E) ≅
          dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E) :=
        @asIso _ _ _ _ (pullbackDualMap (bundleProj E) E)
          (pullbackDualMap_isIso (bundleProj E) E hlf)
      have hcongr2 : chernFamily C (bundleProj E ≫ q)
            ((Scheme.Modules.pullback (bundleProj E)).obj (dualSheaf E)) (n + 1 + 1) =
          chernFamily C (bundleProj E ≫ q)
            (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (n + 1 + 1) :=
        chernFamily_congr C (bundleProj E ≫ q)
          (dualSheaf ((Scheme.Modules.pullback (bundleProj E)).obj E)) (n + 1 + 1) eπ rfl
      -- descend along the injective flat pullback
      refine eq_of_intertwines _ (pullback_injective q E (topHalf C) (n + 1))
        (intertwines_chernFamily C q (dualSheaf E) (n + 1 + 1) (bundleProj E ≫ q)
          (bundleProj E) rfl (n + 1 + 1 - 1) hd _ (Iso.refl _))
        ((intertwines_chernFamily C q E (n + 1 + 1) (bundleProj E ≫ q) (bundleProj E) rfl
          (n + 1 + 1 - 1) hd _ (Iso.refl _)).capFamilySignScale) ?_
      rw [hcongr2, hup]

/-! ### Stacks 0FA5 componentwise on cap products -/

/-- **Stacks 0FA5 componentwise.** For `ℰ` finite locally free of rank `r`, every `0 ≤ i ≤ r`,
every degree `k` and every `α ∈ A_k(X)`,

  `c_i(ℰ^∨) ∩ α = (-1)^i (c_i(ℰ) ∩ α)`  in  `A_{k-i}(X)`,

for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6]. This is
`Stacks.Chow.GenuineChern.chernFamily_dualSheaf` read in one index. -/
theorem chernCap_dualSheaf {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (E : T.Modules)
    (r : ℕ) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (k : ℤ) (j : Fin (r + 1)) (α : chowGroup C q k) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf E r hE
    chernCap C r q (dualSheaf E) k j α = ((-1 : ℤ) ^ (j : ℕ)) • chernCap C r q E k j α := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf E r hE
  have hj : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.isLt
  have h2 : chernFamily C q (dualSheaf E) r k (j : ℕ) α =
      ((-1 : ℤ) ^ (j : ℕ)) • chernFamily C q E r k (j : ℕ) α := by
    rw [chernFamily_dualSheaf C r q E, capFamilySignScale_apply]
  rw [chernFamily_apply_of_le C q (dualSheaf E) r k hj,
    chernFamily_apply_of_le C q E r k hj] at h2
  exact h2

/-! ### Stacks 0FA5 as an identity of bivariant classes -/

/-- **Stacks 0FA5, bivariantly and unconditionally.** For a finite locally free `𝒪_X`-module `ℰ`
of rank `r` on a scheme `X` locally of finite type over the base and every `0 ≤ i ≤ r`,

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`

in `A^i(X)`, the group of bivariant classes of degree `i` for `𝟙 X` of Stacks 0B76, for the Chern
classes `Stacks.Chow.GenuineChern.chernClass` of Stacks 0B7H.

A bivariant class satisfying the characterization of Stacks 0B7H is unique
(`Stacks.Chow.eq_of_isChernClassBivariant`), so it suffices to check that `(-1)^i c_i(ℰ)` caps by
`c_i(g^*(ℰ^∨)) ∩ -` on every test scheme `g : T ⟶ X`. Integer multiples of bivariant classes are
pointwise on cap products, so the left side is `(-1)^i (c_i(g^*ℰ) ∩ -)`, and that is
`c_i(g^*(ℰ^∨)) ∩ -` by `Stacks.Chow.GenuineChern.chernCap_dualSheaf` applied to `g^*ℰ`, once the
base-change isomorphism of Tag 0GMX identifies `g^*(ℰ^∨)` with `(g^*ℰ)^∨`. -/
@[stacks 0FA5 "THE BIVARIANT AND UNCONDITIONAL FORM, an ADDITIONAL carrier -- the registration \
that already stood, Stacks.Chow.chernClassCapExt_eq_zsmul_of_dualFiltration, states the rule in \
the cycle vocabulary and carries two complete filtrations plus six further hypotheses, and \
Stacks.Chow.HasDualChernSignRule (which carries no attribute) states it as an assumed Prop on a \
carried total Chern class series; neither is superseded, because the three speak about three \
different renderings of c_i in this repository. WHAT IS PROVED HERE: for every scheme X locally \
of finite type over the \
base of chapter 42, every finite locally free O_X-module E of rank r, and every i with \
0 <= i <= r, the equality c_i(E^dual) = (-1)^i c_i(E) of BIVARIANT CLASSES in A^i(X) -- the \
group of bivariant classes of degree i for the identity of X, Tag 0B76 -- at the Chern classes \
Stacks.Chow.GenuineChern.chernClass of Tag 0B7H. HYPOTHESES: exactly the rank, i.e. E is finite \
locally free of rank r, plus X locally of finite type over the base. NOTHING ELSE IS CARRIED: no \
filtration of E and no filtration of E^dual, no splitting datum, no normalisation c_0 = 1, no \
binomial-transform equality, and no assumed compatibility of the cap products with flat pullback \
-- the last of these is now proved in this repository \
(Stacks.Chow.GenuineChern.intertwines_chernFamily, Tag 02U8), which is what makes the source's \
reduction performable. The source's first paragraph -- choose pi : P -> X as in Tag 02UL, use \
injectivity of pi^* to reduce to a filtered E, dualise the filtration -- is replaced by an \
induction on r through the projective bundle P(E) of E alone: the tautological sequence \
0 -> F -> pi^*E -> O(1) -> 0 has F finite locally free of rank r-1, its dual is short exact by \
the exactness of duality (Tag 0FV8), and the Whitney sum formula of Tag 02UI (unconditional \
here) computes both total Chern classes upstairs. This avoids the obstruction recorded at \
Stacks.Chow.chernClassCapExt_eq_zsmul_of_dualFiltration, namely that the filtration delivered by \
Tag 02UL is an inductive Prop from which the tower of modules Tag 02UJ takes as input cannot be \
eliminated: no filtration is ever needed, only one short exact sequence per inductive step. The \
rank of the dual is Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf \
(the dual-at-a-constant-rank clause of Tag 0FA7), which is what lets c_i(E^dual) be written at \
all. The dual is Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf, SheafHom(E, O_X) itself, \
and not a chosen tensor inverse. Also proved here, degreewise on cap products, is \
Stacks.Chow.GenuineChern.chernCap_dualSheaf, the same identity for the cap products of Tag 02U6"]
theorem chernClass_dualSheaf {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (j : Fin (r + 1)) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf E r hE
    chernClass C sX (dualSheaf E) r j = ((-1 : ℤ) ^ (j : ℕ)) • chernClass C sX E r j := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf E r hE
  have hlf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    isFiniteLocallyFree_of_rank E r
  refine eq_of_isChernClassBivariant C sX (dualSheaf E) r (gysinSystemOfInvertible C)
    (chernCap C r) (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (dualSheaf E) r) j
    (isChernClassBivariant_chernClass C sX (dualSheaf E) r j) ?_
  intro T g _ k α
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r g
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (dualSheaf E) r g
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    ((Scheme.Modules.pullback g).obj E) r inferInstance
  -- the dual base-change isomorphism `g^*(ℰ^∨) ≅ (g^*ℰ)^∨` of Tag 0GMX
  let eg : (Scheme.Modules.pullback g).obj (dualSheaf E) ≅
      dualSheaf ((Scheme.Modules.pullback g).obj E) :=
    @asIso _ _ _ _ (pullbackDualMap g E) (pullbackDualMap_isIso g E hlf)
  rw [BivariantClass.zsmul_cap, map_zsmul,
    isChernClassBivariant_chernClass C sX E r j g k α,
    chernCap_congr C (g ≫ sX) r eg k j α,
    chernCap_dualSheaf C (g ≫ sX) ((Scheme.Modules.pullback g).obj E) r k j α]

end Stacks.Chow.GenuineChern

end

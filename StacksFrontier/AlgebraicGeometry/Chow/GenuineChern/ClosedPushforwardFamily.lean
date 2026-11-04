module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PushforwardFamily
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FlatCompatProof
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme

/-!
# The Chern class cap products along a closed subscheme

Let `ℰ` be finite locally free of rank `n + 1` on `X` and `W ⊆ X` a closed subscheme. Granted that
projective bundles commute with base change (`Stacks.Chow.GenuineChern.BundleBaseChangeHolds`), the
projective bundle of `ℰ|_W` is the inverse image `π^{-1}(W) ⊆ 𝐏(ℰ)`, compatibly with the twists, so
the family of Chern class cap products of a class `β` on `W` for `ℰ|_W` pushes forward to the
family of `i_*β` for `ℰ` ([Stacks, Tag 02U9] for a closed immersion). At the fundamental class of
an integral `W` this says that the operation of [Stacks, Tag 02U5] at `[W]` is the family of
[Stacks, Tag 02U6].

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) (hG : BundleBaseChangeHolds.{u}) {X : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  (W : X.IdealSheafData)

include hG in
/-- **The family on `W` read on the inverse image of `W`.**  Granted that projective bundles
commute with base change, the projective bundle of `ℰ|_W` is the inverse image `π^{-1}(W) ⊆ 𝐏(ℰ)`:
the comparison `𝐏(ℰ|_W) ≅ π^{-1}(W)` is an isomorphism over `W` carrying the twist of the one to
the pullback of the twist of `𝐏(ℰ)`.  So the family of Chern class cap products of a class `β` on
`W` for `ℰ|_W`, characterized over `𝐏(ℰ|_W)` by Stacks 02U6, is characterized over `π^{-1}(W)`
as well: Stacks 02U9 transports the characterization along the comparison, whose pushforward on
Chow groups is the identity. -/
private theorem isChernCapFamily_comapRestrict
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [Flat (bundleProj E)] [LocallyOfFiniteType (bundleProj E)]
    [LocallyOfFiniteType (comapRestrict W (bundleProj E))]
    [Flat (comapRestrict W (bundleProj E))]
    (hsQ : comapRestrict W (bundleProj E) ≫ (W.subschemeι ≫ sX) =
      (W.comap (bundleProj E)).subschemeι ≫ (bundleProj E ≫ sX))
    (hπQ : AlgebraicGeometry.RelativeDimension (comapRestrict W (bundleProj E)) n) (k : ℤ)
    (β : chowGroup C (W.subschemeι ≫ sX) k) :
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E (n + 1)
    haveI := isInvertible_presheaf_modulePullback (bundleTwist E)
      (W.comap (bundleProj E)).subschemeι
    IsChernCapFamily C (W.subschemeι ≫ sX)
      ((W.comap (bundleProj E)).subschemeι ≫ (bundleProj E ≫ sX))
      (comapRestrict W (bundleProj E)) hsQ (n + 1) hπQ
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ hsQ _ _ k)
      (invCap C _ ((Scheme.Modules.pullback (W.comap (bundleProj E)).subschemeι).obj
        (bundleTwist E))) k β
      (bundleChernCapFamily ((Scheme.Modules.pullback W.subschemeι).obj E) n C
        (W.subschemeι ≫ sX) k β) := by
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E (n + 1)
  have := isInvertible_presheaf_modulePullback (bundleTwist E)
    (W.comap (bundleProj E)).subschemeι
  set F := (Scheme.Modules.pullback W.subschemeι).obj E
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F (n + 1)
  let := flat_bundleProj F n
  let := locallyOfFiniteType_bundleProj F n
  obtain ⟨e, he, ⟨eT⟩⟩ := hG W.subschemeι E F (Iso.refl _)
  have hQ := (isPullback_comapRestrict W (bundleProj E)).flip
  set ψ : bundle F ⟶ (W.comap (bundleProj E)).subscheme := e.hom ≫ hQ.isoPullback.inv with hψ
  have hψ1 : ψ ≫ comapRestrict W (bundleProj E) = bundleProj F := by
    rw [hψ, Category.assoc, IsPullback.isoPullback_inv_fst, he]
  have hψ2 : ψ ≫ (W.comap (bundleProj E)).subschemeι =
      e.hom ≫ pullback.snd W.subschemeι (bundleProj E) := by
    rw [hψ, Category.assoc, IsPullback.isoPullback_inv_snd]
  have eL1 : bundleTwist F ≅ (Scheme.Modules.pullback ψ).obj
      ((Scheme.Modules.pullback (W.comap (bundleProj E)).subschemeι).obj (bundleTwist E)) :=
    eT.symm ≪≫ ((Scheme.Modules.pullbackCongr hψ2).app (bundleTwist E)).symm ≪≫
      ((Scheme.Modules.pullbackComp ψ (W.comap (bundleProj E)).subschemeι).app
        (bundleTwist E)).symm
  have hψs : ψ ≫ ((W.comap (bundleProj E)).subschemeι ≫ (bundleProj E ≫ sX)) =
      bundleProj F ≫ (W.subschemeι ≫ sX) := by
    rw [← hsQ, ← Category.assoc, hψ1]
  -- the family on `W`, for the bundle of `ℰ|_W`
  have hc := isChernCapFamily_bundleChernCapFamily F n C (W.subschemeι ≫ sX) k β
  have h1 := properPushforward_isChernCapFamily C (W.subschemeι ≫ sX) (W.subschemeι ≫ sX)
    (bundleProj F ≫ (W.subschemeι ≫ sX))
    ((W.comap (bundleProj E)).subschemeι ≫ (bundleProj E ≫ sX)) (bundleProj F) rfl
    (comapRestrict W (bundleProj E)) hsQ (n + 1) (relativeDimension_bundleProj F n) hπQ
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ hsQ _ _ k)
    (bundleTwistCap F C (W.subschemeι ≫ sX))
    (invCap C _ ((Scheme.Modules.pullback (W.comap (bundleProj E)).subschemeι).obj
      (bundleTwist E))) (𝟙 _) (Category.id_comp _) ψ hψs
    (chernTermsCompatibleWithPushforward_of_isProper C (W.subschemeι ≫ sX)
      (W.subschemeι ≫ sX) _ _ (bundleProj F) rfl (comapRestrict W (bundleProj E)) hsQ n
      (relativeDimension_bundleProj F n) hπQ _ _ (𝟙 _) (Category.id_comp _) ψ hψs
      (bundleTwist F) _ eL1 (fun k y ↦ by
        rw [properChowPushforward_id, AddMonoidHom.id_apply]
        exact properChowPushforward_bundlePullback_of_isIso C (W.subschemeι ≫ sX) _ _
          (bundleProj F) rfl (comapRestrict W (bundleProj E)) hsQ n
          (relativeDimension_bundleProj F n) hπQ ψ hψ1 hψs k y))
    k β _ hc
  -- the comparison lies over `W`, so its pushforward on Chow groups is the identity
  have hid : ∀ c, properPushforwardChernFamily C (W.subschemeι ≫ sX) (W.subschemeι ≫ sX) (n + 1)
      (𝟙 W.subscheme) (Category.id_comp _) k c = c := fun c ↦ by
    funext j
    simp only [properPushforwardChernFamily, properChowPushforward_id, AddMonoidHom.id_apply]
  rw [hid, properChowPushforward_id, AddMonoidHom.id_apply] at h1
  exact h1

/-- Pushing forward the fundamental class of `W` along `W ⊆ X` gives its cycle class in `X`. -/
private theorem properChowPushforward_mk_cycleAssociatedToClosedSubscheme (k : ℤ) :
    properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl k)
      (QuotientAddGroup.mk' _
        (cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ sX) (𝟙 W.subscheme) k)) =
      QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme C sX W.subschemeι k) := by
  rw [properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (W.subschemeι ≫ sX) sX W.subschemeι rfl (𝟙 W.subscheme) k]
  simp only [Category.id_comp]

include hG in
/-- **Stacks 02U9 along a closed immersion.** The family of Chern class cap products of a class `β`
on a closed subscheme `W ⊆ X` for `ℰ|_W` pushes forward to the family of `i_*β` for `ℰ`. -/
theorem isBundleChernCapFamily_properPushforward (k : ℤ)
    (β : chowGroup C (W.subschemeι ≫ sX) k) :
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E (n + 1)
    IsBundleChernCapFamily E n C sX k
      (properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl k) β)
      (properPushforwardChernFamily C (W.subschemeι ≫ sX) sX (n + 1) W.subschemeι rfl k
        (bundleChernCapFamily ((Scheme.Modules.pullback W.subschemeι).obj E) n C
          (W.subschemeι ≫ sX) k β)) := by
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E (n + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  let := locallyOfFiniteType_comapRestrict W (bundleProj E)
  let := flat_comapRestrict W (bundleProj E)
  have := isInvertible_presheaf_modulePullback (bundleTwist E)
    (W.comap (bundleProj E)).subschemeι
  have hsQ : comapRestrict W (bundleProj E) ≫ (W.subschemeι ≫ sX) =
      (W.comap (bundleProj E)).subschemeι ≫ (bundleProj E ≫ sX) :=
    comapRestrict_comp_base C (bundleProj E ≫ sX) sX (bundleProj E) rfl W
  have hπQ := relativeDimension_comapRestrict W (bundleProj E) (relativeDimension_bundleProj E n)
  -- the family on `W`, transported to the inverse image of `W`
  have h1 := isChernCapFamily_comapRestrict C hG sX E n W hsQ hπQ k β
  -- pushed forward to `X`
  exact properPushforward_isChernCapFamily C (W.subschemeι ≫ sX) sX
    ((W.comap (bundleProj E)).subschemeι ≫ (bundleProj E ≫ sX)) (bundleProj E ≫ sX)
    (comapRestrict W (bundleProj E)) hsQ (bundleProj E) rfl (n + 1) hπQ
    (relativeDimension_bundleProj E n) _
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (invCap C _ ((Scheme.Modules.pullback (W.comap (bundleProj E)).subschemeι).obj
      (bundleTwist E)))
    (bundleTwistCap E C sX) W.subschemeι rfl (W.comap (bundleProj E)).subschemeι rfl
    (chernTermsCompatibleWithPushforward_of_isProper C (W.subschemeι ≫ sX) sX _ _
      (comapRestrict W (bundleProj E)) hsQ (bundleProj E) rfl n hπQ
      (relativeDimension_bundleProj E n) _ _ W.subschemeι rfl
      (W.comap (bundleProj E)).subschemeι rfl _ (bundleTwist E) (Iso.refl _)
      (fun k y ↦ properChowPushforward_bundlePullback_comap C sX (bundleProj E ≫ sX)
        (bundleProj E) rfl n (relativeDimension_bundleProj E n) W k y))
    k _ _ h1

include hG in
/-- **Stacks 02U6 at an integral closed subscheme.** For `W ⊆ X` integral of delta-dimension `k`,
the operation `c_j(ℰ) ∩ -` of Stacks 02U5 at `[W]` is the `j`-th member of the family of Chern
class cap products of `[W]` characterized by Stacks 02U6. -/
theorem chernCapOnCycles_integral_cycle_eq_bundleChernCapFamily (k : ℤ) (j : Fin (n + 1 + 1))
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = (k : EInt)) :
    chernCapOnCycles C sX E (n + 1) k j (cycleAssociatedToClosedSubscheme C sX W.subschemeι k) =
      bundleChernCapFamily E n C sX k
        (QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme C sX W.subschemeι k)) j := by
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E (n + 1)
  have h := isBundleChernCapFamily_properPushforward C hG sX E n W k
    (QuotientAddGroup.mk' _
      (cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ sX) (𝟙 W.subscheme) k))
  rw [properChowPushforward_mk_cycleAssociatedToClosedSubscheme] at h
  rw [← eq_bundleChernCapFamily_of_isChernCapFamily E n C sX k _ _ h,
    chernCapOnCycles_integral_cycle C sX E (n + 1) k j W hW hDim,
    chernClassFundamentalOfRank_succ]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] in
include hG in
/-- **Stacks 02U6 at an integral closed subscheme, at every rank.** For `W ⊆ X` integral of
delta-dimension `k` and `ℰ` of rank `r`, `c_j(ℰ) ∩ [W]` (Stacks 02U5) is the `j`-th member of the
family of Chern class cap products of `[W]` (Stacks 02U6). -/
theorem chernCapOnCycles_integral_cycle_eq_chernCapFamilyOfRank (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = (k : EInt)) :
    chernCapOnCycles C sX E r k j (cycleAssociatedToClosedSubscheme C sX W.subschemeι k) =
      chernCapFamilyOfRank E r C sX k
        (QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme C sX W.subschemeι k)) j := by
  rcases r with _ | m
  · have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E 0
    rw [chernCapOnCycles_integral_cycle C sX E 0 k j W hW hDim, chernClassFundamentalOfRank,
      chernCapFamilyOfRank_rank_zero, chernCapFamilyOfRank_rank_zero,
      ← properChowPushforward_chowGroupCast,
      properChowPushforward_mk_cycleAssociatedToClosedSubscheme]
  · rw [chernCapFamilyOfRank_succ]
    exact chernCapOnCycles_integral_cycle_eq_bundleChernCapFamily C hG sX E m W k j hW hDim

end Stacks.Chow.GenuineChern

end

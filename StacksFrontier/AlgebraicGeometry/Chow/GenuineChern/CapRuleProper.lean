module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PushforwardFamily
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine

/-!
# The Chern class cap products commute with proper pushforward

Let `p : X ⟶ Y` be a proper morphism of schemes locally of finite type over the base of
chapter 42 and let `ℰ` be finite locally free of rank `r` on `Y`. Then

  `p_*(c_j(p^*ℰ) ∩ α) = c_j(ℰ) ∩ p_*α`,  `0 ≤ j ≤ r`,

for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6]. This is
[Stacks, Tag 02U9]. The projective bundle of `p^*ℰ` is the base change of that of `ℰ`,
compatibly with the twists, so pushing the relation of Stacks 02U6 forward along the proper
morphism of bundles gives the relation for `p_*α`: the pullbacks to the bundles commute with the
pushforwards by [Stacks, Tag 02RG]
(`Stacks.Chow.flatPullbackChow_properChowPushforward_unconditional`) and the caps with the
twists commute with them by [Stacks, Tag 02SU]
(`Stacks.Chow.properChowPushforward_invCap_capOnChow`, through
`Stacks.Chow.GenuineChern.chernTermsCompatibleWithPushforward_of_isProper`). The injectivity half
of [Stacks, Tag 02TX] then identifies the two families
(`Stacks.Chow.isChernCapFamily_properPushforward`).

## Main results

* `Stacks.Chow.GenuineChern.bundleChernCapFamily_properPushforward` — Stacks 02U9 for the family
  of a module of rank `n + 1`.
* `Stacks.Chow.GenuineChern.chernCap_properPushforward` — Stacks 02U9 for the cap products in
  every rank.
* `Stacks.Chow.GenuineChern.chernCap_properNaturality` — the projection formula
  `Stacks.Chow.IdentityCapRule.ProperNaturality` of the identity cap rule of the bivariant Chern
  class, which is axiom (1) of Stacks 0B76 read on the test schemes.

## References

* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- **Stacks 02U9 for the cap products of Stacks 02U6, rank `n + 1`.** For `p : X ⟶ Y` proper
over the base, `ℰ` of rank `n + 1` on `Y` and `ℰ' ≅ p^*ℰ`, the family of `p_*α` for `ℰ` is the
pushforward of the family of `α` for `ℰ'`. -/
theorem bundleChernCapFamily_properPushforward {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p]
    (hp : p ≫ sY = sX) (E : Y.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (E' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    (eE : E' ≅ (Scheme.Modules.pullback p).obj E) (k : ℤ) (α : chowGroup C sX k) :
    bundleChernCapFamily E n C sY k
        (properChowPushforward C sX sY p hp k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k) α) =
      properPushforwardChernFamily C sX sY (n + 1) p hp k (bundleChernCapFamily E' n C sX k α) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E'
    (n + 1)
  obtain ⟨e, he, ⟨eT⟩⟩ := bundleBaseChangeHolds p E E' eE
  set p' : bundle E' ⟶ bundle E := e.hom ≫ pullback.snd p (bundleProj E) with hp'def
  have hsq : IsPullback (bundleProj E') p' p (bundleProj E) := by
    refine (IsPullback.of_hasPullback p (bundleProj E)).of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
    · rw [Iso.symm_hom, hp'def, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
  have : IsProper p' := MorphismProperty.of_isPullback hsq inferInstance
  have hcomm : p' ≫ bundleProj E = bundleProj E' ≫ p := hsq.w.symm
  have hp' : p' ≫ (bundleProj E ≫ sY) = bundleProj E' ≫ sX := by
    rw [← Category.assoc, hcomm, Category.assoc, hp]
  let := Stacks.Chow.flat_bundleProj E n
  let := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  let := Stacks.Chow.flat_bundleProj E' n
  let := Stacks.Chow.locallyOfFiniteType_bundleProj E' n
  have hrE := Stacks.Chow.relativeDimension_bundleProj E n
  have hrE' := Stacks.Chow.relativeDimension_bundleProj E' n
  have hfX := fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E' ≫ sX) sX (bundleProj E') rfl n hrE' j
  have hfY := fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E ≫ sY) sY (bundleProj E) rfl n hrE j
  have hPB : ∀ (k : ℤ) (y : chowGroup C sX k),
      properChowPushforward C (bundleProj E' ≫ sX) (bundleProj E ≫ sY) p' hp' (k + n)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ p' hp' _)
          (bundlePullback C sX (bundleProj E' ≫ sX) (bundleProj E') rfl n
            hrE' k y) =
        bundlePullback C sY (bundleProj E ≫ sY) (bundleProj E) rfl n
          hrE k
          (properChowPushforward C sX sY p hp k
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k) y) :=
    fun k y => (flatPullbackChow_properChowPushforward_unconditional C sX sY
      (bundleProj E' ≫ sX) (bundleProj E ≫ sY) p (bundleProj E) (bundleProj E') p' hsq hp rfl rfl
      n hrE k y).symm
  have hcompat := chernTermsCompatibleWithPushforward_of_isProper C sX sY (bundleProj E' ≫ sX)
    (bundleProj E ≫ sY) (bundleProj E') rfl (bundleProj E) rfl n
    hrE' hrE
    hfX
    hfY
    p hp p' hp' (bundleTwist E') (bundleTwist E) eT.symm hPB
  have hinj := projectiveBundleRelationInjective_of_bundleMap C sY (bundleProj E ≫ sY)
    (bundleProj E) rfl n hrE
    hfY
    (bundleTwistCap E C sY) fun j ↦ (projectiveBundle_formula E n C sY j).1
  exact isChernCapFamily_properPushforward C sX sY (bundleProj E' ≫ sX) (bundleProj E ≫ sY)
    (bundleProj E') rfl (bundleProj E) rfl (n + 1)
    hrE' hrE
    hfX
    hfY
    (bundleTwistCap E' C sX) (bundleTwistCap E C sY) p hp p' hp' hinj hcompat k α _ _
    (isChernCapFamily_bundleChernCapFamily E' n C sX k α)
    (isChernCapFamily_bundleChernCapFamily E n C sY k _)

/-- **Stacks 02U9 for the cap products of Stacks 02U6, in every rank.** For `p : X ⟶ Y` proper
over the base, `ℰ` of rank `r` on `Y` and `ℰ' ≅ p^*ℰ`,

  `c_j(ℰ) ∩ p_*α = p_*(c_j(ℰ') ∩ α)`. -/
theorem chernCap_properPushforward {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p]
    (hp : p ≫ sY = sX) (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (E' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback p).obj E) (k : ℤ) (j : Fin (r + 1))
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (hfacp : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp (k - (j : ℤ)))
    (α : chowGroup C sX k) :
    chernCap C r sY E k j (properChowPushforward C sX sY p hp k hfac α) =
      properChowPushforward C sX sY p hp (k - (j : ℤ)) hfacp (chernCap C r sX E' k j α) := by
  cases r with
  | zero =>
    rw [chernCap_zero, chernCap_zero]
    exact properChowPushforward_chowGroupCast C sX sY p hp _ α
  | succ n =>
    rw [chernCap_succ, chernCap_succ, bundleChernCap_apply, bundleChernCap_apply]
    exact congrFun (bundleChernCapFamily_properPushforward C sX sY p hp E n E' eE k α) j

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 02U9, as the projection formula of the identity cap rule of the bivariant Chern
class.** For `ℱ` finite locally free of rank `r` on `X` and every `0 ≤ j ≤ r`, the rule
`α ↦ c_j(g^*ℱ) ∩ α` on the test schemes `g : T ⟶ X` commutes with proper pushforward. -/
theorem chernCap_properNaturality (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1)) :
    IdentityCapRule.ProperNaturality C sX (j : ℤ)
      (chernIdentityCapRuleOfRank C sX F r (chernCap C r) j) := by
  intro T T' g _ h _ k hfac hfacp α
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r (h ≫ g)
  exact chernCap_properPushforward C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc])
    ((Scheme.Modules.pullback g).obj F) r ((Scheme.Modules.pullback (h ≫ g)).obj F)
    ((Scheme.Modules.pullbackComp h g).app F).symm k j hfac hfacp α

end Stacks.Chow.GenuineChern

end

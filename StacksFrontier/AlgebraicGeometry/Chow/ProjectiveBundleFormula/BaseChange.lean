module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIso
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.PushforwardFamily
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.CapPowCommute
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic

/-!
# The projective space bundle formula for a base change of a projective bundle

Let `ℰ` be a finite locally free module of rank `n + 1` on `X`, let `g : U ⟶ X` be a morphism and
let `q : Q ⟶ U` be a base change of the projective bundle `π : 𝐏(ℰ) ⟶ X` along `g`, with second
projection `h : Q ⟶ 𝐏(ℰ)`, and `ℒ ≅ h^*𝒪(1)` on `Q`. Then `Q` is the projective bundle of `g^*ℰ`
with twist `ℒ` (Stacks 01O3), so the projective space bundle formula of Stacks 02TX holds for
`(q, ℒ)`: the map

  `⨁_{i ≤ n} A_{k+i}(U) ⟶ A_{k+n}(Q)`,  `(α_i) ↦ ∑_i c₁(ℒ)^i ∩ q^*α_i`

is bijective. This is how the projective space bundle formula is applied to a projective bundle
presented as a fibre product, as in the proof of Stacks 0FGQ, where `Q = Z × 𝐏(ℰ)` over
`U = Z × X`.

## Main results

* `Stacks.Chow.bijective_bundleMap_of_isPullback`.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Flat pullback along equal morphisms agrees, heterogeneously. -/
theorem flatPullbackChow_heq_of_eq_hom (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {f f' : X' ⟶ X} [LocallyOfFiniteType f] [Flat f] [LocallyOfFiniteType f'] [Flat f']
    (e : f = f') (hbase : f ≫ sX = sX') (hbase' : f' ≫ sX = sX') {r r' : ℕ} (er : r = r')
    (hf : AlgebraicGeometry.RelativeDimension f r) (hf' : AlgebraicGeometry.RelativeDimension f' r')
    (k : ℤ) (x : chowGroup C sX k) :
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k x ≍
      flatPullbackChowOfRelativeDimension C sX' sX f' hbase' r' hf' k x := by
  subst e er
  rfl

variable (C : ChowSituation.{u}) {X U Q : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
  (g : U ⟶ X) (q : Q ⟶ U) [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sU = sQ)
  (hqn : AlgebraicGeometry.RelativeDimension q n) (h : Q ⟶ bundle E)

/-- **Stacks 02TX for a base change of a projective bundle.** If `q : Q ⟶ U` is the base change of
the projective bundle `𝐏(ℰ) ⟶ X` of a module of rank `n + 1` along `g : U ⟶ X`, with second
projection `h`, and `ℒ ≅ h^*𝒪(1)`, then `(α_i) ↦ ∑_i c₁(ℒ)^i ∩ q^*α_i`,
`⨁_{i ≤ n} A_{k+i}(U) ⟶ A_{k+n}(Q)`, is bijective. -/
theorem bijective_bundleMap_of_isPullback
    (hsq : IsPullback q h g (bundleProj E))
    (L : Q.Modules) [SheafOfModules.IsInvertible Q.sheaf.obj Q.ringCatSheaf.property L]
    (eL : L ≅ (Scheme.Modules.pullback h).obj (bundleTwist E)) (k : ℤ) :
    Function.Bijective (bundleMap C sU sQ q hq n hqn (invCap C sQ L) k) := by
  set E' := (Scheme.Modules.pullback g).obj E with hE'
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1) :=
    isFiniteLocallyFreeOfRank_pullback g E (n + 1)
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E' (n + 1)
  let := flat_bundleProj E' n
  let := locallyOfFiniteType_bundleProj E' n
  have hP' := isPullback_bundleBaseChangeHom g E E' (Iso.refl _)
  set Θ := hsq.isoIsPullback _ _ hP' with hΘ
  have hΘπ : Θ.hom ≫ bundleProj E' = q := hsq.isoIsPullback_hom_fst _ _ hP'
  have hΘh : Θ.hom ≫ bundleBaseChangeHom g E E' (Iso.refl _) = h :=
    hsq.isoIsPullback_hom_snd _ _ hP'
  have hΘs : Θ.hom ≫ bundleProj E' ≫ sU = sQ := by rw [← Category.assoc, hΘπ, hq]
  -- the twist of `𝐏(ℰ')` pulls back to `ℒ`
  have eT : (Scheme.Modules.pullback Θ.hom).obj (bundleTwist E') ≅ L :=
    (Scheme.Modules.pullback Θ.hom).mapIso
        ((bundleBaseChange g E E' (Iso.refl _)).twistIso.symm ≪≫
          (Scheme.Modules.pullbackCongr (bundleBaseChangeIso_hom_snd g E E' (Iso.refl _))).app _) ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hΘh).app _ ≪≫ eL.symm
  have := GenuineChern.isInvertible_pullback Θ.hom (bundleTwist E')
  have hΘ0 : AlgebraicGeometry.RelativeDimension Θ.hom 0 := relativeDimension_of_isOpenImmersion _
  -- flat pullback along `Θ` is bijective
  have hbijΘ := flatPullbackChow_bijective_of_isIso C sQ (bundleProj E' ≫ sU) Θ.hom hΘs hΘ0
    (k + n) (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
  -- the map of Stacks 02TX for `ℰ'` is bijective
  have h02TX := projectiveBundle_formula E' n C sU k
  -- our map is flat pullback along `Θ` of the map of Stacks 02TX for `ℰ'`
  have key : ∀ β, bundleMap C sU sQ q hq n hqn (invCap C sQ L) k β ≍
      flatPullbackChow C sQ (bundleProj E' ≫ sU) Θ.hom hΘs 0 hΘ0 (k + n)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (bundleMap C sU (bundleProj E' ≫ sU) (bundleProj E') rfl n
          (relativeDimension_bundleProj E' n)
          (invCap C (bundleProj E' ≫ sU) (bundleTwist E')) k β) := by
    intro β
    have hterm : ∀ i : Fin (n + 1),
        bundleTerm C sU sQ q hq n hqn (invCap C sQ L) k i (β i) ≍
          flatPullbackChow C sQ (bundleProj E' ≫ sU) Θ.hom hΘs 0 hΘ0 (k + n)
            (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
            (bundleTerm C sU (bundleProj E' ≫ sU) (bundleProj E') rfl n
              (relativeDimension_bundleProj E' n) (invCap C (bundleProj E' ≫ sU) (bundleTwist E'))
              k i (β i)) := by
      intro i
      simp only [bundleTerm, AddMonoidHom.coe_comp, Function.comp_apply]
      have hcp := flatPullbackChowOfRelativeDimension_capPow C sQ (bundleProj E' ≫ sU) Θ.hom hΘs 0
        hΘ0 (bundleTwist E') i (k + i + n) (k + n) (by ring)
        (bundlePullback C sU (bundleProj E' ≫ sU) (bundleProj E') rfl n
          (relativeDimension_bundleProj E' n) (k + i) (β i))
      refine HEq.trans ?_ (heq_of_eq hcp).symm
      rw [GenuineChern.capPow_invCap_congr C sQ eT]
      refine capPow_heq_of_heq C sQ (invCap C sQ L) i _ _ (by push_cast; ring) (by push_cast; ring)
        ?_
      have hcomp := flatPullbackChow_comp C sQ (bundleProj E' ≫ sU) sU Θ.hom (bundleProj E') hΘs rfl
        0 n hΘ0 (relativeDimension_bundleProj E' n) (k + i)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) (β i)
      exact ((flatPullbackChow_heq_of_eq_hom C sQ sU hΘπ.symm hq _ (by simp) hqn _ (k + i)
        (β i)).trans hcomp.symm)
    have hsum := map_sum (flatPullbackChow C sQ (bundleProj E' ≫ sU) Θ.hom hΘs 0 hΘ0 (k + n)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _))
      (fun i : Fin (n + 1) ↦ bundleTerm C sU (bundleProj E' ≫ sU) (bundleProj E') rfl n
        (relativeDimension_bundleProj E' n) (invCap C (bundleProj E' ≫ sU) (bundleTwist E')) k i
        (β i)) Finset.univ
    rw [bundleMap_apply, bundleMap_apply, hsum]
    have hcast := map_sum (chowGroupCast C sQ (by push_cast; ring : k + n + ((0 : ℕ) : ℤ) = k + n))
      (fun i : Fin (n + 1) ↦ flatPullbackChow C sQ (bundleProj E' ≫ sU) Θ.hom hΘs 0 hΘ0 (k + n)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (bundleTerm C sU (bundleProj E' ≫ sU) (bundleProj E') rfl n
          (relativeDimension_bundleProj E' n) (invCap C (bundleProj E' ≫ sU) (bundleTwist E')) k i
          (β i))) Finset.univ
    refine HEq.trans ?_ (chowGroupCast_heq C sQ
      (by push_cast; ring : k + n + ((0 : ℕ) : ℤ) = k + n) _)
    rw [hcast]
    exact heq_of_eq (Finset.sum_congr rfl fun i _ ↦
      eq_of_heq ((hterm i).trans (chowGroupCast_heq C sQ _ _).symm))
  have hfun : ⇑(bundleMap C sU sQ q hq n hqn (invCap C sQ L) k) =
      ⇑(chowGroupCast C sQ (by push_cast; ring : k + n + ((0 : ℕ) : ℤ) = k + n)) ∘
        (flatPullbackChow C sQ (bundleProj E' ≫ sU) Θ.hom hΘs 0 hΘ0 (k + n)
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)) ∘
        (bundleMap C sU (bundleProj E' ≫ sU) (bundleProj E') rfl n
          (relativeDimension_bundleProj E' n) (invCap C (bundleProj E' ≫ sU) (bundleTwist E')) k) :=
    funext fun β ↦ eq_of_heq ((key β).trans (chowGroupCast_heq C sQ _ _).symm)
  rw [hfun]
  exact (chowGroupCast C sQ _).bijective.comp (hbijΘ.comp h02TX)

end Stacks.Chow

end

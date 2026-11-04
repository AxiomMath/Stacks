module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Compat

/-!
# Stacks 02TW for a base change of a projective bundle

Let `ℰ` be a finite locally free module of rank `n + 1` on `X`, let `g : U ⟶ X` be a morphism and
let `q : Q ⟶ U` be a base change of the projective bundle `π : 𝐏(ℰ) ⟶ X` along `g`, with second
projection `h : Q ⟶ 𝐏(ℰ)`, and `ℒ ≅ h^*𝒪(1)` on `Q`. Then `Q` is the projective bundle of `g^*ℰ`
with twist `ℒ` (Stacks 01O3), so Stacks 02TW holds for `(q, ℒ)`: for `s ≤ n` and `α ∈ A_k(U)`,

  `q_*(c₁(ℒ)^s ∩ q^*α) = 0` if `s < n`, and `q_*(c₁(ℒ)^n ∩ q^*α) = α`.

The comparison is through an isomorphism `ψ : Q ≅ P` over `U` carrying the twist of `P` to `ℒ`:
the operation of Stacks 02TW only depends on `(Q, ℒ)` up to such an isomorphism, since pushing
forward along `ψ` commutes with capping with `c₁` and undoes flat pullback.

## Main results

* `Stacks.Chow.bundleProjection_eq_of_isIso`: the operation of Stacks 02TW is invariant under an
  isomorphism of bundles over the same base respecting the invertible modules.
* `Stacks.Chow.bundleProjection_of_isPullback`: Stacks 02TW for a base change of a projective
  bundle.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **The operation of Stacks 02TW is invariant under isomorphism.** If `ψ : Q ⟶ P` is an
isomorphism with `ψ ≫ π = q`, and `ψ^*𝒩 ≅ ℒ`, then `q_*(c₁(ℒ)^s ∩ q^*α) = π_*(c₁(𝒩)^s ∩ π^*α)`. -/
theorem bundleProjection_eq_of_isIso (C : ChowSituation.{u}) {U Q P : Scheme.{u}}
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (q : Q ⟶ U) [LocallyOfFiniteType q] [Flat q]
    [IsProper q] (hq : q ≫ sU = sQ) (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π] [IsProper π]
    (hsP : π ≫ sU = sP) (n : ℕ) (hqn : AlgebraicGeometry.RelativeDimension q n)
    (hπ : AlgebraicGeometry.RelativeDimension π n) (ψ : Q ⟶ P) [IsIso ψ] (hψ : ψ ≫ π = q)
    (L : Q.Modules) [SheafOfModules.IsInvertible Q.sheaf.obj Q.ringCatSheaf.property L]
    (N : P.Modules) [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property N]
    (e : (Scheme.Modules.pullback ψ).obj N ≅ L) (s : ℕ) (k m : ℤ) (hkm : k + n = m + s)
    (α : chowGroup C sU k) :
    bundleProjection C sU sQ q hq n hqn (invCap C sQ L) s k m hkm α =
      bundleProjection C sU sP π hsP n hπ (invCap C sP N) s k m hkm α := by
  subst hψ
  have hψs : ψ ≫ sP = sQ := by rw [← hsP, ← hq, Category.assoc]
  have := GenuineChern.isInvertible_pullback ψ N
  simp only [bundleProjection, AddMonoidHom.comp_apply]
  rw [← GenuineChern.capPow_invCap_congr C _ e]
  have hcomp := DFunLike.congr_fun (properChowPushforward_comp C sQ sP sU ψ π hψs hsP m
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _))
  rw [← hcomp _, AddMonoidHom.comp_apply, properChowPushforward_capPow,
    GenuineChern.properChowPushforward_bundlePullback_of_isIso C sU sQ sP (ψ ≫ π) hq π hsP
      n hqn hπ ψ rfl hψs k α]

variable (C : ChowSituation.{u}) {X U Q : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
  (g : U ⟶ X) (q : Q ⟶ U) [LocallyOfFiniteType q] [Flat q] [IsProper q] (hq : q ≫ sU = sQ)
  (hqn : AlgebraicGeometry.RelativeDimension q n) (h : Q ⟶ bundle E)

/-- **Stacks 02TW for a base change of a projective bundle.** If `q : Q ⟶ U` is the base change of
the projective bundle `𝐏(ℰ) ⟶ X` of a module of rank `n + 1` along `g : U ⟶ X`, with second
projection `h`, and `ℒ ≅ h^*𝒪(1)`, then for `s ≤ n` and `α ∈ A_k(U)` the class
`q_*(c₁(ℒ)^s ∩ q^*α) ∈ A_{k+n-s}(U)` is `0` if `s < n` and is `α` if `s = n`. -/
theorem bundleProjection_of_isPullback (hsq : IsPullback q h g (bundleProj E))
    (L : Q.Modules) [SheafOfModules.IsInvertible Q.sheaf.obj Q.ringCatSheaf.property L]
    (eL : L ≅ (Scheme.Modules.pullback h).obj (bundleTwist E)) (s : ℕ) (hs : s ≤ n) (k m : ℤ)
    (hkm : k + n = m + s) (α : chowGroup C sU k) :
    bundleProjection C sU sQ q hq n hqn (invCap C sQ L) s k m hkm α =
      if hsn : s = n then chowGroupCast C sU (by subst hsn; omega) α else 0 := by
  set E' := (Scheme.Modules.pullback g).obj E
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1) :=
    isFiniteLocallyFreeOfRank_pullback g E (n + 1)
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E' (n + 1)
  let := flat_bundleProj E' n
  let := locallyOfFiniteType_bundleProj E' n
  have hP' := isPullback_bundleBaseChangeHom g E E' (Iso.refl _)
  set Θ := hsq.isoIsPullback _ _ hP'
  have hΘπ : Θ.hom ≫ bundleProj E' = q := hsq.isoIsPullback_hom_fst _ _ hP'
  have hΘh : Θ.hom ≫ bundleBaseChangeHom g E E' (Iso.refl _) = h :=
    hsq.isoIsPullback_hom_snd _ _ hP'
  -- the twist of `𝐏(ℰ')` pulls back to `ℒ`
  have eT : (Scheme.Modules.pullback Θ.hom).obj (bundleTwist E') ≅ L :=
    (Scheme.Modules.pullback Θ.hom).mapIso
        ((bundleBaseChange g E E' (Iso.refl _)).twistIso.symm ≪≫
          (Scheme.Modules.pullbackCongr (bundleBaseChangeIso_hom_snd g E E' (Iso.refl _))).app _) ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hΘh).app _ ≪≫ eL.symm
  rw [bundleProjection_eq_of_isIso C sU sQ (bundleProj E' ≫ sU) q hq (bundleProj E') rfl n hqn
    (relativeDimension_bundleProj E' n) Θ.hom hΘπ L (bundleTwist E') eT s k m hkm α]
  exact projectiveBundle_projection E' n C sU s hs k m hkm α

end Stacks.Chow

end

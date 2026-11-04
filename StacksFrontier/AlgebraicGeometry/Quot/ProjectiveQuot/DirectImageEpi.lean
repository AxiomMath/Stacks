module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.EpiResidueFields
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# Surjectivity of `π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))`, reduced to the fibres

For `K ∈ Quot^P(T)` with quotient map `q : 𝒪^{⊕ r} ⟶ 𝒬` and `m = regularityIndex n r hr P`, the
map `π_*(q(m)) : π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))` is surjective as soon as, for every point `t ∈ T`,
the base-change morphism of `𝒪^{⊕ r}(m)` along `Spec κ(t) ⟶ T` is invertible and the map
`Γ(ℙⁿ_{κ(t)}, 𝒪^{⊕ r}(m)) ⟶ Γ(ℙⁿ_{κ(t)}, 𝒬_t(m))` is surjective, read as a map of modules on
`Spec κ(t)`. The target `π_*(𝒬(m))` is finite locally free and commutes with base change
(`AlgebraicGeometry.ProjectiveQuot.isIso_baseChangeNatTrans_twist_quotient`), so this is
Nakayama's lemma
(`AlgebraicGeometry.Scheme.Modules.epi_of_forall_epi_pullback_fromSpecResidueField`). This is the
step of the proof of Stacks 0DPA producing the surjection `W ⊗ 𝒪_T ⟶ π_*(𝒬(m))`.

The two fibrewise inputs are explicit hypotheses of this unregistered reduction lemma.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.epi_pushforward_twistMap_quotientπ_of_fibres`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ} (hr : 1 ≤ r) {P : Polynomial ℚ}

/-- **`π_*(q(m))` is surjective once it is on fibres.** -/
theorem epi_pushforward_twistMap_quotientπ_of_fibres {T : Scheme.{u}}
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T)
    (hF : ∀ t : T, IsIso ((baseChangeNatTrans
      (isPullback_projectiveSpaceOverMap n (T.fromSpecResidueField t)).w).app
        (twist (regularityIndex.{u} n r hr P : ℤ) (freeModule n r T))))
    (hfib : ∀ t : T, Epi ((Scheme.Modules.pushforward
      (projectiveSpaceOver n (Spec (T.residueField t)) ↘ Spec (T.residueField t))).map
        ((Scheme.Modules.pullback (fibreMap n t)).map
          (twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K))))) :
    Epi ((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).map
      (twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K))) := by
  have hlf := isFiniteLocallyFreeOfRank_pushforward_twist_quotient hr hK
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).obj
      (twist (regularityIndex.{u} n r hr P : ℤ) (quotient K)))
    ⌊P.eval ((regularityIndex.{u} n r hr P : ℕ) : ℚ)⌋₊
  refine Scheme.Modules.epi_of_forall_epi_pullback_fromSpecResidueField _
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree _) fun t => ?_
  have hsq := isPullback_projectiveSpaceOverMap n (T.fromSpecResidueField t)
  have hQ := isIso_baseChangeNatTrans_twist_quotient hr hK _ _ _ hsq
  have hnat : (Scheme.Modules.pullback (T.fromSpecResidueField t)).map
        ((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).map
          (twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K))) ≫
        (baseChangeNatTrans hsq.w).app
          (twist (regularityIndex.{u} n r hr P : ℤ) (quotient K)) =
      (baseChangeNatTrans hsq.w).app
          (twist (regularityIndex.{u} n r hr P : ℤ) (freeModule n r T)) ≫
        (Scheme.Modules.pushforward
          (projectiveSpaceOver n (Spec (T.residueField t)) ↘ Spec (T.residueField t))).map
          ((Scheme.Modules.pullback (fibreMap n t)).map
            (twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K))) :=
    (baseChangeNatTrans hsq.w).naturality
      (twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K))
  set b := (baseChangeNatTrans hsq.w).app
    (twist (regularityIndex.{u} n r hr P : ℤ) (quotient K)) with hb
  set a := (Scheme.Modules.pullback (T.fromSpecResidueField t)).map
    ((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).map
      (twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K))) with ha
  have hcomp : Epi (a ≫ b) := by
    rw [hnat]
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (hF t)) _ (hfib t)
  exact (@epi_comp_iff_of_isIso _ _ _ _ _ a b hQ).mp hcomp

end AlgebraicGeometry.ProjectiveQuot

end

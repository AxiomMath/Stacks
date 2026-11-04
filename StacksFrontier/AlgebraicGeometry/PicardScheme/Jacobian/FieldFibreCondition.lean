module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism

/-!
# The condition of Stacks 0B9V over a field

Over the spectrum of a field `K`, the condition "`Rg_*ℱ` is a finite locally free module of
rank `r` placed in degree `i`" of [Stacks, Tag 0B9S] holds as soon as the cohomology of `ℱ` has
dimension `r` in degree `i` and vanishes in every other degree. This is how the source reads the
condition of [Stacks, Tag 0B9V] on a field-valued point, in the proofs of
[Stacks, Tag 0B9X] and [Stacks, Tag 0B9Z]: there `ℒ` is in `F(Spec K)` when
`H⁰(X_K, ℒ) = K` and `H¹(X_K, ℒ) = 0`.

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.hasDerivedPushforwardRank_of_finrank` —
  the criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The condition of [Stacks, Tag 0B9S] over a field, from the cohomology.** Let `g : Y ⟶ Spec K`
be proper and of finite presentation and `ℱ` an `𝒪_Y`-module of finite presentation, flat over
`K`. If `dim_K Hⁱ(Y, ℱ) = r` and `dim_K Hʲ(Y, ℱ) = 0` for every `j ≠ i` with `j ≥ 0`, then
`Rg_*ℱ` is a finite locally free module of rank `r` placed in degree `i`. -/
theorem hasDerivedPushforwardRank_of_finrank (K : Type u) [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (hfp : FinitePresentation g) [IsProper g] (F : Y.Modules)
    (hF : F.IsFinitePresentation) (hflat : IsFlatOver g.toLRSHom.toShHom F) (i : ℕ) (r : ℕ)
    (hi : Module.finrank K (cohomologyOverField K g F i) = r)
    (hj : ∀ j : ℕ, j ≠ i → Module.finrank K (cohomologyOverField K g F j) = 0) :
    HasDerivedPushforwardRank g F i r := by
  have hperf := perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward g hfp
    inferInstance F hF hflat
  have hpc := DerivedFibreBetti.isPseudoCoherent_of_isPerfect _ hperf
  set E := derivedPushforwardModule g F
  set U := Scheme.Modules.singleDegreeRankOpen E (i : ℤ) r
  have hU : ∀ pt : Spec (.of K), pt ∈ U := by
    intro pt
    rw [Scheme.Modules.mem_singleDegreeRankOpen_iff E (i : ℤ) r hperf pt]
    intro j
    have hb := DerivedFibreBetti.derivedFiberBetti_apply (Spec (.of K)) E hpc j pt
    rw [← hb]
    rcases lt_or_ge j 0 with hneg | hnn
    · rw [DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule_of_neg K g F hpc hneg,
        ite_eq_right (by omega)]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
      rw [DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule K g F hpc n]
      by_cases hn : n = i
      · subst hn; rw [ite_eq_left rfl, hi]
      · rw [ite_eq_right (by exact_mod_cast hn), hj n hn]
  have hfac : ∃ h : Spec (.of K) ⟶ U.toScheme, h ≫ U.ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift U.ι (𝟙 _) (by rintro _ ⟨pt, rfl⟩; simpa using hU pt),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    (Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback E (i : ℤ) r hperf
      (𝟙 _)).1 hfac
  exact ⟨M, hM, ⟨((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso _).app E).symm ≪≫
    e⟩⟩

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end

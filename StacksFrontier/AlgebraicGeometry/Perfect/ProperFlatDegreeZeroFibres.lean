module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.FibreBettiNumbersCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.Assembly
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal

/-!
# A flat family whose fibres have cohomology in degree zero only

Let `π : Y ⟶ T` be proper and of finite presentation and `ℱ` an `𝒪_Y`-module of finite
presentation, flat over `T`. Suppose that on the fibre over every point `t ∈ T` the cohomology of
`ℱ_t` vanishes in positive degrees and is `d`-dimensional in degree zero. Then for every base
change `π' : Y' ⟶ T'` of `π`, the derived direct image `Rπ'_* ℱ'` is a finite locally free
`𝒪_{T'}`-module of rank `d` placed in degree zero.

This is the form of cohomology and base change ([Stacks, Tag 0B91], [Stacks, Tag 0BDK],
[Stacks, Tag 0BDN]) in which the proof of [Stacks, Tag 0DPA] uses it, for the twists `𝒬(m)` of a
flat family of quotients with Hilbert polynomial `P`.

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.fibreBetti_eq_finrank_cohomologyOverField`:
  the Betti number `β_j(t)` of the family is `dim_{κ(t)} H^j(Y_t, ℱ_t)`, computed on any cartesian
  square over `Spec κ(t) ⟶ T`.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.hasDerivedPushforwardRank_zero_of_fibres`:
  the statement above.

## Implementation notes

The open of [Stacks, Tag 0BDK] for the perfect object `Rπ_* ℱ` ([Stacks, Tag 0B91]), degree `0`
and rank `d` contains every point, by its pointwise description through the derived fibres and the
identification of these with the cohomology of the fibres ([Stacks, Tag 0BDN]). Every morphism
`T' ⟶ T` therefore factors through it, and the base change of `Rπ_* ℱ` is `Rπ'_* ℱ'`.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- **The Betti numbers of a flat family are the dimensions of the cohomology of its fibres**,
computed on any cartesian square over `Spec κ(t) ⟶ T`. -/
theorem fibreBetti_eq_finrank_cohomologyOverField {Y T : Scheme.{u}} {π : Y ⟶ T} {F : Y.Modules}
    (h : FibreBetti.IsFlatFamily π F) (t : T) {Yt : Scheme.{u}}
    (πt : Yt ⟶ Spec (T.residueField t)) (ιt : Yt ⟶ Y)
    (hsq : IsPullback ιt πt π (T.fromSpecResidueField t)) (j : ℕ) :
    FibreBetti.fibreBetti π F j t =
      Module.finrank (T.residueField t)
        (cohomologyOverField (T.residueField t) πt ((Scheme.Modules.pullback ιt).obj F) j) := by
  let pt : Spec (T.residueField t) := IsLocalRing.closedPoint _
  have hpb := congrFun (FibreBetti.fibreBetti_pullback hsq h (j : ℤ)) pt
  simp only [Function.comp_apply, Scheme.fromSpecResidueField_apply] at hpb
  rw [← hpb, FibreBetti.fibreBetti_eq_derivedFiberBetti (FibreBetti.isFlatFamily_pullback hsq h)]
  exact DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule (T.residueField t) πt
    ((Scheme.Modules.pullback ιt).obj F) _ j pt

/-- **The Betti numbers of a flat family vanish in negative degrees.** -/
theorem fibreBetti_eq_zero_of_neg {Y T : Scheme.{u}} {π : Y ⟶ T} {F : Y.Modules}
    (h : FibreBetti.IsFlatFamily π F) (t : T) {Yt : Scheme.{u}}
    (πt : Yt ⟶ Spec (T.residueField t)) (ιt : Yt ⟶ Y)
    (hsq : IsPullback ιt πt π (T.fromSpecResidueField t)) {j : ℤ} (hj : j < 0) :
    FibreBetti.fibreBetti π F j t = 0 := by
  let pt : Spec (T.residueField t) := IsLocalRing.closedPoint _
  have hpb := congrFun (FibreBetti.fibreBetti_pullback hsq h j) pt
  simp only [Function.comp_apply, Scheme.fromSpecResidueField_apply] at hpb
  rw [← hpb, FibreBetti.fibreBetti_eq_derivedFiberBetti (FibreBetti.isFlatFamily_pullback hsq h)]
  exact DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule_of_neg (T.residueField t)
    πt ((Scheme.Modules.pullback ιt).obj F) _ hj pt

/-- **Cohomology and base change in degree zero.** Let `π : Y ⟶ T` be proper and of finite
presentation and `ℱ` of finite presentation and flat over `T`. If on the fibre over every point
`t ∈ T` the cohomology of `ℱ_t` has dimension `d` in degree `0` and vanishes in positive degrees,
then for every base change `π' : Y' ⟶ T'` of `π` along any `h : T' ⟶ T`, `Rπ'_* ℱ'` is a finite
locally free `𝒪_{T'}`-module of rank `d` placed in degree `0`. -/
theorem hasDerivedPushforwardRank_zero_of_fibres {Y T : Scheme.{u}} (π : Y ⟶ T)
    (hfp : FinitePresentation π) [IsProper π] (F : Y.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver π.toLRSHom.toShHom F) (d : ℕ)
    (hfib : ∀ t : T, ∃ (Yt : Scheme.{u}) (πt : Yt ⟶ Spec (T.residueField t)) (ιt : Yt ⟶ Y),
      IsPullback ιt πt π (T.fromSpecResidueField t) ∧
        Module.finrank (T.residueField t)
          (cohomologyOverField (T.residueField t) πt ((Scheme.Modules.pullback ιt).obj F) 0) = d ∧
        ∀ j : ℕ, 0 < j → Module.finrank (T.residueField t)
          (cohomologyOverField (T.residueField t) πt ((Scheme.Modules.pullback ιt).obj F) j) = 0)
    {Y' T' : Scheme.{u}} (h : T' ⟶ T) (π' : Y' ⟶ T') (h' : Y' ⟶ Y)
    (hsq : IsPullback h' π' π h) :
    HasDerivedPushforwardRank π' ((Scheme.Modules.pullback h').obj F) 0 d := by
  have hfam : FibreBetti.IsFlatFamily π F := ⟨hfp, inferInstance, hF, hflat⟩
  have hperf := perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward π hfp
    inferInstance F hF hflat
  have htop : Scheme.Modules.singleDegreeRankOpen (derivedPushforwardModule π F) 0 d = ⊤ := by
    refine eq_top_iff.mpr fun t _ => ?_
    refine (Scheme.Modules.mem_singleDegreeRankOpen_iff _ 0 d hperf t).mpr fun j => ?_
    obtain ⟨Yt, πt, ιt, hsqt, h0, hpos⟩ := hfib t
    have hβ := congrFun (FibreBetti.fibreBetti_eq_derivedFiberBetti hfam j) t
    rw [DerivedFibreBetti.derivedFiberBetti_apply] at hβ
    refine hβ.symm.trans ?_
    rcases lt_or_ge j 0 with hj | hj
    · rw [ite_eq_right hj.ne, fibreBetti_eq_zero_of_neg hfam t πt ιt hsqt hj]
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      rw [fibreBetti_eq_finrank_cohomologyOverField hfam t πt ιt hsqt k]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [h0]
        simp
      · rw [hpos k hk, ite_eq_right (by omega)]
  have hrange : Set.range h.base ⊆
      Set.range
        (Scheme.Modules.singleDegreeRankOpen (derivedPushforwardModule π F) 0 d).ι.base := by
    rw [Scheme.Opens.range_ι, htop]
    exact fun _ _ => trivial
  obtain ⟨M, hM, ⟨e⟩⟩ := (Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback
    _ 0 d hperf h).mp ⟨IsOpenImmersion.lift _ h hrange, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨e'⟩ := baseChangeDerivedPushforward π h π' h' hsq hfp inferInstance F hF hflat
  exact ⟨M, hM, ⟨e'.symm ≪≫ e⟩⟩

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end

module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcess
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.Chow.BlowupExceptionalBundle
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TautologicalKernelTopChern
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.ConormalRank

/-!
# The degree of `c_{r-1}(𝓕^∨) ∩ [E]` on the fibres of the exceptional divisor

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`, of dimensions `e < n`,
`b : X' ⟶ X` the blowing up of `X` in `Z`, `j : E ⟶ X'` the exceptional divisor and `π : E ⟶ Z`,
and `𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})` the sheaf of Tag 0FVA, of rank `r - 1` for `r = n - e`.
This file proves

  `π_*(c_{r-1}(𝓕^∨) ∩ [E]) = [Z]`   in `CH_e(Z)`,

the computation the proof of [Stacks, Tag 0FIH] omits ("it suffices to prove that the degree of
the codimension `r - 1` cycle `(-1)^{r-1} c_{r-1}(𝓕) ∩ [E]` on the fibres of `π` is `1`").

## The proof

By Stacks 0FUT the exceptional divisor is the projective bundle `𝐏(𝒞_{Z/X})` over `Z` with
`𝒪(1) = 𝒪_{X'}(-E)|_E = 𝒞_{E/X'}`, a projective tower of fibre dimension `r - 1` locally on `Z`
(`Stacks.AlgebraicGeometry.isLocallyProjectiveTower_pullbackSnd_blowUpToBase`), and the excess
conormal sequence `0 ⟶ 𝓕 ⟶ π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'} ⟶ 0` is its tautological sequence. So
`Stacks.Chow.GenuineChern.pushforward_chernFamily_dualKernel_bundlePullback` (Stacks 02UI, 02U8 and
02TW) gives `π_*(c_{r-1}(𝓕^∨) ∩ π^*β) = β` for every `β`, and `π^*[Z] = [E]` (`π` flat of relative
dimension `r - 1`).

## Main results

* `Stacks.Chow.chowCohomologyCap_totalChernOfFiniteLocallyFree_heq`: the cap product with a
  component of the total Chern class of Stacks 0ESW is the Chern class cap product of Stacks 02U6.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.isLocallyProjectiveTower_exceptionalConormal`:
  `(π, 𝒞_{E/X'})` is a projective tower of fibre dimension `r - 1` locally on `Z`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.properChowPushforward_excessChernCap`:
  **`π_*(c_{r-1}(𝓕^∨) ∩ [E]) = [Z]`.**

## References

* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

/-- **The cap product with the `s`-th component of the total Chern class of Stacks 0ESW is the
Chern class cap product `c_s(ℰ) ∩ -` of Stacks 02U6**, for `ℰ` of constant rank `s`. -/
theorem chowCohomologyCap_totalChernOfFiniteLocallyFree_heq (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] (k : ℤ)
    (x : chowGroup C sX k) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX s (totalChernOfFiniteLocallyFree C sX F s)
        k x ≍ GenuineChern.chernFamily C sX F s k s x := by
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sX s _ k x).trans ?_
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F s (𝟙 X)
  show (totalChernOfFiniteLocallyFree C sX F).op (𝟙 X) k s
    (chowGroupCongr C (Category.id_comp sX).symm k x) ≍ _
  rw [op_totalChernOfFiniteLocallyFree_of_rank C sX F (𝟙 X) s]
  have key : ∀ {q : X ⟶ C.S} [LocallyOfFiniteType q] (hq : q = sX) (G : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s] (_ : G ≅ F)
      (y : chowGroup C q k), y ≍ x →
        GenuineChern.chernFamily C q G s k s y ≍ GenuineChern.chernFamily C sX F s k s x := by
    intro q _ hq G _ eG y hy
    subst hq
    rw [eq_of_heq hy, GenuineChern.chernFamily_congr C q F s eG rfl]
  exact key (Category.id_comp sX) _ ((Scheme.Modules.pullbackId X).app F) _
    (chowGroupCongr_heq C _ k x)

end Stacks.Chow

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open Stacks.Chow
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- The projection `π : E ⟶ Z` of the exceptional divisor is proper. -/
instance isProper_exceptionalProj : IsProper (exceptionalProj i).hom.left := by
  have : IsProper ((exceptionalProj i).hom.left ≫ Z.obj.hom) :=
    inferInstanceAs (IsProper (exceptionalObj i).obj.hom)
  exact IsProper.of_comp _ Z.obj.hom

variable {n e : ℕ} (hX : RelativeDimension X.obj.hom n) (hZ : RelativeDimension Z.obj.hom e)

/-- A sheaf locally free of rank `n - e` is locally free of rank `n - e - 1 + 1` when `e < n`. -/
private theorem isFiniteLocallyFreeOfRank_sub_one_add_one {Y : Scheme.{u}} {G : Y.Modules}
    (he : e < n)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (n - e)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (n - e - 1 + 1) := by
  rwa [show n - e - 1 + 1 = n - e by omega]

include hX hZ in
/-- **The exceptional divisor with `𝒞_{E/X'}` is a projective tower over the centre**, of fibre
dimension `r - 1` for `r = n - e` the codimension of the centre, locally on `Z`. -/
theorem isLocallyProjectiveTower_exceptionalConormal (he : e < n) :
    IsLocallyProjectiveTower (n - e - 1) (exceptionalProj i).hom.left (exceptionalConormal i) := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have hinv : inv i.hom.left.toImage ≫ i.hom.left = i.hom.left.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr (Scheme.Hom.toImage_imageι _).symm
  have : Smooth (i.hom.left.ker.subschemeι ≫ X.obj.hom) := by
    rw [← hinv, Category.assoc]
    infer_instance
  have hZ' : RelativeDimension (i.hom.left ≫ X.obj.hom) e := by
    have key : ∀ (q : Z.obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q], q = Z.obj.hom →
        RelativeDimension q e := by
      rintro q _ rfl; exact hZ
    exact key _ (Over.w i.hom)
  have hZ'' : RelativeDimension (i.hom.left.ker.subschemeι ≫ X.obj.hom) e :=
    RelativeDimension.of_isPullback (IsPullback.of_horiz_isIso (fst := inv i.hom.left.toImage)
      (g := 𝟙 _) ⟨by rw [← hinv]; simp⟩) hZ'
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne i.hom.left.ker.subschemeι) (n - e - 1 + 1) := by
    exact isFiniteLocallyFreeOfRank_sub_one_add_one he
      (Stacks.ConormalSequenceRight.isFiniteLocallyFreeOfRank_conormalSheafDegreeOne
        i.hom.left.ker.subschemeι X.obj.hom hX hZ'')
  exact (Stacks.AlgebraicGeometry.isLocallyProjectiveTower_pullbackSnd_blowUpToBase X.obj.hom
    i.hom.left (n - e - 1)).of_iso_module (exceptionalConormalIso i)

include hX hZ in
/-- **`π_*(c_{r-1}(𝓕^∨) ∩ [E]) = [Z]`** in `CH_e(Z)`, for `r = n - e` the codimension of the
centre: the cycle `c_{r-1}(𝓕^∨) ∩ [E]` of Lemma 0FIH (`excessChernCap`, with `[E]` in dimension
`n - 1`) pushes forward to the fundamental class of `Z`. -/
theorem properChowPushforward_excessChernCap (he : e < n) :
    properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
        (exceptionalProj i).hom.left rfl (e : ℤ)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
          (exceptionalObj i).obj.hom Z.obj.hom (exceptionalProj i).hom.left rfl _)
        (chowGroupCast (fieldChowSituation k) _ (by omega)
          (excessChernCap i (n - e) ((n : ℤ) - 1))) =
      fundamentalChowClass (fieldChowSituation k) Z.obj.hom e := by
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (excessConormal i) (n - e - 1) := isFiniteLocallyFreeOfRank_excessConormal i hX hZ he
  have hFd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    (excessConormal i) (n - e - 1) hF
  have h𝒞 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (centreConormal i) (n - e - 1 + 1) := by
    exact isFiniteLocallyFreeOfRank_sub_one_add_one he
      (isFiniteLocallyFreeOfRank_centreConormal i hX hZ)
  have hM := isInvertible_exceptionalConormal i
  have hπ : RelativeDimension (exceptionalProj i).hom.left (n - e - 1) := by
    have h := relativeDimension_exceptionalProj i hX hZ
    rwa [show n - 1 - e = n - e - 1 by omega] at h
  have htower := isLocallyProjectiveTower_exceptionalConormal i hX hZ he
  have key := GenuineChern.pushforward_chernFamily_dualKernel_bundlePullback
    (fieldChowSituation k) Z.obj.hom (exceptionalObj i).obj.hom (exceptionalProj i).hom.left rfl
    (n - e - 1) hπ (centreConormal i) (excessShortComplex i) (excessShortComplex_shortExact i)
    (hF := hF) (hM := hM) (excessShortComplexX₂Iso i) htower e
    (fundamentalChowClass (fieldChowSituation k) Z.obj.hom e)
  have hpull : bundlePullback (fieldChowSituation k) Z.obj.hom (exceptionalObj i).obj.hom
      (exceptionalProj i).hom.left rfl (n - e - 1) hπ e
        (fundamentalChowClass (fieldChowSituation k) Z.obj.hom e) =
      fundamentalChowClass (fieldChowSituation k) (exceptionalObj i).obj.hom
        (e + ((n - e - 1 : ℕ) : ℤ)) :=
    flatPullbackChow_fundamentalChowClass (fieldChowSituation k) _ _ _ rfl _ hπ e _
      (schemeDeltaDimension_le_of_relativeDimension Z.obj.hom hZ)
  rw [hpull] at key
  refine Eq.trans ?_ key
  congr 1
  refine eq_of_heq ((chowGroupCast_heq _ _ _ _).trans
    (HEq.trans ?_ (chowGroupCast_heq _ _ _ _).symm))
  refine (chowCohomologyCap_totalChernOfFiniteLocallyFree_heq (fieldChowSituation k)
    (exceptionalObj i).obj.hom (dualSheaf (excessConormal i)) (n - e - 1) _ _).trans ?_
  exact Stacks.Chow.heq_apply_of_degree (fieldChowSituation k) (exceptionalObj i).obj.hom
    (exceptionalObj i).obj.hom (fun d => d) (fun d => d - ((n - e - 1 : ℕ) : ℤ))
    (fun d => GenuineChern.chernFamily (fieldChowSituation k) (exceptionalObj i).obj.hom
      (dualSheaf (excessConormal i)) (n - e - 1) d (n - e - 1)) (by omega)
    (congr_arg_heq (fun d => fundamentalChowClass (fieldChowSituation k)
      (exceptionalObj i).obj.hom d) (by omega))

end Stacks.WeilCohomology.SmoothProjectiveScheme

end

module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.SplitStep
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchChowInjective

/-!
# The zero section formula descends from the projective bundle

Let `ℰ` be finite locally free of rank `n + 1` on `X` and `π : P = 𝐏(ℰ) ⟶ X` its projective
bundle. If the zero section formula holds for `π^*ℰ` on `P`, it holds for `ℰ` on `X`: the vector
bundle `𝐕((π^*ℰ)^∨)` is `𝐕(ℰ^∨) ×_X P`, so the zero section of `𝐕((π^*ℰ)^∨)` is the base change
of that of `𝐕(ℰ^∨)` (Stacks 02RG), the Chern classes commute with `π^*` (Stacks 02U8), and the
projection `π_V : 𝐕((π^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)` is the projective bundle of the pullback of `ℰ` to
`𝐕(ℰ^∨)`, so `π_V^*` is injective on Chow groups (Stacks 02TX).

## Main results

* `Stacks.Chow.zeroSectionFormula_of_bundle` — the descent.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) (n : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- The pullback `g^*F` of a finite locally free module `F` of rank `r` is finite locally free of
rank `r`. -/
instance isFiniteLocallyFreeOfRank_pullback_obj'' {T : Scheme.{u}} (g : T ⟶ X) (F : X.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj F) r :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r

omit [LocallyOfFiniteType sX]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] in
/-- The projection `π_V : 𝐕((π^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)` lies over `π`. -/
theorem dualBundleBaseChangeMap_comp_base {T : Scheme.{u}} (g : T ⟶ X) :
    dualBundleBaseChangeMap g E ≫ dualVectorBundleToBase E ≫ sX =
      dualVectorBundleToBase ((Scheme.Modules.pullback g).obj E) ≫ g ≫ sX := by
  rw [← Category.assoc, (isPullback_dualBundleBaseChangeMap g E).w, Category.assoc]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] in
/-- If `g : T ⟶ X` is locally of finite type, so is the projection `𝐕((g^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)`. -/
theorem locallyOfFiniteType_dualBundleBaseChangeMap {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] : LocallyOfFiniteType (dualBundleBaseChangeMap g E) :=
  MorphismProperty.of_isPullback (isPullback_dualBundleBaseChangeMap g E).flip inferInstance

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] in
/-- If `g : T ⟶ X` is flat, so is the projection `𝐕((g^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)`. -/
theorem flat_dualBundleBaseChangeMap {T : Scheme.{u}} (g : T ⟶ X) [Flat g] :
    Flat (dualBundleBaseChangeMap g E) :=
  MorphismProperty.of_isPullback (isPullback_dualBundleBaseChangeMap g E).flip inferInstance

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] in
/-- If `g : T ⟶ X` has relative dimension `r`, so does the projection `𝐕((g^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)`. -/
theorem relativeDimension_dualBundleBaseChangeMap {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (r : ℕ) (hg : AlgebraicGeometry.RelativeDimension g r) :
    haveI := locallyOfFiniteType_dualBundleBaseChangeMap E g
    AlgebraicGeometry.RelativeDimension (dualBundleBaseChangeMap g E) r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback
    (isPullback_dualBundleBaseChangeMap g E).flip hg

/-- **The projection `𝐕((π^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)` has injective flat pullback**: it is the projective
bundle of the pullback of `ℰ` to `𝐕(ℰ^∨)`, up to isomorphism, and pullback to a projective bundle
is injective (Stacks 02TX). -/
theorem dualBundleBaseChangeMap_bundleProj_injective (k : ℤ) :
    haveI := flat_bundleProj E n
    haveI := locallyOfFiniteType_bundleProj E n
    haveI := locallyOfFiniteType_dualBundleBaseChangeMap E (bundleProj E)
    haveI := flat_dualBundleBaseChangeMap E (bundleProj E)
    Function.Injective (flatPullbackChowOfRelativeDimension C
      (dualVectorBundleToBase ((Scheme.Modules.pullback (bundleProj E)).obj E) ≫ bundleProj E ≫ sX)
      (dualVectorBundleToBase E ≫ sX) (dualBundleBaseChangeMap (bundleProj E) E)
      (dualBundleBaseChangeMap_comp_base C sX E (bundleProj E)) n
      (relativeDimension_dualBundleBaseChangeMap E (bundleProj E) n
        (relativeDimension_bundleProj E n)) k) := by
  have := flat_bundleProj E n
  have := locallyOfFiniteType_bundleProj E n
  have := locallyOfFiniteType_dualBundleBaseChangeMap E (bundleProj E)
  have := flat_dualBundleBaseChangeMap E (bundleProj E)
  let pE := dualVectorBundleToBase E
  let G := (Scheme.Modules.pullback pE).obj E
  have := flat_bundleProj G n
  have := locallyOfFiniteType_bundleProj G n
  have hV := isPullback_dualBundleBaseChangeMap (bundleProj E) E
  obtain ⟨e, he, -⟩ := GenuineChern.bundleBaseChangeHolds pE E G (Iso.refl _)
  let φ := hV.isoPullback ≪≫ e.symm
  have hφ : φ.hom ≫ bundleProj G = dualBundleBaseChangeMap (bundleProj E) E := by
    simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he, Iso.inv_hom_id_assoc]
    exact hV.isoPullback_hom_fst
  have hq := GenuineChern.pullback_injective (sX := pE ≫ sX) G (GenuineChern.topHalf C) n k
  exact flatPullbackChow_injective_of_isIso_comp C _ (bundleProj G ≫ pE ≫ sX) _ φ.hom
    (bundleProj G) _ hφ (by rw [← Category.assoc, hφ, dualBundleBaseChangeMap_comp_base]) rfl _
    n (relativeDimension_bundleProj G n) _ k (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) _ hq

/-- Pulled back along `π_V : 𝐕((π^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)`, the two sides of the zero section formula
for `ℰ` agree, given the formula for `π^*ℰ`. -/
private theorem dualBundleBaseChangeMap_flatPullback_zeroSectionFormula_heq
    (hP : ZeroSectionFormula C (bundleProj E ≫ sX) ((Scheme.Modules.pullback (bundleProj E)).obj E)
      (n + 1)) (k : ℤ) (α : chowGroup C sX k) :
    haveI := flat_bundleProj E n
    haveI := locallyOfFiniteType_bundleProj E n
    haveI := locallyOfFiniteType_dualBundleBaseChangeMap E (bundleProj E)
    haveI := flat_dualBundleBaseChangeMap E (bundleProj E)
    flatPullbackChow C _ _ (dualBundleBaseChangeMap (bundleProj E) E)
        (dualBundleBaseChangeMap_comp_base C sX E (bundleProj E)) n
        (relativeDimension_dualBundleBaseChangeMap E (bundleProj E) n
          (relativeDimension_bundleProj E n)) k
        (flatPullbackDescends C _ _ _ _ _ _ _) (dualZeroSectionPushforward C sX E k α) ≍
      flatPullbackChow C _ _ (dualBundleBaseChangeMap (bundleProj E) E)
        (dualBundleBaseChangeMap_comp_base C sX E (bundleProj E)) n
        (relativeDimension_dualBundleBaseChangeMap E (bundleProj E) n
          (relativeDimension_bundleProj E n))
        (k - ((n + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ)) (flatPullbackDescends C _ _ _ _ _ _ _)
        (dualBundlePullback C sX E (n + 1) (k - ((n + 1 : ℕ) : ℤ))
          (GenuineChern.chernCap C (n + 1) sX E k (Fin.last (n + 1)) α)) := by
  have := flat_bundleProj E n
  have := locallyOfFiniteType_bundleProj E n
  have := locallyOfFiniteType_dualBundleBaseChangeMap E (bundleProj E)
  have := flat_dualBundleBaseChangeMap E (bundleProj E)
  have := locallyOfFiniteType_dualVectorBundleToBase E (n + 1)
  have := flat_dualVectorBundleToBase E (n + 1)
  have := locallyOfFiniteType_dualVectorBundleToBase
    ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1)
  have := flat_dualVectorBundleToBase ((Scheme.Modules.pullback (bundleProj E)).obj E) (n + 1)
  have hπ := relativeDimension_bundleProj E n
  have hΦ := relativeDimension_dualBundleBaseChangeMap E (bundleProj E) n hπ
  have hg := dualBundleBaseChangeMap_comp_base C sX E (bundleProj E)
  -- Stacks 02RG for the zero sections
  have e1 := flatPullbackChow_properChowPushforward_unconditional C sX
    (dualVectorBundleToBase E ≫ sX) (bundleProj E ≫ sX)
    (dualVectorBundleToBase ((Scheme.Modules.pullback (bundleProj E)).obj E) ≫ bundleProj E ≫ sX)
    (dualVectorBundleZeroSection E) (dualBundleBaseChangeMap (bundleProj E) E) (bundleProj E)
    (dualVectorBundleZeroSection ((Scheme.Modules.pullback (bundleProj E)).obj E))
    (isPullback_dualVectorBundleZeroSection_dualBundleBaseChangeMap (bundleProj E) E)
    (dualVectorBundleZeroSection_comp_base C sX E) hg rfl n hΦ k α
  set γ := GenuineChern.chernCap C (n + 1) sX E k (Fin.last (n + 1)) α
  -- the formula on the projective bundle, and Stacks 02U8
  refine (heq_of_eq e1).trans ?_
  refine (hP (k + n) _).trans ?_
  have e3 := GenuineChern.chernCap_flatPullback_heq C sX (bundleProj E ≫ sX) (bundleProj E) rfl
    n hπ E (n + 1) ((Scheme.Modules.pullback (bundleProj E)).obj E) (Iso.refl _) k
    (Fin.last (n + 1)) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) α
  refine (flatPullbackChow_heq_of_degree C _ _ _ rfl (n + 1)
    (relativeDimension_dualVectorBundleToBase _ (n + 1)) (by simp; omega)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) e3).trans ?_
  refine (flatPullbackChow_comp C _ (bundleProj E ≫ sX) sX _ (bundleProj E) rfl rfl (n + 1) n
    (relativeDimension_dualVectorBundleToBase _ (n + 1)) hπ (k - ((n + 1 : ℕ) : ℤ))
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) γ).trans ?_
  refine HEq.trans ?_ (flatPullbackChow_comp C _ (dualVectorBundleToBase E ≫ sX) sX
    (dualBundleBaseChangeMap (bundleProj E) E) (dualVectorBundleToBase E) hg rfl n (n + 1) hΦ
    (relativeDimension_dualVectorBundleToBase E (n + 1)) (k - ((n + 1 : ℕ) : ℤ))
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) γ).symm
  exact flatPullbackChow_heq_congr C _ sX _ _ _ _
    (isPullback_dualBundleBaseChangeMap (bundleProj E) E).w.symm (by omega) _ _ rfl _ _ _ _ HEq.rfl

/-- **The zero section formula descends from the projective bundle**: if it holds for `π^*ℰ` on
`𝐏(ℰ)`, it holds for `ℰ` on `X`. -/
theorem zeroSectionFormula_of_bundle
    (hP : ZeroSectionFormula C (bundleProj E ≫ sX) ((Scheme.Modules.pullback (bundleProj E)).obj E)
      (n + 1)) :
    ZeroSectionFormula C sX E (n + 1) := by
  intro k α
  have := flat_bundleProj E n
  have := locallyOfFiniteType_bundleProj E n
  have := locallyOfFiniteType_dualBundleBaseChangeMap E (bundleProj E)
  have := flat_dualBundleBaseChangeMap E (bundleProj E)
  -- injectivity of the pullback to `𝐕((π^*ℰ)^∨)`
  rw [dualBundleBaseChangeMap_bundleProj_injective C sX E n k <| eq_of_heq <|
    (dualBundleBaseChangeMap_flatPullback_zeroSectionFormula_heq C sX E n hP k α).trans
      (flatPullbackChow_heq_of_degree C _ _ _ _ n _ (by omega)
        (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
        (chowGroupCast_heq C _ (show k - ((n + 1 : ℕ) : ℤ) + ((n + 1 : ℕ) : ℤ) = k by omega)
          _).symm)]
  exact chowGroupCast_heq C _ _ _

end Stacks.Chow

end

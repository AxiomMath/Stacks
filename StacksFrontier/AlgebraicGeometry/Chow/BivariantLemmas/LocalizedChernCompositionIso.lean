module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionReduction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalConeFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Conormal.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology

/-!
# Stacks 0FEC: the case `Y = X`

The proof of Stacks 0FEC first treats the case `Y = X`, on the fundamental class of an integral
scheme `X`:

  `c(Z ⟶ Y, 𝒩') ∩ c(Y ⟶ X, 𝒩'') ∩ [X] = c(Z ⟶ Y, 𝒩') ∩ c_top(𝒩'') ∩ [Y]
      = c_top(𝒩''|_Z) ∩ c(Z ⟶ Y, 𝒩') ∩ [Y] = c(Z ⟶ X, 𝒩) ∩ [X]`,

by Stacks 0FBL twice and Stacks 02UA. Here `Y ⟶ X` is a closed immersion which is an isomorphism,
`Stacks.Chow.CompositionIsoCase`.

An isomorphism is a regular immersion with vanishing conormal sheaf, so the splitting off of the
excess normal sheaf (`Stacks.Chow.ConormalCompatibleVirtualNormalBundles.excessReduction`, which
packages the two uses of Stacks 0FBL and the use of Stacks 02UA) reduces the case to
`𝒩'' = 𝒞_{Y/X}^∨ = 0`, where the top row of the datum identifies `𝒩₁^∨` with `(𝒩')^∨`. What is
left is the identification of `Y` with `X`:

* `c(Y ⟶ X, 0) ∩ [X] = [Y]` (Stacks 0FBM for the regular immersion `Y ⟶ X` of codimension `0`);
* `c(Z ⟶ X, 𝒩₁) ∩ [X]` is `c(Z ⟶ X, 𝒩₁) ∩ [Y]` on the test scheme `Y ⟶ X` (Stacks 0B76 (1)
  along the isomorphism `Y ⟶ X`), which is `c(Z ⟶ Y, 𝒩₁|_Z) ∩ [Y]` (the base-change clause of
  Stacks 0FBK for the cartesian square `Z = Z ×_X Y`), and `𝒩₁|_Z ≅ 𝒩'` compatibly with the
  surjections onto `𝒞_{Z/Y}` (`Stacks.Chow.virtualNormalGysinClass_eq_of_dualIso`).

## Main results

* `Stacks.Chow.compositionIsoCase` — **the case `Y = X` of the proof of Stacks 0FEC**.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

section Core

variable (C : ChowSituation.{u}) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {i : Z ⟶ Y} {j : Y ⟶ X} [IsClosedImmersion i] [IsClosedImmersion j] [IsIso j]
  (hi : i ≫ sY = sZ) (hj : j ≫ sX = sY) [IsLocallyNoetherian Y]

omit [IsClosedImmersion i] [IsClosedImmersion j] [IsLocallyNoetherian Y] in
/-- The square `Z = Z ×_X Y` of a closed immersion `i : Z ⟶ Y` over an isomorphism
`j : Y ⟶ X`. -/
theorem isPullback_id_of_isIso : IsPullback i (𝟙 Z) j (i ≫ j) :=
  IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]⟩

/-- **The core of the case `Y = X`.** Let `j : Y ⟶ X` be an isomorphism, `𝒩₁` a virtual normal
bundle for `i ≫ j` of rank `p` and `𝒩'` one for `i` of rank `p`, with `𝒩₁^∨ ≅ (𝒩')^∨`
compatibly with the surjections and the map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the conormal sequence. Then on
the fundamental class of `X`

  `c(Z ⟶ X, 𝒩₁) ∩ [X]_n = c(Z ⟶ Y, 𝒩') ∩ c(Y ⟶ X, 𝒞_{Y/X}^∨) ∩ [X]_n`

for `dim_δ X ≤ n`. -/
theorem virtualNormalGysinClass_cap_fundamentalChowClass_heq_of_isIso
    (hreg : IsRegularImmersion j)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) 0]
    (𝒩₁ : VirtualNormalBundle (i ≫ j)) (𝒩' : VirtualNormalBundle i) (p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩₁.bundle (p + 0)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle p]
    (e : dualSheaf 𝒩₁.bundle ≅ dualSheaf 𝒩'.bundle)
    (he : e.hom ≫ 𝒩'.surjection = 𝒩₁.surjection ≫ Stacks.Immersion.conormalSequenceRightMap i j)
    (n : ℤ) (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    (virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) 𝒩₁
          (p + 0)).cap (𝟙 X) n (fundamentalChowClass C (𝟙 X ≫ sX) n) ≍
      (bivariantCompositeOfInvertible C sZ sY sX i j hi hj (p : ℤ) ((0 : ℕ) : ℤ)
          (virtualNormalBundleClass C sZ sY i hi 𝒩' p)
          (virtualNormalBundleClass C sY sX j hj (VirtualNormalBundle.ofIsRegularImmersion j hreg)
            0)).cap (𝟙 X) n (fundamentalChowClass C (𝟙 X ≫ sX) n) := by
  have sq := isPullback_id_of_isIso (i := i) (j := j)
  have hij : i ≫ (j ≫ sX) = sZ := by rw [hj, hi]
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (𝒩₁.baseChange (i ≫ j) i (𝟙 Z) j sq).bundle (p + 0) :=
    isFiniteLocallyFreeOfRank_modulePullback (𝟙 Z) 𝒩₁.bundle (p + 0) inferInstance
  -- `𝒩₁|_Z ≅ 𝒩'` compatibly with the surjections onto `𝒞_{Z/Y}`
  have hbc : virtualNormalBundleClass C sZ (j ≫ sX) i hij (𝒩₁.baseChange (i ≫ j) i (𝟙 Z) j sq)
      (p + 0) = virtualNormalBundleClass C sZ (j ≫ sX) i hij 𝒩' (p + 0) := by
    refine virtualNormalGysinClass_eq_of_dualIso C sZ (j ≫ sX) i hij _ 𝒩'
      (e.symm ≪≫ 𝒩₁.baseChangeIdDualIso j sq) ?_ (p + 0)
    have key := VirtualNormalBundle.baseChangeIdDualIso_hom_comp_surjection j sq 𝒩₁
    have he' : 𝒩'.surjection = e.inv ≫ 𝒩₁.surjection ≫
        Stacks.Immersion.conormalSequenceRightMap i j := by
      rw [← he]; exact (e.inv_hom_id_assoc _).symm
    exact (Category.assoc _ _ _).trans ((congrArg (e.inv ≫ ·) key).trans he'.symm)
  subst hj
  -- the left-hand side: `[X] = j_*[Y]`, then Stacks 0B76 (1) and the base-change clause of 0FBK
  have hL1 : fundamentalChowClass C (𝟙 X ≫ sX) n =
      chowPushforwardOfIso C (j ≫ sX) (𝟙 X ≫ sX) j (by rw [Category.id_comp]) n
        (fundamentalChowClass C (j ≫ sX) n) :=
    (chowPushforwardOfIso_fundamentalChowClass C _ _ j _ n).symm
  have hL2 := BivariantClass.cap_chowPushforwardOfIso
    (virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi rfl) 𝒩₁ (p + 0))
    (𝟙 X) j j (Category.comp_id j) (j ≫ sX) rfl n (by rw [Category.id_comp])
    (fundamentalChowClass C (j ≫ sX) n) (fundamentalChowClass C (j ≫ sX) n) rfl
  have hL3 := virtualNormalGysinClass_cap_eq_chowPushforwardOfIso_cap_id C sZ sX (i ≫ j)
    (comp_comp_structureMorphism_eq hi rfl) 𝒩₁ (p + 0) j i (𝟙 Z) sq sZ hij n
    (fundamentalChowClass C (j ≫ sX) n)
  rw [chowGroupCongr_fundamentalChowClass, hbc] at hL3
  -- the right-hand side: `c(Y ⟶ X, 0) ∩ [X] = [Y]`, then Stacks 0B76 (1) along `Y ×_X X ≅ Y`
  have hR1 := virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion C (j ≫ sX)
    sX j rfl hreg 0 (VirtualNormalBundle.ofIsRegularImmersion j hreg) n hX
  have hR2 : fundamentalChowClass C (pullback.fst j (𝟙 X) ≫ j ≫ sX) (n - ((0 : ℕ) : ℤ)) =
      chowPushforwardOfIso C (j ≫ sX) (pullback.fst j (𝟙 X) ≫ j ≫ sX) (inv (pullback.fst j (𝟙 X)))
        (by rw [IsIso.inv_hom_id_assoc])
        (n - ((0 : ℕ) : ℤ)) (fundamentalChowClass C (j ≫ sX) (n - ((0 : ℕ) : ℤ))) :=
    (chowPushforwardOfIso_fundamentalChowClass C _ _ (inv (pullback.fst j (𝟙 X))) _ _).symm
  have hR3 := BivariantClass.cap_chowPushforwardOfIso
    (virtualNormalBundleClass C sZ (j ≫ sX) i hi 𝒩' p) (pullback.fst j (𝟙 X))
    (inv (pullback.fst j (𝟙 X))) (𝟙 Y) (IsIso.inv_hom_id (pullback.fst j (𝟙 X)))
    (j ≫ sX) (Category.id_comp _).symm (n - ((0 : ℕ) : ℤ)) (by rw [IsIso.inv_hom_id_assoc])
    (fundamentalChowClass C (j ≫ sX) (n - ((0 : ℕ) : ℤ)))
    (fundamentalChowClass C (𝟙 Y ≫ j ≫ sX) (n - ((0 : ℕ) : ℤ)))
    (chowGroupCongr_fundamentalChowClass C _ _)
  rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply, hR1,
    hR2, hR3, hL1, hL2, hL3, properChowPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  have hsnd : inv (pullback.fst j (𝟙 X)) ≫ pullback.snd j (𝟙 X) = j := by
    rw [IsIso.inv_comp_eq, pullback.condition, Category.comp_id]
  rw [chowPushforwardOfIso_congr_apply C _ _ _ ((testBaseChangeIso i (pullback.fst j (𝟙 X))
      (inv (pullback.fst j (𝟙 X))) (𝟙 Y) (IsIso.inv_hom_id (pullback.fst j (𝟙 X)))).hom ≫
        (pullbackRightPullbackFstIso j (𝟙 X) i).hom) (by
    refine pullback.hom_ext ?_ ?_
    · simp only [subschemeIdentityTestIso, Category.assoc, pullbackRightPullbackFstIso_hom_fst]
      simp only [testBaseChangeIso_hom_fst, IsPullback.isoPullback_hom_fst]
      exact Category.comp_id _
    · simp only [subschemeIdentityTestIso, Category.assoc, pullbackRightPullbackFstIso_hom_snd]
      conv_rhs => rw [← Category.assoc, testBaseChangeIso_hom_snd, Category.assoc, hsnd]
      simp [pullback.condition_assoc]) _ (by
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_comp_fst_comp, ← Category.assoc,
      testBaseChangeIso_hom_fst])]
  refine chowPushforwardOfIso_heq _ _ _ rfl rfl (by push_cast; ring) ?_
  have hcongr : ∀ {k k' : ℤ} (_ : k = k') {α : chowGroup C (𝟙 Y ≫ j ≫ sX) k}
      {α' : chowGroup C (𝟙 Y ≫ j ≫ sX) k'} (_ : α ≍ α'),
      (virtualNormalBundleClass C sZ (j ≫ sX) i hi 𝒩' p).cap (𝟙 Y) k α ≍
        (virtualNormalBundleClass C sZ (j ≫ sX) i hi 𝒩' p).cap (𝟙 Y) k' α' := by
    intro k k' hk α α' hα
    subst hk
    obtain rfl := eq_of_heq hα
    rfl
  exact hcongr (by push_cast; ring) (fundamentalChowClass_heq C _ (by push_cast; ring))

end Core

/-- **The case `Y = X` of the proof of Stacks 0FEC.** For a closed immersion `j : Y ⟶ X` which is
an isomorphism onto an integral `X`, a closed immersion `i : Z ⟶ Y` and a conormal-compatible
triple `𝒩, 𝒩', 𝒩''` of constant ranks `p + q, p, q`,

  `c(Z ⟶ X, 𝒩) ∩ [X] = c(Z ⟶ Y, 𝒩') ∩ c(Y ⟶ X, 𝒩'') ∩ [X]`.

`j` is a regular immersion with `𝒞_{Y/X} = 0`, so splitting off the excess normal sheaf
(Stacks 0FBL twice and 02UA) reduces to `𝒩'' = 0`, where `𝒩₁^∨ ≅ (𝒩')^∨` and the formula is
`Stacks.Chow.virtualNormalGysinClass_cap_fundamentalChowClass_heq_of_isIso`. In degrees other than
`dim_δ X` the fundamental class vanishes. -/
theorem compositionIsoCase (C : ChowSituation.{u}) : CompositionIsoCase C := by
  intro Z Y X sZ _ sY _ sX _ i j _ _ hi hj D p q _ _ _ _ k
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hreg : IsRegularImmersion j :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth j (𝟙 X)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) 0 :=
    isFiniteLocallyFreeOfRank_zero_of_isZero
      (hM := Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso j)
  unfold CompositionFormulaAt compositeVirtualNormalGysinClass
  refine eq_of_heq (HEq.trans ?_ (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ (𝟙 X) k _).symm)
  refine D.virtualNormalGysinClass_cap_heq_of_excessReduction C sZ sY sX hi hj hreg p q 0 (𝟙 X) k
    _ ?_
  by_cases hk : relativeDimension C.dimensionFunction (𝟙 X ≫ sX) (genericPoint X) = k
  · have hX : schemeDeltaDimension C sX ≤ (k : EInt) := by
      rw [schemeDeltaDimension_eq_genericPoint, ← hk, Category.id_comp]
    -- the top row of the reduced datum identifies `𝒩₁^∨` with `(𝒩')^∨`
    have hse := D.shortExact_excessLeft_excessRight hreg
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback i).obj (conormalModule j)) 0 :=
      AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i _ 0
    have hiso : IsIso (D.excessRight hreg) :=
      hse.isIso_g_iff.2 (isZero_of_isFiniteLocallyFreeOfRank_zero _)
    exact virtualNormalGysinClass_cap_fundamentalChowClass_heq_of_isIso C sZ sY sX hi hj hreg
      (D.excessKernelBundle hreg) D.bundleZY p (@asIso _ _ _ _ (D.excessRight hreg) hiso)
      (D.excessRight_comp_surjection hreg) k hX
  · have h0 : fundamentalChowClass C (𝟙 X ≫ sX) k = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne C (𝟙 X ≫ sX)
        genericPoints_eq_singleton hk, map_zero]
    rw [h0, map_zero, map_zero]

end Stacks.Chow

end

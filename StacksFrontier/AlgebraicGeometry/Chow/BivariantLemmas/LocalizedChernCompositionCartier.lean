module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionReduction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalConeFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.NormalLineConeZeroSectionGysin
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.DivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimConormalRank
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleNormalConeBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.Regularity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalBasisSections
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ProjHyperplane
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0FEC when `Y` is an effective Cartier divisor

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Z ⊆ Y ⊆ X` be closed
immersions `i : Z ⟶ Y`, `j : Y ⟶ X` of schemes locally of finite type over `S`, and let
`𝒩, 𝒩', 𝒩''` be a conormal-compatible triple of virtual normal sheaves for `Z ⊆ X`, `Z ⊆ Y`,
`Y ⊆ X` (`Stacks.Chow.ConormalCompatibleVirtualNormalBundles`). This file proves the last case of
the proof of Stacks 0FEC: `X` integral and `Y` an effective Cartier divisor, on the fundamental
class `[X]` of `X`.

By the reduction of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionExcess` one may
replace `𝒩''` by the normal bundle `𝒞_{Y/X}^∨` of rank one and `𝒩` by the kernel `𝒩₁` of
`𝒩 ⟶ i^*ℰ`, of rank `p + 1` when `𝒩'` has rank `p`. Then `c(Y ⟶ X, 𝒞_{Y/X}^∨) ∩ [X]_n` is
`[Y]_{n-1}` (Stacks 0FBM), and one has to prove

  `c(Z ⟶ X, 𝒩₁) ∩ [X]_n = c(Z ⟶ Y, 𝒩') ∩ [Y]_{n-1}`.

The source's argument: `γ = c(Z ⟶ X, 𝒩₁) ∩ [X]_n` and `γ' = c(Z ⟶ Y, 𝒩') ∩ [Y]_{n-1}` are
characterized by `p^*γ = [C_ZX]_n` in `CH_n(N₁)` and `(p')^*γ' = [C_ZY]_{n-1}` in `CH_{n-1}(N')`.
Let `Ψ : N₁ ⟶ C_YX` be the morphism to the normal line cone of `Y` which restricts to the
canonical morphism `φ : C_ZX ⟶ C_YX` of normal cones on `C_ZX ⊆ N₁`, and such that `N' ⊆ N₁` is
the inverse image of the zero section `o(Y) ⊆ C_YX`, a relative effective Cartier divisor on `N₁`
over `Z`. Let `o^*` be the Gysin class of `o(Y)` (Stacks 0B79). By Stacks 0FEB,
`o^*[C_ZX]_n = [C_ZY]_{n-1}`; pushed forward along `C_ZX ⟶ N₁` (Stacks 0B76 (1)) this computes
`o^* ∩ p^*γ` as `[C_ZY]_{n-1}` on `N'`. By Stacks 02TR, `o^* ∩ p^*γ = (p')^*γ`. Hence
`(p')^*γ = (p')^*γ'`, and `γ = γ'` as `(p')^*` is injective (Stacks 02TY).

## Main results

* `gysinSystemOfInvertible_onChow_flatPullbackChow_of_isRelativeEffectiveCartierDivisor` —
  Stacks 02TR on Chow groups, for the Gysin map of an invertible module.
* `Stacks.Chow.flatPullbackChow_projection_virtualNormalGysinClass_cap_fundamentalChowClass` —
  `p^*(c(Z ⟶ X, 𝒩) ∩ [T]_n) = ι_*[C_ZX]_n` on `N`, for an isomorphism `T ⟶ X` with
  `dim_δ(T) ≤ n`, read on `Z` and `N` themselves.
* `Stacks.Chow.heq_of_flatPullbackChow_eq_normalConeEmbedding_pushforward` — the comparison of
  `γ` and `γ'` above.
* `Stacks.Chow.isEffectiveCartierDivisor_ker_vectorBundleMap_of_shortExact` — a subbundle of
  corank one is an effective Cartier divisor; `N' ⊆ N₁` is one
  (`Stacks.Chow.isEffectiveCartierDivisor_ker_vectorBundleMap_excessRight`).
* `Stacks.Chow.normalConeEmbedding_comp_vectorBundleMap_excessRight` — the square of cones and
  vector bundles: `C_ZY ⟶ N' ⟶ N₁` is `C_ZY ⟶ C_ZX ⟶ N₁`.
* `Stacks.Chow.isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor` — an effective
  Cartier divisor is a regular closed immersion of codimension one.
* `Stacks.Chow.compositionFormulaAt_fundamentalChowClass_of_isEffectiveCartierDivisor` — the
  Cartier case of Stacks 0FEC, `Stacks.Chow.CompositionCartierCase`, for a triple `D`, given the
  morphism `Ψ : N₁ ⟶ C_YX` and an embedding `N' ⟶ N₁` with their geometric properties.
* `Stacks.Chow.compositionFormulaAt_fundamentalChowClass_of_normalConeMap` — the same for the
  embedding `N' ⟶ N₁` of the reduced datum, given only the properties of `Ψ`.

## Implementation notes

The morphism `Ψ` and the embedding `ν : N' ⟶ N₁` enter
`Stacks.Chow.compositionFormulaAt_fundamentalChowClass_of_isEffectiveCartierDivisor` as data,
with the properties the source uses: `Ψ` lies over `Z ⟶ Y`; `Ψ` restricts to `φ` on `C_ZX`; the
square `N' ⟶ N₁`, `N' ⟶ Z ⟶ Y`, `Ψ`, `o` is cartesian; `ν` restricts to the comparison
`C_ZY ⟶ C_ZX` of normal cones on `C_ZY ⊆ N'`; and the inverse image of `o(Y)` along `Ψ` is an
effective Cartier divisor. The first three are the "commutative diagram of cones and vector
bundles over `Z`" and the cartesian square of the source, the last its observation that `N'` is
a relative effective Cartier divisor in `N₁`. For `ν` the embedding of the reduced datum, the
fourth and the last are proved here
(`Stacks.Chow.compositionFormulaAt_fundamentalChowClass_of_normalConeMap`).

The class `γ` is a cap along the test scheme `𝟙 X` and `γ'` one along `Y ×_X X ⟶ Y`, so both live
on chosen pullbacks isomorphic to `Z`. They are compared after pushing them forward to `Z`
itself.

The source takes `X` integral of dimension `n`; the comparison only uses `dim_δ(X) ≤ n`, and on an
integral `X` the fundamental class vanishes in every other degree.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Chow

/-! ### Stacks 02TR on Chow groups -/

/-- **Stacks 02TR, first equality, on Chow groups.** Let `p : X ⟶ Y` be flat of relative
dimension `r + 1` and let `D = Z(t)` be a relative effective Cartier divisor on `X/Y`, the zero
scheme of a section of an invertible module, with `D ⟶ Y` of relative dimension `r`. Then the
Gysin map of `t` carries `p^* α` to `(p|_D)^* α`, for every class `α`. -/
theorem gysinSystemOfInvertible_onChow_flatPullbackChow_of_isRelativeEffectiveCartierDivisor
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p]
    (hbase : p ≫ sY = sX) (r : ℕ) (hp : RelativeDimension p (r + 1)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (t : Γ(L, ⊤))
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p (Stacks.Divisors.zeroScheme X L t))
    (hq : RelativeDimension ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p) r) (k : ℤ)
    (α : chowGroup C sY k) :
    haveI : Flat ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p) := hD.2
    (gysinSystemOfInvertible C).onChow sX L t (k + (r : ℤ))
        (chowGroupDegreeEquiv C sX (by push_cast; ring : k + ((r + 1 : ℕ) : ℤ) = k + (r : ℤ) + 1)
          (flatPullbackChow C sX sY p hbase (r + 1) hp k (flatPullbackDescends C _ _ _ _ _ _ _)
            α)) =
      flatPullbackChow C ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p) (by rw [Category.assoc, hbase]) r hq
        k (flatPullbackDescends C _ _ _ _ _ _ _) α := by
  have : Flat ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p) := hD.2
  obtain ⟨σ, rfl⟩ := exists_sections_eval_eq L t
  obtain ⟨k, rfl⟩ : ∃ k' : ℤ, k = k' + 1 := ⟨k - 1, by ring⟩
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1 := by push_cast; ring
    have h02TR := gysinRule_extendCycleGroup_flatPullback C sX sY p hbase r hp k L σ hD hq hcast a
    have hmk : chowGroupDegreeEquiv C sX hcast
        (flatPullbackChow C sX sY p hbase (r + 1) hp (k + 1)
          (flatPullbackDescends C _ _ _ _ _ _ _)
          (QuotientAddGroup.mk' (rationalEquivalences C sY (k + 1)) a)) =
        QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1 + (r : ℤ) + 1))
          (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1) a) := by
      rw [flatPullbackChow_mk]
      exact chowGroupDegreeEquiv_mk_eq_mk_of_val C sX hcast _ _
        (val_cycleGroup_cast C sX hcast _).symm
    refine (congrArg _ hmk).trans ?_
    refine congrArg (QuotientAddGroup.mk' _) (Subtype.ext ?_)
    exact congrArg Subtype.val h02TR



/-- **Stacks 02TR on Chow groups, with the degrees matched up to heterogeneous equality.** The
form of
`Stacks.Chow.gysinSystemOfInvertible_onChow_flatPullbackChow_of_isRelativeEffectiveCartierDivisor`
in which the class the Gysin map is applied to is only heterogeneously equal to `p^* α`. -/
theorem gysinSystemOfInvertible_onChow_heq_flatPullbackChow_of_isRelativeEffectiveCartierDivisor
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p]
    (hbase : p ≫ sY = sX) (r : ℕ) (hp : RelativeDimension p (r + 1)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (t : Γ(L, ⊤))
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p (Stacks.Divisors.zeroScheme X L t))
    (hq : RelativeDimension ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p) r) {k l : ℤ}
    (hkl : k + (r : ℤ) = l) (α : chowGroup C sY k) (x : chowGroup C sX (l + 1))
    (hx : x ≍ flatPullbackChow C sX sY p hbase (r + 1) hp k (flatPullbackDescends C _ _ _ _ _ _ _)
      α) :
    haveI : Flat ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p) := hD.2
    (gysinSystemOfInvertible C).onChow sX L t l x ≍
      flatPullbackChow C ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p) (by rw [Category.assoc, hbase]) r hq
        k (flatPullbackDescends C _ _ _ _ _ _ _) α := by
  subst hkl
  have hx' : x = chowGroupDegreeEquiv C sX (by push_cast; ring)
      (flatPullbackChow C sX sY p hbase (r + 1) hp k (flatPullbackDescends C _ _ _ _ _ _ _) α) :=
    eq_of_heq (hx.trans (chowGroupDegreeEquiv_heq C sX _ _).symm)
  rw [hx', gysinSystemOfInvertible_onChow_flatPullbackChow_of_isRelativeEffectiveCartierDivisor C
    sX sY p hbase r hp L t hD hq k α]


/-! ### The defining relation of Stacks 0FBK on a fundamental class, read on `Z` -/

/-- **`p^*(c(Z ⟶ X, 𝒩) ∩ [T]_n) = ι_*[C_ZX]_n`**, for an isomorphism `t : T ⟶ X` with
`dim_δ(T) ≤ n`. The cap product lives on the chosen pullback `Z ×_X T`; pushed forward to `Z`
along the isomorphism `Z ×_X T ⟶ Z`, its flat pullback along the bundle projection `p : N ⟶ Z`
is the pushforward of the fundamental class of the normal cone along `ι : C_ZX ⟶ N`. This is the
relation of Stacks 0FBK together with the computation of the proof of Stacks 0FBM. -/
theorem flatPullbackChow_projection_virtualNormalGysinClass_cap_fundamentalChowClass
    (C : ChowSituation.{u}) {Z X T : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
    (hf : f ≫ sX = sZ) (𝒩 : VirtualNormalBundle f) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    (t : T ⟶ X) [IsIso t] (n : ℤ) (hT : schemeDeltaDimension C (t ≫ sX) ≤ (n : EInt)) :
    haveI := 𝒩.flat_projection_of_rank r
    haveI := locallyOfFiniteType_normalConeToBase C sX f
    flatPullbackChow C (𝒩.projection ≫ sZ) sZ 𝒩.projection rfl r
        (𝒩.relativeDimension_projection_of_rank r) (n - r) (flatPullbackDescends C _ _ _ _ _ _ _)
        (chowPushforwardOfIso C (pullback.fst f t ≫ sZ) sZ (pullback.fst f t) rfl (n - r)
          ((virtualNormalBundleClass C sZ sX f hf 𝒩 r).cap t n
            (fundamentalChowClass C (t ≫ sX) n))) ≍
      properChowPushforward C (Stacks.Conormal.normalConeToBase f ≫ sZ) (𝒩.projection ≫ sZ)
        𝒩.normalConeEmbedding (by rw [𝒩.normalConeEmbedding_projection_assoc]) n
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (Stacks.Conormal.normalConeToBase f ≫ sZ) n) := by
  have := 𝒩.flat_projection_of_rank r
  have := locallyOfFiniteType_normalConeToBase C sX f
  have := locallyOfFiniteType_bundleTestBaseChange f 𝒩.projection t
  have := flat_bundleTestBaseChange f 𝒩.projection (𝒩.flat_projection_of_rank r) t
  have hA := bundleFlatPullbackChow_virtualNormalBundleClass_cap C sZ sX f hf 𝒩 r t n
    (fundamentalChowClass C (t ≫ sX) n)
  rw [virtualNormalConeClass_cap_fundamentalChowClass C sZ sX f hf 𝒩 t n hT] at hA
  unfold bundleFlatPullbackChow at hA
  have key := flatPullbackChow_chowPushforwardOfIso C (pullback.fst f t ≫ sZ)
    (pullback.fst (𝒩.projection ≫ f) t ≫ 𝒩.projection ≫ sZ) sZ (𝒩.projection ≫ sZ)
    (pullback.fst f t) rfl (pullback.fst (𝒩.projection ≫ f) t) rfl
    (bundleTestBaseChange f 𝒩.projection t)
    (bundleTestBaseChange_comp_structureMorphism f 𝒩.projection sZ _ rfl t) 𝒩.projection rfl
    (bundleTestBaseChange_fst f 𝒩.projection t) r
    (relativeDimension_bundleTestBaseChange f 𝒩.projection
      (𝒩.relativeDimension_projection_of_rank r) t)
    (𝒩.relativeDimension_projection_of_rank r) (n - r) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _)
    ((virtualNormalBundleClass C sZ sX f hf 𝒩 r).cap t n (fundamentalChowClass C (t ≫ sX) n))
  refine (heq_of_eq key).trans ?_
  refine (chowPushforwardOfIso_heq_congr C _ _ _ rfl (by ring) _ _ hA).trans ?_
  set ιT := bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ f) t
  set fK := pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ f) t
  have hK : fK ≫ 𝒩.normalConeEmbedding = ιT ≫ pullback.fst (𝒩.projection ≫ f) t :=
    (bivariantPushforwardBaseChange_fst _ _ _).symm
  have hw : (ιT ≫ pullback.fst (𝒩.projection ≫ f) t) ≫ 𝒩.projection ≫ sZ =
      fK ≫ Stacks.Conormal.normalConeToBase f ≫ sZ := by
    rw [← hK, Category.assoc]
    exact congrArg (fK ≫ ·) (𝒩.normalConeEmbedding_projection_assoc sZ)
  have e1 := properChowPushforward_comp_apply C _ _ (𝒩.projection ≫ sZ) ιT
    (pullback.fst (𝒩.projection ≫ f) t) _ rfl
    (bivariantPushforwardBaseChange_comp_structure
      (by rw [𝒩.normalConeEmbedding_projection_assoc]) (𝒩.projection ≫ f) t) rfl hw (n - 0)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    (fundamentalChowClass C (fK ≫ Stacks.Conormal.normalConeToBase f ≫ sZ) (n - 0))
  have e2 := properChowPushforward_comp_apply C _ (Stacks.Conormal.normalConeToBase f ≫ sZ)
    (𝒩.projection ≫ sZ) fK 𝒩.normalConeEmbedding _ hK rfl
    (by rw [𝒩.normalConeEmbedding_projection_assoc]) hw (n - 0)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    (fundamentalChowClass C (fK ≫ Stacks.Conormal.normalConeToBase f ≫ sZ) (n - 0))
  rw [properChowPushforward_eq_chowPushforwardOfIso C _ _ fK rfl (n - 0),
    chowPushforwardOfIso_fundamentalChowClass] at e2
  rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _ (pullback.fst (𝒩.projection ≫ f) t)
      rfl (n - 0) (properPushforwardDescends C _ _ _ _ _), ← e1, e2]
  exact properChowPushforward_heq_congr C _ _ _ _ (by ring) _ _ _ _
    (fundamentalChowClass_heq C _ (by ring))


/-! ### The comparison of the two classes -/

section Comparison

variable (C : ChowSituation.{u}) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {i : Z ⟶ Y} [IsClosedImmersion i] {j : Y ⟶ X} [IsClosedImmersion j]
  [Stacks.Divisors.IsEffectiveCartierDivisor j.ker] (hi : i ≫ sY = sZ) (hj : j ≫ sX = sY)
  (𝒩₁ : VirtualNormalBundle (i ≫ j)) (𝒩' : VirtualNormalBundle i) (p : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩₁.bundle (p + 1)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle p]
  (Ψ : 𝒩₁.totalSpace ⟶ Stacks.Conormal.normalCone j)
  (hΨ₀ : Ψ ≫ Stacks.Conormal.normalConeToBase j = 𝒩₁.projection ≫ i)
  (hΨ : 𝒩₁.normalConeEmbedding ≫ Ψ =
    normalConeChangeOfCentreMap (i ≫ j) j (Scheme.Hom.le_ker_comp i j))
  (ν : 𝒩'.totalSpace ⟶ 𝒩₁.totalSpace)
  (hν : IsPullback ν (𝒩'.projection ≫ i) Ψ (normalConeZeroSection j))
  (hcone : 𝒩'.normalConeEmbedding ≫ ν =
    normalConeBaseChangeMap j sX (i ≫ j) i (ker_eq_comap_ker_of_comp_eq j (i ≫ j) i rfl) ≫
      𝒩₁.normalConeEmbedding)
  (hcart : Stacks.Divisors.IsEffectiveCartierDivisor ((normalConeZeroSectionIdeal j).comap Ψ))

include hi hj hΨ₀ hΨ hν hcone hcart in
/-- **The comparison of `γ` and `γ'` in the proof of Stacks 0FEC.** Let `Y ⊆ X` be an effective
Cartier divisor, `𝒩₁` a virtual normal bundle for `Z ⊆ X` of rank `p + 1` and `𝒩'` one for
`Z ⊆ Y` of rank `p`, with vector bundles `p₁ : N₁ ⟶ Z` and `p' : N' ⟶ Z`. Let `Ψ : N₁ ⟶ C_YX` and
`ν : N' ⟶ N₁` be as in the source: `Ψ` lies over `Z ⟶ Y` and restricts to the change of centre
`φ : C_ZX ⟶ C_YX` on `C_ZX`, `N'` is the inverse image along `Ψ` of the zero section `o(Y)`, an
effective Cartier divisor of `N₁`, and `ν` restricts to `C_ZY ⟶ C_ZX`. If `dim_δ(X) ≤ n` and
`γ, γ' ∈ CH_{n-1-p}(Z)` satisfy `p₁^*γ = ι_*[C_ZX]_n` and `(p')^*γ' = ι'_*[C_ZY]_{n-1}`, then
`γ = γ'`.

The Gysin class `o^*` of `o(Y)` caps `ι_*[C_ZX]_n` to the pushforward of `[C_ZY]_{n-1}` by
Stacks 0FEB and Stacks 0B76 (1), and caps `p₁^*γ` to `(p')^*γ` by Stacks 02TR; flat pullback along
`p'` is injective. The degrees of the classes are equal integers written differently. -/
theorem heq_of_flatPullbackChow_eq_normalConeEmbedding_pushforward (n n' m m' : ℤ)
    (hm : m + ((p + 1 : ℕ) : ℤ) = n) (hn' : n' = n - 1) (hmm' : m' = m)
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) (γ : chowGroup C sZ m) (γ' : chowGroup C sZ m')
    (hγ : haveI := 𝒩₁.flat_projection_of_rank (p + 1)
      haveI := locallyOfFiniteType_normalConeToBase C sX (i ≫ j)
      flatPullbackChow C (𝒩₁.projection ≫ sZ) sZ 𝒩₁.projection rfl (p + 1)
        (𝒩₁.relativeDimension_projection_of_rank (p + 1)) m
        (flatPullbackDescends C _ _ _ _ _ _ _) γ ≍
      properChowPushforward C (Stacks.Conormal.normalConeToBase (i ≫ j) ≫ sZ)
        (𝒩₁.projection ≫ sZ) 𝒩₁.normalConeEmbedding
        (by rw [𝒩₁.normalConeEmbedding_projection_assoc]) n
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (Stacks.Conormal.normalConeToBase (i ≫ j) ≫ sZ) n))
    (hγ' : haveI := 𝒩'.flat_projection_of_rank p
      haveI := locallyOfFiniteType_normalConeToBase C sY i
      flatPullbackChow C (𝒩'.projection ≫ sZ) sZ 𝒩'.projection rfl p
        (𝒩'.relativeDimension_projection_of_rank p) m' (flatPullbackDescends C _ _ _ _ _ _ _) γ' ≍
      properChowPushforward C (Stacks.Conormal.normalConeToBase i ≫ sZ) (𝒩'.projection ≫ sZ)
        𝒩'.normalConeEmbedding (by rw [𝒩'.normalConeEmbedding_projection_assoc]) n'
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (Stacks.Conormal.normalConeToBase i ≫ sZ) n')) :
    γ ≍ γ' := by
  subst m' n'
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := locallyOfFiniteType_normalConeToBase C sX (i ≫ j)
  have := locallyOfFiniteType_normalConeToBase C sY i
  have := 𝒩₁.flat_projection_of_rank (p + 1)
  have := 𝒩'.flat_projection_of_rank p
  have hij : (i ≫ j) ≫ sX = sZ := comp_comp_structureMorphism_eq hi hj
  have hle : j.ker ≤ (i ≫ j).ker := Scheme.Hom.le_ker_comp i j
  have hker := ker_eq_comap_ker_of_comp_eq j (i ≫ j) i rfl
  -- `Ψ` and `φ` over the base
  have hΨs : Ψ ≫ normalConeToX j ≫ sX = 𝒩₁.projection ≫ sZ := by
    simp only [normalConeToX, Category.assoc]
    rw [reassoc_of% hΨ₀, hj, hi]
  have : LocallyOfFiniteType Ψ := by
    have : LocallyOfFiniteType (Ψ ≫ normalConeToX j ≫ sX) := by rw [hΨs]; infer_instance
    exact locallyOfFiniteType_of_comp Ψ (normalConeToX j ≫ sX)
  have hC : Stacks.Conormal.normalConeToBase (i ≫ j) ≫ sZ =
      normalConeChangeOfCentreMap (i ≫ j) j hle ≫ normalConeToX j ≫ sX := by
    rw [← Category.assoc, normalConeChangeOfCentreMap_toX]
    simp only [normalConeToX, Category.assoc, hij]
  have hCi : Stacks.Conormal.normalConeToBase i ≫ sZ = normalConeToX i ≫ j ≫ sX := by
    rw [normalConeToX, Category.assoc, hj, hi]
  -- the base change of `C_ZX ⟶ N₁` along the zero section
  let h' : pullback (gysinTripleInclusion
        (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal j))
        (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal j)))
        (normalConeChangeOfCentreMap (i ≫ j) j hle) ⟶
      pullback (gysinTripleInclusion (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal j))
        (Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal j))) Ψ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ 𝒩₁.normalConeEmbedding)
      (by rw [Category.assoc, hΨ]; exact pullback.condition)
  have hfst : h' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hsnd : h' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝒩₁.normalConeEmbedding :=
    pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.snd _ _) h' 𝒩₁.normalConeEmbedding (pullback.snd _ _) := by
    refine IsPullback.of_bot ?_ hsnd.symm (IsPullback.of_hasPullback _ Ψ).flip
    rw [hfst, hΨ]
    exact (IsPullback.of_hasPullback _ _).flip
  -- Stacks 0FEB, pushed forward to `N₁` (Stacks 0B76 (1))
  have h1 := (gysinBivariantClass C (normalConeToX j ≫ sX)
    (Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal j))
    (Stacks.Divisors.divisorSheafGlobalSection
      (normalConeZeroSectionIdeal j))).1.proper_naturality_of_test_eq
    Ψ 𝒩₁.normalConeEmbedding (normalConeChangeOfCentreMap (i ≫ j) j hle) hΨ h' sq hfst n
    (by rw [← Category.assoc, hΨ]) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    (fundamentalChowClass C (normalConeChangeOfCentreMap (i ≫ j) j hle ≫ normalConeToX j ≫ sX) n)
  have hκ := normalConeToZeroSectionPullback_toBase C sX j (i ≫ j) hle i hker
  have hκ' : (normalConeToZeroSectionPullback j (i ≫ j) hle i hker ≫ h') ≫
      pullback.fst _ Ψ ≫ gysinTripleInclusion _ _ ≫ normalConeToX j ≫ sX =
      normalConeToX i ≫ j ≫ sX := by
    rw [Category.assoc, reassoc_of% hfst]
    exact hκ
  rw [gysinBivariantClass_cap_normalCone_eq C sX j (i ≫ j) hle i hker hX,
    ← properChowPushforward_comp_apply C _ _ _ _ _ _ rfl _ _ hκ' (n - 1) _ _
      (properPushforwardDescends C _ _ _ _ _)] at h1
  -- the zero section `o(Y)` as the zero scheme `D₀` of the canonical section
  let L := Stacks.Divisors.divisorSheaf (normalConeZeroSectionIdeal j)
  let σ := Stacks.Divisors.divisorSheafGlobalSection (normalConeZeroSectionIdeal j)
  have hz : Stacks.Divisors.zeroScheme _ L σ = normalConeZeroSectionIdeal j :=
    Stacks.Divisors.zeroScheme_canonicalSection _
  let e₀ : (Stacks.Divisors.zeroScheme _ L σ).subscheme ⟶ Y :=
    eqToHom (congrArg Scheme.IdealSheafData.subscheme hz) ≫
      (normalConeZeroSectionIdeal j).subschemeι ≫ Stacks.Conormal.normalConeToBase j
  have he₀ : e₀ ≫ normalConeZeroSection j = gysinTripleInclusion L σ := by
    simp only [e₀, normalConeZeroSection, Category.assoc, IsIso.hom_inv_id_assoc]
    exact subschemeι_eqToHom hz
  -- `N'` as the base change of `D₀` along `Ψ`
  have hν' : IsPullback ((𝒩'.projection ≫ i) ≫ inv e₀) ν (gysinTripleInclusion L σ) Ψ := by
    refine hν.flip.of_iso (Iso.refl _) (asIso e₀).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [← he₀]
    · simp
  let E := hν'.isoPullback
  have hEsnd : E.hom ≫ pullback.snd _ _ = ν := hν'.isoPullback_hom_snd
  have hEfst : E.hom ≫ pullback.fst _ _ = (𝒩'.projection ≫ i) ≫ inv e₀ :=
    hν'.isoPullback_hom_fst
  let Θ := gysinDivisorBaseChangeIso L σ Ψ
  have hνp : ν ≫ 𝒩₁.projection = 𝒩'.projection := by
    rw [← cancel_mono i, Category.assoc, ← hΨ₀, ← Category.assoc, hν.w, Category.assoc,
      normalConeZeroSection_toBase, Category.comp_id]
  have hΞ : (Θ.hom ≫ E.inv) ≫ 𝒩'.projection =
      (gysinTripleDivisor L σ Ψ).subschemeι ≫ 𝒩₁.projection := by
    rw [← hνp, ← hEsnd]
    simp only [Θ, Category.assoc, Iso.inv_hom_id_assoc, gysinDivisorBaseChangeIso_hom_snd_assoc]
  have hEinv : E.inv ≫ 𝒩'.projection ≫ sZ =
      pullback.fst _ Ψ ≫ gysinTripleInclusion L σ ≫ normalConeToX j ≫ sX := by
    rw [Iso.inv_comp_eq, ← Category.assoc E.hom, hEfst, ← he₀]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, normalConeToX,
      normalConeZeroSection_toBase_assoc, hj, hi]
  -- the zero scheme `Ψ⁻¹(D₀)` of the pulled-back section is `N'`, a relative effective Cartier
  -- divisor on `N₁` over `Z`
  have hD''eq : gysinTripleDivisor L σ Ψ = (normalConeZeroSectionIdeal j).comap Ψ := by
    rw [gysinTripleDivisor, Stacks.Divisors.zeroScheme_pullback, hz]
  have hsqΞ : IsPullback (Θ.hom ≫ E.inv)
      ((gysinTripleDivisor L σ Ψ).subschemeι ≫ 𝒩₁.projection) 𝒩'.projection (𝟙 Z) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hΞ]⟩
  have hDflat : Flat ((gysinTripleDivisor L σ Ψ).subschemeι ≫ 𝒩₁.projection) :=
    MorphismProperty.of_isPullback hsqΞ (𝒩'.flat_projection_of_rank p)
  have hDrel : RelativeDimension ((gysinTripleDivisor L σ Ψ).subschemeι ≫ 𝒩₁.projection) p :=
    RelativeDimension.of_isPullback hsqΞ (𝒩'.relativeDimension_projection_of_rank p)
  have hDcart : Stacks.Divisors.IsRelativeEffectiveCartierDivisor 𝒩₁.projection
      (gysinTripleDivisor L σ Ψ) := ⟨hD''eq ▸ hcart, hDflat⟩
  -- `ι_*[C_ZX]_n = p₁^* γ` on `N₁`
  set x := properChowPushforward C
      (normalConeChangeOfCentreMap (i ≫ j) j hle ≫ normalConeToX j ≫ sX)
      (Ψ ≫ normalConeToX j ≫ sX) 𝒩₁.normalConeEmbedding (by rw [← Category.assoc, hΨ]) n
      (properPushforwardDescends C _ _ _ _ _)
      (fundamentalChowClass C (normalConeChangeOfCentreMap (i ≫ j) j hle ≫ normalConeToX j ≫ sX)
        n)
  have hx : x ≍
      flatPullbackChow C (Ψ ≫ normalConeToX j ≫ sX) sZ 𝒩₁.projection hΨs.symm (p + 1)
        (𝒩₁.relativeDimension_projection_of_rank (p + 1)) m
        (flatPullbackDescends C _ _ _ _ _ _ _) γ := by
    refine HEq.trans ?_ (hγ.symm.trans ?_)
    · exact properChowPushforward_heq_congr_base C _ hC.symm hΨs _ _ rfl _ _ _ _
        (fundamentalChowClass_heq_of_hom_eq C hC.symm n)
    · exact flatPullbackChow_heq_congr_base C hΨs.symm rfl rfl _ _ rfl _ _ rfl _ _ γ γ HEq.rfl
  -- the Gysin map of the pulled-back section on `p₁^* γ` (Stacks 02TR)
  have hG := (gysinBivariantClass C (normalConeToX j ≫ sX) L σ).2 Ψ n x
  rw [gysinBivariantCap_apply] at hG
  have h02 :=
    gysinSystemOfInvertible_onChow_heq_flatPullbackChow_of_isRelativeEffectiveCartierDivisor C
    (Ψ ≫ normalConeToX j ≫ sX) sZ 𝒩₁.projection hΨs.symm p
    (𝒩₁.relativeDimension_projection_of_rank (p + 1)) (gysinTripleModule L Ψ)
    (gysinTripleSection L σ Ψ)
    hDcart hDrel (k := m) (l := n - 1) (by push_cast at hm ⊢; omega) γ
    (chowGroupDegreeEquiv C _ (by ring : n = n - 1 + 1) _)
    ((chowGroupDegreeEquiv_heq C _ _ _).trans hx)
  -- the two closed immersions of `C_ZY` into the base change of `D₀` along `Ψ`
  have hκE : normalConeToZeroSectionPullback j (i ≫ j) hle i hker ≫ h' =
      𝒩'.normalConeEmbedding ≫ E.hom := by
    rw [← cancel_mono (pullback.snd (gysinTripleInclusion L σ) Ψ), Category.assoc, hsnd,
      ← Category.assoc, normalConeToZeroSectionPullback_snd, Category.assoc, hEsnd, hcone]
  -- flat pullback of `γ` along `N' ⟶ Z`, through `Ψ⁻¹(D₀) ≅ N'`
  have hΞs : (Θ.hom ≫ E.inv) ≫ 𝒩'.projection ≫ sZ =
      (gysinTripleDivisor L σ Ψ).subschemeι ≫ Ψ ≫ normalConeToX j ≫ sX := by
    rw [← Category.assoc, hΞ, Category.assoc, hΨs]
  have hc := flatPullbackChow_chowPushforwardOfIso C sZ
    ((gysinTripleDivisor L σ Ψ).subschemeι ≫ Ψ ≫ normalConeToX j ≫ sX) sZ (𝒩'.projection ≫ sZ)
    (𝟙 Z) (Category.id_comp _) (Θ.hom ≫ E.inv) hΞs
    ((gysinTripleDivisor L σ Ψ).subschemeι ≫ 𝒩₁.projection) (by rw [Category.assoc, hΨs])
    𝒩'.projection rfl (by rw [Category.comp_id, hΞ]) p hDrel
    (𝒩'.relativeDimension_projection_of_rank p) m
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) γ
  rw [chowPushforwardOfIso_id, ← chowPushforwardOfIso_comp_apply C _
    (pullback.fst _ Ψ ≫ gysinTripleInclusion L σ ≫ normalConeToX j ≫ sX) _ Θ.hom E.inv
    (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L σ C (normalConeToX j ≫ sX) Ψ)
    hEinv] at hc
  have hTh := (chowPushforwardOfIso_heq_congr C _ _ Θ.hom
    (gysinDivisorBaseChangeIso_hom_comp_structureMorphism L σ C (normalConeToX j ≫ sX) Ψ)
    (by push_cast at hm ⊢; omega) _ _ h02.symm).trans (heq_of_eq (hG.symm.trans h1))
  have hι' : chowPushforwardOfIso C _ (𝒩'.projection ≫ sZ) E.inv hEinv (n - 1)
      (properChowPushforward C (normalConeToX i ≫ j ≫ sX) _
        (normalConeToZeroSectionPullback j (i ≫ j) hle i hker ≫ h') hκ' (n - 1)
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (normalConeToX i ≫ j ≫ sX) (n - 1))) =
      properChowPushforward C (normalConeToX i ≫ j ≫ sX) (𝒩'.projection ≫ sZ)
        𝒩'.normalConeEmbedding (by rw [𝒩'.normalConeEmbedding_projection_assoc, hCi])
        (n - 1) (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (normalConeToX i ≫ j ≫ sX) (n - 1)) := by
    rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _ E.inv hEinv (n - 1)
        (properPushforwardDescends C _ _ _ _ _),
      ← properChowPushforward_comp_apply C _ _ _ _ _ 𝒩'.normalConeEmbedding
        (by rw [hκE, Category.assoc, Iso.hom_inv_id, Category.comp_id])]
  have hfin : flatPullbackChow C (𝒩'.projection ≫ sZ) sZ 𝒩'.projection rfl p
      (𝒩'.relativeDimension_projection_of_rank p) m (flatPullbackDescends C _ _ _ _ _ _ _) γ =
      flatPullbackChow C (𝒩'.projection ≫ sZ) sZ 𝒩'.projection rfl p
      (𝒩'.relativeDimension_projection_of_rank p) m (flatPullbackDescends C _ _ _ _ _ _ _) γ' := by
    refine eq_of_heq ((heq_of_eq hc).trans ?_)
    refine ((chowPushforwardOfIso_heq_congr C _ _ E.inv hEinv
      (by push_cast at hm ⊢; omega) _ _ hTh).trans (heq_of_eq hι')).trans ?_
    refine HEq.trans ?_ hγ'.symm
    exact properChowPushforward_heq_congr_base C _ hCi.symm rfl _ _ rfl _ _ _ _
      (fundamentalChowClass_heq_of_hom_eq C hCi.symm _)
  have hinj := (flatPullbackChow_bijective_vectorBundleToBase_factorsGeneral C sZ
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩'.bundle) p m).1
  exact heq_of_eq (hinj hfin)

include hΨ₀ hΨ hν hcone hcart in
/-- **Stacks 0FEC for `𝒩'' = 𝒞_{Y/X}^∨` and `Y` an effective Cartier divisor, on `[X]_n`.** In the
situation of `Stacks.Chow.heq_of_flatPullbackChow_eq_normalConeEmbedding_pushforward`, if
`dim_δ(X) ≤ n` then

  `c(Z ⟶ X, 𝒩₁) ∩ [X]_n = c(Z ⟶ Y, 𝒩') ∩ c(Y ⟶ X, 𝒞_{Y/X}^∨) ∩ [X]_n`,

both sides read on the test scheme `𝟙 X`. The inner cap on the right is `[Y]_{n-1}` by
Stacks 0FBM, and the two sides, pushed forward to `Z`, satisfy the two relations of
`Stacks.Chow.heq_of_flatPullbackChow_eq_normalConeEmbedding_pushforward`. -/
theorem virtualNormalGysinClass_cap_fundamentalChowClass_heq_of_changeOfCentre
    [IsLocallyNoetherian Y] (hreg : IsRegularImmersion j)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) 1]
    (n : ℤ) (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    (virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) 𝒩₁
        (p + 1)).cap (𝟙 X) n (fundamentalChowClass C (𝟙 X ≫ sX) n) ≍
      (bivariantCompositeOfInvertible C sZ sY sX i j hi hj (p : ℤ) ((1 : ℕ) : ℤ)
        (virtualNormalBundleClass C sZ sY i hi 𝒩' p)
        (virtualNormalBundleClass C sY sX j hj (VirtualNormalBundle.ofIsRegularImmersion j hreg)
          1)).cap (𝟙 X) n (fundamentalChowClass C (𝟙 X ≫ sX) n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := locallyOfFiniteType_normalConeToBase C sX (i ≫ j)
  have := locallyOfFiniteType_normalConeToBase C sY i
  have := 𝒩₁.flat_projection_of_rank (p + 1)
  have := 𝒩'.flat_projection_of_rank p
  have hij : (i ≫ j) ≫ sX = sZ := comp_comp_structureMorphism_eq hi hj
  rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply,
    virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion C sY sX j hj hreg 1 _ n
      hX]
  -- the two test schemes `X` over `X` and `Y' = Y ×_X X` over `Y`
  set y := pullback.fst j (𝟙 X) with hy_def
  have hYdim : schemeDeltaDimension C sY ≤ ((n - ((1 : ℕ) : ℤ) : ℤ) : EInt) :=
    schemeDeltaDimension_le_sub_of_isRegularImmersion C sY sX j hj hreg 1 n hX
  have hY' : schemeDeltaDimension C (y ≫ sY) ≤ ((n - ((1 : ℕ) : ℤ) : ℤ) : EInt) :=
    le_trans (le_of_eq (schemeDeltaDimension_comp_iso C (asIso y) sY)) hYdim
  have hX' : schemeDeltaDimension C (𝟙 X ≫ sX) ≤ (n : EInt) := by simpa using hX
  set γ' := (virtualNormalBundleClass C sZ sY i hi 𝒩' p).cap y (n - ((1 : ℕ) : ℤ))
    (fundamentalChowClass C (y ≫ sY) (n - ((1 : ℕ) : ℤ))) with hγ'_def
  set γ := (virtualNormalBundleClass C sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hi hj) 𝒩₁
    (p + 1)).cap (𝟙 X) n (fundamentalChowClass C (𝟙 X ≫ sX) n) with hγ_def
  -- the two classes read on `Z`
  set γ₀ := chowPushforwardOfIso C (pullback.fst (i ≫ j) (𝟙 X) ≫ sZ) sZ
    (pullback.fst (i ≫ j) (𝟙 X)) rfl _ γ with hγ₀_def
  set γ'₀ := chowPushforwardOfIso C (pullback.fst i y ≫ sZ) sZ (pullback.fst i y) rfl _ γ'
    with hγ'₀_def
  -- the defining relations of the two classes (Stacks 0FBK, 0FBM)
  have hA := flatPullbackChow_projection_virtualNormalGysinClass_cap_fundamentalChowClass C sZ sX
    (i ≫ j) hij 𝒩₁ (p + 1) (𝟙 X) n hX'
  have hB := flatPullbackChow_projection_virtualNormalGysinClass_cap_fundamentalChowClass C sZ sY
    i hi 𝒩' p y _ hY'
  -- the main claim
  have hmain : γ₀ ≍ γ'₀ :=
    heq_of_flatPullbackChow_eq_normalConeEmbedding_pushforward C sZ sY sX hi hj 𝒩₁ 𝒩' p Ψ hΨ₀ hΨ
      ν hν hcone hcart n (n - ((1 : ℕ) : ℤ))
      (n - ((p + 1 : ℕ) : ℤ)) (n - ((1 : ℕ) : ℤ) - (p : ℤ)) (by ring) (by push_cast; ring)
      (by push_cast; ring) hX γ₀ γ'₀ hA hB
  -- conclusion
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  rw [properChowPushforward_eq_chowPushforwardOfIso]
  have hdeg : n - ((p + 1 : ℕ) : ℤ) = n - ((1 : ℕ) : ℤ) - (p : ℤ) := by push_cast; ring
  refine (chowGroupDegreeEquiv_heq C _ hdeg γ).symm.trans (heq_of_eq ?_)
  refine chowPushforwardOfIso_injective C _ _ (pullback.fst (i ≫ j) (𝟙 X)) rfl _ ?_
  rw [chowPushforwardOfIso_comp_apply]
  refine eq_of_heq (((chowPushforwardOfIso_heq_congr C _ _ _ rfl hdeg.symm _ _
    (chowGroupDegreeEquiv_heq C _ hdeg γ)).trans hmain).trans (heq_of_eq ?_))
  exact chowPushforwardOfIso_congr_apply C _ _ _ _
    (pullbackRightPullbackFstIso_hom_fst j (𝟙 X) i).symm _ _ _ _

end Comparison

/-! ### The vector bundles `N' ⊆ N₁` and the normal cones -/

section Subbundle

/-- **`𝐕(𝟙^*M) ⟶ 𝐕(M)` is inverse to `𝐕(𝟙^*M ≅ M)`**: the base change of the vector bundle of `M`
along the identity, read through the identification `𝟙^*M ≅ M`, is the identity of `𝐕(M)`. -/
theorem vectorBundleMap_pullbackId_hom_comp_vectorBundlePullbackProjection {Z : Scheme.{u}}
    (M : Z.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.vectorBundleMap Z (F := (Scheme.Modules.pullback (𝟙 Z)).obj M) (G := M)
      ((Scheme.Modules.pullbackId Z).hom.app M)).left ≫
      (Scheme.Modules.vectorBundlePullbackProjection (𝟙 Z) M).left = 𝟙 _ := by
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)).unit.app M ≫
      (Scheme.Modules.pushforward (𝟙 Z)).map ((Scheme.Modules.pullbackId Z).hom.app M) =
      (Adjunction.id (C := Z.Modules)).unit.app M := by
    have h := unit_conjugateEquiv (Adjunction.id)
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)) (Scheme.Modules.pullbackId Z).hom M
    rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
    exact h.symm
  have h2 : Scheme.Modules.vectorBundleClassifyingMap M
      (Over.homMk (U := (Over.map (𝟙 Z)).obj (Scheme.Modules.vectorBundleOver Z (F := M)))
        (V := Scheme.Modules.vectorBundleOver Z (F := M)) (𝟙 _) (by simp)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)).unit.app M ≫
        (Scheme.Modules.pushforward (𝟙 Z)).map ((Scheme.Modules.pullbackId Z).hom.app M ≫
          Scheme.Modules.vectorBundleClassifyingMap M (𝟙 _)) := by
    refine Eq.trans ?_ ((congrArg (· ≫ (Scheme.Modules.pushforward (𝟙 Z)).map
      (Scheme.Modules.vectorBundleClassifyingMap M (𝟙 _))) hu).symm.trans ?_)
    · rfl
    · exact (Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) ((Scheme.Modules.pushforward (𝟙 Z)).map_comp _ _).symm)
  have hV := Scheme.Modules.vectorBundleClassifyingMap_comp_vectorBundleMap
    ((Scheme.Modules.pullback (𝟙 Z)).obj M) (G := M)
    ((Scheme.Modules.pullbackId Z).hom.app M) (𝟙 _)
  rw [Category.id_comp] at hV
  have h1 := (Scheme.Modules.vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection
    (𝟙 Z) M (Scheme.Modules.vectorBundleMap Z (F := (Scheme.Modules.pullback (𝟙 Z)).obj M)
      (G := M) ((Scheme.Modules.pullbackId Z).hom.app M))).trans
    (congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)).unit.app M ≫
      (Scheme.Modules.pushforward (𝟙 Z)).map t) hV)
  have h := Scheme.Modules.vectorBundle_hom_ext M (h1.trans h2.symm)
  exact congrArg CommaMorphism.left h

/-- **A corank-one subbundle is an effective Cartier divisor.** Let `0 ⟶ ℒ ⟶ 𝒩^∨ ⟶ (𝒩')^∨ ⟶ 0`
be a short exact sequence of finite locally free modules with `ℒ` invertible. Then the closed
immersion `𝐕((𝒩')^∨) ⟶ 𝐕(𝒩^∨)` induced by `b : 𝒩^∨ ⟶ (𝒩')^∨` is an effective Cartier divisor:
over an affine open on which `ℒ` and `(𝒩')^∨` are free, `𝐕(𝒩^∨)` is a polynomial ring in which the
ideal of `𝐕((𝒩')^∨)` is generated by one of the variables. -/
theorem isEffectiveCartierDivisor_ker_vectorBundleMap_of_shortExact {X : Scheme.{u}}
    (N' N L : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (r' : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    (a : L ⟶ dualSheaf N) (b : dualSheaf N ⟶ dualSheaf N') (w : a ≫ b = 0)
    (hS : (ShortComplex.mk a b w).ShortExact) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.Modules.vectorBundleMap X (F := dualSheaf N) (G := dualSheaf N') b).left.ker := by
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have hdd := @Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_isIso_of_isFiniteLocallyFree X
  have := hdd L hL
  have := hdd N inferInstance
  have := hdd N' inferInstance
  have := hdd (dualSheaf N) (isFiniteLocallyFree_dualSheaf N inferInstance)
  have := hdd (dualSheaf N') (isFiniteLocallyFree_dualSheaf N' inferInstance)
  -- the dual of the canonical map of a reflexive module is the inverse canonical map
  have hdt : ∀ (F : X.Modules) [IsIso (toDoubleDual (dualSheaf F))],
      dualMap (toDoubleDual F) = inv (toDoubleDual (dualSheaf F)) := fun F _ =>
    IsIso.eq_inv_of_hom_inv_id (toDoubleDual_dualMap_comp F)
  -- the double dual of a map out of a module with invertible canonical map
  have hddm : ∀ {F G : X.Modules} [IsIso (toDoubleDual F)] (f : F ⟶ G),
      dualMap (dualMap f) = inv (toDoubleDual F) ≫ f ≫ toDoubleDual G := fun f =>
    (IsIso.eq_inv_comp _).mpr (toDoubleDual_naturality f).symm
  -- `N' ⊆ N` as the subbundle of an inclusion `N' ⟶ N` whose dual is `b`
  let inc : N' ⟶ N := toDoubleDual N' ≫ dualMap b ≫ inv (toDoubleDual N)
  have hdi : dualMap inc = b := by
    have h0 : dualMap (toDoubleDual N) ≫ dualMap (inv (toDoubleDual N)) = 𝟙 _ := by
      rw [← dualMap_comp, IsIso.inv_hom_id, dualMap_id]
    rw [hdt N, IsIso.inv_comp_eq, Category.comp_id] at h0
    simp only [inc, dualMap_comp, h0, hdt N']
    simp [hddm b]
  -- the quotient `N ⟶ L^∨` whose dual is `a`, up to `L ≅ L^∨∨`
  let pr : N ⟶ dualSheaf L := toDoubleDual N ≫ dualMap a
  have hdp : dualMap pr = inv (toDoubleDual L) ≫ a := by
    simp only [pr, dualMap_comp, hdt N]
    simp [hddm a]
  have w' : dualMap pr ≫ dualMap inc = 0 := by rw [hdp, hdi, Category.assoc, w, comp_zero]
  have hS' : (ShortComplex.mk (dualMap pr) (dualMap inc) w').ShortExact := by
    refine ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk a b w)
      (ShortComplex.isoMk (asIso (toDoubleDual L)) (Iso.refl _) (Iso.refl _) ?_ ?_) hS
    · simp [hdp]
    · simp [hdi]
  have : Epi (dualMap inc) := hS'.epi_g
  have : IsClosedImmersion (subbundleEmbedding N' N inc) :=
    @Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi X _ _ _ _ (dualMap inc) hS'.epi_g
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf L) :=
    isFiniteLocallyFree_dualSheaf L hL
  have key : Stacks.Divisors.IsEffectiveCartierDivisor (subbundleEmbedding N' N inc).ker := by
    refine (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor
      _).mpr fun x => ?_
    obtain ⟨U₁, hU₁, hb₁⟩ := exists_forall_isAffineOpen_basis_sections
      (dualSheaf (dualSheaf L)) 1 (dualVectorBundleToBase N x)
    obtain ⟨U₂, hU₂, hb₂⟩ := exists_forall_isAffineOpen_basis_sections (dualSheaf N') r'
      (dualVectorBundleToBase N x)
    obtain ⟨V, hV, hxV, hVU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (show dualVectorBundleToBase N x ∈ U₁ ⊓ U₂ from ⟨hU₁, hU₂⟩)
    obtain ⟨bK⟩ := hb₁ V hV fun y hy => (hVU hy).1
    obtain ⟨bP⟩ := hb₂ V hV fun y hy => (hVU hy).2
    obtain ⟨χ, hχX, -⟩ := exists_polyEquiv hV N' N (dualSheaf L) inc pr w' hS' bK bP
    refine ⟨bundlePreimage hV N, hxV, subbundleCosectionFn N (dualSheaf L) pr (bK 0), ?_, ?_⟩
    · have hreg := GenuineChern.isRegular_ringEquiv χ.symm
        (MvPolynomial.isRegular_X (n := (Sum.inl 0 : Fin 1 ⊕ Fin r')) (R := Γ(X, V)))
      rw [χ.symm_apply_eq.mpr (hχX 0).symm] at hreg
      exact isRegular_iff_mem_nonZeroDivisors.mp hreg
    · rw [ker_subbundleEmbedding_ideal_eq_span hV N' N (dualSheaf L) inc pr w' hS' bK]
      congr 1
      ext f
      simp only [Set.mem_range, Fin.exists_fin_one]
      exact ⟨fun h => h ▸ rfl, fun h => h.symm⟩
  have he : subbundleEmbedding N' N inc =
      (Scheme.Modules.vectorBundleMap X (F := dualSheaf N) (G := dualSheaf N') b).left := by
    rw [subbundleEmbedding, hdi]
  rw [← he]
  exact key

variable {Z Y X : Scheme.{u}} {i : Z ⟶ Y} {j : Y ⟶ X} [IsClosedImmersion i] [IsClosedImmersion j]
  (D : ConormalCompatibleVirtualNormalBundles i j) (hreg : IsRegularImmersion j)

/-- **`N' ⊆ N₁` is an effective Cartier divisor**, for the virtual normal bundles `𝒩₁` of
`Stacks.Chow.ConormalCompatibleVirtualNormalBundles.excessKernelBundle` and `𝒩'`, when `Y ⊆ X` is
a regular immersion of codimension one: the top row `0 ⟶ i^*𝒞_{Y/X}^∨∨ ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨ ⟶ 0`
of the reduced datum is short exact with invertible kernel. -/
theorem isEffectiveCartierDivisor_ker_vectorBundleMap_excessRight [IsLocallyNoetherian Y] (p : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule j) 1] :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.Modules.vectorBundleMap Z (F := dualSheaf (D.excessKernelBundle hreg).bundle)
        (G := dualSheaf D.bundleZY.bundle) (D.excessRight hreg)).left.ker :=
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj (dualSheaf (dualSheaf (conormalModule j)))) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i _ 1
  have := D.bundleZY.isFiniteLocallyFree
  have := (D.excessKernelBundle hreg).isFiniteLocallyFree
  isEffectiveCartierDivisor_ker_vectorBundleMap_of_shortExact D.bundleZY.bundle
    (D.excessKernelBundle hreg).bundle _ p (D.excessReductionDualLeft hreg) (D.excessRight hreg)
    (D.excessReductionDualLeft_comp_excessRight hreg)
    (D.shortExact_excessReductionDualLeft_excessRight hreg)

/-- **The square of cones and vector bundles of the proof of Stacks 0FEC**: the closed immersion
`ι' : C_ZY ⟶ N'` followed by `N' ⟶ N₁` is the comparison `C_ZY ⟶ C_ZX` of normal cones
(`Stacks.Chow.normalConeBaseChangeMap`) followed by `ι₁ : C_ZX ⟶ N₁`.

It is the compatibility of `ι` with base change
(`Stacks.Chow.normalConeBaseChangeMap_comp_normalConeEmbedding`) for the square
`Z ⟶ Y ⟶ X`, `Z ⟶ Z ⟶ X`, together with the right-hand square of the reduced datum
(`Stacks.Chow.ConormalCompatibleVirtualNormalBundles.excessRight_comp_surjection`), compared on
classifying maps. -/
theorem normalConeEmbedding_comp_vectorBundleMap_excessRight {S : Scheme.{u}} (sX : X ⟶ S) :
    D.bundleZY.normalConeEmbedding ≫
        (Scheme.Modules.vectorBundleMap Z (F := dualSheaf (D.excessKernelBundle hreg).bundle)
          (G := dualSheaf D.bundleZY.bundle) (D.excessRight hreg)).left =
      normalConeBaseChangeMap j sX (i ≫ j) i (ker_eq_comap_ker_of_comp_eq j (i ≫ j) i rfl) ≫
        (D.excessKernelBundle hreg).normalConeEmbedding := by
  have sq := Stacks.Immersion.conormalSequence_isPullback i j
  -- The lemmas used below are stated over `[IsClosedImmersion _]`, so they spell the instance
  -- `IsImmersion (i ≫ j)` of `D.excessKernelBundle hreg` differently from its own type. `key` and
  -- `key2` compare the two spellings at `vectorBundleMap` and `conormalDegreeOneSurjection`, where
  -- the comparison is cheap, rather than inside a composite, where it unfolds `vectorBundleMap`.
  have key : ∀ φ, φ = Scheme.Modules.vectorBundleMap Z
        (D.excessKernelBundle hreg).conormalDegreeOneSurjection →
      (normalConeBaseChangeOver sX (i ≫ j) i (𝟙 Z) j sq ≫ normalConeToNormalBundleOver (i ≫ j) ≫
        φ).left =
      normalConeBaseChangeMap j sX (i ≫ j) i (ker_eq_comap_ker_of_comp_eq j (i ≫ j) i rfl) ≫
        (D.excessKernelBundle hreg).normalConeEmbedding := by
    rintro φ rfl
    rfl
  let M₁ := dualSheaf (D.excessKernelBundle hreg).bundle
  let b' : (Scheme.Modules.pullback (𝟙 Z)).obj M₁ ⟶ dualSheaf D.bundleZY.bundle :=
    (Scheme.Modules.pullbackId Z).hom.app M₁ ≫ D.excessRight hreg
  let k := (normalConeToNormalBundleOver i ≫
    Scheme.Modules.vectorBundleMap Z D.bundleZY.conormalDegreeOneSurjection) ≫
      Scheme.Modules.vectorBundleMap Z (F := (Scheme.Modules.pullback (𝟙 Z)).obj M₁)
        (G := dualSheaf D.bundleZY.bundle) b'
  -- the two surjections onto `𝒞_{Z/Y}`
  have hσ : pullbackDualMap (𝟙 Z) (D.excessKernelBundle hreg).bundle ≫
      ((D.excessKernelBundle hreg).baseChange (i ≫ j) i (𝟙 Z) j sq).surjection =
      (Scheme.Modules.pullback (𝟙 Z)).map (D.excessKernelBundle hreg).surjection ≫
        Stacks.Immersion.immersionConormalSheafMap i (i ≫ j) (𝟙 Z) j
          (Stacks.Immersion.toShHom_square sq.w) := by
    rw [VirtualNormalBundle.baseChange_surjection]
    exact Iso.hom_inv_id_assoc (@asIso _ _ _ _ (pullbackDualMap (𝟙 Z) _)
      (pullbackDualMap_isIso (𝟙 Z) _ (D.excessKernelBundle hreg).isFiniteLocallyFree)) _
  have hb : b' ≫ D.bundleZY.surjection =
      pullbackDualMap (𝟙 Z) (D.excessKernelBundle hreg).bundle ≫
        ((D.excessKernelBundle hreg).baseChange (i ≫ j) i (𝟙 Z) j sq).surjection := by
    refine Eq.trans ?_ hσ.symm
    have e1 : (Scheme.Modules.pullbackId Z).hom.app M₁ ≫ (D.excessKernelBundle hreg).surjection =
        (Scheme.Modules.pullback (𝟙 Z)).map (D.excessKernelBundle hreg).surjection ≫
          (Scheme.Modules.pullbackId Z).hom.app _ :=
      ((Scheme.Modules.pullbackId Z).hom.naturality (D.excessKernelBundle hreg).surjection).symm
    have e2 := ((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
      (Stacks.Conormal.conormalSheaf (i ≫ j))).hom_inv_id
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (D.excessRight_comp_surjection hreg)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e1).trans ?_)
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e2).trans ?_)
    exact Category.id_comp _
  have hb' : b' ≫ D.bundleZY.conormalDegreeOneSurjection =
      pullbackDualMap (𝟙 Z) (D.excessKernelBundle hreg).bundle ≫
        ((D.excessKernelBundle hreg).baseChange (i ≫ j) i (𝟙 Z) j sq).conormalDegreeOneSurjection :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans (Category.assoc _ _ _))
  -- the classifying maps of the two morphisms `C_ZY ⟶ N₁` over `Z`
  have hL := (Scheme.Modules.vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection
    (𝟙 Z) M₁ k).trans (congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction
      (𝟙 Z)).unit.app M₁ ≫ (Scheme.Modules.pushforward (𝟙 Z)).map t)
      ((Scheme.Modules.vectorBundleClassifyingMap_comp_vectorBundleMap _ b' _).trans
        (congrArg (b' ≫ ·) (vectorBundleClassifyingMap_normalConeEmbedding D.bundleZY))))
  have hR := (Scheme.Modules.vectorBundleClassifyingMap_comp _
    (normalConeBaseChangeOver sX (i ≫ j) i (𝟙 Z) j sq) _).trans
    ((congrArg (· ≫ _) (vectorBundleClassifyingMap_normalConeEmbedding
      (D.excessKernelBundle hreg))).trans
    (conormalDegreeOneSurjection_comp_pushforwardAlgebraMap_normalConeBaseChangeOver sX (i ≫ j) i
      (𝟙 Z) j sq (D.excessKernelBundle hreg)))
  have key2 : ∀ φ, φ = ((D.excessKernelBundle hreg).baseChange (i ≫ j) i (𝟙 Z) j
        sq).conormalDegreeOneSurjection →
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)).unit.app M₁ ≫
        (Scheme.Modules.pushforward (𝟙 Z)).map ((b' ≫ D.bundleZY.conormalDegreeOneSurjection ≫
          conormalDegreeOneIncl i ≫ RelativeSpec.AlgebraSheaf.underlyingModuleMap
            (AffineAlgebraEquivalence.pushforwardAlgebraIso
              (Stacks.Conormal.conormalAlgebraSheaf i)).inv :) : _ ⟶
            RelativeSpec.AlgebraSheaf.underlyingModule (AffineAlgebraEquivalence.pushforwardAlgebra
              (Over.mk (Stacks.Conormal.normalConeToBase i)).hom)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)).unit.app
          (dualSheaf (D.excessKernelBundle hreg).bundle) ≫
        (Scheme.Modules.pushforward (𝟙 Z)).map
          (pullbackDualMap (𝟙 Z) (D.excessKernelBundle hreg).bundle ≫ φ ≫
            conormalDegreeOneIncl i ≫ RelativeSpec.AlgebraSheaf.underlyingModuleMap
              (AffineAlgebraEquivalence.pushforwardAlgebraIso
                (Stacks.Conormal.conormalAlgebraSheaf i)).inv) := by
    rintro φ rfl
    refine congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Z)).unit.app M₁ ≫
      (Scheme.Modules.pushforward (𝟙 Z)).map t) ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb').trans (Category.assoc _ _ _))
  have hLR := (hL.trans (key2 _ (by rfl))).trans hR.symm
  have h := congrArg Over.Hom.left (Scheme.Modules.vectorBundle_hom_ext M₁ hLR)
  have hk : ((Over.map (𝟙 Z)).map k ≫
      Scheme.Modules.vectorBundlePullbackProjection (𝟙 Z) M₁).left =
      D.bundleZY.normalConeEmbedding ≫
        (Scheme.Modules.vectorBundleMap Z (F := dualSheaf (D.excessKernelBundle hreg).bundle)
          (G := dualSheaf D.bundleZY.bundle) (D.excessRight hreg)).left := by
    have e : (Scheme.Modules.vectorBundleMap Z (F := (Scheme.Modules.pullback (𝟙 Z)).obj M₁)
        (G := dualSheaf D.bundleZY.bundle) b').left =
        (Scheme.Modules.vectorBundleMap Z (F := dualSheaf (D.excessKernelBundle hreg).bundle)
          (G := dualSheaf D.bundleZY.bundle) (D.excessRight hreg)).left ≫
        (Scheme.Modules.vectorBundleMap Z (F := (Scheme.Modules.pullback (𝟙 Z)).obj M₁)
          (G := M₁) ((Scheme.Modules.pullbackId Z).hom.app M₁)).left :=
      congrArg CommaMorphism.left (Scheme.Modules.vectorBundleMap_comp Z
        (F := (Scheme.Modules.pullback (𝟙 Z)).obj M₁) (G := M₁)
        (H := dualSheaf D.bundleZY.bundle) ((Scheme.Modules.pullbackId Z).hom.app M₁)
        (D.excessRight hreg))
    have hk1 : ((Over.map (𝟙 Z)).map k ≫
        Scheme.Modules.vectorBundlePullbackProjection (𝟙 Z) M₁).left =
        (D.bundleZY.normalConeEmbedding ≫
          (Scheme.Modules.vectorBundleMap Z (F := (Scheme.Modules.pullback (𝟙 Z)).obj M₁)
            (G := dualSheaf D.bundleZY.bundle) b').left) ≫
        (Scheme.Modules.vectorBundlePullbackProjection (𝟙 Z) M₁).left := rfl
    rw [hk1, e]
    exact (Category.assoc D.bundleZY.normalConeEmbedding _
        (Scheme.Modules.vectorBundlePullbackProjection (𝟙 Z) M₁).left).trans
      (congrArg (D.bundleZY.normalConeEmbedding ≫ ·) ((Category.assoc
        (Scheme.Modules.vectorBundleMap Z (F := dualSheaf (D.excessKernelBundle hreg).bundle)
          (G := dualSheaf D.bundleZY.bundle) (D.excessRight hreg)).left
        (Scheme.Modules.vectorBundleMap Z (F := (Scheme.Modules.pullback (𝟙 Z)).obj M₁)
          (G := M₁) ((Scheme.Modules.pullbackId Z).hom.app M₁)).left
        (Scheme.Modules.vectorBundlePullbackProjection (𝟙 Z) M₁).left).trans
        ((congrArg ((Scheme.Modules.vectorBundleMap Z
            (F := dualSheaf (D.excessKernelBundle hreg).bundle)
            (G := dualSheaf D.bundleZY.bundle) (D.excessRight hreg)).left ≫ ·)
          (vectorBundleMap_pullbackId_hom_comp_vectorBundlePullbackProjection M₁)).trans
          (Category.comp_id _))))
  exact (hk.symm.trans h).trans (key _ rfl)

end Subbundle

/-! ### The Cartier case of Stacks 0FEC -/

/-- **An effective Cartier divisor is a regular closed immersion of codimension one**: its ideal
is locally generated by a single nonzerodivisor (Stacks 01WS). -/
@[ega "IV 21.2.12"]
theorem isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor {Y X : Scheme.{u}}
    (j : Y ⟶ X) [IsClosedImmersion j] (hj : Stacks.Divisors.IsEffectiveCartierDivisor j.ker) :
    IsRegularClosedImmersionOfCodim j 1 := by
  rw [isRegularClosedImmersionOfCodim_iff_kerGeneratedBy]
  intro x _
  obtain ⟨V, hxV, t, ht, hgen⟩ :=
    (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor j.ker).mp hj x
  refine ⟨V, hxV, 1, fun _ => t, ?_, rfl, ?_⟩
  · rw [← Scheme.Hom.ker_apply j V, hgen, Set.range_const]
  · rw [show List.ofFn (fun _ : Fin 1 => t) = [t] from rfl]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ t).mpr
      (isRegular_iff_mem_nonZeroDivisors.mpr ht).left


/-- **The Cartier case of the proof of Stacks 0FEC** (`Stacks.Chow.CompositionCartierCase`), for
one triple `D`. Let `X` be integral and `Y ⊆ X` an effective Cartier divisor, and let
`N₁ = 𝐕(𝒩₁^∨)`, for the virtual normal bundle `𝒩₁` of
`Stacks.Chow.ConormalCompatibleVirtualNormalBundles.excessKernelBundle`, and `N' = 𝐕((𝒩')^∨)`.
Given `Ψ : N₁ ⟶ C_YX` and `ν : N' ⟶ N₁` with the properties of the source (see the
implementation notes), the composition formula holds on `[X]_k` in every degree `k`:

  `c(Z ⟶ X, 𝒩) ∩ [X]_k = c(Z ⟶ Y, 𝒩') ∩ c(Y ⟶ X, 𝒩'') ∩ [X]_k`.

By `ConormalCompatibleVirtualNormalBundles.virtualNormalGysinClass_cap_heq_of_excessReduction`
it suffices to treat `𝒩₁`, `𝒩'`, `𝒞_{Y/X}^∨`, which is
`Stacks.Chow.virtualNormalGysinClass_cap_fundamentalChowClass_heq_of_changeOfCentre` in the degree
`n = dim_δ(X)`; in every other degree `[X]_k = 0`. -/
theorem compositionFormulaAt_fundamentalChowClass_of_isEffectiveCartierDivisor
    (C : ChowSituation.{u}) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {i : Z ⟶ Y} {j : Y ⟶ X} [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ)
    (hj : j ≫ sX = sY) (D : ConormalCompatibleVirtualNormalBundles i j) (p q : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]
    [IsIntegral X] (hY : Stacks.Divisors.IsEffectiveCartierDivisor j.ker)
    (hreg : IsRegularImmersion j)
    (Ψ : (D.excessKernelBundle hreg).totalSpace ⟶ Stacks.Conormal.normalCone j)
    (hΨ₀ : Ψ ≫ Stacks.Conormal.normalConeToBase j = (D.excessKernelBundle hreg).projection ≫ i)
    (hΨ : (D.excessKernelBundle hreg).normalConeEmbedding ≫ Ψ =
      normalConeChangeOfCentreMap (i ≫ j) j (Scheme.Hom.le_ker_comp i j))
    (ν : D.bundleZY.totalSpace ⟶ (D.excessKernelBundle hreg).totalSpace)
    (hν : IsPullback ν (D.bundleZY.projection ≫ i) Ψ (normalConeZeroSection j))
    (hcone : D.bundleZY.normalConeEmbedding ≫ ν =
      normalConeBaseChangeMap j sX (i ≫ j) i (ker_eq_comap_ker_of_comp_eq j (i ≫ j) i rfl) ≫
        (D.excessKernelBundle hreg).normalConeEmbedding)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor ((normalConeZeroSectionIdeal j).comap Ψ))
    (k : ℤ) :
    CompositionFormulaAt C sZ sY sX hi hj D p q (𝟙 X) k (fundamentalChowClass C (𝟙 X ≫ sX) k) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : Stacks.Divisors.IsEffectiveCartierDivisor j.ker := hY
  have := (isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor j
    hY).isFiniteLocallyFreeOfRank_conormalModule
  by_cases hk : relativeDimension C.dimensionFunction (𝟙 X ≫ sX) (genericPoint X) = k
  · subst hk
    have hX : schemeDeltaDimension C sX ≤
        ((relativeDimension C.dimensionFunction (𝟙 X ≫ sX) (genericPoint X) : ℤ) : EInt) := by
      rw [schemeDeltaDimension_eq_genericPoint, Category.id_comp]
    unfold CompositionFormulaAt compositeVirtualNormalGysinClass
    exact eq_of_heq ((D.virtualNormalGysinClass_cap_heq_of_excessReduction C sZ sY sX hi hj hreg
      p q 1 (𝟙 X) _ _ (virtualNormalGysinClass_cap_fundamentalChowClass_heq_of_changeOfCentre C sZ
        sY sX hi hj (D.excessKernelBundle hreg) D.bundleZY p Ψ hΨ₀ hΨ ν hν hcone hcart hreg _
        hX)).trans (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ _ _ _).symm)
  · unfold CompositionFormulaAt
    rw [fundamentalChowClass_eq_zero_of_ne C (𝟙 X ≫ sX) hk, map_zero, map_zero]

/-- **The Cartier case of the proof of Stacks 0FEC, from the change of centre `Ψ`.** The form of
`Stacks.Chow.compositionFormulaAt_fundamentalChowClass_of_isEffectiveCartierDivisor` for the
embedding `N' ⟶ N₁` induced by the right-hand map `𝒩₁^∨ ⟶ (𝒩')^∨` of the reduced datum: given
`Ψ : N₁ ⟶ C_YX` over `Z ⟶ Y`, restricting to the change of centre on `C_ZX`, with `N'` the
inverse image of the zero section, the composition formula holds on `[X]_k` in every degree. The
square of cones is `Stacks.Chow.normalConeEmbedding_comp_vectorBundleMap_excessRight`, and `N'` is
an effective Cartier divisor of `N₁` by
`Stacks.Chow.isEffectiveCartierDivisor_ker_vectorBundleMap_excessRight`. -/
theorem compositionFormulaAt_fundamentalChowClass_of_normalConeMap
    (C : ChowSituation.{u}) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {i : Z ⟶ Y} {j : Y ⟶ X} [IsClosedImmersion i] [IsClosedImmersion j] (hi : i ≫ sY = sZ)
    (hj : j ≫ sX = sY) (D : ConormalCompatibleVirtualNormalBundles i j) (p q : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleZY.bundle p]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.bundleYX.bundle q]
    [IsIntegral X] (hY : Stacks.Divisors.IsEffectiveCartierDivisor j.ker)
    (hreg : IsRegularImmersion j)
    (Ψ : (D.excessKernelBundle hreg).totalSpace ⟶ Stacks.Conormal.normalCone j)
    (hΨ₀ : Ψ ≫ Stacks.Conormal.normalConeToBase j = (D.excessKernelBundle hreg).projection ≫ i)
    (hΨ : (D.excessKernelBundle hreg).normalConeEmbedding ≫ Ψ =
      normalConeChangeOfCentreMap (i ≫ j) j (Scheme.Hom.le_ker_comp i j))
    (hν : IsPullback (Scheme.Modules.vectorBundleMap Z
        (F := dualSheaf (D.excessKernelBundle hreg).bundle) (G := dualSheaf D.bundleZY.bundle)
        (D.excessRight hreg)).left (D.bundleZY.projection ≫ i) Ψ (normalConeZeroSection j))
    (k : ℤ) :
    CompositionFormulaAt C sZ sY sX hi hj D p q (𝟙 X) k (fundamentalChowClass C (𝟙 X ≫ sX) k) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := (isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor j
    hY).isFiniteLocallyFreeOfRank_conormalModule
  have hker := ker_eq_comap_of_isPullback Ψ hν
  rw [ker_normalConeZeroSection] at hker
  exact compositionFormulaAt_fundamentalChowClass_of_isEffectiveCartierDivisor C sZ sY sX hi hj D
    p q hY hreg Ψ hΨ₀ hΨ _ hν (normalConeEmbedding_comp_vectorBundleMap_excessRight D hreg sX)
    (hker ▸ isEffectiveCartierDivisor_ker_vectorBundleMap_excessRight D hreg p) k

end Stacks.Chow

end

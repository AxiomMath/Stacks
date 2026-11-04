module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Construction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ChowSteps
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNormalBundleIso
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSymmetricIso
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.CompositeCaps

/-!
# The Gysin class of a regular immersion on the fundamental class

Let `(S, δ)` be as in Situation 02QL, let `i : Z ⟶ X` be a regular closed immersion of schemes
locally of finite type over `S` whose conormal sheaf has constant rank `r`, and let
`i^! = c(Z ⟶ X, 𝒩_{Z/X})` be the class of Stacks 0FBK of its normal sheaf. If
`dim_δ(X) ≤ n` and `dim_δ(Z) ≤ n - r`, then

  `i^![X]_n = [Z]_{n-r}`.

This is the case `Y = X` of Stacks 0FBM, where the excess normal sheaf is zero; it is the input of
the case `Y' = Y` of Stacks 0FF7, which Stacks 0FF8 (b) uses.

## The argument

The source's: `c = c(Z ⟶ X, 𝒩)` is characterized by `p^* (c ∩ α) = ι_* j^*(C ∩ α)` with
`p : N ⟶ Z` the normal bundle, and `p^*` is injective (Stacks 02TY). On `α = [X]_n`:

* `C ∩ [X]_n = [W_∞]_n` restricted to the open `D = W ∖ X'`, that is the fundamental class of the
  special fibre `Z(t⁻¹) = C_ZX` of the deformation space
  (`Stacks.Chow.GysinAtInfinity.infinityCap_id_fundamentalChowClass`): `[D]_{n+1}` lifts
  `[X]_n`, and `t⁻¹` is a nonzerodivisor;
* for a regular immersion `C_ZX ⟶ N` is an isomorphism: `Sym(𝒞_{Z/X}) ⟶ ⊕ ℐⁿ/ℐⁿ⁺¹` is an
  isomorphism by Stacks 063M (3), and `𝒩^∨ ⟶ 𝒞_{Z/X}` is an isomorphism; so `ι_*[C_ZX]_n = [N]_n`;
* `[N]_n = p^*[Z]_{n-r}` (Stacks 02RE), and `p^*` is injective.

The δ-dimension of the deformation space is at most `n + 1`: away from the special fibre it is
flat of relative dimension one over `X`, and the special fibre is `N`, of δ-dimension at most
`n`.

## Main results

All names below are in the namespace `Stacks.Chow.VirtualNormalBundle`.

* `isIso_specialFibreEmbedding_of_isIso`, `isIso_specialFibreEmbedding_ofIsRegularImmersion` —
  the closed immersion `C_ZX ⟶ N` is an isomorphism for a quasi-regular immersion and a virtual
  normal bundle whose structural map is an isomorphism, for instance the normal sheaf of a regular
  immersion.
* `virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection`,
  `virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection_of_isIso` —
  `c(Z ⟶ X, 𝒩) ∩ [X]_n = [Z]_{n-r}`.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow.VirtualNormalBundle

section Iso

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X) [IsImmersion i]
  (hi : IsRegularImmersion i)

/-- For a regular immersion the structural map `𝒩^∨ ⟶ 𝒞_{Z/X,1}` of the normal sheaf, read in
degree one of the conormal algebra, is an isomorphism. -/
instance isIso_surjectionDegreeOne_ofIsRegularImmersion :
    IsIso (VirtualNormalBundle.ofIsRegularImmersion i hi).surjectionDegreeOne := by
  unfold surjectionDegreeOne
  rw [VirtualNormalBundle.ofIsRegularImmersion_surjection]
  unfold regularNormalSurjection
  exact Iso.isIso_hom ((conormalReflexiveIso i hi).symm ≪≫
    Stacks.Conormal.immersionConormalSheafIsoDegreeOne i)

omit [IsLocallyNoetherian Z] in
/-- **For a quasi-regular immersion and a virtual normal bundle whose structural map is an
isomorphism, the closed immersion `C_ZX ⟶ N` is an isomorphism**: `C_ZX ⟶ N_ZX` is, by Stacks 063M
(3), and `N_ZX ⟶ N` is the vector bundle map of an isomorphism. -/
theorem isIso_specialFibreEmbedding_of_isIso (𝒩 : VirtualNormalBundle i) [IsIso 𝒩.surjection]
    (hQ : IsQuasiRegularImmersion i) : IsIso 𝒩.specialFibreEmbedding := by
  have : IsIso (Stacks.Conormal.normalConeToNormalBundle i) :=
    Stacks.Conormal.isIso_normalConeToNormalBundle i
      fun n => Stacks.Conormal.isIso_conormalSymmetricHom_app i hQ n
  have : IsIso 𝒩.surjectionDegreeOne := by
    unfold surjectionDegreeOne
    exact Iso.isIso_hom (asIso 𝒩.surjection ≪≫ Stacks.Conormal.immersionConormalSheafIsoDegreeOne i)
  set e := asIso 𝒩.surjectionDegreeOne
  have hiso : IsIso (Scheme.Modules.vectorBundleMap Z e.hom) :=
    ⟨⟨Scheme.Modules.vectorBundleMap Z e.inv,
      (Scheme.Modules.vectorBundleMap_comp Z e.inv e.hom).symm.trans
        ((congrArg (Scheme.Modules.vectorBundleMap Z) e.inv_hom_id).trans
          (Scheme.Modules.vectorBundleMap_id Z)),
      (Scheme.Modules.vectorBundleMap_comp Z e.hom e.inv).symm.trans
        ((congrArg (Scheme.Modules.vectorBundleMap Z) e.hom_inv_id).trans
          (Scheme.Modules.vectorBundleMap_id Z))⟩⟩
  have : IsIso 𝒩.bundleEmbedding :=
    inferInstanceAs (IsIso ((Over.forget Z).map (Scheme.Modules.vectorBundleMap Z e.hom)))
  unfold specialFibreEmbedding coneEmbedding
  infer_instance

/-- The structural map of the normal sheaf of a regular immersion is an isomorphism. -/
instance isIso_surjection_ofIsRegularImmersion :
    IsIso (VirtualNormalBundle.ofIsRegularImmersion i hi).surjection := by
  rw [VirtualNormalBundle.ofIsRegularImmersion_surjection]
  unfold regularNormalSurjection
  exact Iso.isIso_inv (conormalReflexiveIso i hi)

/-- **For a regular immersion the closed immersion `C_ZX ⟶ N` of the normal cone into the normal
bundle is an isomorphism**: `C_ZX ⟶ N_ZX` is, by Stacks 063M (3), and `N_ZX ⟶ N` is the vector
bundle map of an isomorphism. -/
theorem isIso_specialFibreEmbedding_ofIsRegularImmersion :
    IsIso (VirtualNormalBundle.ofIsRegularImmersion i hi).specialFibreEmbedding := by
  have hQ : IsQuasiRegularImmersion i :=
    isQuasiRegularImmersion_of_isH1RegularImmersion i
      (isH1RegularImmersion_of_isKoszulRegularImmersion i
        (isKoszulRegularImmersion_of_isRegularImmersion i hi))
  exact isIso_specialFibreEmbedding_of_isIso i (VirtualNormalBundle.ofIsRegularImmersion i hi) hQ

end Iso

section Dimension

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] {i : Z ⟶ X} [IsClosedImmersion i]
  (𝒩 : VirtualNormalBundle i) [IsIso 𝒩.surjection]
  (hQ : IsQuasiRegularImmersion i) (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    𝒩.bundle r]

include 𝒩 hQ

omit [IsLocallyNoetherian Z] in
include hZ in
/-- For a regular immersion with `dim_δ(Z) ≤ k - r`, the special fibre `Z(t⁻¹) ≅ N` of the
deformation space has δ-dimension at most `k`. -/
theorem schemeDeltaDimension_specialFibre_le (k : ℤ)
    (hZd : schemeDeltaDimension C sZ ≤ ((k - r : ℤ) : EInt)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    schemeDeltaDimension C ((Stacks.Deformation.specialFibre i).subschemeι ≫
      (Stacks.Deformation.deformationProjection i ≫ sX)) ≤ (k : EInt) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  have := isIso_specialFibreEmbedding_of_isIso _ 𝒩 hQ
  have hN := Stacks.Chow.SectionZeroScheme.schemeDeltaDimension_le_of_flat C sZ 𝒩.proj r
    (𝒩.relativeDimension_projection r) hZd
  have he : (Stacks.Deformation.specialFibre i).subschemeι ≫
      (Stacks.Deformation.deformationProjection i ≫ sX) =
      𝒩.specialFibreEmbedding ≫ (𝒩.proj ≫ sZ) := by
    rw [← Category.assoc, ← 𝒩.specialFibreEmbedding_projection_comp, ← hZ]
    simp only [Category.assoc]
  rw [schemeDeltaDimension_congr C he]
  refine (schemeDeltaDimension_le_of_isClosedImmersion C (𝒩.proj ≫ sZ)
    𝒩.specialFibreEmbedding hN).trans ?_
  exact WithBotTop.coe_le_coe.mpr (by omega)

omit [IsLocallyNoetherian Z] in
include hZ in
/-- For a regular immersion with `dim_δ(X) ≤ k` and `dim_δ(Z) ≤ k - r`, the deformation space has
δ-dimension at most `k + 1`: away from the special fibre it is flat of relative dimension one over
`X`, and the special fibre has δ-dimension at most `k`. -/
theorem schemeDeltaDimension_deformationSpace_le (k : ℤ)
    (hX : schemeDeltaDimension C sX ≤ (k : EInt))
    (hZd : schemeDeltaDimension C sZ ≤ ((k - r : ℤ) : EInt)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    schemeDeltaDimension C (Stacks.Deformation.deformationProjection i ≫ sX) ≤
      ((k + 1 : ℤ) : EInt) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have hS := schemeDeltaDimension_specialFibre_le 𝒩 hQ C sX sZ hZ r k hZd
  have hU := Stacks.Chow.SectionZeroScheme.schemeDeltaDimension_le_of_flat C sX
    ((Stacks.Deformation.complementOpen (Stacks.Conormal.coborderIdeal i)).ι ≫
      Stacks.Deformation.deformationProjection i) 1
    (Stacks.Deformation.relativeDimension_complementOpen_deformationProjection i) hX
  have hpt : ∀ z, relativeDimension C.dimensionFunction
      (Stacks.Deformation.deformationProjection i ≫ sX) z ≤ k + 1 := by
    intro z
    by_cases hz : z ∈ Set.range
        (Stacks.Deformation.complementOpen (Stacks.Conormal.coborderIdeal i)).ι.base
    · obtain ⟨w, rfl⟩ := hz
      have h1 := relativeDimension_le_of_schemeDeltaDimension_le' C _ hU w
      rw [Category.assoc, relativeDimension_comp_isOpenImmersion] at h1
      simpa using h1
    · have hz' : z ∈ Set.range (Stacks.Deformation.specialFibre i).subschemeι.base := by
        rw [Stacks.Deformation.range_zeroScheme_paramGlobal]; exact hz
      obtain ⟨w, rfl⟩ := hz'
      have h1 := relativeDimension_le_of_schemeDeltaDimension_le' C _ hS w
      rw [relativeDimension_comp_closedImmersion] at h1
      omega
  have h := schemeDeltaDimension_le_of_forall_point C
    (Stacks.Deformation.deformationProjection i ≫ sX)
    (𝟙 (Stacks.Deformation.deformationSpace (Stacks.Conormal.coborderIdeal i)))
    (k := k + 1) fun z => by simpa using hpt z
  exact (schemeDeltaDimension_congr C (Category.id_comp _)).symm.trans_le h

end Dimension

section Cone

/-- A transported class takes a fundamental class to a fundamental class if the original does. -/
theorem copy_cap_eq_fundamentalChowClass (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hff' : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) {p p' : ℤ} (hpp' : p = p')
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k)
    (h : c.cap g k α = fundamentalChowClass C (pullback.fst f g ≫ sX) (k - p)) :
    (BivariantClass.copy C G sX sY hff' hf hf' hpp' c).cap g k α =
      fundamentalChowClass C (pullback.fst f' g ≫ sX) (k - p') := by
  subst hff'
  subst hpp'
  exact h

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] {i : Z ⟶ X} [IsClosedImmersion i]
  (𝒩 : VirtualNormalBundle i) [IsIso 𝒩.surjection]
  (hQ : IsQuasiRegularImmersion i) (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    𝒩.bundle r]

include 𝒩 hQ

omit [IsLocallyNoetherian Z] in
/-- **`ι_* j^*(C ∩ [X]_k) = [N]_k`** for a regular immersion: the class at infinity takes `[X]_k`
to the fundamental class of the special fibre `C_ZX`, and `ι : C_ZX ⟶ N` is an isomorphism. -/
theorem pushforwardClass_cap_fundamentalChowClass (k : ℤ)
    (hX : schemeDeltaDimension C sX ≤ (k : EInt))
    (hZd : schemeDeltaDimension C sZ ≤ ((k - r : ℤ) : EInt)) :
    haveI := 𝒩.locallyOfFiniteType_projection r
    (𝒩.pushforwardClass C sX sZ hZ r).cap (𝟙 X) k
        (fundamentalChowClass C (𝟙 X ≫ sX) k) =
      fundamentalChowClass C (pullback.fst (𝒩.proj ≫
        i) (𝟙 X) ≫ (𝒩.proj ≫ sZ))
        (k - (-(r : ℤ) + r)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := 𝒩.locallyOfFiniteType_projection r
  have := isIso_specialFibreEmbedding_of_isIso _ 𝒩 hQ
  have hcone := Stacks.Chow.GysinAtInfinity.infinityCap_id_fundamentalChowClass C sX
    (Stacks.Deformation.deformationProjection i)
    (Stacks.Deformation.complementOpen (Stacks.Conormal.coborderIdeal i)).ι
    (Stacks.Deformation.relativeDimension_complementOpen_deformationProjection i)
    (Scheme.unitModule (Stacks.Deformation.deformationSpace (Stacks.Conormal.coborderIdeal i)))
    (Stacks.Deformation.paramGlobal (Stacks.Conormal.coborderIdeal i))
    (Stacks.Deformation.range_zeroScheme_paramGlobal (Stacks.Conormal.coborderIdeal i))
    (Stacks.Chow.isTrivial_pullback_unitModule _) k hX
    (schemeDeltaDimension_deformationSpace_le 𝒩 hQ C sX sZ hZ r k hX hZd)
    (Stacks.Deformation.isEffectiveCartierDivisor_zeroScheme_paramGlobal _)
  unfold pushforwardClass
  refine copy_cap_eq_fundamentalChowClass C _ _ _ rfl _ _ _ _ (𝟙 X) k _ ?_
  rw [canonicalBivariantProperPushforward_cap]
  refine (congrArg (properChowPushforward C _ _ _ _ _ _)
    (copy_cap_eq_fundamentalChowClass C _ _ _ _ _ _ _ (Stacks.Deformation.normalConeClass C sX i)
      (𝟙 X) k _ hcone)).trans ?_
  have : IsIso (bivariantPushforwardBaseChange
      𝒩.specialFibreEmbedding
      (𝒩.proj ≫ i) (𝟙 X)) := by
    unfold bivariantPushforwardBaseChange
    infer_instance
  exact properChowPushforward_fundamentalChowClass_of_isIso C _ _ _ _ _ _

omit [IsLocallyNoetherian Z] in
/-- **`i^![X]_k = [Z]_{k-r}` for a regular closed immersion** (Stacks 0FBM at vanishing excess,
`Y = X`). Let `i : Z ⟶ X` be a regular closed immersion of schemes locally of finite type over
`S` whose normal sheaf `𝒩_{Z/X}` has constant rank `r`, and let `c(Z ⟶ X, 𝒩_{Z/X})` be the class
of Stacks 0FBK. If `dim_δ(X) ≤ k` and `dim_δ(Z) ≤ k - r`, then `c(Z ⟶ X, 𝒩_{Z/X}) ∩ [X]_k` is the
fundamental class `[Z]_{k-r}`, read on `Z ×_X X` (the cap operation at the test scheme `𝟙 X`). -/
theorem virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection (k : ℤ)
    (hX : schemeDeltaDimension C sX ≤ (k : EInt))
    (hZd : schemeDeltaDimension C sZ ≤ ((k - r : ℤ) : EInt)) :
    (𝒩.virtualNormalClass C sX sZ hZ r).cap (𝟙 X) k
        (fundamentalChowClass C (𝟙 X ≫ sX) k) =
      fundamentalChowClass C (pullback.fst i (𝟙 X) ≫ sZ) (k - r) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := 𝒩.locallyOfFiniteType_projection r
  have := 𝒩.flat_projection r
  apply (𝒩.middleCap_pullbackClass_bijective C sZ r
    (𝟙 X) (k - r)).1
  rw [middleCap_virtualNormalClass_cap, pushforwardClass_cap_fundamentalChowClass 𝒩 hQ C sX sZ hZ r
    k hX hZd, chowGroupDegreeEquiv_fundamentalChowClass, middleCap_apply]
  have hdim : schemeDeltaDimension C (pullback.fst i (𝟙 X) ≫ sZ) ≤ ((k - r : ℤ) : EInt) := by
    have : IsIso (pullback.fst i (𝟙 X)) := inferInstance
    exact (schemeDeltaDimension_comp_iso C (asIso (pullback.fst i (𝟙 X))) sZ).trans_le hZd
  symm
  refine (congrArg (properChowPushforward C _ _ _ _ _ _) ?_).trans
    (properChowPushforward_fundamentalChowClass_of_isIso C _ _ _ _ _ _)
  refine (flatPullbackBivariantCap_apply C _ _ _ rfl r
    (𝒩.relativeDimension_projection r)
    (flatPullbackDescends C) _ _ _).trans ?_
  refine (congrArg (chowGroupDegreeEquiv C _ _)
    (flatPullbackChow_fundamentalChowClass C _ _ _ _ r _ _ _ hdim)).trans ?_
  exact chowGroupDegreeEquiv_fundamentalChowClass C _ _

omit [IsLocallyNoetherian Z] in
/-- **`i^![T]_k = [Z ×_X T]_{k-r}` at a test scheme isomorphic to `X`.** The case `T = X` is
`virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection`; an isomorphism of test schemes
moves fundamental classes to fundamental classes on both sides (Stacks 0B76 (1)). -/
theorem virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection_of_isIso
    {T : Scheme.{u}} (t : T ⟶ X) [IsIso t] [LocallyOfFiniteType t] (k : ℤ)
    (hX : schemeDeltaDimension C sX ≤ (k : EInt))
    (hZd : schemeDeltaDimension C sZ ≤ ((k - r : ℤ) : EInt)) :
    (𝒩.virtualNormalClass C sX sZ hZ r).cap t k
        (fundamentalChowClass C (t ≫ sX) k) =
      fundamentalChowClass C (pullback.fst i t ≫ sZ) (k - r) := by
  have hh : inv t ≫ t = 𝟙 X := IsIso.inv_hom_id t
  rw [← chowPushforwardOfIso_fundamentalChowClass C (𝟙 X ≫ sX) (t ≫ sX) (inv t)
    (by rw [← Category.assoc, hh]) k]
  rw [BivariantClass.cap_chowPushforwardOfIso_map C
    (𝒩.virtualNormalClass C sX sZ hZ r) t (inv t)
    (𝟙 X) hh k,
    virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection 𝒩 hQ C sX sZ hZ r k hX hZd]
  have : IsIso (pullback.map i (𝟙 X) i t (𝟙 Z) (inv t) (𝟙 X) (by simp)
      (by rw [Category.comp_id, hh])) := by
    infer_instance
  exact properChowPushforward_fundamentalChowClass_of_isIso C _ _ _ _ _ _

end Cone

end Stacks.Chow.VirtualNormalBundle

end

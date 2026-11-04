module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocusNullstellensatz
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# Infinitesimal neighbourhoods of a closed subspace, and the Nullstellensatz for closed subspaces

Let `X` be an algebraic space over a scheme `S` and let `Y ⊆ X` be a closed subspace with ideal
sheaf `ℐ_Y`. The powers `ℐ_Yⁿ` are quasi-coherent, so by Stacks 03MB they cut out closed
subspaces `Y⁽ⁿ⁾ ⊆ X`, the *infinitesimal neighbourhoods* of `Y`. If `X` is Noetherian and
`Z ⊆ X` is a closed subspace whose points all lie in `Y`, then `Z ⊆ Y⁽ⁿ⁾` for some `n`: this is
the Nullstellensatz `ℐ_Yⁿ ⊆ ℐ_Z` of
`AlgebraicGeometry.Space.exists_idealPow_le_of_idealZeroLocus_subset`, read through Stacks 03MB.

## Main definitions

* `AlgebraicGeometry.Space.infinitesimalNeighbourhood`: the closed subspace `Y⁽ⁿ⁾` cut out by
  `ℐ_Yⁿ`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPow`: powers of a quasi-coherent sheaf of
  ideals are quasi-coherent, and `AlgebraicGeometry.Space.idealPow_obj_eq_pow_of_isAffine`:
  over an affine chart their sections are the powers of the sections.
* `AlgebraicGeometry.Space.definingIdealSheaf_infinitesimalNeighbourhood`: the ideal of `Y⁽ⁿ⁾`
  is `ℐ_Yⁿ`.
* `AlgebraicGeometry.Space.infinitesimalNeighbourhood_antitone` and
  `AlgebraicGeometry.Space.le_infinitesimalNeighbourhood`: `Y⁽ᵐ⁾ ⊆ Y⁽ⁿ⁾` for `m ≤ n`, and
  `Y ⊆ Y⁽ⁿ⁾` for `n ≥ 1`.
* `AlgebraicGeometry.Space.infinitesimalNeighbourhood_preimage_le`: for a morphism
  `f : Y ⟶ X`, `(f⁻¹T)⁽ⁿ⁾ ⊆ f⁻¹(T⁽ⁿ⁾)`.
* `AlgebraicGeometry.Space.exists_le_infinitesimalNeighbourhood`: **the Nullstellensatz for
  closed subspaces of a Noetherian algebraic space**, and its relative form
  `AlgebraicGeometry.Space.exists_le_preimage_infinitesimalNeighbourhood`: if the points of
  `Z ⊆ W` lie over `T ⊆ X` for `p : W ⟶ X` with `W` Noetherian, then `Z ⊆ p⁻¹(T⁽ⁿ⁾)`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `n`-th power of an ideal sheaf is the corresponding submodule of the unit module. -/
private theorem idealPowSubmodule_unit_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (I : IdealSheaves B S hS F hF) (n : ℕ) :
    idealPowSubmodule I n (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))) =
        Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS F hF).O) I n :=
  Stacks.Sites.idealSmul_top_eq (O := (smallEtaleRingedSite B S hS F hF).O)
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS F hF).O) I n)

/-- **Powers of a quasi-coherent sheaf of ideals on an algebraic space are quasi-coherent.** The
`n`-th power `ℐⁿ` is the submodule `ℐⁿ 𝒪_F` of the structure sheaf, which is quasi-coherent
because `𝒪_F` and `ℐ` are. -/
theorem isQuasicoherentOnSite_idealPow (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (I : IdealSheaves B S hS F hF)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) (n : ℕ) :
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS F hF).O) I
      n).toSheafOfModules.IsQuasicoherentOnSite := by
  have hunit : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ isCartesianOnAffineCharts_unit
  have h := isQuasicoherentOnSite_idealPowSubmodule B S hS F hF I _ hunit hI n
  rwa [← idealPowSubmodule_unit_eq B S hS F hF I n]

/-- **Over an affine chart the sections of `ℐⁿ` are the `n`-th power of the sections of `ℐ`**,
for a quasi-coherent sheaf of ideals `ℐ`. -/
theorem idealPow_obj_eq_pow_of_isAffine (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (I : IdealSheaves B S hS F hF)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) (n : ℕ) {U : SmallEtale B S hS F}
    (hU : IsAffine (chartScheme U)) :
    chartSectionIdeal B S hS F hF
        (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS F hF).O) I n) U =
      chartSectionIdeal B S hS F hF I U ^ n := by
  have h := chartSubmodule_idealPowSubmodule_eq_of_isAffine B S hS F hF I _
    isCartesianOnAffineCharts_unit
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF I.toSheafOfModules hI) n hU
  rw [idealPowSubmodule_unit_eq] at h
  exact h.trans (Ideal.mul_top _)

/-- The `n`-th **infinitesimal neighbourhood** `Y⁽ⁿ⁾` of a closed subspace `Y` of an algebraic
space `X`: the closed subspace cut out by the `n`-th power of the ideal sheaf of `Y`. -/
noncomputable def infinitesimalNeighbourhood (X : AlgebraicSpaces B S hS)
    (Y : ClosedSubspaces B S hS X.1) (n : ℕ) : ClosedSubspaces B S hS X.1 :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
      (definingIdealSheaf B S hS X Y) n)
    (isQuasicoherentOnSite_idealPow B S hS X.1 X.2 _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Y) n)).choose

/-- The ideal sheaf of `Y⁽ⁿ⁾` is the `n`-th power of the ideal sheaf of `Y`. -/
theorem definingIdealSheaf_infinitesimalNeighbourhood (X : AlgebraicSpaces B S hS)
    (Y : ClosedSubspaces B S hS X.1) (n : ℕ) :
    definingIdealSheaf B S hS X (infinitesimalNeighbourhood B S hS X Y n) =
      Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
      (definingIdealSheaf B S hS X Y) n :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
      (definingIdealSheaf B S hS X Y) n)
    (isQuasicoherentOnSite_idealPow B S hS X.1 X.2 _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Y) n)).choose_spec

/-- The infinitesimal neighbourhoods of `Y` increase with `n`. -/
theorem infinitesimalNeighbourhood_antitone (X : AlgebraicSpaces B S hS)
    (Y : ClosedSubspaces B S hS X.1) {m n : ℕ} (h : m ≤ n) :
    (infinitesimalNeighbourhood B S hS X Y m).1 ≤ (infinitesimalNeighbourhood B S hS X Y n).1 := by
  refine le_of_definingIdealSheaf_le B S hS X _ _ ?_
  rw [definingIdealSheaf_infinitesimalNeighbourhood, definingIdealSheaf_infinitesimalNeighbourhood]
  exact Stacks.Sites.idealPow_antitone (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
    (definingIdealSheaf B S hS X Y) h

/-- A closed subspace lies in each of its infinitesimal neighbourhoods of positive order. -/
theorem le_infinitesimalNeighbourhood (X : AlgebraicSpaces B S hS)
    (Y : ClosedSubspaces B S hS X.1) {n : ℕ} (hn : 1 ≤ n) :
    Y.1 ≤ (infinitesimalNeighbourhood B S hS X Y n).1 := by
  refine le_of_definingIdealSheaf_le B S hS X _ _ ?_
  rw [definingIdealSheaf_infinitesimalNeighbourhood]
  exact (Stacks.Sites.idealPow_antitone (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
    (definingIdealSheaf B S hS X Y) hn).trans_eq
      (Stacks.Sites.idealPow_one (O := (smallEtaleRingedSite B S hS X.1 X.2).O) _)

/-- **The ideal of the preimage of an infinitesimal neighbourhood.** For a morphism
`f : Y ⟶ X` and a closed subspace `T ⊆ X`, the ideal sheaf of `f⁻¹(T⁽ⁿ⁾)` is contained in the
`n`-th power of the ideal sheaf of `f⁻¹T`. On an affine chart of `Y` mapping to an affine chart
of `X` both ideals are extended from `X`, and extension of ideals commutes with powers. -/
theorem definingIdealSheaf_preimage_infinitesimalNeighbourhood_le {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (T : ClosedSubspaces B S hS X.1) (n : ℕ) :
    definingIdealSheaf B S hS Y (preimageClosedSubspace f (infinitesimalNeighbourhood B S hS X T n))
      ≤ Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS Y.1 Y.2).O)
        (definingIdealSheaf B S hS Y (preimageClosedSubspace f T)) n := by
  have key : ∀ (U : SmallEtale B S hS Y.1) (x : chartRing B S hS Y.1 Y.2 U),
      x ∈ definingIdealAt B S hS Y
        (preimageClosedSubspace f (infinitesimalNeighbourhood B S hS X T n)) (op U) →
      x ∈ chartSectionIdeal B S hS Y.1 Y.2 (Stacks.Sites.idealPow
        (O := (smallEtaleRingedSite B S hS Y.1 Y.2).O)
        (definingIdealSheaf B S hS Y (preimageClosedSubspace f T)) n) U := by
    intro U x hx
    refine (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS Y.1 Y.2).O)
      (definingIdealSheaf B S hS Y (preimageClosedSubspace f T)) n).isSheaf x
      (mem_topology_of_hasAffineChartDiagram B S hS f U _ ?_)
    rintro W a ⟨hWaff, V, q, hq, hVaff⟩
    have hxW : chartRestrict (hF := Y.2) a x ∈ definingIdealAt B S hS Y
        (preimageClosedSubspace f (infinitesimalNeighbourhood B S hS X T n)) (op W) :=
      chartIdeal_map_mem B S hS Y.1 Y.2 (definingIdealSheaf B S hS Y _) a hx
    have hVaff' : IsAffine (chartScheme V) := hVaff
    have h1 := definingIdealAt_preimage_eq_map B S hS f
      (infinitesimalNeighbourhood B S hS X T n) V W q hq
    have h3 := definingIdealAt_preimage_eq_map B S hS f T V W q hq
    have h2 : chartSectionIdeal B S hS X.1 X.2
        (definingIdealSheaf B S hS X (infinitesimalNeighbourhood B S hS X T n)) V =
        chartSectionIdeal B S hS X.1 X.2 (definingIdealSheaf B S hS X T) V ^ n := by
      rw [definingIdealSheaf_infinitesimalNeighbourhood]
      exact idealPow_obj_eq_pow_of_isAffine B S hS X.1 X.2 _
        (isQuasicoherentOnSite_definingIdealSheaf B S hS X T) n hVaff'
    have e1 : chartSectionIdeal B S hS Y.1 Y.2 (definingIdealSheaf B S hS Y
        (preimageClosedSubspace f (infinitesimalNeighbourhood B S hS X T n))) W =
        Ideal.map ((BigFppfOver.toScheme B S hS).map q).appTop.hom
          (chartSectionIdeal B S hS X.1 X.2
            (definingIdealSheaf B S hS X (infinitesimalNeighbourhood B S hS X T n)) V) := h1
    have e3 : chartSectionIdeal B S hS Y.1 Y.2 (definingIdealSheaf B S hS Y
        (preimageClosedSubspace f T)) W =
        Ideal.map ((BigFppfOver.toScheme B S hS).map q).appTop.hom
          (chartSectionIdeal B S hS X.1 X.2 (definingIdealSheaf B S hS X T) V) := h3
    have hle : chartSectionIdeal B S hS Y.1 Y.2 (definingIdealSheaf B S hS Y
        (preimageClosedSubspace f (infinitesimalNeighbourhood B S hS X T n))) W ≤
        chartSectionIdeal B S hS Y.1 Y.2 (definingIdealSheaf B S hS Y
          (preimageClosedSubspace f T)) W ^ n := by
      rw [e1, e3, h2]
      exact (Ideal.map_pow _ _ n).le
    have hx2 : chartRestrict (hF := Y.2) a x ∈ chartSectionIdeal B S hS Y.1 Y.2
        (definingIdealSheaf B S hS Y (preimageClosedSubspace f T)) W ^ n := hle hxW
    have hx3 := Stacks.Sites.mem_idealPow_of_mem_pow
      (O := (smallEtaleRingedSite B S hS Y.1 Y.2).O)
      (definingIdealSheaf B S hS Y (preimageClosedSubspace f T)) n (X := op W) hx2
    exact hx3
  exact fun U x hx => key U.unop x hx

/-- **The infinitesimal neighbourhood of a preimage lies in the preimage of the infinitesimal
neighbourhood**: `(f⁻¹T)⁽ⁿ⁾ ⊆ f⁻¹(T⁽ⁿ⁾)` for a morphism `f : Y ⟶ X` of algebraic spaces. -/
theorem infinitesimalNeighbourhood_preimage_le {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (T : ClosedSubspaces B S hS X.1) (n : ℕ) :
    (infinitesimalNeighbourhood B S hS Y (preimageClosedSubspace f T) n).1 ≤
      (preimageClosedSubspace f (infinitesimalNeighbourhood B S hS X T n)).1 := by
  refine le_of_definingIdealSheaf_le B S hS Y _ _ ?_
  rw [definingIdealSheaf_infinitesimalNeighbourhood]
  exact definingIdealSheaf_preimage_infinitesimalNeighbourhood_le B S hS f T n

/-- **The Nullstellensatz for closed subspaces of a Noetherian algebraic space.** If every point
of a closed subspace `Z` lies in a closed subspace `Y`, then `Z` lies in some infinitesimal
neighbourhood `Y⁽ⁿ⁾` of `Y`. -/
theorem exists_le_infinitesimalNeighbourhood (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (Z Y : ClosedSubspaces B S hS X.1)
    (h : subspacePointSet B S hS X.1 Z.1 ⊆ subspacePointSet B S hS X.1 Y.1) :
    ∃ n : ℕ, Z.1 ≤ (infinitesimalNeighbourhood B S hS X Y n).1 := by
  obtain ⟨n, hn⟩ := exists_idealPow_le_of_idealZeroLocus_subset B S hS hZ X hN
    (definingIdealSheaf B S hS X Z) (definingIdealSheaf B S hS X Y)
    (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z)
    (isQuasicoherentOnSite_definingIdealSheaf B S hS X Y)
    (by rwa [← range_pointsMap_ι_eq_idealZeroLocus, ← range_pointsMap_ι_eq_idealZeroLocus])
  refine ⟨n, le_of_definingIdealSheaf_le B S hS X _ _ ?_⟩
  rw [definingIdealSheaf_infinitesimalNeighbourhood]
  exact hn

/-- **The Nullstellensatz relative to a morphism.** Let `p : W ⟶ X` be a morphism from a
Noetherian algebraic space, `T ⊆ X` a closed subspace and `Z ⊆ W` a closed subspace whose points
all lie over `T`. Then `Z ⊆ p⁻¹(T⁽ⁿ⁾)` for some `n`. -/
theorem exists_le_preimage_infinitesimalNeighbourhood (hZ : B.Contains (⊤_ Scheme.{u}))
    {X W : AlgebraicSpaces B S hS} (hN : IsNoetherian B S hS hZ W.1) (p : W ⟶ X)
    (Z : ClosedSubspaces B S hS W.1) (T : ClosedSubspaces B S hS X.1)
    (h : subspacePointSet B S hS W.1 Z.1 ⊆
      subspacePointSet B S hS W.1 (preimageClosedSubspace p T).1) :
    ∃ n : ℕ, Z.1 ≤ (preimageClosedSubspace p (infinitesimalNeighbourhood B S hS X T n)).1 := by
  obtain ⟨n, hn⟩ := exists_le_infinitesimalNeighbourhood B S hS hZ W hN Z _ h
  exact ⟨n, hn.trans (infinitesimalNeighbourhood_preimage_le B S hS p T n)⟩

end AlgebraicGeometry.Space

end

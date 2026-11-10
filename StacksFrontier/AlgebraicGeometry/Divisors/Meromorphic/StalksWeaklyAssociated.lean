module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Sheaves.CommRingCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.Topology.Sheaves.Presheaf.LocalizationStalk
public import StacksFrontier.Topology.Sheaves.Presheaf.Localization

/-!
# Meromorphic functions when the weakly associated points are generic

Suppose that every weakly associated point of a scheme is a generic point of an irreducible
component and that every quasi-compact open has finitely many irreducible components. Then the
germs of regular sections at any point are precisely the nonzerodivisors of the local ring
there, and the stalk of the presheaf of meromorphic functions is the total quotient ring of
that local ring. These hypotheses neither imply nor are implied by local Noetherianity, which
is why these two statements are separate from their locally Noetherian counterparts.

## Main results

* `regularSectionGerms_eq_nonZeroDivisors_of_weaklyAssociatedPoints_subset_genericPoints`: the
  germs of regular sections are the nonzerodivisors of the local ring.
* `stalk_totalQuotientPresheaf_isFractionRing_of_weaklyAssociatedPoints_subset_genericPoints`:
  the stalk of the presheaf of meromorphic functions is a total quotient ring.

## Implementation notes

Mathlib's `submonoidPresheafOfStalk` expresses the regular sections on an open set as the
sections whose germs at all of its points are nonzerodivisors, and the supremum of their images
under the germ maps is the canonical stalk of that submonoid presheaf. The finiteness
hypothesis is used to shrink an affine neighbourhood so that every generic point it contains
specializes to the chosen point.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private lemma exists_open_generic_specializes {Y : Type*} [TopologicalSpace Y]
    (hfinite : (irreducibleComponents Y).Finite) (x : Y) :
    ∃ V : Opens Y, x ∈ V ∧ ∀ y ∈ V, y ∈ genericPoints Y → y ⤳ x := by
  let B := {Z ∈ irreducibleComponents Y | x ∉ Z}
  have hB : B.Finite := hfinite.subset (fun _ h ↦ h.1)
  let V : Opens Y := ⟨(⋃ Z ∈ B, Z)ᶜ,
    (hB.isClosed_biUnion
      (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · change x ∉ ⋃ Z ∈ B, Z
    simpa only [Set.mem_iUnion, not_exists] using (fun Z hZ ↦ hZ.2)
  · intro y hy hyg
    by_contra h
    exact hy (Set.mem_iUnion.mpr ⟨closure {y}, Set.mem_iUnion.mpr
      ⟨⟨hyg, fun hx ↦ h (specializes_iff_mem_closure.mpr hx)⟩,
        subset_closure (Set.mem_singleton y)⟩⟩)

private lemma genericPoint_mem_open {Y : TopCat} (U : Opens Y) (y : U)
    (hy : y.1 ∈ genericPoints Y) : y ∈ genericPoints U := by
  change closure {y} ∈ irreducibleComponents U
  rw [U.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.closure_eq_preimage_closure_image,
    Set.image_singleton]
  exact preimage_mem_irreducibleComponents hy U.isOpen.isOpenEmbedding_subtypeVal
    ⟨y.1, subset_closure (Set.mem_singleton y.1), ⟨y, rfl⟩⟩

private lemma exists_affine_generic_specializes (X : Scheme.{u})
    (hfinite : ∀ (U : X.Opens), IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {x : X} {W : X.Opens} (hx : x ∈ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      ∀ y ∈ U, y ∈ genericPoints X → y ⤳ x := by
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
  obtain ⟨V, hxV, hV⟩ := exists_open_generic_specializes (hfinite U hU.isCompact) ⟨x, hxU⟩
  let V' : X.Opens := ⟨Subtype.val '' (V : Set U), U.isOpenEmbedding.isOpenMap _ V.isOpen⟩
  obtain ⟨T, hT, hxT, hTV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V' from ⟨⟨x, hxU⟩, hxV, rfl⟩)
  have hTU : T ≤ U := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := hTV hy
    exact z.2
  refine ⟨T, hT, hxT, hTU.trans hUW, ?_⟩
  intro y hy hyg
  obtain ⟨z, hz, rfl⟩ := hTV hy
  exact (hV z hz (genericPoint_mem_open U z hyg)).map continuous_subtype_val

private lemma germ_injective_of_weaklyAssociated_specializes (X : Scheme.{u})
    {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (hass : ∀ y : U, Stacks.Divisors.IsWeaklyAssociatedPoint
      (SheafOfModules.unit X.ringCatSheaf) y → (y : X) ⤳ x) :
    Function.Injective (X.presheaf.germ U x x.2) := by
  let := X.presheaf.algebra_section_stalk x
  let := hU.isLocalization_stalk x
  change Function.Injective (algebraMap Γ(X, U) (X.presheaf.stalk x))
  apply IsLocalization.injective (M := (hU.primeIdealOf x).asIdeal.primeCompl)
  intro r hr
  rw [mem_nonZeroDivisors_iff_left]
  intro z hz
  by_contra hz0
  have hproper : (Γ(X, U) ∙ z).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1 : Γ(X, U)) ∈ (Γ(X, U) ∙ z).annihilator := by rw [h]; trivial
    exact hz0 (by simpa using (Submodule.mem_annihilator_span_singleton z 1).mp h1)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hproper
  let p : PrimeSpectrum Γ(X, U) := ⟨q, hq.1.1⟩
  have hpU : hU.fromSpec p ∈ U := by
    change hU.fromSpec p ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self p
  let y : U := ⟨hU.fromSpec p, hpU⟩
  have hyp : hU.primeIdealOf y = p :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf y)
  have hw : Stacks.Divisors.IsWeaklyAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) y := by
    apply (AlgebraicGeometry.isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
      (SheafOfModules.unit X.ringCatSheaf) U hU y y.2).mp
    change IsWeaklyAssociatedPrime Γ(X, U) Γ(X, U) (hU.primeIdealOf y).asIdeal
    rw [hyp]
    exact ⟨z, hq⟩
  have hle : (hU.primeIdealOf y).asIdeal ≤ (hU.primeIdealOf x).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr
      (((subtype_specializes_iff y x).mpr (hass y hw)).map hU.isoSpec.hom.continuous)
  rw [hyp] at hle
  exact hr (hle (hq.1.2 ((Submodule.mem_annihilator_span_singleton z r).mpr
    (by simpa [smul_eq_mul, mul_comm] using hz))))

/-- If weakly associated points are generic points of irreducible components and
quasi-compact opens have finitely many irreducible components, then the germs of regular
sections at every point are exactly the nonzerodivisors in its local ring. -/
@[stacks 0EMF "regular_elements_in_stalks"]
lemma regularSectionGerms_eq_nonZeroDivisors_of_weaklyAssociatedPoints_subset_genericPoints
    (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ (U : X.Opens), IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    (⨆ (U : Opens X) (hx : x ∈ U),
      ((X.presheaf.submonoidPresheafOfStalk
        (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))).obj (Opposite.op U)).map
          (X.presheaf.germ U x hx).hom) =
      nonZeroDivisors (X.presheaf.stalk x) := by
  apply le_antisymm
  · refine iSup_le fun U ↦ iSup_le fun hx ↦ ?_
    rintro _ ⟨s, hs, rfl⟩
    exact Submonoid.mem_iInf.mp hs ⟨x, hx⟩
  · intro a ha
    obtain ⟨V, hxV, s, hsa⟩ := X.presheaf.exists_germ_eq a
    obtain ⟨U, hU, hxU, hUV, hgen⟩ := exists_affine_generic_specializes X hfinite hxV
    let i : U ⟶ V := homOfLE hUV
    let t : Γ(X, U) := X.presheaf.map i.op s
    have hta : X.presheaf.germ U x hxU t = a := (X.presheaf.germ_res_apply i x hxU s).trans hsa
    have ht : t ∈ nonZeroDivisors Γ(X, U) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro b hb
      apply germ_injective_of_weaklyAssociated_specializes X hU ⟨x, hxU⟩
        fun y hy ↦ hgen y y.2 (hass hy)
      rw [map_zero]
      apply (mem_nonZeroDivisors_iff_left.mp ha)
      rw [← hta, ← map_mul, hb, map_zero]
    apply Submonoid.mem_iSup_of_mem U
    apply Submonoid.mem_iSup_of_mem hxU
    refine ⟨t, ?_, hta⟩
    change t ∈ ⨅ y : U, Submonoid.comap (X.presheaf.germ U y y.2).hom
      (nonZeroDivisors (X.presheaf.stalk y))
    rw [Submonoid.mem_iInf]
    intro y
    let := X.presheaf.algebra_section_stalk y
    let := hU.isLocalization_stalk y
    exact IsLocalization.nonZeroDivisors_le_comap (hU.primeIdealOf y).asIdeal.primeCompl
      (X.presheaf.stalk y) ht

/-- If every weakly associated point of a scheme is a generic point of an irreducible component
and every quasi-compact open has finitely many irreducible components, then the stalk of the
presheaf of meromorphic functions at any point is the total quotient ring of the local ring. -/
@[stacks 0EMF "stalk_total_quotient_ring"]
lemma stalk_totalQuotientPresheaf_isFractionRing_of_weaklyAssociatedPoints_subset_genericPoints
    (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ (U : X.Opens), IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) := by
  let D : Stacks.Presheaf.PresheafLocalizationData :=
    ⟨X, X.presheaf, X.presheaf.submonoidPresheafOfStalk
      (fun y ↦ nonZeroDivisors (X.presheaf.stalk y))⟩
  have hS : D.S.stalk x = nonZeroDivisors (X.presheaf.stalk x) :=
    regularSectionGerms_eq_nonZeroDivisors_of_weaklyAssociatedPoints_subset_genericPoints
      X hass hfinite x
  convert Stacks.Presheaf.Localization.localizationPresheaf_stalk_isLocalization D x using 1
  simp only [D, TopCat.Presheaf.totalQuotientPresheaf, hS]
  rfl

end AlgebraicGeometry

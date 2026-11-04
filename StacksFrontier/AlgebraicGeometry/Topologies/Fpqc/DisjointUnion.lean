module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Topology.Sets.CompactOpenCovered
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
public import StacksCore.Tactic.StacksAttribute

/-!
# Fpqc coverings and disjoint unions

A family of morphisms of schemes is an fpqc covering if and only if the single morphism out
of the disjoint union of its sources is one.

## Main results

* `AlgebraicGeometry.ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem`: an fpqc
  covering family is characterized by the induced morphism from its coproduct.

## Implementation notes

Fpqc covering families are members of `AlgebraicGeometry.Scheme.fpqcPrecoverage`, and the
disjoint-union morphism is the coproduct descent `CategoryTheory.Limits.Sigma.desc`.  Both
sides are compared through the condition of Stacks 03L7 that every affine open of the
target be covered by compact opens of the sources, which transports along the
homeomorphism between the underlying space of the coproduct and the disjoint union of the
underlying spaces.

## References

* [Stacks Project, Tag 040I](https://stacks.math.columbia.edu/tag/040I)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

namespace AlgebraicGeometry

private lemma compactOpenCovered_iff_family_data
    {S : Type*} [TopologicalSpace S] {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (g : ∀ i, X i → S) (U : Set S) :
    (∃ V : ∀ i, Opens (X i),
      (∀ i, IsCompact (V i : Set (X i))) ∧
        ({i | V i ≠ ⊥} : Set ι).Finite ∧
        ⋃ i, g i '' (V i : Set (X i)) = U) ↔ IsCompactOpenCovered g U := by
  classical
  constructor
  · rintro ⟨V, hV, hfinite, hU⟩
    let s : Set ι := {i | V i ≠ ⊥}
    refine ⟨s, hfinite, fun i _ ↦ V i, fun i _ ↦ hV i, ?_⟩
    have hEq : (⋃ i, ⋃ (_ : i ∈ s), g i '' (V i : Set (X i))) =
        ⋃ i, g i '' (V i : Set (X i)) := by
      refine Set.iUnion_congr fun i => ?_
      by_cases hi : i ∈ s
      · simp [hi]
      · simp [show V i = ⊥ by simpa [s] using hi]
    rw [hEq, hU]
  · rintro ⟨s, hs, V, hV, hU⟩
    let W : ∀ i, Opens (X i) := fun i => if hi : i ∈ s then V i hi else ⊥
    refine ⟨W, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ s
      · simpa [W, hi] using hV i hi
      · simp [W, hi]
    · refine hs.subset fun i hi => ?_
      by_contra hnot
      simp [W, hnot] at hi
    · have hEq : (⋃ i, g i '' (W i : Set (X i))) =
          ⋃ i, ⋃ (hi : i ∈ s), g i '' (V i hi : Set (X i)) := by
        refine Set.iUnion_congr fun i => ?_
        by_cases hi : i ∈ s <;> simp [W, hi]
      rw [hEq, hU]

/-- Compact open coverings by a single map transfer along a homeomorphism of the source. -/
private lemma compactOpenCovered_unit_of_homeomorph
    {X Y S : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
    (e : X ≃ₜ Y) (g : X → S) (h : Y → S) (hgh : h ∘ e = g) {U : Set S}
    (hU : IsCompactOpenCovered (fun _ : Unit => g) U) :
    IsCompactOpenCovered (fun _ : Unit => h) U := by
  subst hgh
  rw [IsCompactOpenCovered.iff_of_unique] at hU ⊢
  obtain ⟨V, hV, hU⟩ := hU
  exact ⟨⟨e '' (V : Set X), e.isOpenMap _ V.2⟩, hV.image e.continuous, by
    rwa [Set.image_image]⟩

private lemma compactOpenCovered_homeomorph_iff
    {X Y S : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
    (e : X ≃ₜ Y) (g : X → S) (h : Y → S) (hgh : g = h ∘ e) (U : Set S) :
    IsCompactOpenCovered (fun _ : Unit => g) U ↔
      IsCompactOpenCovered (fun _ : Unit => h) U :=
  ⟨compactOpenCovered_unit_of_homeomorph e g h hgh.symm,
    compactOpenCovered_unit_of_homeomorph e.symm h g (by rw [hgh]; ext; simp)⟩

private lemma compactOpenCovered_family_sigmaDesc_iff
    {ι : Type v} [Small.{u} ι] {T : Scheme.{u}} (T' : ι → Scheme.{u})
    (f : ∀ i, T' i ⟶ T) (U : Set T) :
    IsCompactOpenCovered (fun i x => (f i).base x) U ↔
      IsCompactOpenCovered (fun _ : Unit => fun x : (∐ T' : Scheme.{u}) =>
        (Sigma.desc f).base x) U := by
  classical
  obtain ⟨ι₀, ⟨e₀⟩⟩ := Small.equiv_small.{u} (α := ι)
  let T₀ : ι₀ → Scheme.{u} := fun j => T' (e₀.symm j)
  let eSigma : (Σ j, T₀ j) ≃ (Σ i, T' i) :=
    Equiv.sigmaCongrLeft (β := fun i => T' i) e₀.symm
  have hSigmaMap : IsHomeomorph (Sigma.map
      (α₁ := ι₀) (α₂ := ι)
      (β₁ := fun j => (T₀ j : Type u)) (β₂ := fun i => (T' i : Type u))
      e₀.symm (fun _ x => x)) :=
    @IsHomeomorph.sigmaMap ι₀ ι
      (fun j : ι₀ => (T' (e₀.symm j) : Type u)) (fun i : ι => (T' i : Type u))
      (fun _ => inferInstance) (fun _ => inferInstance)
      e₀.symm e₀.symm.bijective (fun j x => x) (fun _ => IsHomeomorph.id)
  have hSigmaIso : IsHomeomorph eSigma := by
    convert hSigmaMap using 1
    ext p <;> cases p <;> rfl
  let hSigma : (Σ j, T₀ j) ≃ₜ (Σ i, T' i) :=
    eSigma.toHomeomorphOfIsInducing hSigmaIso.isInducing
  let hCop : (∐ T₀ : Scheme.{u}) ≃ₜ (∐ T' : Scheme.{u}) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (Sigma.reindex e₀.symm T'))
  let e : (Σ i, T' i) ≃ₜ (∐ T' : Scheme.{u}) :=
    hSigma.symm.trans (AlgebraicGeometry.sigmaMk T₀) |>.trans hCop
  have hcopι (i : ι) (x : T' i) :
      hCop ((Sigma.ι T₀ (e₀ i)) (eSigma.symm ⟨i, x⟩).2) = (Sigma.ι T' i) x := by
    let q := eSigma.symm ⟨i, x⟩
    show (Sigma.ι (T' ∘ e₀.symm) q.1 ≫ (Sigma.reindex e₀.symm T').hom) q.2 = _
    rw [Sigma.ι_reindex_hom]
    have hq : (⟨e₀.symm q.1, q.2⟩ : Σ j, T' j) = ⟨i, x⟩ := by
      simpa only [eSigma, Equiv.sigmaCongrLeft_apply] using
        eSigma.apply_symm_apply ⟨i, x⟩
    exact congrArg (fun z : Σ j, T' j => (Sigma.ι T' z.1) z.2) hq
  have hcomp : (fun p : Σ i, T' i => (f p.1).base p.2) =
      (fun x : (∐ T' : Scheme.{u}) => (Sigma.desc f).base x) ∘ e := by
    funext p
    obtain ⟨i, x⟩ := p
    have he : e ⟨i, x⟩ = (Sigma.ι T' i) x := by
      simpa [e, hSigma, eSigma, Equiv.sigmaCongrLeft, T₀] using hcopι i x
    show (f i).base x = (Sigma.desc f).base (e ⟨i, x⟩)
    rw [he]
    simp [← Scheme.Hom.comp_apply]
  rw [IsCompactOpenCovered.iff_isCompactOpenCovered_sigmaMk]
  exact compactOpenCovered_homeomorph_iff e _ _ hcomp U

private lemma flat_sigmaDesc_iff
    {ι : Type v} [Small.{u} ι] {T : Scheme.{u}} (T' : ι → Scheme.{u})
    (f : ∀ i, T' i ⟶ T) : (∀ i, Flat (f i)) ↔ Flat (Sigma.desc f) := by
  refine ⟨fun _ => inferInstance, fun h i => ?_⟩
  simpa only [Sigma.ι_desc] using
    MorphismProperty.comp_mem _ _ _ (inferInstance : Flat (Sigma.ι T' i)) h

/-- A family of morphisms of schemes is an fpqc covering precisely when the induced
morphism from the disjoint union of the source schemes is an fpqc covering. -/
@[stacks 040I]
public lemma ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem
    {ι : Type v} [Small.{u} ι] {T : Scheme.{u}} (T' : ι → Scheme.{u})
    (f : ∀ i, T' i ⟶ T) :
    Presieve.ofArrows T' f ∈ Scheme.fpqcPrecoverage T ↔
      Presieve.singleton (Sigma.desc f) ∈ Scheme.fpqcPrecoverage T := by
  rw [← Presieve.ofArrows_pUnit.{u} (Sigma.desc f),
    mem_fpqcPrecoverage_iff_affine_finite_support (T := T) (X := T') f,
    mem_fpqcPrecoverage_iff_affine_finite_support (T := T)
      (X := fun _ : PUnit => (∐ T' : Scheme.{u})) (fun _ => Sigma.desc f)]
  constructor
  · rintro ⟨hflat, hcover⟩
    refine ⟨fun _ => (flat_sigmaDesc_iff T' f).mp hflat, fun U hU => ?_⟩
    obtain ⟨W, hW, himage⟩ := (IsCompactOpenCovered.iff_of_unique
      (f := fun _ : Unit => fun x : (∐ T' : Scheme.{u}) => (Sigma.desc f).base x)).mp
      ((compactOpenCovered_family_sigmaDesc_iff T' f (U : Set T)).mp
        ((compactOpenCovered_iff_family_data _ _).mp (hcover U hU)))
    exact ⟨fun _ => W, fun _ => hW, Set.toFinite _, (iSup_unique _).trans himage⟩
  · rintro ⟨hflat, hcover⟩
    refine ⟨(flat_sigmaDesc_iff T' f).mpr (hflat PUnit.unit), fun U hU => ?_⟩
    obtain ⟨V, hV, -, himage⟩ := hcover U hU
    replace himage := (iSup_unique _).symm.trans himage
    exact (compactOpenCovered_iff_family_data _ _).mpr
      ((compactOpenCovered_family_sigmaDesc_iff T' f (U : Set T)).mpr
        ((IsCompactOpenCovered.iff_of_unique
          (f := fun _ : Unit => fun x : (∐ T' : Scheme.{u}) => (Sigma.desc f).base x)).mpr
          ⟨V default, hV default, himage⟩))

end AlgebraicGeometry

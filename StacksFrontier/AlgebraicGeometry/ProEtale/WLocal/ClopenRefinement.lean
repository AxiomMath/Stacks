module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Separation.DisjointCover
public import Mathlib.Topology.Spectral.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Compact.ClosedPointsKolmogorov
public import StacksCore.Topology.Connected.ComponentSpace
public import StacksFrontier.Topology.Spectral.ComponentSpace
public import StacksFrontier.Topology.Spectral.ConstructiblyClosed
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable
public import StacksFrontier.Topology.Spectral.ProfiniteCharacterization
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# Clopen refinements and closed points of a spectral space

For a spectral space `X`, the following two conditions are equivalent: every open cover of `X`
admits a finite refinement by pairwise disjoint clopen subsets, and the canonical map from the
closed points of `X` to the space `π₀(X)` of connected components is bijective. The second
condition holds as soon as the closed points of `X` form a closed subset and every point
specializes to a unique closed point.

## Main results

* `AlgebraicGeometry.ProEtale.clopen_refinement_iff_closedPoints_bijective`: the equivalence
  between the clopen-refinement property and bijectivity of the canonical map from closed points
  to connected components.
* `exists_finite_disjoint_clopen_refinement_of_unique_closed_specialization`: the clopen
  refinement of an open cover, assuming unique closed specializations.
* `closedPoints_to_connectedComponents_bijective_of_unique_specialization`: bijectivity of the
  canonical map, assuming unique closed specializations.

## Implementation notes

A finite disjoint-union decomposition is represented by a family of `Clopens X` indexed by
`Fin n`, together with its covering, pairwise-disjointness and refinement properties. The
canonical map sends a closed point to its connected component. The set of closed points is
Mathlib's `closedPoints X` and the space of connected components is `ConnectedComponents X`.

The two independent conclusions drawn from unique closed specialization are stated separately.

## References

* [Stacks Project, Tag 0968](https://stacks.math.columbia.edu/tag/0968)
-/

@[expose] public section

open Set TopologicalSpace
open scoped Function

namespace AlgebraicGeometry.ProEtale

/-- Every point of a spectral space lies in the same connected component as some closed point
of its closure. -/
private lemma exists_closed_point_same_component
    (X : Type*) [TopologicalSpace X] [SpectralSpace X] (z : X) :
    ∃ y : closedPoints X, (y.1 : ConnectedComponents X) = (z : ConnectedComponents X) ∧
      y.1 ∈ closure ({z} : Set X) := by
  obtain ⟨y, hycl, hyclosed⟩ :=
    isClosed_closure.exists_closed_singleton ⟨z, subset_closure (Set.mem_singleton z)⟩
  refine ⟨⟨y, mem_closedPoints_iff.mpr hyclosed⟩, ConnectedComponents.coe_eq_coe'.2 ?_, hycl⟩
  exact isConnected_singleton.closure.subset_connectedComponent
    (subset_closure (Set.mem_singleton z)) hycl

/-- **Stacks Project, Tag 0968.** For a spectral space, every open cover has a finite pairwise
disjoint clopen refinement if and only if the canonical map from its closed points to its
connected components is bijective. -/
@[stacks 0968 "clopen_refinement_equivalence"]
theorem clopen_refinement_iff_closedPoints_bijective
    (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    (∀ {ι : Type*} (U : ι → Opens X), IsOpenCover U →
      ∃ (n : ℕ) (W : Fin n → Clopens X),
        (∀ j, ∃ i, (W j : Set X) ⊆ U i) ∧
        (Set.univ : Set X) ⊆ ⋃ j, (W j : Set X) ∧
        Pairwise (Disjoint on W)) ↔
    Function.Bijective (fun x : closedPoints X => (x.1 : ConnectedComponents X)) := by
  classical
  let f : closedPoints X → ConnectedComponents X := fun x => (x.1 : ConnectedComponents X)
  have hcompactClosedPoints : CompactSpace (closedPoints X) :=
    isCompact_iff_compactSpace.mp (isCompact_closedPoints X)
  have hfcont : Continuous f :=
    ConnectedComponents.continuous_coe.comp continuous_subtype_val
  have hprof := connectedComponents_isProfinite X
  have hpiT2 : T2Space (ConnectedComponents X) := hprof.1
  have hpiCompact : CompactSpace (ConnectedComponents X) := hprof.2.1
  have hpiTd : TotallyDisconnectedSpace (ConnectedComponents X) := hprof.2.2
  constructor
  · intro h
    constructor
    · intro x y hxy
      by_contra hn
      have hxyval : (x : X) ≠ (y : X) := fun heq => hn (Subtype.ext heq)
      let U : ULift.{_} Bool → Opens X := fun i =>
        if i.down then ⟨({(y : X)} : Set X)ᶜ, y.2.isOpen_compl⟩
        else ⟨({(x : X)} : Set X)ᶜ, x.2.isOpen_compl⟩
      have hU : IsOpenCover U := by
        apply IsOpenCover.of_sets (fun i => (U i).isOpen)
        ext z
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        by_cases hz : z = (x : X)
        · subst z
          exact ⟨ULift.up true, by simpa [U] using hxyval⟩
        · exact ⟨ULift.up false, by simpa [U] using hz⟩
      obtain ⟨n, W, hWref, hWcov, hWdisj⟩ := h (U := U) hU
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hWcov (Set.mem_univ (x : X)))
      obtain ⟨i, hi⟩ := hWref j
      have hi1 : i.down = true := by
        rcases i with ⟨_ | _⟩
        · exact absurd (hi hj) (by simp [U])
        · rfl
      have hyW : (y : X) ∉ (W j : Set X) := fun hy => by simpa [U, hi1] using hi hy
      have hsub : connectedComponent (x : X) ⊆ (W j : Set X) :=
        (Clopens.isClopen (W j)).connectedComponent_subset hj
      exact hyW (hsub (ConnectedComponents.coe_eq_coe'.mp hxy.symm))
    · intro c
      obtain ⟨x, rfl⟩ := c.exists_rep
      obtain ⟨y, hyc, _⟩ := exists_closed_point_same_component X x
      exact ⟨y, hyc⟩
  · intro hf
    have hm : IsHomeomorph f := isHomeomorph_iff_continuous_bijective.mpr ⟨hfcont, hf⟩
    let e : closedPoints X ≃ₜ ConnectedComponents X := hm.homeomorph
    intro ι U hU
    have he : ∀ (z : X) (y : closedPoints X), (y.1 : ConnectedComponents X) = z →
        e.symm (ConnectedComponents.mk z) = y := fun z y hyc => by
      rw [← hyc]
      exact e.symm_apply_apply _
    let q : ConnectedComponents X → X := fun c => (e.symm c : X)
    let A : ι → Set (ConnectedComponents X) := fun i => q ⁻¹' (U i : Set X)
    let AU : ι → Opens (ConnectedComponents X) := fun i =>
      ⟨A i, (U i).isOpen.preimage (continuous_subtype_val.comp e.symm.continuous)⟩
    have hAU : IsOpenCover AU := by
      apply IsOpenCover.of_sets (fun i => (AU i).isOpen)
      ext c
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨z, rfl⟩ := c.exists_rep
      obtain ⟨y, hyc, _⟩ := exists_closed_point_same_component X z
      obtain ⟨i, hi⟩ := hU.exists_mem y.1
      refine ⟨i, ?_⟩
      show ((e.symm (ConnectedComponents.mk z) : closedPoints X) : X) ∈ (U i : Set X)
      rwa [he z y hyc]
    obtain ⟨n, V, hVref, hVcov, hVdisj⟩ :=
      hAU.exists_finite_nonempty_disjoint_clopen_cover
    let W : Fin n → Clopens X := fun j =>
      ⟨ConnectedComponents.mk ⁻¹' (V j : Set _),
        (V j).isClopen.preimage ConnectedComponents.continuous_coe⟩
    refine ⟨n, W, ?_, ?_, ?_⟩
    · intro j
      obtain ⟨i, hi⟩ := (hVref j).2
      refine ⟨i, ?_⟩
      intro z hz
      have hzV : (ConnectedComponents.mk z) ∈ (V j : Set (ConnectedComponents X)) := hz
      have hqA : ConnectedComponents.mk z ∈ A i := hi hzV
      obtain ⟨y, hyc, hycl⟩ := exists_closed_point_same_component X z
      change ((e.symm (ConnectedComponents.mk z) : closedPoints X) : X) ∈ (U i : Set X) at hqA
      rw [he z y hyc] at hqA
      exact (U i).isOpen.stableUnderGeneralization (specializes_iff_mem_closure.mpr hycl) hqA
    · intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hVcov (Set.mem_univ (ConnectedComponents.mk z)))
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    · exact fun j k hjk => Clopens.coe_disjoint.mp
        ((Clopens.coe_disjoint.mpr (hVdisj hjk)).preimage ConnectedComponents.mk)

/-- The generalizations of a clopen set of closed points form a closed subset, when every point
specializes to a unique closed point. -/
private lemma isClosed_generalizationsOf_clopen_closedPoints
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    [CompactSpace (closedPoints X)]
    (hunique : ∀ x : X, ∃! x₀ : closedPoints X, Specializes x x₀.1)
    (U : Clopens (closedPoints X)) :
    IsClosed (SpectralSubset.generalizationsOf
      ((Subtype.val : closedPoints X → X) '' (U : Set (closedPoints X)))) := by
  let E : Set X := (Subtype.val : closedPoints X → X) '' (U : Set (closedPoints X))
  let W : Set X := SpectralSubset.generalizationsOf E
  have hWinter : SpectralSubset.IsInterCompactOpen W :=
    (SpectralSubset.characterizations_equiv W).2.2.1.mp
      ⟨E, U.isClosed.isCompact.image continuous_subtype_val, rfl⟩
  have hWct : @IsClosed X (constructibleTopology X) W := by
    rcases hWinter with ⟨S, hWS, hS⟩
    rw [hWS]
    exact @isClosed_sInter X (constructibleTopology X) S (fun s hs =>
      (show @IsClopen X (constructibleTopology X) s from
        (hS s hs).2.isClopen_constructibleTopology (hS s hs).1).1)
  have hWspec : StableUnderSpecialization W := by
    rintro a b hab ⟨c, hc, hbc⟩
    obtain ⟨d, hdU, rfl⟩ := hc
    obtain ⟨e, hbe, hbe_unique⟩ := hunique b
    exact ⟨d, ⟨d, hdU, rfl⟩, ((hunique a).unique hbc (hab.trans hbe)) ▸ hbe⟩
  exact isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization hWct hWspec

/-- When the closed points form a closed subset and every point specializes to a unique closed
point, the canonical map from closed points to connected components is bijective. -/
private lemma closedPoints_bijective {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (hclosed : IsClosed (closedPoints X))
    (hunique : ∀ x : X, ∃! x₀ : closedPoints X, Specializes x x₀.1) :
    Function.Bijective (fun x₀ : closedPoints X ↦ ConnectedComponents.mk x₀.1) := by
  have hspectral : SpectralSpace (closedPoints X) :=
    spectralSpace_of_isClosed_constructibleTopology _ hclosed.isClosed_constructibleTopology
  have ht1 : T1Space (closedPoints X) := ⟨fun x => by
    refine (isClosed_induced_iff).2 ⟨{(x : X)}, mem_closedPoints_iff.mp x.2, ?_⟩
    ext z
    simp [Subtype.ext_iff]⟩
  have hcompact : CompactSpace (closedPoints X) := inferInstance
  have hsep : ∀ ⦃x y : closedPoints X⦄, x ≠ y → ∃ U : Clopens (closedPoints X),
      x ∈ U ∧ y ∉ U := by
    intro x y hxy
    have htd : TotallySeparatedSpace (closedPoints X) :=
      totallySeparatedSpace_of_qcOpen_isClosed (fun U hUo hUc => by
        apply isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
        · exact (hUc.isClopen_constructibleTopology hUo).1
        · exact fun a b hab hb => hab.eq ▸ hb)
    obtain ⟨U, hU, hxU, hyU⟩ :=
      (exists_isClopen_of_totally_separated (α := closedPoints X)) hxy
    exact ⟨⟨U, hU⟩, hxU, hyU⟩
  constructor
  · intro x y hxy
    by_contra hne
    obtain ⟨U, hxU, hyU⟩ := hsep hne
    let E : Set X := (Subtype.val : closedPoints X → X) '' (U : Set (closedPoints X))
    let W : Set X := SpectralSubset.generalizationsOf E
    have hWclosed : IsClosed W := isClosed_generalizationsOf_clopen_closedPoints hunique U
    have hxW : (x : X) ∈ W := ⟨x, ⟨x, hxU, rfl⟩, specializes_rfl⟩
    have hyW : (y : X) ∉ W := by
      rintro ⟨c, ⟨d, hdU, rfl⟩, hcy⟩
      exact hyU ((hunique (y : X)).unique hcy specializes_rfl ▸ hdU)
    have hWcclosed : IsClosed Wᶜ := by
      let Wc : Set X := SpectralSubset.generalizationsOf
        ((Subtype.val : closedPoints X → X) '' (Uᶜ : Set (closedPoints X)))
      have heq : Wc = Wᶜ := by
        ext a
        constructor
        · rintro ⟨d, ⟨d, hd, rfl⟩, had⟩ ⟨e, ⟨e', he', rfl⟩, hae⟩
          exact hd ((hunique a).unique had hae ▸ he')
        · intro ha
          obtain ⟨d, hd, had⟩ := hunique a
          have hdU : d ∈ Uᶜ := by
            intro hdU
            exact ha ⟨d, ⟨d, hdU, rfl⟩, hd⟩
          exact ⟨d, ⟨d, hdU, rfl⟩, hd⟩
      exact heq ▸ isClosed_generalizationsOf_clopen_closedPoints hunique Uᶜ
    have hWclopen : IsClopen W :=
      ⟨hWclosed, by simpa only [compl_compl] using hWcclosed.isOpen_compl⟩
    exact hyW (hWclopen.connectedComponent_subset hxW
      (ConnectedComponents.coe_eq_coe.mp hxy ▸ mem_connectedComponent))
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨z, hzc, _⟩ := exists_closed_point_same_component X x
    exact ⟨z, hzc⟩

/-- **Stacks 0968, unique-specialization refinement.** If the closed points of a spectral space
form a closed subset and every point specializes to a unique closed point, every open cover has a
finite refinement by pairwise-disjoint clopen subsets. -/
@[stacks 0968 "unique_specialization_refinement"]
theorem exists_finite_disjoint_clopen_refinement_of_unique_closed_specialization
    {ι X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (hclosed : IsClosed (closedPoints X))
    (hunique : ∀ x : X, ∃! x₀ : closedPoints X, Specializes x x₀.1)
    {U : ι → Opens X} (hU : IsOpenCover U) :
    ∃ (n : ℕ) (W : Fin n → Clopens X),
      (∀ j, ∃ i, (W j : Set X) ⊆ U i) ∧
      (Set.univ : Set X) ⊆ ⋃ j, (W j : Set X) ∧
      Pairwise (Disjoint on W) :=
  ((clopen_refinement_iff_closedPoints_bijective X).2
    (closedPoints_bijective hclosed hunique)) U hU

/-- **Stacks 0968, unique-specialization refinement.** Under the same hypotheses, sending a
closed point to its connected component is a bijection from the closed points of `X` to
`π₀(X)`. -/
@[stacks 0968 "unique_specialization_refinement"]
theorem closedPoints_to_connectedComponents_bijective_of_unique_specialization
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (hclosed : IsClosed (closedPoints X))
    (hunique : ∀ x : X, ∃! x₀ : closedPoints X, Specializes x x₀.1) :
    Function.Bijective
      (fun x₀ : closedPoints X ↦ ConnectedComponents.mk x₀.1) :=
  closedPoints_bijective hclosed hunique

end AlgebraicGeometry.ProEtale

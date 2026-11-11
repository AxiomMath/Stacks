module

public import StacksFrontier.RingTheory.Jacobson.Constructions
public import StacksFrontier.RingTheory.Jacobson.FiniteType
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.GenericFinitePresentation.ConstructibleImage
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.Image

import StacksCore.Tactic.StacksAttribute

/-!
# Images of constructible sets under finite type maps of Jacobson rings

Let `R` be a Jacobson ring, let `S` be a finite type `R`-algebra (so `S` is Jacobson too, by
Stacks 00GB), and write `f : Spec S → Spec R` for the induced map of spectra. For a
constructible subset `E ⊆ Spec S`, and with a subscript `₀` denoting the points of a subset that
are closed in that subset (`subspaceClosedPoints`), this file proves Stacks Lemma 10.35.20
(Tag 00GD):

1. `f(E)₀ = f(E₀) = X₀ ∩ f(E)`;
2. a point `ξ ∈ Spec R` lies in `f(E)` if and only if `closure {ξ} ∩ f(E₀)` is dense in
   `closure {ξ}`.

## Main results

* `exists_mem_inter_closedPoints_of_isConstructible_of_isClosed`: in a Jacobson space, a
  constructible set meeting a closed set `F` meets it in a closed point.
* `mem_closedPoints_of_mem_subspaceClosedPoints`: in a Jacobson space, a point of a
  constructible set `C` which is closed in `C` is closed (Stacks 005X for constructible sets).
* `mem_range_comap_of_mem_closure_inter_range`: for any ring map `ψ`, a point `ξ` adherent to
  `closure {ξ} ∩ range (comap ψ)` lies in `range (comap ψ)`.
* `comap_image_subspaceClosedPoints_and_mem_image_iff`: Stacks 00GD.

## Implementation notes

Density of `closure {ξ} ∩ f(E₀)` in the closed set `closure {ξ}` is written
`closure {ξ} ⊆ closure (closure {ξ} ∩ f(E₀))`; the reverse inclusion always holds, so this
says the closure of `closure {ξ} ∩ f(E₀)` is `closure {ξ}`, which is what density in the
subspace `closure {ξ}` means.

In part (2), the "if" direction is proved without going through part (1): the density
hypothesis implies that `ξ` is adherent to `closure {ξ} ∩ f(E)`, and `f(E)` is the image of
`Spec S'` for a finitely presented `S`-algebra `S'` (Stacks 00F8), which reduces it to
`mem_range_comap_of_mem_closure_inter_range`. This is the content the source extracts from
Stacks 00FJ applied to `R/𝔭 → S'/𝔭S'`.
-/

@[expose] public section

open Topology

/-- In a Jacobson space, a constructible set `C` meeting a closed set `F` meets it in a point
which is closed in the whole space. -/
theorem exists_mem_inter_closedPoints_of_isConstructible_of_isClosed
    {Z : Type*} [TopologicalSpace Z] [JacobsonSpace Z]
    {C F : Set Z} (hC : IsConstructible C) (hF : IsClosed F) (hne : (C ∩ F).Nonempty) :
    ∃ z ∈ C ∩ F, z ∈ closedPoints Z := by
  have hSL : IsSublattice {U : Set Z | IsOpen U ∧ IsRetrocompact U} :=
    ⟨fun _ ha _ hb => ⟨ha.left.union hb.left, ha.right.union hb.right⟩,
     fun _ ha _ hb => ⟨ha.left.inter hb.left, ha.right.inter_isOpen hb.right hb.left⟩⟩
  have hbot : (⊥ : Set Z) ∈ {U : Set Z | IsOpen U ∧ IsRetrocompact U} :=
    ⟨isOpen_empty, IsRetrocompact.empty⟩
  have htop : (⊤ : Set Z) ∈ {U : Set Z | IsOpen U ∧ IsRetrocompact U} :=
    ⟨isOpen_univ, IsRetrocompact.univ⟩
  obtain ⟨t, ht⟩ := (BooleanSubalgebra.mem_closure_iff_sup_sdiff hSL hbot htop).mp hC
  obtain ⟨c, hcC, hcF⟩ := hne
  rw [ht, Finset.sup_set_eq_biUnion] at hcC
  simp only [Set.mem_iUnion] at hcC
  obtain ⟨p, hpt, hcp⟩ := hcC
  obtain ⟨⟨U, hU⟩, ⟨V, hV⟩⟩ := p
  have hLlc : IsLocallyClosed ((U \ V) ∩ F) :=
    ⟨U, Vᶜ ∩ F, hU.left, hV.left.isClosed_compl.inter hF, by
      rw [Set.sdiff_eq, Set.inter_assoc]⟩
  obtain ⟨z, ⟨hzL, hzF⟩, hzc⟩ := nonempty_inter_closedPoints
    (show ((U \ V) ∩ F).Nonempty from ⟨c, hcp, hcF⟩) hLlc
  refine ⟨z, ⟨?_, hzF⟩, hzc⟩
  rw [ht, Finset.sup_set_eq_biUnion]
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hpt, hzL⟩⟩

/-- If `a` is closed in the subspace `A` and `b ∈ A` lies in the closure of `{a}`, then
`b = a`. -/
theorem eq_of_mem_closure_singleton_of_mem_subspaceClosedPoints
    {Z : Type*} [TopologicalSpace Z] {A : Set Z} {a b : Z}
    (ha : a ∈ subspaceClosedPoints A) (hb : b ∈ A) (hab : b ∈ closure {a}) : b = a := by
  obtain ⟨⟨a, haA⟩, hacl, rfl⟩ := ha
  have hs : (⟨a, haA⟩ : A) ⤳ ⟨b, hb⟩ :=
    IsInducing.subtypeVal.specializes_iff.mp (specializes_iff_mem_closure.mpr hab)
  exact congrArg Subtype.val
    (Set.mem_singleton_iff.mp (hs.mem_closed (mem_closedPoints_iff.mp hacl) (Set.mem_singleton _)))

/-- **Stacks 005X, constructible case.** In a Jacobson space, a point of a constructible set
`C` which is closed in the subspace `C` is closed in the whole space. -/
theorem mem_closedPoints_of_mem_subspaceClosedPoints
    {Z : Type*} [TopologicalSpace Z] [JacobsonSpace Z]
    {C : Set Z} (hC : IsConstructible C) {z : Z} (hz : z ∈ subspaceClosedPoints C) :
    z ∈ closedPoints Z := by
  obtain ⟨w, ⟨hwC, hwz⟩, hwc⟩ := exists_mem_inter_closedPoints_of_isConstructible_of_isClosed
    (F := closure {z}) hC isClosed_closure
    ⟨z, subspaceClosedPoints_subset C hz, subset_closure (Set.mem_singleton z)⟩
  rwa [← eq_of_mem_closure_singleton_of_mem_subspaceClosedPoints hz hwC hwz]

/-- Let `ψ : R →+* T` be any ring map. If a point `ξ ∈ Spec R` lies in the closure of
`closure {ξ} ∩ range (comap ψ)`, then `ξ` lies in `range (comap ψ)`. -/
theorem mem_range_comap_of_mem_closure_inter_range
    {R T : Type*} [CommRing R] [CommRing T] (ψ : R →+* T) {ξ : PrimeSpectrum R}
    (h : ξ ∈ closure (closure {ξ} ∩ Set.range (PrimeSpectrum.comap ψ))) :
    ξ ∈ Set.range (PrimeSpectrum.comap ψ) := by
  rw [PrimeSpectrum.mem_range_comap_iff ψ]
  refine le_antisymm (fun r hr => ?_) Ideal.le_comap_map
  by_contra hrξ
  obtain ⟨_, haU, haξ, t, rfl⟩ := mem_closure_iff.mp h (PrimeSpectrum.basicOpen r)
    (PrimeSpectrum.basicOpen r).isOpen ((PrimeSpectrum.mem_basicOpen _ _).mpr hrξ)
  have hle : ξ.asIdeal ≤ (PrimeSpectrum.comap ψ t).asIdeal :=
    (PrimeSpectrum.le_iff_mem_closure _ _).mpr haξ
  rw [PrimeSpectrum.comap_asIdeal] at hle
  refine (PrimeSpectrum.mem_basicOpen _ _).mp haU ?_
  rw [PrimeSpectrum.comap_asIdeal]
  exact Ideal.mem_comap.mpr (Ideal.map_le_iff_le_comap.mpr hle (Ideal.mem_comap.mp hr))

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsJacobsonRing R]
  [Algebra.FiniteType R S]

/-- The comap of a closed point of `Spec S` is a closed point of `Spec R`, for `S` of finite
type over the Jacobson ring `R` (Stacks 00GB (2)). -/
theorem comap_mem_closedPoints_of_isJacobsonRing {y : PrimeSpectrum S}
    (hy : y ∈ closedPoints (PrimeSpectrum S)) :
    PrimeSpectrum.comap (algebraMap R S) y ∈ closedPoints (PrimeSpectrum R) := by
  rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hy ⊢
  rw [PrimeSpectrum.comap_asIdeal]
  have : y.asIdeal.IsMaximal := hy
  let : Field (S ⧸ y.asIdeal) := Ideal.Quotient.field _
  have h := Algebra.ker_algebraMap_isMaximal_of_finiteType_of_isJacobsonRing R (S ⧸ y.asIdeal)
  rwa [IsScalarTower.algebraMap_eq R S (S ⧸ y.asIdeal), ← RingHom.comap_ker,
    Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at h

variable {E : Set (PrimeSpectrum S)} (hE : IsConstructible E)
include hE

/-- `f(E₀) = X₀ ∩ f(E)` for `f = Spec S → Spec R` and `E ⊆ Spec S` constructible, `S` of finite
type over the Jacobson ring `R`. -/
theorem comap_image_subspaceClosedPoints_eq_closedPoints_inter :
    PrimeSpectrum.comap (algebraMap R S) '' subspaceClosedPoints E =
      closedPoints (PrimeSpectrum R) ∩ PrimeSpectrum.comap (algebraMap R S) '' E := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨comap_mem_closedPoints_of_isJacobsonRing (mem_closedPoints_of_mem_subspaceClosedPoints
      hE hy), y, subspaceClosedPoints_subset E hy, rfl⟩
  · rintro x ⟨hxc, hxE⟩
    have hx := closedPoints_inter_subset_subspaceClosedPoints _ ⟨hxc, hxE⟩
    obtain ⟨y, hyE, rfl⟩ := hxE
    obtain ⟨w, ⟨hwE, hwy⟩, hwc⟩ := exists_mem_inter_closedPoints_of_isConstructible_of_isClosed
      (F := PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        closure {PrimeSpectrum.comap (algebraMap R S) y})
      hE (isClosed_closure.preimage (PrimeSpectrum.continuous_comap (algebraMap R S)))
      ⟨y, hyE, subset_closure (Set.mem_singleton _)⟩
    refine ⟨w, closedPoints_inter_subset_subspaceClosedPoints _ ⟨hwc, hwE⟩, ?_⟩
    exact eq_of_mem_closure_singleton_of_mem_subspaceClosedPoints hx ⟨w, hwE, rfl⟩ hwy

/-- `f(E)₀ = f(E₀)` for `f = Spec S → Spec R` and `E ⊆ Spec S` constructible, `S` of finite
type over the Jacobson ring `R`. -/
theorem subspaceClosedPoints_comap_image_eq_comap_image_subspaceClosedPoints :
    subspaceClosedPoints (PrimeSpectrum.comap (algebraMap R S) '' E) =
      PrimeSpectrum.comap (algebraMap R S) '' subspaceClosedPoints E := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  rw [comap_image_subspaceClosedPoints_eq_closedPoints_inter hE]
  refine le_antisymm (fun x hx => ?_) (closedPoints_inter_subset_subspaceClosedPoints _)
  have hxE := subspaceClosedPoints_subset _ hx
  obtain ⟨y, hyE, rfl⟩ := hxE
  obtain ⟨w, ⟨hwE, hwy⟩, hwc⟩ := exists_mem_inter_closedPoints_of_isConstructible_of_isClosed
    (F := PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        closure {PrimeSpectrum.comap (algebraMap R S) y})
    hE (isClosed_closure.preimage (PrimeSpectrum.continuous_comap (algebraMap R S)))
    ⟨y, hyE, subset_closure (Set.mem_singleton _)⟩
  rw [← eq_of_mem_closure_singleton_of_mem_subspaceClosedPoints hx ⟨w, hwE, rfl⟩ hwy]
  exact ⟨comap_mem_closedPoints_of_isJacobsonRing hwc, w, hwE, rfl⟩

/-- A point `ξ ∈ Spec R` lies in `f(E)` if and only if `closure {ξ} ∩ f(E₀)` is dense in
`closure {ξ}`, for `f = Spec S → Spec R` and `E ⊆ Spec S` constructible, `S` of finite type over
the Jacobson ring `R`. -/
theorem mem_comap_image_iff_closure_singleton_subset_closure (ξ : PrimeSpectrum R) :
    ξ ∈ PrimeSpectrum.comap (algebraMap R S) '' E ↔
      closure {ξ} ⊆ closure (closure {ξ} ∩
        PrimeSpectrum.comap (algebraMap R S) '' subspaceClosedPoints E) := by
  constructor
  · intro hξ w hw
    obtain ⟨D, hDopen, hDdense, hDsub⟩ := image_constructible_contains_open_dense_in_closure
      (algebraMap R S) (RingHom.finiteType_algebraMap.mpr inferInstance) E hE ξ hξ
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hDopen
    rw [mem_closure_iff]
    intro U hU hwU
    obtain ⟨⟨v, hvξ⟩, hvU, hvO⟩ := hDdense.inter_open_nonempty _
      (hU.preimage continuous_subtype_val) ⟨⟨w, hw⟩, hwU⟩
    have hLlc : IsLocallyClosed ((O ∩ U) ∩ closure {ξ}) :=
      ⟨O ∩ U, closure {ξ}, hO.inter hU, isClosed_closure, rfl⟩
    obtain ⟨z, ⟨⟨hzO, hzU⟩, hzξ⟩, hzc⟩ :=
      nonempty_inter_closedPoints
        (show ((O ∩ U) ∩ closure {ξ}).Nonempty from ⟨v, ⟨hvO, hvU⟩, hvξ⟩) hLlc
    have hzE : z ∈ PrimeSpectrum.comap (algebraMap R S) '' E :=
      (hDsub ⟨⟨z, hzξ⟩, hzO, rfl⟩).2
    refine ⟨z, hzU, hzξ, ?_⟩
    rw [comap_image_subspaceClosedPoints_eq_closedPoints_inter hE]
    exact ⟨hzc, hzE⟩
  · intro h
    obtain ⟨S', _, g, -, hg⟩ :=
      PrimeSpectrum.exists_range_eq_of_isConstructible_finitePresentation hE
    have himage : PrimeSpectrum.comap (algebraMap R S) '' E ⊆
        Set.range (PrimeSpectrum.comap (g.comp (algebraMap R S))) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← hg] at hy
      obtain ⟨t, rfl⟩ := hy
      exact ⟨t, PrimeSpectrum.ext (Ideal.comap_comap _ _).symm⟩
    obtain ⟨t, ht⟩ := mem_range_comap_of_mem_closure_inter_range (g.comp (algebraMap R S))
      (closure_mono (Set.inter_subset_inter_right _
        ((Set.image_mono (subspaceClosedPoints_subset E)).trans himage))
        (h (subset_closure (Set.mem_singleton ξ))))
    rw [← ht, ← hg]
    exact ⟨PrimeSpectrum.comap g t, ⟨t, rfl⟩, PrimeSpectrum.ext (Ideal.comap_comap _ _)⟩

/-- **Stacks 00GD.** Let `R` be a Jacobson ring and `S` a finite type `R`-algebra (hence also
Jacobson, Stacks 00GB); write `X = Spec R`, `Y = Spec S` and `f : Y → X` for the induced map.
Let `E ⊆ Y` be constructible, and denote with a subscript `₀` the set of points of a subset
that are closed in it (`subspaceClosedPoints`; `X₀ = closedPoints X`). Then
1. `f(E)₀ = f(E₀) = X₀ ∩ f(E)`;
2. a point `ξ ∈ X` lies in `f(E)` if and only if `closure {ξ} ∩ f(E₀)` is dense in
   `closure {ξ}`, written `closure {ξ} ⊆ closure (closure {ξ} ∩ f(E₀))`. -/
@[stacks 00GD]
theorem comap_image_subspaceClosedPoints_and_mem_comap_image_iff :
    (subspaceClosedPoints (PrimeSpectrum.comap (algebraMap R S) '' E) =
        PrimeSpectrum.comap (algebraMap R S) '' subspaceClosedPoints E ∧
      PrimeSpectrum.comap (algebraMap R S) '' subspaceClosedPoints E =
        closedPoints (PrimeSpectrum R) ∩ PrimeSpectrum.comap (algebraMap R S) '' E) ∧
    ∀ ξ : PrimeSpectrum R, ξ ∈ PrimeSpectrum.comap (algebraMap R S) '' E ↔
      closure {ξ} ⊆ closure (closure {ξ} ∩
        PrimeSpectrum.comap (algebraMap R S) '' subspaceClosedPoints E) :=
  ⟨⟨subspaceClosedPoints_comap_image_eq_comap_image_subspaceClosedPoints hE,
    comap_image_subspaceClosedPoints_eq_closedPoints_inter hE⟩,
    mem_comap_image_iff_closure_singleton_subset_closure hE⟩

end

end

module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen
import all StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen

/-!
# Invariant affine neighbourhoods inside a given affine open (Stacks 03JE, refined)

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` finite locally free, and let `u` be a
point of `U` whose equivalence class `t(s⁻¹({u}))` is contained in an affine open `W` of `U`.
Then `u` has an `R`-invariant affine open neighbourhood contained in `W`. This refines
`AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem` (Stacks 03JE), which
gives an invariant affine open neighbourhood of `u` without the containment in `W`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_le`: a point whose
  equivalence class lies in an affine open `W` has an invariant affine open neighbourhood
  contained in `W`.
-/
@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- **Stacks 03JE, inside a given affine open.** Let `(U, R, s, t, c)` be a groupoid scheme with
`s` and `t` finite locally free, and let `u` be a point of `U` whose equivalence class
`t(s⁻¹({u}))` is contained in an affine open `W` of `U`. Then `u` has an `R`-invariant affine open
neighbourhood contained in `W`. -/
theorem exists_isInvariantOpen_isAffineOpen_mem_le
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (u : G.objects.left)
    (W : G.objects.left.Opens) (hWaff : IsAffineOpen W)
    (hTW : G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left)) :
    ∃ V : G.objects.left.Opens, IsInvariantOpen G V ∧ IsAffineOpen V ∧ u ∈ V ∧ V ≤ W := by
  obtain ⟨hsfin, -, -⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    G.source.left).mp inferInstance
  obtain ⟨htfin, -, -⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    G.target.left).mp inferInstance
  have hs : IsFinite G.source.left := hsfin
  have ht : IsFinite G.target.left := htfin
  have hTfin : (G.target.left.base '' (G.source.left.base ⁻¹' {u})).Finite :=
    (G.source.left.finite_preimage_singleton u).image _
  have hsatClosed : IsClosed (G.target.left.base ''
      (G.source.left.base ⁻¹' (W : Set G.objects.left)ᶜ)) :=
    G.target.left.isClosedMap _ (W.2.isClosed_compl.preimage G.source.left.continuous)
  have hTW' : G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆
      (G.target.left.base '' (G.source.left.base ⁻¹' (W : Set G.objects.left)ᶜ))ᶜ :=
    fun x hx => notMem_saturation_compl_of_subset G u hTW hx
  obtain ⟨f, hfT, hfW'⟩ := hWaff.exists_basicOpen_subset_of_finite hTfin
    (fun x hx => hTW hx) ⟨_, hsatClosed.isOpen_compl⟩ hTW'
  have hPaff : IsAffineOpen (G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) :=
    IsAffineHom.isAffine_preimage _ (hWaff.basicOpen f)
  have hle : G.source.left ⁻¹ᵁ G.objects.left.basicOpen f ≤ G.target.left ⁻¹ᵁ W := by
    intro r hr
    exact target_mem_of_source_notMem_saturation_compl G (hfW' hr)
  obtain ⟨hfin, hproj⟩ :=
    finite_projective_app_of_isFiniteLocallyFree G.source.left (hWaff.basicOpen f)
  let a : Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) :=
    G.target.left.appLE W (G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) hle f
  have hbo : G.arrows.left.basicOpen a =
      (G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) ⊓
        G.target.left ⁻¹ᵁ G.objects.left.basicOpen f :=
    Scheme.basicOpen_appLE _ _ _ hle f
  let : Algebra Γ(G.objects.left, G.objects.left.basicOpen f)
      Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) :=
    (G.source.left.app (G.objects.left.basicOpen f)).hom.toAlgebra
  let : Module.Finite Γ(G.objects.left, G.objects.left.basicOpen f)
      Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) := hfin
  let : Module.Projective Γ(G.objects.left, G.objects.left.basicOpen f)
      Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) := hproj
  have hiff : ∀ v : G.objects.left, v ∈ G.objects.left.basicOpen f →
      (v ∈ G.objects.left.basicOpen
          (Algebra.projectiveNorm Γ(G.objects.left, G.objects.left.basicOpen f) a) ↔
        ∀ p : G.arrows.left, G.source.left.base p = v → p ∈ G.arrows.left.basicOpen a) :=
    fun v hv => mem_basicOpen_projectiveNorm_iff G.source.left (hWaff.basicOpen f) hPaff
      hfin hproj a hv
  have hkey : ∀ w : G.objects.left,
      w ∈ G.objects.left.basicOpen
          (Algebra.projectiveNorm Γ(G.objects.left, G.objects.left.basicOpen f) a) ↔
        ∀ r : G.arrows.left, G.source.left.base r = w →
          G.target.left.base r ∈ G.objects.left.basicOpen f := by
    intro w
    constructor
    · intro hw r hr
      have hwf : w ∈ G.objects.left.basicOpen f := G.objects.left.basicOpen_le _ hw
      have hmem := (hiff w hwf).mp hw r hr
      rw [hbo] at hmem
      exact hmem.2
    · intro hall
      obtain ⟨r₀, hr₀s, hr₀t⟩ := subset_target_image_source_preimage G {w} rfl
      have hwf : w ∈ G.objects.left.basicOpen f := hr₀t ▸ hall r₀ hr₀s
      refine (hiff w hwf).mpr fun p hp => ?_
      rw [hbo]
      exact ⟨show G.source.left.base p ∈ G.objects.left.basicOpen f from hp ▸ hwf, hall p hp⟩
  refine ⟨G.objects.left.basicOpen
      (Algebra.projectiveNorm Γ(G.objects.left, G.objects.left.basicOpen f) a),
    isInvariantSet_of_forall_target_mem G hkey, (hWaff.basicOpen f).basicOpen _, ?_,
    (G.objects.left.basicOpen_le _).trans (G.objects.left.basicOpen_le _)⟩
  exact (hkey u).mpr fun r hr => hfT ⟨r, hr, rfl⟩

end AlgebraicGeometry.GroupoidScheme

end

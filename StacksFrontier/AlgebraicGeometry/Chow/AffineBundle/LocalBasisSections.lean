module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle

/-!
# Local bases of the sections of a finite locally free sheaf

Let `X` be a scheme and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r`. Around every
point of `X` there is an open neighbourhood `U` such that over *every* affine open `V ⊆ U` the
sections `Γ(ℰ, V)` are a free `Γ(X, V)`-module with a basis indexed by `Fin r`; in particular such
affine opens can be found inside any given neighbourhood of the point.
`Stacks.Chow.exists_isAffineOpen_basis_sections` gives one such affine open around each point.

## Main results

* `Stacks.Chow.exists_forall_isAffineOpen_basis_sections` — the sections are free over every
  affine open inside a suitable neighbourhood of a point.
* `Stacks.Chow.exists_isAffineOpen_basis_sections_le` — an affine open with free sections around
  a point, inside any given open neighbourhood of it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Chow

/-- **A finite locally free sheaf of rank `r` is free on a neighbourhood of every point**, in the
sense that its sections over every affine open contained in that neighbourhood are a free module
with a basis indexed by `Fin r`. -/
theorem exists_forall_isAffineOpen_basis_sections {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
      Nonempty (Module.Basis (Fin r) Γ(X, V) Γ(E, V)) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf E r x
  refine ⟨U, hxU, fun V hV hVU => ?_⟩
  have hr : Set.range hV.fromSpec.base ⊆ Set.range U.ι.base := by
    rw [← Scheme.Hom.coe_opensRange, hV.opensRange_fromSpec, Scheme.Opens.range_ι]
    exact fun y hy => hVU hy
  obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset U.ι hV.fromSpec E
    (ULift.{u} (Fin r)) hr e
  have hb := (tilde_fixed_free_iff_basis Γ(X, V) Γ(E, V) (ULift.{u} (Fin r))).mp
    ⟨Stacks.Modules.tildeIsoRestrictFromSpec E hV ≪≫ e'⟩
  exact hb.map fun b ↦ b.reindex Equiv.ulift

/-- **A finite locally free sheaf of rank `r` has free sections of rank `r` over arbitrarily
small affine opens.** Inside every open neighbourhood `W` of a point there is an affine open `V`
around the point on which `Γ(ℰ, V)` is a free `Γ(X, V)`-module with a basis indexed by `Fin r`. -/
theorem exists_isAffineOpen_basis_sections_le {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] {x : X}
    {W : X.Opens} (hxW : x ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W ∧
      Nonempty (Module.Basis (Fin r) Γ(X, V) Γ(E, V)) := by
  obtain ⟨U, hxU, hU⟩ := exists_forall_isAffineOpen_basis_sections E r x
  obtain ⟨V, hV, hxV, hVUW⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show x ∈ U ⊓ W from ⟨hxU, hxW⟩)
  exact ⟨V, hV, hxV, fun y hy => (hVUW hy).2, hU V hV fun y hy => (hVUW hy).1⟩

end Stacks.Chow

end

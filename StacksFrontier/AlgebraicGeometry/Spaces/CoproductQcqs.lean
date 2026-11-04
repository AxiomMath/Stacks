module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.Topology.Spectral.Sigma

/-!
# Finite coproducts of quasi-compact quasi-separated schemes

A finite coproduct of quasi-compact schemes is quasi-compact, and a finite coproduct of
quasi-separated schemes is quasi-separated: the underlying space of a coproduct of schemes is the
disjoint union of the underlying spaces.

## Main results

* `AlgebraicGeometry.compactSpace_sigmaObj`
* `AlgebraicGeometry.quasiSeparatedSpace_sigmaObj`

## Implementation notes

Mathlib's `AlgebraicGeometry.sigmaMk`, the homeomorphism of the coproduct with the disjoint union,
is stated for a family indexed by a type of the schemes' own universe; the families here are
indexed by an arbitrary finite type, so they are first reindexed by `ULift (Fin n)` along
`CategoryTheory.Limits.Sigma.reindex`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A finite type is equivalent to `ULift (Fin n)` for some `n`. -/
private theorem exists_nonempty_equiv_ulift_fin (σ : Type*) [Finite σ] :
    ∃ n : ℕ, Nonempty (ULift.{u} (Fin n) ≃ σ) :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  ⟨n, ⟨Equiv.ulift.trans e.symm⟩⟩

/-- **A finite coproduct of quasi-compact schemes is quasi-compact.** -/
theorem compactSpace_sigmaObj {σ : Type*} [Finite σ] (g : σ → Scheme.{u})
    [∀ i, CompactSpace (g i)] : CompactSpace (∐ g : Scheme.{u}) := by
  obtain ⟨n, ⟨ε⟩⟩ := exists_nonempty_equiv_ulift_fin.{u} σ
  have _ (i : ULift.{u} (Fin n)) : CompactSpace ((g ∘ ε) i) :=
    inferInstanceAs (CompactSpace (g (ε i)))
  have _ : CompactSpace (∐ (g ∘ ε) : Scheme.{u}) := (sigmaMk (g ∘ ε)).compactSpace
  exact (Scheme.homeoOfIso (Sigma.reindex ε g)).compactSpace

/-- **A finite coproduct of quasi-separated schemes is quasi-separated.** -/
theorem quasiSeparatedSpace_sigmaObj {σ : Type*} [Finite σ] (g : σ → Scheme.{u})
    [∀ i, QuasiSeparatedSpace (g i)] : QuasiSeparatedSpace (∐ g : Scheme.{u}) := by
  obtain ⟨n, ⟨ε⟩⟩ := exists_nonempty_equiv_ulift_fin.{u} σ
  have _ (i : ULift.{u} (Fin n)) : QuasiSeparatedSpace ((g ∘ ε) i) :=
    inferInstanceAs (QuasiSeparatedSpace (g (ε i)))
  have _ (i : ULift.{u} (Fin n)) : PrespectralSpace ((g ∘ ε) i) := inferInstance
  exact (quasiSeparatedSpace_congr (Scheme.homeoOfIso (Sigma.reindex ε g))).mp
    ((quasiSeparatedSpace_congr (sigmaMk (g ∘ ε))).mp
      (quasiSeparatedSpace_sigma fun i ↦ (((g ∘ ε) i : Scheme.{u}) : Type u)))

end AlgebraicGeometry

end

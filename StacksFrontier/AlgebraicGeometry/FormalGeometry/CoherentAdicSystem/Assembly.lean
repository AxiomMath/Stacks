module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition

/-!
# Assembling a coherent adic system from its terms

A sequence of coherent `𝒪_X`-modules `G_0, G_1, …` in which `G_n` is annihilated by `𝒦 ⁿ⁺¹`
and is identified with `G_{n+1} / 𝒦 ⁿ⁺¹ G_{n+1}` is an object of `Coh(X, 𝒦)`, with the
transition maps read off those identifications.

## Main definitions

* `Stacks.Coherent.succQuotientSystem` — the inverse system `n ↦ G_n` whose successive
  transition is the quotient projection followed by the given identification.
* `Stacks.Coherent.coherentAdicOfSuccQuotientIso` — the resulting object of `Coh(X, 𝒦)`.

## Main results

* `Stacks.Coherent.isCoherentAdicSystem_succQuotientSystem` — **the assembled system is a
  coherent adic system.**
* `Stacks.Coherent.exists_coherentAdicSystem_of_succQuotientIso` — the same statement with the
  identifications given only up to `Nonempty`, which is the form in which they arise from an
  essential-surjectivity argument.

## Implementation notes

The system is zero-indexed as everywhere in this directory: term `n` is the source's `F_{n+1}`,
annihilated by `𝒦 ⁿ⁺¹`.

The functor is written out with its `obj` field given explicitly, as in
`Stacks.Coherent.transferSystem`, so that `(succQuotientSystem 𝒦 G e).obj (op n)` is `G n` by
definition; the action on morphisms is borrowed from `CategoryTheory.Functor.ofOpSequence`.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} (K : X.IdealSheafData) (G : ℕ → X.Modules)
  (e : ∀ n : ℕ, idealPowerQuotient K (n + 1) (G (n + 1)) ≅ G n)

/-- The transition map forced by an identification of `G_n` with `G_{n+1} / 𝒦 ⁿ⁺¹ G_{n+1}`. -/
public abbrev succQuotientStep (n : ℕ) : G (n + 1) ⟶ G n :=
  cokernel.π (C := X.Modules) (idealPowerMultiple K (n + 1) (G (n + 1))).ι ≫ (e n).hom

/-- The inverse system `n ↦ G_n` assembled from a sequence of modules together with
identifications of each term with the next one divided by the corresponding power. -/
public def succQuotientSystem : ℕᵒᵖ ⥤ X.Modules where
  obj n := G n.unop
  map {_ _} f := (Functor.ofOpSequence (X := G) (succQuotientStep K G e)).map f
  map_id _ := (Functor.ofOpSequence (X := G) (succQuotientStep K G e)).map_id _
  map_comp f g := (Functor.ofOpSequence (X := G) (succQuotientStep K G e)).map_comp f g

/-- The terms of the assembled system are the given modules. -/
@[simp]
public theorem succQuotientSystem_obj (n : ℕᵒᵖ) :
    (succQuotientSystem K G e).obj n = G n.unop := rfl

/-- The successive transition of the assembled system is the forced one. -/
public theorem succQuotientSystem_map_succ (n : ℕ) :
    (succQuotientSystem K G e).map (homOfLE (Nat.le_succ n)).op = succQuotientStep K G e n := by
  dsimp only [succQuotientSystem]
  simp only [Functor.ofOpSequence_map_homOfLE_succ]

/-- **A sequence of coherent modules with successive quotient identifications is a coherent adic
system.** The three clauses of `Stacks.Coherent.IsCoherentAdicSystem` are the three hypotheses:
coherence of each term, annihilation of the `n`-th term by `𝒦 ⁿ⁺¹`, and the identification of
`G_n` with `G_{n+1} / 𝒦 ⁿ⁺¹ G_{n+1}`, which by construction intertwines the quotient projection
with the transition map.

This is the constructor the library was missing: every other producer of
`IsCoherentAdicSystem` transports a system that already exists. -/
public theorem isCoherentAdicSystem_succQuotientSystem
    (hcoh : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent.{u} (G n))
    (hann : ∀ n : ℕ, idealPowerMultiple K (n + 1) (G n) = ⊥) :
    IsCoherentAdicSystem K (succQuotientSystem K G e) :=
  ⟨hcoh, hann, fun n => ⟨e n, (succQuotientSystem_map_succ K G e n).symm⟩⟩

/-- The object of `Coh(X, 𝒦)` assembled from a sequence of coherent modules with successive
quotient identifications. -/
public def coherentAdicOfSuccQuotientIso
    (hcoh : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent.{u} (G n))
    (hann : ∀ n : ℕ, idealPowerMultiple K (n + 1) (G n) = ⊥) :
    CoherentAdicSystems K :=
  ⟨succQuotientSystem K G e, isCoherentAdicSystem_succQuotientSystem K G e hcoh hann⟩

/-- The terms of the assembled object of `Coh(X, 𝒦)` are the given modules. -/
public theorem coherentAdicOfSuccQuotientIso_obj_obj
    (hcoh : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent.{u} (G n))
    (hann : ∀ n : ℕ, idealPowerMultiple K (n + 1) (G n) = ⊥) (n : ℕᵒᵖ) :
    (coherentAdicOfSuccQuotientIso K G e hcoh hann).obj.obj n = G n.unop := rfl

end Stacks.Coherent

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-- **The assembly in existential form.** Identifications of `G_n` with
`G_{n+1} / 𝒦 ⁿ⁺¹ G_{n+1}` given only up to `Nonempty` — the form in which an
essential-surjectivity argument delivers them — still produce an object of `Coh(X, 𝒦)` whose
terms are the `G_n`. -/
public theorem exists_coherentAdicSystem_of_succQuotientIso (K : X.IdealSheafData)
    (G : ℕ → X.Modules) (hcoh : ∀ n : ℕ, _root_.SheafOfModules.IsCoherent.{u} (G n))
    (hann : ∀ n : ℕ, idealPowerMultiple K (n + 1) (G n) = ⊥)
    (he : ∀ n : ℕ, Nonempty (idealPowerQuotient K (n + 1) (G (n + 1)) ≅ G n)) :
    ∃ F : CoherentAdicSystems K, ∀ n : ℕᵒᵖ, F.obj.obj n = G n.unop :=
  ⟨coherentAdicOfSuccQuotientIso K G (fun n => (he n).some) hcoh hann,
    coherentAdicOfSuccQuotientIso_obj_obj K G (fun n => (he n).some) hcoh hann⟩

end Stacks.Coherent

end

module

public import Mathlib.Algebra.Module.Presentation.Finite
public import Mathlib.Algebra.Module.Presentation.Tensor
public import Mathlib.Basic.Finite.Sum
import StacksCore.Tactic.StacksAttribute

/-!
## Tensor products of finite and of finitely presented modules

Stacks tag 05BS: for `R`-modules `M` and `N`,

* if `M` and `N` are finite, then so is `M ⊗[R] N` (`Module.Finite.tensorProduct`, upstream);
* if `M` and `N` are finitely presented, then so is `M ⊗[R] N`
  (`Module.FinitePresentation.tensorProduct`).

Part 2 comes from `Module.Presentation.tensor`, which turns presentations of `M` and `N` into a
presentation of `M ⊗[R] N` with generators `G₁ × G₂` and relations `(R₁ × G₂) ⊕ (G₁ × R₂)`; both
index types are then finite for free.

Part 1 holds over a `CommSemiring`, whereas part 2 is stated over a `CommRing`, since
`Module.Presentation` is only developed there.
-/

@[expose] public section

open TensorProduct

add_to_stacks 074G "part 1" Module.Finite.tensorProduct
add_to_stacks 074H "part 1" Module.Finite.tensorProduct
add_to_stacks 05BS "part 1" Module.Finite.tensorProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Stacks 05BS (2).** The tensor product of two finitely presented modules is finitely
presented. -/
@[stacks 05BS "part 2"]
instance Module.FinitePresentation.tensorProduct
    [Module.FinitePresentation R M] [Module.FinitePresentation R N] :
    Module.FinitePresentation R (M ⊗[R] N) := by
  -- Pin the universes of the generator and relation index types; they are finite, so `Type` does.
  have hM : ∃ p : Module.Presentation.{0, 0} R M, Finite p.G ∧ Finite p.R :=
    Module.finitePresentation_iff_exists_presentation.mp ‹_›
  have hN : ∃ p : Module.Presentation.{0, 0} R N, Finite p.G ∧ Finite p.R :=
    Module.finitePresentation_iff_exists_presentation.mp ‹_›
  obtain ⟨p, _, _⟩ := hM
  obtain ⟨q, _, _⟩ := hN
  -- Instance search does not see through the projections of `Module.Presentation.tensor`.
  have : Finite (p.tensor q).G := inferInstanceAs (Finite (p.G × q.G))
  have : Finite (p.tensor q).R := inferInstanceAs (Finite (Sum (p.R × q.G) (p.G × q.R)))
  exact (p.tensor q).finitePresentation

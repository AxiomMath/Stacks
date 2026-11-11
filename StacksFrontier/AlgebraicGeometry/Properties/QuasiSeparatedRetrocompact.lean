module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact opens of a quasi-separated scheme

In the Stacks Project a scheme `X` is quasi-separated when its structure morphism
`X ⟶ Spec ℤ` is quasi-separated. Here this is `QuasiSeparated (terminal.from X)`, the morphism
to the terminal scheme. For such a scheme the intersection of two quasi-compact opens is a
quasi-compact open, and every quasi-compact open is retrocompact.

## Main results

* `AlgebraicGeometry.Scheme.isCompact_inter_of_quasiSeparated`: **Stacks 054D**, the
  intersection of two quasi-compact opens is a quasi-compact open.
* `AlgebraicGeometry.Scheme.isRetrocompact_of_quasiSeparated`: **Stacks 054D**, every
  quasi-compact open is retrocompact.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Let `X` be a quasi-separated scheme, i.e. `X ⟶ Spec ℤ` (the morphism to the terminal
scheme) is quasi-separated. The intersection of any two quasi-compact opens `U`, `V` of `X` is a
quasi-compact open of `X`. -/
@[stacks 054D "first assertion; Stacks' quasi-separated scheme is a quasi-separated \
  morphism to the terminal scheme"]
theorem isCompact_inter_of_quasiSeparated (X : Scheme) [QuasiSeparated (terminal.from X)]
    {U V : Set X} (hU : IsOpen U) (hU' : IsCompact U) (hV : IsOpen V) (hV' : IsCompact V) :
    IsOpen (U ∩ V) ∧ IsCompact (U ∩ V) := by
  have : QuasiSeparatedSpace X := (quasiSeparatedSpace_iff_quasiSeparated X).2 inferInstance
  exact ⟨hU.inter hV, QuasiSeparatedSpace.inter_isCompact U V hU hU' hV hV'⟩

/-- Let `X` be a quasi-separated scheme, i.e. `X ⟶ Spec ℤ` (the morphism to the terminal
scheme) is quasi-separated. Every quasi-compact open `U` of `X` is retrocompact in `X`: its
intersection with every quasi-compact open of `X` is quasi-compact. -/
@[stacks 054D "second assertion; Stacks' quasi-separated scheme is a quasi-separated \
  morphism to the terminal scheme"]
theorem isRetrocompact_of_quasiSeparated (X : Scheme) [QuasiSeparated (terminal.from X)]
    {U : Set X} (hU : IsOpen U) (hU' : IsCompact U) : IsRetrocompact U :=
  fun _ hV' hV ↦ (isCompact_inter_of_quasiSeparated X hU hU' hV hV').2

end AlgebraicGeometry.Scheme

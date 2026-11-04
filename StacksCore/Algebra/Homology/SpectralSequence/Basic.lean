module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Spectral sequences: Stacks 011N (1), (2)

Stacks 011N: a spectral sequence in an abelian category `𝒜` is a system `(E_r, d_r)_{r ≥ 1}` of
objects `E_r` and morphisms `d_r : E_r → E_r` with `d_r ∘ d_r = 0` and
`E_{r+1} = Ker(d_r)/Im(d_r)`; Stacks loosens this to `E_{r+1}` being an object with a given
isomorphism to `Ker(d_r)/Im(d_r)`, and also calls systems `(E_r, d_r)_{r ≥ r₀}` spectral
sequences. A morphism is a family `f_r : E_r → E'_r` commuting with the `d_r` and such that
`f_{r+1}` is the map induced by `f_r` on `Ker(d_r)/Im(d_r)`. Stacks 0AMI is the graded variant:
`E_r` graded or bigraded, with translation functors `T_r`, `d_r : E_r → T_r E_r`,
`T_r d_r ∘ d_r = 0` and `E_{r+1} = Ker(d_r)/Im(T_r^{-1} d_r)`.

Mathlib's `CategoryTheory.SpectralSequence C c r₀` (Joël Riou) is exactly the loosened notion in
the 0AMI generality: for a family of complex shapes `c : ℤ → ComplexShape κ`, the page `E_r` is a
homological complex of shape `c r` (an object `E_r^{pq}` for each `pq : κ` and differentials
`d_r : E_r^{pq} ⟶ E_r^{pq'}` for `(c r).Rel pq pq'`, squaring to zero), and `E.iso r (r + 1) pq`
identifies `E_{r+1}^{pq}` with the homology of `E_r` at `pq`, that is
`Ker(d_r out of pq)/Im(d_r into pq)`. The translation functor `T_r` is the shape `c r`; the
bigraded cohomological case is `CohomologicalSpectralSequence C r₀` (`κ = ℤ × ℤ`,
`T_r = (r, 1 - r)`). Morphisms are `SpectralSequence.Hom`: morphisms of homological complexes
`f_r : E_r ⟶ E'_r` (so they commute with the `d_r`) compatible with the identifications
`E_{r+1} ≅ H(E_r)`, i.e. `f_{r+1}` is the map induced in homology by `f_r`
(`SpectralSequence.Hom.comm`). The `add_to_stacks` lines below record this on Mathlib's
declarations; the only declarations of this file are the abbreviations for the ungraded case.

Stacks' ungraded case is `SpectralSequence.Ungraded C r₀`, an abbreviation for
`SpectralSequence C (fun _ ↦ ComplexShape.refl Unit) r₀`: a homological complex of shape
`ComplexShape.refl Unit` is a single object `X ()` with an endomorphism `d () ()` squaring to
zero. `Ungraded.X r`, `Ungraded.d r`, `Ungraded.d_comp_d`, `Ungraded.homologyIso`
(`Ker(d_r)/Im(d_r) ≅ E_{r+1}`) and `Ungraded.Hom.f`, `Ungraded.Hom.d_f`,
`Ungraded.Hom.homologyMap_comm` spell out `(E_r, d_r)` and `(f_r)` in Stacks' notation; they are
one-line abbreviations, not an API. Stacks' `(E_r, d_r)_{r ≥ 1}` is the case `r₀ = 1`; the remark
that a system starting at another `r₀` is "also" a spectral sequence (by renumbering) is covered
by the parameter `r₀`, and no reindexing equivalence is provided.

The towers `B_r ⊆ Z_r ⊆ E_{r₀}` of 011N and the limit `E_∞` of 011O are in
`StacksCore.Algebra.Homology.SpectralSequence.Tower`, on top of the ports of Riou's edge maps and
infinity page (mathlib#25848) in `StacksCore.Algebra.Homology.SpectralSequence.EdgeStep` and
`StacksCore.Algebra.Homology.SpectralSequence.PageInfinity`.
-/

@[expose] public section

add_to_stacks 011N "(1) `(E_r, d_r)_{r ≥ r₀}` with `E_{r+1} ≅ Ker(d_r)/Im(d_r)`; any shapes"
  CategoryTheory.SpectralSequence
add_to_stacks 011N "(2) `f_r : E_r ⟶ E'_r` commuting with `d_r`, `f_{r+1}` induced by `f_r`"
  CategoryTheory.SpectralSequence.Hom

namespace CategoryTheory.SpectralSequence

variable (C : Type*) [Category* C] [Abelian C] (r₀ : ℤ)

/-- Stacks' ungraded spectral sequences `(E_r, d_r)_{r ≥ r₀}` in `C`: `E_r ∈ C`,
`d_r : E_r → E_r` with `d_r ∘ d_r = 0`, and `E_{r+1} ≅ Ker(d_r)/Im(d_r)`. This is Mathlib's
`SpectralSequence` for the shape `ComplexShape.refl Unit` on every page: a homological complex of
that shape is one object `X ()` with one differential `d () () : X () ⟶ X ()` squaring to zero.
Stacks' `(E_r, d_r)_{r ≥ 1}` is `r₀ = 1`. -/
@[stacks 011N "(1) the ungraded case: `d_r : E_r → E_r`, `E_{r+1} ≅ Ker(d_r)/Im(d_r)`"]
abbrev Ungraded := SpectralSequence C (fun _ ↦ ComplexShape.refl Unit) r₀

namespace Ungraded

variable {C r₀} (E : Ungraded C r₀)

/-- `E_r`, the `r`-th term of an ungraded spectral sequence. -/
abbrev X (r : ℤ) (hr : r₀ ≤ r := by lia) : C := (E.page r hr).X ()

/-- `d_r : E_r → E_r`. -/
abbrev d (r : ℤ) (hr : r₀ ≤ r := by lia) : E.X r ⟶ E.X r := (E.page r hr).d () ()

/-- `d_r ∘ d_r = 0`. -/
lemma d_comp_d (r : ℤ) (hr : r₀ ≤ r := by lia) : E.d r ≫ E.d r = 0 :=
  (E.page r hr).d_comp_d () () ()

/-- `E_{r+1} ≅ Ker(d_r)/Im(d_r)`: the homology of `E_r` (Mathlib's `homology` of the one-object
complex `(E_r, d_r)`) is `E_{r+1}`. -/
abbrev homologyIso (r : ℤ) (hr : r₀ ≤ r := by lia) : (E.page r hr).homology () ≅ E.X (r + 1) :=
  E.iso r (r + 1) () rfl hr

variable {E} {E' : Ungraded C r₀}

/-- `f_r : E_r → E'_r`, the `r`-th component of a morphism of ungraded spectral sequences. -/
abbrev Hom.f (φ : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r := by lia) : E.X r ⟶ E'.X r := (φ.hom r hr).f ()

/-- `f_r` commutes with `d_r`. -/
lemma Hom.d_f (φ : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.d r ≫ Hom.f φ r = Hom.f φ r ≫ E'.d r :=
  ((φ.hom r hr).comm () ()).symm

/-- `f_{r+1}` is the map induced by `f_r` on `Ker(d_r)/Im(d_r)`. -/
lemma Hom.homologyMap_comm (φ : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r := by lia) :
    HomologicalComplex.homologyMap (φ.hom r hr) () ≫ (E'.homologyIso r).hom =
      (E.homologyIso r).hom ≫ Hom.f φ (r + 1) :=
  φ.comm r (r + 1) () rfl hr

end Ungraded

end CategoryTheory.SpectralSequence

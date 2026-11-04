module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Standard refinements of affine open covers

Given an affine open cover of a scheme, every affine open of that scheme carries a finite
standard open cover each of whose members is also a standard open in one member of the given
cover.

## Main results

* `AlgebraicGeometry.Scheme.exists_isStandardOpenCover_basicOpen_eq_of_iSup_eq_top`: the finite
  standard refinement, together with the choice of a member of the original cover containing
  each of its members.

## Implementation notes

The refinement is indexed by `Fin n`. Each of its members is presented twice: by a section on
the affine open being covered, and by a section on the chosen member of the original cover whose
standard open coincides with it. Both the ring-theoretic standard-cover condition of Tag 01HT
and its realization as a cover by opens of the ambient scheme are recorded.

## References

* [Stacks Project, Tag 01IX](https://stacks.math.columbia.edu/tag/01IX)
-/

@[expose] public section

open TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u v

/-- Every affine open has a finite standard open cover each of whose members is also a standard
open in a member of a given affine open cover of the ambient scheme. -/
@[stacks 01IX]
theorem exists_isStandardOpenCover_basicOpen_eq_of_iSup_eq_top
    (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUcover : ⨆ i, U i = ⊤)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, V)) (i : Fin n → ι)
      (g : ∀ j, Γ(X, U (i j))),
      PrimeSpectrum.IsStandardOpenCoverOfSpectrum f ∧
        (⨆ j, X.basicOpen (f j)) = V ∧
        ∀ j, X.basicOpen (f j) = X.basicOpen (g j) := by
  classical
  have hlocal : ∀ x : V, ∃ (i : ι) (f : Γ(X, V)) (g : Γ(X, U i)),
      X.basicOpen f = X.basicOpen g ∧ x.1 ∈ X.basicOpen f := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hUcover.ge (Set.mem_univ x.1))
    obtain ⟨f, g, hfg, hx⟩ :=
      exists_basicOpen_le_affine_inter hV (hU i) x.1 ⟨x.2, hi⟩
    exact ⟨i, f, g, hfg, hfg ▸ hx⟩
  choose i₀ f₀ g₀ hfg₀ hx₀ using hlocal
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover
    (fun x : V => (X.basicOpen (f₀ x) : Set X))
    (fun x => (X.basicOpen (f₀ x)).2)
    fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hx₀ ⟨x, hx⟩⟩
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let f : Fin (Fintype.card t) → Γ(X, V) := fun j => f₀ (e.symm j)
  let i : Fin (Fintype.card t) → ι := fun j => i₀ (e.symm j)
  let g : ∀ j, Γ(X, U (i j)) := fun j => g₀ (e.symm j)
  have hcover : (⨆ j, X.basicOpen (f j)) = V := by
    apply le_antisymm (iSup_le fun j => X.basicOpen_le _)
    intro x hx
    obtain ⟨_, ⟨y, rfl⟩, hxy⟩ := ht hx
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hxy
    exact (le_iSup (fun j => X.basicOpen (f j)) (e ⟨y, hy⟩)) (by simpa [f] using hxy)
  refine ⟨Fintype.card t, f, i, g, ?_, hcover, fun j => hfg₀ (e.symm j)⟩
  show (⨆ j, PrimeSpectrum.basicOpen (f j)) = PrimeSpectrum.basicOpen (1 : Γ(X, V))
  rw [PrimeSpectrum.basicOpen_one, PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  exact (hV.iSup_basicOpen_eq_self_iff (s := Set.range f)).mp
    (by simpa only [iSup_range'] using hcover)

end AlgebraicGeometry.Scheme

end

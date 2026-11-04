module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine opens lying over affine opens

For a morphism of schemes `f : X ⟶ S`, the affine opens `U ⊆ X` which map into some affine open
of `S` form a basis of the topology of `X`. The proofs of Stacks 0E2W and Stacks 0E2X glue along
this collection `ℬ`, through Stacks 0D66 and the BBD glueing lemma Stacks 0D6C, whose two
hypotheses on the collection are proved here: the members cover `X`, and the intersection of two
members (indeed every open) is the union of the members it contains.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.chartOpens`: the collection `ℬ`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isBasis_chartOpens`: `ℬ` is a basis of the topology of `X`.
* `AlgebraicGeometry.Scheme.Hom.eq_sSup_chartOpens`: every open is the union of the members of
  `ℬ` it contains.
* `AlgebraicGeometry.Scheme.Hom.sSup_chartOpens`: the members of `ℬ` cover `X`.

## References

* [Stacks Project, Lemma 48.28.5 (Tag 0E2W)](https://stacks.math.columbia.edu/tag/0E2W)
* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Theorem 20.45.8 (Tag 0D6C)](https://stacks.math.columbia.edu/tag/0D6C)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The affine opens of `X` which map into an affine open of `S`. -/
def chartOpens : Set X.Opens :=
  {U | IsAffineOpen U ∧ ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ f ⁻¹ᵁ V}

variable {f} in
/-- An open `U` of `X` lies in `chartOpens f` if and only if it is affine and contained in the
preimage of an affine open of `S`. -/
theorem mem_chartOpens {U : X.Opens} :
    U ∈ chartOpens f ↔ IsAffineOpen U ∧ ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ f ⁻¹ᵁ V :=
  Iff.rfl

/-- The affine opens of `X` mapping into an affine open of `S` form a basis of `X`. -/
theorem isBasis_chartOpens : Opens.IsBasis (chartOpens f) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {O x} hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := (isBasis_affineOpens S).exists_subset_of_mem_open
    (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := (isBasis_affineOpens X).exists_subset_of_mem_open
    (show x ∈ ((O ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) from ⟨hx, hxV⟩) (O ⊓ f ⁻¹ᵁ V).isOpen
  exact ⟨U, ⟨hU, V, hV, fun y hy => (hUO hy).2⟩, hxU, fun y hy => (hUO hy).1⟩

/-- Every open of `X` is the union of the members of `chartOpens f` it contains. -/
theorem eq_sSup_chartOpens (O : X.Opens) : O = sSup {W | W ∈ chartOpens f ∧ W ≤ O} := by
  refine le_antisymm (fun x hx => ?_) (sSup_le fun W hW => hW.2)
  obtain ⟨W, hW, hxW, hWO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_chartOpens f) hx
  exact Opens.mem_sSup.mpr ⟨W, ⟨hW, hWO⟩, hxW⟩

/-- The members of `chartOpens f` cover `X`. -/
theorem sSup_chartOpens : sSup (chartOpens f) = ⊤ := by
  refine top_le_iff.mp ((eq_sSup_chartOpens f ⊤).le.trans (sSup_le_sSup fun W hW => hW.1))

end AlgebraicGeometry.Scheme.Hom

end

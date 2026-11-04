module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# Finiteness of a field whose unit group is finitely generated over the units of the base

Let `K` be a Jacobson ring and `L` a field which is a `K`-algebra. If the group `Lˣ` modulo the
image of `Kˣ` is finitely generated, then `L` is a finite `K`-module.

Lifting a finite generating set of the quotient to units of `L` and adjoining those units
together with their inverses produces a `K`-subalgebra containing every unit of `L`, because the
units lying in that subalgebra together with their inverses form a subgroup which contains both
the image of `Kˣ` and the chosen lifts. Since `L` is a field, every nonzero element is a unit, so
the subalgebra is all of `L` and `L` is of finite type over `K`. Zariski's lemma over a Jacobson
ring then upgrades finite type to finite.

## Main results

* `Stacks.Jacobson.finite_of_fg_units_quotient`: the finiteness statement above.
-/

@[expose] public section

namespace Stacks.Jacobson

/-- If the units of a field `L` modulo the image of the units of a Jacobson ring `K` form a
finitely generated group, then `L` is finite as a `K`-module.

Generators of the quotient are lifted to units of `L`; those lifts and their inverses generate
`L` as a `K`-algebra, and Zariski's lemma over a Jacobson ring turns finite type into finite. -/
public theorem finite_of_fg_units_quotient (K L : Type*) [CommRing K] [IsJacobsonRing K]
    [Field L] [Algebra K L]
    (hfg : Group.FG (Lˣ ⧸ (Units.map (algebraMap K L).toMonoidHom).range)) :
    Module.Finite K L := by
  classical
  set N : Subgroup Lˣ := (Units.map (algebraMap K L).toMonoidHom).range with hNdef
  obtain ⟨S, hSclosure, hSfin⟩ := Group.fg_iff.mp hfg
  choose lift hlift using (QuotientGroup.mk_surjective (s := N))
  set T : Set L :=
    (fun q => ((lift q : Lˣ) : L)) '' S ∪ (fun q => (((lift q)⁻¹ : Lˣ) : L)) '' S with hTdef
  have hTfin : T.Finite := (hSfin.image _).union (hSfin.image _)
  set A : Subalgebra K L := Algebra.adjoin K T with hAdef
  -- The units whose value and inverse both lie in `A` form a subgroup of `Lˣ`.
  set H : Subgroup Lˣ :=
    { carrier := {u : Lˣ | (u : L) ∈ A ∧ ((u⁻¹ : Lˣ) : L) ∈ A}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨by simpa using A.mul_mem ha hb, by simpa [mul_comm] using A.mul_mem hb' ha'⟩
      one_mem' := by exact ⟨by simp, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by simpa using ha⟩ } with hHdef
  have hNH : N ≤ H := by
    rintro u ⟨c, rfl⟩
    refine ⟨?_, ?_⟩
    · exact A.algebraMap_mem (c : K)
    · have : ((Units.map (algebraMap K L).toMonoidHom c)⁻¹ : Lˣ) =
          Units.map (algebraMap K L).toMonoidHom c⁻¹ := by
        simp
      rw [this]
      exact A.algebraMap_mem ((c⁻¹ : Kˣ) : K)
  have hliftH : ∀ q ∈ S, lift q ∈ H := by
    intro q hq
    exact ⟨Algebra.subset_adjoin (Or.inl ⟨q, hq, rfl⟩),
      Algebra.subset_adjoin (Or.inr ⟨q, hq, rfl⟩)⟩
  have hmapTop : H.map (QuotientGroup.mk' N) = ⊤ := by
    rw [eq_top_iff, ← hSclosure, Subgroup.closure_le]
    intro q hq
    exact ⟨lift q, hliftH q hq, hlift q⟩
  have hHtop : H = ⊤ := by
    have hker : (QuotientGroup.mk' N).ker ≤ H := by
      rw [QuotientGroup.ker_mk']
      exact hNH
    have := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' N) (H := H) hker
    rw [hmapTop, Subgroup.comap_top] at this
    exact this.symm
  have hAtop : A = ⊤ := by
    refine Algebra.eq_top_iff.mpr fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact A.zero_mem
    · have hmem : Units.mk0 x hx ∈ H := hHtop ▸ Subgroup.mem_top _
      exact hmem.1
  have : Algebra.FiniteType K L :=
    ⟨⟨hTfin.toFinset, by rw [hTfin.coe_toFinset]; exact hAtop⟩⟩
  exact finite_of_finite_type_of_isJacobsonRing K L

end Stacks.Jacobson

end

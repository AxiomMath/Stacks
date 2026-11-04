module

public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto

/-!
# Degreewise surjectivity in the Mayer--Vietoris sequence of an injective module sheaf

For an injective sheaf of modules on a ringed space, every section over `U ⊓ V` is a difference
of restrictions of sections over `U` and over `V`. This is the degreewise surjectivity which the
Stacks proof of Tag 01EB establishes and which later lemmas cite as "the proof of Lemma 01EB";
it is deduced from Tag 01EA by taking the second section to be zero.

## Main results

* `Stacks.Cohomology.MayerVietoris.injective_mayerVietoris_surjective`: for an injective sheaf
  of modules, every section over `U ⊓ V` is a difference of restrictions of sections over `U`
  and over `V`.

## References

* [The Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
-/

@[expose] public noncomputable section

universe w v u

namespace Stacks.Cohomology.MayerVietoris

open Opposite TopologicalSpace CategoryTheory CategoryTheory.Limits

/-- **Degreewise surjectivity.** For an injective sheaf of modules `I` on a ringed space, every
section of `I` over `U ⊓ V` is the difference of the restrictions of a section over `U` and a
section over `V`: take the second section to be zero and apply Tag 01EA. -/
theorem injective_mayerVietoris_surjective
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    (I : SheafOfModules.{w} R) [Injective I] (U V : Opens X)
    (t : I.val.presheaf.obj (op (U ⊓ V))) :
    ∃ (a : I.val.presheaf.obj (op U)) (b : I.val.presheaf.obj (op V)),
      I.val.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a -
        I.val.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b = t := by
  obtain ⟨a, ha⟩ := Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
    R I (inf_le_left : U ⊓ V ≤ U) t
  exact ⟨a, 0, by rw [ha, map_zero, sub_zero]⟩

end Stacks.Cohomology.MayerVietoris

end

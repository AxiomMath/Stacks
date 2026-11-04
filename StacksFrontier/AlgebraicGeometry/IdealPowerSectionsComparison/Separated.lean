module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSectionsComparison.Basic

/-!
# Sections away from `V(I)` are determined on the basic opens of `I`

The open `Spec(A) \ V(I)` is covered by the basic opens `D(f)` with `f ∈ I`, so a section of
`M̃` on it is determined by its restrictions to those.  This is the separatedness input to the
surjectivity half of [Stacks, Tag 01PM]: there a candidate preimage of a section is produced
on each `D(f)`, and this lemma is what identifies the two global sections once they agree
there.

## Main results

* `sections_eq_of_restrictToBasicOpen_eq`: two sections of `M̃` on `Spec(A) \ V(I)` which agree
  on `D(f)` for every `f ∈ I` are equal.

## Implementation notes

The cover is not a chosen finite generating set but the whole of `I`: every point of
`Spec(A) \ V(I)` misses some element of `I` by `exists_mem_liftedIdeal_notMem`, which is
exactly the hypothesis of `TopCat.Presheaf.IsSheaf.section_ext` for the tilde sheaf. No
finiteness is needed, and the conclusion is then usable for an arbitrary `f ∈ I` rather than
only for generators.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.StructureSheaf

universe u v

namespace Stacks.AlgebraicGeometry.IdealPowerSections

variable (A : Type u) [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- Two sections of `M̃` on `Spec(A) \ V(I)` which agree on `D(f)` for every `f ∈ I` are equal:
those basic opens cover. -/
public lemma sections_eq_of_restrictToBasicOpen_eq {t₁ t₂ : sectionsOnComplement A I M}
    (h : ∀ (f : A) (hf : f ∈ I),
      restrictToBasicOpen A I M f hf t₁ = restrictToBasicOpen A I M f hf t₂) :
    t₁ = t₂ := by
  refine TopCat.Presheaf.IsSheaf.section_ext
    (modulesSpecToSheaf.obj (tilde (R := .of (ULift.{v} A))
      (ModuleCat.of (ULift.{v} A) (ULift.{u} M)))).2 fun p hp => ?_
  obtain ⟨g, hg, hgp⟩ := exists_mem_liftedIdeal_notMem A I p hp
  exact ⟨PrimeSpectrum.basicOpen g, basicOpen_le_liftedComplement A I g hg, hgp,
    h g.down ((mem_liftedIdeal A I).mp hg)⟩

end Stacks.AlgebraicGeometry.IdealPowerSections

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.IteratedColimit

/-!
# A faithfully flat ind-étale algebra splitting étale covers

For every commutative ring `A` there is a faithfully flat ind-étale `A`-algebra `C` such that
every faithfully flat étale `C`-algebra admits a retraction to `C`.

The algebra is the colimit of `A → T(A) → T²(A) → ⋯` of
`AlgebraicGeometry.ProEtale.iteratedSplittingColimit`, read at the cardinal `max ℵ₀ #A`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_faithfullyFlat_ind_etale_algebra_splitting_etale`

## Implementation notes

Ind-étaleness is expressed by `CategoryTheory.ObjectProperty.ind` for the property that the
structure map of an object under `A` is étale. A retraction of `C → B` is represented by a
`C`-algebra homomorphism `B → C`, whose compatibility with the structure map is part of the
algebra-homomorphism data.

## References

* [Stacks Project, Tag 097R](https://stacks.math.columbia.edu/tag/097R)
-/

open Cardinal CategoryTheory

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- There is a faithfully flat ind-étale `A`-algebra such that every faithfully flat étale
algebra over it has a retraction. -/
@[stacks 097R]
theorem exists_faithfullyFlat_ind_etale_algebra_splitting_etale
    (A : Type u) [CommRing A] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      (algebraMap A C).FaithfullyFlat ∧
        ObjectProperty.ind.{u}
          (fun D : Under (CommRingCat.of A) ↦ D.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom (algebraMap A C))) ∧
        ∀ (B : Type u) [CommRing B] [Algebra C B],
          (algebraMap C B).FaithfullyFlat → Algebra.Etale C B →
            Nonempty (B →ₐ[C] C) := by
  obtain ⟨C, hCR, hCA, -, hff, hind, hsplit⟩ :=
    exists_small_faithfullyFlat_ind_etale_algebra_splitting_etale A
      (max ℵ₀ (Cardinal.mk A)) (le_max_left _ _) (le_max_right _ _)
  exact ⟨C, hCR, hCA, hff, hind, hsplit⟩

end AlgebraicGeometry.ProEtale

end

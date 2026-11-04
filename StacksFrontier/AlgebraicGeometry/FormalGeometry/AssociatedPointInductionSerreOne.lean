module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointSplittingConstruction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExactMiddle
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneClosure

/-!
# Algebraization of formal sections: the induction of Stacks 0EG2 over Stacks 0EIF (3)(a)

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, `U = Spec(A) ∖ V(𝔞)` and `F` a coherent module on
`U`. Stacks 0EG2 says that the comparison map
`Stacks.Algebraization.comparisonMap A I 𝔞 F` is an isomorphism under conditions (1) and (2) of
Stacks 0EIF alone. The source's proof is an induction on the number of associated points of `F`
off `V(I)`, which only ever applies Stacks 0EIF to modules with at most one associated point off
`V(I)`; such a module has no embedded associated point there, so condition (3) of Stacks 0EIF
holds for it in the form (3)(a).

This file runs that induction against Stacks 0EIF in the form (3)(a) only, which is the form in
which the library proves it:
`Stacks.Algebraization.isIso_comparisonMap_of_serreOne_of_completedComplementIsFormalSections`,
granted the single input `Stacks.Algebraization.CompletedComplementIsFormalSections` (the
identity `RΓ(V, F)^∧ = R lim RΓ(V, F/IⁿF)` of Stacks 0BLX, 0A0K and 0D60 on the complement of a
closed subset of `Spec(A)`). The other two inputs of the induction are proved:
the middle clause of Stacks 0H48 (`Stacks.Algebraization.isIso_comparisonMap_middle_of_ends`)
and the splitting of `F` assembled from Stacks 0BK0, 0DX3 and 0AW0
(`Stacks.Algebraization.exists_shortExact_serreOne_of_nonempty`).

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_of_associatedRank_le_of_completedComplement` — the
  induction.
* `Stacks.Algebraization.isIso_comparisonMap_of_bootstrapHypotheses_of_completedComplement` — Stacks
  0EG2, granted `Stacks.Algebraization.CompletedComplementIsFormalSections`.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)

/-- **The induction of Stacks 0EG2**, on the number of associated points off `V(I)`, granted
`Stacks.Algebraization.CompletedComplementIsFormalSections`. A coherent module satisfying
conditions (1) and (2) whose associated points off `V(I)` number at most `n` has an isomorphic
comparison map.

With no associated point off `V(I)` the module satisfies condition (3)(a) of Stacks 0EIF
vacuously. Otherwise `Stacks.Algebraization.exists_shortExact_serreOne_of_nonempty` produces
`0 → F' → F → F'' → 0` with `F''` satisfying conditions (1), (2) and (3)(a), and `F'` satisfying
(1) and (2) with fewer associated points off `V(I)`; Stacks 0EIF applies to `F''`, the induction
hypothesis to `F'`, and the middle clause of Stacks 0H48 concludes for `F`. -/
public theorem isIso_comparisonMap_of_associatedRank_le_of_completedComplement
    (h0BLX : CompletedComplementIsFormalSections.{u}) :
    ∀ (n : ℕ) (F : (complementZeroLocus A a : Scheme).Modules), F.IsCoherent →
      BootstrapHypotheses A I a F → associatedRank A I a F ≤ n →
        IsIso (comparisonMap A I a F) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hFc hF hrank
    rcases Set.eq_empty_or_nonempty (associatedPointsOffVanishing A I a F) with hemp | hne
    · have hS : IsSerreOneOffVanishing A I a F :=
        isSerreOneOffVanishing_of_associatedPointsOffVanishing_eq_empty A I a F hemp
      exact isIso_comparisonMap_of_serreOne_of_completedComplementIsFormalSections h0BLX hF.le F
        hFc (hF.formalSectionsHypotheses A I a (Or.inl hS)) hS
    · obtain ⟨F', F'', f, g, w, hSE, hF'c, hF''c, hF'', hS'', hlt⟩ :=
        exists_shortExact_serreOne_of_nonempty A I a F hFc hF hne
      have _ : Mono f := hSE.mono_f
      have h₁ : IsIso (comparisonMap A I a F') :=
        ih _ (by omega) F' hF'c (BootstrapHypotheses.of_mono A I a f hF) le_rfl
      have h₃ : IsIso (comparisonMap A I a F'') :=
        isIso_comparisonMap_of_serreOne_of_completedComplementIsFormalSections h0BLX hF.le F''
          hF''c hF'' hS''
      let : (ShortComplex.mk f g w).X₁.IsCoherent := hF'c
      let : (ShortComplex.mk f g w).X₂.IsCoherent := hFc
      let : (ShortComplex.mk f g w).X₃.IsCoherent := hF''c
      exact isIso_comparisonMap_middle_of_ends A I a (ShortComplex.mk f g w) hSE h₁ h₃

/-- **Stacks 0EG2, granted `Stacks.Algebraization.CompletedComplementIsFormalSections`.** Let
`I ⊆ 𝔞` be ideals of a Noetherian ring `A` and `F` a coherent module on `U = Spec(A) ∖ V(𝔞)`
satisfying conditions (1) and (2) of Stacks 0EIF
(`Stacks.Algebraization.BootstrapHypotheses`). Then the comparison map
`Stacks.Algebraization.comparisonMap A I 𝔞 F`, from the sections of `F` on arbitrarily small open
neighbourhoods of `U ∩ V(I)` to the compatible families of sections of `F / Iⁿ F` on `U`, is an
isomorphism. -/
public theorem isIso_comparisonMap_of_bootstrapHypotheses_of_completedComplement
    (h0BLX : CompletedComplementIsFormalSections.{u})
    (F : (complementZeroLocus A a : Scheme).Modules) [hFc : F.IsCoherent]
    (hF : BootstrapHypotheses A I a F) :
    IsIso (comparisonMap A I a F) :=
  isIso_comparisonMap_of_associatedRank_le_of_completedComplement A I a h0BLX
    (associatedRank A I a F) F hFc hF le_rfl

end Stacks.Algebraization

end

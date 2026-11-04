module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodCompletion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionColimitEquivalence

/-!
# The conditions of Tag 0EK2 for a closed subscheme given by its ideal sheaf

[Stacks, Tag 0EK2] compares four conditions on a closed subscheme `Y` of a Noetherian scheme `X`.
They are stated in `StacksDraft.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful
.NeighbourhoodCompletion` for a closed immersion `i : Y ⟶ X`, where all four implications are
proved. The fundamental group chapter states conditions (1) and (2) for a closed subscheme given
by an ideal sheaf `Y : X.IdealSheafData`, as
`Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteQuasiAffine` and
`Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteAmplePowers`. This file shows that those are
conditions (1) and (2) of Tag 0EK2 for the closed immersion `Y.subschemeι`, and chains the
implications `(1) ⇒ (2) ⇒ (3) ⇒ (4)` of that tag in that vocabulary.

## Main results

* `Stacks.FundamentalGroup.isQuasiAffineComplete_iff_neighbourhoodSectionsCompleteQuasiAffine`,
  `Stacks.FundamentalGroup.hasAmpleComplete_iff_neighbourhoodSectionsCompleteAmplePowers` — the
  two spellings of conditions (1) and (2) agree.
* `Stacks.FundamentalGroup`
  `.completionFullyFaithfulComplete_of_neighbourhoodSectionsCompleteAmplePowers` — condition (2)
  implies condition (4), through condition (3).
* `Stacks.FundamentalGroup`
  `.completionFullyFaithfulComplete_of_neighbourhoodSectionsCompleteQuasiAffine` — condition (1)
  implies condition (4).

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

open Stacks.Algebraization Stacks.Algebraization.NeighbourhoodCompletion

variable {X : Scheme.{u}} (Y : X.IdealSheafData)

/-- Condition (1) of [Stacks, Tag 0EK2] for the closed immersion of `Y` is the quasi-affine
condition of the fundamental group chapter. -/
public theorem isQuasiAffineComplete_iff_neighbourhoodSectionsCompleteQuasiAffine :
    IsQuasiAffineComplete Y.subschemeι ↔ NeighbourhoodSectionsCompleteQuasiAffine Y :=
  and_congr Iff.rfl (infTower_isSectionsComplete_iff Y.subschemeι _)

/-- Condition (2) of [Stacks, Tag 0EK2] for the closed immersion of `Y` is the ample-powers
condition of the fundamental group chapter. -/
public theorem hasAmpleComplete_iff_neighbourhoodSectionsCompleteAmplePowers :
    HasAmpleComplete Y.subschemeι ↔ NeighbourhoodSectionsCompleteAmplePowers Y :=
  exists_congr fun _ => exists_congr fun _ => and_congr Iff.rfl <| exists_congr fun _ =>
    forall₂_congr fun _ _ => infTower_isSectionsComplete_iff Y.subschemeι _

/-- **Condition (2) implies condition (4) in [Stacks, Tag 0EK2].** If `X` is Noetherian and has
an ample invertible module `L` with `colim_𝒱 Γ(V, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` an
isomorphism for all `m ≫ 0`, then the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is fully
faithful on the finite locally free objects. This is `(2) ⇒ (3)` followed by `(3) ⇒ (4)`. -/
public theorem completionFullyFaithfulComplete_of_neighbourhoodSectionsCompleteAmplePowers
    [IsNoetherian X] (h : NeighbourhoodSectionsCompleteAmplePowers Y) :
    CompletionFullyFaithfulComplete Y.subschemeι :=
  completionFullyFaithfulComplete_of_finiteLocallyFreeComplete Y.subschemeι
    (finiteLocallyFreeComplete_of_hasAmpleComplete Y.subschemeι
      ((hasAmpleComplete_iff_neighbourhoodSectionsCompleteAmplePowers Y).2 h))

/-- **Condition (1) implies condition (4) in [Stacks, Tag 0EK2].** If `X` is Noetherian and
quasi-affine and `colim_𝒱 Γ(V, 𝒪_V) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism, then the
completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is fully faithful on the finite locally free
objects. -/
public theorem completionFullyFaithfulComplete_of_neighbourhoodSectionsCompleteQuasiAffine
    [IsNoetherian X] (h : NeighbourhoodSectionsCompleteQuasiAffine Y) :
    CompletionFullyFaithfulComplete Y.subschemeι :=
  completionFullyFaithfulComplete_of_finiteLocallyFreeComplete Y.subschemeι
    (finiteLocallyFreeComplete_of_hasAmpleComplete Y.subschemeι
      (hasAmpleComplete_of_isQuasiAffineComplete Y.subschemeι
        ((isQuasiAffineComplete_iff_neighbourhoodSectionsCompleteQuasiAffine Y).2 h)))

end Stacks.FundamentalGroup

end

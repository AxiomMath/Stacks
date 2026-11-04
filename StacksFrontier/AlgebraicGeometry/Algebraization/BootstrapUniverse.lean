module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.Dualizing.UniverseDescent

/-!
# The dualizing universe of a bootstrap situation

The dualizing complex of a bootstrap situation lives in the module universe `max u w`, where `u`
is the universe of the ring. Since a dualizing complex in any module universe yields one in the
ring's own universe (`Dualizing.exists_isDualizingComplex_of_isDualizingComplex`), the universe
`w` can always be replaced by `u`, and the ring has finite Krull dimension ([Stacks, Tag 0A80]).

## Main results

* `Stacks.Algebraization.BootstrapSituation.exists_isDualizingComplex` — the ring of a bootstrap
  situation has a dualizing complex in the universe of the ring.
* `Stacks.Algebraization.BootstrapSituation.ringKrullDim_lt_top` — the ring of a bootstrap
  situation has finite Krull dimension.
* `Stacks.Algebraization.BootstrapSituation.reuniverse` — the same situation with its dualizing
  complex taken in the universe of the ring.

## Implementation notes

`reuniverse` is a structure update: only the proof of assumption (1) changes, so the ring, the
ideal, the module, the locus and both bounds are definitionally those of the original situation.

## References

* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

namespace BootstrapSituation

/-- The ring of a bootstrap situation has a dualizing complex in its own universe. -/
public theorem exists_isDualizingComplex (S : BootstrapSituation.{u, v, w}) :
    ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K := by
  obtain ⟨K, hK⟩ := S.dualizing
  exact Dualizing.exists_isDualizingComplex_of_isDualizingComplex hK

/-- The ring of a bootstrap situation has finite Krull dimension, because it has a dualizing
complex ([Stacks, Tag 0A80]). -/
public theorem ringKrullDim_lt_top (S : BootstrapSituation.{u, v, w}) : ringKrullDim S.A < ⊤ := by
  obtain ⟨K, hK⟩ := S.exists_isDualizingComplex
  exact Dualizing.ringKrullDim_lt_top_of_isDualizingComplex hK

/-- The bootstrap situation `S` with its dualizing complex taken in the universe of the ring. -/
public def reuniverse (S : BootstrapSituation.{u, v, w}) : BootstrapSituation.{u, v, u} :=
  { S with dualizing := S.exists_isDualizingComplex }

end BootstrapSituation

end Stacks.Algebraization

end

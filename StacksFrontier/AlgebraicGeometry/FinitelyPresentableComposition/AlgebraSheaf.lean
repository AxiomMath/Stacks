module

public import StacksFrontier.AlgebraicGeometry.FinitelyPresentableComposition.Directed
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# The two-stage composition at algebra sheaves, in [Stacks, Tag 0817]'s universe

`Stacks.FinitelyPresentableComposition.exists_directed_index_of_twoStage` is a statement about an
arbitrary category whose morphisms lie in the universe of the two index types.  This file records
that it *fits* the category and the universe [Stacks, Tag 0817] is stated in, which is not free:
`Stacks.RelativeSpec.AlgebraSheaf X` for `X : Scheme.{u}` is `CategoryTheory.Under X.sheaf`, whose
objects lie in `Type (u + 1)` while its morphisms lie in `Type u`, so the generic statement has to
be instantiated at **two different** universes — object universe `u + 1`, morphism universe `u` —
and then the composed index lands in `Type u`, which is where [Stacks, Tag 0817] wants it.
Written in the same file as the generic statement this instantiation does not elaborate,
because the file's own
`universe` variables are then reused instead of being instantiated; that is why this is a separate
module and not a corollary there.

## Main results

* `Stacks.FinitelyPresentableComposition.exists_directed_index_algebraSheaf`: for a scheme `X` and
  an algebra sheaf `A` on it, a filtered colimit of filtered colimits of algebra sheaves that are
  **finitely presentable along those very cocones** with vertex `A` is a colimit over a nonempty
  directed preorder in `Type u` whose diagram consists of those same algebra sheaves.

## Where `hfp` is discharged

For the two cocones of [Stacks, Tag 0817] part (2) it is discharged by
`Stacks.AlgebraicGeometry.Tag0817Presentable.presentableAlong_of_isFinitePresentation`, and that
tag's part (2) is proved in `StacksFrontier/AlgebraicGeometry/PartTwoResidue/Complete.lean`.

## What is not done, and no stacks attribute

**No `@[stacks]` attribute is attached.** The hypothesis `hfp` — that the inner stages are finitely
presentable along the cocones of the two systems being composed — is exactly what is missing for
[Stacks, Tag 0817] part (2).  It is implied by [Stacks, Tag 01BS] for algebra sheaves, which this
repository does not prove, but it is weaker: nothing is asked about any cocone other than the ones
at hand, and in particular nothing about filtered colimits of algebra sheaves that are not
quasi-coherent.
What this file establishes is that `hfp` is the **only** thing missing on top of part (1) and
[Stacks, Tag 086N]: the compatibility between the systems that tag 086N chooses separately for each
finite subalgebra, which that tag's statement does not provide, is supplied by the composition and
needs nothing else.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RelativeSpec

universe u

namespace Stacks.FinitelyPresentableComposition

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {X : Scheme.{u}} {A : AlgebraSheaf X}
  {I : Type u} [SmallCategory I] [IsFiltered I] {D : I ⥤ AlgebraSheaf X}
  (t : D ⟶ (Functor.const I).obj A)
  {K : I → Type u} [∀ i, SmallCategory (K i)] [∀ i, IsFiltered (K i)]
  {E : ∀ i, K i ⥤ AlgebraSheaf X} (s : ∀ i, E i ⟶ (Functor.const (K i)).obj (D.obj i))
  (ht : IsColimit (Cocone.mk A t)) (hs : ∀ i, IsColimit (Cocone.mk (D.obj i) (s i)))
  (hfp : TwoStagePresentable t s)

include ht hs hfp in
/-- **The two-stage composition at algebra sheaves, with the index in the universe
[Stacks, Tag 0817] states its conclusion in.**

Let `A` be a sheaf of commutative `𝒪_X`-algebras which is the colimit of a filtered system of
algebra sheaves, each member of which is itself the colimit of a filtered system of algebra
sheaves, all of the inner stages being finitely presentable objects.  Then `A` is a directed
colimit, over a nonempty preorder in `Type u`, of those inner stages — so any property they share
is shared by the whole new diagram.

**The hypothesis `hfp` is the whole of what is still owed.**  For [Stacks, Tag 0817] part (2) the
inner stages are the finite and finitely presented quasi-coherent algebras produced by
[Stacks, Tag 086N]; their finite presentability as objects of
`Stacks.RelativeSpec.AlgebraSheaf X` would give it, and that is [Stacks, Tag 01BS], not available
in this repository.  What `hfp` actually asks is less: presentability along the outer cocone and
the inner cocones only, all of whose stages and vertices are quasi-coherent. -/
theorem exists_directed_index_algebraSheaf (P : AlgebraSheaf X → Prop)
    (hP : ∀ (i : I) (k : K i), P ((E i).obj k)) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (F : J ⥤ AlgebraSheaf X) (σ : F ⟶ (Functor.const J).obj A)
      (_ : IsColimit (Cocone.mk A σ)),
      ∀ j, P (F.obj j) :=
  exists_directed_index_of_twoStage t s ht hs hfp P hP

end Stacks.FinitelyPresentableComposition

end

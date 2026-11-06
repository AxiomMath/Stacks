module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale

/-!
# The diagonal of a separated étale morphism splits off its fibre square

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S`. Its
relative diagonal `Δ : V ⟶ V ×_W V` is an open immersion, because an étale morphism is
unramified; and it is a closed immersion, because that is what separatedness says. So the point
set of the diagonal is open and closed in the point space of `V ×_W V`, and `V ×_W V` splits
into the diagonal and a complementary open-and-closed subspace.

This is the decomposition `V ×_W V = Δ(V) ⊔ U` which opens the proof of Stacks 0BGY.

## Main results

* `AlgebraicGeometry.Space.isClopen_range_pointsMap_pullbackDiagonal`: the point set of the
  relative diagonal of a separated étale morphism of algebraic spaces is open and closed.
* `AlgebraicGeometry.Space.exists_diagonalComplement_decomposition`: the fibre square of a
  separated étale morphism of algebraic spaces is the union of two complementary
  open-and-closed subspaces, the point set of one being the diagonal and of the other its
  complement.

## Implementation notes

Both halves of the clopen condition come from results already in the library. Openness is
`AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified` (Stacks 05W1 part
(1)) applied through `AlgebraicGeometry.Space.isUnramified_of_isEtale` (Stacks 06CR), followed
by Stacks 03BZ part (1) on points. Closedness is immediate from
`AlgebraicGeometry.Space.IsSeparated`, which *is* the statement that the relative diagonal is a
closed immersion, followed by Stacks 04CD on points. Nothing here is a Stacks statement in its
own right, so nothing carries a tag.

The decomposition is stated in the shape
`AlgebraicGeometry.Space.exists_clopen_subspace_decomposition_of_isClopen` provides: two
subfunctors which are open subspaces and closed subspaces of `V ×_W V`, whose join sheafifies to
the whole fibre square and whose meet is the sheafification of the bottom subfunctor. That is
the lattice form of `V ×_W V = Δ(V) ⊔ U`, not an isomorphism onto a coproduct; the two are
related by the lemmas of
`StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubfunctorDecomposition`.

The complementary piece is returned first and the diagonal piece second, matching the argument
order of the underlying decomposition lemma.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SeparatedEtaleDiagonalComplement :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SeparatedEtaleDiagonalComplement
    {X' Y' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ Z') (g : Y' ⟶ Z') :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_SeparatedEtaleDiagonalComplement B S hS).has_limit _

/-- The point set of the relative diagonal of a separated étale morphism of algebraic spaces
over `S` is open and closed in the point space of the fibre square: the diagonal is an open
immersion because an étale morphism is unramified, and a closed immersion because the morphism
is separated. -/
theorem isClopen_range_pointsMap_pullbackDiagonal (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) :
    IsClopen (Set.range (pointsMap B S hS V (pullback.diagonal f))) :=
  ⟨isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (isAlgebraicSpace_pullback B S hS f f hV hV hW) (pullback.diagonal f) hsep,
    isOpen_range_pointsMap_of_isOpenImmersion B S hS (pullback.diagonal f)
      (isOpenImmersion_diagonal_of_isUnramified B S hS hV hW f
        (isUnramified_of_isEtale B S hS hf))⟩

/-- **The decomposition `V ×_W V = Δ(V) ⊔ U` of Stacks 0BGY.** For a separated étale morphism
`f : V ⟶ W` of algebraic spaces over `S` the fibre square `V ×_W V` carries two subfunctors,
each an open subspace and a closed subspace, whose join sheafifies to the whole of `V ×_W V` and
whose meet is the sheafification of the bottom subfunctor; the point set of the second is the
image of the relative diagonal and that of the first is its complement. -/
theorem exists_diagonalComplement_decomposition (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) :
    ∃ C D : Subfunctor (pullback f f),
      IsOpenSubspace B S hS C ∧ IsClosedSubspace B S hS C ∧
      IsOpenSubspace B S hS D ∧ IsClosedSubspace B S hS D ∧
      (C ⊔ D).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      C ⊓ D = (⊥ : Subfunctor (pullback f f)).sheafify (BigFppfOver.topology B S hS) ∧
      Set.range (pointsMap B S hS D.toFunctor D.ι) =
        Set.range (pointsMap B S hS V (pullback.diagonal f)) ∧
      Set.range (pointsMap B S hS C.toFunctor C.ι) =
        (Set.range (pointsMap B S hS V (pullback.diagonal f)))ᶜ :=
  have hclopen := isClopen_range_pointsMap_pullbackDiagonal B S hS hV hW f hf hsep
  exists_clopen_subspace_decomposition_of_isClopen B S hS
    (isAlgebraicSpace_pullback B S hS f f hV hV hW) _ hclopen.2 hclopen.1

end AlgebraicGeometry.Space

end

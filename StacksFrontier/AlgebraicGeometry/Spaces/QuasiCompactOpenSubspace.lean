module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# Open subspaces of a Noetherian algebraic space are quasi-compact

Let `X` be a Noetherian algebraic space over a scheme `S`, meaning that it is quasi-compact,
absolutely quasi-separated and locally Noetherian. Its space of points is then a Noetherian
topological space, so every subspace of it is Noetherian and in particular quasi-compact.
Consequently an immersion into `X` has quasi-compact source, and since `X` is quasi-separated
such a morphism is a quasi-compact morphism of algebraic spaces. The inclusion of an open
subspace of `X` is a special case.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isImmersion_of_isNoetherian`: an immersion
  into a Noetherian algebraic space has quasi-compact source.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isImmersion_of_isNoetherian`: an immersion into a
  Noetherian algebraic space is a quasi-compact morphism.
* `AlgebraicGeometry.Space.isQuasiCompact_ι_of_isNoetherian`: the inclusion of an open
  subspace of a Noetherian algebraic space is quasi-compact.

## Implementation notes

The source of an immersion is quasi-compact for a purely topological reason: its space of
points is embedded in the space of points of `X`, which is a Noetherian topological space, and
a Noetherian topological space is compact with every subspace Noetherian. Openness of the
subspace plays no part, so the statements are made for an arbitrary immersion and the open
case is read off from it.

Quasi-separatedness enters only in the passage from quasi-compactness of the source to
quasi-compactness of the morphism, and it enters in the absolute form of Stacks 03BS,
part (3), which is the form Noetherianity of an algebraic space carries.

## References

* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An immersion into a Noetherian algebraic space has quasi-compact source.** The map on
points induced by an immersion is a topological embedding by part one of Stacks 0ABJ, and the
space of points of the target is a Noetherian topological space; a subspace of a Noetherian
topological space is Noetherian, hence compact, and compactness of the space of points is
quasi-compactness of the algebraic space by Stacks 03E4. -/
theorem isQuasiCompactSpace_of_isImmersion_of_isNoetherian
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hN : IsNoetherian B S hS hZ X) (i : Y ⟶ X)
    (hi : IsImmersion B S hS i) :
    IsQuasiCompactSpace B S hS Y := by
  have hXnoeth : NoetherianSpace (points B S hS X) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X hX hN.1 hN.2.2
  have hYnoeth : NoetherianSpace (points B S hS Y) :=
    (isEmbedding_pointsMap_of_isImmersion B S hS hX i hi).isInducing.noetherianSpace
  exact (isQuasiCompactSpace_iff_compactSpace_points B S hS Y hY).mpr
    (NoetherianSpace.compactSpace _)

/-- **An immersion into a Noetherian algebraic space is a quasi-compact morphism.** Its source
is quasi-compact, and a morphism from a quasi-compact algebraic space into an absolutely
quasi-separated one is quasi-compact by part (1) of Stacks 073B; absolute quasi-separatedness
of the target is one of the three components of its Noetherianity. -/
theorem isQuasiCompact_of_isImmersion_of_isNoetherian
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hN : IsNoetherian B S hS hZ X) (i : Y ⟶ X)
    (hi : IsImmersion B S hS i) :
    IsQuasiCompact B S hS i :=
  isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hN.2.1
    (isQuasiCompactSpace_of_isImmersion_of_isNoetherian B S hS hZ hX hY hN i hi) i

/-- **The inclusion of an open subspace of a Noetherian algebraic space over `S` is
quasi-compact.** An open immersion is an immersion, so this is the case of
`AlgebraicGeometry.Space.isQuasiCompact_of_isImmersion_of_isNoetherian` at the inclusion of an
open subfunctor; the source is an algebraic space because that is part of being an open
subspace. -/
theorem isQuasiCompact_ι_of_isNoetherian
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hN : IsNoetherian B S hS hZ X) {O : Subfunctor X} (hO : IsOpenSubspace B S hS O) :
    IsQuasiCompact B S hS O.ι :=
  isQuasiCompact_of_isImmersion_of_isNoetherian B S hS hZ hX hO.1 hN O.ι
    (isImmersion_of_isOpenImmersion B S hS hO.2)

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationExtensionOnSite

/-!
# Finite direct sums of modules of finite presentation on a site

Let `R` be a sheaf of rings on a site.  A finite direct sum of sheaves of `R`-modules of finite
presentation (Stacks 03DL (7), in the rendering `SheafOfModules.IsFinitePresentationOnSite`) is of
finite presentation.  A zero module is the cokernel of the zero map between two empty coproducts of
copies of the structure sheaf, and a direct sum of two modules is an extension of one by the other,
so the binary case is the closure under extensions of Stacks 01BY (4).

## Main results

* `SheafOfModules.IsFinitePresentationOnSite.biprod`: a binary direct sum of modules of finite
  presentation is of finite presentation.
* `SheafOfModules.isFinitePresentationOnSite_isClosedUnderBinaryCoproducts`: finite presentation
  of sheaves of modules is closed under binary coproducts.

The closure under finite coproducts, which needs the zero case
`SheafOfModules.IsFinitePresentationOnSite.of_isZero`, is in
`StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteFiniteCoproductsClosure`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A binary direct sum of sheaves of modules of finite presentation is of finite
presentation**: it is an extension of the second summand by the first (Stacks 01BY (4)). -/
theorem IsFinitePresentationOnSite.biprod [Balanced (SheafOfModules.{w} R)]
    [HasZeroObject (SheafOfModules.{w} R)] {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N]
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite) :
    (M ⊞ N).IsFinitePresentationOnSite :=
  Stacks.SheafOfModules.isFinitePresentationOnSite_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact hM hN

/-- Finite presentation of sheaves of modules is invariant under isomorphism. -/
instance isFinitePresentationOnSite_isClosedUnderIsomorphisms :
    (isFinitePresentationOnSite.{u, v, w, m} R).IsClosedUnderIsomorphisms :=
  ⟨fun e h => IsFinitePresentationOnSite.of_iso e h⟩

/-- Finite presentation of sheaves of modules is closed under binary coproducts: a binary
coproduct of sheaves of modules is a binary biproduct. -/
instance isFinitePresentationOnSite_isClosedUnderBinaryCoproducts
    [Balanced (SheafOfModules.{w} R)] [HasZeroObject (SheafOfModules.{w} R)] :
    (isFinitePresentationOnSite.{u, v, w, w} R).IsClosedUnderBinaryCoproducts :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    have : HasBinaryBiproduct (G.obj ⟨WalkingPair.left⟩) (G.obj ⟨WalkingPair.right⟩) :=
      HasBinaryBiproduct.of_hasBinaryCoproduct _ _
    refine ObjectProperty.prop_of_iso _
      ((HasColimit.isoOfNatIso (diagramIsoPair G)).trans
        (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (pair _ _))
          (BinaryBiproduct.isColimit _ _))).symm ?_
    exact IsFinitePresentationOnSite.biprod (hG ⟨WalkingPair.left⟩) (hG ⟨WalkingPair.right⟩))

end SheafOfModules

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Invariance
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatLocusWarning

/-!
# Flatness at a point along an open immersion of the source

`AlgebraicGeometry.Space.isFlatAt_iff_of_isOpenSubspace` compares flatness at a point of a
morphism of algebraic spaces with flatness at a point of its restriction to an *open subspace*
of the source, that is to a subfunctor. This file restates it for an arbitrary open immersion
`m : X' ⟶ X` of algebraic spaces, which is the form in which a projection produced by a base
change arrives: the open subspace it cuts out is its range, and the corestriction to the range
is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isFlatAt_comp_iff_of_isOpenImmersion`: for an open immersion
  `m : X' ⟶ X` of algebraic spaces and a morphism `h : X ⟶ Y`, the composite `m ≫ h` is flat at
  a point `x'` of `|X'|` exactly when `h` is flat at the image of `x'`.

## Implementation notes

The range of an open immersion out of an algebraic space is an open subspace
(`AlgebraicGeometry.Space.isOpenSubspace_subfunctorRange`) and the corestriction
`CategoryTheory.Subfunctor.toRange` to it is an isomorphism, an open immersion being a
monomorphism. Flatness at a point is invariant under an isomorphism of the source, by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iso_iff` at the germ property of
**Stacks 03ML** (2); the open-subspace statement then applies to the range.

No `@[stacks]` attribute is attached: **Stacks 03ML** is the definition of flatness at a point
and its locality on the source is part of **Stacks 03MM**, whose covering set in this library is
in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Flat.lean`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04RE](https://stacks.math.columbia.edu/tag/04RE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Flatness at a point is unchanged by restricting the source along an open immersion.** Let
`m : X' ⟶ X` be an open immersion of algebraic spaces over `S` and let `h : X ⟶ Y` be a morphism
to an algebraic space. Then `m ≫ h` is flat at a point `x'` of `|X'|` exactly when `h` is flat at
the image of `x'` in `|X|`.

This is `AlgebraicGeometry.Space.isFlatAt_iff_of_isOpenSubspace` at the open subspace
`Subfunctor.range m`, transported along the isomorphism `X' ≅ Subfunctor.range m` which the
corestriction of `m` to its range is. -/
theorem isFlatAt_comp_iff_of_isOpenImmersion (hX : IsAlgebraicSpace B S hS X)
    (hX' : IsAlgebraicSpace B S hS X') (hY : IsAlgebraicSpace B S hS Y)
    (m : X' ⟶ X) (hm : IsOpenImmersion B S hS m) (h : X ⟶ Y)
    (x' : points B S hS X') :
    IsFlatAt B S hS (m ≫ h) x' ↔ IsFlatAt B S hS h (pointsMap B S hS X' m x') := by
  have _ : Mono m := mono_of_isOpenImmersion B S hS m hm
  have hR : IsOpenSubspace B S hS (Subfunctor.range m) :=
    isOpenSubspace_subfunctorRange B S hS hX' hm
  have hfac : Subfunctor.toRange m ≫ (Subfunctor.range m).ι = m := Subfunctor.toRange_ι m
  have hcomm : (asIso (Subfunctor.toRange m)).hom ≫ ((Subfunctor.range m).ι ≫ h) =
      (m ≫ h) ≫ (Iso.refl Y).hom := by
    rw [Iso.refl_hom, Category.comp_id, asIso_hom, ← Category.assoc, hfac]
  have hiso := holdsOnEveryEtaleChartAtPoint_iso_iff B S hS (@MorphismOfGerms.IsFlat.{u})
    (asIso (Subfunctor.toRange m)) (Iso.refl Y) (m ≫ h)
    ((Subfunctor.range m).ι ≫ h) hcomm x'
  have hpt : pointsMap B S hS (Subfunctor.range m).toFunctor (Subfunctor.range m).ι
      (pointsMap B S hS X' (asIso (Subfunctor.toRange m)).hom x') =
      pointsMap B S hS X' m x' := by
    rw [← pointsMap_comp_apply]
    exact congrArg (fun k : X' ⟶ X => pointsMap B S hS X' k x') hfac
  refine hiso.trans ?_
  refine Iff.trans ?_ (iff_of_eq (congrArg (IsFlatAt B S hS h) hpt))
  exact (isFlatAt_iff_of_isOpenSubspace B S hS hX hY (Subfunctor.range m) hR h _).symm

end AlgebraicGeometry.Space

end

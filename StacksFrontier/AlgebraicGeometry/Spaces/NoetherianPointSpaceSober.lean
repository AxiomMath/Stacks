module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus

/-!
# The point space of a Noetherian algebraic space is sober and Noetherian

Tag 04ZG says that the space of points of a Noetherian algebraic space over a scheme `S` is a
sober Noetherian topological space.

Noetherianity of an algebraic space is quasi-compactness together with quasi-separatedness
and local Noetherianity, so the two conclusions come from two different pieces of the
hypothesis.  Sobriety uses only quasi-separatedness: a quasi-separated algebraic space is
Zariski locally quasi-separated by Tag 03JX, `(η) ⇒ (ζ)`, hence has sober point space by
Tag 06NJ.  Noetherianity uses quasi-compactness and local Noetherianity, and is Tag 04ZF (2).

## Main results

* `AlgebraicGeometry.Space.stacksSober_points_of_isNoetherian` and
  `AlgebraicGeometry.Space.noetherianSpace_points_of_isNoetherian` are the two halves of
  Tag 04ZG, and `AlgebraicGeometry.Space.stacksSober_and_noetherianSpace_points_of_isNoetherian`
  is their conjunction.

## Implementation notes

Sobriety is `StacksSober` of Definition 004X, existence together with uniqueness of generic
points, as in Tag 06NJ; Noetherianity of a topological space is Mathlib's
`TopologicalSpace.NoetherianSpace`.  The topology on the space of points is
`AlgebraicGeometry.Space.pointTopology`, installed as a local instance as elsewhere in this
directory.

Quasi-separatedness in `AlgebraicGeometry.Space.IsNoetherian` is the absolute notion of
Tag 03BS, part (3), which is the form Tag 03JX, `(η) ⇒ (ζ)` takes as input; its conclusion is
the absolute Zariski local quasi-separatedness of Tag 03BS, part (4), which Tag 03W7, `(2) ⇒
(1)` converts to the relative notion of Tag 02X5 that Tag 06NJ is stated for.  The
containment `hZ` of the terminal scheme in the site is required throughout, since the
absolute notions are phrased on the slice over it.

## References

* [Stacks Project, Tag 04ZG](https://stacks.math.columbia.edu/tag/04ZG)
* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03W7](https://stacks.math.columbia.edu/tag/03W7)
* [Stacks Project, Tag 06NJ](https://stacks.math.columbia.edu/tag/06NJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 04ZG, sobriety.** The space of points of a Noetherian algebraic space over `S`
is sober in the sense of Definition 004X: every irreducible closed subset of it has a unique
generic point.

Only quasi-separatedness is used: it makes the space Zariski locally quasi-separated by
Tag 03JX, `(η) ⇒ (ζ)` and Tag 03W7, so Tag 06NJ applies. -/
@[stacks 04ZG "sobriety"]
theorem stacksSober_points_of_isNoetherian (hF : IsAlgebraicSpace B S hS F)
    (hN : IsNoetherian B S hS hZ F) : StacksSober (points B S hS F) :=
  stacksSober_points_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ F hF
    (isZariskiLocallyQuasiSeparatedOver_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ hF
      (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS F hZ hF
        hN.2.1))

/-- **Stacks 04ZG, Noetherianity.** The space of points of a Noetherian algebraic space over
`S` is a Noetherian topological space.

Only quasi-compactness and local Noetherianity are used, which is Tag 04ZF (2). -/
@[stacks 04ZG "Noetherianity"]
theorem noetherianSpace_points_of_isNoetherian (hF : IsAlgebraicSpace B S hS F)
    (hN : IsNoetherian B S hS hZ F) : NoetherianSpace (points B S hS F) :=
  noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS _ hF hN.1 hN.2.2

/-- **Stacks 04ZG.** The space of points of a Noetherian algebraic space over `S` is a sober
Noetherian topological space. -/
@[stacks 04ZG]
theorem stacksSober_and_noetherianSpace_points_of_isNoetherian
    (hF : IsAlgebraicSpace B S hS F) (hN : IsNoetherian B S hS hZ F) :
    StacksSober (points B S hS F) ∧ NoetherianSpace (points B S hS F) :=
  ⟨stacksSober_points_of_isNoetherian B S hS hZ hF hN,
    noetherianSpace_points_of_isNoetherian B S hS hZ hF hN⟩

end AlgebraicGeometry.Space

end

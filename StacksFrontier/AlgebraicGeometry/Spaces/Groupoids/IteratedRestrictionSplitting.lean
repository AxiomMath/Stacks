module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.IteratedRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings

/-!
# Splittings and the two readings of a double restriction

An open finite subgroupoid of a groupoid scheme transports along a morphism of groupoid schemes
which is an isomorphism on arrow schemes and an equality on object schemes.  Applied to the
comparison morphism between the two ways of restricting twice, this carries a quasi-splitting of
a realization of `(G|_{U'})|_{U''}` to a quasi-splitting of a realization of `G|_{U''}`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid.transport` is the transported open
  finite subgroupoid.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isQuasiSplitAt_of_iteratedRestriction` and
  `AlgebraicGeometry.GroupoidScheme.isQuasiSplitAt_of_iteratedRestriction'`: a realization of
  `G|_{U''}` is quasi-split at the point corresponding to one at which a realization of
  `(G|_{U'})|_{U''}` is quasi-split.

## Implementation notes

The transported subgroupoid is the original one; what changes is its inclusion, which is
composed with the comparison morphism, and the recorded equality of object schemes.  Openness of
the inclusion on arrow schemes is preserved because an open immersion followed by an isomorphism
is an open immersion, and finiteness of the source and target maps is a property of the
subgroupoid alone.

## References

* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- Transport of an open finite subgroupoid along a morphism of groupoid schemes which is an
isomorphism on arrow schemes and is given on objects by an equality of object schemes. -/
def OpenFiniteSubgroupoid.transport {K L : GroupoidScheme S} (P : OpenFiniteSubgroupoid K)
    (Φ : Hom K L) (e : K.objects = L.objects) (hΦ : Φ.mapObjects = eqToHom e)
    [IsIso Φ.mapArrows] : OpenFiniteSubgroupoid L where
  subgroupoid := P.subgroupoid
  objects_eq := P.objects_eq.trans e
  inclusion := AlgebraicGeometry.GroupoidScheme.Hom.comp P.inclusion Φ
  mapObjects_eq := by
    change P.inclusion.mapObjects ≫ Φ.mapObjects = _
    rw [P.mapObjects_eq, hΦ, eqToHom_trans]
  arrows_open := by
    have hP : IsOpenImmersion P.inclusion.mapArrows.left := P.arrows_open
    have hΦ' : IsIso Φ.mapArrows.left :=
      inferInstanceAs (IsIso ((Over.forget S).map Φ.mapArrows))
    change IsOpenImmersion (P.inclusion.mapArrows ≫ Φ.mapArrows).left
    rw [Over.comp_left]
    infer_instance
  source_finite := P.source_finite
  target_finite := P.target_finite

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {H : Stacks.Groupoids.GroupoidScheme S} {U' U'' : Over S}
  {g : U' ⟶ H.objects} (R' : Restriction H g) {j : U'' ⟶ R'.groupoid.objects}
  (R'' : Restriction R'.groupoid j) (R''' : Restriction H (j ≫ R'.hom.mapObjects))

/-- A realization of `G|_{U''}` is quasi-split at the image of a point at which a realization of
`(G|_{U'})|_{U''}` is quasi-split. -/
theorem isQuasiSplitAt_of_iteratedRestriction {u : R''.groupoid.objects.left}
    (h : Stacks.Groupoids.GroupoidScheme.IsQuasiSplitAt R''.groupoid u) :
    Stacks.Groupoids.GroupoidScheme.IsQuasiSplitAt R'''.groupoid
      ((eqToHom (iteratedRestriction_objects_eq R' R'' R''')).left.base u) :=
  h.elim fun P =>
    ⟨(P.toOpenFiniteSubgroupoid.transport (iteratedRestrictionHom R' R'' R''')
      (iteratedRestriction_objects_eq R' R'' R''') rfl).toQuasiSplitting _⟩

/-- A realization of `G|_{U''}` is quasi-split over a point of `U''` whenever a realization of
`(G|_{U'})|_{U''}` is quasi-split over that same point. -/
theorem isQuasiSplitAt_of_iteratedRestriction' (u'' : U''.left)
    (h : Stacks.Groupoids.GroupoidScheme.IsQuasiSplitAt R''.groupoid
      ((eqToHom R''.objects_eq.symm).left.base u'')) :
    Stacks.Groupoids.GroupoidScheme.IsQuasiSplitAt R'''.groupoid
      ((eqToHom R'''.objects_eq.symm).left.base u'') := by
  have key : (eqToHom (iteratedRestriction_objects_eq R' R'' R''')).left.base
      ((eqToHom R''.objects_eq.symm).left.base u'') =
      (eqToHom R'''.objects_eq.symm).left.base u'' := by
    have h1 : eqToHom R''.objects_eq.symm ≫
        eqToHom (iteratedRestriction_objects_eq R' R'' R''') =
          eqToHom R'''.objects_eq.symm := by
      rw [eqToHom_trans]
    have h2 := congrArg
      (fun k : U'' ⟶ R'''.groupoid.objects => k.left.base u'') h1
    simpa only [Over.comp_left, Scheme.Hom.comp_apply] using h2
  rw [← key]
  exact isQuasiSplitAt_of_iteratedRestriction R' R'' R''' h

end AlgebraicGeometry.GroupoidScheme

end

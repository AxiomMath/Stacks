module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppf
public import Mathlib.CategoryTheory.GuitartExact.Basic

/-!
# The degree squares of `u : U_{spaces,étale} ⥤ (Spaces/U)_{fppf,total}` are Guitart exact

Let `U` be a simplicial object of a big fppf site of algebraic spaces and `u` the functor
`V/U_n ↦ V/U_n` of the proof of Stacks 0DH5. In each simplicial degree `m` the square
```
  (U_m)_{spaces,étale} --incl--> Spaces/U_m
          |                          |
   degreeInclusion              slicesι m
          v                          v
   U_{spaces,étale} -------u-----> (Spaces/U)_{fppf,total}
```
commutes with identity components, and it is Guitart exact: for `W` over `U_m` the arrows from
`W/U_m` into `u` reduce to arrows of degree `m` (the cartesian lifts `V ×_{U_k} U_m`), which is
`ToBigFppfTotal.structuredArrowInclusion_initial`. This is the exactness behind the restriction
of `h^*`, `h_*` of Stacks 0DHC to components (Stacks 0DH0).

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeTwoSquare_guitartExact`.

## Implementation notes

The components of the square are read through the `rfl` lemmas `degreeTwoSquare_app` and
`structuredArrowDownwards_obj_hom`; letting the kernel compare the two spellings of the objects
directly exhausts it.

## References

* [Stacks Project, Tag 0DH5](https://stacks.math.columbia.edu/tag/0DH5)
* [Stacks Project, Tag 0DH0](https://stacks.math.columbia.edu/tag/0DH0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} (U : SimplicialObject T.Spaces)

/-- The square of the degree-`m` inclusions and `u`. -/
abbrev degreeTwoSquare (m : SimplexCategory) :
    TwoSquare (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m)))
      (degreeInclusion U m) (slicesι U m) (toBigFppfTotal U) :=
  (degreeInclusionCompToBigFppfTotalIso U m).inv

/-- The component of the degree square at an object is an identity. -/
theorem degreeTwoSquare_app (m : SimplexCategory)
    (V : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op m))) :
    (degreeTwoSquare U m).natTrans.app V =
      𝟙 ((slicesι U m).obj
        ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m))).obj V)) :=
  rfl

/-- The structured arrow attached by the degree square to an arrow `W ⟶ incl(V)`. -/
theorem structuredArrowDownwards_obj_hom (m : SimplexCategory) (W : Over (U.obj (op m)))
    (c : StructuredArrow W (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op m)))) :
    (((degreeTwoSquare U m).structuredArrowDownwards W).obj c).hom =
      (slicesι U m).map c.hom ≫ (degreeTwoSquare U m).natTrans.app c.right :=
  rfl

/-- The downwards structured arrows of the degree square are the arrows of degree `m`. -/
def structuredArrowDownwardsIso (m : SimplexCategory) (W : Over (U.obj (op m))) :
    ToBigFppfTotal.structuredArrowInclusion U W ≅
      (degreeTwoSquare U m).structuredArrowDownwards W :=
  NatIso.ofComponents (fun c ↦ StructuredArrow.isoMk (Iso.refl _) (by
    refine ((congrArg _ ((toBigFppfTotal U).map_id _)).trans (Category.comp_id _)).trans ?_
    rw [structuredArrowDownwards_obj_hom, degreeTwoSquare_app]
    exact (Category.comp_id _).symm)) (fun {c c'} x ↦ by
      ext
      exact (Category.comp_id ((degreeInclusion U m).map x.right)).trans
        (Category.id_comp ((degreeInclusion U m).map x.right)).symm)

/-- **The degree square of `u` is Guitart exact.** -/
instance degreeTwoSquare_guitartExact (m : SimplexCategory) :
    (degreeTwoSquare U m).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_initial]
  intro W
  have := ToBigFppfTotal.structuredArrowInclusion_initial U W
  exact Functor.initial_of_natIso (structuredArrowDownwardsIso U m W)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

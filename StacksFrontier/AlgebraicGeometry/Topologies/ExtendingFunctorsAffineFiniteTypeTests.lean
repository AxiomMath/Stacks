module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsNoetherianRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsRepresentableSheaf

/-!
# The test objects of criterion (3) of Stacks 0GE5

Criterion (3) of Stacks 0GE5 is tested on the objects of `Sch/S` which are affine, of finite type
over `S`, and map into an affine open of `S`. Three facts needed to run the source's proof of the
implication (3) ⇒ (1) are collected here.

* The stages of an approximation of an affine object of `Sch/S` lying over an affine open of `S` by
  objects of finite presentation over that affine open are test objects. This is what makes
  criterion (3) applicable to the stage through which a section of `G'` over such an object
  factors.
* For any object `T` of `Sch/S`, the opens of `T` which are affine and lie over an affine open of
  `S` form a basis of the topology of `T`. This is the basis over which the source glues the
  representing objects.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.isAffineFiniteTypeOverAffineOpen_of_finitePresentation`: an
  affine object of `Sch/S` whose structure morphism factors through an affine open of `S` by a
  morphism of finite presentation is a test object of criterion (3).
* `AlgebraicGeometry.ExtendingFunctors.isBasis_isAffineOverAffineOpen`: the opens of an object of
  `Sch/S` which are affine and lie over an affine open of `S` form a basis of its topology.
* `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimitsOnSubcategory_uliftYoneda`: the functor
  of points, on a full subcategory of `Sch/S`, of an object of that subcategory which is locally of
  finite presentation over `S` takes directed inverse limits of affine objects of the subcategory
  to filtered colimits. This is the hypothesis of Stacks 0GE4.

## Implementation notes

Being affine, a test object is of finite type over `S` exactly when its structure morphism is
locally of finite type, which is how
`AlgebraicGeometry.ExtendingFunctors.IsAffineFiniteTypeOverAffineOpen` is phrased; a morphism of
finite presentation to an affine open is locally of finite type, and so is the inclusion of the
affine open, being an open immersion.

The basis statement is the neighbourhood criterion
`TopologicalSpace.Opens.isBasis_iff_nbhd` applied to
`AlgebraicGeometry.ExtendingFunctors.exists_isAffineOverAffineOpen_nbhd`.

## References

* [Stacks Project, Tag 0GE5](https://stacks.math.columbia.edu/tag/0GE5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

/-- **An affine object of `Sch/S` of finite presentation over an affine open of `S` is a test
object of criterion (3) of Stacks 0GE5.** It is affine and lies over an affine open of `S` by
assumption, and its structure morphism is locally of finite type, being the composite of a
morphism of finite presentation with an open immersion. -/
theorem isAffineFiniteTypeOverAffineOpen_of_finitePresentation {X : Over S} (hX : IsAffine X.left)
    (U : S.affineOpens) (g : X.left ⟶ U.1.toScheme) (hg : g ≫ U.1.ι = X.hom)
    (hfp : FinitePresentation g) : IsAffineFiniteTypeOverAffineOpen X := by
  refine ⟨⟨hX, U, g, hg⟩, ?_⟩
  have hlfp : LocallyOfFinitePresentation g := hfp.1
  have hgt : LocallyOfFiniteType g := inferInstance
  have : LocallyOfFiniteType (g ≫ U.1.ι) := inferInstance
  rw [← hg]
  exact this

/-- **The opens of an object of `Sch/S` which are affine and lie over an affine open of `S` form a
basis of its topology.** This is the basis over which Stacks 0GE5 glues the representing objects of
the fibre products over the affine test objects. -/
theorem isBasis_isAffineOverAffineOpen (T : Over S) :
    TopologicalSpace.Opens.IsBasis {V : T.left.Opens | IsAffineOverAffineOpen (overOpen T V)} := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {O z} hz => ?_
  obtain ⟨V, -, hzV, hVO, hVover⟩ := exists_isAffineOverAffineOpen_nbhd T z O hz
  exact ⟨V, hVover, hzV, hVO⟩

/-- **The functor of points, on a full subcategory of `Sch/S`, of an object of that subcategory
which is locally of finite presentation over `S` takes directed inverse limits of affine objects of
the subcategory to filtered colimits.** This is the hypothesis of Stacks 0GE4: the functor of
points on the subcategory is the restriction of the functor of points on `Sch/S`, which is limit
preserving by Stacks 01ZC. -/
theorem preservesAffineLimitsOnSubcategory_uliftYoneda {P : ObjectProperty (Over S)}
    (X : P.FullSubcategory) [LocallyOfFinitePresentation X.obj.hom] :
    PreservesAffineLimitsOnSubcategory P (uliftYoneda.{max w (u + 1)}.obj X) :=
  preservesAffineLimitsOnSubcategory_of_natIso
    (uliftYonedaIotaIso.{max w (u + 1), u, u + 1} P X)
    (preservesAffineLimitsOnSubcategory_of_preservesAffineLimits
      (preservesAffineLimits_uliftYoneda X.obj))

end AlgebraicGeometry.ExtendingFunctors

end

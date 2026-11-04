module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.CompletedFormalBase
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.LengthCriterion
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.Realization
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.ResidueFieldTransport
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.SecondOrderDescent
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation.StalkBaseVersality

/-!
# Algebraization of a versal formal object

An effective versal formal object over a locally Noetherian base is the system of
infinitesimal restrictions of an object over a scheme of finite type over that base, and
the algebraizing object is versal at the point carrying the formal object's residue field
(**Stacks 07XH**, `Deformation.Artin.exists_finiteType_versal_approximation`).

The development is split into the following parts, in order:

* `FormalObjectApproximation.CompletedFormalBase` — restriction of objects along base
  isomorphisms, the completed local ring at a finite type point as a formal base, and the
  lifting of compatible reductions of formal objects.
* `FormalObjectApproximation.LengthCriterion` — bijectivity of maps of complete local rings
  and isomorphy of formal objects from surjectivity and equality of lengths, via associated
  graded pieces.
* `FormalObjectApproximation.Realization` — closed points and residue fields of the
  quotients, levelwise isomorphisms of formal objects, realizations of formal objects, and
  the change-of-residue-field functor on Artinian local algebras.
* `FormalObjectApproximation.ResidueFieldTransport` — transport of predeformation
  categories, formal objects and versality along a change of residue field.
* `FormalObjectApproximation.SecondOrderDescent` — descent of a second-order comparison to
  the residue quotients, and the complete local restriction of an object at a finite type
  point.
* `FormalObjectApproximation.StalkBaseVersality` — the versality comparison of Stacks 0CXK
  with its deformation base pinned to the local ring of `S`, and Stacks 07XH.

## References

* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
-/

module

public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomComplexExtGeneral
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclicGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# A property-(P) representative of an object of the derived category

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, with the base ring,
the algebra and the modules in three independent universes. Every object of `D(A, d)` is
isomorphic there to the class of a differential graded module with property (P): the
localization functor `K(A, d) ⥤ D(A, d)` is essentially surjective, every object of the homotopy
category *is* a differential graded module, and a differential graded module receives a
quasi-isomorphism from one with property (P) by Tag 09KP.

This file makes that representative a chosen one, `DifferentialGradedModule.propertyPModel`,
together with the isomorphism `DifferentialGradedModule.propertyPModelIso` identifying its class
with the given object. It is what lets a construction or an identification available only at a
module with property (P) be transported to every object of `D(A, d)`, which is the reduction the
proof of Tag 0CS6 performs — "we may assume `M` and `N` are differential graded `E`-modules with
property (P)" — and which the statement of that tag, quantified over every `M`, `N` in
`D(E, d)`, therefore must not carry as a hypothesis.

## Main definitions

* `DifferentialGradedModule.propertyPModel`: the chosen differential graded module with
  property (P) representing an object of `D(A, d)`.
* `DifferentialGradedModule.propertyPModelIso`: the isomorphism of `D(A, d)` identifying the
  class of that module with the given object.

## Main results

* `DifferentialGradedModule.propertyPFiltration_propertyPModel`: the chosen module has
  property (P).
* `DifferentialGradedModule.leftOrthogonal_acyclic_propertyPModel`: it is therefore orthogonal
  on the left to the acyclic modules (Tag 09KM), which is the form in which the localization
  functor is bijective on morphisms out of it.
* `DifferentialGradedModule.propertyPModelExtEquiv`: the degree-`n` cohomology of the
  differential graded Hom complex of two chosen representatives is the `Ext`-group
  `Ext^n_{D(A, d)}(M, N)` of the two *arbitrary* objects they represent.

## Implementation notes

The chosen representative is `Classical.choose` of the proved
`DifferentialGradedModule.General.exists_propertyP_resolution` (Tag 09KP at independent
universes) applied to the differential graded module underlying a chosen preimage of the object
under the localization functor. Both choices are forced to be choices: Tag 09KP is an existence
statement, and the localization functor is essentially surjective rather than surjective on
objects up to equality. This is the same pattern as
`AlgebraicGeometry.RingedSite.kInjectiveModel`, which resolves a chosen preimage under
`CategoryTheory.DerivedCategory.Q`.

*Why the homotopy category can be entered by `.as`.* `DifferentialGradedModule.HomotopyCategory`
is a quotient of the category of differential graded modules by the homotopy relation on
morphisms only, so `DifferentialGradedModule.toHomotopyCategory` is the identity on objects and
`(toHomotopyCategory A).obj Y.as = Y` holds by `rfl`. No comparison isomorphism is needed on
that leg.

*The universe shape.* `DifferentialGradedModule.General.exists_propertyP_resolution` produces a
resolution in the module universe it is given, and that universe must absorb the algebra's — the
graded pieces of a property-(P) filtration are direct sums of shifts of the algebra. The module
universe is therefore written `max v w` throughout, which is the shape in which a consumer with
an algebra in universe `0` and modules in a large universe needs it; see the implementation notes
of `StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclicGeneral`.

## References

* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP)
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
* [Stacks Project, Tag 0BYW](https://stacks.math.columbia.edu/tag/0BYW)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- The localization functor `K(A, d) ⥤ D(A, d)` is essentially surjective, being the
localization functor of a localization. -/
instance essSurj_quasiIsomorphisms_Q :
    (quasiIsomorphisms.{u, v, max v w} A).Q.EssSurj :=
  Localization.essSurj _ (quasiIsomorphisms.{u, v, max v w} A)

/-- The differential graded module underlying a chosen preimage of an object of `D(A, d)` under
the localization functor. Objects of the homotopy category *are* differential graded modules, so
this is the preimage itself with its homotopy-category wrapper removed. -/
def derivedPreimage (M : derivedCategory.{u, v, max v w} A) :
    DifferentialGradedModule.{u, v, max v w} A :=
  ((quasiIsomorphisms.{u, v, max v w} A).Q.objPreimage M).as

/-- The chosen preimage does represent the given object. -/
def derivedPreimageIso (M : derivedCategory.{u, v, max v w} A) :
    (quasiIsomorphisms.{u, v, max v w} A).Q.obj
        ((toHomotopyCategory A).obj (derivedPreimage.{u, v, w} A M)) ≅ M :=
  (quasiIsomorphisms.{u, v, max v w} A).Q.objObjPreimageIso M

/-- **A chosen property-(P) representative of an object of `D(A, d)`.** The property-(P)
resolution of Tag 09KP of the differential graded module underlying a chosen preimage of the
object under the localization functor. -/
def propertyPModel (M : derivedCategory.{u, v, max v w} A) :
    DifferentialGradedModule.{u, v, max v w} A :=
  (General.exists_propertyP_resolution.{u, v, w} A (derivedPreimage.{u, v, w} A M)).choose

/-- The augmentation of the chosen property-(P) representative into the chosen preimage. -/
def propertyPModelMap (M : derivedCategory.{u, v, max v w} A) :
    propertyPModel.{u, v, w} A M ⟶ derivedPreimage.{u, v, w} A M :=
  (General.exists_propertyP_resolution.{u, v, w} A
    (derivedPreimage.{u, v, w} A M)).choose_spec.choose

/-- The augmentation of the chosen property-(P) representative is a quasi-isomorphism of the
underlying cochain complexes. -/
theorem quasiIso_propertyPModelMap (M : derivedCategory.{u, v, max v w} A) :
    QuasiIso ((forgetToCochainComplex A).map (propertyPModelMap.{u, v, w} A M)) :=
  (General.exists_propertyP_resolution.{u, v, w} A
    (derivedPreimage.{u, v, w} A M)).choose_spec.choose_spec.1

/-- **The chosen representative has property (P).** -/
theorem propertyPFiltration_propertyPModel (M : derivedCategory.{u, v, max v w} A) :
    Nonempty (General.PropertyPFiltration (propertyPModel.{u, v, w} A M)) :=
  (General.exists_propertyP_resolution.{u, v, w} A
    (derivedPreimage.{u, v, w} A M)).choose_spec.choose_spec.2

/-- **The chosen representative is orthogonal on the left to the acyclic modules**, which is
Tag 09KM at independent universes applied to its property-(P) filtration. -/
theorem leftOrthogonal_acyclic_propertyPModel (M : derivedCategory.{u, v, max v w} A) :
    (acyclic.{u, v, max v w} A).leftOrthogonal
      ((toHomotopyCategory A).obj (propertyPModel.{u, v, w} A M)) :=
  General.leftOrthogonal_acyclic_of_propertyP.{u, v, w}
    (propertyPFiltration_propertyPModel.{u, v, w} A M).some

/-- The augmentation of the chosen property-(P) representative becomes invertible in
`D(A, d)`. -/
instance isIso_Q_map_propertyPModelMap (M : derivedCategory.{u, v, max v w} A) :
    IsIso ((quasiIsomorphisms.{u, v, max v w} A).Q.map
      ((toHomotopyCategory A).map (propertyPModelMap.{u, v, w} A M))) :=
  Localization.inverts (quasiIsomorphisms.{u, v, max v w} A).Q
    (quasiIsomorphisms.{u, v, max v w} A) _
    ((quasiIsomorphisms_map_iff A _).2 (quasiIso_propertyPModelMap.{u, v, w} A M))

/-- **The chosen property-(P) module does represent the given object of `D(A, d)`.** Its
augmentation into the chosen preimage is a quasi-isomorphism, hence invertible in `D(A, d)`, and
the chosen preimage represents the object by essential surjectivity of the localization
functor. -/
def propertyPModelIso (M : derivedCategory.{u, v, max v w} A) :
    (quasiIsomorphisms.{u, v, max v w} A).Q.obj
        ((toHomotopyCategory A).obj (propertyPModel.{u, v, w} A M)) ≅ M :=
  asIso ((quasiIsomorphisms.{u, v, max v w} A).Q.map
      ((toHomotopyCategory A).map (propertyPModelMap.{u, v, w} A M))) ≪≫
    derivedPreimageIso.{u, v, w} A M

/-! ### `Ext` out of an arbitrary object of the derived category -/

/-- **`H^n(Hom^•_{(A, d)}(P_M, P_N)) = Ext^n_{D(A, d)}(M, N)` for arbitrary `M`, `N` in
`D(A, d)`**, where `P_M` and `P_N` are the chosen property-(P) representatives.

This is the content of Tag 0BYW with no hypothesis on `M` or `N`: the property-(P) reduction is
performed by the choice of representative rather than assumed. On the representatives it is
`DifferentialGradedModule.General.homComplexExtEquivOfPropertyP`, and the two isomorphisms
`DifferentialGradedModule.propertyPModelIso` transport the `Ext`-group from the representatives
to the objects, the shift being moved across by the commutation of the shift functor with an
isomorphism. -/
@[stacks 0BYW "the cohomology of the differential graded Hom complex of chosen property-(P) \
representatives is Ext between the objects they represent, at independent universes"]
def propertyPModelExtEquiv (M N : derivedCategory.{u, v, max v w} A) (n : ℤ) :
    ↥((General.homComplex A (propertyPModel.{u, v, w} A M)
        (propertyPModel.{u, v, w} A N)).homology n) ≃+ (M ⟶ N⟦n⟧) :=
  (General.homComplexExtEquivOfPropertyP.{u, v, w} A n
      (propertyPFiltration_propertyPModel.{u, v, w} A M)).trans
    (Linear.homCongr ℤ (propertyPModelIso.{u, v, w} A M)
      ((CategoryTheory.shiftFunctor (derivedCategory.{u, v, max v w} A) n).mapIso
        (propertyPModelIso.{u, v, w} A N))).toAddEquiv

end DifferentialGradedModule

end

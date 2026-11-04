module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclicGeneral
public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute
public import StacksFrontier.CategoryTheory.Functor.Derived.OrthogonalResolutions
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexHomotopy
public import StacksFrontier.Homology.PseudoCoherent.BaseChange

/-!
# The derived tensor product with a complex of modules on a ringed site

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. Tensoring
with `K` is a functor `K(Mod_(E, d)) ⥤ K(O)` of homotopy categories; followed by localization of
the target it becomes a functor `K(Mod_(E, d)) ⥤ D(O)`, and its left derived functor is defined
on all of `D(E, d)`. The resulting functor is the derived tensor product
`- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory`: the functor being derived,
  `K(Mod_(E, d)) ⥤ D(O)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived`: the derived tensor product
  `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCounit`: its comparison with ordinary
  tensoring.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap`: the maps
  `Ext^n_{D(E, d)}(M, N) → Ext^n_{D(O)}(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)` induced by `- ⊗_E^𝐋 K`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategoryExtMap`: the same maps before
  deriving, induced by tensoring with `K` on the homotopy category.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_isLeftDerivable`: the left
  derived functor is defined at every object of `K(Mod_(E, d))`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_hasLeftDerivedFunctor`: the
  total left derived functor exists; this is what names `- ⊗_E^𝐋 K` on `D(E, d)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isLeftDerivedFunctor`: the comparison
  exhibits `- ⊗_E^𝐋 K` as that left derived functor.
* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerivedCounit_app_of_leftOrthogonal` and
  `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerivedCounit_app_of_propertyP`: the
  comparison `- ⊗_E^𝐋 K → - ⊗_E K` is invertible at an object orthogonal on the left to the
  acyclic modules, in particular at a differential graded module with property (P).
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCommShift`: `- ⊗_E^𝐋 K` commutes with
  the translation, which is what makes the maps on `Ext` available.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap_q`: on a class coming from
  `K(Mod_(E, d))` the map on `Ext` is, through the comparison with ordinary tensoring, the map
  induced by tensoring with `K`.

## Implementation notes

The criterion is the one of Tag 06XN, in the form of
`CategoryTheory.ObjectProperty.hasLeftDerivedFunctor_of_leftOrthogonal_resolutions`: it suffices
that every object of `K(Mod_(E, d))` receive a quasi-isomorphism from an object orthogonal on
the left to the acyclic modules. The source checks the hypothesis of Tag 06XN with the modules
having property (P), whose quasi-isomorphisms are homotopy equivalences by Tag 09KY; the
orthogonality used here is the same input in the form of Tag 09KM.

The endomorphism differential graded algebra of a complex of sheaves is an algebra over the base
ring `R` whose carrier lies in the section universe of the site, so the base ring and the algebra
live in different universes. The resolutions are therefore taken from
`DifferentialGradedModule.exists_trW_leftOrthogonal_acyclic`, which is Tag 09KP followed by
Tag 09KM at independent universes, and the homotopy and derived categories are the
universe-polymorphic ones of `StacksFrontier.Algebra.DGA.QuasiIsomorphisms` and
`StacksFrontier.Algebra.DGA.DerivedCategory`.

The maps on `Ext` of Tag 0CS6 are `Ext^n_{D(C)}(X, Y) = Hom_{D(C)}(X, Y[n])` throughout, so what
has to be supplied for them to exist is a commutation of `- ⊗_E^𝐋 K` with the translation; that
is `StacksDraft.PseudoCoherence.leftDerivedCommShift`, the commutation a total left derived
functor inherits from the functor being derived.

*The base ring is the source's.* Everything in this file is formed at
`AlgebraicGeometry.RingedSite.Rep X R K` for the `R` of the source — a commutative ring with an
`R`-linear structure on the sheaves of `O`-modules whose scalars are sections of `O`
(`AlgebraicGeometry.RingedSite.ScalarSections`), which by
`AlgebraicGeometry.RingedSite.ScalarSections.algebraSheaf` is exactly the source's datum of a
sheaf of commutative `R`-algebras. So `E` is a differential graded `R`-algebra, `D(E, d)` is its
derived category of differential graded modules, `- ⊗_E^𝐋 K` is defined on it, and `Ext` is a
module over `R`. At `R = ℤ` the instance is `AlgebraicGeometry.RingedSite.scalarSectionsInt`.

What is *not* carried here is the reading of the whole of `RHom(M, N)` and
`RHom_O(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)` in `D(R)` rather than of the individual `Ext`-groups as
`R`-modules; for that, and for the source's canonical map itself — whose target is the global
derived hom of Cohomology on Sites, Section 21.36 (Tag 0B6E) —
see `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMap` and the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHom`.

## References

* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW)
* [Stacks Project, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN)
* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe u v w t s o

namespace AlgebraicGeometry.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- Tensoring with `K`, followed by localization of the target: the functor
`K(Mod_(E, d)) ⥤ D(O)` whose left derived functor is the derived tensor product with `K`. -/
def tensorWithComplexToDerivedCategory :
    DifferentialGradedModule.HomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra ⥤
      DerivedCategory (TensorModO.{u, v, w, t, s} X) :=
  tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙ DerivedCategory.Qh

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Every object of the homotopy category of differential graded modules over the endomorphism
algebra of `K` receives a quasi-isomorphism from an object orthogonal on the left to the acyclic
modules: a resolution by a module with property (P). -/
theorem exists_trW_leftOrthogonal_acyclic_rep
    (Y : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra) :
    ∃ (P : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra)
      (f : P ⟶ Y), (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).trW f ∧
        (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal P := by
  obtain ⟨M⟩ := Y
  obtain ⟨P, f, hf, ⟨F⟩⟩ :=
    DifferentialGradedModule.General.exists_propertyP_resolution.{o, max u v w t s, 0} _ M
  refine ⟨(toHomotopyCategory _).obj P, (toHomotopyCategory _).map f, ?_,
    DifferentialGradedModule.General.leftOrthogonal_acyclic_of_propertyP.{o, max u v w t s, 0} F⟩
  rw [acyclic_trW_eq_quasiIsomorphisms, quasiIsomorphisms_map_iff]
  exact hf

/-- **Stacks 09LX**, in the source's own sense. The left derived functor of tensoring with `K`,
followed by localization of the target, is defined at every object of `K(Mod_(E, d))`: the
pro-object of its values along the quasi-isomorphisms into an object is essentially constant. -/
@[stacks 09LX "existence in the pro-object sense"]
theorem tensorWithComplexToDerivedCategory_isLeftDerivable :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).IsLeftDerivable
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms]
  refine (acyclic (Rep.{u, v, w, t, s, o} X R
    K).algebra).isLeftDerivable_of_leftOrthogonal_resolutions
    _ (exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, o} X R K) ?_
  rw [acyclic_trW_eq_quasiIsomorphisms]
  exact (quasiIsomorphisms_isSaturated _).isSaturatedMultiplicative

/-- **Stacks 09LX**, in the Kan extension sense. Tensoring with `K`, followed by localization of
the target, has a total left derived functor on `D(E, d)`. -/
@[stacks 09LX "existence of the total left derived functor"]
theorem tensorWithComplexToDerivedCategory_hasLeftDerivedFunctor :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).HasLeftDerivedFunctor
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms]
  exact ObjectProperty.hasLeftDerivedFunctor_of_leftOrthogonal_resolutions
    (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra) _
    (exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, o} X R K)

/-- **Stacks 09LX.** The derived tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)`: the total left
derived functor of tensoring with `K` followed by localization of the target. -/
@[stacks 09LX "the derived tensor functor"]
def tensorWithComplexDerived :
    DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, o} X R K).algebra ⥤
      DerivedCategory (TensorModO.{u, v, w, t, s} X) := by
  letI := tensorWithComplexToDerivedCategory_hasLeftDerivedFunctor.{u, v, w, t, s, o} X R K
  exact (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).totalLeftDerived
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)

/-- The canonical comparison from the derived tensor product to ordinary tensoring: the counit
of the Kan extension defining `- ⊗_E^𝐋 K`. -/
def tensorWithComplexDerivedCounit :
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
        tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⟶
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K := by
  letI := tensorWithComplexToDerivedCategory_hasLeftDerivedFunctor.{u, v, w, t, s, o} X R K
  exact (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).totalLeftDerivedCounit
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)

/-- The universal property of **Stacks 09LX**: the comparison exhibits `- ⊗_E^𝐋 K` as the left
derived functor of tensoring with `K` followed by localization of the target. -/
@[stacks 09LX "universal property"]
instance tensorWithComplexDerived_isLeftDerivedFunctor :
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).IsLeftDerivedFunctor
      (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) := by
  let _ := tensorWithComplexToDerivedCategory_hasLeftDerivedFunctor.{u, v, w, t, s, o} X R K
  change ((tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).totalLeftDerived
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)).IsLeftDerivedFunctor
    ((tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).totalLeftDerivedCounit
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra))
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
  infer_instance

/-! ### Where the comparison with ordinary tensoring is invertible -/

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- **Morphisms out of a left-orthogonal object are not changed by localization.** If `P` is
orthogonal on the left to the acyclic differential graded modules over the endomorphism algebra
of `K`, then the localization functor `K(Mod_(E, d)) ⥤ D(E, d)` is bijective on the morphisms
out of `P`.

This is `DifferentialGradedModule.bijective_q_map_of_leftOrthogonal` at the independent universes
of the endomorphism algebra: the quasi-isomorphisms are the class attached to the acyclic objects
by `DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`, so the localization is one at that
class and Mathlib's orthogonality criterion applies. -/
theorem bijective_q_map_of_leftOrthogonal_rep
    {P : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra}
    (hP : (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal P)
    (Y : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra) :
    Function.Bijective ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map :
      (P ⟶ Y) → _) := by
  have hloc : (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.IsLocalization
      (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).trW := by
    rw [acyclic_trW_eq_quasiIsomorphisms]
    infer_instance
  exact hP.map_bijective_of_isTriangulated _ Y

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Every object of `K(Mod_(E, d))` receives a quasi-isomorphism from an object out of which the
localization functor is bijective on morphisms: the property-(P) resolution of
`AlgebraicGeometry.RingedSite.exists_trW_leftOrthogonal_acyclic_rep` together with
`AlgebraicGeometry.RingedSite.bijective_q_map_of_leftOrthogonal_rep`. -/
theorem exists_resolution_q_map_bijective_rep
    (Y : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra) :
    ∃ (P : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra) (f : P ⟶ Y),
      quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra f ∧
        ∀ Z : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, o} X R K).algebra,
          Function.Bijective ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map :
            (P ⟶ Z) → _) := by
  obtain ⟨P, f, hf, hP⟩ := exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, o} X R K Y
  rw [acyclic_trW_eq_quasiIsomorphisms] at hf
  exact ⟨P, f, hf, fun Z => bijective_q_map_of_leftOrthogonal_rep.{u, v, w, t, s, o} X R K hP Z⟩

/-- The left derived functor of tensoring with `K` followed by localization of the target is
*pointwise* defined: the resolutions of
`AlgebraicGeometry.RingedSite.exists_resolution_q_map_bijective_rep` are by objects at which the
localization functor is fully faithful, which is what makes the pointwise right Kan extension
exist. This is the form of existence that locates the comparison map. -/
instance tensorWithComplexToDerivedCategory_hasPointwiseLeftDerivedFunctor :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).HasPointwiseLeftDerivedFunctor
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) :=
  Functor.hasPointwiseLeftDerivedFunctor_of_resolutions _ _
    (exists_resolution_q_map_bijective_rep.{u, v, w, t, s, o} X R K)

/-- **The comparison `- ⊗_E^𝐋 K → - ⊗_E K` is invertible at a left-orthogonal object.** At an
object `P` of `K(Mod_(E, d))` orthogonal on the left to the acyclic modules the derived tensor
product is computed by the ordinary one.

The comparison exhibits `- ⊗_E^𝐋 K` as a pointwise right Kan extension along the localization,
and at an object out of which the localization is bijective on morphisms the identity is an
initial object of the comparison's index category, so the comparison is invertible there. -/
theorem isIso_tensorWithComplexDerivedCounit_app_of_leftOrthogonal
    {P : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra}
    (hP : (acyclic (Rep.{u, v, w, t, s, o} X R K).algebra).leftOrthogonal P) :
    IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P) :=
  (Functor.RightExtension.mk _
      (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)).isIso_hom_app_of_bijective
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
      (tensorWithComplexDerived.{u, v, w, t, s, o} X R K)
      (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) _)
    (fun Z => bijective_q_map_of_leftOrthogonal_rep.{u, v, w, t, s, o} X R K hP Z)

/-- **The comparison `- ⊗_E^𝐋 K → - ⊗_E K` is invertible at a module with property (P).** A
differential graded module with property (P) is orthogonal on the left to the acyclic modules,
which is Tag 09KM at independent universes, so the previous statement applies: on such a module
the derived tensor product with `K` is the ordinary one. -/
theorem isIso_tensorWithComplexDerivedCounit_app_of_propertyP
    {M : DifferentialGradedModule.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra}
    (hM : Nonempty (DifferentialGradedModule.General.PropertyPFiltration M)) :
    IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app
      ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).obj M)) :=
  isIso_tensorWithComplexDerivedCounit_app_of_leftOrthogonal.{u, v, w, t, s, o} X R K
    (DifferentialGradedModule.General.leftOrthogonal_acyclic_of_propertyP.{o,
      max u v w t s, 0} hM.some)

/-! ### The maps induced on `Ext` -/

/-- Tensoring with `K`, followed by localization of the target, commutes with the translation:
both factors do, tensoring by the commutation of Tag 09LW and localization by the shift of the
derived category. -/
instance tensorWithComplexToDerivedCategoryCommShift :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).CommShift ℤ := by
  unfold tensorWithComplexToDerivedCategory
  infer_instance

/-- **The derived tensor product with `K` commutes with the translation.** `- ⊗_E^𝐋 K` is the
total left derived functor of tensoring with `K` followed by localization; that functor and the
localization functor of `K(Mod_(E, d))` both commute with the translation and the
quasi-isomorphisms are stable under it, so the derived functor does too. -/
@[instance_reducible]
instance tensorWithComplexDerivedCommShift :
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K)
    (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) ℤ

/-- The comparison `- ⊗_E^𝐋 K → - ⊗_E K` is compatible with the commutation with the translation
of `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCommShift`. -/
instance tensorWithComplexDerivedCounitCommShift :
    NatTrans.CommShift (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K) ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K)
    (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) ℤ

/-- The map `Hom_{K(Mod_(E, d))}(P, Y[n]) → Hom_{D(O)}(P ⊗_E K, (Y ⊗_E K)[n])` induced by
tensoring with `K` on the homotopy category, followed by localization of the target. -/
def tensorWithComplexToDerivedCategoryExtMap
    {P Y : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra} (n : ℤ) (f : P ⟶ Y⟦n⟧) :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).obj P ⟶
      ((tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).obj Y)⟦n⟧ :=
  (tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).map f ≫
    ((tensorWithComplexToDerivedCategory.{u, v, w, t, s, o} X R K).commShiftIso n).hom.app Y

/-- **Stacks 0CS6.** *The maps
`Ext^n_{D(E, d)}(M, N) → Ext^n_{D(𝒪)}(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)` induced by the functor
`- ⊗_E^𝐋 K^•`.* With `Ext^n_{D(C)}(X, Y) = Hom_{D(C)}(X, Y[n])`, the map induced by a functor
is its action on morphisms followed by its commutation with the translation, here that of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCommShift`. -/
@[stacks 0CS6 "the induced maps on Ext"]
def tensorWithComplexDerivedExtMap
    {M N : DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, o} X R K).algebra} (n : ℤ)
    (f : M ⟶ N⟦n⟧) :
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj M ⟶
      ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj N)⟦n⟧ :=
  (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).map f ≫
    ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).commShiftIso n).hom.app N

/-- The map on `Ext` induced by `- ⊗_E^𝐋 K` is contravariantly functorial: precomposing a class
with a morphism of `D(E, d)` precomposes its image with the image of that morphism. -/
theorem tensorWithComplexDerivedExtMap_comp_left
    {M M' N : DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, o} X R K).algebra}
    (n : ℤ) (g : M' ⟶ M) (f : M ⟶ N⟦n⟧) :
    tensorWithComplexDerivedExtMap.{u, v, w, t, s, o} X R K n (g ≫ f) =
      (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).map g ≫
        tensorWithComplexDerivedExtMap.{u, v, w, t, s, o} X R K n f := by
  simp [tensorWithComplexDerivedExtMap]

/-- The map on `Ext` induced by `- ⊗_E^𝐋 K` is covariantly functorial: postcomposing a class
with the `n`-shift of a morphism of `D(E, d)` postcomposes its image with the `n`-shift of the
image of that morphism. -/
theorem tensorWithComplexDerivedExtMap_comp_right
    {M N N' : DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, o} X R K).algebra}
    (n : ℤ) (f : M ⟶ N⟦n⟧) (h : N ⟶ N') :
    tensorWithComplexDerivedExtMap.{u, v, w, t, s, o} X R K n (f ≫ h⟦n⟧') =
      tensorWithComplexDerivedExtMap.{u, v, w, t, s, o} X R K n f ≫
        ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).map h)⟦n⟧' := by
  simp [tensorWithComplexDerivedExtMap, Functor.commShiftIso_hom_naturality]

/-- **Stacks 0CS6, the maps on `Ext` are those induced by tensoring with `K`.** On a class coming
from `K(Mod_(E, d))`, the map induced by `- ⊗_E^𝐋 K` agrees, through the comparison
`- ⊗_E^𝐋 K → - ⊗_E K` of Tag 09LX, with the map induced by the differential graded tensor
functor of Tag 09LV read on homotopy categories. This is the compatibility of that comparison
with the translation. -/
@[stacks 0CS6 "the maps on Ext are those induced by tensoring with K"]
theorem tensorWithComplexDerivedExtMap_q
    {P Y : DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra} (n : ℤ) (f : P ⟶ Y⟦n⟧) :
    (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P ≫
        tensorWithComplexToDerivedCategoryExtMap.{u, v, w, t, s, o} X R K n f =
      tensorWithComplexDerivedExtMap.{u, v, w, t, s, o} X R K n
          ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map f ≫
            (((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q).commShiftIso n).hom.app
              Y) ≫
        ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app Y)⟦n⟧' := by
  dsimp [tensorWithComplexToDerivedCategoryExtMap, tensorWithComplexDerivedExtMap]
  rw [← Category.assoc, ← (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).naturality f,
    Category.assoc,
    ← NatTrans.shift_app_comm (tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K) n Y,
    Functor.commShiftIso_comp_hom_app, Functor.map_comp]
  simp

end AlgebraicGeometry.RingedSite

end

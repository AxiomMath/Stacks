module

public import StacksFrontier.Algebra.DifferentialGraded.Module.ExtLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorLinear
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.SignTwist

/-!
# The derived tensor product with a complex is linear over the base ring

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded `R`-algebra. The
derived category `D(E, d)` is `R`-linear, and so is `D(O)`, through the `R`-linear structure of
the `O`-modules. This file proves that the derived tensor product
`- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX is `R`-linear.

By `CategoryTheory.Functor.linear_iff` it suffices that `r • 𝟙 M` is sent to `r • 𝟙`. On
differential graded modules that is the `R`-linearity of the differential graded tensor functor
of Tag 09LV on its Hom-modules; it passes to the homotopy categories, whose quotient functors
are `R`-linear, and to the derived categories through the comparison of the derived tensor
product with the ordinary one, which is invertible at every module orthogonal on the left to the
acyclic modules. The argument is that of
`StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorLinear` for bimodules.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_linear`

## References

* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type u) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, u} X R]
  (K : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- On differential graded modules, tensoring with `K` carries `r • 𝟙 M` to `r • 𝟙`: the
differential graded tensor functor of Tag 09LV is `R`-linear on its Hom-modules. -/
theorem dgFunctorToComplexes_tensorWithComplexDG_map_smul_id
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) (r : R) :
    (dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).map
        (r • 𝟙 M) =
      r • 𝟙 ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
        M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  have h : (cocycleOfHom _ (r • 𝟙 M)).1 =
      r • (dgCategory (Rep.{u, u, u, u, u, u} X R K).algebra).id M := by
    rfl
  change ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map
    (cocycleOfHom _ (r • 𝟙 M)).1).v i i (add_zero i) = _
  rw [h, (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map_smul,
    (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map_id]
  rfl

/-- On the homotopy categories, tensoring with `K` carries `r • 𝟙 P` to `r • 𝟙`. -/
theorem tensorWithComplexHomotopy_map_smul_id
    (P : DifferentialGradedModule.HomotopyCategory.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra)
    (r : R) :
    (tensorWithComplexHomotopy.{u, u, u, u, u, u} X R K).map (r • 𝟙 P) =
      r • 𝟙 ((tensorWithComplexHomotopy.{u, u, u, u, u, u} X R K).obj P) := by
  obtain ⟨M⟩ := P
  have hid : (toHomotopyCategory (Rep.{u, u, u, u, u, u} X R K).algebra).map (r • 𝟙 M) =
      r • 𝟙 ((toHomotopyCategory (Rep.{u, u, u, u, u, u} X R K).algebra).obj M) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  change (tensorWithComplexHomotopy.{u, u, u, u, u, u} X R K).map
    (r • 𝟙 ((toHomotopyCategory (Rep.{u, u, u, u, u, u} X R K).algebra).obj M)) = _
  rw [← hid, tensorWithComplexHomotopy_map, dgFunctorToComplexes_tensorWithComplexDG_map_smul_id,
    Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- Tensoring with `K` followed by the localization of `K(O)` carries `r • 𝟙 P` to `r • 𝟙`. -/
theorem tensorWithComplexToDerivedCategory_map_smul_id
    (P : DifferentialGradedModule.HomotopyCategory.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra)
    (r : R) :
    (tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R K).map (r • 𝟙 P) =
      r • 𝟙 ((tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R K).obj P) := by
  change DerivedCategory.Qh.map ((tensorWithComplexHomotopy.{u, u, u, u, u, u} X R K).map
    (r • 𝟙 P)) = _
  rw [tensorWithComplexHomotopy_map_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- The derived tensor product carries `r • 𝟙` to `r • 𝟙` at the class of an object orthogonal
on the left to the acyclic modules, where its comparison with the ordinary tensor product is
invertible. -/
theorem tensorWithComplexDerived_map_smul_id_q
    (P : DifferentialGradedModule.HomotopyCategory.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra)
    (hP : (acyclic (Rep.{u, u, u, u, u, u} X R K).algebra).leftOrthogonal P) (r : R) :
    (tensorWithComplexDerived.{u, u, u, u, u, u} X R K).map
        (r • 𝟙 ((quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.obj P)) =
      r • 𝟙 ((tensorWithComplexDerived.{u, u, u, u, u, u} X R K).obj
        ((quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.obj P)) := by
  have := isIso_tensorWithComplexDerivedCounit_appOver.{u, u, u, u, u, u} X R K P hP
  have hq : (quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.map (r • 𝟙 P) =
      r • 𝟙 ((quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.obj P) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have hnat := (tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R K).naturality (r • 𝟙 P)
  rw [Functor.comp_map, hq, tensorWithComplexToDerivedCategory_map_smul_id] at hnat
  refine (cancel_mono ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R K).app P)).mp
    (hnat.trans ?_)
  rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- **The derived tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` is `R`-linear.** Every object of
`D(E, d)` is isomorphic to the class of a module orthogonal on the left to the acyclic modules (a
module with property (P)), so `CategoryTheory.Functor.linear_iff` reduces the statement to
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_map_smul_id_q`. -/
instance tensorWithComplexDerived_linear :
    (tensorWithComplexDerived.{u, u, u, u, u, u} X R K).Linear R := by
  rw [Functor.linear_iff]
  intro M r
  have := Localization.essSurj (quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q
    (quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra)
  obtain ⟨P, f, hf, hP⟩ := exists_trW_leftOrthogonal_acyclic_rep.{u, u, u, u, u, u} X R K
    ((quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.objPreimage M)
  rw [acyclic_trW_eq_quasiIsomorphisms] at hf
  have : IsIso ((quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.map f) :=
    Localization.inverts (quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q
      (quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra) f hf
  exact Functor.map_smul_id_of_iso _
    ((asIso ((quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.map f) ≪≫
      (quasiIsomorphisms (Rep.{u, u, u, u, u, u} X R K).algebra).Q.objObjPreimageIso M).symm) r
    (tensorWithComplexDerived_map_smul_id_q X R K P hP r)

end AlgebraicGeometry.RingedSite

end

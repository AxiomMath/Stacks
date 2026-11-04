module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived

/-!
# The derived tensor product with a complex of quasi-coherent cohomology

Let `(C, O)` be a ringed site — for instance the small etale site of an algebraic space over a
scheme, with its structure sheaf — let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The derived
tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX is built in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived`. This file studies where it
sends an object whose cohomology sheaves are quasi-coherent.

Two things are proved. First, every value of `- ⊗_E^𝐋 K` is the plain tensor product
`P ⊗_E K`, taken in the derived category of `O`-modules, for some differential graded `E`-module
`P` left orthogonal to the acyclic modules; this is the reduction with which the source's proof
opens. Second, at the free rank-one module `E` itself the derived tensor product gives back `K`,
so that it lands in `D_QCoh(O)` as soon as `K` does.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerivedCounit_app`: the comparison of
  `- ⊗_E^𝐋 K` with plain tensoring is invertible at every differential graded `E`-module left
  orthogonal to the acyclic modules.
* `AlgebraicGeometry.RingedSite.exists_leftOrthogonal_iso_tensorWithComplexDerived_obj`: every
  value of `- ⊗_E^𝐋 K` is isomorphic to `P ⊗_E K` for such a `P`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedObjRegularIso`: the value of
  `- ⊗_E^𝐋 K` at the regular module `E` is `K`.
* `AlgebraicGeometry.RingedSite.derivedCategoryB_tensorWithComplexDerived_obj_regular`: the
  clause proved here — that value lies in `D_QCoh(O)` when `K` does.

## What is not proved

The source asserts that the *whole* image of `- ⊗_E^𝐋 K` lies in `D_QCoh(O)`, and deduces
that from the clause proved here by a dévissage: a differential graded `E`-module `P` with
property (P) is the homotopy colimit of the stages of its filtration, each stage carries a
finite filtration whose graded pieces are direct sums of shifts of `E`, and `E[k] ⊗_E K` is
`K[k]`. Running that argument needs, over and above what is proved here:

* that `D_QCoh(O)` is a strictly full triangulated subcategory of `D(O)` closed under direct
  sums. For the small etale site of an algebraic space these are Tags 03M1 and 08F3; in this
  repository they are available as
  `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass` and
  `AlgebraicGeometry.Space.isClosedUnderCoproducts_quasicoherentDerivedCategory`, each on the
  closure hypotheses recorded there;
* the dévissage for `D(E, d)` itself, Tag 0FQE. The repository has it as
  `DifferentialGradedModule.property_of_coproducts_of_two_out_of_three_of_shifts`, but only for
  a differential graded algebra whose carrier lies in the universe of its base ring. The
  endomorphism algebra of a complex of sheaves is an algebra over `ℤ` whose carrier lies in the
  section universe of the site, so that form does not apply and a universe-polymorphic 0FQE is
  the missing input;
* the compatibility of `- ⊗_E K` with the filtration of property (P): that it carries the
  admissible short exact sequences of Tags 09KK and 09KL to distinguished triangles of `K(O)`
  and commutes with the direct sums occurring there.

## Implementation notes

*Why the regular module is spelled as a representable.* The object of `D(E, d)` at which the
value is computed is the image of `Hom(K, K)` viewed as a module over itself, which is how the
endomorphism algebra enters Tag 09LX; it is `(Rep X K).functor.obj (liftComplex X K)`.
`DGCategory.representableSelfIsoRegular` identifies it with
`DifferentialGradedModule.regularModule` of the endomorphism algebra. The two have the same
carrier, grading and differential on the nose; only the right action differs in its
presentation, as composition against multiplication in the endomorphism algebra, and
`DGCategory.repActionLinear_eq_mul` is that comparison.

*Why the counit is invertible on the left orthogonal.* `- ⊗_E^𝐋 K` is a right Kan extension
along the localization functor `Q`, and Tag 09LX already provides the resolutions that make it
a pointwise one. At an object `P` orthogonal on the left to the acyclic modules, `Q` is
bijective on the morphisms out of `P`, so the identity of `Q.obj P` is initial in the category
indexing the limit, by `CategoryTheory.structuredArrowMkIdIsInitial`, and the limit is attained
by its value at `P`. This is the same input, in the same form, that Tag 09LX uses to produce
the derived functor in the first place; `CategoryTheory.Functor.RightExtension`'s own criterion
cannot be used because it asks for `Q` to be full and faithful.

*How `D_QCoh(O)` is spelled.* Quasi-coherence of an `O`-module is
`SheafOfModules.IsQuasicoherentOnSite`, the site-level notion of Tag 03DL, whose module
universe is free; `SheafOfModules.IsQuasicoherent` would force the sections of a module to live
in the universe of the sections of the structure sheaf, which the ambient category
`TensorModO X` of Tag 09LX never does. `D_QCoh(O)` is then
`DerivedCategoryB.derivedCategoryB` of that property, the objects of `D(O)` all of whose
cohomology sheaves are quasi-coherent. This is the spelling the algebraic-space development of
this repository uses, in `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory`.

*The hypothesis on `K`.* The tensor product of Tag 09LX is formed in the ambient category of
`O`-modules, whose sections absorb the site, the structure ring and the modules; `K` enters it
through `AlgebraicGeometry.RingedSite.liftComplex`, which only raises the universe of its
sections. The hypothesis that the cohomology sheaves of `K` be quasi-coherent is therefore
stated for `liftComplex X K`, which is the complex the functor actually tensors with.

## References

* [Stacks Project, Tag 09MA](https://stacks.math.columbia.edu/tag/09MA)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits DifferentialGradedModule

namespace DGCategory

universe w v u

variable {R : Type u} [CommRing R] {A : DGCategory.{w, v, u} R} {x : A.Obj}

/-- The right action of the endomorphism algebra of `x` on `Hom(x, x)` is its own
multiplication: both are composition in `A`, so they agree on homogeneous elements, and both
are additive in each variable. -/
theorem repActionLinear_eq_mul (a z : endTotal A x) :
    repActionLinear A x x a z = z * a := by
  classical
  let _ : DirectSum.GSemiring (endFamily A x) := (endGRing A x).toGSemiring
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, mul_add]
  | of i a =>
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => rw [map_add, h₁, h₂, add_mul]
    | of n b => rw [repActionLinear_of, DirectSum.of_mul_of]; rfl

/-- The identity of `Hom(x, x)`, as a homomorphism from the representable module at `x` to the
regular module over the endomorphism algebra of `x`. -/
noncomputable def representableSelfToRegular :
    representableModule A x x ⟶ regularModule (endAlgebra A x) where
  toFun := LinearMap.id
  map_smul := fun z a => repActionLinear_eq_mul a z
  map_grading := fun _ _ hz => hz
  map_d := rfl

/-- The identity of `Hom(x, x)`, in the other direction. -/
noncomputable def representableSelfFromRegular :
    regularModule (endAlgebra A x) ⟶ representableModule A x x where
  toFun := LinearMap.id
  map_smul := fun z a => (repActionLinear_eq_mul a z).symm
  map_grading := fun _ _ hz => hz
  map_d := rfl

/-- `Hom(x, x)`, as a differential graded module over the endomorphism algebra of `x`, is the
regular module over that algebra. -/
noncomputable def representableSelfIsoRegular :
    representableModule A x x ≅ regularModule (endAlgebra A x) where
  hom := representableSelfToRegular
  inv := representableSelfFromRegular
  hom_inv_id := rfl
  inv_hom_id := rfl

end DGCategory

namespace DifferentialGradedModule

universe u w

variable {R : Type u} [CommRing R]

/-- The zero shift of the regular module is the regular module: the shift leaves the carrier
and the action untouched, moves the grading by `n + 0 = n` and multiplies the differential by
`(-1)^0`. -/
noncomputable def shiftZeroIsoRegular (B : DifferentialGradedAlgebra.{u, w} R) :
    shift (regularModule B) 0 ≅ regularModule B where
  hom :=
    { toFun := LinearMap.id
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ hz => by simpa using hz
      map_d := by simp [shift] }
  inv :=
    { toFun := LinearMap.id
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ hz => by simpa using hz
      map_d := by simp [shift] }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The regular module is orthogonal on the left to the acyclic differential graded modules:
every homomorphism from it to an acyclic module is homotopic to zero. This is Tag 09K1 for the
zero shift, at independent universes for the algebra and its base ring. -/
theorem leftOrthogonal_acyclic_regularModule (B : DifferentialGradedAlgebra.{u, w} R) :
    (acyclic B).leftOrthogonal ((toHomotopyCategory B).obj (regularModule B)) := by
  refine General.leftOrthogonal_acyclic_of_iso B (shiftZeroIsoRegular B) ?_
  rw [General.leftOrthogonal_acyclic_iff]
  intro N hN g
  exact (General.isNullHomotopic_iff_homotopic_zero g).mp
    (General.isNullHomotopic_of_acyclic hN 0 g)

end DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-- `Hom(K, K)`, as a module over the endomorphism differential graded algebra of `K`, is
orthogonal on the left to the acyclic modules: it is the regular module over that algebra. -/
theorem leftOrthogonal_acyclic_rep_self :
    (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal
      ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
        ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))) :=
  General.leftOrthogonal_acyclic_of_iso _ DGCategory.representableSelfIsoRegular.symm
    (leftOrthogonal_acyclic_regularModule _)

/-- The comparison of `- ⊗_E^𝐋 K` with plain tensoring is invertible at every object of
`K(Mod_(E, d))` orthogonal on the left to the acyclic modules. -/
theorem isIso_tensorWithComplexDerivedCounit_app
    (P : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (hP : (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal P) :
    IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app P) := by
  have hpw :
      (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).HasPointwiseLeftDerivedFunctor
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) := by
    rw [← acyclic_trW_eq_quasiIsomorphisms]
    exact (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      |>.hasPointwiseLeftDerivedFunctor_of_leftOrthogonal_resolutions _
        (exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, 0} X ℤ K)
  have hloc : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.IsLocalization
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).trW := by
    rw [acyclic_trW_eq_quasiIsomorphisms]
    infer_instance
  have hbij := fun Y => ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated hP
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q Y
  have h := Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
    (F' := tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K)
    (α := tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K)
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
  simpa using (h _).isIso_π_app_of_isInitial _
    (structuredArrowMkIdIsInitial _ P hbij)

/-- **The reduction of Stacks 09MA.** Every value of `- ⊗_E^𝐋 K` is the plain tensor product
with `K` of a differential graded `E`-module orthogonal on the left to the acyclic modules —
in the source, a module with property (P). -/
theorem exists_leftOrthogonal_iso_tensorWithComplexDerived_obj
    (M : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :
    ∃ P : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra,
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal P ∧
        Nonempty ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj M ≅
          (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).obj P) := by
  have hess : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.EssSurj :=
    Localization.essSurj _ (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
  obtain ⟨P, f, hf, hP⟩ :=
    exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, 0} X ℤ K
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.objPreimage M)
  refine ⟨P, hP, ⟨?_⟩⟩
  have hfiso : IsIso ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.map f) := by
    rw [acyclic_trW_eq_quasiIsomorphisms] at hf
    exact Localization.inverts (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) f hf
  have hcounit := isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K P hP
  exact (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.objObjPreimageIso M).symm ≪≫
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso (asIso
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.map f)).symm ≪≫
    asIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app P)

/-- Tensoring `Hom(K, K)` with `K` gives back `K`: the image of the regular module under the
differential graded tensor functor of Tag 09LV, read in the homotopy category of complexes of
ambient `O`-modules. -/
noncomputable def tensorWithComplexHomotopyRegularIso :
    (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).obj
        ((tensorWithComplexDG.{u, v, w, t, s, 0} X ℤ K).functor.obj
          ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))) ≅
      (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).obj
        (liftComplex.{u, v, w, t, s} X K) :=
  (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).mapIso
    ((CochainComplex.complexesToCochainFunctor (TensorModO.{u, v, w, t, s} X)).mapIso
      (tensorWithComplexDG_regular.{u, v, w, t, s, 0} X ℤ K))

/-- **The value of `- ⊗_E^𝐋 K` at the regular module `E` is `K`.** The comparison with plain
tensoring is invertible there, because `Hom(K, K)` is orthogonal on the left to the acyclic
modules, and plain tensoring sends it to `K`. -/
noncomputable def tensorWithComplexDerivedObjRegularIso :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
            ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)))) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) := by
  have hcounit := isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _
    (leftOrthogonal_acyclic_rep_self.{u, v, w, t, s} X K)
  exact asIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app _) ≪≫
    DerivedCategory.Qh.mapIso (tensorWithComplexHomotopyRegularIso.{u, v, w, t, s} X K) ≪≫
    (DerivedCategory.quotientCompQhIso (TensorModO.{u, v, w, t, s} X)).app
      (liftComplex.{u, v, w, t, s} X K)

/-- **Stacks 09MA at the regular module.** Let `K` be a complex of `O`-modules whose cohomology
sheaves are quasi-coherent. Then `- ⊗_E^𝐋 K` sends the free rank-one differential graded
`E`-module to an object of `D_QCoh(O)`, namely to `K` itself.

This carries **no** `@[stacks 09MA]` attribute.  The tag asserts that the *whole image* of
`- ⊗_E^𝐋 K` lies in `D_QCoh(O)`; what is proved here is its value at one object.  That is a
genuine theorem and the first step of the source's proof, but it is not a component the
source delineates, so tagging it would make the project's audit scanner — which matches a
tag's four characters wherever they appear — count 09MA as covered.  The dévissage that
would promote this to the full tag is Stacks 0FQE, discussed in the implementation notes. -/
theorem derivedCategoryB_tensorWithComplexDerived_obj_regular
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
            ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj
              (liftComplex.{u, v, w, t, s} X K))))) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctor (TensorModO.{u, v, w, t, s} X) n).mapIso
      (tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K)).symm) (hK n)

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexHomBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage

/-!
# The comparison `- ⊗_A^𝐋 Hom(L, K) ⟶ RHom(L, - ⊗_A^𝐋 K)`

Let `(C, O)` be a ringed site over a base ring `R` (Stacks 0CS6), let `K` and `L` be complexes of
`O`-modules with endomorphism differential graded algebras `A = End(K)` and `B = End(L)`, and let
`Ω' = Hom(L, K)`, a differential graded `(A, B)`-bimodule. This file constructs the natural
comparison

`Ψ : - ⊗_A^𝐋 Ω' ⟶ RHom(L, - ⊗_A^𝐋 K)`

of functors `D(A, d) ⥤ D(B, d)`, where `- ⊗_A^𝐋 Ω'` is the derived tensor product with a
bimodule (Tag 09LS), `- ⊗_A^𝐋 K` the derived tensor product with `K` (Tag 09LX) and `RHom(L, -)`
derived Hom (Tag 09LY). On a differential graded module `M` it is induced by
`M ⊗_A Hom(L, K) ⟶ Hom(L, M ⊗_A K)`, `x ⊗ φ ↦ (x ⊗ -) ∘ φ`.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorHomComparisonModule`: the comparison on differential
  graded modules.
* `AlgebraicGeometry.RingedSite.tensorHomDGComparisonHomotopy`: the comparison on homotopy
  categories.

## References

* [Stacks Project, Tag 0DK9](https://stacks.math.columbia.edu/tag/0DK9)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

universe u v w t s

namespace AlgebraicGeometry.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type (max u v w t s)) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, max u v w t s} X R]
  (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- `Hom(L, -)` after tensoring with `K`, on a closed degree-zero map: the image of the map under
the composite functor of differential graded categories. -/
theorem homWithComplexOver_map_dgFunctorToComplexes_toFun
    {M M' : DifferentialGradedModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra}
    (g : M ⟶ M') :
    ((homWithComplexOver.{u, v, w, t, s, max u v w t s} X R L).map
        ((dgFunctorToComplexes
          (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor).map g)).toFun =
      ((tensorHomDGFunctor.{u, v, w, t, s} X R K L).map (cocycleOfHom _ g).1).1 := by
  let z : Cocycle _ _ 0 := Cocycle.mk
    ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map (cocycleOfHom _ g).1) 1
    rfl ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map_cocycle
      (cocycleOfHom _ g))
  show ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
    (Cochain.ofHom (Cocycle.homOf z))).1 = _
  rw [show Cochain.ofHom (Cocycle.homOf z) = (z : Cochain _ _ 0) from
    congrArg Subtype.val (Cocycle.ofHom_homOf_eq_self z)]
  rfl

/-- **The comparison `M ⊗_A Φ(A) ⟶ Hom(L, M ⊗_A K)`, on differential graded modules**, for
`Φ(M) = Hom(L, M ⊗_A K)`: the comparison of
`DifferentialGraded.Bimodule.dgFunctorTensorComparison`, read on closed degree-zero maps. -/
def tensorHomComparisonModule :
    DifferentialGraded.Bimodule.tensorCompFunctor
        (DifferentialGraded.Bimodule.ofDGFunctorRegular
          (tensorHomDGFunctor.{u, v, w, t, s} X R K L)) ⟶
      dgFunctorToComplexes (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor ⋙
        homWithComplexOver.{u, v, w, t, s, max u v w t s} X R L where
  app M := homOfCocycle _
    ((DifferentialGraded.Bimodule.dgFunctorTensorComparison
      (tensorHomDGFunctor.{u, v, w, t, s} X R K L)).app M)
  naturality M M' g := by
    apply DifferentialGradedModule.Hom.ext
    have h := congrArg Subtype.val ((DifferentialGraded.Bimodule.dgFunctorTensorComparison
      (tensorHomDGFunctor.{u, v, w, t, s} X R K L)).naturality (cocycleOfHom _ g).1)
    refine h.trans ?_
    change _ = ((homWithComplexOver.{u, v, w, t, s, max u v w t s} X R L).map
        ((dgFunctorToComplexes
          (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor).map g)).toFun ∘ₗ _
    rw [homWithComplexOver_map_dgFunctorToComplexes_toFun]
    rfl

/-- `Hom(L, -)` after tensoring with `K`, on homotopy categories, is the lift of the functor on
differential graded modules. -/
theorem toHomotopyCategory_comp_tensorWithComplexHomotopy_comp_homWithComplexHomotopyOver :
    toHomotopyCategory (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra ⋙
        (tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K ⋙
          homWithComplexHomotopyOver.{u, v, w, t, s, max u v w t s} X R L) =
      (dgFunctorToComplexes (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor ⋙
        homWithComplexOver.{u, v, w, t, s, max u v w t s} X R L) ⋙
          toHomotopyCategory (Rep.{u, v, w, t, s, max u v w t s} X R L).algebra := by
  rw [← Functor.assoc, tensorWithComplexHomotopy_spec, Functor.assoc, Functor.assoc]
  congr 1

/-- **The comparison `M ⊗_A Φ(A) ⟶ Hom(L, M ⊗_A K)`, on homotopy categories**: the comparison on
differential graded modules, descended along the quotient by homotopy. -/
def tensorHomDGComparisonHomotopy :
    DifferentialGraded.Bimodule.tensorHomotopyFunctor
        (DifferentialGraded.Bimodule.ofDGFunctorRegular
          (tensorHomDGFunctor.{u, v, w, t, s} X R K L)) ⟶
      tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K ⋙
        homWithComplexHomotopyOver.{u, v, w, t, s, max u v w t s} X R L :=
  CategoryTheory.Quotient.natTransLift (homotopyRel _)
    ((DifferentialGraded.Bimodule.tensorCompFunctor_quotient _).inv ≫
      Functor.whiskerRight (tensorHomComparisonModule.{u, v, w, t, s} X R K L)
        (toHomotopyCategory _) ≫
      eqToHom
        (toHomotopyCategory_comp_tensorWithComplexHomotopy_comp_homWithComplexHomotopyOver.{u, v,
          w, t, s} X R K L).symm)


/-- `- ⊗_A^𝐋 K` followed by `RHom(L, -)` is a left derived functor of tensoring with `K` followed
by localization and `RHom(L, -)`: the comparison of Tag 09LX, whiskered by `RHom(L, -)`, exhibits
it so, since `- ⊗_A^𝐋 K` is computed on resolutions by modules with property (P). -/
instance tensorWithComplexDerived_comp_derivedHomWithComplexOver_isLeftDerivedFunctor :
    (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
        derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        (tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K)
        (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L))
      (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) :=
  Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q)
    (W := quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
    (tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K)
    (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L)
    (exists_resolution_q_map_bijective_rep.{u, v, w, t, s, max u v w t s} X R K)

/-- The comparison `M ⊗_A^𝐋 Φ(A) ⟶ RHom(L, M ⊗_A K)` on the objects of `K(A, d)`, to which the
universal property of the derived functor is applied: the comparison of Tag 09LS from the derived
to the plain tensor product, the comparison on homotopy categories, and the comparison of
`Hom(L, -)` with its right derived functor. -/
def tensorHomDGComparisonDerivedAux :
    (quasiIsomorphisms' (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q ⋙
        DifferentialGraded.Bimodule.derivedTensorFunctor
          (DifferentialGraded.Bimodule.ofDGFunctorRegular
            (tensorHomDGFunctor.{u, v, w, t, s} X R K L)) ⟶
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, max u v w t s} X R K ⋙
        derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L :=
  DifferentialGraded.Bimodule.derivedTensorFunctorCounit _ ≫
    Functor.whiskerRight (tensorHomDGComparisonHomotopy.{u, v, w, t, s} X R K L)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R L).algebra).Q ≫
    Functor.whiskerLeft (tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K)
      (derivedHomWithComplexUnitOver.{u, v, w, t, s, max u v w t s} X R L)

/-- **The comparison `Ψ : - ⊗_A^𝐋 Φ(A) ⟶ RHom(L, - ⊗_A^𝐋 K)`** of functors `D(A, d) ⥤ D(B, d)`,
for `Φ(A) = Hom(L, A ⊗_A K)`: the unique transformation into the left derived functor
`RHom(L, - ⊗_A^𝐋 K)` compatible with
`AlgebraicGeometry.RingedSite.tensorHomDGComparisonDerivedAux`. -/
def tensorHomDGComparisonDerived :
    DifferentialGraded.Bimodule.derivedTensorFunctor
        (DifferentialGraded.Bimodule.ofDGFunctorRegular
          (tensorHomDGFunctor.{u, v, w, t, s} X R K L)) ⟶
      tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
        derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L :=
  (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
      derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L).leftDerivedLift
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
      (tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K)
      (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L))
    (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
    _ (tensorHomDGComparisonDerivedAux.{u, v, w, t, s} X R K L)

/-- At the image in `D(A, d)` of an object `M` of `K(A, d)`, the comparison
`AlgebraicGeometry.RingedSite.tensorHomDGComparisonDerived` followed by `RHom(L, -)` applied to
the counit of `- ⊗_A^𝐋 K` at `M` equals
`AlgebraicGeometry.RingedSite.tensorHomDGComparisonDerivedAux` at `M`. -/
theorem tensorHomComparisonDerived_fac_app
    (M : DifferentialGradedModule.HomotopyCategory
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) :
    (tensorHomDGComparisonDerived.{u, v, w, t, s} X R K L).app
        ((quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.obj M) ≫
      (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L).map
        ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app M) =
    (tensorHomDGComparisonDerivedAux.{u, v, w, t, s} X R K L).app M := by
  have := Functor.leftDerived_fac_app
    (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
      derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L)
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
      (tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K)
      (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L))
    (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
    _ (tensorHomDGComparisonDerivedAux.{u, v, w, t, s} X R K L) M
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp] at this
  exact this

/-! ### The comparison at the shifts of the regular module -/

/-- The shifts of the regular module are orthogonal on the left to the acyclic modules
(Tag 09K1), at independent universes for the algebra and its base ring. -/
theorem leftOrthogonal_acyclic_shift_regularModule {S : Type*} [CommRing S]
    (B : DifferentialGradedAlgebra S) (k : ℤ) :
    (acyclic B).leftOrthogonal ((toHomotopyCategory B).obj (shift (regularModule B) k)) := by
  rw [General.leftOrthogonal_acyclic_iff]
  intro N hN g
  exact (General.isNullHomotopic_iff_homotopic_zero g).mp
    (General.isNullHomotopic_of_acyclic hN k g)

/-- **`RHom(L, -)` is computed by `Hom(L, -)` on K-injective complexes**: the comparison of
`Hom^•(L, -)` with its right derived functor is invertible at a K-injective complex. -/
theorem isIso_derivedHomWithComplexOverUnit_app_of_isKInjective
    (I : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) [I.IsKInjective] :
    IsIso ((derivedHomWithComplexUnitOver.{u, v, w, t, s, max u v w t s} X R L).app
      ((HomotopyCategory.quotient _ _).obj I)) := by
  let : HasDerivedCategory (TensorModO.{u, v, w, t, s} X) := HasDerivedCategory.standard _
  have := Functor.hasPointwiseRightDerivedFunctor_of_coresolutions
    (L := DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplexToDerivedCategoryOver.{u, v, w, t, s, max u v w t s} X R L)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  exact (Functor.LeftExtension.mk _ (derivedHomWithComplexUnitOver.{u, v, w, t, s, max u v w t s}
      X R L)).isIso_hom_app_of_bijective
    (Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor _ _
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) _)
    (fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z I)

/-- The comparison on differential graded modules is the comparison
`DifferentialGraded.Bimodule.dgFunctorTensorComparisonHom`. -/
theorem tensorHomComparisonModule_app
    (M : DifferentialGradedModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) :
    (tensorHomComparisonModule.{u, v, w, t, s} X R K L).app M =
      DifferentialGraded.Bimodule.dgFunctorTensorComparisonHom
        (tensorHomDGFunctor.{u, v, w, t, s} X R K L) M :=
  DifferentialGradedModule.Hom.ext rfl

/-- The comparison on homotopy categories is invertible at every shift of the regular module. -/
theorem isIso_tensorHomComparisonHomotopy_app_shift (k : ℤ) :
    IsIso ((tensorHomDGComparisonHomotopy.{u, v, w, t, s} X R K L).app
      ((toHomotopyCategory _).obj
        (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k))) := by
  rw [tensorHomDGComparisonHomotopy, CategoryTheory.Quotient.natTransLift_app]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, tensorHomComparisonModule_app,
    eqToHom_app]
  have h := DifferentialGraded.Bimodule.isIso_dgFunctorTensorComparisonHom_shift_regular
    (tensorHomDGFunctor.{u, v, w, t, s} X R K L) k
  have h' := Functor.map_isIso
    (toHomotopyCategory (Rep.{u, v, w, t, s, max u v w t s} X R L).algebra)
    (show DifferentialGraded.Bimodule.tensorObj' _ _ ⟶ _ from
      DifferentialGraded.Bimodule.dgFunctorTensorComparisonHom
        (tensorHomDGFunctor.{u, v, w, t, s} X R K L)
        (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k))
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h' inferInstance)

/-- `A[k] ⊗_A K ≅ K[k]` is K-injective when `K` is. -/
theorem isKInjective_tensorWithComplexDG_obj_shift_regularModule
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] (k : ℤ) :
    ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj
      (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
        k)).IsKInjective := by
  have e₁ := dgFunctorToComplexesShiftIso
    (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor
    (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k
  have e₂ := (asIso (regularPure.{u, v, w, t, s} X R K)).symm
  have : ((dgFunctorToComplexes
        (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor).obj
      (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)).IsKInjective :=
    CochainComplex.isKInjective_of_iso e₂.symm
  exact CochainComplex.isKInjective_of_iso e₁.symm

/-- **The comparison `Ψ` is invertible at every shift of the regular module**, when `K` is
K-injective: there the derived tensor products are computed by the plain ones, the plain
comparison `A[k] ⊗_A Φ(A) ⟶ Hom(L, A[k] ⊗_A K)` is an isomorphism, and
`Hom(L, A[k] ⊗_A K) = Hom(L, K[k])` computes `RHom(L, K[k])`. -/
theorem isIso_tensorHomComparisonDerived_app_shift
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] (k : ℤ) :
    IsIso ((tensorHomDGComparisonDerived.{u, v, w, t, s} X R K L).app
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.obj
        ((toHomotopyCategory _).obj
          (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k)))) := by
  let P := (toHomotopyCategory (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).obj
    (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k)
  have hlo := leftOrthogonal_acyclic_shift_regularModule
    (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra k
  have h₁ : IsIso ((DifferentialGraded.Bimodule.derivedTensorFunctorCounit
      (DifferentialGraded.Bimodule.ofDGFunctorRegular
        (tensorHomDGFunctor.{u, v, w, t, s} X R K L))).app P) :=
    DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal _ P hlo
  have h₂ := isIso_tensorHomComparisonHomotopy_app_shift.{u, v, w, t, s} X R K L k
  have := isKInjective_tensorWithComplexDG_obj_shift_regularModule.{u, v, w, t, s} X R K k
  have h₃ := isIso_derivedHomWithComplexOverUnit_app_of_isKInjective.{u, v, w, t, s} X R L
    ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj
      (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k))
  have h₄ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app P) :=
    isIso_tensorWithComplexDerivedCounit_app_of_leftOrthogonal _ _ _ hlo
  have hAux : IsIso ((tensorHomDGComparisonDerivedAux.{u, v, w, t, s} X R K L).app P) := by
    simp only [tensorHomDGComparisonDerivedAux, NatTrans.comp_app]
    exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso'
      (Functor.map_isIso (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R L).algebra).Q
        ((tensorHomDGComparisonHomotopy.{u, v, w, t, s} X R K L).app P)) h₃)
  rw [← tensorHomComparisonDerived_fac_app] at hAux
  have h₅ : IsIso ((derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L).map
      ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app P)) :=
    Functor.map_isIso _ _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R L).map
      ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app P)) h₅ hAux

end AlgebraicGeometry.RingedSite

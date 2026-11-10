module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRegularCounit
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRegularExt
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRepCohomology
public import StacksFrontier.CategoryTheory.Adjunction.Quotient
public import StacksFrontier.CategoryTheory.Adjunction.QuotientCounit
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithfulDevissage
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherent

/-!
# The endomorphism algebra of a K-injective complex computes its ext groups

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)`. If `K` is K-injective then `H^n(E) = Ext^n_{D(O)}(K, K)` for
every `n` (Tag 09MD). In the form hypothesis (2) of Tag 09LZ takes, it says that `- ⊗_E^𝐋 K` is
bijective on `Hom_{D(E, d)}(E, E[n])`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerived_adj_unit_app_regular_of_isIso`: the
  unit of the adjunction `- ⊗_E^𝐋 K ⊣ RHom(K, -)` of Tag 09LY is invertible at the regular module
  as soon as the comparison `Hom^•(K, -) → RHom(K, -)` is invertible at `K`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_bijective_map_regular_of_isIso`: the
  bijectivity of `- ⊗_E^𝐋 K` on `Hom_{D(E, d)}(E, E[n])` under the same hypothesis.

For `K` K-injective these are
`AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerived_adj_unit_app_repRegularDerived` and
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_map_bijective_of_isKInjective`
(`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRegularExt`), and Stacks 09MD itself
is
`AlgebraicGeometry.RingedSite.repCohomologyEquivDerivedHom`
(`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRepCohomology`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DifferentialGradedModule

universe u v w t s

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- The counit of the adjunction `- ⊗_E K ⊣ Hom^•(K, -)` on complexes is invertible at `K`. -/
theorem isIso_tensorWithComplexComplexes_adj_counit_app :
    IsIso ((tensorWithComplexComplexes_adj_homWithComplex.{u, v, w, t, s} X K).counit.app
      (liftComplex.{u, v, w, t, s} X K)) := by
  have h := isIso_tensorWithComplexDG_adjunction_counit_app.{u, v, w, t, s, 0} X ℤ K
  simp only [tensorWithComplexComplexes_adj_homWithComplex, Adjunction.comp_counit_app]
  refine IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ ?_) inferInstance
  exact IsIso.comp_isIso' inferInstance h

/-- The counit of the adjunction `- ⊗_E K ⊣ Hom^•(K, -)` on homotopy categories is invertible at
`K`. -/
theorem isIso_tensorWithComplexHomotopy_adj_counit_app :
    IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).counit.app
      ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))) := by
  have := isIso_tensorWithComplexComplexes_adj_counit_app.{u, v, w, t, s} X K
  exact Quotient.isIso_adjunctionOfSquares_counit_app _ _ _ _ _ _

/-- The unit of the adjunction `- ⊗_E K ⊣ Hom^•(K, -)` on homotopy categories is invertible at
`Hom^•(K, K)`: it is inverse to `Hom^•(K, -)` applied to the counit at `K`. -/
theorem isIso_tensorWithComplexHomotopy_adj_unit_app :
    IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).unit.app
      ((homWithComplexHomotopy.{u, v, w, t, s} X K).obj
        ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)))) := by
  have := isIso_tensorWithComplexHomotopy_adj_counit_app.{u, v, w, t, s} X K
  have h := (tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K
    ).right_triangle_components
      ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))
  have : IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).unit.app
      ((homWithComplexHomotopy.{u, v, w, t, s} X K).obj
        ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))) ≫
      (homWithComplexHomotopy.{u, v, w, t, s} X K).map
        ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).counit.app
          ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)))) := by
    rw [h]; exact IsIso.id _
  exact IsIso.of_isIso_comp_right _
    ((homWithComplexHomotopy.{u, v, w, t, s} X K).map
      ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).counit.app
        ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))))

/-- The comparison `Hom^•(K, -) → RHom(K, -)` is invertible at an object of `K(O)` into which the
localization functor `K(O) ⥤ D(O)` is bijective on morphisms. -/
theorem isIso_derivedHomWithComplexUnit_app_of_bijective
    (I : _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (hI : ∀ Z : _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ),
      Function.Bijective (DerivedCategory.Qh.map : (Z ⟶ I) → _)) :
    IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app I) := by
  have := Functor.hasPointwiseRightDerivedFunctor_of_coresolutions
    (L := DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplexToDerivedCategory.{u, v, w, t, s} X K)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  exact (Functor.LeftExtension.mk _ (derivedHomWithComplexUnit.{u, v, w, t, s} X K)
    ).isIso_hom_app_of_bijective
    (Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor _ _
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) _) hI

/-- The comparison `Hom^•(K, -) → RHom(K, -)` is invertible at a K-injective complex. -/
theorem isIso_derivedHomWithComplexUnit_app
    (I : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) [I.IsKInjective] :
    IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
      ((HomotopyCategory.quotient _ _).obj I)) :=
  isIso_derivedHomWithComplexUnit_app_of_bijective.{u, v, w, t, s} X K _
    fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z I

/-- **The unit of `- ⊗_E^𝐋 K ⊣ RHom(K, -)` is invertible at `Hom^•(K, K)`** as soon as the
comparison `Hom^•(K, -) → RHom(K, -)` is invertible at `K` itself. -/
theorem isIso_tensorWithComplexDerived_adj_unit_app_rep_of_isIso
    (hβK : IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
      ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)))) :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).unit.app
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
        ((homWithComplexHomotopy.{u, v, w, t, s} X K).obj
          ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))))) := by
  let adjH := tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K
  let R := (homWithComplexHomotopy.{u, v, w, t, s} X K).obj
    ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))
  let α : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⋙
        tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⟶
      tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙ DerivedCategory.Qh :=
    tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K
  let β : homWithComplexHomotopy.{u, v, w, t, s} X K ⋙
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⟶
      DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K :=
    derivedHomWithComplexUnit.{u, v, w, t, s} X K
  have hα : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).IsLeftDerivedFunctor α
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :=
    tensorWithComplexDerived_isLeftDerivedFunctor.{u, v, w, t, s, 0} X ℤ K
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q)
    (W := quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) α
    (derivedHomWithComplex.{u, v, w, t, s} X K)
    (exists_resolution_map_bijective_rep.{u, v, w, t, s} X K)
  have key := adjH.derivedη_fac_app (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) α β R
  change IsIso ((adjH.derivedη (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) α β).app
    ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj R))
  have hR : (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal R :=
    leftOrthogonal_acyclic_rep_self.{u, v, w, t, s} X K
  have : IsIso (α.app R) := isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K R hR
  have : IsIso (adjH.unit.app R) := isIso_tensorWithComplexHomotopy_adj_unit_app.{u, v, w, t, s} X K
  have hc := isIso_tensorWithComplexHomotopy_adj_counit_app.{u, v, w, t, s} X K
  have : IsIso (β.app ((tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K).obj R)) := by
    have hn := β.naturality (adjH.counit.app
      ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)))
    have : IsIso ((homWithComplexHomotopy.{u, v, w, t, s} X K ⋙
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).map (adjH.counit.app
          ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))) ≫
        β.app ((𝟭 _).obj ((HomotopyCategory.quotient _ _).obj
          (liftComplex.{u, v, w, t, s} X K)))) :=
      IsIso.comp_isIso' inferInstance hβK
    exact IsIso.of_isIso_fac_right hn.symm
  have : IsIso ((adjH.derivedη (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) α β).app
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj R) ≫
        (derivedHomWithComplex.{u, v, w, t, s} X K).map (α.app R)) := by
    rw [key]
    exact IsIso.comp_isIso' inferInstance inferInstance
  exact IsIso.of_isIso_comp_right _ ((derivedHomWithComplex.{u, v, w, t, s} X K).map (α.app R))

/-- **The unit of `- ⊗_E^𝐋 K ⊣ RHom(K, -)` is invertible at `Hom^•(K, K)`** when `K` is
K-injective. -/
theorem isIso_tensorWithComplexDerived_adj_unit_app_rep
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).unit.app
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
        ((homWithComplexHomotopy.{u, v, w, t, s} X K).obj
          ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))))) :=
  isIso_tensorWithComplexDerived_adj_unit_app_rep_of_isIso.{u, v, w, t, s} X K
    (isIso_derivedHomWithComplexUnit_app.{u, v, w, t, s} X K (liftComplex.{u, v, w, t, s} X K))

/-- **The unit of `- ⊗_E^𝐋 K ⊣ RHom(K, -)` is invertible at the regular module** `E` as soon as
the comparison `Hom^•(K, -) → RHom(K, -)` is invertible at `K`. -/
theorem isIso_tensorWithComplexDerived_adj_unit_app_regular_of_isIso
    (hβK : IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
      ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)))) :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).unit.app
      (repRegularDerived.{u, v, w, t, s} X K)) := by
  let eReg : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
        ((homWithComplexHomotopy.{u, v, w, t, s} X K).obj
          ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K))) ≅
      repRegularDerived.{u, v, w, t, s} X K :=
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.mapIso
      ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).mapIso
        DGCategory.representableSelfIsoRegular)
  have := isIso_tensorWithComplexDerived_adj_unit_app_rep_of_isIso.{u, v, w, t, s} X K hβK
  have hn :=
    (tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).unit.naturality
      eReg.hom
  have : IsIso ((𝟭 _).map eReg.hom ≫
      (tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).unit.app
        (repRegularDerived.{u, v, w, t, s} X K)) := by
    rw [hn]
    exact IsIso.comp_isIso' inferInstance inferInstance
  exact IsIso.of_isIso_comp_left ((𝟭 _).map eReg.hom) _

/-- **Hypothesis (2) of Tag 09LZ from the comparison at `K`.** If the comparison
`Hom^•(K, -) → RHom(K, -)` is invertible at `K`, the endomorphism differential graded algebra
`E = Hom^•(K, K)` computes the ext groups of `K`: the derived tensor product `- ⊗_E^𝐋 K` is
bijective on `Hom_{D(E, d)}(E, E[n])` for every `n`. -/
theorem tensorWithComplexDerived_bijective_map_regular_of_isIso
    (hβK : IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
      ((HomotopyCategory.quotient _ _).obj (liftComplex.{u, v, w, t, s} X K)))) (n : ℤ) :
    Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶ (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f) := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
  let := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have := isIso_tensorWithComplexDerived_adj_unit_app_regular_of_isIso.{u, v, w, t, s} X K hβK
  have hu : IsIso (adj.unit.app ((repRegularDerived.{u, v, w, t, s} X K)⟦n⟧)) := by
    rw [← Adjunction.unit_app_shift_commShiftIso_inv_app adj ℤ n]
    infer_instance
  refine (adj.bijective_comp_unit_app_iff _ _).1 ⟨fun a b h => ?_, fun b => ⟨b ≫
    inv (adj.unit.app ((repRegularDerived.{u, v, w, t, s} X K)⟦n⟧)), ?_⟩⟩
  · simpa using congrArg (· ≫ inv (adj.unit.app ((repRegularDerived.{u, v, w, t, s} X K)⟦n⟧))) h
  · simp

end AlgebraicGeometry.RingedSite

end

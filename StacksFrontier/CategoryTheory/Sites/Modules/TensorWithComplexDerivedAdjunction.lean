module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Adjunction.Quotient
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparison
public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# The derived tensor--Hom adjunction for a complex of modules on a ringed site

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The derived
tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX is left adjoint to derived Hom
`RHom(K^•, -) : D(O) ⥤ D(E, d)`.

## Main definitions

* `CochainComplex.cochainCompEquivalence`: the category of complexes of the differential graded
  category of cochain complexes in `B` is equivalent to the category of cochain complexes in `B`.
* `AlgebraicGeometry.RingedSite.homWithComplex`: `Hom^•(K, -)` as a functor
  `Comp(O) ⥤ Mod_(E, d)`, the representable differential graded functor of Tag 09LE read on
  closed degree-zero morphisms.
* `AlgebraicGeometry.RingedSite.homWithComplexHomotopy`: the same on homotopy categories,
  `K(O) ⥤ K(Mod_(E, d))`.
* `AlgebraicGeometry.RingedSite.homWithComplexToDerivedCategory`: that functor followed by
  localization of the target, `K(O) ⥤ D(E, d)`, which is the functor being right derived.
* `AlgebraicGeometry.RingedSite.derivedHomWithComplex`: derived Hom
  `RHom(K^•, -) : D(O) ⥤ D(E, d)`, together with its comparison
  `AlgebraicGeometry.RingedSite.derivedHomWithComplexUnit`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexComplexes_adj_homWithComplex` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_adj_homWithComplexHomotopy`: the
  adjunction on complexes and on homotopy categories.
* `AlgebraicGeometry.RingedSite.homWithComplexToDerivedCategory_hasRightDerivedFunctor`: derived
  Hom out of `K` is defined on all of `D(O)`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplex`:
  **Stacks 09LY**, the adjunction `- ⊗_E^𝐋 K^• ⊣ RHom(K^•, -)` between the derived categories.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedPreservesCoproducts`: the derived tensor
  product commutes with all small direct sums, being a left adjoint.

## References

* [Stacks Project, Tag 09LY](https://stacks.math.columbia.edu/tag/09LY)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
* [Stacks Project, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

universe i u v w t s

namespace CochainComplex

variable (B : Type u) [Category.{v} B] [Preadditive B]

/-- The category of complexes of the differential graded category of complexes in `B` is
isomorphic to the ordinary category of cochain complexes in `B`: both functors are the identity
on objects and pass between a closed degree-zero cochain and the chain map it is. -/
def cochainCompEquivalence : (CochainComplex.dgCategory B).Comp ≌ CochainComplex B ℤ where
  functor := CochainComplex.complexesToCochainFunctor B
  inverse := CochainComplex.cochainToComplexFunctor B
  unitIso := NatIso.ofComponents (fun P => Iso.refl P) (fun {P Q} f =>
    show f ≫ 𝟙 Q = 𝟙 P ≫ Cocycle.ofHom (Cocycle.homOf f) from
      (Category.comp_id f).trans
        ((Cocycle.ofHom_homOf_eq_self f).symm.trans
          (Category.id_comp (show P ⟶ Q from Cocycle.ofHom (Cocycle.homOf f))).symm))
  counitIso := NatIso.ofComponents (fun P => Iso.refl P) (fun {P Q} f =>
    show Cocycle.homOf (Cocycle.ofHom f) ≫ 𝟙 Q = 𝟙 P ≫ f from
      (Category.comp_id _).trans
        ((Cocycle.homOf_ofHom_eq_self f).trans (Category.id_comp f).symm))
  functor_unitIso_comp := fun P =>
    show (CochainComplex.complexesToCochainFunctor B).map (𝟙 P) ≫ 𝟙 _ = 𝟙 _ from
      (Category.comp_id _).trans ((CochainComplex.complexesToCochainFunctor B).map_id P)

end CochainComplex

namespace AlgebraicGeometry.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-! ### Hom out of `K`, on complexes and on homotopy categories -/

/-- `Hom^•(K, -)` as an ordinary functor from the cochain complexes of `O`-modules to the
differential graded modules over the endomorphism algebra of `K`: the representable differential
graded functor of Tag 09LE, read on closed degree-zero morphisms. -/
def homWithComplex :
    CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ ⥤
      DifferentialGradedModule (Rep.{u, v, w, t, s, 0} X ℤ K).algebra :=
  CochainComplex.cochainToComplexFunctor _ ⋙ (Rep.{u, v, w, t, s, 0} X ℤ K).complexesFunctor

/-- **Tensoring with `K` is left adjoint to `Hom^•(K, -)` on complexes.** This is the
differential graded adjunction of Tag 09LV, read on closed degree-zero morphisms through the
identifications of Tag 09LC of the two categories of complexes with the ordinary categories of
differential graded modules and of cochain complexes. -/
def tensorWithComplexComplexes_adj_homWithComplex :
    DifferentialGradedModule.dgFunctorToComplexes
        (tensorWithComplexDG.{u, v, w, t, s, 0} X ℤ K).functor ⊣
      homWithComplex.{u, v, w, t, s} X K :=
  (((DifferentialGradedModule.compModulesEquivalence
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).symm.toAdjunction :
      DifferentialGradedModule.modulesToComp (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⊣
        DifferentialGradedModule.compToModules (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).comp
    (tensorWithComplexDG.{u, v, w, t, s, 0} X ℤ K).adjunction).comp
    ((CochainComplex.cochainCompEquivalence
        (TensorModO.{u, v, w, t, s} X)).toAdjunction :
      CochainComplex.complexesToCochainFunctor (TensorModO.{u, v, w, t, s} X) ⊣
        CochainComplex.cochainToComplexFunctor (TensorModO.{u, v, w, t, s} X))

/-- Homotopic chain maps of `O`-modules have homotopic images under `Hom^•(K, -)`. -/
theorem homWithComplex_homotopic {Y Z : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ}
    {f g : Y ⟶ Z} (h : _root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) f g) :
    DifferentialGradedModule.homotopyRel (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
      ((homWithComplex.{u, v, w, t, s} X K).map f)
      ((homWithComplex.{u, v, w, t, s} X K).map g) := by
  obtain ⟨H⟩ := h
  have hdg : (CompDG.{u, v, w, t, s, 0} X ℤ).Homotopic (Cocycle.ofHom f) (Cocycle.ofHom g) := by
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g H
    exact ⟨z, (sub_eq_iff_eq_add).2 hz⟩
  have hmk : (Quotient.mk _ ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.mapCocycle (Cocycle.ofHom f)) :
        (dgCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).HomotopyClass _ _) =
      Quotient.mk _ ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.mapCocycle (Cocycle.ofHom g)) :=
    congrArg (Rep.{u, v, w, t, s, 0} X ℤ K).functor.mapHomotopyClass (Quotient.sound hdg)
  exact DifferentialGradedModule.homOfCocycle_homotopic _ (Quotient.exact hmk)

/-- `Hom^•(K, -)` followed by the passage to homotopy classes identifies homotopic chain maps. -/
theorem homWithComplex_toHomotopyCategory_descends
    (Y Z : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) (f g : Y ⟶ Z)
    (h : _root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) f g) :
    (homWithComplex.{u, v, w, t, s} X K ⋙
        DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).map f =
      (homWithComplex.{u, v, w, t, s} X K ⋙
        DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).map g :=
  CategoryTheory.Quotient.sound
    (DifferentialGradedModule.homotopyRel (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (homWithComplex_homotopic.{u, v, w, t, s} X K h)

/-- `Hom^•(K, -)` on the homotopy categories, `K(O) ⥤ K(Mod_(E, d))`: the functor on complexes,
descended along the passage to homotopy classes. -/
def homWithComplexHomotopy :
    _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) ⥤
      DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra :=
  CategoryTheory.Quotient.lift
    (_root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplex.{u, v, w, t, s} X K ⋙
      DifferentialGradedModule.toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (homWithComplex_toHomotopyCategory_descends.{u, v, w, t, s} X K)

/-- **Tensoring with `K` is left adjoint to `Hom^•(K, -)` on the homotopy categories**, as
functors `K(Mod_(E, d)) ⥤ K(O)` and `K(O) ⥤ K(Mod_(E, d))`: the adjunction on complexes,
descended to the two quotient categories. -/
def tensorWithComplexHomotopy_adj_homWithComplexHomotopy :
    tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⊣
      homWithComplexHomotopy.{u, v, w, t, s} X K :=
  CategoryTheory.Quotient.adjunctionOfSquares
    (DifferentialGradedModule.homotopyRel (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (_root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (tensorWithComplexComplexes_adj_homWithComplex.{u, v, w, t, s} X K)
    (eqToIso (tensorWithComplexHomotopy_spec.{u, v, w, t, s, 0} X ℤ K).symm)
    (eqToIso (CategoryTheory.Quotient.lift_spec
      (_root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
      (homWithComplex.{u, v, w, t, s} X K ⋙
        DifferentialGradedModule.toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      (homWithComplex_toHomotopyCategory_descends.{u, v, w, t, s} X K)).symm)

/-! ### Derived Hom out of `K` -/

/-- `Hom^•(K, -)` on the homotopy category, followed by localization of the target: the functor
`K(O) ⥤ D(E, d)` whose right derived functor is derived Hom out of `K`. -/
def homWithComplexToDerivedCategory :
    _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) ⥤
      DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra :=
  homWithComplexHomotopy.{u, v, w, t, s} X K ⋙
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q

/-- Every object of `K(O)` admits a quasi-isomorphism into an object into which the localization
functor `Qh` is bijective on morphisms, namely a K-injective resolution (Tag 079P). -/
theorem exists_coresolution_map_bijective_sheaf
    (Y : _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) :
    ∃ (I : _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
      (f : Y ⟶ I),
      HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) f ∧
      ∀ Z : _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ),
        Function.Bijective (DerivedCategory.Qh.map : (Z ⟶ I) → _) := by
  let _ : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} _ _
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  refine ⟨(HomotopyCategory.quotient _ _).obj
      ((Stacks.Injectives.kInjectiveResolutionFunctor
        (TensorModO.{u, v, w, t, s} X)).obj M),
    (HomotopyCategory.quotient _ _).map
      ((Stacks.Injectives.kInjectiveResolutionInclusion
        (TensorModO.{u, v, w, t, s} X)).app M),
    ?_, fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z _⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
    ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)

/-- **Derived Hom out of `K` exists on all of `D(O)`**: the functor `K(O) ⥤ D(E, d)` has a total
right derived functor. -/
theorem homWithComplexToDerivedCategory_hasRightDerivedFunctor :
    (homWithComplexToDerivedCategory.{u, v, w, t, s} X K).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) := by
  have := Functor.hasPointwiseRightDerivedFunctor_of_coresolutions
    (L := DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplexToDerivedCategory.{u, v, w, t, s} X K)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  infer_instance

/-- **Derived Hom out of `K`**, `RHom(K^•, -) : D(O) ⥤ D(E, d)`: the total right derived functor
of `Hom^•(K, -)` on the homotopy category followed by localization of the target. -/
def derivedHomWithComplex :
    DerivedCategory (TensorModO.{u, v, w, t, s} X) ⥤
      DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra := by
  let _ := homWithComplexToDerivedCategory_hasRightDerivedFunctor.{u, v, w, t, s} X K
  exact (homWithComplexToDerivedCategory.{u, v, w, t, s} X K).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))

/-- The canonical comparison from `Hom^•(K, -)` to its derived functor: the unit of the Kan
extension defining `RHom(K^•, -)`. -/
def derivedHomWithComplexUnit :
    homWithComplexToDerivedCategory.{u, v, w, t, s} X K ⟶
      DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K := by
  let _ := homWithComplexToDerivedCategory_hasRightDerivedFunctor.{u, v, w, t, s} X K
  exact (homWithComplexToDerivedCategory.{u, v, w, t, s} X K).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))

/-- The comparison exhibits `RHom(K^•, -)` as the right derived functor of `Hom^•(K, -)`
followed by localization of the target. -/
instance derivedHomWithComplex_isRightDerivedFunctor :
    (derivedHomWithComplex.{u, v, w, t, s} X K).IsRightDerivedFunctor
      (derivedHomWithComplexUnit.{u, v, w, t, s} X K)
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) := by
  let _ := homWithComplexToDerivedCategory_hasRightDerivedFunctor.{u, v, w, t, s} X K
  change ((homWithComplexToDerivedCategory.{u, v, w, t, s} X K).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X)
      (ComplexShape.up ℤ))).IsRightDerivedFunctor
    ((homWithComplexToDerivedCategory.{u, v, w, t, s} X K).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
  infer_instance

/-- Every object of `K(Mod_(E, d))` receives a quasi-isomorphism from an object out of which the
localization functor is bijective on morphisms, namely a resolution by a module with
property (P). -/
theorem exists_resolution_map_bijective_rep
    (Y : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :
    ∃ (P : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) (f : P ⟶ Y),
      quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra f ∧
      ∀ Z : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra,
        Function.Bijective
          ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.map : (P ⟶ Z) → _) := by
  obtain ⟨P, f, hf, hP⟩ := exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, 0} X ℤ K Y
  rw [← acyclic_trW_eq_quasiIsomorphisms]
  exact ⟨P, f, hf, fun Z => hP.map_bijective_of_isTriangulated _ Z⟩

/-! ### Stacks 09LY -/

/-- **The derived tensor--Hom adjunction**: the derived tensor product
`- ⊗_E^𝐋 K^• : D(E, d) ⥤ D(O)` of Tag 09LX is left adjoint to derived Hom
`RHom(K^•, -) : D(O) ⥤ D(E, d)`. -/
@[stacks 09LY]
def tensorWithComplexDerived_adj_derivedHomWithComplex :
    tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⊣
      derivedHomWithComplex.{u, v, w, t, s} X K := by
  have hα : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).IsLeftDerivedFunctor
      (show (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⋙
            tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⟶
          tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙ DerivedCategory.Qh from
        tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :=
    tensorWithComplexDerived_isLeftDerivedFunctor.{u, v, w, t, s, 0} X ℤ K
  have hβ : (derivedHomWithComplex.{u, v, w, t, s} X K).IsRightDerivedFunctor
      (show homWithComplexHomotopy.{u, v, w, t, s} X K ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⟶
          DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K from
        derivedHomWithComplexUnit.{u, v, w, t, s} X K)
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) :=
    derivedHomWithComplex_isRightDerivedFunctor.{u, v, w, t, s} X K
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q)
    (W := quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K)
    (derivedHomWithComplex.{u, v, w, t, s} X K)
    (exists_resolution_map_bijective_rep.{u, v, w, t, s} X K)
  have hright := Functor.isRightDerivedFunctor_comp_of_coresolutions
    (L := DerivedCategory.Qh)
    (W := HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (show homWithComplexHomotopy.{u, v, w, t, s} X K ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⟶
        DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K from
      derivedHomWithComplexUnit.{u, v, w, t, s} X K)
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  exact (tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).derived
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K)
    (show homWithComplexHomotopy.{u, v, w, t, s} X K ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⟶
        DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K from
      derivedHomWithComplexUnit.{u, v, w, t, s} X K)

/-- **The derived tensor product with `K` commutes with all small direct sums.** -/
instance tensorWithComplexDerivedPreservesCoproducts (I : Type i) :
    Limits.PreservesColimitsOfShape (Discrete I)
      (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K) :=
  ((tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
    ).leftAdjoint_preservesColimits).preservesColimitsOfShape

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedAdjunction

/-!
# The derived tensor--Hom adjunction over the source's base ring

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O` (an `AlgebraicGeometry.RingedSite.ScalarSections` instance), let `K`
be a complex of `O`-modules and let `(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism
differential graded `R`-algebra. The derived tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of
Tag 09LX is formed over `R` in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived`; this file constructs its right
adjoint `RHom(K^•, -) : D(O) ⥤ D(E, d)` over `R` and the adjunction of Tag 09LY between them.

`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedAdjunction` carries out the same
construction for the base ring `ℤ`; the argument is that one, read over `R`. The only ingredient
which is not already stated over an arbitrary base ring is the identification of the category of
complexes of the differential graded category `Comp^dg(O)` with the cochain complexes of
`O`-modules, which is `CochainComplex.cochainCompEquivalenceLinear` below: the `R`-linear
differential graded category `CochainComplex.dgCategoryLinear` has literally the objects,
morphisms, differential and composition of the `ℤ`-linear one.

## Main definitions

* `AlgebraicGeometry.RingedSite.homWithComplexOver`: `Hom^•(K, -) : Comp(O) ⥤ Mod_(E, d)`.
* `AlgebraicGeometry.RingedSite.homWithComplexHomotopyOver`: the same on homotopy categories.
* `AlgebraicGeometry.RingedSite.derivedHomWithComplexOver`: `RHom(K^•, -) : D(O) ⥤ D(E, d)`,
  with its comparison `AlgebraicGeometry.RingedSite.derivedHomWithComplexUnitOver`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplexOver`:
  **Stacks 09LY** over `R`, the adjunction `- ⊗_E^𝐋 K^• ⊣ RHom(K^•, -)`.

## References

* [Stacks Project, Tag 09LY](https://stacks.math.columbia.edu/tag/09LY)
* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

universe i u v w t s o

namespace CochainComplex

variable (B : Type u) [Category.{v} B] [Preadditive B] (R : Type o) [CommRing R] [Linear R B]

/-- `CochainComplex.cochainToComplexFunctor`, read in the `R`-linear differential graded category
of complexes, which has the same objects and closed degree-zero morphisms. -/
def cochainToComplexFunctorLinear : CochainComplex B ℤ ⥤ (dgCategoryLinear B R).Comp :=
  cochainToComplexFunctor B

/-- `CochainComplex.complexesToCochainFunctor`, read in the `R`-linear differential graded
category of complexes. -/
def complexesToCochainFunctorLinear : (dgCategoryLinear B R).Comp ⥤ CochainComplex B ℤ :=
  complexesToCochainFunctor B

/-- The category of complexes of the `R`-linear differential graded category of complexes in `B`
is isomorphic to the ordinary category of cochain complexes in `B`. -/
def cochainCompEquivalenceLinear : (dgCategoryLinear B R).Comp ≌ CochainComplex B ℤ :=
  cochainCompEquivalence B

end CochainComplex

namespace AlgebraicGeometry.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

/-! ### Hom out of `K`, on complexes and on homotopy categories -/

/-- `Hom^•(K, -)` as an ordinary functor from the cochain complexes of `O`-modules to the
differential graded modules over the endomorphism algebra of `K`: the representable differential
graded functor of Tag 09LE, read on closed degree-zero morphisms. -/
def homWithComplexOver :
    CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ ⥤
      DifferentialGradedModule (Rep.{u, v, w, t, s, o} X R K).algebra :=
  CochainComplex.cochainToComplexFunctorLinear _ R ⋙ (Rep.{u, v, w, t, s, o} X R K).complexesFunctor

/-- **Tensoring with `K` is left adjoint to `Hom^•(K, -)` on complexes.** This is the
differential graded adjunction of Tag 09LV, read on closed degree-zero morphisms through the
identifications of Tag 09LC of the two categories of complexes with the ordinary categories of
differential graded modules and of cochain complexes. -/
def tensorWithComplexComplexes_adj_homWithComplexOver :
    DifferentialGradedModule.dgFunctorToComplexes
        (tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor ⊣
      homWithComplexOver.{u, v, w, t, s, o} X R K :=
  (((DifferentialGradedModule.compModulesEquivalence
        (Rep.{u, v, w, t, s, o} X R K).algebra).symm.toAdjunction :
      DifferentialGradedModule.modulesToComp (Rep.{u, v, w, t, s, o} X R K).algebra ⊣
        DifferentialGradedModule.compToModules (Rep.{u, v, w, t, s, o} X R K).algebra).comp
    (tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction).comp
    ((CochainComplex.cochainCompEquivalenceLinear
        (TensorModO.{u, v, w, t, s} X) R).toAdjunction :
      CochainComplex.complexesToCochainFunctorLinear (TensorModO.{u, v, w, t, s} X) R ⊣
        CochainComplex.cochainToComplexFunctorLinear (TensorModO.{u, v, w, t, s} X) R)

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Homotopic chain maps of `O`-modules have homotopic images under `Hom^•(K, -)`: a homotopy of
chain maps is a degree `-1` cochain whose differential is their difference, the differential
graded functor `Hom^•(K, -)` carries it to such a cochain over the endomorphism algebra, and that
is a homotopy of homomorphisms of differential graded modules. -/
theorem homWithComplex_homotopicOver {Y Z : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ}
    {f g : Y ⟶ Z} (h : _root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) f g) :
    DifferentialGradedModule.homotopyRel (Rep.{u, v, w, t, s, o} X R K).algebra
      ((homWithComplexOver.{u, v, w, t, s, o} X R K).map f)
      ((homWithComplexOver.{u, v, w, t, s, o} X R K).map g) := by
  obtain ⟨H⟩ := h
  have hdg : (CompDG.{u, v, w, t, s, o} X R).Homotopic (Cocycle.ofHom f) (Cocycle.ofHom g) := by
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g H
    exact ⟨z, (sub_eq_iff_eq_add).2 hz⟩
  have hmk : (Quotient.mk _ ((Rep.{u, v, w, t, s, o} X R K).functor.mapCocycle (Cocycle.ofHom f)) :
        (dgCategory (Rep.{u, v, w, t, s, o} X R K).algebra).HomotopyClass _ _) =
      Quotient.mk _ ((Rep.{u, v, w, t, s, o} X R K).functor.mapCocycle (Cocycle.ofHom g)) :=
    congrArg (Rep.{u, v, w, t, s, o} X R K).functor.mapHomotopyClass (Quotient.sound hdg)
  exact DifferentialGradedModule.homOfCocycle_homotopic _ (Quotient.exact hmk)

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- `Hom^•(K, -)` followed by the passage to homotopy classes identifies homotopic chain maps,
which is what lets it be lifted to the homotopy category of `O`-modules. -/
theorem homWithComplex_toHomotopyCategory_descendsOver
    (Y Z : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) (f g : Y ⟶ Z)
    (h : _root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) f g) :
    (homWithComplexOver.{u, v, w, t, s, o} X R K ⋙
        DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, v, w, t, s, o} X R K).algebra).map f =
      (homWithComplexOver.{u, v, w, t, s, o} X R K ⋙
        DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, v, w, t, s, o} X R K).algebra).map g :=
  CategoryTheory.Quotient.sound
    (DifferentialGradedModule.homotopyRel (Rep.{u, v, w, t, s, o} X R K).algebra)
    (homWithComplex_homotopicOver.{u, v, w, t, s, o} X R K h)

/-- `Hom^•(K, -)` on the homotopy categories, `K(O) ⥤ K(Mod_(E, d))`: the functor on complexes,
descended along the passage to homotopy classes. -/
def homWithComplexHomotopyOver :
    _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) ⥤
      DifferentialGradedModule.HomotopyCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra :=
  CategoryTheory.Quotient.lift
    (_root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplexOver.{u, v, w, t, s, o} X R K ⋙
      DifferentialGradedModule.toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra)
    (homWithComplex_toHomotopyCategory_descendsOver.{u, v, w, t, s, o} X R K)

/-- **Tensoring with `K` is left adjoint to `Hom^•(K, -)` on the homotopy categories**, as
functors `K(Mod_(E, d)) ⥤ K(O)` and `K(O) ⥤ K(Mod_(E, d))`. This is the adjunction on complexes,
descended to the two quotient categories; both functors are the canonical descents, so no
comparison isomorphism intervenes. -/
def tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver :
    tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⊣
      homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K :=
  CategoryTheory.Quotient.adjunctionOfSquares
    (DifferentialGradedModule.homotopyRel (Rep.{u, v, w, t, s, o} X R K).algebra)
    (_root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (tensorWithComplexComplexes_adj_homWithComplexOver.{u, v, w, t, s, o} X R K)
    (eqToIso (tensorWithComplexHomotopy_spec.{u, v, w, t, s, o} X R K).symm)
    (eqToIso (CategoryTheory.Quotient.lift_spec
      (_root_.homotopic (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
      (homWithComplexOver.{u, v, w, t, s, o} X R K ⋙
        DifferentialGradedModule.toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra)
      (homWithComplex_toHomotopyCategory_descendsOver.{u, v, w, t, s, o} X R K)).symm)

/-! ### Derived Hom out of `K` -/

/-- `Hom^•(K, -)` on the homotopy category, followed by localization of the target: the functor
`K(O) ⥤ D(E, d)` whose right derived functor is derived Hom out of `K`. -/
def homWithComplexToDerivedCategoryOver :
    _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) ⥤
      DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, o} X R K).algebra :=
  homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K ⋙
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- **Derived Hom out of `K` exists on all of `D(O)`.** The functor `K(O) ⥤ D(E, d)` has a total
right derived functor, by the criterion of Tag 06XN applied to the K-injective resolutions of
Tag 079P. -/
theorem homWithComplexToDerivedCategory_hasRightDerivedFunctorOver :
    (homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) := by
  have := Functor.hasPointwiseRightDerivedFunctor_of_coresolutions
    (L := DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  exact (homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K
    |>.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _)

/-- **Derived Hom out of `K`**, `RHom(K^•, -) : D(O) ⥤ D(E, d)`: the total right derived functor
of `Hom^•(K, -)` on the homotopy category followed by localization of the target. -/
def derivedHomWithComplexOver :
    DerivedCategory (TensorModO.{u, v, w, t, s} X) ⥤
      DifferentialGradedModule.derivedCategory (Rep.{u, v, w, t, s, o} X R K).algebra := by
  let _ := homWithComplexToDerivedCategory_hasRightDerivedFunctorOver.{u, v, w, t, s, o} X R K
  exact (homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))

/-- The canonical comparison from `Hom^•(K, -)` to its derived functor: the unit of the Kan
extension defining `RHom(K^•, -)`. -/
def derivedHomWithComplexUnitOver :
    homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K ⟶
      DerivedCategory.Qh ⋙ derivedHomWithComplexOver.{u, v, w, t, s, o} X R K := by
  let _ := homWithComplexToDerivedCategory_hasRightDerivedFunctorOver.{u, v, w, t, s, o} X R K
  exact (homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))

/-- The comparison exhibits `RHom(K^•, -)` as the right derived functor of `Hom^•(K, -)`
followed by localization of the target. -/
instance derivedHomWithComplex_isRightDerivedFunctorOver :
    (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).IsRightDerivedFunctor
      (derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K)
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) := by
  let _ := homWithComplexToDerivedCategory_hasRightDerivedFunctorOver.{u, v, w, t, s, o} X R K
  change ((homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X)
      (ComplexShape.up ℤ))).IsRightDerivedFunctor
    ((homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
  infer_instance

/-! ### Stacks 09LY -/

/-- **Stacks 09LY.** The derived tensor product `- ⊗_E^𝐋 K^• : D(E, d) ⥤ D(O)` of Tag 09LX is a
left adjoint of derived Hom `RHom(K^•, -) : D(O) ⥤ D(E, d)`.

The deduction is Mathlib's `CategoryTheory.Adjunction.derived` applied to the adjunction on the
homotopy categories, whose absoluteness hypotheses are discharged from the two supplies of
resolutions: the modules with property (P) on the left and the K-injective complexes of
`O`-modules on the right. -/
def tensorWithComplexDerived_adj_derivedHomWithComplexOver :
    tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⊣
      derivedHomWithComplexOver.{u, v, w, t, s, o} X R K := by
  -- `tensorWithComplexToDerivedCategory` and `homWithComplexToDerivedCategoryOver` are plain
  -- `def`s, so instance search does not see the composites `G ⋙ Qh` and `F ⋙ Q` that
  -- `CategoryTheory.Adjunction.derived` asks for. Ascribing the two comparison maps — which is
  -- checked at default transparency — records the derived-functor instances at the spelling the
  -- final application needs.
  have hα : (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).IsLeftDerivedFunctor
      (show (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
            tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⟶
          tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙ DerivedCategory.Qh from
        tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) :=
    tensorWithComplexDerived_isLeftDerivedFunctor.{u, v, w, t, s, o} X R K
  have hβ : (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).IsRightDerivedFunctor
      (show homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⟶
          DerivedCategory.Qh ⋙ derivedHomWithComplexOver.{u, v, w, t, s, o} X R K from
        derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K)
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) :=
    derivedHomWithComplex_isRightDerivedFunctorOver.{u, v, w, t, s, o} X R K
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q)
    (W := quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K)
    (exists_resolution_q_map_bijective_rep.{u, v, w, t, s, o} X R K)
  have hright := Functor.isRightDerivedFunctor_comp_of_coresolutions
    (L := DerivedCategory.Qh)
    (W := HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (show homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⟶
        DerivedCategory.Qh ⋙ derivedHomWithComplexOver.{u, v, w, t, s, o} X R K from
      derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K)
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  exact (tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K).derived
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (show homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⟶
        DerivedCategory.Qh ⋙ derivedHomWithComplexOver.{u, v, w, t, s, o} X R K from
      derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K)

/-- **The derived tensor product with `K` commutes with all small direct sums.** It is a left
adjoint by Tag 09LY, and a left adjoint preserves every colimit.

This is the form in which Tag 09LY feeds the dévissage of Tag 0FQE: the dévissage criterion
`Stacks.DerivedQCoh.derivedQuasicoherent_of_regular` asks for preservation of the coproducts
indexed by each type, and there is no route to it for a total left derived functor other than
exhibiting it as a left adjoint. Compare
`AlgebraicGeometry.RingedSite.tensorWithComplexDG_preservesCoproducts`, which is the same
statement for the underived differential graded tensor functor. -/
instance tensorWithComplexDerivedPreservesCoproductsOver (I : Type i) :
    Limits.PreservesColimitsOfShape (Discrete I)
      (tensorWithComplexDerived.{u, v, w, t, s, o} X R K) :=
  ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o} X R K
    ).leftAdjoint_preservesColimits).preservesColimitsOfShape

end AlgebraicGeometry.RingedSite

end

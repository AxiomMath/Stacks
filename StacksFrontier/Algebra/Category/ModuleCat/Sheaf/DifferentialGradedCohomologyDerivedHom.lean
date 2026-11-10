module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitAlgebraHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodResolutionDataConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensorUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedHomRegular
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsomorphisms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveExistence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftCompatibility
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFunctor

/-!
# Cohomology of a differential graded module as morphisms in `D(A, d)`

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras, let `M` be
a right differential graded `A`-module and let `n` be an integer. This file proves Tag 0FTX:

`H^n(C, M) = Hom_{D(A, d)}(A, M[n])`,

where on the left `M` is viewed as a complex of `O`-modules.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.cohomology`: `H^n(C, M)`, the `n`-th cohomology of
  the derived global sections of the underlying complex of `M`.
* `SheafOfModules.DifferentialGradedModule.cohomologyAddEquivDerivedHom`: **Tag 0FTX**, the
  identification `H^n(C, M) ≃+ Hom_{D(A, d)}(A, M[n])`.
* `SheafOfModules.DifferentialGradedModule.structureExtension`: extension of scalars
  `- ⊗_{(O, 0)} A` along the unit `(O, 0) ⟶ A`, left adjoint to restriction of scalars.
* `SheafOfModules.DifferentialGradedModule.structureExtensionRegularIso`: the isomorphism
  `(O, 0) ⊗_{(O, 0)} A ≅ A` of right differential graded `A`-modules.
* `SheafOfModules.DifferentialGradedModule.regularHomotopyHomAddEquiv`: morphisms `A ⟶ N` of
  `K(Mod(A, d))` are morphisms `O ⟶ N` of complexes of `O`-modules up to homotopy.
* `SheafOfModules.DifferentialGradedModule.complexCohomologyAddEquiv`: for a complex `K` of
  `O`-modules, `H^n(C, K) ≃+ Hom_{D(O)}(O, K[n])`.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIso_structureExtension_map`: the tensor product
  with `A` carries a quasi-isomorphism between flat and K-flat right differential graded
  `(O, 0)`-modules to a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.bijective_precomp_structureRestriction`: such a
  quasi-isomorphism induces a bijection on homotopy classes of morphisms into the restriction of
  a graded injective and K-injective right differential graded `A`-module.
* `SheafOfModules.DifferentialGradedModule.bijective_Qh_map_unitComplex`: for a graded
  injective and K-injective right differential graded `A`-module `I`, the localization functor
  `K(O) ⥤ D(O)` is bijective on morphisms `O ⟶ I`.

## Implementation notes

The source computes `RΓ(C, M)` as `Γ(C, I)` for a quasi-isomorphism `M ⟶ I` into a graded
injective and K-injective module, by Tags 0FTN and 0FTW. The underlying complex of `I` need not
be K-injective, so this is proved here directly in the only form needed: morphisms `O ⟶ I` of
the homotopy category of complexes of `O`-modules are morphisms of `D(O)`. A morphism of `D(O)`
is a fraction with a quasi-isomorphism `P ⟶ O`; refining `P` to a flat and K-flat right
differential graded `(O, 0)`-module (Tag 0FSH), its tensor product with `A` is a
quasi-isomorphism onto `A`, by clause (1) of Tag 0FSI applied to its cone, and the adjunction of
Tag 0FRP turns morphisms out of `P` into the restriction of `I` into morphisms out of `P ⊗ A`
into `I`, where Tag 0FSX applies.

The chain of identifications is then: `H^n(C, M) = Hom_{D(O)}(O, M[n])` on a K-injective
resolution in `D(O)` (Tag 0A94), `M[n] ⟶ I` for a graded injective and K-injective resolution
(Tag 0FT0), the bijectivity above, restriction along the unit `O ⟶ A`, and Tag 0FT8.

The algebra `A` of the main statement is over `AlgebraicGeometry.RingedSite.ringSheaf`, as in
the rest of the development; the construction works over `toRingCat X.J X.O`, the same sheaf of
rings, over which `(O, 0)` (`SheafOfModules.unitDGAlgebra`) is built.

## References

* [Stacks Project, Tag 0FTX](https://stacks.math.columbia.edu/tag/0FTX)
* [Stacks Project, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)
* [Stacks Project, Tag 0FT8](https://stacks.math.columbia.edu/tag/0FT8)
* [Stacks Project, Tag 0FSX](https://stacks.math.columbia.edu/tag/0FSX)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

namespace SheafOfModules

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J (Type u)]
  (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))

/-- The tensor product `- ⊗_{(O, 0)} A` along the unit `(O, 0) ⟶ A`. -/
noncomputable abbrev structureExtensionData :=
  RelativeTensor.tensorFunctorDataDgTensorRight
    ((unitAlgebraHom A).toBimodule (unitAlgebraHom_preservesOne A))

/-- Extension of scalars along the unit `(O, 0) ⟶ A`. -/
noncomputable abbrev structureExtension :
    DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O) ⥤
      DifferentialGradedModule.{u, u, u} A :=
  (structureExtensionData A).functor

/-- Restriction of scalars along the unit `(O, 0) ⟶ A`: the underlying complex of `O`-modules,
as a right differential graded `(O, 0)`-module. -/
noncomputable abbrev structureRestriction :
    DifferentialGradedModule.{u, u, u} A ⥤
      DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O) :=
  restriction.{u, u, u} (unitAlgebraHom A) (unitAlgebraHom_preservesOne A)

/-- Extension of scalars along the unit `(O, 0) ⟶ A` is left adjoint to restriction. -/
noncomputable abbrev structureAdjunction : structureExtension A ⊣ structureRestriction A :=
  extensionRestrictionAdjunction (unitAlgebraHom A) (unitAlgebraHom_preservesOne A)
    (structureExtensionData A)

/-- **The tensor product with `A` over `(O, 0)` carries a quasi-isomorphism between flat and
K-flat modules to a quasi-isomorphism.** The cone is flat, K-flat and acyclic, so its tensor
product with `A` is acyclic (Tag 0FSI, clause (1)), and that is the cone of the tensored
homomorphism. -/
theorem quasiIso_structureExtension_map
    {P Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (s : P ⟶ Q)
    (hP : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P)
    (hQ : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
      RelativeTensor.IsKFlat Q)
    (hs : QuasiIso s.toHomologicalComplex) :
    QuasiIso ((structureExtension A).map s).toHomologicalComplex := by
  have hc := isGradedFlat_and_isKFlat_cone s hP hQ
  have hac : (cone s).complex.Acyclic := (acyclic_cone_iff_quasiIso _ s).2 hs
  have hE : ((structureExtension A).obj (cone s)).complex.Acyclic :=
    acyclic_of_isTensorProduct_of_isKFlat_of_acyclic hc.2 hac
      ((structureExtensionData A).isTensorProduct (cone s))
  have hcone : (cone ((structureExtension A).map s)).complex.Acyclic := fun i =>
    (hE i).of_iso ((structureExtensionData A).coneComplexIso s).symm
  exact (acyclic_cone_iff_quasiIso _ _).1 hcone

/-- The adjunction `- ⊗_{(O, 0)} A ⊣ res`, descended to the homotopy categories. -/
noncomputable abbrev structureHomotopyAdjunction :
    HomotopyCategory.descend (structureExtension A) (structureExtensionData A).preservesHomotopic ⊣
      HomotopyCategory.descend (structureRestriction A)
        (preservesHomotopic_restriction _ (unitAlgebraHom_preservesOne A)) :=
  HomotopyCategory.descendAdjunction (structureAdjunction A)
    (preservesHomotopic_restriction _ (unitAlgebraHom_preservesOne A))
    (structureExtensionData A).preservesHomotopic

/-- **Precomposition with a quasi-isomorphism between flat and K-flat right differential graded
`(O, 0)`-modules is bijective on homotopy classes of morphisms into the restriction of a graded
injective and K-injective right differential graded `A`-module.** Through the adjunction it is
precomposition with the tensored quasi-isomorphism on homotopy classes of morphisms into the
module itself, and that is bijective by Tag 0FSX. -/
theorem bijective_precomp_structureRestriction
    {P Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (s : P ⟶ Q)
    (hP : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
      RelativeTensor.IsKFlat P)
    (hQ : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
      RelativeTensor.IsKFlat Q)
    (hs : QuasiIso s.toHomologicalComplex)
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I) :
    Function.Bijective (fun g : (HomotopyCategory.quotient _).obj Q ⟶
        (HomotopyCategory.quotient _).obj ((structureRestriction A).obj I) =>
      (HomotopyCategory.quotient _).map s ≫ g) := by
  let adj := structureHomotopyAdjunction A
  let L := HomotopyCategory.descend (structureExtension A)
    (structureExtensionData A).preservesHomotopic
  have hloc := isLocal_quotient_obj_of_isKInjective hI hI'
  have hW : quasiIsomorphisms.{u, u, u} A (L.map ((HomotopyCategory.quotient _).map s)) :=
    (quasiIsomorphisms_quotient_map_iff _).2 (quasiIso_structureExtension_map A s hP hQ hs)
  have hb := hloc _ hW
  have key : (fun g : (HomotopyCategory.quotient _).obj Q ⟶
        (HomotopyCategory.quotient _).obj ((structureRestriction A).obj I) =>
      (HomotopyCategory.quotient _).map s ≫ g) =
      (adj.homEquiv _ _) ∘ (fun h => L.map ((HomotopyCategory.quotient _).map s) ≫ h) ∘
        (adj.homEquiv _ _).symm := by
    funext g
    exact ((adj.homEquiv _ _).apply_symm_apply _).symm.trans
      (congrArg (adj.homEquiv _ _) (adj.homEquiv_naturality_left_symm _ _))
  rw [key]
  exact (adj.homEquiv _ _).bijective.comp (hb.comp (adj.homEquiv _ _).symm.bijective)

/-! ### Homotopy classes over `(O, 0)` are homotopy classes of complexes -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J (Type u)] in
/-- Two morphisms of right differential graded `(O, 0)`-modules are homotopic exactly when their
underlying morphisms of complexes are. -/
theorem structure_quotient_map_eq_iff
    {M N : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (h h' : M ⟶ N) :
    (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map h.toHomologicalComplex =
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map h'.toHomologicalComplex ↔
      (HomotopyCategory.quotient _).map h = (HomotopyCategory.quotient _).map h' := by
  rw [HomotopyCategory.quotient_map_eq_iff]
  constructor
  · intro e
    exact ⟨unitHomotopyOfHomotopy (M := M) (N := N) (f := h) (g := h')
      (_root_.HomotopyCategory.homotopyOfEq _ _ e)⟩
  · rintro ⟨H⟩
    exact _root_.HomotopyCategory.eq_of_homotopy _ _ H.toComplexHomotopy

omit [HasWeakSheafify X.J (Type u)] in
/-- The descended adjunction on a homotopy class of a module-level morphism is the homotopy
class of the module-level adjoint. -/
theorem structureHomotopyAdjunction_homEquiv_quotient_map
    {M : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)}
    {N : DifferentialGradedModule.{u, u, u} A} (k : (structureExtension A).obj M ⟶ N) :
    (structureHomotopyAdjunction A).homEquiv ((HomotopyCategory.quotient _).obj M)
        ((HomotopyCategory.quotient _).obj N) ((HomotopyCategory.quotient _).map k) =
      (HomotopyCategory.quotient _).map ((structureAdjunction A).homEquiv M N k) := by
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

/-! ### The extension of the regular module is the regular module -/

/-- The unit `(O, 0) ⟶ A`, as a morphism of right differential graded `(O, 0)`-modules from the
regular module into the restriction of the regular module of `A`. -/
noncomputable def structureRegularHom :
    regularModule (unitDGAlgebra X.O) ⟶ (structureRestriction A).obj (regularModule A) :=
  homMk (M := regularModule (unitDGAlgebra X.O))
    (N := (structureRestriction A).obj (regularModule A)) (unitAlgebraComplexHom A)

/-- The morphism `(O, 0) ⊗_{(O, 0)} A ⟶ A` adjoint to the unit, `x ⊗ a ↦ x a`. -/
noncomputable def structureExtensionRegularHom :
    (structureExtension A).obj (regularModule (unitDGAlgebra X.O)) ⟶ regularModule A :=
  ((structureAdjunction A).homEquiv _ _).symm (structureRegularHom A)

omit [HasWeakSheafify X.J (Type u)] in
/-- The adjoint of `structureExtensionRegularHom` is `structureRegularHom`. -/
theorem structureAdjunction_homEquiv_extensionRegularHom :
    (structureAdjunction A).homEquiv _ _ (structureExtensionRegularHom A) =
      structureRegularHom A :=
  Equiv.apply_symm_apply _ _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J (Type u)] in
/-- Morphisms out of the regular module agree as soon as they agree at the unit. -/
theorem hom_ext_regularModule {B : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
    {M : DifferentialGradedModule.{u, u, u} B} {f f' : regularModule B ⟶ M}
    (h : ∀ U, (f.toHomologicalComplex.f 0).val.app U (B.one.eval U) =
      (f'.toHomologicalComplex.f 0).val.app U (B.one.eval U)) : f = f' :=
  (homRegularEquivClosedSections M).injective
    (Subtype.ext (PresheafOfModules.sections_ext _ _ h))

/-- The inverse of `structureExtensionRegularHom`: `a ↦ 1 ⊗ a`. -/
noncomputable def structureExtensionRegularInv :
    regularModule A ⟶ (structureExtension A).obj (regularModule (unitDGAlgebra X.O)) :=
  ofSection (M := (structureExtension A).obj (regularModule (unitDGAlgebra X.O)))
    (evalOne (A := unitDGAlgebra X.O)
      ((structureAdjunction A).unit.app (regularModule (unitDGAlgebra X.O))))
    (evalOneClosed (A := unitDGAlgebra X.O)
      ((structureAdjunction A).unit.app (regularModule (unitDGAlgebra X.O)))).2

omit [HasWeakSheafify X.J (Type u)] in
/-- `structureExtensionRegularInv` sends the unit of `A` to the image of the unit of `(O, 0)`
under the unit of the adjunction `structureAdjunction`. -/
theorem structureExtensionRegularInv_one (U : X.Cᵒᵖ) :
    ((structureExtensionRegularInv A).toHomologicalComplex.f 0).val.app U (A.one.eval U) =
      (((structureAdjunction A).unit.app (regularModule (unitDGAlgebra X.O))).toHomologicalComplex.f
        0).val.app U ((unitDGAlgebra X.O).one.eval U) := by
  have := congrArg (fun z => PresheafOfModules.sections.eval z U)
    (evalOne_ofSection (M := (structureExtension A).obj (regularModule (unitDGAlgebra X.O)))
      (evalOne (A := unitDGAlgebra X.O)
        ((structureAdjunction A).unit.app (regularModule (unitDGAlgebra X.O))))
      (evalOneClosed (A := unitDGAlgebra X.O) ((structureAdjunction A).unit.app
        (regularModule (unitDGAlgebra X.O)))).2)
  exact this

omit [HasWeakSheafify X.J (Type u)] in
/-- `structureExtensionRegularHom` sends the image of the unit of `(O, 0)` under the unit of
the adjunction `structureAdjunction` to the unit of `A`. -/
theorem structureExtensionRegularHom_unit (U : X.Cᵒᵖ) :
    ((structureExtensionRegularHom A).toHomologicalComplex.f 0).val.app U
        ((((structureAdjunction A).unit.app
          (regularModule (unitDGAlgebra X.O))).toHomologicalComplex.f 0).val.app U
            ((unitDGAlgebra X.O).one.eval U)) = A.one.eval U := by
  have h := congrArg (fun k => (k.toHomologicalComplex.f 0).val.app U
    ((unitDGAlgebra X.O).one.eval U)) (structureAdjunction_homEquiv_extensionRegularHom A)
  rw [Adjunction.homEquiv_unit] at h
  refine h.trans ?_
  exact unitAlgebraHomF_app_one A U

/-- **`(O, 0) ⊗_{(O, 0)} A ≅ A`** as right differential graded `A`-modules. -/
noncomputable def structureExtensionRegularIso :
    (structureExtension A).obj (regularModule (unitDGAlgebra X.O)) ≅ regularModule A where
  hom := structureExtensionRegularHom A
  inv := structureExtensionRegularInv A
  hom_inv_id := by
    refine ((structureAdjunction A).homEquiv _ _).injective ?_
    rw [Adjunction.homEquiv_naturality_right, structureAdjunction_homEquiv_extensionRegularHom,
      Adjunction.homEquiv_id]
    refine hom_ext_regularModule fun U => ?_
    change ((structureExtensionRegularInv A).toHomologicalComplex.f 0).val.app U
      ((unitAlgebraHomF A 0).val.app U ((unitDGAlgebra X.O).one.eval U)) = _
    exact (congrArg _ (unitAlgebraHomF_app_one A U)).trans
      (structureExtensionRegularInv_one A U)
  inv_hom_id := by
    refine hom_ext_regularModule fun U => ?_
    change ((structureExtensionRegularHom A).toHomologicalComplex.f 0).val.app U
      (((structureExtensionRegularInv A).toHomologicalComplex.f 0).val.app U (A.one.eval U)) = _
    rw [structureExtensionRegularInv_one, structureExtensionRegularHom_unit]
    rfl

/-! ### Morphisms out of the regular module are morphisms out of the structure sheaf -/

omit [HasWeakSheafify X.J (Type u)] in
/-- The adjoint of `structureExtensionRegularHom ≫ g` has underlying morphism of complexes
`unitAlgebraComplexHom A ≫ g`. -/
theorem structureAdjunction_homEquiv_extensionRegularHom_comp
    {N : DifferentialGradedModule.{u, u, u} A} (g : regularModule A ⟶ N) :
    ((structureAdjunction A).homEquiv _ _
        (structureExtensionRegularHom A ≫ g)).toHomologicalComplex =
      unitAlgebraComplexHom A ≫ g.toHomologicalComplex := by
  rw [Adjunction.homEquiv_naturality_right, structureAdjunction_homEquiv_extensionRegularHom]
  rfl

omit [HasWeakSheafify X.J (Type u)] in
/-- Every morphism of complexes from `O` to the underlying complex of a right differential
graded `A`-module is the restriction to `O` of a morphism from `A`. -/
theorem exists_unitAlgebraComplexHom_comp {N : DifferentialGradedModule.{u, u, u} A}
    (f : unitComplex X.O ⟶ N.complex) :
    ∃ g : regularModule A ⟶ N, unitAlgebraComplexHom A ≫ g.toHomologicalComplex = f := by
  let h : regularModule (unitDGAlgebra X.O) ⟶ (structureRestriction A).obj N :=
    homMk (M := regularModule (unitDGAlgebra X.O))
      (N := (structureRestriction A).obj N) f
  refine ⟨(structureExtensionRegularIso A).inv ≫ ((structureAdjunction A).homEquiv _ _).symm h,
    ?_⟩
  rw [← structureAdjunction_homEquiv_extensionRegularHom_comp]
  change ((structureAdjunction A).homEquiv _ _ ((structureExtensionRegularIso A).hom ≫
    (structureExtensionRegularIso A).inv ≫ _)).toHomologicalComplex = f
  rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  rfl

omit [HasWeakSheafify X.J (Type u)] in
/-- Two morphisms from `A` into a right differential graded `A`-module are homotopic as soon as
their restrictions to `O` are homotopic as morphisms of complexes. -/
theorem quotient_map_eq_of_unitAlgebraComplexHom_comp
    {N : DifferentialGradedModule.{u, u, u} A} (g g' : regularModule A ⟶ N)
    (h : (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (unitAlgebraComplexHom A ≫ g.toHomologicalComplex) =
      (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (unitAlgebraComplexHom A ≫ g'.toHomologicalComplex)) :
    (HomotopyCategory.quotient A).map g = (HomotopyCategory.quotient A).map g' := by
  rw [← structureAdjunction_homEquiv_extensionRegularHom_comp,
    ← structureAdjunction_homEquiv_extensionRegularHom_comp] at h
  have h₁ := (structure_quotient_map_eq_iff
    (M := regularModule (unitDGAlgebra X.O)) (N := (structureRestriction A).obj N) _ _).1 h
  rw [← structureHomotopyAdjunction_homEquiv_quotient_map,
    ← structureHomotopyAdjunction_homEquiv_quotient_map] at h₁
  have h' := ((structureHomotopyAdjunction A).homEquiv _ _).injective h₁
  rw [Functor.map_comp, Functor.map_comp] at h'
  have : IsIso ((HomotopyCategory.quotient A).map (structureExtensionRegularHom A)) :=
    Functor.map_isIso _ (structureExtensionRegularIso A).hom
  exact (cancel_epi _).1 h'

/-! ### Morphisms from `O` into the underlying complex of a K-injective module -/

/-- A quasi-isomorphism `s : P ⟶ O` is refined by a quasi-isomorphism `t : P' ⟶ P` such that
precomposition with `t ≫ s` is bijective on homotopy classes of morphisms into the underlying
complex of a graded injective and K-injective right differential graded `A`-module. -/
theorem exists_quasiIso_bijective_precomp
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I)
    {P : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ}
    (s : P ⟶ unitComplex X.O) (hs : QuasiIso s) :
    ∃ (P' : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ) (t : P' ⟶ P),
      QuasiIso t ∧
        (∀ f : P' ⟶ I.complex, ∃ g : unitComplex X.O ⟶ I.complex,
          (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (t ≫ s ≫ g) =
            (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) ∧
        ∀ g g' : unitComplex X.O ⟶ I.complex,
          (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (t ≫ s ≫ g) =
              (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (t ≫ s ≫ g') →
            (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g =
              (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g' := by
  obtain ⟨P', t, ht, hP'₁, hP'₂⟩ := exists_flat_quasiIso (ofComplex (Osharp := X.O) P)
  let s' : P' ⟶ regularModule (unitDGAlgebra X.O) :=
    homMk (M := P') (N := regularModule (unitDGAlgebra X.O))
      (t.toHomologicalComplex ≫ s)
  have hs' : QuasiIso s'.toHomologicalComplex := by
    exact quasiIso_comp (K := P'.complex) (L := P) t.toHomologicalComplex s (hφ := ht)
      (hφ' := hs)
  have hb := bijective_precomp_structureRestriction A s' ⟨hP'₁, hP'₂⟩
    ⟨RelativeTensor.isGradedFlat_ofDifferentialGraded_regularModule (unitDGAlgebra X.O),
      RelativeTensor.isKFlat_regularModule (unitDGAlgebra X.O)⟩ hs' hI hI'
  let G : (unitComplex X.O ⟶ I.complex) → (regularModule (unitDGAlgebra X.O) ⟶
      (structureRestriction A).obj I) := fun k =>
    homMk (M := regularModule (unitDGAlgebra X.O)) (N := (structureRestriction A).obj I) k
  refine ⟨P'.complex, t.toHomologicalComplex, ht, fun f => ?_, fun g g' hgg' => ?_⟩
  · obtain ⟨γ, hγ⟩ := hb.2 ((HomotopyCategory.quotient _).map
      (homMk (M := P') (N := (structureRestriction A).obj I) f))
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _).map_surjective γ
    refine ⟨g.toHomologicalComplex, ?_⟩
    have hγ' : (HomotopyCategory.quotient _).map (s' ≫ g) =
        (HomotopyCategory.quotient _).map
          (homMk (M := P') (N := (structureRestriction A).obj I) f) :=
      ((HomotopyCategory.quotient _).map_comp _ _).trans hγ
    exact (structure_quotient_map_eq_iff (s' ≫ g) _).2 hγ'
  · have h1 : (HomotopyCategory.quotient _).map (s' ≫ G g) =
        (HomotopyCategory.quotient _).map (s' ≫ G g') :=
      (structure_quotient_map_eq_iff (s' ≫ G g) (s' ≫ G g')).1 (by
        have e : ∀ k : unitComplex X.O ⟶ I.complex,
            (s' ≫ G k).toHomologicalComplex = t.toHomologicalComplex ≫ s ≫ k := fun k =>
          (Category.assoc _ _ _)
        exact (congrArg _ (e g)).trans (hgg'.trans (congrArg _ (e g')).symm))
    rw [Functor.map_comp, Functor.map_comp] at h1
    exact (structure_quotient_map_eq_iff (G g) (G g')).2 (hb.1 h1)

/-- The homotopy class of the restriction to `O` of a morphism out of the regular module. -/
noncomputable def structureClass {N : DifferentialGradedModule.{u, u, u} A}
    (g : regularModule A ⟶ N) :
    (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplex X.O) ⟶
      (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N.complex :=
  (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    (unitAlgebraComplexHom A ≫ g.toHomologicalComplex)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J (Type u)] in
/-- Homotopic morphisms out of the regular module have the same `structureClass`. -/
theorem structureClass_eq {N : DifferentialGradedModule.{u, u, u} A}
    {g g' : regularModule A ⟶ N}
    (h : (HomotopyCategory.quotient A).map g = (HomotopyCategory.quotient A).map g') :
    structureClass A g = structureClass A g' := by
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_iff g g').1 h
  exact ((_root_.HomotopyCategory.quotient _ _).map_comp _ _).trans
    ((congrArg (_ ≫ ·) (_root_.HomotopyCategory.eq_of_homotopy _ _ H.toComplexHomotopy)).trans
      ((_root_.HomotopyCategory.quotient _ _).map_comp _ _).symm)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J (Type u)] in
/-- `structureClass` is additive. -/
theorem structureClass_add {N : DifferentialGradedModule.{u, u, u} A}
    (g g' : regularModule A ⟶ N) :
    structureClass A (g + g') = structureClass A g + structureClass A g' := by
  have : (g + g').toHomologicalComplex = g.toHomologicalComplex + g'.toHomologicalComplex :=
    HomologicalComplex.hom_ext _ _ fun n => add_f g g' n
  exact (congrArg (fun k => (_root_.HomotopyCategory.quotient _ _).map
    (unitAlgebraComplexHom A ≫ k)) this).trans
    ((congrArg (_root_.HomotopyCategory.quotient _ _).map (Preadditive.comp_add _ _ _ _ _ _)).trans
      ((_root_.HomotopyCategory.quotient _ _).map_add))

/-- Restriction along the unit `O ⟶ A`, on homotopy classes of morphisms out of `A`. -/
noncomputable def regularHomotopyHomAddHom (N : DifferentialGradedModule.{u, u, u} A) :
    ((HomotopyCategory.quotient A).obj (regularModule A) ⟶
        (HomotopyCategory.quotient A).obj N) →+
      ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplex X.O) ⟶
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N.complex) :=
  AddMonoidHom.mk' (fun x => structureClass A ((HomotopyCategory.quotient A).preimage x))
    fun x y => by
      refine (structureClass_eq A (g' := (HomotopyCategory.quotient A).preimage x +
        (HomotopyCategory.quotient A).preimage y) ?_).trans (structureClass_add A _ _)
      rw [Functor.map_preimage, Functor.map_add, Functor.map_preimage, Functor.map_preimage]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J (Type u)] in
/-- `regularHomotopyHomAddHom` sends the homotopy class of `g` to `structureClass A g`. -/
theorem regularHomotopyHomAddHom_quotient_map {N : DifferentialGradedModule.{u, u, u} A}
    (g : regularModule A ⟶ N) :
    regularHomotopyHomAddHom A N ((HomotopyCategory.quotient A).map g) =
      structureClass A g :=
  structureClass_eq A (Functor.map_preimage _ _)

/-- **Morphisms `A ⟶ N` of `K(Mod(A, d))` are morphisms `O ⟶ N` of complexes up to homotopy**,
by restriction along the unit `O ⟶ A`. -/
noncomputable def regularHomotopyHomAddEquiv (N : DifferentialGradedModule.{u, u, u} A) :
    ((HomotopyCategory.quotient A).obj (regularModule A) ⟶
        (HomotopyCategory.quotient A).obj N) ≃+
      ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplex X.O) ⟶
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N.complex) :=
  AddEquiv.ofBijective (regularHomotopyHomAddHom A N)
    ⟨fun x y h => by
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective x
      obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient A).map_surjective y
      rw [regularHomotopyHomAddHom_quotient_map, regularHomotopyHomAddHom_quotient_map] at h
      exact quotient_map_eq_of_unitAlgebraComplexHom_comp A g g' h,
    fun y => by
      obtain ⟨f, rfl⟩ := (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective y
      obtain ⟨g, hg⟩ := exists_unitAlgebraComplexHom_comp A f
      refine ⟨(HomotopyCategory.quotient A).map g, ?_⟩
      rw [regularHomotopyHomAddHom_quotient_map, structureClass, hg]⟩

omit [HasWeakSheafify X.J (Type u)] in
/-- `regularHomotopyHomAddEquiv` sends the homotopy class of `g` to `structureClass A g`. -/
theorem regularHomotopyHomAddEquiv_quotient_map {N : DifferentialGradedModule.{u, u, u} A}
    (g : regularModule A ⟶ N) :
    regularHomotopyHomAddEquiv A N ((HomotopyCategory.quotient A).map g) =
      structureClass A g :=
  regularHomotopyHomAddHom_quotient_map A g

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **For a graded injective and K-injective right differential graded `A`-module `I`, the
localization functor `K(O) ⥤ D(O)` is bijective on morphisms from `O` into the underlying
complex of `I`.** The underlying complex need not be K-injective; what is used is that `O` is
resolved by flat and K-flat right differential graded `(O, 0)`-modules, against which the
underlying complex of `I` behaves as if it were. -/
theorem bijective_Qh_map_unitComplex
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I) :
    Function.Bijective (fun g : (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (unitComplex X.O) ⟶ (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          I.complex => DerivedCategory.Qh.map g) := by
  let q := _root_.HomotopyCategory.quotient (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  let W := _root_.HomotopyCategory.quasiIso (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  have hqi : ∀ {P Q : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ} (s : P ⟶ Q),
      W (q.map s) ↔ QuasiIso s := fun s =>
    (_root_.HomotopyCategory.quotient_map_mem_quasiIso_iff s).trans
      (HomologicalComplex.mem_quasiIso_iff _)
  refine ⟨fun g₁ g₂ h => ?_, fun φ => ?_⟩
  · obtain ⟨Y, s, hs, hs'⟩ :=
      (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh W g₁ g₂).1 h
    obtain ⟨P, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨s, rfl⟩ := q.map_surjective s
    obtain ⟨h₁, rfl⟩ := q.map_surjective g₁
    obtain ⟨h₂, rfl⟩ := q.map_surjective g₂
    have hs₀ : QuasiIso s := (hqi s).1 hs
    obtain ⟨P', t, -, -, hinj⟩ := exists_quasiIso_bijective_precomp A hI hI' s hs₀
    refine hinj h₁ h₂ ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    rw [← Functor.map_comp, ← Functor.map_comp] at hs'
    exact congrArg (q.map t ≫ ·) ((q.map_comp _ _).symm.trans (hs'.trans (q.map_comp _ _)))
  · obtain ⟨@⟨Y, s, hs, f⟩, rfl⟩ := Localization.exists_rightFraction DerivedCategory.Qh W φ
    obtain ⟨P, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨s, rfl⟩ := q.map_surjective s
    obtain ⟨f, rfl⟩ := q.map_surjective f
    have hs₀ : QuasiIso s := (hqi s).1 hs
    obtain ⟨P', t, ht, hsurj, -⟩ := exists_quasiIso_bijective_precomp A hI hI' s hs₀
    obtain ⟨g, hg⟩ := hsurj (t ≫ f)
    refine ⟨q.map g, ?_⟩
    have : IsIso (DerivedCategory.Qh.map (q.map s)) := Localization.inverts _ W _ hs
    have : IsIso (DerivedCategory.Qh.map (q.map t)) := Localization.inverts _ W _
      ((hqi t).2 ht)
    change DerivedCategory.Qh.map (q.map g) =
      inv (DerivedCategory.Qh.map (q.map s)) ≫ DerivedCategory.Qh.map (q.map f)
    rw [← cancel_epi (DerivedCategory.Qh.map (q.map s)), IsIso.hom_inv_id_assoc,
      ← cancel_epi (DerivedCategory.Qh.map (q.map t))]
    simp only [← Functor.map_comp]
    exact congrArg DerivedCategory.Qh.map hg

end Derived

end DifferentialGradedModule

/-! ### Cohomology as morphisms in the derived category -/

namespace DifferentialGradedModule

open DifferentialGradedAlgebra Stacks.Cohomology.ModuleSections

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}

/-- The cohomology `H^n(C, M)` of a right differential graded module, viewed as a complex of
`O`-modules: the `n`-th cohomology of `RΓ(C, M)`. -/
noncomputable abbrev cohomology
    {A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) : Type u :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
    ((derivedModuleGlobalSections X).obj (DerivedCategory.Q.obj M.complex))

/-- **On a K-injective complex `J`, the degree-zero cohomology of its global sections is
`Hom_{D(O)}(O, J)`**: the global sections of `J` are those of `SheafHom(O, J)`, and Tag 0A94. -/
noncomputable def kInjectiveSectionsHomologyAddEquiv
    (J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] :
    ((AlgebraicGeometry.RingedSite.globalSectionsComplex X J).homology 0 : Type u) ≃+
      (DerivedCategory.Q.obj (unitComplex X.O) ⟶ DerivedCategory.Q.obj J) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).mapIso
      (((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (AlgebraicGeometry.RingedSite.structureSheafHomIso
          X J).symm)).addCommGroupIsoToAddEquiv.trans
    (AlgebraicGeometry.RingedSite.sheafHomGlobalHomologyEquivDerivedCategoryHom X
      (AlgebraicGeometry.RingedSite.structureSheafComplex X) J)

/-- **The cohomology of a complex of `O`-modules is morphisms from `O` in `D(O)`**:
`H^n(C, K) = Hom_{D(O)}(O, K[n])`, computed on a K-injective resolution of `K`. -/
noncomputable def complexCohomologyAddEquiv
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections X).obj (DerivedCategory.Q.obj K)) : Type u) ≃+
      (DerivedCategory.Q.obj (unitComplex X.O) ⟶ DerivedCategory.Q.obj (K⟦n⟧)) :=
  let t := (Stacks.Injectives.kInjectiveResolutionInclusion
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app K
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).obj K
  haveI : IsIso (DerivedCategory.Q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).2 inferInstance
  haveI : IsIso (DerivedCategory.Q.map (t⟦n⟧')) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      ((derivedModuleGlobalSections X).mapIso (asIso (DerivedCategory.Q.map t))) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
      (globalSectionsKInjectiveIso X J).symm ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
      (AlgebraicGeometry.RingedSite.globalSectionsComplex X J) ≪≫
    (((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).shiftIso
      n 0 n (add_zero n)).app (AlgebraicGeometry.RingedSite.globalSectionsComplex X J)).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).mapIso
      (AlgebraicGeometry.RingedSite.globalSectionsComplexShiftIso
        X J n).symm).addCommGroupIsoToAddEquiv.trans
    ((kInjectiveSectionsHomologyAddEquiv (J⟦n⟧)).trans
      (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
        (asIso (DerivedCategory.Q.map (t⟦n⟧'))).symm).toAddEquiv)

/-- Let `(C, O)` be a ringed site, `A` a sheaf of differential graded `O`-algebras, `M` a right
differential graded `A`-module and `n` an integer. Then `H^n(C, M) = Hom_{D(A, d)}(A, M[n])`,
where on the left `M` is viewed as a complex of `O`-modules.

The identification is the source's: for a quasi-isomorphism `M[n] ⟶ I` into a graded injective
and K-injective module (Tag 0FT0), morphisms `A ⟶ M[n]` of `D(A, d)` are morphisms `A ⟶ I` of
the homotopy category (Tag 0FT8), which are morphisms `O ⟶ I` of complexes up to homotopy, and
these compute `H^0(RΓ(C, I)) = H^n(C, M)`. The last step is the source's `RΓ(C, M) = Γ(C, I)`;
it is proved here by comparing with a K-injective resolution of `I` in `D(O)`, using that `O`
is resolved by flat and K-flat right differential graded `(O, 0)`-modules, the tensor product
with `A` of such a resolution is a resolution of `A` (Tag 0FSI), and extension of scalars along
`(O, 0) ⟶ A` is left adjoint to restriction (Tag 0FRP). -/
@[stacks 0FTX]
noncomputable def cohomologyAddEquivDerivedHom
    (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    cohomology M n ≃+
      ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦n⟧) := by
  let N := shiftedModule A M n
  have hres := hasKInjectiveResolutions_dg.{u, u, u} A N
  let I := hres.choose
  let b : N ⟶ I := hres.choose_spec.choose
  have hb : QuasiIso b.toHomologicalComplex := hres.choose_spec.choose_spec.1
  have hGI : GradedInjective I := hres.choose_spec.choose_spec.2.1
  have hKI : IsKInjective I := hres.choose_spec.choose_spec.2.2
  have hN : N.complex = M.complex⟦n⟧ := HomotopyCategory.shiftFunctor_obj_complex A n M
  haveI : IsIso (DerivedCategory.Q.map b.toHomologicalComplex) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hb
  let qO := _root_.HomotopyCategory.quotient
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
  let e₁ := complexCohomologyAddEquiv M.complex n
  let e₂ : (DerivedCategory.Q.obj (unitComplex X.O) ⟶
      DerivedCategory.Q.obj (M.complex⟦n⟧)) ≃+
      (DerivedCategory.Q.obj (unitComplex X.O) ⟶ DerivedCategory.Q.obj I.complex) :=
    (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
      (eqToIso (congrArg DerivedCategory.Q.obj hN.symm) ≪≫
        asIso (DerivedCategory.Q.map b.toHomologicalComplex))).toAddEquiv
  let e₃ : (DerivedCategory.Q.obj (unitComplex X.O) ⟶ DerivedCategory.Q.obj I.complex) ≃+
      (DerivedCategory.Qh.obj (qO.obj (unitComplex X.O)) ⟶
        DerivedCategory.Qh.obj (qO.obj I.complex)) :=
    (CategoryTheory.Linear.homCongr ℤ
      ((DerivedCategory.quotientCompQhIso _).app _).symm
      ((DerivedCategory.quotientCompQhIso _).app _).symm).toAddEquiv
  let A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O) := A
  let I' : DifferentialGradedModule.{u, u, u} A' := I
  let e₄ : (DerivedCategory.Qh.obj (qO.obj (unitComplex X.O)) ⟶
        DerivedCategory.Qh.obj (qO.obj I.complex)) ≃+
      (qO.obj (unitComplex X.O) ⟶ qO.obj I.complex) :=
    (AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (bijective_Qh_map_unitComplex A' (I := I') hKI hGI)).symm
  let e₅ := (regularHomotopyHomAddEquiv A' I').symm
  have hloc := isLocal_quotient_obj_of_isKInjective.{u, u, u} hKI hGI
  let e₆ : ((HomotopyCategory.quotient A).obj (regularModule A) ⟶
        (HomotopyCategory.quotient A).obj I) ≃+
      ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
        (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj N)) :=
    AddEquiv.ofBijective
      (AddMonoidHom.mk' (fun g => (toDerivedCategory.{u, u, u} A).map g ≫
          (toDerivedCategoryIso b hb).inv)
        fun g g' => by rw [Functor.map_add, Preadditive.add_comp])
      (by
        convert (derivedHomEquivHomotopyHom (M := regularModule A) hloc hb).symm.bijective
          using 1
        funext g
        exact (derivedHomEquivHomotopyHom_symm_apply hloc hb g).symm)
  let e₇ : ((toDerivedCategory.{u, u, u} A).obj
        ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
        (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj N)) ≃+
      ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦n⟧) :=
    (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
      (((toDerivedCategory.{u, u, u} A).commShiftIso n).app
        ((HomotopyCategory.quotient A).obj M))).toAddEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans e₇)))))

end DifferentialGradedModule

end SheafOfModules

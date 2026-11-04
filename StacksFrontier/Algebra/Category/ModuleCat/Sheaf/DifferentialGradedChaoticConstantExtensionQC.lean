module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantDerivedAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionComparisonPlain
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestrictionQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantQuasiCoherent
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeLeftOrthogonal
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic

/-!
# Extension of scalars from the constant ring lands in the quasi-coherent objects

Let `C` be a small category with the chaotic topology, `R` a commutative ring and `A` a sheaf of
differential graded algebras over the constant sheaf of rings with value `R`. For a complex `K`
of `R`-modules the comparison map `(K ⊗_R A(V)) ⊗_{A(V)} A(U) ⟶ K ⊗_R A(U)` of the extension of
scalars `K ⊗_R A` along `V ⟶ U` is the isomorphism `x ⊗ b ⊗ c ↦ x ⊗ b|_U c` of extension of
scalars along a composite. When `K` is orthogonal on the left to the acyclic complexes, so is
`K ⊗_R A(V)`, and then the comparison maps of quasi-coherence are invertible: `K ⊗_R A` is
quasi-coherent. Every object of `D(R)` is computed by such a `K` (a resolution with property (P)),
so the derived extension of scalars `F' : D(R) ⥤ D(A, d)` takes values in `QC(A, d)`. This is
the statement that `Lf^*` lands in `QC(ℬ)` of the proof of Proposition 0GZK.

## Main results

* `Stacks.ChaoticSite.plainSectionComparison_extendFunctor`: the plain comparison map of
  `K ⊗_R A` is the comparison of extension of scalars along a composite, read through the
  identifications of the sections.
* `Stacks.ChaoticSite.isQCModule_extendFunctor_obj`: `K ⊗_R A` is quasi-coherent when `K` is
  orthogonal on the left to the acyclic complexes.
* `Stacks.ChaoticSite.exists_leftOrthogonal_iso_Q`: every object of `D(R)` is the class of a
  complex orthogonal on the left to the acyclic complexes.
* `Stacks.ChaoticSite.qc_derivedExtend_obj`: **the derived extension of scalars takes values in
  the quasi-coherent objects.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Stacks.PresheafOfModules

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.ChaoticSite

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]

/-! ### The comparison maps of `K ⊗_R A` -/

section Strict

variable (A : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)))
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The restriction homomorphism of `K ⊗_R A` is the map `x ⊗ b ↦ x ⊗ b|_U` into extension of
scalars along the composite `R → A(V) → A(U)`. -/
theorem extensionRestr_eq_compBackwardInner {U V : Cᵒᵖ} (a : V ⟶ U) :
    extensionRestr A K a = compBackwardInner (structureHom A V) (A.sectionRestriction a)
      (structureHom A U) (sectionRestriction_structureHom A a) (baseModule K) :=
  rfl

/-- The plain transpose of the restriction homomorphism of `K ⊗_R A` is the comparison
`(K ⊗_R A(V)) ⊗_{A(V)} A(U) ⟶ K ⊗_R A(U)` of extension of scalars along a composite. -/
theorem plainTranspose_extensionRestr {U V : Cᵒᵖ} (a : V ⟶ U) :
    plainTranspose (A.sectionRestriction a) (extensionRestr A K a) =
      compBackward (structureHom A V) (A.sectionRestriction a) (structureHom A U)
        (sectionRestriction_structureHom A a) (baseModule K) :=
  rfl

/-- **The plain comparison map of `K ⊗_R A`**, read through the identifications of the sections,
is the comparison of extension of scalars along the composite `R → A(V) → A(U)`. -/
theorem plainSectionComparison_extendFunctor {U V : Cᵒᵖ} (a : V ⟶ U) :
    Chaotic.plainSectionComparison ((extendFunctor A).obj K) a ≫
        ((extensionSystem A K).sectionsIso U).hom =
      (tensorCompFunctor (regular (A.sectionRestriction a))).map
          ((extensionSystem A K).sectionsIso V).hom ≫
        compBackward (structureHom A V) (A.sectionRestriction a) (structureHom A U)
          (sectionRestriction_structureHom A a) (baseModule K) := by
  have h := (extensionSystem A K).sectionModuleRestriction_sectionsIso a
  refine ((tensorRegularAdjRestrictScalars (A.sectionRestriction a)).homEquiv_naturality_right_symm
    _ _).symm.trans ?_
  refine (congrArg (fun g => ((tensorRegularAdjRestrictScalars
    (A.sectionRestriction a)).homEquiv _ _).symm g) h).trans ?_
  exact ((tensorRegularAdjRestrictScalars (A.sectionRestriction a)).homEquiv_naturality_left_symm
    _ _)

/-- The plain comparison map `(K ⊗_R A(V)) ⊗_{A(V)} A(U) ⟶ K ⊗_R A(U)` of `K ⊗_R A` along
`V ⟶ U` is an isomorphism. -/
theorem isIso_plainSectionComparison_extendFunctor {U V : Cᵒᵖ} (a : V ⟶ U) :
    IsIso (Chaotic.plainSectionComparison ((extendFunctor A).obj K) a) := by
  have h := plainSectionComparison_extendFunctor A K a
  have : IsIso (compBackward (structureHom A V) (A.sectionRestriction a) (structureHom A U)
      (sectionRestriction_structureHom A a) (baseModule K)) :=
    (compIso (structureHom A V) (A.sectionRestriction a) (structureHom A U)
      (sectionRestriction_structureHom A a) (baseModule K)).isIso_inv
  have h' : Chaotic.plainSectionComparison ((extendFunctor A).obj K) a =
      ((tensorCompFunctor (regular (A.sectionRestriction a))).map
          ((extensionSystem A K).sectionsIso V).hom ≫
        compBackward (structureHom A V) (A.sectionRestriction a) (structureHom A U)
          (sectionRestriction_structureHom A a) (baseModule K)) ≫
        ((extensionSystem A K).sectionsIso U).inv :=
    (Iso.eq_comp_inv ((extensionSystem A K).sectionsIso U)).2 h
  rw [h']
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
    this) (Iso.isIso_inv _)

variable {K}

/-- **`K ⊗_R A` is quasi-coherent when `K` is orthogonal on the left to the acyclic
complexes.** -/
theorem isQCModule_extendFunctor_obj
    (hK : (_root_.DifferentialGradedModule.acyclic' (baseDGA R)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (baseDGA R)).obj (baseModule K))) :
    Chaotic.IsQCModule ((extendFunctor A).obj K) := by
  intro U V a
  have hV : (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra V)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).obj
        (((extendFunctor A).obj K).sectionModule V)) :=
    (_root_.DifferentialGradedModule.acyclic' (A.sectionAlgebra V)).leftOrthogonal.prop_of_iso
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).mapIso
        ((extensionSystem A K).sectionsIso V).symm)
      (leftOrthogonal_tensorCompFunctor_obj (structureHom A V) hK)
  have := isIso_plainSectionComparison_extendFunctor A K a
  exact (Chaotic.isIso_sectionComparison_iff_quasiIso _ a hV).2 inferInstance

end Strict

/-! ### Resolutions orthogonal on the left to the acyclic complexes -/

section Resolution

attribute [local instance] HasDerivedCategory.standard

open _root_.DifferentialGradedModule in
/-- **Every object of `D(R)` is the class of a complex orthogonal on the left to the acyclic
complexes**: the complex of homogeneous components of a resolution with property (P). -/
theorem exists_leftOrthogonal_iso_Q (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (acyclic' (baseDGA R)).leftOrthogonal
        ((toHomotopyCategory (baseDGA R)).obj (baseModule P)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj L) := by
  obtain ⟨P', f, hf, ⟨F⟩⟩ := exists_propertyP_resolution (baseDGA R) (baseModule L)
  have : QuasiIso ((degreeZeroComponentFunctor (ULift.{u} ℤ) R).map f) :=
    (degreeZeroComplexMap_quasiIso_iff (A := R) f).2 hf
  refine ⟨(degreeZeroComponentFunctor (ULift.{u} ℤ) R).obj P', ?_,
    ⟨asIso (DerivedCategory.Q.map ((degreeZeroComponentFunctor (ULift.{u} ℤ) R).map f)) ≪≫
      DerivedCategory.Q.mapIso (degreeZeroComplexIso (R := ULift.{u} ℤ) (S := R) (A := R) L)⟩⟩
  exact (acyclic' (baseDGA R)).leftOrthogonal.prop_of_iso
    ((toHomotopyCategory (baseDGA R)).mapIso
      ((degreeZeroTotalIso (R := ULift.{u} ℤ) (S := R) (A := R)).app P').symm)
    (leftOrthogonal_acyclic_of_propertyP F)

end Resolution

/-! ### The derived extension of scalars lands in `QC(A, d)` -/

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {B : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R)}

/-- The derived extension of scalars at the class of a complex `K` is the class of `K ⊗_R B`. -/
def derivedExtendQIso (hB : ExtendInvertsQuasiIso B) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtend hB).obj (DerivedCategory.Q.obj K) ≅
      Chaotic.derivedClass B ((castDGMod B).obj ((extendFunctor (castAlg B)).obj K)) :=
  (derivedExtend hB).mapIso ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
    (derivedExtendFac hB).app _

/-- The derived extension of scalars at the class of a complex orthogonal on the left to the
acyclic complexes is quasi-coherent. -/
theorem qc_derivedExtend_Q_obj (hB : ExtendInvertsQuasiIso B)
    {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : (_root_.DifferentialGradedModule.acyclic' (baseDGA R)).leftOrthogonal
      ((_root_.DifferentialGradedModule.toHomotopyCategory (baseDGA R)).obj (baseModule K))) :
    Chaotic.QC B ((derivedExtend hB).obj (DerivedCategory.Q.obj K)) :=
  (Chaotic.QC B).prop_of_iso (derivedExtendQIso hB K).symm
    ((Chaotic.qc_derivedClass_iff (O := constCommRingSheaf (C := C) R) B _).2
      (isQCModule_extendFunctor_obj (castAlg B) hK))

/-- **The derived extension of scalars `F' : D(R) ⥤ D(B, d)` takes values in the quasi-coherent
objects `QC(B, d)`.** -/
theorem qc_derivedExtend_obj (hB : ExtendInvertsQuasiIso B)
    (X : DerivedCategory (ModuleCat.{u} R)) : Chaotic.QC B ((derivedExtend hB).obj X) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_leftOrthogonal_iso_Q (DerivedCategory.Q.objPreimage X)
  exact (Chaotic.QC B).prop_of_iso
    ((derivedExtend hB).mapIso (e ≪≫ DerivedCategory.Q.objObjPreimageIso X))
    (qc_derivedExtend_Q_obj hB hP)

end Derived

end Stacks.ChaoticSite

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedExtensionUnitQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorPullbackFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedGoodResolutionDataConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived extension of scalars along a quasi-isomorphism is an equivalence

Let `(C, O)` be a ringed site and let `φ : A ⟶ B` be a homomorphism of sheaves of differential
graded `O`-algebras which induces an isomorphism on cohomology sheaves. This file proves
[Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ): derived extension of scalars

`D(A, d) ⟶ D(B, d)`, `M ↦ M ⊗^𝐋_A B`

is an equivalence of categories, with restriction of scalars as quasi-inverse.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedExtension`: the functor `M ↦ M ⊗^𝐋_A B`. It
  is the derived tensor product of [Stacks, Tag 0FTG] (1) with the bimodule `{}_A B_B`, computed
  on flat and K-flat resolutions (Tag 0FSH).
* `SheafOfModules.DifferentialGradedModule.derivedExtensionAdjunction`: derived extension of
  scalars is left adjoint to restriction of scalars `D(B, d) ⟶ D(A, d)`.
* `SheafOfModules.DifferentialGradedModule.derivedExtensionEquivalence`: the equivalence
  `D(A, d) ≌ D(B, d)` for a quasi-isomorphism `φ`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isIso_derivedExtensionAdjunction_unit_app` and
  `SheafOfModules.DifferentialGradedModule.isIso_derivedExtensionAdjunction_counit_app`: for a
  quasi-isomorphism `φ` the unit and the counit of the derived adjunction are invertible.
* `SheafOfModules.DifferentialGradedModule.isEquivalence_derivedExtension`: derived extension of
  scalars along a quasi-isomorphism is an equivalence.
* `SheafOfModules.DifferentialGradedModule.isEquivalence_derivedRestriction`: restriction of
  scalars along a quasi-isomorphism is an equivalence of derived categories.

## Implementation notes

Restriction of scalars inverts quasi-isomorphisms, so it is its own derived functor; the adjunction
`- ⊗_A B ⊣ res_φ` of Tag 0FRP descends to the homotopy categories and then to the derived
categories (Mathlib's `CategoryTheory.Adjunction.derived`, whose absoluteness conditions hold
because the derived extension is computed by a resolving class and restriction is a localization
lift). The unit of the derived adjunction at a flat and K-flat module `P` is the unit
`P ⟶ res_φ (P ⊗_A B)` of the underived one, which is a quasi-isomorphism by
`quasiIso_extensionUnit_of_isKFlat`; every object of `D(A, d)` is such a module. The last step is
`isEquivalence_of_isIso_unit_derivedRestriction`: restriction of scalars reflects isomorphisms,
which is how "the kernel of the restriction functor is zero" enters.

The homogeneous pieces of the two algebras and the modules live in the universe of the ringed
site, which is where the relative tensor product of differential graded modules is constructed.

## References

* [Stacks Project, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : A ⟶ B)
  (hφ : φ.PreservesOne)

/-- Extension of scalars `- ⊗_A B` along `φ`, as a tensor product functor: the tensor product
with the bimodule `{}_A B_B`. -/
@[ega "II 2.1.2" "more general"]
abbrev extensionData : TensorFunctorData.{u, u, u, u, u} A B (φ.toBimodule hφ) :=
  RelativeTensor.tensorFunctorDataDgTensorRight
    (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)))
    (B := (B : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) (φ.toBimodule hφ)

/-- **Extension of scalars is exact on flat K-flat modules**: it commutes with cones (Tag 0FTE),
and it carries a flat, K-flat and acyclic module to an acyclic one (Tag 0FSI (1)). -/
def extensionExactnessData :
    PullbackTensorExactnessData (idPullbackData.{u, u, u} (A := A)) (extensionData φ hφ)
      (tensorGood (A := A)) :=
  tensorExactnessData (φ.toBimodule hφ)

/-- **Derived extension of scalars** `- ⊗^𝐋_A B : D(A, d) ⥤ D(B, d)` along `φ`: the derived
tensor product of Tag 0FTG (1) with the bimodule `{}_A B_B`. -/
@[sga "5 IIIB 5.9" "more general"]
def derivedExtension : derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} B :=
  derivedTensorProduct (φ.toBimodule hφ)

/-- The pullback along the identity morphism of ringed sites is the identity functor. -/
def idPullbackFunctorIso : 𝟭 (DifferentialGradedModule.{u, u, u} A) ≅
    (idPullbackData.{u, u, u} (A := A)).functor :=
  NatIso.ofComponents (fun M => Iso.refl M) fun ψ =>
    (Category.comp_id ψ).trans ((idPullbackData_map ψ).symm.trans (Category.id_comp _).symm)

/-- The components of `idPullbackFunctorIso` are identities. -/
@[simp]
theorem idPullbackFunctorIso_hom_app (M : DifferentialGradedModule.{u, u, u} A) :
    (idPullbackFunctorIso (A := A)).hom.app M = 𝟙 M :=
  rfl

/-- The unit of the adjunction `- ⊗_A B ⊣ res_φ` of Tag 0FRP is `x ↦ x ⊗ 1`. -/
theorem extensionRestrictionAdjunction_unit_app (M : DifferentialGradedModule.{u, u, u} A) :
    (extensionRestrictionAdjunction φ hφ (extensionData φ hφ)).unit.app M =
      extensionUnit φ hφ (extensionData φ hφ) M := by
  change extensionUnit φ hφ (extensionData φ hφ) M ≫ (restriction φ hφ).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Extension of scalars along `φ`, written as the functor `ℳ ↦ f^*ℳ ⊗_A B` for the identity
morphism of ringed sites, is left adjoint to restriction of scalars. -/
def extensionAdjunction :
    pullbackTensorFunctor idPullbackData (extensionData φ hφ) ⊣ restriction.{u, u, u} φ hφ :=
  (extensionRestrictionAdjunction φ hφ (extensionData φ hφ)).ofNatIsoLeft
    ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (idPullbackFunctorIso (A := A)) (extensionData φ hφ).functor)

/-- The unit of `extensionAdjunction` is `x ↦ x ⊗ 1`. -/
theorem extensionAdjunction_unit_app (M : DifferentialGradedModule.{u, u, u} A) :
    (extensionAdjunction φ hφ).unit.app M = extensionUnit φ hφ (extensionData φ hφ) M := by
  change (extensionRestrictionAdjunction φ hφ (extensionData φ hφ)).unit.app M ≫
    (restriction φ hφ).map (𝟙 _ ≫ (extensionData φ hφ).functor.map (𝟙 M)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (extensionRestrictionAdjunction_unit_app φ hφ M)

/-- The adjunction `- ⊗_A B ⊣ res_φ`, descended to the homotopy categories. -/
def homotopyExtensionAdjunction :
    HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (extensionData φ hφ) ⊣
      homotopyRestriction.{u, u, u} φ hφ :=
  HomotopyCategory.descendAdjunction (extensionAdjunction φ hφ)
    (preservesHomotopic_restriction φ hφ)
    (preservesHomotopic_pullbackTensorFunctor idPullbackDataHomotopyExtension _)

/-- The unit of `homotopyExtensionAdjunction` at a module is the class of `x ↦ x ⊗ 1`. -/
theorem homotopyExtensionAdjunction_unit_app (M : DifferentialGradedModule.{u, u, u} A) :
    (homotopyExtensionAdjunction φ hφ).unit.app ((HomotopyCategory.quotient A).obj M) =
      (HomotopyCategory.quotient A).map (extensionUnit φ hφ (extensionData φ hφ) M) := by
  rw [← extensionAdjunction_unit_app]
  rfl

/-- The comparison `M ⊗^𝐋_A B ⟶ M ⊗_A B` of derived extension of scalars with extension of
scalars, natural in the object of `K(Mod(A, d))`. -/
def derivedExtensionCounit :
    toDerivedCategory.{u, u, u} A ⋙ derivedExtension φ hφ ⟶
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (extensionData φ hφ) ⋙
        toDerivedCategory.{u, u, u} B :=
  derivedPullbackTensorCounit idPullbackDataHomotopyExtension (extensionExactnessData φ hφ)

/-- Derived extension of scalars is a left derived functor of extension of scalars. -/
instance isLeftDerivedFunctor_derivedExtension :
    (derivedExtension φ hφ).IsLeftDerivedFunctor (derivedExtensionCounit φ hφ)
      (quasiIsomorphisms.{u, u, u} A) :=
  isLeftDerivedFunctor_derivedPullbackTensorCounit _ _

/-- On a flat and K-flat module the derived extension of scalars is the underived one. -/
theorem isIso_derivedExtensionCounit_app {P : DifferentialGradedModule.{u, u, u} A}
    (hP : (tensorGood (A := A)).IsGood P) :
    IsIso ((derivedExtensionCounit φ hφ).app ((HomotopyCategory.quotient A).obj P)) :=
  isIso_derivedPullbackTensorCounit_app_of_isGood _ _ hP

/-- Restriction of scalars on the derived categories is a right derived functor of restriction of
scalars, which inverts quasi-isomorphisms. -/
instance isRightDerivedFunctor_derivedRestriction :
    (derivedRestriction.{u, u, u} φ hφ).IsRightDerivedFunctor
      (derivedRestrictionIso.{u, u, u} φ hφ).inv (quasiIsomorphisms.{u, u, u} B) :=
  Functor.isRightDerivedFunctor_of_inverts (quasiIsomorphisms.{u, u, u} B) _
    (derivedRestrictionIso.{u, u, u} φ hφ)

/-- `res_φ ∘ (- ⊗^𝐋_A B)` is a left derived functor, computed on flat K-flat modules. This is the
absoluteness condition of `CategoryTheory.Adjunction.derived` on the left. -/
instance isLeftDerivedFunctor_derivedExtension_comp_derivedRestriction :
    (derivedExtension φ hφ ⋙ derivedRestriction.{u, u, u} φ hφ).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedExtensionCounit φ hφ) (derivedRestriction.{u, u, u} φ hφ))
      (quasiIsomorphisms.{u, u, u} A) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (quasiIsomorphisms.{u, u, u} A) (tensorGood (A := A)).objectProperty
    (tensorGood (A := A)).exists_objectProperty _
    (fun s hs hX hY => by
      have := isIso_pullbackTensor_map_of_objectProperty idPullbackDataHomotopyExtension
        (extensionExactnessData φ hφ) s hs hX hY
      exact (inferInstance : IsIso ((derivedRestriction.{u, u, u} φ hφ).map
        ((HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (extensionData φ hφ) ⋙
          toDerivedCategory.{u, u, u} B).map s))))
    (toDerivedCategory.{u, u, u} A) _ _ (fun Y hY => by
      have : IsIso ((derivedExtensionCounit φ hφ).app Y) :=
        isIso_derivedExtensionCounit_app φ hφ (P := Y.as) hY
      simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Category.id_comp]
      infer_instance)

/-- `(- ⊗^𝐋_A B) ∘ res_φ` is a right derived functor, being a localization lift. This is the
absoluteness condition of `CategoryTheory.Adjunction.derived` on the right. -/
instance isRightDerivedFunctor_derivedRestriction_comp_derivedExtension :
    (derivedRestriction.{u, u, u} φ hφ ⋙ derivedExtension φ hφ).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedRestrictionIso.{u, u, u} φ hφ).inv (derivedExtension φ hφ) ≫
        (Functor.associator _ _ _).hom) (quasiIsomorphisms.{u, u, u} B) :=
  Functor.isRightDerivedFunctor_of_inverts (quasiIsomorphisms.{u, u, u} B) _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedRestrictionIso.{u, u, u} φ hφ) (derivedExtension φ hφ))

/-- **Derived extension of scalars is left adjoint to restriction of scalars**
`D(A, d) ⇄ D(B, d)`: the adjunction `- ⊗_A B ⊣ res_φ` of Tag 0FRP, descended to the homotopy
categories, induces one between the derived functors. -/
def derivedExtensionAdjunction : derivedExtension φ hφ ⊣ derivedRestriction.{u, u, u} φ hφ :=
  (homotopyExtensionAdjunction φ hφ).derived (quasiIsomorphisms.{u, u, u} A)
    (quasiIsomorphisms.{u, u, u} B) (derivedExtensionCounit φ hφ)
    (derivedRestrictionIso.{u, u, u} φ hφ).inv

/-- The unit of the derived adjunction is compatible with the unit of the adjunction of
homotopy categories. -/
theorem derivedExtensionAdjunction_unit_app_comp (M : HomotopyCategory.{u, u, u} A) :
    (derivedExtensionAdjunction φ hφ).unit.app ((toDerivedCategory.{u, u, u} A).obj M) ≫
        (derivedRestriction.{u, u, u} φ hφ).map ((derivedExtensionCounit φ hφ).app M) =
      (toDerivedCategory.{u, u, u} A).map ((homotopyExtensionAdjunction φ hφ).unit.app M) ≫
        (derivedRestrictionIso.{u, u, u} φ hφ).inv.app
          ((HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
            (extensionData φ hφ)).obj M) :=
  (homotopyExtensionAdjunction φ hφ).derivedη_fac_app (quasiIsomorphisms.{u, u, u} A)
    (derivedExtensionCounit φ hφ) (derivedRestrictionIso.{u, u, u} φ hφ).inv M

/-- A quasi-isomorphism of differential graded modules becomes invertible in the derived
category. -/
private theorem isIso_toDerivedCategory_map_quotient_map
    {M N : DifferentialGradedModule.{u, u, u} A}
    (f : M ⟶ N) (hf : QuasiIso f.toHomologicalComplex) :
    IsIso ((toDerivedCategory.{u, u, u} A).map ((HomotopyCategory.quotient A).map f)) :=
  Localization.inverts _ (quasiIsomorphisms.{u, u, u} A) _
    ((quasiIsomorphisms_quotient_map_iff _).2 hf)

/-- At a flat and K-flat module `P`, the unit `P ⟶ res_φ (P ⊗^𝐋_A B)` of the derived adjunction
is invertible when `φ` is a quasi-isomorphism. -/
theorem isIso_derivedExtensionAdjunction_unit_app_of_isGood (hqis : φ.IsQuasiIso)
    {P : DifferentialGradedModule.{u, u, u} A} (hP : (tensorGood (A := A)).IsGood P) :
    IsIso ((derivedExtensionAdjunction φ hφ).unit.app
      ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj P))) := by
  have h₁ : IsIso ((toDerivedCategory.{u, u, u} A).map ((homotopyExtensionAdjunction φ hφ).unit.app
      ((HomotopyCategory.quotient A).obj P))) := by
    rw [homotopyExtensionAdjunction_unit_app]
    exact isIso_toDerivedCategory_map_quotient_map _
      (quasiIso_extensionUnit_of_isKFlat (A := (A : DifferentialGradedAlgebra.{u, u}
        (toRingCat X.J X.O))) hP.2 φ hφ hqis)
  have h₂ := isIso_derivedExtensionCounit_app φ hφ hP
  have h₃ : IsIso ((derivedExtensionAdjunction φ hφ).unit.app
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj P)) ≫
      (derivedRestriction.{u, u, u} φ hφ).map
        ((derivedExtensionCounit φ hφ).app ((HomotopyCategory.quotient A).obj P))) := by
    rw [derivedExtensionAdjunction_unit_app_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((derivedRestriction.{u, u, u} φ hφ).map
    ((derivedExtensionCounit φ hφ).app ((HomotopyCategory.quotient A).obj P)))

/-- When `φ` is a quasi-isomorphism the unit of the derived adjunction is invertible. -/
theorem isIso_derivedExtensionAdjunction_unit_app (hqis : φ.IsQuasiIso)
    (Y : derivedCategory.{u, u, u} A) :
    IsIso ((derivedExtensionAdjunction φ hφ).unit.app Y) := by
  obtain ⟨M, rfl⟩ := exists_toDerivedCategory_obj_eq A Y
  obtain ⟨P, p, hP, hp⟩ := (tensorGood (A := A)).exists_isGood M
  have hpi := isIso_toDerivedCategory_map_quotient_map p hp
  have := isIso_derivedExtensionAdjunction_unit_app_of_isGood φ hφ hqis hP
  exact (NatTrans.isIso_app_iff_of_iso (derivedExtensionAdjunction φ hφ).unit
    (asIso ((toDerivedCategory.{u, u, u} A).map ((HomotopyCategory.quotient A).map p)))).1 this

/-- When `φ` is a quasi-isomorphism the counit of the derived adjunction is invertible: by the
triangle identity restriction of scalars carries it to the inverse of a unit, and restriction of
scalars reflects isomorphisms. -/
theorem isIso_derivedExtensionAdjunction_counit_app (hqis : φ.IsQuasiIso)
    (Y : derivedCategory.{u, u, u} B) :
    IsIso ((derivedExtensionAdjunction φ hφ).counit.app Y) := by
  have : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  have := isIso_derivedExtensionAdjunction_unit_app φ hφ hqis
    ((derivedRestriction.{u, u, u} φ hφ).obj Y)
  have heq : inv ((derivedExtensionAdjunction φ hφ).unit.app
      ((derivedRestriction.{u, u, u} φ hφ).obj Y)) =
      (derivedRestriction.{u, u, u} φ hφ).map ((derivedExtensionAdjunction φ hφ).counit.app Y) :=
    IsIso.inv_eq_of_hom_inv_id ((derivedExtensionAdjunction φ hφ).right_triangle_components Y)
  refine isIso_of_isIso_derivedRestriction_map φ hφ _ ?_
  rw [← heq]
  infer_instance

/-- Let `(C, O)` be a ringed site and let `φ : A ⟶ B` be a homomorphism of sheaves of
differential graded `O`-algebras which induces an isomorphism on cohomology sheaves. Then derived
extension of scalars

`D(A, d) ⟶ D(B, d)`, `M ↦ M ⊗^𝐋_A B`

is an equivalence of categories.

The source's functor `M ↦ M ⊗^𝐋_A B` is defined only for a homomorphism `φ` preserving `1`,
since `B` is made a left `A`-module through `φ`; so `PreservesOne` is implicit in the
statement. -/
@[stacks 0FTZ]
theorem isEquivalence_derivedExtension
    {A B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (φ : A ⟶ B) (unital : φ.PreservesOne) (qis : φ.IsQuasiIso) :
    (derivedExtension φ unital).IsEquivalence :=
  have : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  isEquivalence_of_isIso_unit_derivedRestriction φ unital (derivedExtensionAdjunction φ unital)
    (isIso_derivedExtensionAdjunction_unit_app φ unital qis)

/-- The equivalence `D(A, d) ≌ D(B, d)` of Tag 0FTZ: derived extension of scalars, with
restriction of scalars as quasi-inverse. -/
def derivedExtensionEquivalence (hqis : φ.IsQuasiIso) :
    derivedCategory.{u, u, u} A ≌ derivedCategory.{u, u, u} B :=
  haveI := isIso_derivedExtensionAdjunction_unit_app φ hφ hqis
  haveI := isIso_derivedExtensionAdjunction_counit_app φ hφ hqis
  (derivedExtensionAdjunction φ hφ).toEquivalence

/-- The functor of the equivalence is derived extension of scalars. -/
@[simp]
theorem derivedExtensionEquivalence_functor (hqis : φ.IsQuasiIso) :
    (derivedExtensionEquivalence φ hφ hqis).functor = derivedExtension φ hφ :=
  rfl

/-- The quasi-inverse of the equivalence is restriction of scalars. -/
@[simp]
theorem derivedExtensionEquivalence_inverse (hqis : φ.IsQuasiIso) :
    (derivedExtensionEquivalence φ hφ hqis).inverse = derivedRestriction.{u, u, u} φ hφ :=
  rfl

/-- Restriction of scalars along a quasi-isomorphism is an equivalence of derived categories. -/
theorem isEquivalence_derivedRestriction (hqis : φ.IsQuasiIso) :
    (derivedRestriction.{u, u, u} φ hφ).IsEquivalence :=
  (derivedExtensionEquivalence φ hφ hqis).isEquivalence_inverse

end SheafOfModules.DifferentialGradedModule

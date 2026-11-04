module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDegreeZeroDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionQuasiCoherent
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestrictionComposite
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentRestrictScalars

/-!
# Quasi-coherence across `D(A, d) = D(O)` for an algebra concentrated in degree zero

Let `C` be a category with the chaotic topology, `R` a sheaf of rings on it and `(A, d)` a sheaf
of differential graded `R`-algebras concentrated in degree zero, identified with a presheaf of
commutative rings `O` (`SheafOfModules.DifferentialGradedModule.DegreeZero.Data`). The derived
category `D(A, d)` is then `D(O)`
(`SheafOfModules.DifferentialGradedModule.DegreeZero.derivedEquivalence`). Each side has its
subcategory of quasi-coherent objects: `QC(A, d)` of Differential Graded Sheaves, Definition
24.33.1 (Tag 0GZ9), cut out by the comparison maps `RΓ(V, K) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, K)` of
`D(A(U), d)`, and `QC(O)` of Cohomology on Sites (Tag 0GYV), cut out by the
comparison maps `RΓ(V, K) ⊗^𝐋_{O(V)} O(U) ⟶ RΓ(U, K)` of `D(O(U))`. This file shows that the
equivalence `D(A, d) ≌ D(O)` matches them.

The two comparison maps are not compared through the derived tensor products. Each is the
adjoint transpose of a restriction map, so it is invertible exactly when the restriction map is a
universal arrow for derived restriction of scalars
(`CategoryTheory.Functor.isUniversalArrow_iff_isIso`), and universal arrows are transported along
equivalences compatible with the two derived restrictions of scalars
(`CategoryTheory.Functor.isUniversalArrow_iff_of_iso`). The equivalences are, for each object `U`,
`D(A(U), d) ≌ D(O(U))`: the section algebra `A(U)` is `O(U)` placed in degree zero
(`sectionAlgebraHom`), and differential graded modules over a ring in degree zero are complexes
of modules over it (`DifferentialGradedModule.degreeZeroDerivedEquivalence`).

## Main definitions

* `DifferentialGradedModule.derivedRestrictionEquivalence`: derived restriction of scalars along
  mutually inverse homomorphisms of differential graded algebras is an equivalence.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.sectionAlgebraHom`: the isomorphism of
  differential graded algebras from `O(U)ᵐᵒᵖ` in degree zero to the section algebra `A(U)`, with
  inverse `sectionAlgebraInv`.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.sectionDerivedEquivalence`: the equivalence
  `D(A(U), d) ≌ D(O(U))`, for any model of the derived categories of `O(U)`-modules.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.sectionDerivedSquare`: its compatibility
  with derived restriction of scalars along `A(V) ⟶ A(U)` and `O(V) ⟶ O(U)`.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.sectionClassIso`: the class of the section
  module `M(U)` corresponds to the derived sections over `U` of the complex of `O`-modules of `M`.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.qcEquivalence`: **the equivalence
  `QC(A, d) ≌ QC(O)`**.

## Main results

* `SheafOfModules.DifferentialGradedModule.DegreeZero.sectionClassIso_restriction`: the
  identification of derived sections is compatible with the restriction maps.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.isQCModule_iff_isQC`: a differential graded
  module satisfies the condition of Tag 0GZ9 exactly when its complex of `O`-modules satisfies the
  condition of Tag 0GYV.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.qc_iff_isQC`: **`K ∈ QC(A, d)` exactly when
  its image in `D(O)` lies in `QC(O)`**, for any base-change datum.

## Implementation notes

Everything is stated at one universe: the site, the rings and the modules all live in `u`, which
is where both `Chaotic.QC` and `QC` are available together. The equivalences
`D(A(U), d) ≌ D(O(U))` and their compatibilities are stated for an arbitrary family of models
`[∀ U, HasDerivedCategory (ModuleCat (O.obj U))]`; the comparison with Tag 0GYV specializes them
to the model `HasDerivedCategory.standard` used by
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.RGamma`.

`O(U)` enters the degree-zero identification as the opposite ring `O(U)ᵐᵒᵖ` placed in degree
zero, through `DifferentialGradedAlgebra.IsOppositeAlgebra.opSelf`: a right differential graded
module over `O(U)ᵐᵒᵖ` in degree zero is a complex of left `O(U)`-modules, with no commutative ring
structure on `O(U)` to be chosen. The commutativity recorded in the data `D` is what makes
`O(U)ᵐᵒᵖ ⟶ A(U)` multiplicative.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

/-! ### Derived restriction of scalars along mutually inverse homomorphisms -/

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **Derived restriction of scalars along an isomorphism of differential graded algebras is an
equivalence**, with inverse the derived restriction along the inverse isomorphism. -/
def derivedRestrictionEquivalence (φ : A.Hom B) (ψ : B.Hom A) (h₁ : ψ.comp φ = A.idHom)
    (h₂ : φ.comp ψ = B.idHom) : derivedCategory' B ≌ derivedCategory' A :=
  CategoryTheory.Equivalence.mk (derivedRestriction φ) (derivedRestriction ψ)
    ((derivedRestrictionIdIso B).symm ≪≫ eqToIso (congrArg derivedRestriction h₂).symm ≪≫
      (derivedRestrictionComp ψ φ).symm)
    (derivedRestrictionComp φ ψ ≪≫ eqToIso (congrArg derivedRestriction h₁) ≪≫
      derivedRestrictionIdIso A)

/-- The functor of `derivedRestrictionEquivalence φ ψ h₁ h₂` is derived restriction of scalars
along `φ`. -/
@[simp]
theorem derivedRestrictionEquivalence_functor (φ : A.Hom B) (ψ : B.Hom A)
    (h₁ : ψ.comp φ = A.idHom) (h₂ : φ.comp ψ = B.idHom) :
    (derivedRestrictionEquivalence φ ψ h₁ h₂).functor = derivedRestriction φ := rfl

end DifferentialGradedModule

namespace SheafOfModules

namespace DifferentialGradedModule

namespace DegreeZero

open _root_.DifferentialGradedAlgebra

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing

/-- A ring, as an algebra over the universe-lifted integers. -/
@[instance_reducible]
def ringCatUliftIntAlgebra (X : RingCat.{u}) : Algebra (ULift.{u, 0} ℤ) X :=
  Stacks.uliftIntAlgebra X

attribute [local instance] ringCatUliftIntAlgebra

/-- The algebra map from the lifted integers to a ring sends `c` to the integer cast of
`c.down`. -/
theorem algebraMap_uliftInt_eq {T : Type u} [Ring T] [Algebra (ULift.{u, 0} ℤ) T]
    (c : ULift.{u, 0} ℤ) : algebraMap (ULift.{u, 0} ℤ) T c = ((c.down : ℤ) : T) := by
  rw [← map_intCast (algebraMap (ULift.{u, 0} ℤ) T) c.down]
  rfl

variable {C : Type u} [Category.{u} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u}}
  {A : SheafOfModules.DifferentialGradedAlgebra.{u, u} R} {O : Cᵒᵖ ⥤ RingCat.{u}} (D : Data A O)

/-- The sections `O(U)`, as a differential graded algebra over the lifted integers concentrated
in degree zero: the opposite ring of `O(U)`, whose right modules are the `O(U)`-modules. -/
abbrev zeroAlgebra (O : Cᵒᵖ ⥤ RingCat.{u}) (U : Cᵒᵖ) :
    _root_.DifferentialGradedAlgebra.{u, u} (ULift.{u, 0} ℤ) :=
  degreeZero (ULift.{u, 0} ℤ) (O.obj U)ᵐᵒᵖ

/-- The ring homomorphism `O(U)ᵐᵒᵖ ⟶ A(U)`, `b ↦ ψ b` placed in degree zero. -/
def sectionRingHom (U : Cᵒᵖ) : (O.obj U)ᵐᵒᵖ →+* A.toGradedAlgebra.totalSections U where
  toFun x := DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (D.ψ U x.unop)
  map_one' := by
    rw [MulOpposite.unop_one, D.ψ_one]
    exact DirectSum.of_zero_one _
  map_mul' x y := by
    rw [GradedAlgebra.of_mul_of_eq, MulOpposite.unop_mul, D.comm, D.ψ_mul]
    rfl
  map_zero' := by
    rw [MulOpposite.unop_zero, map_zero, map_zero]
  map_add' x y := by
    rw [MulOpposite.unop_add, map_add, map_add]

/-- `sectionRingHom D U` sends `x` to `D.ψ U x.unop` placed in degree zero. -/
theorem sectionRingHom_apply (U : Cᵒᵖ) (x : (O.obj U)ᵐᵒᵖ) :
    sectionRingHom D U x =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (D.ψ U x.unop) := rfl

/-- The ring homomorphism `sectionRingHom D U : O(U)ᵐᵒᵖ →+* A(U)` is bijective. -/
theorem sectionRingHom_bijective (U : Cᵒᵖ) : Function.Bijective (sectionRingHom D U) := by
  refine ⟨fun x y h => ?_, fun s => ?_⟩
  · have h' := DirectSum.of_injective (β := A.toGradedAlgebra.sectionsPiece U) 0 h
    exact MulOpposite.unop_injective ((D.ψ U).injective h')
  · induction s using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of i y =>
      by_cases hi : i = 0
      · subst hi
        exact ⟨MulOpposite.op ((D.ψ U).symm y), by
          rw [sectionRingHom_apply, MulOpposite.unop_op, AddEquiv.apply_symm_apply]⟩
      · have hy : y = 0 := (D.subsingleton i hi U).elim _ _
        subst hy
        exact ⟨0, by rw [map_zero, map_zero]⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

/-- The ring isomorphism `O(U)ᵐᵒᵖ ≃ A(U)`. -/
def sectionRingEquiv (U : Cᵒᵖ) : (O.obj U)ᵐᵒᵖ ≃+* A.toGradedAlgebra.totalSections U :=
  RingEquiv.ofBijective (sectionRingHom D U) (sectionRingHom_bijective D U)

/-- The ring isomorphism `sectionRingEquiv D U` agrees with `sectionRingHom D U`. -/
theorem sectionRingEquiv_apply (U : Cᵒᵖ) (x : (O.obj U)ᵐᵒᵖ) :
    sectionRingEquiv D U x = sectionRingHom D U x := rfl

include D in
/-- The differential of the section algebra `A(U)` vanishes when `A` is concentrated in degree
zero. -/
theorem sectionAlgebra_d_eq_zero (U : Cᵒᵖ) (s : (A.sectionAlgebra U).A) :
    (A.sectionAlgebra U).d s = 0 := by
  obtain ⟨x, rfl⟩ := (sectionRingHom_bijective D U).2 s
  rw [sectionRingHom_apply, SheafOfModules.DifferentialGradedAlgebra.sectionAlgebra_d_of]
  have h : (A.complex.d 0 (0 + 1)).val.app U (D.ψ U x.unop) = 0 :=
    (D.subsingleton (0 + 1) (by omega) U).elim _ _
  rw [h]
  exact map_zero _

/-- The degree-`n` part of `zeroAlgebra O U` is zero for `n ≠ 0`. -/
theorem zeroAlgebra_grading_eq_bot (U : Cᵒᵖ) {n : ℤ} (hn : n ≠ 0) :
    (zeroAlgebra O U).grading n = ⊥ :=
  degreeZeroGrading_eq_bot _ _ hn

/-- The degree-zero part of `zeroAlgebra O U` is everything. -/
theorem zeroAlgebra_grading_zero (U : Cᵒᵖ) : (zeroAlgebra O U).grading 0 = ⊤ :=
  degreeZeroGrading_zero _ _

/-- The differential of `zeroAlgebra O U` is zero. -/
theorem zeroAlgebra_d_apply (U : Cᵒᵖ) (x : (zeroAlgebra O U).A) : (zeroAlgebra O U).d x = 0 :=
  rfl

/-- The algebra homomorphism `O(U)ᵐᵒᵖ ⟶ A(U)` over the lifted integers. -/
def sectionAlgHom (U : Cᵒᵖ) : (zeroAlgebra O U).A →ₐ[ULift.{u, 0} ℤ] (A.sectionAlgebra U).A where
  toRingHom := sectionRingHom D U
  commutes' c := by
    rw [algebraMap_uliftInt_eq, algebraMap_uliftInt_eq]
    exact map_intCast (sectionRingHom D U) c.down

/-- The algebra homomorphism `sectionAlgHom D U` agrees with `sectionRingHom D U`. -/
theorem sectionAlgHom_apply (U : Cᵒᵖ) (x : (zeroAlgebra O U).A) :
    sectionAlgHom D U x = sectionRingHom D U x := rfl

/-- The inverse algebra homomorphism `A(U) ⟶ O(U)ᵐᵒᵖ` over the lifted integers. -/
def sectionAlgInv (U : Cᵒᵖ) : (A.sectionAlgebra U).A →ₐ[ULift.{u, 0} ℤ] (zeroAlgebra O U).A where
  toRingHom := (sectionRingEquiv D U).symm.toRingHom
  commutes' c := by
    rw [algebraMap_uliftInt_eq, algebraMap_uliftInt_eq]
    exact map_intCast (sectionRingEquiv D U).symm.toRingHom c.down

/-- The algebra homomorphism `sectionAlgInv D U` agrees with the inverse of
`sectionRingEquiv D U`. -/
theorem sectionAlgInv_apply (U : Cᵒᵖ) (s : (A.sectionAlgebra U).A) :
    sectionAlgInv D U s = (sectionRingEquiv D U).symm s := rfl

/-- `sectionAlgHom D U` is a left inverse of `sectionAlgInv D U`. -/
theorem sectionAlgHom_sectionAlgInv (U : Cᵒᵖ) (s : (A.sectionAlgebra U).A) :
    sectionAlgHom D U (sectionAlgInv D U s) = s :=
  (sectionRingEquiv D U).apply_symm_apply s

/-- `sectionAlgInv D U` is a left inverse of `sectionAlgHom D U`. -/
theorem sectionAlgInv_sectionAlgHom (U : Cᵒᵖ) (x : (zeroAlgebra O U).A) :
    sectionAlgInv D U (sectionAlgHom D U x) = x :=
  (sectionRingEquiv D U).symm_apply_apply x

/-- **The sections of `O` over `U`, in degree zero, are the section algebra `A(U)`**: the
homomorphism of differential graded algebras `O(U)ᵐᵒᵖ ⟶ A(U)`. -/
def sectionAlgebraHom (U : Cᵒᵖ) : (zeroAlgebra O U).Hom (A.sectionAlgebra U) where
  toAlgebraHom := sectionAlgHom D U
  map_grading n x hx := by
    by_cases hn : n = 0
    · subst hn
      exact ⟨D.ψ U (MulOpposite.unop x), rfl⟩
    · rw [zeroAlgebra_grading_eq_bot U hn, Submodule.mem_bot] at hx
      have h0 : sectionAlgHom D U x = 0 := by
        rw [hx]
        exact map_zero (sectionAlgHom D U)
      rw [h0]
      exact Submodule.zero_mem _
  map_d x := by
    rw [sectionAlgebra_d_eq_zero D U, zeroAlgebra_d_apply]
    exact map_zero (sectionAlgHom D U)

/-- The inverse homomorphism of differential graded algebras `A(U) ⟶ O(U)ᵐᵒᵖ`. -/
def sectionAlgebraInv (U : Cᵒᵖ) : (A.sectionAlgebra U).Hom (zeroAlgebra O U) where
  toAlgebraHom := sectionAlgInv D U
  map_grading n s hs := by
    by_cases hn : n = 0
    · subst hn
      rw [zeroAlgebra_grading_zero]
      exact Submodule.mem_top
    · obtain ⟨y, rfl⟩ := hs
      have hy : y = 0 := (D.subsingleton n hn U).elim _ _
      have h0 : sectionAlgInv D U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n y) = 0 := by
        rw [hy, map_zero]
        exact map_zero (sectionAlgInv D U)
      rw [h0]
      exact Submodule.zero_mem _
  map_d s := by
    rw [sectionAlgebra_d_eq_zero D U, zeroAlgebra_d_apply]
    exact map_zero (sectionAlgInv D U)

/-- Homomorphisms of differential graded algebras are equal when their underlying algebra
homomorphisms are. -/
private theorem hom_eq_of_toAlgebraHom_eq {R : Type u} [CommRing R]
    {A B : _root_.DifferentialGradedAlgebra.{u, u} R} {φ ψ : A.Hom B}
    (h : φ.toAlgebraHom = ψ.toAlgebraHom) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- `sectionAlgebraHom D U` followed by `sectionAlgebraInv D U` is the identity of
`zeroAlgebra O U`. -/
theorem sectionAlgebraInv_comp_hom (U : Cᵒᵖ) :
    (sectionAlgebraInv D U).comp (sectionAlgebraHom D U) = (zeroAlgebra O U).idHom :=
  hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun x => sectionAlgInv_sectionAlgHom D U x)

/-- `sectionAlgebraInv D U` followed by `sectionAlgebraHom D U` is the identity of the section
algebra `A(U)`. -/
theorem sectionAlgebraHom_comp_inv (U : Cᵒᵖ) :
    (sectionAlgebraHom D U).comp (sectionAlgebraInv D U) = (A.sectionAlgebra U).idHom :=
  hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun s => sectionAlgHom_sectionAlgInv D U s)

/-! ### The derived category of a section algebra -/

attribute [local instance] IsOppositeAlgebra.opSelf

section Derived

variable [hD : ∀ U : Cᵒᵖ, HasDerivedCategory.{w} (ModuleCat.{u} (O.obj U))]

/-- **The derived category of the section algebra `A(U)` is the derived category of
`O(U)`-modules**: derived restriction of scalars along `O(U)ᵐᵒᵖ ≅ A(U)`, followed by the
identification of differential graded modules over a ring in degree zero with complexes of
modules over it. -/
def sectionDerivedEquivalence (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.derivedCategory' (A.sectionAlgebra U) ≌
      DerivedCategory (ModuleCat.{u} (O.obj U)) :=
  (_root_.DifferentialGradedModule.derivedRestrictionEquivalence (sectionAlgebraHom D U)
      (sectionAlgebraInv D U) (sectionAlgebraInv_comp_hom D U)
      (sectionAlgebraHom_comp_inv D U)).trans
    (_root_.DifferentialGradedModule.degreeZeroDerivedEquivalence (R := ULift.{u, 0} ℤ)
      (A := O.obj U))

end Derived

/-- The chain-level functor underlying `sectionDerivedEquivalence`: restriction of scalars along
`O(U)ᵐᵒᵖ ≅ A(U)`, followed by taking homogeneous components. -/
abbrev sectionComplexFunctor (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule (A.sectionAlgebra U) ⥤
      CochainComplex (ModuleCat.{u} (O.obj U)) ℤ :=
  _root_.DifferentialGradedModule.restrictScalarsFunctor (sectionAlgebraHom D U) ⋙
    _root_.DifferentialGradedModule.degreeZeroComponentFunctor (ULift.{u, 0} ℤ) (O.obj U)

section Derived

variable [hD : ∀ U : Cᵒᵖ, HasDerivedCategory.{w} (ModuleCat.{u} (O.obj U))]

/-- `sectionDerivedEquivalence` read through the localizations: the class of a differential
graded `A(U)`-module goes to the class of its complex of homogeneous components. -/
def sectionDerivedFac (U : Cᵒᵖ) :
    (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U) ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q) ⋙
      (sectionDerivedEquivalence D U).functor ≅
    sectionComplexFunctor D U ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (_root_.DifferentialGradedModule.derivedRestrictionFactorization
            (sectionAlgebraHom D U))
          (_root_.DifferentialGradedModule.degreeZeroDerivedEquivalence (R := ULift.{u, 0} ℤ)
            (A := O.obj U)).functor ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso (sectionAlgebraHom D U))
      ((_root_.DifferentialGradedModule.quasiIsomorphisms' (zeroAlgebra O U)).Q ⋙
        (_root_.DifferentialGradedModule.degreeZeroDerivedEquivalence (R := ULift.{u, 0} ℤ)
          (A := O.obj U)).functor) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (_root_.DifferentialGradedModule.restrictScalarsFunctor (sectionAlgebraHom D U))
      ((Functor.associator _ _ _).symm ≪≫
        _root_.DifferentialGradedModule.degreeZeroDerivedComponentIso (R := ULift.{u, 0} ℤ)
          (A := O.obj U)) ≪≫
    (Functor.associator _ _ _).symm

end Derived

/-! ### The sections of a module, read over `O(U)` -/

section Sections

variable (M : DifferentialGradedModule.{u, u, u} A) (U : Cᵒᵖ)

/-- An element of a homogeneous component of the section module `M(U)`, read in `M(U)`. -/
def sectionComponentVal {n : ℤ}
    (x : ((sectionComplexFunctor D U).obj (M.sectionModule U)).X n) : M.totalSections U :=
  x.1

/-- Elements of a homogeneous component of `M(U)` are equal when they are equal in `M(U)`. -/
theorem sectionComponent_ext {n : ℤ}
    {x y : ((sectionComplexFunctor D U).obj (M.sectionModule U)).X n}
    (h : sectionComponentVal D M U x = sectionComponentVal D M U y) : x = y :=
  Subtype.ext h

/-- Scalar multiplication by `b : O(U)` on a homogeneous component of `M(U)` is the action of
`D.ψ U b`, placed in degree zero. -/
theorem sectionComponentVal_smul (n : ℤ) (b : O.obj U)
    (x : ((sectionComplexFunctor D U).obj (M.sectionModule U)).X n) :
    sectionComponentVal D M U (b • x) =
      M.act U (sectionComponentVal D M U x)
        (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (D.ψ U b)) :=
  rfl

/-- A degree-`n` section of `M` over `U`, as an element of the degree-`n` homogeneous component of
the section module `M(U)`. -/
def sectionComponentMk {n : ℤ} (y : M.sectionsPiece U n) :
    ((sectionComplexFunctor D U).obj (M.sectionModule U)).X n :=
  (⟨DirectSum.of (M.sectionsPiece U) n y,
    Stacks.ExternalGrading.of_mem_intSummand (M.sectionsPiece U) n y⟩ :
      Stacks.ExternalGrading.intSummand (M.sectionsPiece U) n)

/-- `sectionComponentMk D M U y`, read in `M(U)`, is `y` placed in degree `n`. -/
theorem sectionComponentVal_mk {n : ℤ} (y : M.sectionsPiece U n) :
    sectionComponentVal D M U (sectionComponentMk D M U y) =
      DirectSum.of (M.sectionsPiece U) n y :=
  rfl

/-- The degree-`n` sections of `M` over `U` are the degree-`n` homogeneous component of the
section module `M(U)`, as `O(U)`-modules. -/
def sectionPieceEquiv (n : ℤ) :
    ((toComplex D M).X n).obj U ≃ₗ[O.obj U]
      ((sectionComplexFunctor D U).obj (M.sectionModule U)).X n where
  toFun y := sectionComponentMk D M U (n := n) y
  invFun x := sectionComponentVal D M U x n
  map_add' y y' := sectionComponent_ext D M U (map_add (DirectSum.of (M.sectionsPiece U) n) y y')
  map_smul' b y := by
    refine sectionComponent_ext D M U ?_
    exact (of_gradedCast (T := M.sectionsPiece U) (add_zero n)
      ((M.mul n 0).app U y (D.ψ U b))).trans
      ((SheafOfModules.DifferentialGradedModule.actOn_of M U n 0 y (D.ψ U b)).symm.trans
        ((DFunLike.congr_fun (SheafOfModules.DifferentialGradedModule.act_of M U n y) _).symm.trans
          (sectionComponentVal_smul D M U n b (sectionComponentMk D M U (n := n) y)).symm))
  left_inv y := by
    change (DirectSum.of (M.sectionsPiece U) n y) n = y
    exact DirectSum.of_eq_same (β := M.sectionsPiece U) n y
  right_inv x := sectionComponent_ext D M U
    (Stacks.ExternalGrading.of_coord_eq (M.sectionsPiece U) (i := n) x)

/-- `sectionPieceEquiv D M U n y`, read in `M(U)`, is `y` placed in degree `n`. -/
theorem sectionComponentVal_sectionPieceEquiv (n : ℤ) (y : ((toComplex D M).X n).obj U) :
    sectionComponentVal D M U (sectionPieceEquiv D M U n y) =
      DirectSum.of (M.sectionsPiece U) n y :=
  rfl

/-- The inverse of `sectionPieceEquiv D M U n` takes the degree-`n` coordinate in `M(U)`. -/
theorem sectionPieceEquiv_symm_apply (n : ℤ)
    (x : ((sectionComplexFunctor D U).obj (M.sectionModule U)).X n) :
    (sectionPieceEquiv D M U n).symm x = sectionComponentVal D M U x n :=
  rfl

/-- **The complex of `O(U)`-modules of the sections of `M` over `U` is the complex of
homogeneous components of the section module `M(U)`.** -/
def sectionComplexIso :
    ((PresheafOfModules.evaluation O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (toComplex D M) ≅
      (sectionComplexFunctor D U).obj (M.sectionModule U) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (sectionPieceEquiv D M U n).toModuleIso)
    (by
      rintro i _ rfl
      rw [show ((sectionComplexFunctor D U).obj (M.sectionModule U)).d i (i + 1) =
          _root_.DifferentialGradedModule.degreeZeroComplexDiff _ i from
        _root_.DifferentialGradedModule.degreeZeroComplex_d_self _ i]
      ext y
      exact sectionComponent_ext D M U (M.sectionModule_d_of U i y))

end Sections

/-! ### Restriction along a morphism of the site -/

section Restriction

variable {U V : Cᵒᵖ}

/-- The ring homomorphisms `O(V)ᵐᵒᵖ ⟶ A(V) ⟶ A(U)` and `O(V)ᵐᵒᵖ ⟶ O(U)ᵐᵒᵖ ⟶ A(U)` agree. -/
theorem sectionRestriction_sectionAlgHom (a : V ⟶ U) (x : (zeroAlgebra O V).A) :
    (A.sectionRestriction a).toAlgebraHom (sectionAlgHom D V x) =
      sectionAlgHom D U (MulOpposite.op (O.map a (MulOpposite.unop x))) := by
  rw [sectionAlgHom_apply, sectionRingHom_apply,
    SheafOfModules.DifferentialGradedAlgebra.sectionRestriction_of, sectionAlgHom_apply,
    sectionRingHom_apply, MulOpposite.unop_op, D.ψ_map]
  rfl

/-- An element of a homogeneous component of `(sectionComplexFunctor D U).obj N`, read in `N`. -/
def componentVal (N : _root_.DifferentialGradedModule (A.sectionAlgebra U)) {n : ℤ}
    (x : ((sectionComplexFunctor D U).obj N).X n) : N.M :=
  x.1

/-- Elements of a homogeneous component of `(sectionComplexFunctor D U).obj N` are equal when
they are equal in `N`. -/
theorem componentVal_ext (N : _root_.DifferentialGradedModule (A.sectionAlgebra U)) {n : ℤ}
    {x y : ((sectionComplexFunctor D U).obj N).X n}
    (h : componentVal D N x = componentVal D N y) : x = y :=
  Subtype.ext h

/-- Scalar multiplication by `b : O(U)` on a homogeneous component of
`(sectionComplexFunctor D U).obj N` is the right action of `sectionAlgHom D U (op b)` on `N`. -/
theorem componentVal_smul (N : _root_.DifferentialGradedModule (A.sectionAlgebra U)) {n : ℤ}
    (b : O.obj U) (x : ((sectionComplexFunctor D U).obj N).X n) :
    componentVal D N (b • x) =
      MulOpposite.op (sectionAlgHom D U (MulOpposite.op b)) • componentVal D N x :=
  rfl

/-- The differential of the complex of homogeneous components of a differential graded module
over `Tᵐᵒᵖ` in degree zero is the differential of the module. -/
theorem degreeZeroComplex_d_val {T : Type u} [Ring T] [Algebra (ULift.{u, 0} ℤ) T]
    (N : _root_.DifferentialGradedModule (degreeZero (ULift.{u, 0} ℤ) Tᵐᵒᵖ)) (i : ℤ)
    (x : (_root_.DifferentialGradedModule.degreeZeroComplex (A := T) N).X i) :
    ((_root_.DifferentialGradedModule.degreeZeroComplex (A := T) N).d i (i + 1) x).1 = N.d x.1 := by
  rw [_root_.DifferentialGradedModule.degreeZeroComplex_d_self]
  rfl

/-- The square of restrictions of scalars on homogeneous components, in one degree: restricting
along `A(V) ⟶ A(U)` and reading over `O(V)` is reading over `O(U)` and restricting along
`O(V) ⟶ O(U)`. -/
def componentRestrictEquiv (a : V ⟶ U) (N : _root_.DifferentialGradedModule (A.sectionAlgebra U))
    (n : ℤ) :
    ((sectionComplexFunctor D V).obj
        ((_root_.DifferentialGradedModule.restrictScalarsFunctor (A.sectionRestriction a)).obj
          N)).X n ≃ₗ[O.obj V]
      (((ModuleCat.restrictScalars (O.map a).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((sectionComplexFunctor D U).obj N)).X n where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' b x := by
    refine componentVal_ext D N (n := n) ?_
    exact congrArg (fun s => MulOpposite.op s • componentVal D N (n := n) x)
      (sectionRestriction_sectionAlgHom D a (MulOpposite.op b))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The square of restrictions of scalars**, on complexes of homogeneous components. -/
def sectionComplexSquare (a : V ⟶ U) :
    _root_.DifferentialGradedModule.restrictScalarsFunctor (A.sectionRestriction a) ⋙
        sectionComplexFunctor D V ≅
      sectionComplexFunctor D U ⋙
        (ModuleCat.restrictScalars (O.map a).hom).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents
    (fun N => HomologicalComplex.Hom.isoOfComponents
      (fun n => (componentRestrictEquiv D a N n).toModuleIso)
      (by
        rintro i _ rfl
        ext x
        refine componentVal_ext D N (n := i + 1) ?_
        exact (degreeZeroComplex_d_val
          ((_root_.DifferentialGradedModule.restrictScalarsFunctor (sectionAlgebraHom D U)).obj N)
            i x).trans
          (degreeZeroComplex_d_val
            ((_root_.DifferentialGradedModule.restrictScalarsFunctor (sectionAlgebraHom D V)).obj
              ((_root_.DifferentialGradedModule.restrictScalarsFunctor
                (A.sectionRestriction a)).obj N)) i x).symm))
    (fun f => by
      ext n x
      rfl)

section Derived

variable [hD : ∀ U : Cᵒᵖ, HasDerivedCategory.{w} (ModuleCat.{u} (O.obj U))]

/-- Derived restriction of scalars along `A(V) ⟶ A(U)`, read through the localizations. -/
def derivedRestrictionSectionFac (a : V ⟶ U) :
    _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U) ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q ⋙
          _root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a) ≅
      _root_.DifferentialGradedModule.restrictScalarsFunctor (A.sectionRestriction a) ⋙
        _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V) ⋙
          (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q :=
  Functor.isoWhiskerLeft _
      (_root_.DifferentialGradedModule.derivedRestrictionFactorization (A.sectionRestriction a)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso (A.sectionRestriction a))
      _ ≪≫
    Functor.associator _ _ _

/-- The square of derived categories attached to `a : V ⟶ U`, on the image of a differential
graded `A(U)`-module. -/
def sectionDerivedSquareAux (a : V ⟶ U) :
    _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U) ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q ⋙
          _root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a) ⋙
            (sectionDerivedEquivalence D V).functor ≅
      _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U) ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q ⋙
          (sectionDerivedEquivalence D U).functor ⋙
            (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategory :=
  Functor.isoWhiskerRight (derivedRestrictionSectionFac a)
      (sectionDerivedEquivalence D V).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sectionDerivedFac D V) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sectionComplexSquare D a) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sectionDerivedFac D U).symm _

/-- **The square of derived categories attached to `a : V ⟶ U`**: derived restriction of scalars
along `A(V) ⟶ A(U)` corresponds to derived restriction of scalars along `O(V) ⟶ O(U)`. -/
def sectionDerivedSquare (a : V ⟶ U) :
    _root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a) ⋙
        (sectionDerivedEquivalence D V).functor ≅
      (sectionDerivedEquivalence D U).functor ⋙
        (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategory :=
  Localization.liftNatIso
    (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q
    (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)) _ _ _ _
    (h₁ := Localization.Lifting.compLeft _ _ _) (h₂ := Localization.Lifting.compLeft _ _ _)
    (CategoryTheory.Quotient.natIsoLift _ (sectionDerivedSquareAux D a))

/-- On the class of a differential graded `A(U)`-module `N`, `sectionDerivedSquare D a` is
`sectionDerivedSquareAux D a` at `N`. -/
theorem sectionDerivedSquare_hom_app (a : V ⟶ U)
    (N : _root_.DifferentialGradedModule (A.sectionAlgebra U)) :
    (sectionDerivedSquare D a).hom.app
        ((_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q.obj
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj N)) =
      (sectionDerivedSquareAux D a).hom.app N := by
  simp [sectionDerivedSquare]

end Derived

section Derived

variable [hD : ∀ U : Cᵒᵖ, HasDerivedCategory.{w} (ModuleCat.{u} (O.obj U))]

/-- The component of `derivedRestrictionSectionFac a` at `N`, as the composite of the
factorization of derived restriction of scalars and the restriction of scalars on homotopy
categories. -/
theorem derivedRestrictionSectionFac_hom_app (a : V ⟶ U)
    (N : _root_.DifferentialGradedModule (A.sectionAlgebra U)) :
    (derivedRestrictionSectionFac a).hom.app N =
      (_root_.DifferentialGradedModule.derivedRestrictionFactorization
          (A.sectionRestriction a)).hom.app
        ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).obj N) ≫
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
        ((_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso
          (A.sectionRestriction a)).hom.app N) := by
  simp [derivedRestrictionSectionFac]

/-- The component of `sectionDerivedSquareAux D a` at `N`, as the composite built from
`derivedRestrictionSectionFac a`, `sectionDerivedFac D V`, `sectionComplexSquare D a`, the
factorization of derived restriction of scalars along `O(V) ⟶ O(U)` and `sectionDerivedFac D U`. -/
theorem sectionDerivedSquareAux_hom_app (a : V ⟶ U)
    (N : _root_.DifferentialGradedModule (A.sectionAlgebra U)) :
    (sectionDerivedSquareAux D a).hom.app N =
      (sectionDerivedEquivalence D V).functor.map ((derivedRestrictionSectionFac a).hom.app N) ≫
        (sectionDerivedFac D V).hom.app
          ((_root_.DifferentialGradedModule.restrictScalarsFunctor (A.sectionRestriction a)).obj
            N) ≫
        DerivedCategory.Q.map ((sectionComplexSquare D a).hom.app N) ≫
        (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategoryFactors.inv.app
          ((sectionComplexFunctor D U).obj N) ≫
        (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategory.map
          ((sectionDerivedFac D U).inv.app N) := by
  simp [sectionDerivedSquareAux]

end Derived

end Restriction

/-! ### Derived sections and derived restriction maps -/

section Bookkeeping

universe s₁ t₁

variable {𝔼 : Type t₁} [Category.{s₁} 𝔼]

/-- In a category, two composites agree given two commuting squares, a commuting square of
composites and two cancelling pairs. This is the bookkeeping behind
`sectionClassIso_restriction`; stating it over an abstract category is what lets `exact` supply
the definitionally equal spellings of the objects involved. -/
theorem restriction_chase {x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ : 𝔼}
    {β₁ : x₀ ⟶ x₁} {βd : x₁ ⟶ x₂} {fV' : x₂ ⟶ x₃} {q₁ : x₃ ⟶ x₄} {ι₁ : x₄ ⟶ x₅}
    {r₁ : x₅ ⟶ x₆} {e : x₆ ⟶ x₈} {r₂ : x₆ ⟶ x₅} {r₃ : x₅ ⟶ x₇} {r₄ : x₇ ⟶ x₈}
    {eV : x₀ ⟶ y₃} {fV : x₀ ⟶ y₁} {qV : y₁ ⟶ y₂} {mi : y₂ ⟶ y₃} {m : y₃ ⟶ y₂} {qr : y₂ ⟶ y₄}
    {ι₂ : y₄ ⟶ x₇} {βs : x₀ ⟶ x₂} {qs : y₁ ⟶ x₃} {q₃ : x₄ ⟶ y₄}
    (h₁ : β₁ ≫ βd = βs) (h₂ : βs ≫ fV' = fV ≫ qs) (h₃ : ι₁ ≫ r₃ = q₃ ≫ ι₂)
    (h₄ : qs ≫ q₁ ≫ q₃ = qV ≫ qr) (h₅ : r₁ ≫ r₂ = 𝟙 x₅) (h₆ : mi ≫ m = 𝟙 y₂)
    (he : e = r₂ ≫ r₃ ≫ r₄) (heV : eV = fV ≫ qV ≫ mi) :
    (β₁ ≫ βd ≫ fV' ≫ q₁ ≫ ι₁ ≫ r₁) ≫ e = eV ≫ m ≫ qr ≫ ι₂ ≫ r₄ := by
  subst he heV
  simp only [Category.assoc]
  rw [reassoc_of% h₅, reassoc_of% h₃, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₄,
    reassoc_of% h₆]

/-- A functor applied to a composite with a cancelling pair at the end. -/
theorem map_comp_map_comp_map_eq_of_comp_eq_id {𝔸 : Type*} [Category 𝔸] (F : 𝔸 ⥤ 𝔼)
    {a b c : 𝔸} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ b} (hgh : g ≫ h = 𝟙 b) :
    F.map f ≫ F.map g ≫ F.map h = F.map f := by
  rw [← F.map_comp g h, hgh, F.map_id, Category.comp_id]

/-- A functor applied to an equation between composites of three and of two morphisms. -/
theorem map_comp_three_eq {𝔸 : Type*} [Category 𝔸] (F : 𝔸 ⥤ 𝔼) {a₀ a₁ a₂ a₃ : 𝔸}
    {f₁ : a₀ ⟶ a₁} {f₂ : a₁ ⟶ a₂} {f₃ : a₂ ⟶ a₃} {b : 𝔸} {g₁ : a₀ ⟶ b} {g₂ : b ⟶ a₃}
    (h : f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂) :
    F.map f₁ ≫ F.map f₂ ≫ F.map f₃ = F.map g₁ ≫ F.map g₂ := by
  rw [← F.map_comp, ← F.map_comp, h, F.map_comp]

end Bookkeeping

/-- The degree-`n` coordinate of the restriction of `s : M(V)` along `a` is the restriction of
the degree-`n` coordinate of `s`. -/
theorem sectionRestrictAdd_apply (M : DifferentialGradedModule.{u, u, u} A) {U V : Cᵒᵖ}
    (a : V ⟶ U) (s : M.totalSections V) (n : ℤ) :
    M.sectionRestrictAdd a s n = (M.complex.X n).val.map a (s n) :=
  DirectSum.map_apply _ n s

section DerivedSections

variable [hD : ∀ U : Cᵒᵖ, HasDerivedCategory.{w} (ModuleCat.{u} (O.obj U))]
  (M : DifferentialGradedModule.{u, u, u} A)

/-- **The derived sections of the complex of `O`-modules of `M` over `U` are the class of the
section module `M(U)`**, read through `D(A(U), d) ≌ D(O(U))`. -/
def sectionClassIso (U : Cᵒᵖ) :
    (sectionDerivedEquivalence D U).functor.obj (Chaotic.sectionClass M U) ≅
      (PresheafOfModules.evaluation O U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (toComplex D M)) :=
  (sectionDerivedFac D U).app (M.sectionModule U) ≪≫
    DerivedCategory.Q.mapIso (sectionComplexIso D M U).symm ≪≫
    ((PresheafOfModules.evaluation O U).mapDerivedCategoryFactors.app (toComplex D M)).symm

variable {U V : Cᵒᵖ}

omit hD in
/-- On complexes, restriction of sections of the section modules is restriction of sections of
the complex of `O`-modules: the chain-level square behind `sectionClassIso_restriction`. -/
theorem sectionComplexIso_restriction (a : V ⟶ U) :
    (sectionComplexFunctor D V).map (M.sectionModuleRestriction a) ≫
        (sectionComplexSquare D a).hom.app (M.sectionModule U) ≫
        ((ModuleCat.restrictScalars (O.map a).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (sectionComplexIso D M U).inv =
      (sectionComplexIso D M V).inv ≫
        (NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
          (ComplexShape.up ℤ)).app (toComplex D M) := by
  ext n x
  exact sectionRestrictAdd_apply M a (sectionComponentVal D M V x) n

/-- **The identification of derived sections is compatible with the restriction maps**: through
`sectionClassIso` and the square `sectionDerivedSquare`, the image in `D(A(V), d)` of restriction
of sections `M(V) ⟶ M(U)` is the derived restriction map of the complex of `O`-modules of `M`. -/
theorem sectionClassIso_restriction (a : V ⟶ U) :
    ((sectionDerivedEquivalence D V).functor.map (Chaotic.derivedSectionRestriction M a) ≫
        (sectionDerivedSquare D a).hom.app (Chaotic.sectionClass M U)) ≫
      (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategory.map
        (sectionClassIso D M U).hom =
    (sectionClassIso D M V).hom ≫
      (PresheafOfModules.evaluation O V).mapDerivedCategoryFactors.hom.app (toComplex D M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
        (ComplexShape.up ℤ)).app (toComplex D M)) ≫
      (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategoryFactors.inv.app
        (((PresheafOfModules.evaluation O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (toComplex D M)) ≫
      (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategory.map
        ((PresheafOfModules.evaluation O U).mapDerivedCategoryFactors.inv.app (toComplex D M)) := by
  rw [sectionDerivedSquare_hom_app, sectionDerivedSquareAux_hom_app]
  have h₁ : (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
        (M.sectionModuleRestriction a)) =
      Chaotic.derivedSectionRestriction M a ≫
        (derivedRestrictionSectionFac a).hom.app (M.sectionModule U) := by
    simp only [Chaotic.derivedSectionRestriction, derivedRestrictionSectionFac_hom_app,
      Category.assoc, Iso.inv_hom_id_app_assoc]
    exact (map_comp_map_comp_map_eq_of_comp_eq_id
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q
      (Iso.inv_hom_id_app (_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso
        (A.sectionRestriction a)) (M.sectionModule U))).symm
  have h₄ := map_comp_three_eq DerivedCategory.Q (sectionComplexIso_restriction D M a)
  refine restriction_chase (r₂ := (ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategory.map
      ((sectionDerivedFac D U).hom.app (M.sectionModule U)))
    (((sectionDerivedEquivalence D V).functor.map_comp _ _).symm.trans
      (congrArg _ h₁.symm))
    ((sectionDerivedFac D V).hom.naturality (M.sectionModuleRestriction a))
    ((ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategoryFactors.inv.naturality
      (sectionComplexIso D M U).inv).symm h₄ ?_ (Iso.inv_hom_id_app _ _) ?_ rfl
  · exact ((ModuleCat.restrictScalars (O.map a).hom).mapDerivedCategory.mapIso
      ((sectionDerivedFac D U).app (M.sectionModule U))).inv_hom_id
  · simp only [sectionClassIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      CategoryTheory.Functor.map_comp]
    rfl

end DerivedSections

/-! ### Quasi-coherence on the two sides -/

section QuasiCoherent

open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
  Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars

variable (bc : BaseChangeData.{u} O)

/-- **The comparison map of a differential graded module along `a` is invertible exactly when
the comparison map of its complex of `O`-modules is.** Both are adjoint transposes of restriction
maps, so each is invertible exactly when its restriction map is a universal arrow for derived
restriction of scalars; the two restriction maps correspond under
`D(A(U), d) ≌ D(O(U))`, compatibly with derived restriction of scalars. -/
theorem isIso_sectionComparison_iff (M : DifferentialGradedModule.{u, u, u} A) {U V : Cᵒᵖ}
    (a : V ⟶ U) :
    IsIso (Chaotic.sectionComparison M a) ↔
      IsIso (comparison.{u} bc a (DerivedCategory.Q.obj (toComplex D M))) := by
  let : ∀ U : Cᵒᵖ, HasDerivedCategory (ModuleCat.{u} (O.obj U)) :=
    fun U => HasDerivedCategory.standard _
  rw [isIso_comparison_iff_isUniversalArrow, restrictionMap_Q]
  refine (Functor.isUniversalArrow_iff_isIso (Chaotic.sectionBaseChangeAdj A a)
    (Chaotic.derivedSectionRestriction M a)).symm.trans ?_
  refine (Functor.isUniversalArrow_iff_of_iso (sectionDerivedSquare D a)
    (Chaotic.derivedSectionRestriction M a)).trans ?_
  exact Functor.IsUniversalArrow.iff_of_iso (sectionClassIso D M V) (sectionClassIso D M U)
    (sectionClassIso_restriction D M a)

/-- **A differential graded module satisfies the quasi-coherence condition of Differential Graded
Sheaves, Definition 0GZ9, exactly when its complex of `O`-modules lies in `QC(O)` of Cohomology on
Sites, Definition 0GYV.** -/
theorem isQCModule_iff_isQC (M : DifferentialGradedModule.{u, u, u} A) :
    Chaotic.IsQCModule M ↔ IsQC.{u} bc (DerivedCategory.Q.obj (toComplex D M)) :=
  ⟨fun h _ _ a => (isIso_sectionComparison_iff D bc M a).1 (h a),
    fun h _ _ a => (isIso_sectionComparison_iff D bc M a).2 (h a)⟩

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

/-- Membership in `QC(O)` is invariant under isomorphism. -/
theorem isQC_iff_of_iso {K K' : DMod.{u} O} (e : K ≅ K') : IsQC.{u} bc K ↔ IsQC.{u} bc K' :=
  ⟨fun h _ _ a => (isIso_comparison_iff_of_iso bc a e).1 (h a),
    fun h _ _ a => (isIso_comparison_iff_of_iso bc a e).2 (h a)⟩

/-- The equivalence `D(A, d) ≌ D(O)` on the class of a differential graded module computing an
object. -/
def derivedEquivalenceObjIso {K : derivedCategory.{u, u, u} A}
    (M : DifferentialGradedModule.{u, u, u} A) (hM : Chaotic.derivedClass A M = K) :
    (derivedEquivalence D).functor.obj K ≅ DerivedCategory.Q.obj (toComplex D M) :=
  (derivedEquivalence D).functor.mapIso (eqToIso hM.symm) ≪≫ (derivedEquivalenceFac D).app M

/-- **The equivalence `D(A, d) ≌ D(O)` matches the two notions of quasi-coherent objects**: an
object `K` of `D(A, d)` lies in `QC(A, d)` of Differential Graded Sheaves, Definition 0GZ9,
exactly when its image in `D(O)` lies in `QC(O)` of Cohomology on Sites, Definition 0GYV. -/
theorem qc_iff_isQC (K : derivedCategory.{u, u, u} A) :
    Chaotic.QC A K ↔ IsQC.{u} bc ((derivedEquivalence D).functor.obj K) := by
  obtain ⟨M₀, hM₀⟩ := Chaotic.exists_module_eq A K
  refine ⟨fun h => ?_, fun h M hM => ?_⟩
  · exact (isQC_iff_of_iso bc (derivedEquivalenceObjIso D M₀ hM₀)).2
      ((isQCModule_iff_isQC D bc M₀).1 (h M₀ hM₀))
  · exact (isQCModule_iff_isQC D bc M).2
      ((isQC_iff_of_iso bc (derivedEquivalenceObjIso D M hM)).1 h)

/-- **The equivalence `QC(A, d) ≌ QC(O)`**: the restriction of `D(A, d) ≌ D(O)` to the full
subcategories of quasi-coherent objects. -/
def qcEquivalence : (Chaotic.QC A).FullSubcategory ≌ QC.{u} bc :=
  haveI : ObjectProperty.IsClosedUnderIsomorphisms (fun K : DMod.{u} O => IsQC.{u} bc K) :=
    ⟨fun e h => (isQC_iff_of_iso bc e).1 h⟩
  (derivedEquivalence D).congrFullSubcategory (by
    ext K
    exact (qc_iff_isQC D bc K).symm)

/-- The functor of `qcEquivalence` is `D(A, d) ≌ D(O)` on underlying objects. -/
theorem qcEquivalence_functor_obj_obj (K : (Chaotic.QC A).FullSubcategory) :
    ((qcEquivalence D bc).functor.obj K).obj = (derivedEquivalence D).functor.obj K.obj :=
  rfl

/-- The inverse of `qcEquivalence` is the inverse of `D(A, d) ≌ D(O)` on underlying objects. -/
theorem qcEquivalence_inverse_obj_obj (K : QC.{u} bc) :
    ((qcEquivalence D bc).inverse.obj K).obj = (derivedEquivalence D).inverse.obj K.obj :=
  rfl

end QuasiCoherent

end DegreeZero

end DifferentialGradedModule

end SheafOfModules

end

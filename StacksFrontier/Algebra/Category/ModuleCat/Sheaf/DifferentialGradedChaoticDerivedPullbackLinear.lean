module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedPullbackTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticSystemHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionSystemEquivalence
public import StacksFrontier.CategoryTheory.Linear.LinearOfResolvingClass

/-!
# The derived pullback along a functor of chaotic sites is linear

Let `R` be a commutative ring, `F : C' ⥤ C` a functor of categories with the chaotic topology and
the constant sheaves of rings with value `R`, and `φ : g^*A → A'` a map of sheaves of
differential graded algebras over the identity of the constant sheaf of rings. Multiplication by
`r ∈ R` on a module `M` is right multiplication by the central scalar `r · 1` on its sections;
the pullback `M(F U') ⊗_{A(F U')} A'(U')` carries `x · (r · 1) ⊗ b` to
`x ⊗ (r · 1) b = (x ⊗ b) · (r · 1)`, so the pullback commutes with multiplication by `r`. It is
therefore `R`-linear on the modules and on the homotopy categories, and since the derived pullback
is computed on modules whose sections are K-projective, which reach every object of `D(A, d)`, the
derived pullback `Lg^* : D(A, d) ⥤ D(A', d)` and its restriction `QC(A, d) ⥤ QC(A', d)` are
`R`-linear.

## Main results

* `SheafOfModules.DifferentialGradedModule.pullbackFunctor_map_scalarEnd`: the pullback commutes
  with multiplication by `r ∈ R`.
* `SheafOfModules.DifferentialGradedModule.pullbackHomotopyFunctor_linear`: the pullback on the
  homotopy categories is `R`-linear.
* `SheafOfModules.DifferentialGradedModule.chaoticDerivedPullback_linear` and
  `chaoticQCPullback_linear`: **the derived pullback is `R`-linear**, on `D(A, d)` and on the
  quasi-coherent objects.

## References

* [Stacks Project, Lemma 24.33.4 (Tag 0GZC)](https://stacks.math.columbia.edu/tag/0GZC)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

open Stacks.ChaoticSite

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] {R : Type u} [CommRing R]
  {F : C' ⥤ C}
  {A : DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.PresheafOfModules.constCommRingSheaf (C := C) R))}
  {A' : DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.PresheafOfModules.constCommRingSheaf (C := C') R))}
  (φ : DifferentialGradedAlgebra.InverseImageHom (C := C) (C' := C')
    (Osharp := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R)
    (Osharp' := Stacks.PresheafOfModules.constCommRingSheaf (C := C') R)
    F (constRingInverseImage F) A A')

/-! ### The pullback commutes with the scalars -/

/-- An element of `R`, as a section of the sheaf of rings underlying the constant sheaf of
commutative rings with value `R`. -/
abbrev constSection {D : Type u} [Category.{u} D] (U : Dᵒᵖ) (r : R) :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.PresheafOfModules.constCommRingSheaf (C := D) R)).obj.obj U :=
  r

/-- Multiplication by `r ∈ R` on the total sections of a module is the action of the scalar
`r · 1` of the section algebra. -/
theorem sectionMapAdd_scalarEnd (r : R) (M : DifferentialGradedModule.{u, u, u} A) (U : Cᵒᵖ)
    (x : M.totalSections U) :
    sectionMapAdd (toRingCatScalarEnd A r M) U x =
      M.act U x (A.sectionScalar U (constSection U r)) := by
  refine Eq.trans ?_ (act_sectionScalar M U x (constSection U r)).symm
  induction x using DirectSum.induction_on with
  | zero => exact (map_zero _).trans (smul_zero _).symm
  | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (smul_add _ _ _).symm)
  | of n p =>
      rw [sectionMapAdd_of]
      exact ((DirectSum.lof _ ℤ (M.sectionsPiece U) n).map_smul (constSection U r) p)

/-- Multiplication by `r ∈ R` on the sections of a module is right multiplication by the scalar
`r · 1` of the section algebra. -/
theorem sectionMap_scalarEnd (r : R) (M : DifferentialGradedModule.{u, u, u} A) (U : Cᵒᵖ)
    (x : (M.sectionModule U).M) :
    (sectionMap (toRingCatScalarEnd A r M) U).toFun x =
      A.sectionScalarOp U (constSection U r) • x :=
  sectionMapAdd_scalarEnd r M U x

/-- The homomorphism of section algebras induced by `φ` carries the scalar `r · 1` to the scalar
`r · 1`. -/
theorem sectionHom_sectionScalarAlg (U' : C'ᵒᵖ) (r : R) :
    (φ.sectionHom U').toAlgebraHom (A.sectionScalarAlg (F.op.obj U') (constSection _ r)) =
      A'.sectionScalarAlg U' (constSection U' r) :=
  (φ.sectionRing_of U' 0 _).trans (congrArg (DirectSum.of _ 0)
    ((φ.app_smul 0 U' (constSection _ r) _).trans (congrArg (_ • ·) (φ.app_one U'))))

/-- **The pullback of multiplication by `r` on the sections over `U'`** is right multiplication by
the scalar `r · 1` of `A'(U')`. -/
theorem pullbackSectionsMap_scalarEnd (r : R) (M : DifferentialGradedModule.{u, u, u} A)
    (U' : C'ᵒᵖ) (z : (pullbackSections φ M U').M) :
    (pullbackSectionsMap φ (toRingCatScalarEnd A r M) U').toFun z =
      A'.sectionScalarOp U' (constSection U' r) • z := by
  have key : (pullbackSectionsMap φ (toRingCatScalarEnd A r M) U').toFun.toAddMonoidHom =
      DistribSMul.toAddMonoidHom _ (A'.sectionScalarOp U' (constSection U' r)) := by
    refine tensorObj_addHom_ext_homogeneous _ _ _ _ fun p q x y => ?_
    show (pullbackSectionsMap φ (toRingCatScalarEnd A r M) U').toFun (pullbackPure φ M U' x y) =
      A'.sectionScalarOp U' (constSection U' r) • pullbackPure φ M U' x y
    refine (pullbackSectionsMap_pure φ _ U' x.1 y.1).trans ?_
    refine (congrArg (fun w => pullbackPure φ M U' w y.1) (sectionMap_scalarEnd r M _ x.1)).trans ?_
    have hb := ((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
      (M.sectionModule (F.op.obj U'))).balance p q 0 x y
      ⟨A.sectionScalarAlg (F.op.obj U') (constSection _ r),
        A.sectionScalar_mem (F.op.obj U') (constSection _ r)⟩
    refine hb.trans ?_
    refine (congrArg (pullbackPure φ M U' (x : (M.sectionModule (F.op.obj U')).M))
      ((pullbackBimodule_action φ U' 0 q _ y).trans ?_)).trans
      (((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
        (M.sectionModule (F.op.obj U'))).map_right _ _ (A'.sectionScalarAlg U' (constSection U' r)))
    exact (congrArg (· * _) (sectionHom_sectionScalarAlg φ U' r)).trans
      (A'.sectionScalarAlg_mul_comm U' _ _)
  exact DFunLike.congr_fun key z

/-- **The pullback commutes with multiplication by `r ∈ R`.** -/
theorem pullbackFunctor_map_scalarEnd (r : R) (M : DifferentialGradedModule.{u, u, u} A) :
    (pullbackFunctor φ).map (toRingCatScalarEnd A r M) =
      toRingCatScalarEnd A' r ((pullbackFunctor φ).obj M) := by
  apply DifferentialGradedModule.Hom.ext
  intro n
  apply SheafOfModules.hom_ext
  ext U' x
  exact (pullbackSystem φ M).cElt_injective (pullbackSectionsMap_scalarEnd φ r M U' _)

/-- The pullback on right differential graded modules is `R`-linear. -/
instance pullbackFunctor_linear : (pullbackFunctor φ).Linear R where
  map_smul f r := by
    rw [toRingCat_smul_eq_scalarEnd_comp, toRingCat_smul_eq_scalarEnd_comp, Functor.map_comp,
      pullbackFunctor_map_scalarEnd]

/-- **The pullback on the homotopy categories is `R`-linear.** -/
instance pullbackHomotopyFunctor_linear : (pullbackHomotopyFunctor φ).Linear R where
  map_smul f r := by
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f
    have h : ∀ {X Y : DifferentialGradedModule.{u, u, u} A} (g : X ⟶ Y),
        (pullbackHomotopyFunctor φ).map ((HomotopyCategory.quotient A).map g) =
          (HomotopyCategory.quotient A').map ((pullbackFunctor φ).map g) :=
      fun g => HomotopyCategory.descend_map _ _ g
    rw [← Functor.map_smul, h, h, Functor.map_smul, Functor.map_smul]
    rfl

/-! ### The derived pullback -/

/-- **The derived pullback is `R`-linear.** It is computed on the modules whose sections are
K-projective, which reach every object of `D(A, d)`, and there it is the pullback, which is
`R`-linear. -/
instance chaoticDerivedPullback_linear : (chaoticDerivedPullback φ).Linear R := by
  refine Functor.linear_of_map_smul_id_of_resolving (toDerivedCategory.{u, u, u} A)
    (chaoticDerivedPullback φ) (sectionGoodProperty A) (fun X => ?_) (fun Y hY r => ?_)
  · obtain ⟨Y, hY, s, hs⟩ :=
      exists_sectionGoodProperty A ((toDerivedCategory.{u, u, u} A).objPreimage X)
    have : IsIso ((toDerivedCategory.{u, u, u} A).map s) :=
      (quasiIsomorphisms.{u, u, u} A).Q_inverts _ hs
    exact ⟨Y, hY, ⟨asIso ((toDerivedCategory.{u, u, u} A).map s) ≪≫
      (toDerivedCategory.{u, u, u} A).objObjPreimageIso X⟩⟩
  · have : IsIso ((chaoticDerivedPullbackCounit φ).app Y) :=
      isIso_chaoticDerivedPullbackCounit_app φ (P := Y.as) hY
    have hn := (chaoticDerivedPullbackCounit φ).naturality (r • 𝟙 Y)
    have hF : (pullbackToDerived φ).map (r • 𝟙 Y) = r • 𝟙 _ := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [hF, Functor.comp_map] at hn
    rw [← cancel_mono ((chaoticDerivedPullbackCounit φ).app Y)]
    refine hn.trans ?_
    rw [Linear.comp_smul, Category.comp_id, Linear.smul_comp, Category.id_comp]

/-- **The derived pullback on quasi-coherent objects is `R`-linear.** -/
instance chaoticQCPullback_linear : (chaoticQCPullback φ).Linear R where
  map_smul f r := by
    ext
    exact (chaoticDerivedPullback φ).map_smul r f.hom

end SheafOfModules.DifferentialGradedModule

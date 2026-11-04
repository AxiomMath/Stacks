module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage

/-!
# Constant sheaves lie in `D_ctf`

A constant sheaf of modules with finite projective value `M` is locally constant with finite
projective values in the strongest sense. It is constant on every object of the site, since its
restriction to a slice site is the constant sheaf on `M` there. It is therefore constructible flat:
one stratum per affine open suffices. A complex of such sheaves concentrated in one degree lies in
`D_ctf(X_étale, Λ)`.

The case of interest is the constant sheaf `Λ` itself, the coefficient system of the trace formula
[Stacks, Tag 03UG] in its specialisation [Stacks, Tag 03UJ] to Weil's formula.

## Main results

* `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_constantSheaf`: a constant sheaf with
  finite projective value is locally constant with finite projective values.
* `Stacks.EtaleCohomology.isConstructibleFlatEtaleModule_etaleModuleConstantSheaf`: the constant
  sheaf on a finite projective module is constructible flat on Mathlib's small étale site.
* `Stacks.EtaleCohomology.isCtf_constantModuleSheaf`: the constant sheaf `Λ` in degree zero lies in
  `D_ctf(X_étale, Λ)`.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03UJ](https://stacks.math.columbia.edu/tag/03UJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w c r

namespace Stacks.ConstantSheaf

/-- **A constant sheaf with finite projective value is locally constant with finite projective
values**: on every object `U` it restricts to the constant sheaf on its value over the slice site,
so the one-member covering `{𝟙 U}` trivializes it. -/
public theorem isFiniteProjectiveLocallyConstant_constantSheaf (R : Type r) [Ring R]
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (ModuleCat.{w} R)]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    [∀ (V : C) (F : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R),
      (Over.forget V).op.HasPointwiseRightKanExtension F]
    (M : ModuleCat.{w} R) [Module.Finite R M] [Module.Projective R M] :
    IsFiniteProjectiveLocallyConstant R J ((constantSheaf J (ModuleCat.{w} R)).obj M) := by
  intro U
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ =>
    ⟨M, inferInstance, inferInstance, ⟨(overPullbackConstantSheafIso J _ U).app M⟩⟩⟩
  refine J.superset_covering ?_ (J.top_mem U)
  intro W g _
  exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨PUnit.unit, g, (Category.comp_id g).symm⟩

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- **The constant sheaf on a finite projective module is constructible flat** on Mathlib's small
étale site: its transport to the small étale site of Stacks 021B is the constant sheaf there,
the constant sheaf functors commuting with the equivalence of the two sheaf categories. -/
public theorem isConstructibleFlatEtaleModule_constantSheaf (X : B.Scheme)
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] [Module.Projective Λ M] :
    IsConstructibleFlatEtaleModule B X Λ
      ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  have : IsIso ((SmallEtale.toEtaleSite B X.obj X.property).obj
      (SmallEtale.final B X.obj X.property)).hom :=
    inferInstanceAs (IsIso (B.inclusion.map (𝟙 _)))
  have e := (equivCommuteConstant' (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{max (u + 1) r} Λ) X.obj.smallEtaleTopology
    (SmallEtale.toEtaleSite B X.obj X.property)
    (SmallEtale.finalIsTerminal B X.obj X.property) (isTerminalOfIsIsoHom _)).app M
  exact isConstructibleFlatModuleSheaf_congr B X Λ e
    (fun U => ⟨ConstructibleStratification.singleReduced B X U.1, fun _ =>
      isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ _ _
        (Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_constantSheaf Λ _ M)⟩)

/-- **The constant sheaf `Λ` in degree zero lies in `D_ctf(X_étale, Λ)`**: it is represented by
itself, a bounded complex whose only nonzero term is the constant sheaf on the free module of rank
one. -/
public theorem isCtf_constantModuleSheaf {Λ : Type r} [CommRing Λ] (X : B.Scheme) :
    IsCtf B X Λ (DerivedCategory.Q.obj ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r, u, u + 1} Λ
        X.obj.smallEtaleTopology)).obj) := by
  refine IsRepresentedByConstructibleFlatEtaleComplex.isCtf B Λ ?_
  let F := Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r, u, u + 1} Λ
    X.obj.smallEtaleTopology
  let C := (HomologicalComplex.single (EtaleModules.{u, r} Λ X.obj) (ComplexShape.up ℤ) 0).obj F
  let eU : ULift.{u + 1} Λ ≃ₗ[Λ] Λ := ULift.moduleEquiv
  have : Module.Finite Λ (ULift.{u + 1} Λ) := Module.Finite.equiv eU.symm
  have : Module.Projective Λ (ULift.{u + 1} Λ) := Module.Projective.of_equiv eU.symm
  refine ⟨C, 0, 0, inferInstanceAs (CochainComplex.IsStrictlyGE C 0),
    inferInstanceAs (CochainComplex.IsStrictlyLE C 0), fun i => ?_, ⟨Iso.refl _⟩⟩
  by_cases hi : i = 0
  · subst hi
    exact IsConstructibleFlatEtaleModule.of_iso B X Λ
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm
      (isConstructibleFlatEtaleModule_constantSheaf B Λ X (ModuleCat.of Λ (ULift.{u + 1} Λ)))
  · exact isConstructibleFlatEtaleModule_of_isZero B Λ X
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

end Stacks.EtaleCohomology

end

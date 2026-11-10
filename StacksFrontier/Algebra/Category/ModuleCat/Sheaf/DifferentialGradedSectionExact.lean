module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentChaoticSite
public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism

/-!
# Taking sections on a chaotic site is exact on differential graded modules

Let `C` be a category viewed as a site with the chaotic topology, let `R` be a sheaf of rings on
it and let `U` be an object of `Cᵒᵖ`. Because the only covering sieve is the maximal one, a
presheaf of modules is automatically a sheaf and the evaluation functor
`SheafOfModules R ⥤ ModuleCat (R(U))` is computed pointwise; it is therefore exact. Reading its
values over the lifted integers turns it into the functor `sectionsFunctor R U` with values in
`ModuleCat (ULift ℤ)`, which is again exact and hence preserves homology.

Let `(A, d)` be a sheaf of differential graded `R`-algebras and let `M` be a right differential
graded `A`-module. The cochain complex of `ULift ℤ`-modules obtained by applying
`sectionsFunctor R U` degreewise to the underlying complex of sheaves of modules of `M` is
canonically isomorphic to the cochain complex underlying the differential graded `A(U)`-module
`M(U)` of sections. Consequently a homomorphism `f : M ⟶ N` whose underlying map of complexes
of sheaves of modules is a quasi-isomorphism induces a quasi-isomorphism on sections over `U`.
This is the exactness statement that makes `RΓ(U, M)` computable by `M(U)` on a chaotic site,
and so the one that identifies the comparison map of Definition 24.33.1 with the map built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedSectionComparison.lean`.

## Main definitions

* `Stacks.SheafOfModules.intCastHom`: the integer cast `ULift ℤ →+* R(U)`.
* `Stacks.SheafOfModules.sectionsFunctor`: **evaluation at `U`, read over the lifted integers**,
  the functor `SheafOfModules R ⥤ ModuleCat (ULift ℤ)`.
* `SheafOfModules.DifferentialGradedModule.sectionsPieceIso`: the degreewise identification of
  the sections of the degree-`n` piece of `M` with the degree-`n` piece of `M(U)`.
* `SheafOfModules.DifferentialGradedModule.sectionsCochainIso`: **the identification of the
  complex of sections with the cochain complex underlying `M(U)`.**

## Main results

* `Stacks.SheafOfModules.preservesColimitsOfShape_evaluation`: on the bottom topology,
  evaluation at an object preserves colimits of any shape.
* `SheafOfModules.DifferentialGradedModule.quasiIso_sectionMap`: **a quasi-isomorphism of right
  differential graded `A`-modules induces a quasi-isomorphism of the cochain complexes of
  sections over `U`.**
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_sectionMap`: the same statement
  read in the homotopy category of differential graded `A(U)`-modules.

## Implementation notes

Exactness of `sectionsFunctor R U` is proved by reflecting through the forgetful functor to
abelian groups: restriction of scalars does not change the underlying additive group, so
`sectionsFunctor R U ⋙ forget₂ _ AddCommGrpCat` is literally
`SheafOfModules.evaluation R U ⋙ forget₂ _ AddCommGrpCat`, and the forgetful functor reflects
isomorphisms. This detour is needed because Mathlib's exactness instances for restriction of
scalars ask for both rings to be commutative, whereas `R(U)` is only a ring. Preservation of
finite limits is unconditional; preservation of finite colimits uses that the topology is the
bottom one, through `Stacks.SheafOfModules.botWEqualsLocallyBijective`.

The degreewise identification is `Stacks.ExternalGrading.intSummandEquiv`, which is only an
additive equivalence. Over the lifted integers it is automatically linear, but the two sides
carry different-looking scalar actions: the source is a module over `R(U)` restricted along the
integer cast, the target is the plain action of `ULift ℤ` on an additive group, so linearity is
`Int.cast_smul_eq_zsmul` followed by `map_zsmul`.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **The integer cast `ULift ℤ →+* R(U)`**: the structure map making the ring of sections of a
sheaf of rings over `U` an algebra over the universe-lifted integers. -/
def intCastHom (R : Sheaf J RingCat.{t}) (U : Cᵒᵖ) : ULift.{a, 0} ℤ →+* R.obj.obj U :=
  (Int.castRingHom _).comp (ULift.ringEquiv : ULift.{a, 0} ℤ ≃+* ℤ).toRingHom

/-- **Evaluation at `U`, read over the lifted integers.** It sends a sheaf of `R`-modules to its
group of sections over `U`, viewed as a module over `ULift ℤ` through the integer cast. -/
def sectionsFunctor (R : Sheaf J RingCat.{t}) (U : Cᵒᵖ) :
    _root_.SheafOfModules.{a} R ⥤ ModuleCat.{a} (ULift.{a, 0} ℤ) :=
  _root_.SheafOfModules.evaluation.{a} R U ⋙ ModuleCat.restrictScalars (intCastHom R U)

/-- Restriction of scalars does not change the underlying additive group, so the sections
functor and evaluation have the same composite with the forgetful functor to abelian groups. -/
theorem sectionsFunctor_comp_forget₂ (R : Sheaf J RingCat.{t}) (U : Cᵒᵖ) :
    sectionsFunctor.{t, a} R U ⋙ forget₂ (ModuleCat.{a} (ULift.{a, 0} ℤ)) AddCommGrpCat.{a} =
      _root_.SheafOfModules.evaluation.{a} R U ⋙
        forget₂ (ModuleCat.{a} (R.obj.obj U)) AddCommGrpCat.{a} := rfl

/-- The sections functor is additive, both of its factors being so. -/
instance sectionsFunctorAdditive (R : Sheaf J RingCat.{t}) (U : Cᵒᵖ) :
    (sectionsFunctor.{t, a} R U).Additive :=
  inferInstanceAs (Functor.Additive (_root_.SheafOfModules.evaluation.{a} R U ⋙ _))

/-- **On the bottom topology, evaluation at an object preserves colimits of any shape.** A
presheaf of modules is then automatically a sheaf, so the colimit is computed pointwise; the
statement is reduced to abelian groups, where sheafification inverts exactly the locally
bijective maps. -/
theorem preservesColimitsOfShape_evaluation
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}) (U : Cᵒᵖ)
    (K : Type a) [Category.{a} K] :
    Limits.PreservesColimitsOfShape K (_root_.SheafOfModules.evaluation.{a} R U) := by
  have : (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{a} :=
    botWEqualsLocallyBijective (C := C)
  have : Limits.PreservesColimitsOfShape K (_root_.SheafOfModules.toSheaf.{a} R) :=
    (Limits.preservesColimitsOfSize_of_univLE.{max u a, a, a, a}
      (_root_.SheafOfModules.toSheaf.{a} R)).preservesColimitsOfShape
  have : Limits.PreservesColimitsOfShape K
      (_root_.SheafOfModules.evaluation.{a} R U ⋙
        forget₂ (ModuleCat.{a} (R.obj.obj U)) AddCommGrpCat.{a}) :=
    inferInstanceAs (Limits.PreservesColimitsOfShape K
      (_root_.SheafOfModules.toSheaf.{a} R ⋙
        (sheafBotEquivalence (C := C) AddCommGrpCat.{a}).functor ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{a}).obj U))
  exact Limits.preservesColimitsOfShape_of_reflects_of_preserves
    (_root_.SheafOfModules.evaluation.{a} R U)
    (forget₂ (ModuleCat.{a} (R.obj.obj U)) AddCommGrpCat.{a})

/-- On the bottom topology, evaluation at an object preserves finite colimits. -/
instance evaluationPreservesFiniteColimits
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}) (U : Cᵒᵖ) :
    Limits.PreservesFiniteColimits (_root_.SheafOfModules.evaluation.{a} R U) where
  preservesFiniteColimits K _ _ :=
    have := preservesColimitsOfShape_evaluation.{t, a} R U (ULiftHom.{a} (ULift.{a} K))
    Limits.preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv.{a, a, 0, 0} K).symm _

/-- On the bottom topology, the sections functor preserves finite colimits. -/
instance sectionsFunctorPreservesFiniteColimits
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}) (U : Cᵒᵖ) :
    Limits.PreservesFiniteColimits (sectionsFunctor.{t, a} R U) where
  preservesFiniteColimits K _ _ := by
    have : Limits.PreservesColimitsOfShape K
        (sectionsFunctor.{t, a} R U ⋙
          forget₂ (ModuleCat.{a} (ULift.{a, 0} ℤ)) AddCommGrpCat.{a}) :=
      inferInstanceAs (Limits.PreservesColimitsOfShape K
        (_root_.SheafOfModules.evaluation.{a} R U ⋙
          forget₂ (ModuleCat.{a} (R.obj.obj U)) AddCommGrpCat.{a}))
    exact Limits.preservesColimitsOfShape_of_reflects_of_preserves
      (sectionsFunctor.{t, a} R U)
      (forget₂ (ModuleCat.{a} (ULift.{a, 0} ℤ)) AddCommGrpCat.{a})

/-- The sections functor preserves finite limits, on any topology. -/
instance sectionsFunctorPreservesFiniteLimits (R : Sheaf J RingCat.{t}) (U : Cᵒᵖ) :
    Limits.PreservesFiniteLimits (sectionsFunctor.{t, a} R U) where
  preservesFiniteLimits K _ _ := by
    have : Limits.PreservesLimitsOfShape K
        (sectionsFunctor.{t, a} R U ⋙
          forget₂ (ModuleCat.{a} (ULift.{a, 0} ℤ)) AddCommGrpCat.{a}) :=
      inferInstanceAs (Limits.PreservesLimitsOfShape K
        (_root_.SheafOfModules.evaluation.{a} R U ⋙
          forget₂ (ModuleCat.{a} (R.obj.obj U)) AddCommGrpCat.{a}))
    exact Limits.preservesLimitsOfShape_of_reflects_of_preserves
      (sectionsFunctor.{t, a} R U)
      (forget₂ (ModuleCat.{a} (ULift.{a, 0} ℤ)) AddCommGrpCat.{a})

/-! ### Acyclicity and quasi-isomorphism are detected sectionwise -/

/-- Evaluation at an object is left exact on any site: it is the forgetful functor to
presheaves of modules, a right adjoint, followed by evaluation of a presheaf of modules. -/
noncomputable instance evaluationPreservesFiniteLimits (R : Sheaf J RingCat.{t}) (U : Cᵒᵖ) :
    Limits.PreservesFiniteLimits (_root_.SheafOfModules.evaluation.{a} R U) :=
  inferInstanceAs (Limits.PreservesFiniteLimits
    (_root_.SheafOfModules.forget.{a} R ⋙ PresheafOfModules.evaluation R.obj U))

/-- Being exact, evaluation at an object of a chaotic site preserves homology. -/
noncomputable instance evaluationPreservesHomology
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}) (U : Cᵒᵖ) :
    (_root_.SheafOfModules.evaluation.{a} R U).PreservesHomology :=
  Functor.preservesHomologyOfExact _

section Chaotic

variable {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}} {U : Cᵒᵖ}

/-- On the bottom topology, sheafification of abelian sheaves inverts exactly the locally
bijective maps; this is what puts the abelian structure, and hence homology, on sheaves of
modules. -/
local instance botWEqualsLocallyBijectiveChaotic :
    (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{a} :=
  botWEqualsLocallyBijective

/-- Evaluating the short complex a complex of sheaves of modules has in a degree is the short
complex of the evaluated complex. -/
theorem sc_mapHomologicalComplex_obj (K : CochainComplex (_root_.SheafOfModules.{a} R) ℤ)
    (i : ℤ) :
    (((_root_.SheafOfModules.evaluation.{a} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).sc i =
      (K.sc i).map (_root_.SheafOfModules.evaluation.{a} R U) :=
  rfl

/-- **A complex of sheaves of modules on a chaotic site is exact in a degree exactly when all
of its evaluations are.** Forwards this is exactness of evaluation; backwards it is joint
conservativity of the evaluations, applied to the homology. -/
theorem exactAt_mapHomologicalComplex_obj_iff
    (K : CochainComplex (_root_.SheafOfModules.{a} R) ℤ) (i : ℤ) :
    K.ExactAt i ↔ ∀ V : Cᵒᵖ,
      (((_root_.SheafOfModules.evaluation.{a} R V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt i := by
  refine ⟨fun hK V => ?_, fun hK => ?_⟩
  · rw [HomologicalComplex.exactAt_iff, sc_mapHomologicalComplex_obj]
    exact (HomologicalComplex.exactAt_iff _ _ |>.1 hK).map _
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine Stacks.SheafOfModulesEvaluation.isZero_of_forall_isZero_evaluation R fun V => ?_
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hK V)).of_iso
      (ShortComplex.mapHomologyIso (K.sc i) (_root_.SheafOfModules.evaluation.{a} R V)).symm

/-- Evaluation at an object of a chaotic site carries an exact degree to an exact degree. -/
theorem exactAt_mapHomologicalComplex_obj
    {K : CochainComplex (_root_.SheafOfModules.{a} R) ℤ} {i : ℤ} (hK : K.ExactAt i) :
    (((_root_.SheafOfModules.evaluation.{a} R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt i :=
  (exactAt_mapHomologicalComplex_obj_iff K i).1 hK U

/-- **A complex of sheaves of modules on a chaotic site is acyclic exactly when all of its
evaluations are acyclic.** -/
theorem acyclic_iff_forall_acyclic_evaluation
    (K : CochainComplex (_root_.SheafOfModules.{a} R) ℤ) :
    K.Acyclic ↔ ∀ V : Cᵒᵖ,
      (((_root_.SheafOfModules.evaluation.{a} R V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).Acyclic :=
  ⟨fun hK _ i => exactAt_mapHomologicalComplex_obj (hK i),
    fun hK i => (exactAt_mapHomologicalComplex_obj_iff K i).2 fun V => hK V i⟩

/-- The evaluation of the map induced on homology is invertible as soon as the map induced on
homology by the evaluated morphism is: the two differ by the comparison isomorphism between the
homology of an evaluated short complex and the evaluation of its homology. -/
theorem isIso_evaluation_homologyMap_of_isIso
    {K L : CochainComplex (_root_.SheafOfModules.{a} R) ℤ} (f : K ⟶ L) (i : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap
      (((_root_.SheafOfModules.evaluation.{a} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) i)) :
    IsIso ((_root_.SheafOfModules.evaluation.{a} R U).map
      (HomologicalComplex.homologyMap f i)) := by
  have hsq := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (_root_.SheafOfModules.{a} R)
      (ComplexShape.up ℤ) i).map f) (_root_.SheafOfModules.evaluation.{a} R U)
  have hA : IsIso (ShortComplex.homologyMap
      ((_root_.SheafOfModules.evaluation.{a} R U).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor (_root_.SheafOfModules.{a} R)
          (ComplexShape.up ℤ) i).map f))) := h
  have h' : IsIso ((((HomologicalComplex.shortComplexFunctor (_root_.SheafOfModules.{a} R)
        (ComplexShape.up ℤ) i).obj K).mapHomologyIso
          (_root_.SheafOfModules.evaluation.{a} R U)).hom ≫
      (_root_.SheafOfModules.evaluation.{a} R U).map (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (_root_.SheafOfModules.{a} R)
          (ComplexShape.up ℤ) i).map f))) := by
    rw [← hsq]
    infer_instance
  change IsIso ((_root_.SheafOfModules.evaluation.{a} R U).map (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (_root_.SheafOfModules.{a} R)
      (ComplexShape.up ℤ) i).map f)))
  exact IsIso.of_isIso_comp_left
    ((((HomologicalComplex.shortComplexFunctor (_root_.SheafOfModules.{a} R)
      (ComplexShape.up ℤ) i).obj K).mapHomologyIso
        (_root_.SheafOfModules.evaluation.{a} R U)).hom) _

/-- **A morphism of complexes of sheaves of modules on a chaotic site is a quasi-isomorphism
exactly when all of its evaluations are.** Backwards this is joint conservativity of the
evaluations, applied to the maps induced on homology; it is the converse of
`Stacks.SheafOfModules.quasiIso_sectionMap`, and it is what lets the derived sections over the
objects of the site detect isomorphisms. -/
theorem quasiIso_iff_forall_quasiIso_evaluation
    {K L : CochainComplex (_root_.SheafOfModules.{a} R) ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ V : Cᵒᵖ,
      QuasiIso (((_root_.SheafOfModules.evaluation.{a} R V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) := by
  refine ⟨fun _ _ => inferInstance, fun h => ?_⟩
  rw [_root_.quasiIso_iff]
  intro i
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  refine Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation R _ fun V => ?_
  exact isIso_evaluation_homologyMap_of_isIso f i
    ((_root_.quasiIsoAt_iff_isIso_homologyMap _ _).1 ((_root_.quasiIso_iff _).1 (h V) i))

end Chaotic

end Stacks.SheafOfModules

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- On the bottom topology, sheafification of abelian sheaves inverts exactly the locally
bijective maps. This is `Stacks.SheafOfModules.botWEqualsLocallyBijective` in instance form; it
is what puts the abelian structure, and hence homology, on sheaves of modules here. -/
local instance botWEqualsLocallyBijective' :
    (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{a} :=
  Stacks.SheafOfModules.botWEqualsLocallyBijective

/-- Scaling a section by an integer cast and including it into the total sections is scaling by
that integer: this is the linearity over the lifted integers of the inclusion of a summand. -/
theorem intSummandEquiv_intCast_smul (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ)
    (n : ℤ) (c : ULift.{a, 0} ℤ) (x : M.sectionsPiece U n) :
    Stacks.ExternalGrading.intSummandEquiv (M.sectionsPiece U) n
        (((c.down : ℤ) : R.obj.obj U) • x) =
      c • Stacks.ExternalGrading.intSummandEquiv (M.sectionsPiece U) n x :=
  Subtype.ext (by
    change DirectSum.of (M.sectionsPiece U) n (((c.down : ℤ) : R.obj.obj U) • x) =
      (c.down : ℤ) • DirectSum.of (M.sectionsPiece U) n x
    rw [Int.cast_smul_eq_zsmul, map_zsmul])

/-- **The sections of the degree-`n` piece are the degree-`n` piece of the section module**, as
a linear equivalence over the lifted integers. The underlying additive equivalence is the
inclusion of a summand of an external direct sum. -/
def sectionsPieceLinearEquiv (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ) (n : ℤ) :
    ((Stacks.SheafOfModules.sectionsFunctor R U).obj (M.complex.X n) : Type a) ≃ₗ[ULift.{a, 0} ℤ]
      ((M.sectionModule U).toCochainComplex.X n : Type a) where
  __ := Stacks.ExternalGrading.intSummandEquiv (M.sectionsPiece U) n
  map_smul' c x := M.intSummandEquiv_intCast_smul U n c x

/-- **The sections of the degree-`n` piece are the degree-`n` piece of the section module**, as
an isomorphism of modules over the lifted integers. -/
def sectionsPieceIso (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ) (n : ℤ) :
    (Stacks.SheafOfModules.sectionsFunctor R U).obj (M.complex.X n) ≅
      (M.sectionModule U).toCochainComplex.X n :=
  (M.sectionsPieceLinearEquiv U n).toModuleIso

/-- **The complex of sections of `M` is the cochain complex underlying the section module
`M(U)`.** Degreewise this is the identification of the sections of the degree-`n` piece with the
degree-`n` summand of the total sections; the differentials agree because the differential of
`M(U)` is the differential of `M` read on sections. -/
def sectionsCochainIso (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ) :
    ((Stacks.SheafOfModules.sectionsFunctor R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.complex ≅
      (M.sectionModule U).toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ M.sectionsPieceIso U n) (by
    rintro i j (rfl : i + 1 = j)
    rw [_root_.DifferentialGradedModule.toCochainComplex_d]
    ext x
    exact Subtype.ext (M.sectionD_of U i x))

variable {M N : DifferentialGradedModule.{t, a, a} A}

/-- **The map on sections induced by a homomorphism of differential graded modules is the map
on the cochain complexes underlying the section modules**, read through
`SheafOfModules.DifferentialGradedModule.sectionsCochainIso`. -/
theorem sectionsCochainIso_naturality (f : M ⟶ N) (U : Cᵒᵖ) :
    (M.sectionsCochainIso U).hom ≫
        (_root_.DifferentialGradedModule.forgetToCochainComplex
          (A.sectionAlgebra U)).map (sectionMap f U) =
      ((Stacks.SheafOfModules.sectionsFunctor R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f.toHomologicalComplex ≫ (N.sectionsCochainIso U).hom := by
  ext n x
  exact Subtype.ext (sectionMapAdd_of f U n x)

/-- The square identifying the two maps of cochain complexes, as an isomorphism of arrows. -/
def sectionsArrowIso (f : M ⟶ N) (U : Cᵒᵖ) :
    Arrow.mk (((Stacks.SheafOfModules.sectionsFunctor R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f.toHomologicalComplex) ≅
      Arrow.mk ((_root_.DifferentialGradedModule.forgetToCochainComplex
        (A.sectionAlgebra U)).map (sectionMap f U)) :=
  Arrow.isoMk (M.sectionsCochainIso U) (N.sectionsCochainIso U)
    (sectionsCochainIso_naturality f U)

/-- **A quasi-isomorphism of right differential graded `A`-modules induces a quasi-isomorphism
on sections over `U`.** On a chaotic site evaluation at an object is exact, hence preserves
homology, and the complex of sections of `M` is the cochain complex underlying the section
module `M(U)`. -/
theorem quasiIso_sectionMap (f : M ⟶ N) (U : Cᵒᵖ) (hf : QuasiIso f.toHomologicalComplex) :
    QuasiIso ((_root_.DifferentialGradedModule.forgetToCochainComplex
      (A.sectionAlgebra U)).map (sectionMap f U)) :=
  have := hf
  quasiIso_of_arrow_mk_iso _ _ (sectionsArrowIso f U)

/-- **A quasi-isomorphism of right differential graded `A`-modules is a quasi-isomorphism of the
section modules in the homotopy category of differential graded `A(U)`-modules.** -/
theorem quasiIsomorphisms_sectionMap (f : M ⟶ N) (U : Cᵒᵖ)
    (hf : QuasiIso f.toHomologicalComplex) :
    _root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).map
        (sectionMap f U)) :=
  (_root_.DifferentialGradedModule.quasiIsomorphisms_map_iff' (A.sectionAlgebra U)
    (sectionMap f U)).2 (quasiIso_sectionMap f U hf)

end DifferentialGradedModule

end SheafOfModules

end

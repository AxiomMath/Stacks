module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfectModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale

/-!
# Strictly perfect models on an affine represented algebraic space

On an affine represented algebraic space `U`, `RΓ` of an object with a strictly perfect model in
the sense of `AlgebraicGeometry.Space.HasStrictlyPerfectModel` is perfect, and such an object lies
in `D_QCoh`. (Conversely, the functor `Φ` from the derived category of `Γ(U, 𝒪_U)`-modules carries
perfect objects to objects with a strictly perfect model:
`AlgebraicGeometry.Space.hasStrictlyPerfectModel_representedAffineDerivedAssociated_obj`.)

## Main results

* `isPerfect_representedAffineDerivedSections_obj_of_hasStrictlyPerfectModel`: `RΓ` of an object
  with a strictly perfect model is perfect.
* `qcohDerived_of_hasStrictlyPerfectModel`: an object with a strictly perfect model lies in
  `D_QCoh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w d

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

section Model

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- A retract of a finite biproduct of copies of the structure sheaf is a direct summand of a
finite free module, in the spelling of `AlgebraicGeometry.Space.HasStrictlyPerfectModel`. -/
private theorem isDirectSummandOfFiniteFree_of_isRetractOfFiniteFree_aux
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
    (hM : IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) M) :
    IsDirectSummandOfFiniteFree (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) M := by
  obtain ⟨n, i, r, hir⟩ := hM
  let O₁ := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  let eb : SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (ULift.{u} (Fin n)) ≅
      ⨁ fun _ : Fin n => O₁ :=
    (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
      (biproduct.isoCoproduct _).symm
  exact (isDirectSummandOfFiniteFree_iff_free _ _).2
    ⟨n, i ≫ eb.inv, eb.hom ≫ r, by simp [hir]⟩

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- A strictly perfect model in the spelling of `AlgebraicGeometry.Space.HasStrictlyPerfectModel`
is a strictly perfect complex. -/
private theorem exists_isStrictlyPerfect_of_hasStrictlyPerfectModel_aux
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hE : HasStrictlyPerfectModel B S hS E) :
    ∃ P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) ℤ,
      IsStrictlyPerfect (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) P ∧
      Nonempty (E ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P, hP, ⟨a, b, hGE, hLE⟩, ⟨e⟩⟩ := hE
  refine ⟨P, ⟨(Set.finite_Icc a b).subset fun j hj => ?_, fun j =>
    isDirectSummandOfFiniteFree_of_isRetractOfFiniteFree_aux B S hS U _ (hP j)⟩, ⟨e⟩⟩
  simp only [Set.mem_ofPred_eq] at hj
  simp only [Set.mem_Icc]
  by_contra hne
  apply hj
  rcases not_and_or.mp hne with h | h
  · exact P.isZero_of_isStrictlyGE a j (by omega)
  · exact P.isZero_of_isStrictlyLE b j (by omega)

/-- **`RΓ` of an object with a strictly perfect model is perfect**, in the spelling
`AlgebraicGeometry.Space.HasStrictlyPerfectModel`. -/
theorem isPerfect_representedAffineDerivedSections_obj_of_hasStrictlyPerfectModel
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hE : HasStrictlyPerfectModel B S hS E) :
    StacksDraft.Perfect.IsPerfect ((representedAffineDerivedSections B S hS U).obj E) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_isStrictlyPerfect_of_hasStrictlyPerfectModel_aux B S hS U E hE
  exact isPerfect_representedAffineDerivedSections_obj_of_isStrictlyPerfect E P hP e

/-- An object with a strictly perfect model, in the spelling
`AlgebraicGeometry.Space.HasStrictlyPerfectModel`, lies in `D_QCoh`. -/
theorem qcohDerived_of_hasStrictlyPerfectModel
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hE : HasStrictlyPerfectModel B S hS E) :
    QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_isStrictlyPerfect_of_hasStrictlyPerfectModel_aux B S hS U E hE
  exact qcohDerived_of_isStrictlyPerfect E P hP e

end Model

end AlgebraicGeometry.Space

end

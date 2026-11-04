module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections

/-!
# A perfect object on an affine represented algebraic space is strictly perfect

Let `U` be an object of the big fppf site over `S` whose underlying scheme is affine, and let `E`
be a perfect object of `D(𝒪_{yoneda.obj U})` (Stacks 08G5). Perfectness asks for strictly perfect
models only étale-locally on `U`; on an affine `U` there is a global one: `E` is isomorphic in the
derived category to a strictly perfect complex of `𝒪_{yoneda.obj U}`-modules.

## Main results

* `AlgebraicGeometry.Space.exists_isStrictlyPerfect_iso_of_isPerfect`: a perfect object on an
  affine represented algebraic space has a global strictly perfect model.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

section Affine

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- **A perfect object on an affine represented algebraic space has a global strictly perfect
model.** If the underlying scheme of `U` is affine and `E` is a perfect object of
`D(𝒪_{yoneda.obj U})`, then `E` is isomorphic in the derived category to a strictly perfect
complex of `𝒪_{yoneda.obj U}`-modules. -/
theorem exists_isStrictlyPerfect_iso_of_isPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPerfect E) :
    ∃ P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)) P ∧
      Nonempty (E ≅ DerivedCategory.Q.obj P) := by
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E
    (qcohDerived_of_isPerfect B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E hE)
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_isStrictlyPerfect_iso_representedAffineDerivedAssociated_obj
    B S hS U ((representedAffineDerivedSections B S hS U).obj E)
    (isPerfect_representedAffineDerivedSections_obj B S hS U E hE)
  exact ⟨P, hP,
    ⟨(asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)).symm ≪≫ e⟩⟩

end Affine

end AlgebraicGeometry.Space

end

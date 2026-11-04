module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison

/-!
# The trivialisation of derived internal Hom out of the structure sheaf, at the Hom complex

Let `(𝒞, 𝒪)` be a ringed site. Derived internal Hom out of `𝒪[0]` is the identity functor,
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso`, and the comparison of
[Stacks, Tag 08JH] presents derived internal Hom out of a complex by the internal Hom complex,
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`. This file identifies the composite
of the two: **it is the class of evaluation at the unit section.**

The point of having it is that the comparison and the trivialisation are each opaque — both are
built from a K-injective resolution — while evaluation at the unit section
(`AlgebraicGeometry.RingedSite.structureSheafHomEvaluation`) is a morphism of complexes, and an
invertible one. So a map `𝒪[0] ⟶ R𝑆heafHom_𝒪(E, 𝒪[0])` assembled from the trivialisation and the
contravariant functoriality of derived internal Hom is, after the comparison is cancelled, the
image under `Q` of a single morphism of complexes.

## Main results

* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_comp_derivedStructureSheafHomIso` —
  the comparison out of `𝒪[0]`, followed by the trivialisation, is the class of evaluation at the
  unit section. The target is an **arbitrary** complex.

## Implementation notes

The target is not K-injective, so this is a descent, exactly as in the ringed-space special case
`Stacks.SheafOfModules.strictlyPerfectHomComparison_comp_derivedStructureSheafHomIso`, which this
statement generalizes and which is now deduced from it: the comparison is natural in the target
for arbitrary complexes, at the K-injective resolution of the target it is the inverse of the
model comparison, and there the trivialisation *is* that model comparison followed by evaluation
at the unit section. What remains is the complex-level naturality of evaluation at the unit
section, and the augmentation into the resolution is invertible in the derived category, so it
cancels.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The derived identification `R𝑆heafHom_𝒪(𝒪[0], QF) ≅ QF` is the class of evaluation at the
unit section**, read through the comparison of [Stacks, Tag 08JH] out of the class of the internal
Hom complex. The target `F` is arbitrary. -/
theorem strictlyPerfectHomComparison_comp_derivedStructureSheafHomIso :
    strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X)
          (structureSheafComplex X) F ≫
        (derivedStructureSheafHomIso X (DerivedCategory.Q.obj F)).hom =
      DerivedCategory.Q.map (structureSheafHomEvaluation X F) := by
  have : ((kInjectiveResolution X).obj F).IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective _ _
  have : IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have hnat₁ := strictlyPerfectHomComparison_naturality_target X
    (derivedInternalHomOfBifunctor X) (structureSheafComplex X) F
    ((kInjectiveResolution X).obj F) ((kInjectiveAugmentation X).app F)
  have hnat₂ := derivedStructureSheafHomIso_naturality X
    (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F))
  have hki := strictlyPerfectHomComparison_eq_homComparison_inv X
    (derivedInternalHomOfBifunctor X) (structureSheafComplex X)
    ((kInjectiveResolution X).obj F)
  have hmodel := derivedStructureSheafHomIso_model X ((kInjectiveResolution X).obj F)
  have hev := structureSheafHomEvaluation_naturality X ((kInjectiveAugmentation X).app F)
  refine (cancel_mono (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F))).mp ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t ↦ _ ≫ t) hnat₂.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t ↦ t ≫ _) hnat₁.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t ↦ _ ≫ (t ≫ _)) hki).trans ?_
  refine (congrArg (fun t ↦ _ ≫ (_ ≫ t)) hmodel).trans ?_
  refine (congrArg (fun t ↦ _ ≫ t) (Iso.inv_hom_id_assoc _ _)).trans ?_
  refine (DerivedCategory.Q.map_comp _ _).symm.trans ?_
  exact (congrArg DerivedCategory.Q.map hev).trans (DerivedCategory.Q.map_comp _ _)

end AlgebraicGeometry.RingedSite

end

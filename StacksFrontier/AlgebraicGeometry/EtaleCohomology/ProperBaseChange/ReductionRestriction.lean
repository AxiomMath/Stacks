module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSupportRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction

/-!
# Restriction to a scalar extension and the reduction of a scheme

For a scheme `X` over a field `k` and an extension `k'/k`, surjectivity (and bijectivity) of the
restriction map `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` is the same for `F` and for its inverse
image `F|_{X_red}` on the reduction, with `X_red` regarded over `k` through `X`.

The closed immersion `i : X_red ⟶ X` is a universal homeomorphism, so inverse image along it is an
equivalence of étale topoi (Stacks 03SI) and the unit `F ⟶ i_* i^{-1} F` is an isomorphism; and `i`
is finite, so restriction on the cohomology of `i_* G` is restriction on the cohomology of `G`
(`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite`).
This is the reduction to reduced schemes in the dévissage of Stacks 03SC (7).

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_iff_reduction`
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_iff_reduction`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (π : X ⟶ Spec (.of k))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf X.reduction.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' (X.reductionι ≫ π)).smallEtaleTopology
    AddCommGrpCat.{u + 1})]

/-- The unit `F ⟶ i_* i^{-1} F` along the reduction `i : X_red ⟶ X` is an isomorphism. -/
theorem isIso_unit_reductionι (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} X.reductionι).unit.app F) := by
  have : UniversalHomeomorphism X.reductionι :=
    inferInstanceAs (UniversalHomeomorphism X.nilradical.subschemeι)
  have := etaleAbelianInverseImage_isEquivalence_of_universalHomeomorphism.{u, 0} X.reductionι
  infer_instance

/-- The unit isomorphism `F ≅ i_* i^{-1} F` along the reduction `i : X_red ⟶ X`. -/
private noncomputable def unitIsoReductionι (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    F ≅ (etaleAbelianDirectImage.{u, 0} X.reductionι).obj
      ((etaleAbelianInverseImage.{u, 0} X.reductionι).obj F) :=
  have := isIso_unit_reductionι F
  asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} X.reductionι).unit.app F)

/-- **Surjectivity of restriction can be tested on the reduction.** -/
theorem surjective_etaleCohomologyRestrictionMap_iff_reduction
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
        F q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w}
        (scalarExtensionFst k k' (X.reductionι ≫ π))
        ((etaleAbelianInverseImage.{u, 0} X.reductionι).obj F) q) := by
  rw [← etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, w}
    X.reductionι _ _ _ (isPullback_scalarExtension_closed k k' π X.reductionι)]
  exact ⟨surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, w} _
    (unitIsoReductionι F) q,
    surjective_etaleCohomologyRestrictionMap_of_iso_objectUniverse.{u, w} _
    (unitIsoReductionι F).symm q⟩

/-- **Bijectivity of restriction can be tested on the reduction.** -/
theorem bijective_etaleCohomologyRestrictionMap_iff_reduction
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' π)
        F q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w}
        (scalarExtensionFst k k' (X.reductionι ≫ π))
        ((etaleAbelianInverseImage.{u, 0} X.reductionι).obj F) q) := by
  rw [← etaleCohomologyRestrictionMap_bijective_directImage_iff_of_isFinite.{u, w}
    X.reductionι _ _ _ (isPullback_scalarExtension_closed k k' π X.reductionι)]
  exact ⟨bijective_etaleCohomologyRestrictionMap_of_iso.{u, w} _ (unitIsoReductionι F) q,
    bijective_etaleCohomologyRestrictionMap_of_iso.{u, w} _ (unitIsoReductionι F).symm q⟩

end Stacks.EtaleCohomology

end

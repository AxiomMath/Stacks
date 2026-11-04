module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation

/-!
# The chain-level value of the evaluation of [stacks 0A63]

Write `ev` for the chain-level evaluation
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor` of the internal Hom complex, the
uncurrying of the identity. At a K-flat `X` and a K-injective `I`, the evaluation
`StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation` of [stacks 0A63] is

`RHom(Q X, Q I) ⊗ᴸ Q X --(homIso ⊗ 𝟙)--> Q(Hom(X, I)) ⊗ᴸ Q X --tensorIso--> Q(Hom(X, I) ⊗ X)
--Q(ev)--> Q I`,

where `homIso` is `StacksDraft.DerivedHom.DerivedHomData.homIso` and `tensorIso` is
`StacksDraft.DerivedHom.DerivedHomData.tensorIso`.

## Main results

* `StacksDraft.DerivedHom.DerivedHomData.evaluation_eq_model` -- the value for a
  `StacksDraft.DerivedHom.DerivedHomData`, that is at module universe equal to the ring universe.
* `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_evaluation_eq_model` -- the value for
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` at an independent module universe, at the
  scalar transports of localized complexes of `ULift R`-modules, through the model comparisons
  `StacksDraft.DerivedHom.derivedHomModelIso` and `StacksDraft.DerivedHom.derivedTensorModelIso`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor MonoidalCategory

namespace StacksDraft.DerivedHom

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- If the transpose of `t` is the inverse of an isomorphism `e` with the internal Hom, then the
evaluation is `e.hom ⊗ 𝟙` followed by `t`. -/
private theorem evaluation_eq_of_homEquiv_symm_eq {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (A : DerivedHomAdjunction R)
    {K L M : DerivedCategory (ModuleCat.{v} R)} (e : A.hom.obj (Opposite.op L, M) ≅ K)
    (t : A.tensor.obj (K, L) ⟶ M) (h : (A.homEquiv K L M).symm t = e.inv) :
    A.evaluation L M = A.tensor.map (e.hom, 𝟙 L) ≫ t := by
  have hnat := A.homEquiv_naturality_left e.hom e.inv
  rwa [Iso.hom_inv_id, ← h, AddEquiv.apply_symm_apply] at hnat

open CochainComplex HomComplex in
/-- The evaluation of the tensor--Hom adjunction at a K-flat argument and a K-injective
target is the localized chain-level evaluation, read through the two comparisons. -/
theorem DerivedHomData.evaluation_eq_model {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (d : DerivedHomData R)
    (X I : CochainComplex (ModuleCat.{u} R) ℤ) (hX : X.KFlat) [I.IsKInjective] :
    d.evaluation (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj I) =
      d.tensor.map (show (d.hom.obj (Opposite.op (DerivedCategory.Q.obj X),
            DerivedCategory.Q.obj I), DerivedCategory.Q.obj X) ⟶
          (DerivedCategory.Q.obj (CochainComplex.HomComplexR R X I),
            DerivedCategory.Q.obj X) from
          ((d.homIso X I).hom, 𝟙 (DerivedCategory.Q.obj X))) ≫
        (d.tensorIso (CochainComplex.HomComplexR R X I) X hX).hom ≫
          DerivedCategory.Q.map (DerivedInternalHom.Model.evaluationMor X I) := by
  refine evaluation_eq_of_homEquiv_symm_eq d.toDerivedHomAdjunction (d.homIso X I) _ ?_
  have h := d.homEquiv_symm_map_eq (CochainComplex.HomComplexR R X I) X I hX
    (DerivedInternalHom.Model.evaluationMor X I)
  rw [DerivedInternalHom.Model.evaluationMor,
    DerivedInternalHom.Model.Phi_postcomp_uncurry] at h
  exact h.trans (by rw [CategoryTheory.Functor.map_id]; exact Category.id_comp _)

open CochainComplex HomComplex in
/-- **The chain-level value of the evaluation of [stacks 0A63].** At a K-flat argument `X` and a
K-injective target `I`, the evaluation of the canonical tensor--Hom adjunction on `D(R)` is the
localized chain-level evaluation `DerivedInternalHom.Model.evaluationMor`, read through the
K-injective Hom model `derivedHomModelIso` and the K-flat tensor model
`derivedTensorModelIso`. -/
theorem derivedHomAdjunctionOverRing_evaluation_eq_model {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (X I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ) (hX : X.KFlat)
    [I.IsKInjective] :
    (derivedHomAdjunctionOverRing.{u, v, w} R).evaluation
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj X))
        ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I)) =
      (derivedHomAdjunctionOverRing.{u, v, w} R).tensor.map
          (show ((derivedHomAdjunctionOverRing.{u, v, w} R).hom.obj
                (Opposite.op ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                    (DerivedCategory.Q.obj X)),
                  (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj I)),
              (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj X)) ⟶
            ((derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj
                (CochainComplex.HomComplexR (ULift.{v} R) X I)),
              (derivedScalarEquivalence.{u, v, w} R).functor.obj (DerivedCategory.Q.obj X)) from
            ((derivedHomModelIso.{u, v, w} R X I).hom,
              𝟙 ((derivedScalarEquivalence.{u, v, w} R).functor.obj
                (DerivedCategory.Q.obj X)))) ≫
        (derivedTensorModelIso.{u, v, w} R
            (CochainComplex.HomComplexR (ULift.{v} R) X I) X hX).hom ≫
          (derivedScalarEquivalence.{u, v, w} R).functor.map
            (DerivedCategory.Q.map (DerivedInternalHom.Model.evaluationMor X I)) := by
  refine evaluation_eq_of_homEquiv_symm_eq (derivedHomAdjunctionOverRing.{u, v, w} R)
    (derivedHomModelIso.{u, v, w} R X I) _ ?_
  have h := derivedHomAdjunctionOverRing_homEquiv_symm_apply.{u, v, w}
    (CochainComplex.HomComplexR (ULift.{v} R) X I) X I hX
    (DerivedInternalHom.Model.evaluationMor X I)
  rw [DerivedInternalHom.Model.evaluationMor,
    DerivedInternalHom.Model.Phi_postcomp_uncurry] at h
  exact h.trans (by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact Category.id_comp _)

end StacksDraft.DerivedHom

end

module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedForgetGradedCohomology
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.GradedCohomologyFunctorial

/-!
# The normalisation of the unit of Tag 09LK's reflector on cohomology

Step 3 of the replacement proof of [Stacks, Tag 09LK] consumes a comparison
`β : Hom(K, -) ⟶ Q ⋙ R̃ ⋙ U`, and the clause `unit_app_id` of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` is a statement about the map that `β`
induces on degree-`n` cohomology, read through
`DGCategory.derivedHomReflectorGradedCohomologyIso`. The `β` that steps 1 and 2 produce is built
from the unit `η` of the reflector `L` by
`DGCategory.derivedHomReflectorUnit`, which is the evaluated unit followed by the *inverse* of the
comparison `DGCategory.derivedHomReflectorCompIso`, while the first factor of
`DGCategory.derivedHomReflectorGradedCohomologyIso` is the homology of that same comparison. So
the two cancel, and what the unit does on cohomology is what `η` itself does.

This file proves that cancellation, as a square of natural transformations evaluated at an object:
on the explicit cohomology the unit of the reflector is the map induced by `η.app (Φ X)` after
evaluation at `K`. It is the normalisation the elementwise computation of `unit_app_id` needs, and
it holds for *the reflector's own* unit — not for an arbitrary comparison, the cancellation being
exactly what fails for one.

## What is proved

* `DGCategory.RightModule.derivedForgetGradedCohomologyIso_hom_naturality`: **the source
  identification of step 3 is natural in the module.** The degree-`n` homology of `ev_X (Q_C -)`
  and the explicit cohomology of `- X` are isomorphic as functors of the module, the map on the
  second being `DGCategory.RightModule.gradedCohomologyMapK`. The objectwise isomorphism
  `DGCategory.RightModule.derivedForgetGradedCohomologyIso` is already available; what is added is
  that it is a natural transformation, which is what the naturality clause of
  `CochainComplex.derivedHomLiftIdentificationOfNaturality` needs and what the objectwise statement
  cannot give.
* `DGCategory.derivedHomReflectorUnit_gradedCohomologyMapK`: **the normalisation of the unit.**

## Implementation notes

Both statements are proved by rewriting the two isomorphisms into their two factors — which is a
reflexivity, recorded as
`DGCategory.RightModule.derivedForgetGradedCohomologyIso_hom` and
`DGCategory.derivedHomReflectorGradedCohomologyIso_hom` — and then using naturality of the first
factor and the defining square of `DGCategory.RightModule.gradedCohomologyMapK` on the second. No
property of the reflector is used: the cancellation is formal, and that is the point, since it
makes the normalisation available at the *same* `L`, `η` and `hΦ` that
`DGCategory.exists_derivedHomReflector_data` hands over, with no witness to identify.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

namespace DGCategory

universe w v u v₁ v₂ r

open CategoryTheory CategoryTheory.Limits

namespace RightModule

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]

attribute [local implicit_reducible] DGCategory.K

/-- The source identification of step 3, written as its two factors: the comparison of the
derived evaluation with evaluation on homotopy categories, and the explicit cohomology. -/
theorem derivedForgetGradedCohomologyIso_hom (M : (rightModuleCategory.{v} C).K) (X : C.Obj)
    (n : ℤ) :
    (derivedForgetGradedCohomologyIso C M X n).hom =
      (derivedEvaluationForgetHomologyIso C X n).hom.app M ≫
        (gradedCohomologyIsoK M X n).hom := rfl

/-- **The source identification of step 3 of [Stacks, Tag 09LK] is natural in the module.** For
`u : M ⟶ N` a morphism of `K(Mod^dg(C))`, the map that `u` induces on the degree-`n` homology of
`ev_X (Q_C -)` corresponds to the map `DGCategory.RightModule.gradedCohomologyMapK` that it
induces on the explicit cohomology of the complex `- X`.

The first factor is natural by `DGCategory.RightModule.derivedEvaluationForgetHomologyIso` being
an isomorphism of functors, and the second by the defining square of
`DGCategory.RightModule.gradedCohomologyMapK`. -/
theorem derivedForgetGradedCohomologyIso_hom_naturality (X : C.Obj) (n : ℤ)
    {M N : (rightModuleCategory.{v} C).K} (u : M ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
          ((derivedEvaluationForget C X).map ((derivedQ C).map u)) ≫
        (derivedForgetGradedCohomologyIso C N X n).hom =
      (derivedForgetGradedCohomologyIso C M X n).hom ≫ gradedCohomologyMapK u X n := by
  rw [derivedForgetGradedCohomologyIso_hom, derivedForgetGradedCohomologyIso_hom,
    ← Category.assoc, derivedEvaluationForgetHomologyIso_hom_naturality,
    Category.assoc, gradedCohomologyIsoK_hom_naturality, Category.assoc]

end RightModule

/-! ### At the reflector of steps 1 and 2 -/

section Reflector

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R) (K : C.Obj)
  [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (L : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  {S : Type*} [Category.{v₁} S] [HasZeroObject S] [HasShift S ℤ] [Preadditive S]
  [∀ n : ℤ, (shiftFunctor S n).Additive] [Pretriangulated S] [IsTriangulated S]
  (Φ : S ⥤ (rightModuleCategory.{v} C).K) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (Z : ObjectProperty S) [Z.IsTriangulated]
  {DA : Type*} [Category.{v₂} DA] [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA]
  (q : S ⥤ DA) [q.IsLocalization Z.trW] [q.CommShift ℤ] [q.IsTriangulated]
  (η : 𝟭 (rightModuleCategory.{v} C).K ⟶ L)

attribute [local implicit_reducible] DGCategory.K

omit [IsTriangulated S] [Z.IsTriangulated] [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA] [q.CommShift ℤ]
  [q.IsTriangulated] in
/-- The junction on the source of step 3, written as its two factors: the homology of the
comparison `DGCategory.derivedHomReflectorCompIso`, and the source identification at the
reflected evaluation. -/
theorem derivedHomReflectorGradedCohomologyIso_hom
    (hΦ : ∀ X, Z X → IsZero ((Φ ⋙ L).obj X)) (X : S) (e : (endDGCategory C K).Obj) (n : ℤ) :
    (derivedHomReflectorGradedCohomologyIso C K L Φ Z q hΦ X e n).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
          ((endDerivedForget C K).map
            ((derivedHomReflectorCompIso C K L Φ Z q hΦ).hom.app X)) ≫
        (RightModule.endDerivedForgetGradedCohomologyIso C K (L.obj (Φ.obj X)) e n).hom := rfl

omit [HasDerivedCategory.{w} (ModuleCat.{v} R)] [IsTriangulated S] [Z.IsTriangulated]
  [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA] [∀ n : ℤ, (shiftFunctor DA n).Additive]
  [Pretriangulated DA] [q.CommShift ℤ] [q.IsTriangulated] in
/-- **The unit of the reflector, followed by the comparison, is the evaluated unit.** The
transformation `DGCategory.derivedHomReflectorUnit` is the evaluated unit followed by the inverse
of `DGCategory.derivedHomReflectorCompIso`, so composing it with that comparison returns the
evaluated unit. -/
theorem derivedHomReflectorUnit_app_comp_derivedHomReflectorCompIso_hom_app
    (hΦ : ∀ X, Z X → IsZero ((Φ ⋙ L).obj X)) (X : S) :
    (derivedHomReflectorUnit C K L Φ Z q η hΦ).app X ≫
        (derivedHomReflectorCompIso C K L Φ Z q hΦ).hom.app X =
      (RightModule.derivedQ (endDGCategory C K)).map
        ((evaluationOnK.{v} C K).map (η.app (Φ.obj X))) := by
  change ((derivedEvaluationUnit C K L Φ η).app X ≫
      (derivedHomReflectorCompIso C K L Φ Z q hΦ).inv.app X) ≫
    (derivedHomReflectorCompIso C K L Φ Z q hΦ).hom.app X = _
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, derivedEvaluationUnit_app]

omit [IsTriangulated S] [Z.IsTriangulated] [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA] [q.CommShift ℤ]
  [q.IsTriangulated] in
/-- **The normalisation of the unit of [Stacks, Tag 09LK]'s reflector on cohomology.** Read
through the junction `DGCategory.derivedHomReflectorGradedCohomologyIso`, the map that the unit
`DGCategory.derivedHomReflectorUnit` induces on degree-`n` cohomology is the map that
`η.app (Φ X)`, evaluated at `K`, induces on the explicit cohomology — the comparison
`DGCategory.derivedHomReflectorCompIso` having cancelled against its inverse inside the unit.

This is the square the elementwise computation of the `unit_app_id` clause of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` has to be read through, and it is
stated at the reflector's own unit: for an arbitrary comparison in place of
`DGCategory.derivedHomReflectorCompIso` nothing cancels and no such formula holds. -/
theorem derivedHomReflectorUnit_gradedCohomologyMapK
    (hΦ : ∀ X, Z X → IsZero ((Φ ⋙ L).obj X)) (X : S) (e : (endDGCategory C K).Obj) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
            ((endDerivedForget C K).map
              ((derivedHomReflectorUnit C K L Φ Z q η hΦ).app X)) ≫
          (derivedHomReflectorGradedCohomologyIso C K L Φ Z q hΦ X e n).hom =
      (RightModule.endDerivedForgetGradedCohomologyIso C K (Φ.obj X) e n).hom ≫
        RightModule.gradedCohomologyMapK
          ((evaluationOnK.{v} C K).map (η.app (Φ.obj X))) e n := by
  rw [derivedHomReflectorGradedCohomologyIso_hom, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp,
    derivedHomReflectorUnit_app_comp_derivedHomReflectorCompIso_hom_app C K L Φ Z q η hΦ X]
  exact RightModule.derivedForgetGradedCohomologyIso_hom_naturality (endDGCategory C K) e n
    ((evaluationOnK.{v} C K).map (η.app (Φ.obj X)))

end Reflector

end DGCategory

end

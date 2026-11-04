module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMate
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaComponentInverse
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTranspose
public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution
public import StacksFrontier.Homology.HomComplex.Evaluation.ModelValue

/-!
# The first residue of [stacks 0E2H] with the evaluation of [stacks 0A63] at chain level

`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMate` reduces
`Dualizing.ProjectionFormula.ProjCounitCompat` -- the first of the three things the module
documentation of `StacksFrontier.RingTheory.Dualizing.RelativeCompositionTag` records [stacks 0E2H]
as owing -- to a single mate identity in one variable:

`ω_{RHom_B(Ext N, W)} ≫ i_*(ev_B) = (0E1W_{N,W} ⊗ᴸ_A 𝟙_N) ≫ ev_A`.

This file carries that equation to representatives, and removes the evaluation of [stacks 0A63]
from it.

Three reductions, each strictly a reduction, and then one rewriting:

* the object of `D(B)` may be the scalar transport of the class of a **K-injective** complex of
  `ULift B`-modules, by `Dualizing.ProjectionFormula.projEval_app_eq_of_iso` and
  `StacksDraft.DerivedHom.exists_isKInjective_model`;
* the inverse projection formula may be evaluated at **any** object `Z` presented as isomorphic
  to the internal Hom `RHom_B(Ext N, W)`, because both sides of the identity factor through that
  isomorphism and it cancels -- in particular `Z` may be a localized complex, which is what
  `Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q` asks for;
* with the presentation taken to be the K-injective Hom model
  `StacksDraft.DerivedHom.derivedHomModelIso`, conjugated by a comparison of `Ext N` with the
  scalar transport of a localized K-flat complex (one exists, by
  `StacksDraft.DerivedHom.exists_kFlat_model`), the [stacks 0A63] evaluation is replaced by the
  localized chain-level evaluation
  `StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`.

That last morphism is exactly the one
`Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor` of
`StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorHom` is about, and the chain-level
projection formula that the left-hand side carries through
`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q` is identified with the lax tensor map of
restriction of scalars by
`CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq` of
`StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorProjection`.  So both chain-level
inputs the residue needs are now in the library; what is not done here is the transcription that
puts them together.

## Main results

* `Dualizing.ProjectionFormula.projEval_app_eq_iff_unfold` -- the two sides of the evaluation
  compatibility, unfolded; `Iff.rfl`.
* `Dualizing.ProjectionFormula.projCounitCompat_of_eval_kFlat_kInjective` -- the compatibility at
  a K-flat complex of `A`-modules and a K-injective complex of `ULift B`-modules suffices.
* `Dualizing.ProjectionFormula.projEvalLeft_app_eq_of_model`,
  `Dualizing.ProjectionFormula.projEvalRight_app_eq_of_model` -- both sides at a presentation of
  the internal Hom.
* `Dualizing.ProjectionFormula.projEval_app_eq_iff_of_model`,
  `Dualizing.ProjectionFormula.projEval_app_eq_iff_mate` -- the compatibility there, with the
  common isomorphism cancelled, in the second case with the transposition carried out.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_model` -- `ProjCounitCompat` at every
  object of `D(A)` from the mate identity at representatives and any presentation.
* `StacksDraft.DerivedHom.homEquiv_derivedHomModelIso_inv` and `…_inv_comp` -- the [stacks 0A63]
  transpose of the inverse K-injective Hom model, which is
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_evaluation_eq_model` with the Hom model
  cancelled against its own inverse, and the same read at an arbitrary object of the argument
  slot.
* `Dualizing.ProjectionFormula.projCounitCompat_of_mate_evaluationMor` -- **the sharpest form**:
  `ProjCounitCompat` at every object of `D(A)` from one equation in which the evaluation of
  [stacks 0A63] does not occur.

No `@[stacks]` attribute is placed here: nothing in this file is unconditional about a tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

namespace StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u' v' w'

/-- **The [stacks 0A63] transpose of the inverse K-injective Hom model.**  At a K-flat `X` and a
K-injective `I`, the transpose of `StacksDraft.DerivedHom.derivedHomModelIso.inv` is the K-flat
tensor model followed by the localized chain-level evaluation.  This is
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_evaluation_eq_model` read as a transpose: the
model comparison in the source of the evaluation is cancelled against its own inverse, so what is
left mentions no Hom model at all. -/
theorem homEquiv_derivedHomModelIso_inv (R : Type u') [CommRing R]
    [HasDerivedCategory.{w'} (ModuleCat.{max u' v'} R)]
    (X I : CochainComplex (ModuleCat.{max u' v'} (ULift.{v'} R)) ℤ) (hX : X.KFlat)
    [I.IsKInjective] :
    (derivedHomAdjunctionOverRing.{u', v', w'} R).homEquiv
        ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
          (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v'} R) X I)))
        ((derivedScalarEquivalence.{u', v', w'} R).functor.obj (DerivedCategory.Q.obj X))
        ((derivedScalarEquivalence.{u', v', w'} R).functor.obj (DerivedCategory.Q.obj I))
        (derivedHomModelIso.{u', v', w'} R X I).inv =
      (derivedTensorModelIso.{u', v', w'} R
          (CochainComplex.HomComplexR (ULift.{v'} R) X I) X hX).hom ≫
        (derivedScalarEquivalence.{u', v', w'} R).functor.map
          (DerivedCategory.Q.map (DerivedInternalHom.Model.evaluationMor X I)) := by
  rw [DerivedHomAdjunction.homEquiv_eq_tensor_map_comp_evaluation,
    derivedHomAdjunctionOverRing_evaluation_eq_model.{u', v', w'} (R := R) X I hX,
    ← Category.assoc, DerivedHomAdjunction.tensor_map_comp, Iso.inv_hom_id, Category.id_comp,
    show (derivedHomAdjunctionOverRing.{u', v', w'} R).tensor.map
        (X := ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
            (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v'} R) X I)),
          (derivedScalarEquivalence.{u', v', w'} R).functor.obj (DerivedCategory.Q.obj X)))
        (Y := ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
            (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v'} R) X I)),
          (derivedScalarEquivalence.{u', v', w'} R).functor.obj (DerivedCategory.Q.obj X)))
        (𝟙 _, 𝟙 _) = 𝟙 _ from (derivedHomAdjunctionOverRing.{u', v', w'} R).tensor.map_id _,
    Category.id_comp]

/-- **The [stacks 0A63] transpose of the inverse K-injective Hom model, read at an arbitrary
object of the argument slot.**  `StacksDraft.DerivedHom.homEquiv_derivedHomModelIso_inv`
composed with dinaturality of the transpose: for any morphism `g : Y ⟶ Q X` the transpose of
`derivedHomModelIso.inv` followed by the Hom bifunctor at `g.op` is `g` whiskered into the second
variable, then the K-flat tensor model, then the localized chain-level evaluation.

This is the form a consumer of `Dualizing.ProjectionFormula.projCounitCompat_of_mate_model`
needs: there the argument slot carries `Ext N`, which is not a localized complex, and the only
handle on it is a
comparison `g` with one. -/
theorem homEquiv_derivedHomModelIso_inv_comp (R : Type u') [CommRing R]
    [HasDerivedCategory.{w'} (ModuleCat.{max u' v'} R)]
    (X I : CochainComplex (ModuleCat.{max u' v'} (ULift.{v'} R)) ℤ) (hX : X.KFlat)
    [I.IsKInjective] (Y : DerivedCategory (ModuleCat.{max u' v'} R))
    (g : Y ⟶ (derivedScalarEquivalence.{u', v', w'} R).functor.obj (DerivedCategory.Q.obj X)) :
    (derivedHomAdjunctionOverRing.{u', v', w'} R).homEquiv
        ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
          (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v'} R) X I)))
        Y ((derivedScalarEquivalence.{u', v', w'} R).functor.obj (DerivedCategory.Q.obj I))
        ((derivedHomModelIso.{u', v', w'} R X I).inv ≫
          (derivedHomAdjunctionOverRing.{u', v', w'} R).hom.map
            (show (Opposite.op ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
                  (DerivedCategory.Q.obj X)),
                (derivedScalarEquivalence.{u', v', w'} R).functor.obj
                  (DerivedCategory.Q.obj I)) ⟶
              (Opposite.op Y, (derivedScalarEquivalence.{u', v', w'} R).functor.obj
                (DerivedCategory.Q.obj I)) from
              (g.op, 𝟙 ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
                (DerivedCategory.Q.obj I))))) =
      (derivedHomAdjunctionOverRing.{u', v', w'} R).tensor.map
          (show ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
                (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v'} R) X I)), Y) ⟶
              ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
                  (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v'} R) X I)),
                (derivedScalarEquivalence.{u', v', w'} R).functor.obj
                  (DerivedCategory.Q.obj X)) from
            (𝟙 ((derivedScalarEquivalence.{u', v', w'} R).functor.obj
              (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v'} R) X I))), g)) ≫
        (derivedTensorModelIso.{u', v', w'} R
            (CochainComplex.HomComplexR (ULift.{v'} R) X I) X hX).hom ≫
          (derivedScalarEquivalence.{u', v', w'} R).functor.map
            (DerivedCategory.Q.map (DerivedInternalHom.Model.evaluationMor X I)) := by
  rw [(derivedHomAdjunctionOverRing.{u', v', w'} R).homEquiv_dinaturality g
      (derivedHomModelIso.{u', v', w'} R X I).inv,
    homEquiv_derivedHomModelIso_inv.{u', v', w'} R X I hX]

end StacksDraft.DerivedHom

namespace Dualizing.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe u v

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The goal, restated: the unfolded evaluation compatibility. -/
theorem projEval_app_eq_iff_unfold (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    ((projEvalLeft.{u, v} φ E adj N).app W = (projEvalRight.{u, v} φ E N).app W) ↔
      ((derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
              (Opposite.op (E.functor.obj N), W)) ≫
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
              (E.functor.obj N) W) =
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                  (Opposite.op (E.functor.obj N), W)), N))
            (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.obj
                (Opposite.op N,
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W), N))
            (homRestrictComponent.{u, v} φ E N W, 𝟙 N) ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).evaluation N
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)) :=
  Iff.rfl

/-- Tensoring on the right with a fixed object, on a morphism. -/
private alias tensorRight_map' := Dualizing.ProjectionFormula.tensorRight_map

/-- The transpose over [stacks 0A63] is tensoring on the right followed by evaluation. -/
private theorem homEquiv_eq_tensorRight_map_comp_evaluation (R : Type u) [CommRing R]
    (K L M : DerivedCategory (ModuleCat.{max u v} R))
    (a : K ⟶ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} R).hom.obj
      (Opposite.op L, M)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} R).homEquiv K L M a =
      (tensorRightDerived.{u, max u v} R L).map a ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} R).evaluation L M :=
  (DerivedHomAdjunction.homEquiv_eq_tensor_map_comp_evaluation _ K L M a).trans
    (by rw [tensorRight_map'.{u, max u v}])

/-- **The owed coherence of [stacks 0E2H] at a K-flat complex of `A`-modules and a K-injective
complex of `ULift B`-modules.**  Every object of `D(B)` is isomorphic to the scalar transport of
the class of a K-injective complex, by `StacksDraft.DerivedHom.exists_isKInjective_model`, and
`Dualizing.ProjectionFormula.projEval_app_eq_of_iso` carries the evaluation compatibility along
such an isomorphism, so the compatibility need only be checked there. -/
theorem projCounitCompat_of_eval_kFlat_kInjective (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P →
      ∀ I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ, I.IsKInjective →
        (projEvalLeft.{u, v} φ E adj (DerivedCategory.Q.obj P)).app
            ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
              (DerivedCategory.Q.obj I)) =
          (projEvalRight.{u, v} φ E (DerivedCategory.Q.obj P)).app
            ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
              (DerivedCategory.Q.obj I)))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  refine projCounitCompat_of_eval_kFlat.{u, v} φ E adj (fun P hP J => ?_) N
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_model.{u, max u v, max u v + 1} (R := B)
    (DerivedCategory.Q.obj J)
  exact projEval_app_eq_of_iso.{u, v} φ E adj (DerivedCategory.Q.obj P) e.symm (h P hP I hI)

/-- **The left-hand side at a presentation of the internal Hom.** -/
theorem projEvalLeft_app_eq_of_model (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W Z : DerivedCategory (ModuleCat.{max u v} B))
    (t : Z ≅ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
      (Opposite.op (E.functor.obj N), W)) :
    (projEvalLeft.{u, v} φ E adj N).app W =
      (tensorRightDerived.{u, max u v} A N).map
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.inv) ≫
        (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app Z ≫
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
            ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).map t.hom ≫
              (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
                (E.functor.obj N) W) := by
  show (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
          (Opposite.op (E.functor.obj N), W)) ≫
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
          (E.functor.obj N) W) = _
  have hnat := (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.naturality t.hom
  dsimp only [Functor.comp_map] at hnat
  rw [Functor.map_comp, ← reassoc_of% hnat, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, t.inv_hom_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The right-hand side at a presentation of the internal Hom.** -/
theorem projEvalRight_app_eq_of_model (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W Z : DerivedCategory (ModuleCat.{max u v} B))
    (t : Z ≅ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
      (Opposite.op (E.functor.obj N), W)) :
    (projEvalRight.{u, v} φ E N).app W =
      (tensorRightDerived.{u, max u v} A N).map
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.inv) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z) N
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.hom ≫
            homRestrictComponent.{u, v} φ E N W) := by
  have hid : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.inv ≫
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.hom = 𝟙 _ := by
    rw [← Functor.map_comp, t.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [projEvalRight_app_eq_homEquiv.{u, v} φ E N W,
    homEquiv_eq_tensorRight_map_comp_evaluation.{u, v} A _ N _
      (homRestrictComponent.{u, v} φ E N W),
    homEquiv_eq_tensorRight_map_comp_evaluation.{u, v} A, ← Category.assoc,
    ← Functor.map_comp, ← Category.assoc, hid, Category.id_comp]

/-- **The owed coherence of [stacks 0E2H] at a presentation of the internal Hom.**  Both sides of
the evaluation compatibility factor through the same isomorphism, so the identity at `W` is
equivalent to one in which the inverse projection formula sits at `Z` -- which may be taken to be
the class of a cochain complex -- and the component of [stacks 0E1W] is read through that
presentation. -/
theorem projEval_app_eq_iff_of_model (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W Z : DerivedCategory (ModuleCat.{max u v} B))
    (t : Z ≅ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
      (Opposite.op (E.functor.obj N), W)) :
    ((projEvalLeft.{u, v} φ E adj N).app W = (projEvalRight.{u, v} φ E N).app W) ↔
      ((derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app Z ≫
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
              ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).map t.hom ≫
                (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
                  (E.functor.obj N) W) =
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z) N
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.hom ≫
            homRestrictComponent.{u, v} φ E N W)) := by
  have : IsIso ((tensorRightDerived.{u, max u v} A N).map
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.inv)) := inferInstance
  rw [projEvalLeft_app_eq_of_model.{u, v} φ E adj N W Z t,
    projEvalRight_app_eq_of_model.{u, v} φ E N W Z t]
  exact ⟨fun hh => (cancel_epi _).mp hh, fun hh => by rw [hh]⟩

/-- **The owed coherence of [stacks 0E2H] as a mate identity at a presentation of the internal
Hom.**  `Dualizing.ProjectionFormula.projEval_app_eq_iff_of_model` with the factor
`(- ⊗ᴸ_B 𝟙_{Ext N}) ≫ ev_B` read as the [stacks 0A63] transpose it is: the identity says that the
inverse projection formula at `Z` followed by derived restriction of the transpose of `t.hom` is
the transpose over `A` of `i_*(t.hom)` followed by the component of [stacks 0E1W]. -/
theorem projEval_app_eq_iff_mate (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W Z : DerivedCategory (ModuleCat.{max u v} B))
    (t : Z ≅ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
      (Opposite.op (E.functor.obj N), W)) :
    ((projEvalLeft.{u, v} φ E adj N).app W = (projEvalRight.{u, v} φ E N).app W) ↔
      ((derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app Z ≫
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homEquiv Z
                (E.functor.obj N) W t.hom) =
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z) N
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.hom ≫
            homRestrictComponent.{u, v} φ E N W)) := by
  rw [homEquiv_eq_tensorRight_map_comp_evaluation.{u, v}]
  exact projEval_app_eq_iff_of_model.{u, v} φ E adj N W Z t

/-- **The sharpest form of the first residue of [stacks 0E2H].**  The whole of
`Dualizing.ProjectionFormula.ProjCounitCompat`, at every object of `D(A)`, follows from the mate
identity of `Dualizing.ProjectionFormula.projEval_app_eq_iff_mate` at the class of a K-flat
complex of `A`-modules, the scalar transport of the class of a K-injective complex of `ULift
B`-modules, and
*any* presentation of the internal Hom there -- in particular the one the K-injective Hom model
`StacksDraft.DerivedHom.derivedHomModelIso` provides, which is the form in which the evaluation of
[stacks 0A63] has the chain-level value
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_evaluation_eq_model`. -/
theorem projCounitCompat_of_mate_model (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P →
      ∀ I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ, I.IsKInjective →
      ∃ (Z : DerivedCategory (ModuleCat.{max u v} B))
        (t : Z ≅ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
          (Opposite.op (E.functor.obj (DerivedCategory.Q.obj P)),
            (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
              (DerivedCategory.Q.obj I))),
        (derivedProjNatIso.{u, max u v} φ E _ adj (DerivedCategory.Q.obj P)).inv.app Z ≫
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homEquiv Z
                (E.functor.obj (DerivedCategory.Q.obj P))
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I)) t.hom) =
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z)
            (DerivedCategory.Q.obj P)
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                (DerivedCategory.Q.obj I)))
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map t.hom ≫
              homRestrictComponent.{u, v} φ E (DerivedCategory.Q.obj P)
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I))))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  refine projCounitCompat_of_eval_kFlat_kInjective.{u, v} φ E adj (fun P hP I hI => ?_) N
  obtain ⟨Z, t, ht⟩ := h P hP I hI
  exact (projEval_app_eq_iff_mate.{u, v} φ E adj (DerivedCategory.Q.obj P)
    ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
      (DerivedCategory.Q.obj I)) Z t).mpr ht



/-- **The first residue of [stacks 0E2H] with the evaluation of [stacks 0A63] at chain level.**
`Dualizing.ProjectionFormula.projCounitCompat_of_mate_model` with the presentation of the
internal Hom taken to be the K-injective Hom model `StacksDraft.DerivedHom.derivedHomModelIso`,
conjugated by a comparison `g` of `Ext N` with the scalar transport of a localized K-flat complex
-- one exists by `StacksDraft.DerivedHom.exists_kFlat_model`.  The evaluation of [stacks 0A63] has
then disappeared in favour of the localized chain-level evaluation
`StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`, which is the morphism
`Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor` is about.

So the whole of `Dualizing.ProjectionFormula.ProjCounitCompat`, at every object of `D(A)`, follows
from one equation whose left-hand side mentions only the inverse projection formula at a localized
object, the K-flat tensor model and the chain-level evaluation. -/
theorem projCounitCompat_of_mate_evaluationMor (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P →
      ∀ X I : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ,
      ∀ hX : X.KFlat, ∀ [I.IsKInjective],
      ∀ g : E.functor.obj (DerivedCategory.Q.obj P) ≅
        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj X),
        (derivedProjNatIso.{u, max u v} φ E _ adj (DerivedCategory.Q.obj P)).inv.app
              ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                (DerivedCategory.Q.obj
                  (CochainComplex.HomComplexR (ULift.{max u v} B) X I))) ≫
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
                  (show ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                        (DerivedCategory.Q.obj
                          (CochainComplex.HomComplexR (ULift.{max u v} B) X I)),
                      E.functor.obj (DerivedCategory.Q.obj P)) ⟶
                    ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                        (DerivedCategory.Q.obj
                          (CochainComplex.HomComplexR (ULift.{max u v} B) X I)),
                      (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                        (DerivedCategory.Q.obj X)) from
                    (𝟙 ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                      (DerivedCategory.Q.obj
                        (CochainComplex.HomComplexR (ULift.{max u v} B) X I))), g.hom)) ≫
                (derivedTensorModelIso.{u, max u v, max u v + 1} B
                    (CochainComplex.HomComplexR (ULift.{max u v} B) X I) X hX).hom ≫
                  (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.map
                    (DerivedCategory.Q.map
                      (DerivedInternalHom.Model.evaluationMor X I))) =
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                (DerivedCategory.Q.obj
                  (CochainComplex.HomComplexR (ULift.{max u v} B) X I))))
            (DerivedCategory.Q.obj P)
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                (DerivedCategory.Q.obj I)))
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                ((derivedHomModelIso.{u, max u v, max u v + 1} B X I).inv ≫
                  (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.map
                    (show (Opposite.op
                          ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                            (DerivedCategory.Q.obj X)),
                        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                          (DerivedCategory.Q.obj I)) ⟶
                      (Opposite.op (E.functor.obj (DerivedCategory.Q.obj P)),
                        (derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                          (DerivedCategory.Q.obj I)) from
                      (g.hom.op,
                        𝟙 ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                          (DerivedCategory.Q.obj I))))) ≫
              homRestrictComponent.{u, v} φ E (DerivedCategory.Q.obj P)
                ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
                  (DerivedCategory.Q.obj I))))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  refine projCounitCompat_of_mate_model.{u, v} φ E adj (fun P hP I hI => ?_) N
  have := hI
  obtain ⟨X, hX, ⟨gx⟩⟩ := exists_kFlat_model.{u, max u v, max u v + 1} (R := B)
    (E.functor.obj (DerivedCategory.Q.obj P))
  refine ⟨_, (derivedHomModelIso.{u, max u v, max u v + 1} B X I).symm ≪≫
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.mapIso
      (gx.symm.op.prod (Iso.refl
        ((derivedScalarEquivalence.{u, max u v, max u v + 1} B).functor.obj
          (DerivedCategory.Q.obj I)))), ?_⟩
  exact (congrArg (fun z =>
      (derivedProjNatIso.{u, max u v} φ E _ adj (DerivedCategory.Q.obj P)).inv.app _ ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map z)
    (homEquiv_derivedHomModelIso_inv_comp.{u, max u v, max u v + 1} B X I hX
      (E.functor.obj (DerivedCategory.Q.obj P)) gx.symm.hom)).trans
    (h P hP X I hX gx.symm)


end Dualizing.ProjectionFormula

end

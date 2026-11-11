module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationCohomologyNotProjectiveLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusFieldExtension
public import StacksFrontier.FieldTheory.Galois.PerfectClosureAutomorphisms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram

/-!
# A curve over `k` as a curve over the perfect closure of `k`

Let `k` be a field, `k̄` an algebraic closure of `k`, and `k' = perfectClosure k k̄` the relative
perfect closure of `k` in `k̄`. For a geometrically connected smooth curve `X` over `k`, the base
change `X' = X ×_k k'` is a geometrically connected smooth curve over the perfect field `k'`, over
which `k̄` is separable, and:

* its geometric fibre is the geometric fibre of `X`: `X'_{k̄} ≅ X_{k̄}`
  (`Stacks.EtaleCohomology.fieldBaseChangeExtensionIso`);
* a geometric point `η̄` of `X_{k̄}` gives the geometric point `η̄'` of `X'_{k̄}`, and the images of
  `η̄'` in `X` along `X'_{k̄} ⟶ X' ⟶ X` and of `η̄` along `X_{k̄} ⟶ X` agree;
* `Aut(k̄/k') = Aut(k̄/k)` as topological groups (`perfectClosureAlgEquivContinuousMulEquiv`).

This is the model on which statements about the Galois action on `X_{k̄}` over an arbitrary field
reduce to the case where `k̄` is separable over the base field.

## Main definitions

* `AlgebraicGeometry.perfectClosureModel`: `X' = X ×_k k'`, as an object of the big étale site.
* `AlgebraicGeometry.perfectClosureModelHom`: its structure morphism `X' ⟶ Spec k'`.
* `AlgebraicGeometry.perfectClosureModelPoint`: the geometric point `η̄'` of `X'_{k̄}`.
* `AlgebraicGeometry.perfectClosureModelFundamentalGroupMap`: `π₁(X', η̄') ⟶ π₁(X, η̄)`, induced
  by the projection `X' ⟶ X`.
* `AlgebraicGeometry.perfectClosureModelRes`: restriction of representations along it.

## Main results

* `AlgebraicGeometry.isUnit_natCard_perfectClosure`: `#Λ` is invertible in `k'`.
* `AlgebraicGeometry.not_exists_iso_projectiveLine_perfectClosureModel`: `X'_{k̄} ≇ ℙ¹_{k̄}` if
  `X_{k̄} ≇ ℙ¹_{k̄}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius Stacks.EtaleCohomology Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry

/-- The isomorphism of étale fundamental groups at two equal geometric points. -/
def etaleFundamentalGroupContinuousMulEquivOfEq {S : Scheme.{u}} [ConnectedSpace S]
    {x x' : GeometricPoint S} (h : x = x') :
    EtaleFundamentalGroup S x ≃ₜ* EtaleFundamentalGroup S x' := by
  subst h
  exact ContinuousMulEquiv.refl _

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K]

/-- **The base change `X' = X ×_k k'` to the relative perfect closure `k'` of `k` in `k̄`**, as an
object of the big étale site `B`. -/
abbrev perfectClosureModel : B.Scheme :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f (perfectClosure k K)
  fieldBaseChangeObj B X f (perfectClosure k K)
    (contains_fieldBaseChange_of_isCurve B X f (perfectClosure k K))

/-- The structure morphism `X' ⟶ Spec k'`. -/
abbrev perfectClosureModelHom :
    (perfectClosureModel B X f K).1 ⟶ Spec (.of (perfectClosure k K)) :=
  pullback.snd (Over.mk f).hom (specAlgebraMap k (perfectClosure k K))

/-- The projection `X' ⟶ X`. -/
abbrev perfectClosureModelProj : perfectClosureModel B X f K ⟶ X :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f (perfectClosure k K)
  fieldBaseChangeObjProj B X f (perfectClosure k K)
    (contains_fieldBaseChange_of_isCurve B X f (perfectClosure k K))

/-- `X'` is a curve over `k'`. -/
instance isCurve_perfectClosureModelHom :
    IsCurve (perfectClosure k K) (perfectClosureModelHom B X f K) :=
  isCurve_fieldBaseChange_of_smooth B X f (perfectClosure k K)

/-- `X'` is smooth over `k'`. -/
instance smooth_perfectClosureModelHom : Smooth (perfectClosureModelHom B X f K) :=
  MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k (perfectClosure k K)))
    (‹Smooth f› : Smooth (Over.mk f).hom)

/-- `X'` is geometrically connected over `k'`. -/
instance geometricallyConnected_perfectClosureModelHom :
    GeometricallyConnected (perfectClosureModelHom B X f K) :=
  have : GeometricallyConnected (Over.mk f).hom := ‹GeometricallyConnected f›
  inferInstance

/-- `k̄` is an algebraic closure of `k'`. -/
instance isAlgClosure_perfectClosure' : IsAlgClosure (perfectClosure k K) K :=
  isAlgClosure_perfectClosure k K

/-- `k̄` is separable over `k'`, the latter being perfect. -/
instance isSeparable_perfectClosure' : Algebra.IsSeparable (perfectClosure k K) K :=
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  isSeparable_of_isAlgClosure_perfectClosure k K

/-- **`X'_{k̄} ≅ X_{k̄}`**: the geometric fibre of `X'` over `k'` is the geometric fibre of `X`. -/
abbrev perfectClosureModelFibreIso :
    fieldBaseChange (Over.mk (perfectClosureModelHom B X f K)) K ≅
      fieldBaseChange (Over.mk f) K :=
  fieldBaseChangeExtensionIso (Over.mk f) (perfectClosure k K) K

variable (y : GeometricPoint (fieldBaseChange (Over.mk f) K))

/-- **The geometric point `η̄'` of `X'_{k̄}`** corresponding to `η̄` under `X'_{k̄} ≅ X_{k̄}`. -/
abbrev perfectClosureModelPoint :
    GeometricPoint (fieldBaseChange (Over.mk (perfectClosureModelHom B X f K)) K) :=
  y.map (perfectClosureModelFibreIso B X f K).inv

/-- The image of `η̄'` in `X` along `X'_{k̄} ⟶ X' ⟶ X` is the image of `η̄` along
`X_{k̄} ⟶ X`. -/
theorem perfectClosureModelPoint_map_map :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    ((perfectClosureModelPoint B X f K y).map
        (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
          K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom).map
        (perfectClosureModelProj B X f K).hom =
      y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom := by
  have h := fieldBaseChangeExtensionIso_hom_fst (Over.mk f) (perfectClosure k K) K
  rw [GeometricPoint.map_map, GeometricPoint.map_map]
  congr 1
  change (fieldBaseChangeExtensionIso (Over.mk f) (perfectClosure k K) K).inv ≫
      pullback.fst (extensionOver (Over.mk f) (perfectClosure k K)).hom
        (specAlgebraMap (perfectClosure k K) K) ≫
      extensionProj (Over.mk f) (perfectClosure k K) =
    pullback.fst (Over.mk f).hom (specAlgebraMap k K)
  rw [← h, Iso.inv_hom_id_assoc]

/-- **`π₁(X', η̄') ⟶ π₁(X, η̄)`**, induced by the projection `X' ⟶ X`, the base points being
identified by `AlgebraicGeometry.perfectClosureModelPoint_map_map`. -/
def perfectClosureModelFundamentalGroupMap :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    EtaleFundamentalGroup (perfectClosureModel B X f K).1
        ((perfectClosureModelPoint B X f K y).map
          (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
            K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom) →ₜ*
      EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  ContinuousMonoidHom.comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (etaleFundamentalGroupContinuousMulEquivOfEq (perfectClosureModelPoint_map_map B X f K y)))
    (etaleFundamentalGroupMap (perfectClosureModelProj B X f K).hom _)

/-- **Restriction of representations along `π₁(X', η̄') ⟶ π₁(X, η̄)`**: a finite `Λ`-module with
a continuous action of `π₁(X, η̄)`, read as one of `π₁(X', η̄')`. -/
abbrev perfectClosureModelRes (Λ : Type) [Ring Λ] :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
      (perfectClosureModelHom B X f K)
    letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)) ⥤
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup
        (perfectClosureModel B X f K).1
        ((perfectClosureModelPoint B X f K y).map
          (fieldBaseChangeObjProj B (perfectClosureModel B X f K) (perfectClosureModelHom B X f K)
            K (contains_fieldBaseChange_of_isCurve B _ _ K)).hom)) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := connectedSpace_of_isCurve B (perfectClosureModel B X f K)
    (perfectClosureModelHom B X f K)
  letI := connectedSpace_fieldBaseChange (perfectClosureModelHom B X f K) K
  finiteTypeContinuousModuleRes.{0, u + 1, u + 1} Λ
    (perfectClosureModelFundamentalGroupMap B X f K y)

omit [IsAlgClosure k K] in
/-- `#Λ` is invertible in `k'` when it is in `k`. -/
theorem isUnit_natCard_perfectClosure (Λ : Type) (hΛ : IsUnit ((Nat.card Λ : ℕ) : k)) :
    IsUnit ((Nat.card Λ : ℕ) : perfectClosure k K) := by
  simpa using hΛ.map (algebraMap k (perfectClosure k K))

omit [Smooth f] [GeometricallyConnected f] [IsAlgClosure k K] in
/-- **`X'_{k̄} ≇ ℙ¹_{k̄}` if `X_{k̄} ≇ ℙ¹_{k̄}`**, the two geometric fibres being isomorphic over
`Spec k̄`. -/
theorem not_exists_iso_projectiveLine_perfectClosureModel
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    ¬ ∃ e : fieldBaseChange (Over.mk (perfectClosureModelHom B X f K)) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk (perfectClosureModelHom B X f K)).hom
          (specAlgebraMap (perfectClosure k K) K) := by
  rintro ⟨e, he⟩
  refine hP ⟨(perfectClosureModelFibreIso B X f K).symm ≪≫ e, ?_⟩
  have h := fieldBaseChangeExtensionIso_hom_snd (Over.mk f) (perfectClosure k K) K
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he, ← h, Iso.inv_hom_id_assoc]

end AlgebraicGeometry

end

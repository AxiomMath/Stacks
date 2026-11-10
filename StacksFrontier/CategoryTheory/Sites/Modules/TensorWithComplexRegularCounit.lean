module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex

/-!
# The counit of the tensor--Hom adjunction of Tag 09LV at `K`

The counit `Hom(K, K) ⊗_E K ⟶ K` of the adjunction of Tag 09LV is invertible. The isomorphism
`Hom(K, K) ⊗_E K ≅ K` is the map out of the sheafified tensor complex whose composite with the
sectionwise tensor complex is sectionwise evaluation; it is characterised by that property, and
the counit is the cocycle of this isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDG_adjunction_counit_app`: the counit of
  the adjunction of Tag 09LV is invertible at `K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open DifferentialGraded DifferentialGradedModule
open CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

attribute [local implicit_reducible] ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

variable (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]

section RegularInverse

variable (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
variable (D : TensorWithComplexData.{u, v, w, t, s, o} X R K)

/-- A map of complexes out of `Hom(K, K) ⊗_E K` into `K` whose composite with the sectionwise
tensor complex is sectionwise evaluation is an isomorphism. -/
private lemma isIso_of_sectionwiseToSheaf_comp_eq
    (g : Quiver.Hom (V := CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
      (D.functor.obj ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K))) (liftComplex.{u, v, w, t, s} X K))
    (hg : D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)) ≫
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g =
        regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D) :
    IsIso g := by
  let : (SheafOfModules.forget.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Full :=
    (SheafOfModules.fullyFaithfulForget.{max u v w t s}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).full
  let : (SheafOfModules.forget.{max u v w t s}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Faithful :=
    (SheafOfModules.fullyFaithfulForget.{max u v w t s}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).faithful
  let G := (SheafOfModules.forget.{max u v w t s}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex (ComplexShape.up ℤ)
  let e := regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D
  have : IsIso e := regularSectionwiseEvalHom_isIso.{u, v, w, t, s, o} X R K D
  replace hg : D.sectionwiseToSheaf _ ≫ G.map g = e := hg
  let j : HomologicalComplex.Hom (liftComplex.{u, v, w, t, s} X K) (D.functor.obj
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))) := G.preimage
    (inv e ≫ D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)))
  have hj : G.map j = inv e ≫ D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) := G.map_preimage _
  refine ⟨j, ?_, ?_⟩
  · obtain ⟨g', hg', hu'⟩ := D.sectionwiseUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) (D.functor.obj ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K)))
      (D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)))
    exact (hu' _ (by
      change D.sectionwiseToSheaf _ ≫ G.map (g ≫ j) = _
      rw [Functor.map_comp, ← Category.assoc, hg, hj]
      simp)).trans (hu' _ (by simp)).symm
  · apply G.map_injective
    rw [Functor.map_comp, hj, Category.assoc, hg]
    simp

private noncomputable def regularSheafIsoOfSpec :
    CategoryTheory.Iso (C := CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
      (D.functor.obj ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K))) (liftComplex.{u, v, w, t, s} X K) :=
  haveI := isIso_of_sectionwiseToSheaf_comp_eq.{u, v, w, t, s, o} X R K D _
    (Classical.choose_spec (D.sectionwiseUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) (liftComplex.{u, v, w, t, s} X K)
        (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D))).1
  asIso (Classical.choose (D.sectionwiseUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) (liftComplex.{u, v, w, t, s} X K)
        (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D)))

private lemma regularSheafIsoOfSpec_hom_spec :
    D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)) ≫
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (regularSheafIsoOfSpec.{u, v, w, t, s, o} X R K D).hom =
      regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D :=
  (Classical.choose_spec (D.sectionwiseUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) (liftComplex.{u, v, w, t, s} X K)
        (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D))).1


end RegularInverse

attribute [local instance_reducible] tensorSectionwise tensorDegreePresheaf tensorSheafified
  tensorPresheafMap tensorPresheafDifferential

variable [ScalarSections.{u, v, w, t, s, o} X R]

/-- Tensoring the regular endomorphism module with `K` returns `K`, through
`regularSheafIsoOfSpec`. -/
private noncomputable def tensorWithComplexDGRegularOfSpec
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    letI : Category (CompDG.{u, v, w, t, s, o} X R).Obj := (CompDG.{u, v, w, t, s, o} X
      R).instCategoryComp
    (((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) :
        (CompDG.{u, v, w, t, s, o} X R).Comp) ≅
      (liftComplex.{u, v, w, t, s} X K : (CompDG.{u, v, w, t, s, o} X R).Comp)) :=
  by
  letI : Category (CompDG.{u, v, w, t, s, o} X R).Obj :=
    (CompDG.{u, v, w, t, s, o} X R).instCategoryComp
  let e := regularSheafIsoOfSpec.{u, v, w, t, s, o} X R K
    (tensorWithComplexDG.{u, v, w, t, s, o} X R K)
  refine ⟨CochainComplex.HomComplex.Cocycle.ofHom e.hom,
    CochainComplex.HomComplex.Cocycle.ofHom e.inv, ?_, ?_⟩
  all_goals
    apply Subtype.ext
    refine (Cochain.ofHom_comp _ _).symm.trans ?_
    simp
    rfl

/-- **The counit of the tensor--Hom adjunction of Tag 09LV at `K` is an isomorphism.** It is
evaluation `Hom(K, K) ⊗_E K → K`. -/
public theorem isIso_tensorWithComplexDG_adjunction_counit_app
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    IsIso ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.counit.app
      (liftComplex.{u, v, w, t, s} X K : (CompDG.{u, v, w, t, s, o} X R).Comp)) := by
  let : Category (CompDG.{u, v, w, t, s, o} X R).Obj :=
    (CompDG.{u, v, w, t, s, o} X R).instCategoryComp
  let D := tensorWithComplexDG.{u, v, w, t, s, o} X R K
  let M := (Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)
  let c : (CompDG.{u, v, w, t, s, o} X R).Cocycle (tensorSheafified.{u, v, w, t, s, o} X R K M)
      (liftComplex.{u, v, w, t, s} X K) :=
    D.adjunction.counit.app (liftComplex.{u, v, w, t, s} X K : (CompDG.{u, v, w, t, s, o} X R).Comp)
  let : Category (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj :=
    (dgCategory _).instCategoryComp
  have hc : tensorHomEquiv.{u, v, w, t, s, o} X R K M (liftComplex.{u, v, w, t, s} X K) c =
      (𝟙 M : M ⟶ M) :=
    Equiv.apply_symm_apply _ _
  let e := regularSheafIsoOfSpec.{u, v, w, t, s, o} X R K D
  have hreg : tensorHomEquiv.{u, v, w, t, s, o} X R K M (liftComplex.{u, v, w, t, s} X K)
      (CochainComplex.HomComplex.Cocycle.ofHom e.hom) = (𝟙 M : M ⟶ M) := by
    apply representedCocycle_ext.{u, v, w, t, s, o} X R K M
    intro p x
    apply Cochain.ext
    intro q d h
    ext U y
    change evaluationEvalMap.{u, v, w, t, s, o} X R K (liftComplex.{u, v, w, t, s} X K) d p q
        (by omega) U
      ((cocycleHom (tensorHomEquiv.{u, v, w, t, s, o} X R K M (liftComplex.{u, v, w, t, s} X K)
        (CochainComplex.HomComplex.Cocycle.ofHom e.hom))).gradedMap p x) y =
      evaluationEvalMap.{u, v, w, t, s, o} X R K (liftComplex.{u, v, w, t, s} X K) d p q
          (by omega) U
        ((cocycleHom (𝟙 M : M ⟶ M)).gradedMap p x) y
    refine (tensorHomEquiv_pure.{u, v, w, t, s, o} X R K M (liftComplex.{u, v, w, t, s} X K)
      (CochainComplex.HomComplex.Cocycle.ofHom e.hom) p q d (by omega) U x y).trans ?_
    have h1 := congrArg (fun φ => ((φ.f d).app U).hom
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x y))
      (regularSheafIsoOfSpec_hom_spec.{u, v, w, t, s, o} X R K D)
    have h2 := regularSectionwiseEval_pure.{u, v, w, t, s, o} X R K D U d p q (by omega) x y
    have h3 : cast (congrArg (fun k : ℤ => (((D.sectionwise M).X k).obj U : Type _))
        (by omega : p + q = d)) (D.sectionwisePure M p q U x y) =
        tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x y :=
      tensorDegreePure_cast.{u, v, w, t, s, o} X R K M U (p + q) d p q (by omega) rfl (by omega) x y
    exact h1.trans ((congrArg (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d) h3).symm.trans
      h2)
  have hce : (tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.counit.app
      (liftComplex.{u, v, w, t, s} X K : (CompDG.{u, v, w, t, s, o} X R).Comp) =
        (tensorWithComplexDGRegularOfSpec.{u, v, w, t, s, o} X R K).hom :=
    (tensorHomEquiv.{u, v, w, t, s, o} X R K M (liftComplex.{u, v, w, t, s} X K)).injective
      (hc.trans hreg.symm)
  rw [hce]
  exact Iso.isIso_hom _

end AlgebraicGeometry.RingedSite

module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.FlatPullbackTensor
public import StacksFrontier.Topology.Sheaves.Modules.StalkTotalComplex
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Support of `𝒢 ⊗ f^*K`

Let `f : X ⟶ Y` be a morphism of ringed spaces and `𝒢^•` a bounded complex of `𝒪_X`-modules flat
over `Y`. If every term `𝒢^q` has vanishing stalks outside a subset `Z ⊆ X`, then for every object
`N` of `D(𝒪_Y)` the cohomology sheaves of `Φ N = Tot(f^*N ⊗ 𝒢^•)`
(`Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor`) are supported on `Z`.

Indeed `Φ N` is computed on any complex `K` representing `N` by the total complex of
`f^*K^p ⊗_{𝒪_X} 𝒢^q`; at a point `x ∉ Z` the stalk of each summand is
`(f^*K^p)_x ⊗ 𝒢^q_x = 0`, the stalk functor commutes with the coproducts forming the total complex,
and it is exact, so it kills the cohomology sheaves at `x`.

This is the support input for replacing `X` by an open neighbourhood of the support of `𝒢^•` in
[Stacks, Tag 08IF], and, after a base change, in [Stacks, Tag 0DJS]: its conclusion is the
hypothesis of `Stacks.Cohomology.RelativeExt.bijective_derivedPullback_map_of_supportedOn`.

## Main results

* `Stacks.Cohomology.RelativeExt.isZero_stalk_sheafTensor_of_isZero_stalk_right`
* `Stacks.Cohomology.RelativeExt.isZero_stalk_pullbackTensorComplexFunctor_obj_X`
* `Stacks.Cohomology.RelativeExt.isZero_stalk_homology_of_isZero_stalk_X`
* `Stacks.Cohomology.RelativeExt.cohomologySupportedOn_pullbackTensorDerivedFunctor_obj`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The stalk of `M ⊗_{𝒪_X} N` vanishes at a point where the stalk of `N` vanishes. -/
theorem isZero_stalk_sheafTensor_of_isZero_stalk_right (x : X.carrier)
    (M N : SheafOfModules.{u} (structureSheafRing X))
    (hN : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).obj N)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).obj N)) := by
  refine IsZero.of_iso ?_ (Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso X x M N)
  exact Functor.map_isZero _ hN

variable (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- **The terms of `Tot(f^*K ⊗ 𝒢^•)` have vanishing stalks where all `𝒢^q` do.** -/
theorem isZero_stalk_pullbackTensorComplexFunctor_obj_X (x : X.carrier)
    (hG : ∀ q : ℤ,
      IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).obj
        (G.X q)))
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (n : ℤ) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).obj
      (((pullbackTensorComplexFunctor f G).obj K).X n)) := by
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesAntidiagonalCoproducts
    (structureSheafRing X) x n
  have hc := isColimitOfPreserves
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x)
    (GradedObject.isColimitCofanMapObj
      (((((pullbackTensorBifunctor f).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj G).toGradedObject)
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
  rw [IsZero.iff_id_eq_zero]
  refine hc.hom_ext fun ⟨⟨p, q⟩, hpq⟩ ↦ ?_
  exact (isZero_stalk_sheafTensor_of_isZero_stalk_right x _ _ (hG q)).eq_of_src _ _

/-- A complex whose terms all have vanishing stalk at `x` has cohomology sheaves with vanishing
stalk at `x`: the stalk functor is exact, so it commutes with cohomology. -/
theorem isZero_stalk_homology_of_isZero_stalk_X {Z : RingedSpace.{u, u}} (x : Z.carrier)
    (T : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ)
    (hT : ∀ n : ℤ,
      IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) x).obj
        (T.X n))) (i : ℤ) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) x).obj
      (T.homology i)) := by
  let F := AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) x
  refine IsZero.of_iso ?_ ((T.sc i).mapHomologyIso F).symm
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ (hT i)

/-- **The cohomology sheaves of `Φ N = Tot(f^*N ⊗ 𝒢^•)` are supported where `𝒢^•` is.** If every
term `𝒢^q` has vanishing stalks outside `Z ⊆ X`, then every cohomology sheaf of
`Φ N` (`Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor`) has vanishing stalks
outside `Z`, for every `N` in `D(𝒪_Y)`. Stated at the standard model, the model of `Φ`. -/
theorem cohomologySupportedOn_pullbackTensorDerivedFunctor_obj (hG : IsBoundedFlatOver f G)
    (Z : Set X.carrier)
    (hGZ : ∀ (q : ℤ) (x : X.carrier), x ∉ Z →
      IsZero (TopCat.Presheaf.stalk (X := X.carrier) (G.X q).val.presheaf x)) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
    ∀ N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn (structureSheafRing X) Z
        ((pullbackTensorDerivedFunctor hG).obj N) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
  intro N i x hx
  rw [← AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff]
  let K := DerivedCategory.Q.objPreimage N
  let e : DerivedCategory.Q.obj K ≅ N := DerivedCategory.Q.objObjPreimageIso N
  let eH : (DerivedCategory.homologyFunctor _ i).obj ((pullbackTensorDerivedFunctor hG).obj N) ≅
      ((pullbackTensorComplexFunctor f G).obj K).homology i :=
    (DerivedCategory.homologyFunctor _ i).mapIso
        ((pullbackTensorDerivedFunctor hG).mapIso e.symm ≪≫
          (pullbackTensorDerivedFunctorFactors hG).app K) ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _
  refine IsZero.of_iso ?_
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).mapIso eH)
  refine isZero_stalk_homology_of_isZero_stalk_X x _ (fun n ↦ ?_) i
  refine isZero_stalk_pullbackTensorComplexFunctor_obj_X f G x (fun q ↦ ?_) K n
  exact (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ x _).2 (hGZ q x hx)

/-- **The stalk of `f^*𝒢` at `x` vanishes when the stalk of `𝒢` at `f(x)` does**: it is
`𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} 𝒢_{f(x)}` ([Stacks, Tag 0098]). -/
theorem isZero_stalk_modulePullback (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X.carrier)
    (hG : IsZero (TopCat.Presheaf.stalk (X := Y.carrier) G.val.presheaf (f.hom.base x))) :
    IsZero (TopCat.Presheaf.stalk (X := X.carrier) ((modulePullback f).obj G).val.presheaf x) := by
  obtain ⟨e, -⟩ := exists_modulePullbackStalkLinearEquiv f G x
  have : Subsingleton ↑(TopCat.Presheaf.stalk G.val.presheaf (f.hom.base x)) :=
    AddCommGrpCat.subsingleton_of_isZero hG
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact e.toEquiv.subsingleton

end Stacks.Cohomology.RelativeExt

end

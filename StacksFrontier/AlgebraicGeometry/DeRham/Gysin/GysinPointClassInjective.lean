module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.SingleShiftTransfer
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyMapInjective
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeFaithful
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualityNonvanishing

/-!
# Injectivity of the Gysin map in degree zero, through duality

Let `X` be a proper scheme over a field `k`, `T ⊆ X` closed, `d ≥ 0`, and `ℱ` an `𝒪_X`-module
with `ℋ^j_T(ℱ) = 0` for `j < d`. Let `γ : 𝒜 ⟶ i_*ℋ^d_T(ℱ)` be a sheaf-level Gysin map out of a
quasi-coherent `𝒜` supported on `T` whose global sections are one-dimensional over `k`, and
suppose the relative dualizing complex is `ω_X^• ≅ ℱ[d]`. If `γ ≠ 0`, the Gysin map of
[Stacks, Tag 0G8A]

`γ^0 : H^0(X, 𝒜) ⟶ H^d(X, ℱ)`

is injective. This is the argument of [Stacks, Tag 0G8E] with its geometric inputs isolated.

## Implementation notes

`γ^0` is induced by the morphism `g = γ[-d] ≫ edge : 𝒜[-d] ⟶ ℱ` of `D(𝒪_X)`, and by
`Stacks.DeRham.CohomologicalGysin.injective_cohomologyMapOfSingleHom` it is injective as soon as
`v[-d] ≫ g ≠ 0` for every nonzero `v : 𝒪_X ⟶ 𝒜`. The morphism `g` is nonzero by
`Stacks.DeRham.CohomologicalGysin.eq_zero_of_singleFunctor_map_comp_supportedGysinEdge_eq_zero`.
The cohomological Gysin map is built in the standard model of `D(𝒪_X)`, the duality of
[Stacks, Tag 0FVV] in the locally small one; the two meet in `Ext^d(𝒜, ℱ)`, which does not depend
on the model (`Stacks.DerivedCategoryExt.toExt`). In the locally small model `g` gives a nonzero
`α : 𝒜[0] ⟶ ω_X^•`, and `v ≫ α ≠ 0` is `Stacks.Duality.singleFunctor_map_comp_ne_zero`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Cohomology.SupportedComplexes

namespace Stacks.DeRham.CohomologicalGysin

universe u

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] moduleSheavesHasDerivedCategory

/-- **Injectivity of the Gysin map in degree zero, through duality.** -/
theorem injective_gysinCohomologyMap_zero_of_duality {k : Type u} [Field k] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsProper π] (T : Set X) (hT : IsClosed T) (d : ℕ)
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [(show X.Modules from A).IsQuasicoherent]
    (hvan : ∀ j : ℤ, j < (d : ℤ) → IsZero (localCohomologySheafOfComplex X.toRingedSpace T hT j
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (0 : ℤ)).obj F)))
    (γ : A ⟶ (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).obj
      (localCohomologySheafOfComplex X.toRingedSpace T hT (d : ℤ)
        ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (0 : ℤ)).obj F)))
    (hA : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (d : ℤ)).obj A))
    (hγ : γ ≠ 0)
    (hdim : Module.finrank k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appLE ⊤ ⊤ (by simp)).hom).obj
        ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj A)) = 1)
    (ψ : (Stacks.Duality.relativeDualizingComplex π
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs π)
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))).obj ≅
      (DerivedCategory.singleFunctor X.Modules (-(d : ℤ))).obj F) :
    Function.Injective (gysinCohomologyMap T hT d A F hvan γ 0) := by
  refine injective_cohomologyMapOfSingleHom X.toRingedSpace A F d _ fun v hv => ?_
  by_contra hv0
  let : HasExt.{u + 1} (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    HasExt.standard _
  let : Abelian X.Modules := inferInstance
  let : HasExt.{u + 1} X.Modules := HasExt.standard _
  -- the standard side: the Gysin morphism `g` and its class in `Ext^d(𝒜, ℱ)`
  let g := (DerivedCategory.singleFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (d : ℤ)).map γ ≫
    supportedGysinEdge T hT (d : ℤ) ((DerivedCategory.singleFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (0 : ℤ)).obj F) hvan
  have hg : g ≠ 0 := fun h =>
    hγ (eq_zero_of_singleFunctor_map_comp_supportedGysinEdge_eq_zero T hT (d : ℤ) A F hA hvan γ h)
  let E := Stacks.DerivedCategoryExt.toExt g
  have hE : E ≠ 0 := hg ∘ (Stacks.DerivedCategoryExt.toExt_eq_zero_iff g).1
  have hcomp : (Abelian.Ext.mk₀ v).comp E (zero_add d) = 0 := by
    rw [← Stacks.DerivedCategoryExt.toExt_singleFunctor_map_comp]
    exact (Stacks.DerivedCategoryExt.toExt_eq_zero_iff _).2 hv
  -- the locally small side
  let ω := (Stacks.Duality.relativeDualizingComplex π
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs π)
    (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))).obj
  let E' : Abelian.Ext.{u + 1} (C := X.Modules) A F d := E
  let α : (DerivedCategory.singleFunctor X.Modules 0).obj A ⟶ ω⟦(0 : ℤ)⟧ :=
    E'.hom ≫ ((DerivedCategory.singleFunctors X.Modules).shiftIso (d : ℤ) (-(d : ℤ)) 0
      (by simp)).hom.app F ≫ ψ.inv ≫ (shiftFunctorZero (DerivedCategory X.Modules) ℤ).inv.app ω
  have hα : α ≠ 0 := fun h => hE <|
    (Stacks.DerivedCategoryExt.hom_eq_zero_iff (C := X.Modules) E').1 <| by
      simpa using (show E'.hom ≫ (((DerivedCategory.singleFunctors X.Modules).shiftIso (d : ℤ)
        (-(d : ℤ)) 0 (by simp)).app F ≪≫ ψ.symm ≪≫
        ((shiftFunctorZero (DerivedCategory X.Modules) ℤ).app ω).symm).hom = 0 from h)
  have hs : (A.unitHomEquiv v).val (op ⊤) ≠ 0 := fun h0 => hv0 <| A.unitHomEquiv.injective <|
    (bijective_sections_eval_top X.toRingedSpace A.val).1 (by
      show (A.unitHomEquiv v).val (op ⊤) = (A.unitHomEquiv 0).val (op ⊤)
      rw [h0, _root_.SheafOfModules.unitHomEquiv_apply_coe]
      rfl)
  apply Stacks.Duality.singleFunctor_map_comp_ne_zero π (show X.Modules from A) hdim v hs α hα
  have h1 : (DerivedCategory.singleFunctor X.Modules 0).map v ≫ E'.hom = 0 :=
    (Stacks.DerivedCategoryExt.mk₀_comp_eq_zero_iff (C := X.Modules) v E').1 hcomp
  simp only [α, ← Category.assoc]
  exact (congrArg (fun t => ((t ≫ _) ≫ _) ≫ _) h1).trans (by simp only [zero_comp]; rfl)

end Stacks.DeRham.CohomologicalGysin

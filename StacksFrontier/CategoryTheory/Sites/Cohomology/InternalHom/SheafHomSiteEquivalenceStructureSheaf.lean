module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceNaturality

/-!
# The transport of `R𝓗om(𝒪, -) ≅ id` along an equivalence of ringed sites

Let `e : D ≌ C`, `φ`, `ψ` be an equivalence of ringed sites `(D, 𝒪_D) ≃ (C, 𝒪_C)`, so that the
pushforward `φ_*` of sheaves of modules is an equivalence. The structure map `φ` gives the
canonical morphism `𝒪_D ⟶ φ_* 𝒪_C` sending the unit section to the unit section. This file
proves that the transport `φ_* R𝓗om(𝒪_C, L) ≅ R𝓗om(φ_* 𝒪_C, φ_* L)` of
`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso`, followed by that morphism in the first
variable and by the identification `R𝓗om(𝒪_D, φ_* L) ≅ φ_* L` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, is `φ_*` of the identification
`R𝓗om(𝒪_C, L) ≅ L`.

It is proved at the chain level, as
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_restrict` is for restriction to a slice
site: at a K-injective representative both identifications are evaluation at the unit section, and
the transport does not change the value of a section
(`AlgebraicGeometry.RingedSite.applyHomSectionOver_siteEquivSheafHomComplexIso`).

## Main definitions

* `AlgebraicGeometry.RingedSite.siteEquivUnitHom`: `𝒪_D ⟶ φ_* 𝒪_C`, the unit section going to
  the unit section.
* `AlgebraicGeometry.RingedSite.siteEquivStructureSheafComplexHom`: the same on the structure
  sheaf complexes.
* `AlgebraicGeometry.RingedSite.siteEquivDerivedStructureSheafHom`: the same in `D(𝒪_D)`.

## Main results

* `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso_comp_structureSheafHomEvaluation`:
  the chain-level statement.
* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIso_structureSheaf`: the derived
  statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-! ### The unit -/

section Chain

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  CochainComplex.HomComplex
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget


/-- The unit section of `𝒪_C`, read as a global section of `φ_* 𝒪_C`. -/
def siteEquivUnitSection :
    ((SheafOfModules.pushforward.{u} φ).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).sections :=
  ⟨fun W => (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
      (op (eqv.functor.obj W.unop))),
    fun f => map_one ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map
      (eqv.functor.map f.unop).op).hom⟩

/-- **The canonical morphism `𝒪_D ⟶ φ_* 𝒪_C`** of an equivalence of ringed sites: the morphism
out of the unit module attached to the unit section of `𝒪_C`. -/
def siteEquivUnitHom :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (SheafOfModules.pushforward.{u} φ).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (SheafOfModules.unitHomEquiv _).symm (siteEquivUnitSection eqv φ)

omit [eqv.inverse.IsContinuous X.J Y.J] in
/-- The canonical morphism `𝒪_D ⟶ φ_* 𝒪_C` sends the unit section to the unit section. -/
theorem siteEquivUnitHom_app_one (W : Y.C) :
    (siteEquivUnitHom eqv φ).val.app (op W)
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op W)) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (eqv.functor.obj W))) := by
  simp only [siteEquivUnitHom, SheafOfModules.unitHomEquiv, PresheafOfModules.unitHomEquiv,
    siteEquivUnitSection]
  exact one_smul _ _

/-- The pushforward along `φ` preserves zero morphisms: it is additive. -/
instance pushforward_preservesZeroMorphisms :
    (SheafOfModules.pushforward.{u} φ).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- **The canonical morphism `𝒪_D[0] ⟶ φ_*(𝒪_C[0])`** of structure sheaf complexes. -/
def siteEquivStructureSheafComplexHom :
    structureSheafComplex Y ⟶ (pushComplex eqv φ).obj (structureSheafComplex X) :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (siteEquivUnitHom eqv φ) ≫
    ((HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.pushforward.{u} φ)
      (ComplexShape.up ℤ) 0).app _).inv

omit [eqv.inverse.IsContinuous X.J Y.J] in
/-- In degree zero the canonical morphism of structure sheaf complexes sends the unit section to
the unit section. -/
theorem siteEquivStructureSheafComplexHom_f_zero_one (W : Y.C) :
    ((siteEquivStructureSheafComplexHom eqv φ).f 0).val.app (op W) (structureSheafOne Y W) =
      structureSheafOne X (eqv.functor.obj W) :=
  siteEquivUnitHom_app_one eqv φ W

/-- **The chain-level transport is compatible with evaluation at the unit section.**
Transporting `SheafHom(𝒪_C, I)` along the equivalence, reading its source through
`𝒪_D[0] ⟶ φ_*(𝒪_C[0])` and evaluating at the unit section of `𝒪_D` is the transport of evaluation
at the unit section of `𝒪_C`. -/
theorem siteEquivSheafHomComplexIso_comp_structureSheafHomEvaluation
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ (structureSheafComplex X) I).hom ≫
        homMap Y (siteEquivStructureSheafComplexHom eqv φ) (𝟙 ((pushComplex eqv φ).obj I)) ≫
        structureSheafHomEvaluation Y ((pushComplex eqv φ).obj I) =
      (pushComplex eqv φ).map (structureSheafHomEvaluation X I) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_))
  change applyHomSection Y (sheafHomComplex Y (structureSheafComplex Y) ((pushComplex eqv φ).obj I))
      W.unop n 0 n (zero_add n)
      (((homMap Y (siteEquivStructureSheafComplexHom eqv φ)
          (𝟙 ((pushComplex eqv φ).obj I))).f n).val.app
        W (((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ (structureSheafComplex X) I).hom.f n).val.app
          W s))
      (structureSheafOne Y W.unop) =
    applyHomSection X (sheafHomComplex X (structureSheafComplex X) I) (eqv.functor.obj W.unop)
      n 0 n (zero_add n) s (structureSheafOne X (eqv.functor.obj W.unop))
  rw [applyHomSection_homMap, siteEquivStructureSheafComplexHom_f_zero_one]
  refine (applyHomSectionOver_siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ (structureSheafComplex X) I
    W.unop W.unop (𝟙 W.unop) n 0 n (zero_add n) s _).trans ?_
  simp only [CategoryTheory.Functor.map_id]

end Chain

end AlgebraicGeometry.RingedSite

end

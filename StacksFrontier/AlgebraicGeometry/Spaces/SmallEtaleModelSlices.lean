module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceSlicesHeterogeneous

/-!
# Slices of the small étale site of an algebraic space against its equi-universe model

Let `X` be an algebraic space, `SE` its small étale ringed site (an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`) and `Y` the equi-universe model of `SE`
(`AlgebraicGeometry.Space.smallEtaleModelRingedSite`, an `AlgebraicGeometry.RingedSite.{u, u, u}`),
with the equivalence `e : Mod(𝒪_X) ≌ Mod(𝒪_Y)` of
`AlgebraicGeometry.Space.modulesEquivModelModules`. For an étale chart `V` of `X`, with model
object `V' := e⁻¹(V)`, this file gives the equivalence of the categories of modules on the slices
`SE/V` and `Y/V'` (`AlgebraicGeometry.Space.modelObjSliceModulesEquiv`), under which restricting to
`V'` after transporting along `e` is restricting to `V`
(`AlgebraicGeometry.Space.modelSliceSquare`, an equality on the nose), and which carries the unit
to the unit (`AlgebraicGeometry.Space.modelSliceUnitIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The reversed model equivalence, with its source and target spelled as the categories of the
two ringed sites. -/
abbrev modelEqv :
    (smallEtaleRingedSite B S hS F hF).C ≌ (smallEtaleModelRingedSite B S hS F hF).C :=
  (smallEtaleModelEquivalence B S hS F).symm

/-- The model object of an étale chart. -/
abbrev modelObj (V : (smallEtaleRingedSite B S hS F hF).C) :
    (smallEtaleModelRingedSite B S hS F hF).C :=
  (modelEqv B S hS F hF).functor.obj V

/-- The functor of the reversed model equivalence is continuous for the étale topologies. -/
instance modelEqv_functor_isContinuous :
    (modelEqv B S hS F hF).functor.IsContinuous
      (smallEtaleRingedSite B S hS F hF).J (smallEtaleModelRingedSite B S hS F hF).J :=
  smallEtaleModelRingedSite_inverse_isContinuous B S hS F hF

/-- The inverse of the reversed model equivalence is continuous for the étale topologies. -/
instance modelEqv_inverse_isContinuous :
    (modelEqv B S hS F hF).inverse.IsContinuous
      (smallEtaleModelRingedSite B S hS F hF).J (smallEtaleRingedSite B S hS F hF).J :=
  smallEtaleModelRingedSite_functor_isContinuous B S hS F hF

/-- The structure map of the reversed model equivalence: the counit identifies `𝒪_X` with the
direct image of the model ring. -/
abbrev modelSharp :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O ⟶
      ((modelEqv B S hS F hF).functor.sheafPushforwardContinuous RingCat.{u}
        (smallEtaleRingedSite B S hS F hF).J (smallEtaleModelRingedSite B S hS F hF).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) :=
  Stacks.SheafOfModules.reindexBackSharp (smallEtaleModelEquivalence B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)

/-- The identity structure map of the model ring, as a map into the direct image along the model
equivalence. -/
abbrev modelSharpInv :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O ⟶
      ((modelEqv B S hS F hF).inverse.sheafPushforwardContinuous RingCat.{u}
        (smallEtaleModelRingedSite B S hS F hF).J (smallEtaleRingedSite B S hS F hF).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  𝟙 _

/-- The structure map `modelSharpInv` is an isomorphism. -/
instance : IsIso (modelSharpInv B S hS F hF) := inferInstanceAs (IsIso (𝟙 _))

private theorem map_counit_comp_map_counitInv {C C' : Type*} [Category C] [Category C']
    (e : C' ≌ C) (R : Cᵒᵖ ⥤ RingCat.{u}) (V : C) :
    R.map (e.counit.app V).op ≫ R.map (e.counitInv.app V).op = 𝟙 _ := by
  rw [← R.map_comp, ← op_comp]
  simp

private theorem map_functor_map_unitInv {C C' : Type*} [Category C] [Category C']
    (e : C' ≌ C) (R : Cᵒᵖ ⥤ RingCat.{u}) (Z : C') :
    R.map (e.functor.map (e.unitInv.app Z)).op = R.map (e.counit.app (e.functor.obj Z)).op := by
  rw [Equivalence.counit_app_functor]

/-- The ring map of the model induced by the counit of `modelEqv` is the composite of
`modelSharpInv` with `modelSharp` whiskered by the inverse functor. -/
theorem modelSharp_compat₁ :
    Functor.whiskerRight (NatTrans.op (modelEqv B S hS F hF).counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O).obj =
      (modelSharpInv B S hS F hF).hom ≫
        (modelEqv B S hS F hF).inverse.op.whiskerLeft (modelSharp B S hS F hF).hom := by
  ext Z : 2
  change (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.map
      ((smallEtaleModelEquivalence B S hS F).functor.map
        ((smallEtaleModelEquivalence B S hS F).unitInv.app Z.unop)).op =
    𝟙 _ ≫ (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.map
      ((smallEtaleModelEquivalence B S hS F).counit.app
        ((smallEtaleModelEquivalence B S hS F).functor.obj Z.unop)).op
  rw [Category.id_comp]
  exact map_functor_map_unitInv (smallEtaleModelEquivalence B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj Z.unop

/-- The composite of `modelSharp`, `modelSharpInv` whiskered by the functor, and the ring map
induced by the unit of `modelEqv` is the identity of `𝒪_X`. -/
theorem modelSharp_compat₂ :
    (modelSharp B S hS F hF).hom ≫
        (modelEqv B S hS F hF).functor.op.whiskerLeft (modelSharpInv B S hS F hF).hom ≫
        Functor.whiskerRight (NatTrans.op (modelEqv B S hS F hF).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj := by
  ext V : 2
  change (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.map
      ((smallEtaleModelEquivalence B S hS F).counit.app V.unop).op ≫ 𝟙 _ ≫
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.map
      ((smallEtaleModelEquivalence B S hS F).counitInv.app V.unop).op = 𝟙 _
  rw [Category.id_comp]
  exact map_counit_comp_map_counitInv (smallEtaleModelEquivalence B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj V.unop

/-- **The modules on the slice of the model at `e⁻¹(V)` are the modules on the slice of the small
étale site at `V`.** -/
def modelObjSliceModulesEquiv (V : (smallEtaleRingedSite B S hS F hF).C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS F hF).O).over
          (modelObj B S hS F hF V)) ≌
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).over V) :=
  Stacks.SheafOfModules.InternalHom.AnyUniverse.siteEquivModulesOver
    (X := smallEtaleModelRingedSite B S hS F hF) (Y := smallEtaleRingedSite B S hS F hF)
    (modelEqv B S hS F hF) (modelSharp B S hS F hF)
    (modelSharpInv B S hS F hF) (modelSharp_compat₁ B S hS F hF) (modelSharp_compat₂ B S hS F hF) V

/-- **Restricting to `e⁻¹(V)` after transporting to the model is restricting to `V` and then
transporting along the slice equivalence**, on the nose. -/
def modelSliceSquare (V : (smallEtaleRingedSite B S hS F hF).C) :
    SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) V ⋙
        (modelObjSliceModulesEquiv B S hS F hF V).inverse ≅
      (modulesEquivModelModules B S hS F hF).functor ⋙
        SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)
          (modelObj B S hS F hF V) :=
  Iso.refl _

/-- The slice equivalence carries the unit to the unit. -/
def modelSliceUnitIso (V : (smallEtaleRingedSite B S hS F hF).C) :
    (modelObjSliceModulesEquiv B S hS F hF V).inverse.obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O).over V)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS F hF).O).over
          (modelObj B S hS F hF V)) :=
  RingedSite.pushforwardUnitIsoHet (X := smallEtaleModelRingedSite B S hS F hF)
    (Y := smallEtaleRingedSite B S hS F hF)
    (modelEqv B S hS F hF) (modelSharp B S hS F hF)
    (modelSharpInv B S hS F hF) (modelSharp_compat₁ B S hS F hF) (modelSharp_compat₂ B S hS F hF) V

end AlgebraicGeometry.Space

end

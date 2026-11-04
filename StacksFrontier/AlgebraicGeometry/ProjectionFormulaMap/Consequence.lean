module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The projection formula at the structure sheaf, and the surjectivity it transports

Let `f : X ⟶ Y` be a morphism of ringed spaces and `H` a sheaf of `𝒪_Y`-modules. The canonical
map `𝒪_Y ⊗ H ⟶ f_* 𝒪_X ⊗ H` followed by the projection formula morphism of [Stacks, Tag 0FZE] at
the structure sheaf is, up to isomorphisms on both ends, the unit `H ⟶ f_* f^* H`.

Consequently any functor out of `Mod(𝒪_Y)`, in particular global sections, that takes both the
first map and the projection formula morphism to epimorphisms takes the unit to an epimorphism.

## Main definitions

* `Stacks.ProjectionFormula.pullbackUnitToUnit`: the canonical `f^* 𝒪_Y ⟶ 𝒪_X`, the adjoint
  transpose of `SheafOfModules.unitToPushforwardObjUnit`, with
  `Stacks.ProjectionFormula.isIso_pullbackUnitToUnit` showing it is an isomorphism.
* `Stacks.ProjectionFormula.unitTensorIso`: the left unitor `𝒪_Z ⊗ M ≅ M` on a ringed space.
* `Stacks.ProjectionFormula.structureComparison`: the composite
  `f^*(𝒪_Y ⊗ H) ⟶ f^* 𝒪_Y ⊗ f^* H ⟶ 𝒪_X ⊗ f^* H`, an isomorphism.

## Main results

* `Stacks.ProjectionFormula.tensorUnitToPushforward_comp_projectionFormulaMap'`:
  `(𝒪_Y ⟶ f_* 𝒪_X) ⊗ 𝟙_H` followed by the projection formula morphism at `𝒪_X` equals the unit
  at `𝒪_Y ⊗ H` followed by `f_*` of `structureComparison`.
* `Stacks.ProjectionFormula.epi_map_unit_of_epi`: for any functor `F` out of `Mod(𝒪_Y)`, if `F`
  takes the two maps above to epimorphisms then it takes the unit `H ⟶ f_* f^* H` to one.
* `Stacks.ProjectionFormula.isIso_unit_app_of_isIso`: the unit `H ⟶ f_* f^* H` is an
  isomorphism when `𝒪_Y ⟶ f_* 𝒪_X` and the projection formula morphism at `𝒪_X` are.

## Implementation notes

The identity follows from the naturality of the projection formula morphism, the unit identity
`Stacks.ProjectionFormula.projectionFormulaMap'_unit`, and the fact that
`SheafOfModules.unitToPushforwardObjUnit` is the adjoint transpose of `pullbackUnitToUnit`.

`structureComparison` is an isomorphism because the comparison morphism of [Stacks, Tag 01CD] is
(`Stacks.RingedSpace.comparisonNatTrans_app_isIso`) and `pullbackUnitToUnit` is, the inverse-image
functor on opens being final (`CategoryTheory.final_of_representablyFlat`).

`epi_map_unit_of_epi` is stated for an arbitrary functor `F` rather than for global sections. Its
hypothesis that `F` takes the projection formula morphism at `𝒪_X` to an epimorphism holds when
that morphism is an isomorphism, as [Stacks, Tag 0FZE] asserts for affine `f` and quasi-coherent
arguments.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MonoidalCategory
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

/-! ### The structure sheaf pulls back to the structure sheaf -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The canonical morphism `𝒪_Y ⟶ f_* 𝒪_X` of sheaves of modules, namely
`SheafOfModules.unitToPushforwardObjUnit` stated over the `structureRingSheaf` form of the
structure sheaves. -/
noncomputable def unitHom :
    SheafOfModules.unit (structureRingSheaf Y) ⟶
      (pushforwardFunctor f).obj (SheafOfModules.unit (structureRingSheaf X)) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)

/-- `Stacks.ProjectionFormula.unitHom f` is `SheafOfModules.unitToPushforwardObjUnit`. -/
lemma unitHom_eq :
    unitHom f = SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) := rfl

/-- The canonical morphism `f^* 𝒪_Y ⟶ 𝒪_X`, the adjoint transpose of
`Stacks.ProjectionFormula.unitHom`, namely `SheafOfModules.pullbackObjUnitToUnit` stated over
the ringed-space pullback and pushforward. -/
noncomputable def pullbackUnitToUnit :
    (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) ⟶
      SheafOfModules.unit (structureRingSheaf X) :=
  ((pullbackAdjunction f).homEquiv _ _).symm (unitHom f)

/-- The adjoint transpose of `Stacks.ProjectionFormula.pullbackUnitToUnit f` is
`Stacks.ProjectionFormula.unitHom f`. -/
@[simp]
lemma homEquiv_pullbackUnitToUnit :
    (pullbackAdjunction f).homEquiv _ _ (pullbackUnitToUnit f) = unitHom f :=
  Equiv.apply_symm_apply _ _

/-- `Stacks.ProjectionFormula.unitHom` factors through the unit of `f^* ⊣ f_*`. -/
lemma unitHom_factors :
    unitHom f =
      (pullbackAdjunction f).unit.app (SheafOfModules.unit (structureRingSheaf Y)) ≫
        (pushforwardFunctor f).map (pullbackUnitToUnit f) := by
  rw [← homEquiv_pullbackUnitToUnit f, Adjunction.homEquiv_unit]

/-- The canonical morphism `f^* 𝒪_Y ⟶ 𝒪_X` is an isomorphism. -/
instance isIso_pullbackUnitToUnit : IsIso (pullbackUnitToUnit f) := by
  have : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  have : (Opens.map f.hom.base).Final := CategoryTheory.final_of_representablyFlat _
  exact inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)))

/-- `SheafOfModules.unitToPushforwardObjUnit` is the unit of `f^* ⊣ f_*` at `𝒪_Y` followed by
`f_*` of `Stacks.ProjectionFormula.pullbackUnitToUnit f`. -/
lemma unitToPushforwardObjUnit_factors :
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) =
      (pullbackAdjunction f).unit.app (SheafOfModules.unit (structureRingSheaf Y)) ≫
        (pushforwardFunctor f).map (pullbackUnitToUnit f) :=
  unitHom_factors f

/-! ### The left unitor -/

/-- The left unitor `𝒪_Z ⊗ M ≅ M` for the tensor product of sheaves of modules on a ringed space:
the sheafified left unitor of presheaves of modules, followed by the counit of the sheafification
adjunction at the sheaf `M`. -/
noncomputable def unitTensorIso (Z : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureRingSheaf Z)) :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf, ((Z)).IsSheaf⟩))).obj
      (SheafOfModules.unit (structureRingSheaf Z), M) ≅ M := by
  have : MonoidalCategory (PresheafOfModules.{u} (structureRingSheaf Z).obj) := by
    change MonoidalCategory
      (PresheafOfModules.{u} (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  have : IsIso (PresheafOfModules.sheafificationAdjunction
      (R := structureRingSheaf Z) (𝟙 (structureRingSheaf Z).obj)).counit := by
    infer_instance
  change (PresheafOfModules.sheafification (R := structureRingSheaf Z)
      (𝟙 (structureRingSheaf Z).obj)).obj
      ((SheafOfModules.unit (structureRingSheaf Z)).val ⊗ M.val) ≅ M
  exact (PresheafOfModules.sheafification (R := structureRingSheaf Z)
      (𝟙 (structureRingSheaf Z).obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := structureRingSheaf Z) (𝟙 (structureRingSheaf Z).obj)).counit).app M

/-! ### The comparison at the structure sheaf -/

variable (H : SheafOfModules.{u} (structureRingSheaf Y))

/-- The comparison morphism at the structure sheaf in the first argument, composed with
`f^* 𝒪_Y ≅ 𝒪_X`:

`f^*(𝒪_Y ⊗ H) ⟶ f^* 𝒪_Y ⊗ f^* H ⟶ 𝒪_X ⊗ f^* H`. -/
noncomputable def structureComparison :
    (pullbackFunctor f).obj
        (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj
          (SheafOfModules.unit (structureRingSheaf Y), H)) ⟶
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).obj
        (SheafOfModules.unit (structureRingSheaf X), (pullbackFunctor f).obj H) :=
  (comparisonNatTrans f).app (SheafOfModules.unit (structureRingSheaf Y), H) ≫
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).map
      (pullbackUnitToUnit f ×ₘ 𝟙 ((pullbackFunctor f).obj H))

/-- `Stacks.ProjectionFormula.structureComparison f H` is an isomorphism. -/
instance isIso_structureComparison : IsIso (structureComparison f H) := by
  have hp : IsIso (pullbackUnitToUnit f ×ₘ 𝟙 ((pullbackFunctor f).obj H)) :=
    (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  exact IsIso.comp_isIso' inferInstance
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).mapIso
      (@asIso _ _ _ _ _ hp)).isIso_hom

/-! ### The identity -/

/-- Tensoring `𝒪_Y ⟶ f_* 𝒪_X` with `H` and then applying the projection formula morphism at the
structure sheaf is the unit of `f^* ⊣ f_*` at `𝒪_Y ⊗ H`, followed by `f_*` of
`structureComparison f H`. -/
theorem tensorUnitToPushforward_comp_projectionFormulaMap' :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).map
      (unitHom f ×ₘ 𝟙 H) ≫
        projectionFormulaMap' f (SheafOfModules.unit (structureRingSheaf X)) H =
      (pullbackAdjunction f).unit.app
          (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj
            (SheafOfModules.unit (structureRingSheaf Y), H)) ≫
        (pushforwardFunctor f).map (structureComparison f H) := by
  have h := adjunctionTensorMap_homEquiv (pullbackAdjunction f)
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)))
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
    (comparisonNatTrans f) (SheafOfModules.unit (structureRingSheaf Y)) H
    (SheafOfModules.unit (structureRingSheaf X)) (pullbackUnitToUnit f)
  rw [homEquiv_pullbackUnitToUnit f, Adjunction.homEquiv_unit] at h
  exact h

/-- A property of morphisms of `Mod(𝒪_Y)` that is stable under composition and isomorphisms holds
for the unit `H ⟶ f_* f^* H` as soon as it holds for `𝒪_Y ⟶ f_* 𝒪_X` tensored with `H` and for the
projection formula morphism at the structure sheaf. -/
private theorem unit_app_mem
    (P : MorphismProperty (SheafOfModules.{u} (structureRingSheaf Y)))
    [P.RespectsIso] [P.IsStableUnderComposition]
    (h₁ : P (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).map
      (unitHom f ×ₘ 𝟙 H)))
    (h₂ : P (projectionFormulaMap' f (SheafOfModules.unit (structureRingSheaf X)) H)) :
    P ((pullbackAdjunction f).unit.app H) := by
  have hn : (unitTensorIso Y H).hom ≫ (pullbackAdjunction f).unit.app H = _ :=
    (pullbackAdjunction f).unit.naturality (unitTensorIso Y H).hom
  refine (@MorphismProperty.cancel_left_of_respectsIso _ _ P _ _ _ _ (unitTensorIso Y H).hom _
    (unitTensorIso Y H).isIso_hom).1 (hn ▸ ?_)
  refine (@MorphismProperty.cancel_right_of_respectsIso _ _ P _ _ _ _ _ _
    ((pullbackFunctor f ⋙ pushforwardFunctor f).mapIso (unitTensorIso Y H)).isIso_hom).2 ?_
  refine (@MorphismProperty.cancel_right_of_respectsIso _ _ P _ _ _ _ _
    ((pushforwardFunctor f).map (structureComparison f H))
    ((pushforwardFunctor f).mapIso (asIso (structureComparison f H))).isIso_hom).1 ?_
  exact (tensorUnitToPushforward_comp_projectionFormulaMap' f H) ▸ P.comp_mem _ _ h₁ h₂

/-- For any functor `F` out of `Mod(𝒪_Y)`: if `F` takes the map `𝒪_Y ⊗ H ⟶ f_* 𝒪_X ⊗ H` and the
projection formula morphism at the structure sheaf to epimorphisms, then `F` takes the unit
`H ⟶ f_* f^* H` to an epimorphism. -/
theorem epi_map_unit_of_epi {D : Type*} [Category D]
    (F : SheafOfModules.{u} (structureRingSheaf Y) ⥤ D)
    (h₁ : Epi (F.map (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).map
      (unitHom f ×ₘ 𝟙 H))))
    (h₂ : Epi (F.map
      (projectionFormulaMap' f (SheafOfModules.unit (structureRingSheaf X)) H))) :
    Epi (F.map ((pullbackAdjunction f).unit.app H)) :=
  unit_app_mem f H ((MorphismProperty.epimorphisms D).inverseImage F) h₁ h₂

/-- The unit `H ⟶ f_* f^* H` is an isomorphism if `𝒪_Y ⟶ f_* 𝒪_X` and the projection formula
morphism at the structure sheaf are. -/
theorem isIso_unit_app_of_isIso (h₁ : IsIso (unitHom f))
    (h₂ : IsIso (projectionFormulaMap' f (SheafOfModules.unit (structureRingSheaf X)) H)) :
    IsIso ((pullbackAdjunction f).unit.app H) := by
  have hp : IsIso (unitHom f ×ₘ 𝟙 H) :=
    (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  exact unit_app_mem f H (MorphismProperty.isomorphisms _)
    (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩)).mapIso
        (@asIso _ _ _ _ _ hp)).isIso_hom) h₂

end Stacks.ProjectionFormula

end

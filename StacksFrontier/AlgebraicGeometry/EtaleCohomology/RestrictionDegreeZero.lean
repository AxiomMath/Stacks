module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DegreeZeroTerminal

/-!
# Restriction of étale cohomology in degree zero

For `i : Y ⟶ X` and an abelian sheaf `F` on the small étale site of `X`, restriction
`H⁰(X, F) → H⁰(Y, i⁻¹ F)` is, through `H⁰ ≅ Γ`, the unit `F ⟶ i_* i⁻¹ F` on sections over `X`,
followed by restriction to the chosen final object of the small étale site of `Y`.

## Main results

* `Stacks.EtaleCohomology.equiv₀_etaleCohomologyRestrictionMap_zero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

/-- **Restriction in degree zero is the unit on global sections**: for `x ∈ H⁰(X, F)`, the
global section of `i⁻¹ F` attached to the restriction of `x`, read over any final object `T` of
the small étale site of `Y`, is the image of the global section attached to `x` under the unit
`F ⟶ i_* i⁻¹ F`, restricted along `T ⟶ X ×_X Y`. -/
theorem equiv₀_etaleCohomologyRestrictionMap_zero {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {T : Y.Etale}
    (hT : IsTerminal T) (x : Sheaf.H.{w} F 0) :
    Sheaf.H.equiv₀ ((etaleAbelianInverseImage.{u, v} i).obj F) hT
        (etaleCohomologyRestrictionMap.{u, v, w} i F 0 x) =
      ((etaleAbelianInverseImage.{u, v} i).obj F).obj.map
        (((isTerminalEtaleMkId X).isTerminalObj (smallEtaleBaseChange i)).from T).op
        (((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 X))) (Sheaf.H.equiv₀ F (isTerminalEtaleMkId X) x)) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities
  let T₀ : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let hT₀ : IsTerminal T₀ := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT₀.isTerminalObj (smallEtaleBaseChange i)
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, v} i
  let Z := AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)
  let φ := Abelian.Ext.homEquiv₀ x
  have hres : etaleCohomologyRestrictionMap.{u, v, w} i F 0 x = Abelian.Ext.mk₀
      ((((constantSheafAdj _ _ hT₀).comp adj).leftAdjointUniq
        (constantSheafAdj _ _ hGT)).inv.app Z ≫ (etaleAbelianInverseImage.{u, v} i).map φ) := by
    rw [← Abelian.Ext.mk₀_homEquiv₀_apply x]
    simp only [etaleCohomologyRestrictionMap_apply, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.mk₀_comp_mk₀]
    rfl
  have h := Adjunction.homEquiv_leftAdjointUniq_inv_app_comp_map adj
    (constantSheafAdj _ _ hT₀) (constantSheafAdj _ _ hGT) Z φ
  have h₀ : Sheaf.H.equiv₀ ((etaleAbelianInverseImage.{u, v} i).obj F) hGT
      (etaleCohomologyRestrictionMap.{u, v, w} i F 0 x) =
      ((adj.unit.app F).hom.app (op T₀)) (Sheaf.H.equiv₀ F hT₀ x) := by
    rw [hres, Sheaf.H.equiv₀_mk₀]
    conv_rhs => rw [← Abelian.Ext.mk₀_homEquiv₀_apply x, Sheaf.H.equiv₀_mk₀]
    refine (congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) h).trans ?_
    rfl
  have h₁ : Sheaf.H.equiv₀ ((etaleAbelianInverseImage.{u, v} i).obj F) hT
      (etaleCohomologyRestrictionMap.{u, v, w} i F 0 x) =
      ((etaleAbelianInverseImage.{u, v} i).obj F).obj.map (hGT.from T).op
        (Sheaf.H.equiv₀ ((etaleAbelianInverseImage.{u, v} i).obj F) hGT
          (etaleCohomologyRestrictionMap.{u, v, w} i F 0 x)) :=
    Sheaf.H.equiv₀_eq_map_of_isTerminal.{max (u + 1) v, w} _ _ _ _
  have h₂ : Sheaf.H.equiv₀ F (isTerminalEtaleMkId X) x =
      F.obj.map (hT₀.from (Scheme.Etale.mk (𝟙 X))).op (Sheaf.H.equiv₀ F hT₀ x) :=
    Sheaf.H.equiv₀_eq_map_of_isTerminal.{max (u + 1) v, w} _ _ _ _
  have h₃ : hT₀.from (Scheme.Etale.mk (𝟙 X)) = 𝟙 _ := hT₀.hom_ext _ _
  rw [h₃, op_id, CategoryTheory.Functor.map_id] at h₂
  have h₄ : hGT.from T =
      ((isTerminalEtaleMkId X).isTerminalObj (smallEtaleBaseChange i)).from T := hGT.hom_ext _ _
  refine h₁.trans ?_
  rw [h₀, h₂, h₄]
  rfl

end Stacks.EtaleCohomology

end

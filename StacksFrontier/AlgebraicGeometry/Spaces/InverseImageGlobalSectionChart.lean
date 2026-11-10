module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafMapGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.RingSheafChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpChartPullback

/-!
# The inverse image of a global function, read on a chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `ψ : f⁻¹𝒪_Y ⟶ 𝒜` a morphism of sheaves of
commutative rings on the small étale site of `X`, and `σ` a global section of `𝒪_Y`. The global
section `ψ(f⁻¹σ)` of `𝒜` has, over an étale chart of `X` lying over `X ×_Y V` for an étale chart
`V` of `Y`, the value of the chart component of `ψ`
(`AlgebraicGeometry.Space.inverseImageHomChartRingHom`) at the value of `σ` over `V`. This is the
formula through which inverse images of global functions along a thickening are computed on the
charts of the thickened space.

## Main results

* `AlgebraicGeometry.Space.globalSectionMap_comp_forget_map_app`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for these limits on the small étale presheaf category is deep
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_InverseImageGlobalSectionChart
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the terminal object of the small étale topos is deep
/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_InverseImageGlobalSectionChart
    (Z : AlgebraicSpaces B S hS) : HasTerminal (smallEtaleRingedTopos B S hS Z).Topos :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1})
      ((SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type u))

/-- **The inverse image of a global function, on a chart.** For `ψ : f⁻¹𝒪_Y ⟶ 𝒜` and a global
section `σ` of `𝒪_Y`, the value of `ψ(f⁻¹σ)` over the chart `j` of `X` above `X ×_Y V` is the
chart component of `ψ` at the value of `σ` over `V`. -/
theorem globalSectionMap_comp_forget_map_app
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (ψ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A)
    (σ : ⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⟶
      (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS Y).O)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (p : (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)).obj.obj j.right)
    (q : (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)).obj.obj (op V)) :
    ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.globalSectionMap σ ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ψ).hom.app
          j.right p =
      inverseImageHomChartRingHom B S hS f A ψ V j (σ.hom.app (op V) q) := by
  let F := (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
  let adj := (smallEtaleRingedToposHom B S hS f).toToposHom.adj
  let ρ := F.globalSectionMap σ ≫
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ψ
  have hF : F.map σ ≫
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ψ =
      terminalComparison F ≫ ρ :=
    (IsIso.hom_inv_id_assoc (terminalComparison F) _).symm.trans
      (congrArg (terminalComparison F ≫ ·) (Category.assoc _ _ _).symm)
  have hadj : σ ≫ adj.homEquiv _ _
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ψ) =
      adj.homEquiv _ _ (terminalComparison F) ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map ρ :=
    (adj.homEquiv_naturality_left σ _).symm.trans
      ((congrArg (adj.homEquiv _ _) hF).trans (adj.homEquiv_naturality_right _ _))
  have e1 : inverseImageHomChartRingHom B S hS f A ψ V j (σ.hom.app (op V) q) =
      (chartProjection B S hS f V j).app _
        (((σ ≫ adj.homEquiv _ _ ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget CommRingCat.{u})).map ψ)) ≫
            (smallEtaleDirectImageRanIso B S hS f).hom.app _).hom.app (op V) q) := by
    refine (inverseImageHomChartRingHom_apply B S hS f A ψ V j _).trans ?_
    rw [inverseImageHomRanSet_eq]
    rfl
  have e2 : (σ ≫ adj.homEquiv _ _ ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget CommRingCat.{u})).map ψ)) ≫
            (smallEtaleDirectImageRanIso B S hS f).hom.app _ =
      (adj.homEquiv _ _ (terminalComparison F) ≫
        (smallEtaleDirectImageRanIso B S hS f).hom.app _) ≫
          (smallEtaleDirectImageRan B S hS f).map ρ := by
    rw [hadj]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      ((smallEtaleDirectImageRanIso B S hS f).hom.naturality ρ)).trans (Category.assoc _ _ _).symm)
  have hT : IsTerminal ((⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)).obj.obj j.right) :=
    IsTerminal.isTerminalObj ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj j.right) _
      terminalIsTerminal
  have : Subsingleton ((⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)).obj.obj j.right) :=
    ((Types.isTerminalEquivUnique _) hT).instSubsingleton
  refine Eq.symm (e1.trans ?_)
  rw [e2]
  exact (chartProjection_app_map B S hS f V ρ j _).trans
    (congrArg (fun z => ρ.hom.app j.right z) (Subsingleton.elim _ _))

end AlgebraicGeometry.Space

end

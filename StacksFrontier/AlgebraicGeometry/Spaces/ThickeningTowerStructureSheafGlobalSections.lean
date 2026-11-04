module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningTowerStructureSheafCohomology

/-!
# The global sections of `W ↦ lim Γ(Wₙ, 𝒪)`

Let `F ≅ yoneda.obj V` be a represented algebraic space and `V ⟶ X₀ ⟶ X₁ ⟶ ⋯` a tower of
thickenings. The sections of the sheaf `𝒪 : W ↦ lim Γ(Wₙ, 𝒪)` over an affine chart `W` are, by
construction, the inverse limit of the discrete rings `Γ(Wₙ, 𝒪)`. At the terminal chart `V` the
lift `Vₙ` is the stage `Xₙ` itself, so the global sections of `𝒪` are `lim Γ(Xₙ, 𝒪)` with its
inverse-limit topology. For a countably indexed affine formal algebraic space `X = colim Xₙ` this
is the case `U = X` of the defining property of the structure sheaf in Stacks 0DEJ:
`𝒪_X(X_red) = lim Γ(Xₙ, 𝒪)`.

## Main results

* `AlgebraicGeometry.Space.towerStructureSheafAffineSectionsIso`: the sections over an affine
  chart `W` are `lim Γ(Wₙ, 𝒪)`.
* `AlgebraicGeometry.Space.towerStructureSheafAffineGlobalSectionsIso`: the sections over the
  terminal chart are `lim Γ(Xₙ, 𝒪)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} (e : F ≅ yoneda.obj V)
  (T : ThickeningTower ((BigFppfOver.toScheme B S hS).obj V))

/-- **The sections of `W ↦ lim Γ(Wₙ, 𝒪)` over an affine chart `W` are `lim Γ(Wₙ, 𝒪)`**, the
inverse limit of the discrete rings `Γ(Wₙ, 𝒪)` in topological rings. -/
noncomputable def towerStructureSheafAffineSectionsIso (hF : IsAlgebraicSpace B S hS F)
    (W : AffineEtale B S hS F) :
    (towerStructureSheafAffine e T hF).obj.obj (op W) ≅
      limit (towerTopRingsSystem e T ⋙ (evaluation _ _).obj (op W)) :=
  (isLimitOfPreserves ((evaluation _ _).obj (op W))
    (isLimitOfPreserves (sheafToPresheaf _ _)
      (limit.isLimit (towerSheafSystem e T hF)))).conePointUniqueUpToIso (limit.isLimit _)

/-- The lift of the terminal chart to the stage `Xₙ` maps isomorphically onto `Xₙ`: the terminal
chart is a terminal object of the small étale site of `V`, and the lift, an equivalence, carries
it to a terminal object of the small étale site of `Xₙ`. -/
theorem isIso_lift_terminalChart_hom (n : ℕ) :
    IsIso ((T.lift n).obj ((representedChartEtale e).obj (representedTerminalChart e))).hom := by
  have h₀ : IsIso ((representedChartEtale e).obj (representedTerminalChart e)).hom := by
    have hy : IsIso (yoneda.map (chartToRepresented e (representedTerminalChart e))) := by
      have h : IsIso ((representedTerminalChart e).obj.hom ≫ e.hom) :=
        inferInstanceAs (IsIso (e.inv ≫ e.hom))
      exact (yoneda_map_chartToRepresented e _).symm ▸ h
    have : IsIso (chartToRepresented e (representedTerminalChart e)) :=
      Yoneda.fullyFaithful.isIso_of_isIso_map _
    exact Functor.map_isIso (BigFppfOver.toScheme B S hS) _
  have ht : IsTerminal ((T.lift n).obj ((representedChartEtale e).obj
      (representedTerminalChart e))) :=
    IsTerminal.isTerminalObj (T.lift n) _ (Stacks.EtaleCohomology.isTerminalOfIsIsoHom _)
  have hX : IsIso (Scheme.Etale.mk (𝟙 (T.stage.obj n))).hom :=
    inferInstanceAs (IsIso (𝟙 (T.stage.obj n)))
  let i := ht.uniqueUpToIso (Stacks.EtaleCohomology.isTerminalOfIsIsoHom
    (Scheme.Etale.mk (𝟙 (T.stage.obj n))))
  have hw : i.hom.left ≫ (Scheme.Etale.mk (𝟙 (T.stage.obj n))).hom =
      ((T.lift n).obj ((representedChartEtale e).obj (representedTerminalChart e))).hom :=
    MorphismProperty.Over.w i.hom
  have : IsIso i.hom.left :=
    inferInstanceAs (IsIso ((Scheme.Etale.forget _ ⋙ Over.forget _).map i.hom))
  rw [← hw]
  infer_instance

/-- The inverse system of the discrete rings `Γ(Xₙ, 𝒪)` of the stages of the tower. -/
noncomputable abbrev stageTopRings : ℕᵒᵖ ⥤ TopCommRingCat.{u + 1} :=
  T.stage.op ⋙ Scheme.Γ ⋙ TopCommRingCat.discreteULiftFunctor.{u + 1}

/-- The comparison of the stages `Xₙ` with the lifts `Vₙ` of the terminal chart, on rings of
functions: restriction along the isomorphisms `Vₙ ⟶ Xₙ`. -/
noncomputable def stageTopRingsToTerminal (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    stageTopRings T ⟶ towerTopRingsSystem e T ⋙
      (evaluation _ _).obj (op (representedTerminalAffineChart e hV)) :=
  NatTrans.ofOpSequence
    (fun n ↦ TopCommRingCat.discreteULiftFunctor.{u + 1}.map (Scheme.Γ.map
      ((T.lift n).obj ((representedChartEtale e).obj (representedTerminalChart e))).hom.op))
    (fun n ↦ by
      let W₀ := (representedChartEtale e).obj (representedTerminalChart e)
      let D := TopCommRingCat.discreteULiftFunctor.{u + 1}
      have h := congrArg (fun f ↦ D.map (Scheme.Γ.map f.op)) (T.transition_hom n W₀)
      simp only [op_comp, Functor.map_comp] at h
      change D.map (Scheme.Γ.map (T.stage.map (homOfLE (Nat.le_succ n))).op) ≫
          D.map (Scheme.Γ.map ((T.lift n).obj W₀).hom.op) =
        D.map (Scheme.Γ.map ((T.lift (n + 1)).obj W₀).hom.op) ≫
          D.map (((towerRingsSystem e T).map (homOfLE (Nat.le_succ n)).op).app
            (op (representedTerminalAffineChart e hV)))
      rw [towerRingsSystem_map_succ]
      exact h.symm)

/-- The comparison `stageTopRingsToTerminal` of the rings `Γ(Xₙ, 𝒪)` with the rings of functions of
the lifts `Vₙ` of the terminal chart is an isomorphism. -/
instance isIso_stageTopRingsToTerminal (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsIso (stageTopRingsToTerminal e T hV) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n ↦ ?_
  have := isIso_lift_terminalChart_hom e T n.unop
  exact (TopCommRingCat.discreteULiftFunctor.{u + 1}.mapIso
    (Scheme.Γ.mapIso (asIso ((T.lift n.unop).obj
      ((representedChartEtale e).obj (representedTerminalChart e))).hom).op)).isIso_hom

/-- **The global sections of `W ↦ lim Γ(Wₙ, 𝒪)` are `lim Γ(Xₙ, 𝒪)`**, the inverse limit of the
discrete rings of functions of the stages of the tower, as a topological ring. -/
noncomputable def towerStructureSheafAffineGlobalSectionsIso (hF : IsAlgebraicSpace B S hS F)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    (towerStructureSheafAffine e T hF).obj.obj (op (representedTerminalAffineChart e hV)) ≅
      limit (stageTopRings T) :=
  towerStructureSheafAffineSectionsIso e T hF _ ≪≫
    (HasLimit.isoOfNatIso (asIso (stageTopRingsToTerminal e T hV))).symm

/-- **The sections of `AlgebraicGeometry.Space.towerStructureSheaf` over the terminal chart are
`lim Γ(Xₙ, 𝒪)`.** -/
noncomputable def towerStructureSheafGlobalSectionsIso (hF : IsAlgebraicSpace B S hS F)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    (towerStructureSheaf e T hF).obj.obj (op (representedTerminalChart e)) ≅
      limit (stageTopRings T) :=
  ((sheafToPresheaf _ _).mapIso (towerStructureSheafRestrictionIso e T hF)).app
      (op (representedTerminalAffineChart e hV)) ≪≫
    towerStructureSheafAffineGlobalSectionsIso e T hF hV

end AlgebraicGeometry.Space

end

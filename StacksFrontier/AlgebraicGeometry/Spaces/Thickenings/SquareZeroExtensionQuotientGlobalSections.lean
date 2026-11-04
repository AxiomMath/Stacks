module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageGlobalSectionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientAlgebra
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientStructureSheaf

/-!
# Global sections of the thickened quotient realizing a square-zero extension

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
(the data of Stacks 05ZT) and `i : X ⟶ X' = U'/R'` its thickened quotient, with
`i⁻¹𝒪_{X'} ≅ 𝒜` (`AlgebraicGeometry.Space.SquareZeroExtension.quotientSheafIso`). The inverse
image along `i` is an equivalence of small étale topoi (Stacks 05ZM), so it is bijective on global
sections: every global section of `𝒜` is the image, through `i⁻¹𝒪_{X'} ≅ 𝒜`, of the inverse image
of a unique global section of `𝒪_{X'}`. On the chart `W' ⟶ X'` attached to a chart `W` of `X` over
the presenting chart, the value of that global section of `𝒪_{X'}` is the value over `W` of the
global section of `𝒜`, read in `Γ(W', ⊤) = 𝒜(W)`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.bijective_globalSectionMap_thickeningImmersion`.
*
`AlgebraicGeometry.Space.SquareZeroExtension.app_eq_of_globalSectionMap_comp_quotientSheafIso_hom`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable (P : Presentation B S hS X.obj X.property)
  (hU : B.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- **The inverse image along `X ⟶ X'` is bijective on global sections**, being an equivalence
of small étale topoi (Stacks 05ZM). -/
theorem bijective_globalSectionMap_thickeningImmersion
    (G : Sheaf (SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1) (Type u)) :
    Function.Bijective (fun a : ⊤_ _ ⟶ G =>
      (smallEtaleRingedToposHom B S hS
        (E.thickeningImmersion P hU hR)).toToposHom.inverseImage.globalSectionMap a) := by
  let t := (smallEtaleRingedToposHom B S hS (E.thickeningImmersion P hU hR)).toToposHom
  have := E.isEquivalence_pushforward_thickeningImmersion P hU hR
  have : t.inverseImage.IsEquivalence := t.adj.isEquivalence_left_of_isEquivalence_right
  have hcomp : Function.Bijective (fun b : t.inverseImage.obj (⊤_ _) ⟶ t.inverseImage.obj G =>
      CategoryTheory.inv (terminalComparison t.inverseImage) ≫ b) :=
    ⟨fun b b' h => by simpa using h, fun c => ⟨terminalComparison t.inverseImage ≫ c, by simp⟩⟩
  exact hcomp.comp ((Functor.FullyFaithful.ofFullyFaithful t.inverseImage).map_bijective _ _)

/-- **The value of a global section of `𝒪_{X'}` on the chart `W'`.** If the inverse image of a
global section `σ` of `𝒪_{X'}`, read in `𝒜` through `i⁻¹𝒪_{X'} ≅ 𝒜`, is `τ`, then the value of
`σ` over the chart `W'` attached to a chart `W` of `X` over the presenting chart is the value of
`τ` over `W`, read in `Γ(W', ⊤) = 𝒜(W)`. -/
theorem app_eq_of_globalSectionMap_comp_quotientSheafIso_hom
    (σ : ⊤_ Sheaf (SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O)
    (τ : ⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj E.A)
    (hστ : (smallEtaleRingedToposHom B S hS
        (E.thickeningImmersion P hU hR)).toToposHom.inverseImage.globalSectionMap σ ≫
      (sheafCompose _ (forget CommRingCat.{u})).map (E.quotientSheafIso P hU hR).hom = τ)
    (W : OverPresentation P)
    (p : (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)).obj.obj (op W.obj))
    (q : (⊤_ Sheaf (SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1)
      (Type u)).obj.obj (op (E.thickenedChartDiagram P hU hR W).V)) :
    σ.hom.app (op (E.thickenedChartDiagram P hU hR W).V) q =
      (E.chartRealizedSchemeΓIso W.obj).hom (τ.hom.app (op W.obj) p) := by
  have h := globalSectionMap_comp_forget_map_app B S hS (E.thickeningImmersion P hU hR) E.A
    (E.quotientSheafIso P hU hR).hom σ (E.thickenedChartDiagram P hU hR W).V
    (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) p q
  rw [hστ] at h
  exact ((E.chartRealizedSchemeΓIso W.obj).inv_hom_id_apply _).symm.trans
    (congrArg (E.chartRealizedSchemeΓIso W.obj).hom
      (h.trans (E.inverseImageHomChartRingHom_quotientSheafIso_hom P hU hR W _)).symm)

/-- The values of the terminal sheaf of sets are singletons. -/
instance _root_.CategoryTheory.Sheaf.unique_terminal_obj_obj {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J (Type u)] (U : Cᵒᵖ) :
    Unique ((⊤_ Sheaf J (Type u)).obj.obj U) :=
  (Types.isTerminalEquivUnique _) (IsTerminal.isTerminalObj
    ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj U) _ terminalIsTerminal)

/-- **The global function given by a global section of the structure sheaf**, on sheaves of
sets. -/
def _root_.AlgebraicGeometry.Space.globalFunctionsOfSection {F : AlgebraicSpaces B S hS}
    (σ : ⊤_ Sheaf (SmallEtale.topology B S hS F.1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS F).O) :
    globalFunctions B S hS F.1 :=
  ⟨fun j => σ.hom.app j default, fun {_ j'} f =>
    (ConcreteCategory.congr_hom (σ.hom.naturality f) default).symm.trans
      (congrArg (σ.hom.app j') (Subsingleton.elim _ _))⟩

/-- The value of `globalFunctionsOfSection σ` at `j` is the value of `σ` at `j` on any point
`q` of the terminal sheaf at `j`. -/
theorem _root_.AlgebraicGeometry.Space.globalFunctionsOfSection_apply {F : AlgebraicSpaces B S hS}
    (σ : ⊤_ Sheaf (SmallEtale.topology B S hS F.1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS F).O)
    (j : (SmallEtale B S hS F.1)ᵒᵖ)
    (q : (⊤_ Sheaf (SmallEtale.topology B S hS F.1) (Type u)).obj.obj j) :
    (globalFunctionsOfSection σ).1 j = σ.hom.app j q :=
  congrArg (σ.hom.app j) (Subsingleton.elim _ _)

/-- **Global functions of `X'` agreeing on the charts `W'` agree**: the charts `W'` are
cover-dense in the small étale site of `X'`, and global functions form a sheaf. -/
theorem globalFunctions_ext_of_thickenedChart
    (a b : globalFunctions B S hS (E.thickeningQuotient hS P hU hR).1)
    (h : ∀ W : OverPresentation P, a.1 (op ((E.thickenedChartFunctor P hU hR).obj W)) =
      b.1 (op ((E.thickenedChartFunctor P hU hR).obj W))) : a = b := by
  refine Subtype.ext (funext fun j => ?_)
  have hcov := Functor.IsCoverDense.is_cover (G := E.thickenedChartFunctor P hU hR)
    (K := SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1) j.unop
  refine ((isSheaf_globalSections B S hS _) _ hcov).isSeparatedFor.ext fun Y g hg => ?_
  obtain ⟨⟨W, l, m, rfl⟩⟩ := hg
  have key : ∀ c : globalFunctions B S hS (E.thickeningQuotient hS P hU hR).1,
      (structurePresheaf B S hS _ ⋙ forget CommRingCat).map (m.op ≫ l.op) (c.1 j) =
        (structurePresheaf B S hS _ ⋙ forget CommRingCat).map l.op (c.1 (op _)) := fun c => by
    rw [Functor.map_comp]
    exact congrArg _ (c.2 m.op)
  exact (key a).trans ((congrArg _ (h W)).trans (key b).symm)


/-- **`i⁻¹𝒪_{X'} ≅ 𝒜` is compatible with a global section of square zero**: if the inverse image of
a global section `σ` of `𝒪_{X'}`, read in `𝒜`, has values of square zero on the charts over the
presenting chart, then the global function `σ` has square zero. -/
theorem globalFunctionsOfSection_mul_self_eq_zero
    (σ : ⊤_ Sheaf (SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O)
    (τ : ⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj E.A)
    (hστ : (smallEtaleRingedToposHom B S hS
        (E.thickeningImmersion P hU hR)).toToposHom.inverseImage.globalSectionMap σ ≫
      (sheafCompose _ (forget CommRingCat.{u})).map (E.quotientSheafIso P hU hR).hom = τ)
    (hτ : ∀ (W : OverPresentation P) (p : (⊤_ Sheaf (SmallEtale.topology B S hS X.1)
        (Type u)).obj.obj (op W.obj)),
      (E.chartRealizedSchemeΓIso W.obj).hom (τ.hom.app (op W.obj) p) *
        (E.chartRealizedSchemeΓIso W.obj).hom (τ.hom.app (op W.obj) p) = 0) :
    globalFunctionsOfSection σ * globalFunctionsOfSection σ = 0 := by
  refine E.globalFunctions_ext_of_thickenedChart P hU hR _ _ fun W => ?_
  have h := E.app_eq_of_globalSectionMap_comp_quotientSheafIso_hom P hU hR σ τ hστ W default default
  show (globalFunctionsOfSection σ).1 (op (E.thickenedChartDiagram P hU hR W).V) *
    (globalFunctionsOfSection σ).1 (op (E.thickenedChartDiagram P hU hR W).V) = 0
  rw [globalFunctionsOfSection_apply σ _ default, h]
  exact hτ W default

end AlgebraicGeometry.Space.SquareZeroExtension

end

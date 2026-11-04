module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceTheta
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaSection
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.LegSections
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleOpen
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictCanHom
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators

/-!
# The identification of the targets of `θ` around a square (Stacks 0D2Z)

The square of the scheme factor of the chart maps of `θ` (Stacks 0D2Z, for an algebraic space
`X`) reduces (`AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq_of_factors`) to a
compatibility of the identifications of the targets `⨁_d ℒ^{⊗ d}|_{U}`.  Those identifications are
composites of the pseudofunctoriality isomorphisms of the inverse image of modules, of the
comparisons `restrictFunctorIsoPullback` of a restriction with an inverse image, and of the
comparisons of tensor powers.  This file proves that compatibility,
`AlgebraicGeometry.Space.chartScheme_target_coherence`, by computing both sides on twice
pulled-back sections; the pieces of the computation are:

* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.squareChainIso_hom_app`: the degree-`d`
  component of `…squareChainIso`, written out with its factors as variables and its pieces read as
  modules on the schemes;
* `laurentOnHomOfLEPieceIso_inv_val_app_map`: the inverse of the restriction
  `(U₁ ⊆ U₂)^*(ℒ^{⊗ n}|_{U₂}) ≅ ℒ^{⊗ n}|_{U₁}` on a restricted section;
* `AlgebraicGeometry.Space.sectionPieceChain_val_app_pullbackSection`: the identification
  `g^*(K|_U) ≅ K` along a section `g` of `U ⊆ T` (the shape of
  `…GradedPowerMap.laurentOnSectionPieceIso`) on a pulled-back section;
* `AlgebraicGeometry.Space.comp7_val_app`: a composite of seven morphisms on a section;
* `AlgebraicGeometry.Space.squareChain_val_app_of_eq`,
  `AlgebraicGeometry.Space.thetaTargetChain_val_app_of_eq`,
  `AlgebraicGeometry.Space.sectionPiece_val_app_of_eq`,
  `AlgebraicGeometry.Space.transportPiece_val_app_of_eq`,
  `AlgebraicGeometry.Space.pullbackPiece_val_app_of_eq`: the identifications on pulled-back
  sections, with their factors variables;
* `AlgebraicGeometry.Space.targetCoherence_of_values`: the coherence from the values of the
  factors.

## Implementation notes

The pseudofunctoriality isomorphisms `Scheme.Modules.pullbackComp`, `Scheme.Modules.pullbackCongr`
and the composites built from them are kept *variables* while a chain of them is evaluated on a
section, their values on pulled-back sections being hypotheses: when the intermediate modules of a
chain are spelled differently by its consecutive factors (for instance `(g ⋙ f).obj M` and
`f.obj (g.obj M)`), the kernel otherwise evaluates those isomorphisms to compare the two spellings,
which exhausts its budget.  They are instantiated only in the hypotheses, where each value lemma
has exactly the spelling of its factor.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

section SquareChain

variable {U₀ U₂ Uχ Uψ : Scheme.{u}} {k : U₀ ⟶ Uχ} {n : U₀ ⟶ U₂} {k₂ : U₂ ⟶ Uχ}
  {j₂ : U₂ ⟶ Uψ} {j : U₀ ⟶ Uψ} (hk : n ≫ k₂ = k) (hj : n ≫ j₂ = j)

/-- The degree-`d` component of `squareChainIso`, written out, with the components of the given
identifications as variables (and the pieces read as modules on the schemes). -/
theorem squareChainIso_hom_app
    {A₀ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₀.toRingedSpace)}
    {A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₂.toRingedSpace)}
    {Aχ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uχ.toRingedSpace)}
    {Aψ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uψ.toRingedSpace)}
    (S₁ : pullbackGradedAlgebra k.toLRSHom.toShHom Aχ ≅ A₀)
    (S₂ : pullbackGradedAlgebra k₂.toLRSHom.toShHom Aχ ≅ A₂)
    (S₄ : pullbackGradedAlgebra j₂.toLRSHom.toShHom Aψ ≅ A₂) (d : ℤ)
    (S₁d : (Scheme.Modules.pullback k).obj
        (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d) ⟶
      @SheafOfModules.GradedAlgebra.piece _ _ _ U₀.ringCatSheaf A₀ d) (hS₁ : S₁.hom.app d = S₁d)
    (S₂d : @SheafOfModules.GradedAlgebra.piece _ _ _ U₂.ringCatSheaf A₂ d ⟶
      (Scheme.Modules.pullback k₂).obj
        (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d))
    (hS₂ : S₂.inv.app d = S₂d)
    (S₄d : (Scheme.Modules.pullback j₂).obj
        (@SheafOfModules.GradedAlgebra.piece _ _ _ Uψ.ringCatSheaf Aψ d) ⟶
      @SheafOfModules.GradedAlgebra.piece _ _ _ U₂.ringCatSheaf A₂ d) (hS₄ : S₄.hom.app d = S₄d) :
    (squareChainIso hk hj S₁ S₂ S₄).hom.app d =
      (Scheme.Modules.pullbackCongr hj).inv.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uψ.ringCatSheaf Aψ d) ≫
        (Scheme.Modules.pullbackComp n j₂).inv.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uψ.ringCatSheaf Aψ d) ≫
        (Scheme.Modules.pullback n).map (S₄d ≫ S₂d) ≫
        (Scheme.Modules.pullbackComp n k₂).hom.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d) ≫
        (Scheme.Modules.pullbackCongr hk).hom.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d) ≫ S₁d := by
  subst hS₁ hS₂ hS₄
  rfl

end SquareChain

section LaurentOnHomOfLE

variable {T : Scheme.{u}} (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]

/-- The degree-`n` component of `(laurentOnHomOfLEIso L h).hom` is the restriction
`(laurentOnHomOfLEPieceIso L h n).hom`. -/
theorem laurentOnHomOfLEIso_hom_app {U₁ U₂ : T.Opens} (h : U₁ ≤ U₂) (n : ℤ) :
    (laurentOnHomOfLEIso L h).hom.app n = (laurentOnHomOfLEPieceIso L h n).hom :=
  rfl

/-- The degree-`n` component of `(laurentOnHomOfLEIso L h).inv` is the inverse
`(laurentOnHomOfLEPieceIso L h n).inv`. -/
theorem laurentOnHomOfLEIso_inv_app {U₁ U₂ : T.Opens} (h : U₁ ≤ U₂) (n : ℤ) :
    (laurentOnHomOfLEIso L h).inv.app n = (laurentOnHomOfLEPieceIso L h n).inv :=
  rfl

/-- The inverse of `(U₁ ⊆ U₂)^*(ℒ^{⊗ n}|_{U₂}) ≅ ℒ^{⊗ n}|_{U₁}` on a restricted section is the
pulled-back section. -/
theorem laurentOnHomOfLEPieceIso_inv_val_app_map {U₁ U₂ : T.Opens} (h : U₁ ≤ U₂) (n : ℤ)
    (O' : U₂.toScheme.Opens) (V : U₁.toScheme.Opens) (h4 : V ≤ T.homOfLE h ⁻¹ᵁ O')
    (t : Γ((tensorPowerModule T L n).restrict U₂.ι, O')) (hV : U₁.ι ''ᵁ V ≤ U₂.ι ''ᵁ O') :
    (laurentOnHomOfLEPieceIso L h n).inv.val.app (op V)
        ((tensorPowerModule T L n).val.map (homOfLE hV).op t) =
      pullbackSection (T.homOfLE h) ((laurentOn L U₂).piece n) O' V h4 t := by
  rw [← laurentOnHomOfLEPieceIso_hom_pullbackSection L h n O' V h4 t]
  exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app (op V))
    (laurentOnHomOfLEPieceIso L h n).hom_inv_id) _

end LaurentOnHomOfLE

/-- The degree-`n` component of `laurentOnCongrPieceIso` on a section is the comparison of the
tensor powers on the image of the open. -/
theorem laurentOnCongrPieceIso_hom_val_app {T : Scheme.{u}} {L L' : T.Modules}
    [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L'] (e : L ≅ L')
    (U : T.Opens) (n : ℤ) (W : U.toScheme.Opens) (t : ((laurentOn L U).piece n).val.obj (op W)) :
    (laurentOnCongrPieceIso e U n).hom.val.app (op W) t =
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso e n).hom.val.app
        (op (U.ι ''ᵁ W)) t :=
  rfl

namespace GradedPowerMap

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S} (P : GradedPowerMap A f)

/-- `laurentOnSectionPieceIso` written out as a composite of its four factors. -/
theorem laurentOnSectionPieceIso_hom_eq (g : T ⟶ P.coveringOpen.toScheme)
    (hg : g ≫ P.coveringOpen.ι = 𝟙 T) (n : ℤ) :
    (P.laurentOnSectionPieceIso g hg n).hom =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.restrictFunctorIsoPullback
          P.coveringOpen.ι).hom.app (tensorPowerModule T P.L n)) ≫
        (Scheme.Modules.pullbackComp g P.coveringOpen.ι).hom.app (tensorPowerModule T P.L n) ≫
        (Scheme.Modules.pullbackCongr hg).hom.app (tensorPowerModule T P.L n) ≫
        (Scheme.Modules.pullbackId T).hom.app (tensorPowerModule T P.L n) :=
  rfl

/-- The degree-`d` component of `thetaTransportTargetIso`: the restriction along `U₁ ⊆ U(P)`
followed by the comparison induced by `e`. -/
theorem thetaTransportTargetIso_hom_app {L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L']
    (e : P.L ≅ L') {U₁ : T.Opens} (hU : U₁ ≤ P.coveringOpen) (d : ℤ) :
    (P.thetaTransportTargetIso e hU).hom.app d =
      (laurentOnHomOfLEPieceIso P.L hU d).hom ≫ (laurentOnCongrPieceIso e U₁ d).hom :=
  rfl

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space

section TargetCoherence

variable {T T' : Scheme.{u}}

/-- A composite of seven morphisms of modules on a scheme, on a section. -/
theorem comp7_val_app {Y : Scheme.{u}} {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : Y.Modules} (f₁ : X₀ ⟶ X₁)
    (f₂ : X₁ ⟶ X₂) (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₄) (f₅ : X₄ ⟶ X₅) (f₆ : X₅ ⟶ X₆) (f₇ : X₆ ⟶ X₇)
    (V : Y.Opens) (x : X₀.val.obj (op V)) :
    (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ ≫ f₇).val.app (op V) x =
      f₇.val.app (op V) (f₆.val.app (op V) (f₅.val.app (op V) (f₄.val.app (op V)
        (f₃.val.app (op V) (f₂.val.app (op V) (f₁.val.app (op V) x)))))) :=
  rfl

/-- The identification `g^*(K|_U) ≅ K` along a section `g` of the inclusion `ι : U ⟶ T`, on a
pulled-back section: it is the restriction. -/
theorem sectionPieceChain_val_app_pullbackSection {U : T.Opens} (g : T ⟶ U.toScheme)
    (hg : g ≫ U.ι = 𝟙 T) (K : T.Modules) (O : U.toScheme.Opens) (V : T.Opens)
    (h : V ≤ g ⁻¹ᵁ O) (hV : V ≤ U.ι ''ᵁ O) (t : (K.restrict U.ι).val.obj (op O)) :
    ((Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app K) ≫
      (Scheme.Modules.pullbackComp g U.ι).hom.app K ≫
      (Scheme.Modules.pullbackCongr hg).hom.app K ≫
      (Scheme.Modules.pullbackId T).hom.app K).val.app (op V)
        (pullbackSection g (K.restrict U.ι) O V h t) =
      K.val.map (homOfLE hV).op t := by
  have hO : O ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ O) := (U.ι.preimage_image_eq O).ge
  have h5 : V ≤ (g ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ O) := h.trans (g.preimage_mono hO)
  have h6 : V ≤ (𝟙 T) ⁻¹ᵁ (U.ι ''ᵁ O) := hg ▸ h5
  have g1 := (Scheme.Modules.pullbackSection_naturality g
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app K) O V h t).trans
      (congrArg (pullbackSection g _ O V h) (restrictFunctorIsoPullback_hom_val_app U.ι K O hO t))
  have g2 := Scheme.Modules.pullbackSection_comp g U.ι K (U.ι ''ᵁ O) O V hO h h5 t
  have g3 := Scheme.Modules.pullbackSection_congr hg K (U.ι ''ᵁ O) V h5 h6 t
  have g4 := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pullbackId_hom_pullbackSection
    K (U.ι ''ᵁ O) V h6 hV t
  have g12 :=
    (congrArg (((Scheme.Modules.pullbackComp g U.ι).hom.app K).val.app (op V)) g1).trans g2
  have g123 :=
    (congrArg (((Scheme.Modules.pullbackCongr hg).hom.app K).val.app (op V)) g12).trans g3
  exact (congrArg (((Scheme.Modules.pullbackId T).hom.app K).val.app (op V)) g123).trans g4

/-- **The chain `squareChainIso` on a pulled-back section, with its factors variables.**  For
`Usq ⊆ U₂ ⊆ U_χ`, `l = (Usq ⊆ U₂) ≫ j₂`, a map `Ch` written as the chain
`P₁ ≫ P₂ ≫ (Usq ⊆ U₂)^*S₄ ≫ (Usq ⊆ U₂)^*R₂⁻¹ ≫ P₅ ≫ P₆ ≫ R₁` whose factors `P_i` (the
pseudofunctoriality and congruence isomorphisms of the inverse image), `R₁`, `R₂` (the
restrictions of `ℒ^{⊗ d}`) and `S₄` are variables with their values on pulled-back sections as
hypotheses, `Ch` carries the pullback of a section `a` along `l` to the restriction of the value
`z₀` of `S₄` on the pullback of `a` along `j₂`.  Keeping the factors variables keeps the kernel
from unfolding the pseudofunctoriality isomorphisms when the spellings of the intermediate
modules differ. -/
theorem squareChain_val_app_of_eq (L : T'.Modules) [Stacks.Ample.IsInvertibleModule T' L] (d : ℤ)
    {Ux : Scheme.{u}} (Usq U₂ Uχ : T'.Opens) (hsq₂ : Usq ≤ U₂)
    (h₂χ : U₂ ≤ Uχ) (hsqχ : Usq ≤ Uχ)
    (hkk : T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ = T'.homOfLE hsqχ)
    (l : Usq.toScheme ⟶ Ux) (j₂ : U₂.toScheme ⟶ Ux) (hj₂ : T'.homOfLE hsq₂ ≫ j₂ = l)
    (N : Ux.Modules)
    (R₂ : (Scheme.Modules.pullback (T'.homOfLE h₂χ)).obj ((laurentOn L Uχ).piece d) ≅
      (laurentOn L U₂).piece d)
    (hR₂ : ∀ (O' : Uχ.toScheme.Opens) (V : U₂.toScheme.Opens) (h4 : V ≤ T'.homOfLE h₂χ ⁻¹ᵁ O')
      (t : ((laurentOn L Uχ).piece d).val.obj (op O')) (hV : U₂.ι ''ᵁ V ≤ Uχ.ι ''ᵁ O'),
      R₂.hom.val.app (op V) (pullbackSection (T'.homOfLE h₂χ) _ O' V h4 t) =
        (tensorPowerModule T' L d).val.map (homOfLE hV).op t)
    (R₁ : (Scheme.Modules.pullback (T'.homOfLE hsqχ)).obj ((laurentOn L Uχ).piece d) ≅
      (laurentOn L Usq).piece d)
    (hR₁ : ∀ (O' : Uχ.toScheme.Opens) (V : Usq.toScheme.Opens) (h4 : V ≤ T'.homOfLE hsqχ ⁻¹ᵁ O')
      (t : ((laurentOn L Uχ).piece d).val.obj (op O')) (hV : Usq.ι ''ᵁ V ≤ Uχ.ι ''ᵁ O'),
      R₁.hom.val.app (op V) (pullbackSection (T'.homOfLE hsqχ) _ O' V h4 t) =
        (tensorPowerModule T' L d).val.map (homOfLE hV).op t)
    (S₄d : (Scheme.Modules.pullback j₂).obj N ⟶ (laurentOn L U₂).piece d)
    (P₁ : (Scheme.Modules.pullback l).obj N ⟶ (Scheme.Modules.pullback (T'.homOfLE hsq₂ ≫ j₂)).obj
        N)
    (hP₁ : ∀ (O : Ux.Opens) (V : Usq.toScheme.Opens) (hf : V ≤ (T'.homOfLE hsq₂ ≫ j₂) ⁻¹ᵁ O)
      (hg : V ≤ l ⁻¹ᵁ O) (a : N.val.obj (op O)),
      P₁.val.app (op V) (pullbackSection l N O V hg a) =
        pullbackSection (T'.homOfLE hsq₂ ≫ j₂) N O V hf a)
    (P₂ : (Scheme.Modules.pullback (T'.homOfLE hsq₂ ≫ j₂)).obj N ⟶
      (Scheme.Modules.pullback j₂ ⋙ Scheme.Modules.pullback (T'.homOfLE hsq₂)).obj N)
    (hP₂ : ∀ (O : Ux.Opens) (W₀ : U₂.toScheme.Opens) (V : Usq.toScheme.Opens)
      (hg : W₀ ≤ j₂ ⁻¹ᵁ O) (hf : V ≤ T'.homOfLE hsq₂ ⁻¹ᵁ W₀)
      (h : V ≤ (T'.homOfLE hsq₂ ≫ j₂) ⁻¹ᵁ O) (a : N.val.obj (op O)),
      P₂.val.app (op V) (pullbackSection (T'.homOfLE hsq₂ ≫ j₂) N O V h a) =
        pullbackSection (T'.homOfLE hsq₂) ((Scheme.Modules.pullback j₂).obj N) W₀ V hf
          (pullbackSection j₂ N O W₀ hg a))
    (P₅ : (Scheme.Modules.pullback (T'.homOfLE h₂χ) ⋙ Scheme.Modules.pullback (T'.homOfLE hsq₂)).obj
        ((laurentOn L Uχ).piece d) ⟶
      (Scheme.Modules.pullback (T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ)).obj ((laurentOn L Uχ).piece d))
    (hP₅ : ∀ (U : Uχ.toScheme.Opens) (W : U₂.toScheme.Opens) (V : Usq.toScheme.Opens)
      (hg : W ≤ T'.homOfLE h₂χ ⁻¹ᵁ U) (hf : V ≤ T'.homOfLE hsq₂ ⁻¹ᵁ W)
      (h : V ≤ (T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ) ⁻¹ᵁ U)
      (a : ((laurentOn L Uχ).piece d).val.obj (op U)),
      P₅.val.app (op V) (pullbackSection (T'.homOfLE hsq₂)
        ((Scheme.Modules.pullback (T'.homOfLE h₂χ)).obj ((laurentOn L Uχ).piece d)) W V hf
          (pullbackSection (T'.homOfLE h₂χ) ((laurentOn L Uχ).piece d) U W hg a)) =
        pullbackSection (T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ) ((laurentOn L Uχ).piece d) U V h a)
    (P₆ : (Scheme.Modules.pullback (T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ)).obj ((laurentOn L Uχ).piece
        d) ⟶
      (Scheme.Modules.pullback (T'.homOfLE hsqχ)).obj ((laurentOn L Uχ).piece d))
    (hP₆ : ∀ (U : Uχ.toScheme.Opens) (V : Usq.toScheme.Opens)
      (hf : V ≤ (T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ) ⁻¹ᵁ U) (hg : V ≤ T'.homOfLE hsqχ ⁻¹ᵁ U)
      (a : ((laurentOn L Uχ).piece d).val.obj (op U)),
      P₆.val.app (op V) (pullbackSection (T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ) _ U V hf a) =
        pullbackSection (T'.homOfLE hsqχ) _ U V hg a)
    (Ch : (Scheme.Modules.pullback l).obj N ⟶ (laurentOn L Usq).piece d)
    (hCh : Ch = P₁ ≫ P₂ ≫ (Scheme.Modules.pullback (T'.homOfLE hsq₂)).map S₄d ≫
      (Scheme.Modules.pullback (T'.homOfLE hsq₂)).map R₂.inv ≫ P₅ ≫ P₆ ≫ R₁.hom)
    (O : Ux.Opens) (a : N.val.obj (op O)) (W : T'.Opens) (z₀ : (tensorPowerModule T' L d).val.obj
        (op W))
    (hV3 : U₂.ι ''ᵁ (j₂ ⁻¹ᵁ O) ≤ W)
    (hS₄v : S₄d.val.app (op (j₂ ⁻¹ᵁ O)) (pullbackSection j₂ N O (j₂ ⁻¹ᵁ O) le_rfl a) =
      (tensorPowerModule T' L d).val.map (homOfLE hV3).op z₀)
    (h4 : j₂ ⁻¹ᵁ O ≤ T'.homOfLE h₂χ ⁻¹ᵁ (Uχ.ι ⁻¹ᵁ W)) (hc : Usq.ι ''ᵁ (l ⁻¹ᵁ O) ≤ W) :
    Ch.val.app (op (l ⁻¹ᵁ O)) (pullbackSection l N O (l ⁻¹ᵁ O) le_rfl a) =
      (tensorPowerModule T' L d).val.map (homOfLE hc).op z₀ := by
  subst hCh
  have h1 : l ⁻¹ᵁ O ≤ (T'.homOfLE hsq₂ ≫ j₂) ⁻¹ᵁ O := by rw [hj₂]
  have h1' : l ⁻¹ᵁ O ≤ T'.homOfLE hsq₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ O) := h1
  have hz : Uχ.ι ''ᵁ (Uχ.ι ⁻¹ᵁ W) ≤ W := Uχ.ι.image_preimage_le _
  have hzz : U₂.ι ''ᵁ (j₂ ⁻¹ᵁ O) ≤ Uχ.ι ''ᵁ (Uχ.ι ⁻¹ᵁ W) :=
    image_le_image_of_le_preimage_homOfLE h₂χ _ h4
  have h5 : l ⁻¹ᵁ O ≤ (T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ) ⁻¹ᵁ (Uχ.ι ⁻¹ᵁ W) :=
    h1.trans ((T'.homOfLE hsq₂).preimage_mono h4)
  have h6 : l ⁻¹ᵁ O ≤ T'.homOfLE hsqχ ⁻¹ᵁ (Uχ.ι ⁻¹ᵁ W) := by rw [← hkk]; exact h5
  have c1 := hP₁ O (l ⁻¹ᵁ O) h1 le_rfl a
  have c2 := hP₂ O (j₂ ⁻¹ᵁ O) (l ⁻¹ᵁ O) le_rfl h1' h1 a
  have c4 : R₂.inv.val.app (op (j₂ ⁻¹ᵁ O)) ((tensorPowerModule T' L d).val.map (homOfLE hV3).op
      z₀) =
      pullbackSection (T'.homOfLE h₂χ) _ (Uχ.ι ⁻¹ᵁ W) (j₂ ⁻¹ᵁ O) h4
        ((tensorPowerModule T' L d).val.map (homOfLE hz).op z₀) :=
    (congrArg (R₂.inv.val.app (op (j₂ ⁻¹ᵁ O)))
      ((AlgebraicGeometry.val_map_map (homOfLE hz).op (homOfLE hzz).op z₀ (homOfLE
          hV3).op).symm.trans
        (hR₂ _ _ h4 _ hzz).symm)).trans
      (ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app (op (j₂ ⁻¹ᵁ O))) R₂.hom_inv_id) _)
  have m1 := (Scheme.Modules.pullbackSection_naturality (T'.homOfLE hsq₂)
      S₄d (j₂ ⁻¹ᵁ O) (l ⁻¹ᵁ O) h1' _).trans
        (congrArg (pullbackSection (T'.homOfLE hsq₂) _ (j₂ ⁻¹ᵁ O) (l ⁻¹ᵁ O) h1') hS₄v)
  have m2 := (Scheme.Modules.pullbackSection_naturality (T'.homOfLE hsq₂)
      R₂.inv (j₂ ⁻¹ᵁ O) (l ⁻¹ᵁ O) h1' _).trans
        (congrArg (pullbackSection (T'.homOfLE hsq₂) _ (j₂ ⁻¹ᵁ O) (l ⁻¹ᵁ O) h1') c4)
  have c5 := hP₅ (Uχ.ι ⁻¹ᵁ W) (j₂ ⁻¹ᵁ O) (l ⁻¹ᵁ O) h4 h1' h5
    ((tensorPowerModule T' L d).val.map (homOfLE hz).op z₀)
  have c6 := hP₆ (Uχ.ι ⁻¹ᵁ W) (l ⁻¹ᵁ O) h5 h6 ((tensorPowerModule T' L d).val.map (homOfLE hz).op
      z₀)
  have c7 := (hR₁ _ _ h6 ((tensorPowerModule T' L d).val.map (homOfLE hz).op z₀)
    (image_le_image_of_le_preimage_homOfLE hsqχ _ h6)).trans
      (AlgebraicGeometry.val_map_map _ _ _ (homOfLE hc).op)
  refine (comp7_val_app _ _ _ _ _ _ _ _ _).trans ?_
  rw [c1, c2, m1, m2, c5, c6, c7]

/-- **The identification `g^*(ℒ^{⊗ n}|_U) ≅ ℒ^{⊗ n}` along a section `g` of `U ⊆ T`, on a
pulled-back section**, for a map `φ` given as a chain of four factors that are variables with
their values on pulled-back sections as hypotheses (the shape of
`…GradedPowerMap.laurentOnSectionPieceIso`): `φ` is the restriction. -/
theorem sectionPiece_val_app_of_eq {T : Scheme.{u}} (L : T.Modules)
    [Stacks.Ample.IsInvertibleModule T L]
    (n : ℤ) (U : T.Opens) (g : T ⟶ U.toScheme)
    (φ : (Scheme.Modules.pullback g).obj ((laurentOn L U).piece n) ⟶ tensorPowerModule T L n)
    (A₁ : (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj (tensorPowerModule T L n)) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback U.ι).obj (tensorPowerModule T L n)))
    (A₂ : (Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback g).obj (tensorPowerModule T L n) ⟶
      (Scheme.Modules.pullback (g ≫ U.ι)).obj (tensorPowerModule T L n))
    (A₃ : (Scheme.Modules.pullback (g ≫ U.ι)).obj (tensorPowerModule T L n) ⟶
      (Scheme.Modules.pullback (𝟙 T)).obj (tensorPowerModule T L n))
    (A₄ : (Scheme.Modules.pullback (𝟙 T)).obj (tensorPowerModule T L n) ⟶
      (𝟭 T.Modules).obj (tensorPowerModule T L n))
    (hφ : φ = A₁ ≫ A₂ ≫ A₃ ≫ A₄)
    (hA₁ : ∀ (O : U.toScheme.Opens) (V : T.Opens) (h : V ≤ g ⁻¹ᵁ O) (hO : O ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ O))
      (t : ((Scheme.Modules.restrictFunctor U.ι).obj (tensorPowerModule T L n)).val.obj (op O)),
      A₁.val.app (op V) (pullbackSection g _ O V h t) =
        pullbackSection g ((Scheme.Modules.pullback U.ι).obj (tensorPowerModule T L n)) O V h
          (pullbackSection U.ι (tensorPowerModule T L n) (U.ι ''ᵁ O) O hO t))
    (hA₂ : ∀ (U₀ : T.Opens) (W : U.toScheme.Opens) (V : T.Opens) (hg : W ≤ U.ι ⁻¹ᵁ U₀)
      (hf : V ≤ g ⁻¹ᵁ W) (h : V ≤ (g ≫ U.ι) ⁻¹ᵁ U₀) (a : (tensorPowerModule T L n).val.obj (op U₀)),
      A₂.val.app (op V) (pullbackSection g ((Scheme.Modules.pullback U.ι).obj (tensorPowerModule T
          L n))
        W V hf (pullbackSection U.ι _ U₀ W hg a)) = pullbackSection (g ≫ U.ι) _ U₀ V h a)
    (hA₃ : ∀ (U₀ : T.Opens) (V : T.Opens) (hf : V ≤ (g ≫ U.ι) ⁻¹ᵁ U₀) (hg : V ≤ (𝟙 T) ⁻¹ᵁ U₀)
      (a : (tensorPowerModule T L n).val.obj (op U₀)),
      A₃.val.app (op V) (pullbackSection (g ≫ U.ι) _ U₀ V hf a) = pullbackSection (𝟙 T) _ U₀ V hg a)
    (hA₄ : ∀ (U₀ V : T.Opens) (h : V ≤ (𝟙 T) ⁻¹ᵁ U₀) (hVU : V ≤ U₀)
      (a : (tensorPowerModule T L n).val.obj (op U₀)),
      A₄.val.app (op V) (pullbackSection (𝟙 T) _ U₀ V h a) =
        (tensorPowerModule T L n).val.map (homOfLE hVU).op a)
    (hg : g ≫ U.ι = 𝟙 T)
    (O : U.toScheme.Opens) (V : T.Opens) (h : V ≤ g ⁻¹ᵁ O) (hV : V ≤ U.ι ''ᵁ O)
    (t : ((laurentOn L U).piece n).val.obj (op O)) :
    φ.val.app (op V) (pullbackSection g ((laurentOn L U).piece n) O V h t) =
      (tensorPowerModule T L n).val.map (homOfLE hV).op t := by
  subst hφ
  have hO : O ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ O) := (U.ι.preimage_image_eq O).ge
  have h5 : V ≤ (g ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ O) := h.trans (g.preimage_mono hO)
  have h6 : V ≤ (𝟙 T) ⁻¹ᵁ (U.ι ''ᵁ O) := hg ▸ h5
  have e1 := hA₁ O V h hO t
  have e2 := hA₂ (U.ι ''ᵁ O) O V hO h h5 t
  have e3 := hA₃ (U.ι ''ᵁ O) V h5 h6 t
  have e4 := hA₄ (U.ι ''ᵁ O) V h6 hV t
  exact (congrArg (A₄.val.app (op V)) ((congrArg (A₃.val.app (op V))
    ((congrArg (A₂.val.app (op V)) e1).trans e2)).trans e3)).trans e4

/-- **The identification `j₂^*(ℒ^{⊗ d}|_U) ≅ (τ^*ℒ)^{⊗ d}|_{U₂}` on a pulled-back section**, for a
map `φ` given as a chain of six factors (the shape of `…thetaTargetPieceIso`, with the comparison
`P : τ^*(ℒ^{⊗ d}) ⟶ ℒ'^{⊗ d}` of the tensor powers) that are variables with their values on
pulled-back sections as hypotheses: `φ` carries the pullback of `t` along `j₂` to the restriction
of `P` applied to the pullback of `t` along `τ`. -/
theorem thetaTargetChain_val_app_of_eq (τ : T' ⟶ T) (L₀ : T.Modules)
    [Stacks.Ample.IsInvertibleModule T L₀]
    (L₀' : T'.Modules) [Stacks.Ample.IsInvertibleModule T' L₀'] (d : ℤ) (U : T.Opens) (U₂ :
        T'.Opens)
    (j₂ : U₂.toScheme ⟶ U.toScheme) (hj₂ι : j₂ ≫ U.ι = U₂.ι ≫ τ)
    (P : (Scheme.Modules.pullback τ).obj (tensorPowerModule T L₀ d) ⟶ tensorPowerModule T' L₀' d)
    (φ : (Scheme.Modules.pullback j₂).obj ((laurentOn L₀ U).piece d) ⟶ (laurentOn L₀' U₂).piece d)
    (A₁ : (Scheme.Modules.pullback j₂).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj (tensorPowerModule T L₀ d)) ⟶
      (Scheme.Modules.pullback j₂).obj ((Scheme.Modules.pullback U.ι).obj (tensorPowerModule T L₀
          d)))
    (A₂ : (Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback j₂).obj (tensorPowerModule T L₀
        d) ⟶
      (Scheme.Modules.pullback (j₂ ≫ U.ι)).obj (tensorPowerModule T L₀ d))
    (A₃ : (Scheme.Modules.pullback (j₂ ≫ U.ι)).obj (tensorPowerModule T L₀ d) ⟶
      (Scheme.Modules.pullback (U₂.ι ≫ τ)).obj (tensorPowerModule T L₀ d))
    (A₄ : (Scheme.Modules.pullback (U₂.ι ≫ τ)).obj (tensorPowerModule T L₀ d) ⟶
      (Scheme.Modules.pullback τ ⋙ Scheme.Modules.pullback U₂.ι).obj (tensorPowerModule T L₀ d))
    (A₅ : (Scheme.Modules.pullback U₂.ι).obj ((Scheme.Modules.pullback τ).obj (tensorPowerModule T
        L₀ d)) ⟶
      (Scheme.Modules.pullback U₂.ι).obj (tensorPowerModule T' L₀' d))
    (A₆ : (Scheme.Modules.pullback U₂.ι).obj (tensorPowerModule T' L₀' d) ⟶
      (Scheme.Modules.restrictFunctor U₂.ι).obj (tensorPowerModule T' L₀' d))
    (hφ : φ = A₁ ≫ A₂ ≫ A₃ ≫ A₄ ≫ A₅ ≫ A₆)
    (hA₁ : ∀ (O : U.toScheme.Opens) (V : U₂.toScheme.Opens) (h : V ≤ j₂ ⁻¹ᵁ O)
      (hO : O ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ O))
      (t : ((Scheme.Modules.restrictFunctor U.ι).obj (tensorPowerModule T L₀ d)).val.obj (op O)),
      A₁.val.app (op V) (pullbackSection j₂ _ O V h t) =
        pullbackSection j₂ ((Scheme.Modules.pullback U.ι).obj (tensorPowerModule T L₀ d)) O V h
          (pullbackSection U.ι (tensorPowerModule T L₀ d) (U.ι ''ᵁ O) O hO t))
    (hA₂ : ∀ (U₀ : T.Opens) (W : U.toScheme.Opens) (V : U₂.toScheme.Opens) (hg : W ≤ U.ι ⁻¹ᵁ U₀)
      (hf : V ≤ j₂ ⁻¹ᵁ W) (h : V ≤ (j₂ ≫ U.ι) ⁻¹ᵁ U₀)
      (a : (tensorPowerModule T L₀ d).val.obj (op U₀)),
      A₂.val.app (op V) (pullbackSection j₂ ((Scheme.Modules.pullback U.ι).obj
        (tensorPowerModule T L₀ d)) W V hf (pullbackSection U.ι _ U₀ W hg a)) =
          pullbackSection (j₂ ≫ U.ι) _ U₀ V h a)
    (hA₃ : ∀ (U₀ : T.Opens) (V : U₂.toScheme.Opens) (hf : V ≤ (j₂ ≫ U.ι) ⁻¹ᵁ U₀)
      (hg : V ≤ (U₂.ι ≫ τ) ⁻¹ᵁ U₀) (a : (tensorPowerModule T L₀ d).val.obj (op U₀)),
      A₃.val.app (op V) (pullbackSection (j₂ ≫ U.ι) _ U₀ V hf a) =
        pullbackSection (U₂.ι ≫ τ) _ U₀ V hg a)
    (hA₄ : ∀ (U₀ : T.Opens) (W₀ : T'.Opens) (V : U₂.toScheme.Opens) (hg : W₀ ≤ τ ⁻¹ᵁ U₀)
      (hf : V ≤ U₂.ι ⁻¹ᵁ W₀) (h : V ≤ (U₂.ι ≫ τ) ⁻¹ᵁ U₀)
      (a : (tensorPowerModule T L₀ d).val.obj (op U₀)),
      A₄.val.app (op V) (pullbackSection (U₂.ι ≫ τ) _ U₀ V h a) =
        pullbackSection U₂.ι ((Scheme.Modules.pullback τ).obj (tensorPowerModule T L₀ d)) W₀ V hf
          (pullbackSection τ _ U₀ W₀ hg a))
    (hA₅ : ∀ (W₀ : T'.Opens) (V : U₂.toScheme.Opens) (h : V ≤ U₂.ι ⁻¹ᵁ W₀)
      (x : ((Scheme.Modules.pullback τ).obj (tensorPowerModule T L₀ d)).val.obj (op W₀)),
      A₅.val.app (op V) (pullbackSection U₂.ι _ W₀ V h x) =
        pullbackSection U₂.ι (tensorPowerModule T' L₀' d) W₀ V h (P.val.app (op W₀) x))
    (hA₆ : ∀ (W₀ : T'.Opens) (V : U₂.toScheme.Opens) (h : V ≤ U₂.ι ⁻¹ᵁ W₀) (h' : U₂.ι ''ᵁ V ≤ W₀)
      (b : (tensorPowerModule T' L₀' d).val.obj (op W₀)),
      A₆.val.app (op V) (pullbackSection U₂.ι _ W₀ V h b) =
        (tensorPowerModule T' L₀' d).val.map (homOfLE h').op b)
    (O : U.toScheme.Opens) (V : U₂.toScheme.Opens) (h4 : V ≤ j₂ ⁻¹ᵁ O)
    (t : ((laurentOn L₀ U).piece d).val.obj (op O)) (hV' : U₂.ι ''ᵁ V ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O)) :
    φ.val.app (op V) (pullbackSection j₂ ((laurentOn L₀ U).piece d) O V h4 t) =
      (tensorPowerModule T' L₀' d).val.map (homOfLE hV').op (P.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O)))
        (pullbackSection τ (tensorPowerModule T L₀ d) (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl t))
            := by
  subst hφ
  have hO : O ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ O) := (U.ι.preimage_image_eq O).ge
  have h5 : V ≤ (j₂ ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ O) := h4.trans (j₂.preimage_mono hO)
  have h6 : V ≤ (U₂.ι ≫ τ) ⁻¹ᵁ (U.ι ''ᵁ O) := hj₂ι ▸ h5
  have h7 : V ≤ U₂.ι ⁻¹ᵁ (τ ⁻¹ᵁ (U.ι ''ᵁ O)) := h6
  have e1 := hA₁ O V h4 hO t
  have e2 := hA₂ (U.ι ''ᵁ O) O V hO h4 h5 t
  have e3 := hA₃ (U.ι ''ᵁ O) V h5 h6 t
  have e4 := hA₄ (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) V le_rfl h7 h6 t
  have e5 := hA₅ (τ ⁻¹ᵁ (U.ι ''ᵁ O)) V h7
    (pullbackSection τ (tensorPowerModule T L₀ d) (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl t)
  have e6 := hA₆ (τ ⁻¹ᵁ (U.ι ''ᵁ O)) V h7 hV' (P.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O)))
    (pullbackSection τ (tensorPowerModule T L₀ d) (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl t))
  exact (congrArg (A₆.val.app (op V)) ((congrArg (A₅.val.app (op V)) ((congrArg (A₄.val.app (op V))
    ((congrArg (A₃.val.app (op V)) ((congrArg (A₂.val.app (op V)) e1).trans e2)).trans e3)).trans
      e4)).trans e5)).trans e6

/-- **The restriction along `U₁ ⊆ U₂` followed by a transport along `c : ℒ^{⊗ n} ⟶ ℒ'^{⊗ n}`, on
a pulled-back section**, with both factors variables with their values as hypotheses: the
pullback of the restriction of a section `z` is carried to the restriction of `c z`. -/
theorem transportPiece_val_app_of_eq (L L' : T'.Modules) [Stacks.Ample.IsInvertibleModule T' L]
    [Stacks.Ample.IsInvertibleModule T' L'] (n : ℤ) {U₁ U₂ : T'.Opens} (hU : U₁ ≤ U₂)
    (cI : tensorPowerModule T' L n ⟶ tensorPowerModule T' L' n)
    (φ : (Scheme.Modules.pullback (T'.homOfLE hU)).obj ((laurentOn L U₂).piece n) ⟶
      (laurentOn L' U₁).piece n)
    (D₁ : (Scheme.Modules.pullback (T'.homOfLE hU)).obj ((laurentOn L U₂).piece n) ⟶
      (laurentOn L U₁).piece n)
    (D₂ : (laurentOn L U₁).piece n ⟶ (laurentOn L' U₁).piece n) (hφ : φ = D₁ ≫ D₂)
    (hD₁ : ∀ (O' : U₂.toScheme.Opens) (V : U₁.toScheme.Opens) (h4 : V ≤ T'.homOfLE hU ⁻¹ᵁ O')
      (t : ((laurentOn L U₂).piece n).val.obj (op O')) (hV : U₁.ι ''ᵁ V ≤ U₂.ι ''ᵁ O'),
      D₁.val.app (op V) (pullbackSection (T'.homOfLE hU) _ O' V h4 t) =
        (tensorPowerModule T' L n).val.map (homOfLE hV).op t)
    (hD₂ : ∀ (W : U₁.toScheme.Opens) (t : ((laurentOn L U₁).piece n).val.obj (op W)),
      D₂.val.app (op W) t = cI.val.app (op (U₁.ι ''ᵁ W)) t)
    (W₁ : U₂.toScheme.Opens) (W₀ : U₁.toScheme.Opens) (h : W₀ ≤ T'.homOfLE hU ⁻¹ᵁ W₁)
    (Z : T'.Opens) (hc : U₂.ι ''ᵁ W₁ ≤ Z) (hr : U₁.ι ''ᵁ W₀ ≤ Z)
    (z : (tensorPowerModule T' L n).val.obj (op Z)) :
    φ.val.app (op W₀) (pullbackSection (T'.homOfLE hU) ((laurentOn L U₂).piece n) W₁ W₀ h
      ((tensorPowerModule T' L n).val.map (homOfLE hc).op z)) =
      (tensorPowerModule T' L' n).val.map (homOfLE hr).op (cI.val.app (op Z) z) := by
  subst hφ
  have hV := image_le_image_of_le_preimage_homOfLE hU W₁ h
  have e1 := (hD₁ W₁ W₀ h _ hV).trans
    (AlgebraicGeometry.val_map_map (homOfLE hc).op (homOfLE hV).op z (homOfLE hr).op)
  have e2 := hD₂ W₀ ((tensorPowerModule T' L n).val.map (homOfLE hr).op z)
  have e3 := PresheafOfModules.naturality_apply cI.val (homOfLE hr).op z
  exact ((congrArg (D₂.val.app (op W₀)) e1).trans e2).trans e3

/-- **A comparison `ρ = P ≫ c` on a pulled-back section**: it is the restriction of `c (P b)`
for the pullback `b` of the section over the whole preimage. -/
theorem pullbackPiece_val_app_of_eq (τ : T' ⟶ T) (K₀ : T.Modules) (K₁' K₁ : T'.Modules)
    (P : (Scheme.Modules.pullback τ).obj K₀ ⟶ K₁') (cI : K₁' ⟶ K₁)
    (ρ : (Scheme.Modules.pullback τ).obj K₀ ⟶ K₁) (hρ : ρ = P ≫ cI)
    (Z : T.Opens) (V : T'.Opens) (h : V ≤ τ ⁻¹ᵁ Z) (b : K₀.val.obj (op Z)) :
    ρ.val.app (op V) (pullbackSection τ K₀ Z V h b) =
      K₁.val.map (homOfLE h).op (cI.val.app (op (τ ⁻¹ᵁ Z))
        (P.val.app (op (τ ⁻¹ᵁ Z)) (pullbackSection τ K₀ Z (τ ⁻¹ᵁ Z) le_rfl b))) := by
  subst hρ
  have e0 := (Stacks.Conormal.pullbackSection_restrict_target τ K₀ Z (τ ⁻¹ᵁ Z) V le_rfl h b).symm
  have e1 := PresheafOfModules.naturality_apply P.val (homOfLE h).op
    (pullbackSection τ K₀ Z (τ ⁻¹ᵁ Z) le_rfl b)
  have e2 := PresheafOfModules.naturality_apply cI.val (homOfLE h).op
    (P.val.app (op (τ ⁻¹ᵁ Z)) (pullbackSection τ K₀ Z (τ ⁻¹ᵁ Z) le_rfl b))
  exact ((congrArg (cI.val.app (op V)) ((congrArg (P.val.app (op V)) e0).trans e1)).trans e2)

/-- **The coherence of the identifications of the targets around the square, from the values
of the factors on pulled-back sections.**  Every factor of the two sides of the target hypothesis
of `AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq_of_factors` (for the square
`τ ≫ g = g' ≫ (U' ⊆ Usq) ≫ l` of sections `g`, `g'` of the opens `U ⊆ T`, `U' ⊆ T'`) is a variable,
with its value on pulled-back sections as a hypothesis; both sides carry a twice pulled-back
section `a` of `ℒ^{⊗ d}|_U` to the restriction of `c (P (τ^*a))`, so they agree
(`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection`). -/
theorem targetCoherence_of_values (τ : T' ⟶ T) (L₀ : T.Modules) [Stacks.Ample.IsInvertibleModule T
    L₀]
    (L₀' L₁ : T'.Modules) [Stacks.Ample.IsInvertibleModule T' L₀']
    [Stacks.Ample.IsInvertibleModule T' L₁] (d : ℤ)
    (U : T.Opens) (U' Usq : T'.Opens) (g : T ⟶ U.toScheme) (hg : g ≫ U.ι = 𝟙 T)
    (g' : T' ⟶ U'.toScheme) (hg' : g' ≫ U'.ι = 𝟙 T') (hU' : U' ≤ Usq)
    (l : Usq.toScheme ⟶ U.toScheme) (hl : l ≫ U.ι = Usq.ι ≫ τ)
    (hk : τ ≫ g = g' ≫ T'.homOfLE hU' ≫ l)
    (E₁ : (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback τ).obj ((laurentOn L₀ U).piece d) ⟶
      (Scheme.Modules.pullback (τ ≫ g)).obj ((laurentOn L₀ U).piece d))
    (hE₁ : ∀ (O : U.toScheme.Opens) (W : T.Opens) (V : T'.Opens) (hg : W ≤ g ⁻¹ᵁ O)
      (hf : V ≤ τ ⁻¹ᵁ W) (h : V ≤ (τ ≫ g) ⁻¹ᵁ O) (a : ((laurentOn L₀ U).piece d).val.obj (op O)),
      E₁.val.app (op V) (pullbackSection τ ((Scheme.Modules.pullback g).obj ((laurentOn L₀
          U).piece d))
        W V hf (pullbackSection g ((laurentOn L₀ U).piece d) O W hg a)) =
        pullbackSection (τ ≫ g) ((laurentOn L₀ U).piece d) O V h a)
    (E₂ : (Scheme.Modules.pullback (τ ≫ g)).obj ((laurentOn L₀ U).piece d) ⟶
      (Scheme.Modules.pullback (g' ≫ T'.homOfLE hU' ≫ l)).obj ((laurentOn L₀ U).piece d))
    (hE₂ : ∀ (O : U.toScheme.Opens) (V : T'.Opens) (hf : V ≤ (τ ≫ g) ⁻¹ᵁ O)
      (hg : V ≤ (g' ≫ T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) (a : ((laurentOn L₀ U).piece d).val.obj (op O)),
      E₂.val.app (op V) (pullbackSection (τ ≫ g) ((laurentOn L₀ U).piece d) O V hf a) =
        pullbackSection (g' ≫ T'.homOfLE hU' ≫ l) ((laurentOn L₀ U).piece d) O V hg a)
    (E₃ : (Scheme.Modules.pullback (g' ≫ T'.homOfLE hU' ≫ l)).obj ((laurentOn L₀ U).piece d) ⟶
      (Scheme.Modules.pullback (T'.homOfLE hU' ≫ l) ⋙ Scheme.Modules.pullback g').obj
        ((laurentOn L₀ U).piece d))
    (hE₃ : ∀ (O : U.toScheme.Opens) (W₀ : U'.toScheme.Opens) (V : T'.Opens)
      (hg : W₀ ≤ (T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) (hf : V ≤ g' ⁻¹ᵁ W₀)
      (h : V ≤ (g' ≫ T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) (a : ((laurentOn L₀ U).piece d).val.obj (op O)),
      E₃.val.app (op V) (pullbackSection (g' ≫ T'.homOfLE hU' ≫ l) ((laurentOn L₀ U).piece d) O V
          h a) =
        pullbackSection g' ((Scheme.Modules.pullback (T'.homOfLE hU' ≫ l)).obj
          ((laurentOn L₀ U).piece d)) W₀ V hf
          (pullbackSection (T'.homOfLE hU' ≫ l) ((laurentOn L₀ U).piece d) O W₀ hg a))
    (F₄ : (Scheme.Modules.pullback (T'.homOfLE hU' ≫ l)).obj ((laurentOn L₀ U).piece d) ⟶
      (Scheme.Modules.pullback l ⋙ Scheme.Modules.pullback (T'.homOfLE hU')).obj
        ((laurentOn L₀ U).piece d))
    (hF₄ : ∀ (O : U.toScheme.Opens) (W₁ : Usq.toScheme.Opens) (W₀ : U'.toScheme.Opens)
      (hg : W₁ ≤ l ⁻¹ᵁ O) (hf : W₀ ≤ T'.homOfLE hU' ⁻¹ᵁ W₁) (h : W₀ ≤ (T'.homOfLE hU' ≫ l) ⁻¹ᵁ O)
      (a : ((laurentOn L₀ U).piece d).val.obj (op O)),
      F₄.val.app (op W₀) (pullbackSection (T'.homOfLE hU' ≫ l) ((laurentOn L₀ U).piece d) O W₀ h
          a) =
        pullbackSection (T'.homOfLE hU') ((Scheme.Modules.pullback l).obj ((laurentOn L₀ U).piece
            d))
          W₁ W₀ hf (pullbackSection l ((laurentOn L₀ U).piece d) O W₁ hg a))
    (P : (Scheme.Modules.pullback τ).obj (tensorPowerModule T L₀ d) ⟶ tensorPowerModule T' L₀' d)
    (cI : tensorPowerModule T' L₀' d ⟶ tensorPowerModule T' L₁ d)
    (Ch : (Scheme.Modules.pullback l).obj ((laurentOn L₀ U).piece d) ⟶ (laurentOn L₀' Usq).piece d)
    (hCh : ∀ (O : U.toScheme.Opens) (hc : Usq.ι ''ᵁ (l ⁻¹ᵁ O) ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O))
      (a : ((laurentOn L₀ U).piece d).val.obj (op O)),
      Ch.val.app (op (l ⁻¹ᵁ O)) (pullbackSection l ((laurentOn L₀ U).piece d) O (l ⁻¹ᵁ O) le_rfl
          a) =
        (tensorPowerModule T' L₀' d).val.map (homOfLE hc).op
          (P.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O))) (pullbackSection τ (tensorPowerModule T L₀ d)
            (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl a)))
    (Dh : (Scheme.Modules.pullback (T'.homOfLE hU')).obj ((laurentOn L₀' Usq).piece d) ⟶
      (laurentOn L₁ U').piece d)
    (hDh : ∀ (W₁ : Usq.toScheme.Opens) (W₀ : U'.toScheme.Opens) (h : W₀ ≤ T'.homOfLE hU' ⁻¹ᵁ W₁)
      (Z : T'.Opens) (hc : Usq.ι ''ᵁ W₁ ≤ Z) (hr : U'.ι ''ᵁ W₀ ≤ Z)
      (z : (tensorPowerModule T' L₀' d).val.obj (op Z)),
      Dh.val.app (op W₀) (pullbackSection (T'.homOfLE hU') ((laurentOn L₀' Usq).piece d) W₁ W₀ h
        ((tensorPowerModule T' L₀' d).val.map (homOfLE hc).op z)) =
        (tensorPowerModule T' L₁ d).val.map (homOfLE hr).op (cI.val.app (op Z) z))
    (lam₁ : (Scheme.Modules.pullback g').obj ((laurentOn L₁ U').piece d) ⟶ tensorPowerModule T' L₁
        d)
    (hlam₁ : ∀ (W₀ : U'.toScheme.Opens) (V : T'.Opens) (h : V ≤ g' ⁻¹ᵁ W₀) (hV : V ≤ U'.ι ''ᵁ W₀)
      (t : ((laurentOn L₁ U').piece d).val.obj (op W₀)),
      lam₁.val.app (op V) (pullbackSection g' ((laurentOn L₁ U').piece d) W₀ V h t) =
        (tensorPowerModule T' L₁ d).val.map (homOfLE hV).op t)
    (lam₀ : (Scheme.Modules.pullback g).obj ((laurentOn L₀ U).piece d) ⟶ tensorPowerModule T L₀ d)
    (hlam₀ : ∀ (O : U.toScheme.Opens) (W : T.Opens) (h : W ≤ g ⁻¹ᵁ O) (hW : W ≤ U.ι ''ᵁ O)
      (a : ((laurentOn L₀ U).piece d).val.obj (op O)),
      lam₀.val.app (op W) (pullbackSection g ((laurentOn L₀ U).piece d) O W h a) =
        (tensorPowerModule T L₀ d).val.map (homOfLE hW).op a)
    (ρ : (Scheme.Modules.pullback τ).obj (tensorPowerModule T L₀ d) ⟶ tensorPowerModule T' L₁ d)
    (hρ : ∀ (Z : T.Opens) (V : T'.Opens) (h : V ≤ τ ⁻¹ᵁ Z)
      (b : (tensorPowerModule T L₀ d).val.obj (op Z)),
      ρ.val.app (op V) (pullbackSection τ (tensorPowerModule T L₀ d) Z V h b) =
        (tensorPowerModule T' L₁ d).val.map (homOfLE h).op (cI.val.app (op (τ ⁻¹ᵁ Z))
          (P.val.app (op (τ ⁻¹ᵁ Z)) (pullbackSection τ (tensorPowerModule T L₀ d) Z (τ ⁻¹ᵁ Z)
              le_rfl b)))) :
    (E₁ ≫ E₂ ≫ E₃ ≫ (Scheme.Modules.pullback g').map F₄) ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback (T'.homOfLE hU')).map Ch) ≫
        (Scheme.Modules.pullback g').map Dh ≫ lam₁ =
      (Scheme.Modules.pullback τ).map lam₀ ≫ ρ := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection τ g (fun O a => ?_)
  -- the opens
  have hW : g ⁻¹ᵁ O ≤ U.ι ''ᵁ O := fun x hx =>
    ⟨g.base x, hx, congrArg (fun f : T ⟶ T => f.base x) hg⟩
  have hV : τ ⁻¹ᵁ (g ⁻¹ᵁ O) ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O) := τ.preimage_mono hW
  have h1 : τ ⁻¹ᵁ (g ⁻¹ᵁ O) ≤ (τ ≫ g) ⁻¹ᵁ O := le_rfl
  have h2 : τ ⁻¹ᵁ (g ⁻¹ᵁ O) ≤ (g' ≫ T'.homOfLE hU' ≫ l) ⁻¹ᵁ O := by
    rw [← hk]; exact h1
  have h3 : τ ⁻¹ᵁ (g ⁻¹ᵁ O) ≤ g' ⁻¹ᵁ ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) := h2
  have h4 : (T'.homOfLE hU' ≫ l) ⁻¹ᵁ O ≤ T'.homOfLE hU' ⁻¹ᵁ (l ⁻¹ᵁ O) := le_rfl
  have hc : Usq.ι ''ᵁ (l ⁻¹ᵁ O) ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨l.base x, hx, congrArg (fun f : Usq.toScheme ⟶ T => f.base x) hl⟩
  have hr : U'.ι ''ᵁ ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨l.base ((T'.homOfLE hU').base x), hx, ?_⟩
    have e1 := congrArg (fun f : Usq.toScheme ⟶ T => f.base ((T'.homOfLE hU').base x)) hl
    have e2 := congrArg (fun f : U'.toScheme ⟶ T' => τ.base (f.base x)) (Scheme.homOfLE_ι T' hU')
    exact e1.trans e2
  have hV' : τ ⁻¹ᵁ (g ⁻¹ᵁ O) ≤ U'.ι ''ᵁ ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) := fun x hx =>
    ⟨g'.base x, h3 hx, congrArg (fun f : T' ⟶ T' => f.base x) hg'⟩
  -- the right side
  have r1 := Scheme.Modules.pullbackSection_naturality τ lam₀ (g ⁻¹ᵁ O) (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) le_rfl
    (pullbackSection g ((laurentOn L₀ U).piece d) O (g ⁻¹ᵁ O) le_rfl a)
  have r2 := hlam₀ O (g ⁻¹ᵁ O) le_rfl hW a
  have r3 := (Stacks.Conormal.pullbackSection_restrict_source τ
    (tensorPowerModule T L₀ d) (U.ι ''ᵁ O) (g ⁻¹ᵁ O) hW (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) le_rfl a).symm
  have r4 := hρ (U.ι ''ᵁ O) (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) hV a
  -- the left side
  have l1 := hE₁ O (g ⁻¹ᵁ O) (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) le_rfl le_rfl h1 a
  have l2 := hE₂ O (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) h1 h2 a
  have l3 := hE₃ O ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) le_rfl h3 h2 a
  have l4 := Scheme.Modules.pullbackSection_naturality g' F₄ ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O)
    (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) h3
    (pullbackSection (T'.homOfLE hU' ≫ l) ((laurentOn L₀ U).piece d) O _ le_rfl a)
  have l4' := hF₄ O (l ⁻¹ᵁ O) ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) le_rfl h4 le_rfl a
  have l5 := Scheme.Modules.pullbackSection_naturality g' ((Scheme.Modules.pullback (T'.homOfLE
      hU')).map Ch)
    ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) h3
    (pullbackSection (T'.homOfLE hU') ((Scheme.Modules.pullback l).obj ((laurentOn L₀ U).piece d))
      (l ⁻¹ᵁ O) _ h4 (pullbackSection l ((laurentOn L₀ U).piece d) O (l ⁻¹ᵁ O) le_rfl a))
  have l5' := Scheme.Modules.pullbackSection_naturality (T'.homOfLE hU') Ch (l ⁻¹ᵁ O)
    ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) h4 (pullbackSection l ((laurentOn L₀ U).piece d) O (l ⁻¹ᵁ O)
        le_rfl a)
  have l5'' := hCh O hc a
  have l6 := Scheme.Modules.pullbackSection_naturality g' Dh ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O)
    (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) h3
    (pullbackSection (T'.homOfLE hU') ((laurentOn L₀' Usq).piece d) (l ⁻¹ᵁ O) _ h4
      ((tensorPowerModule T' L₀' d).val.map (homOfLE hc).op
        (P.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O))) (pullbackSection τ (tensorPowerModule T L₀ d)
          (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl a))))
  have l6' := hDh (l ⁻¹ᵁ O) ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) h4 _ hc hr
    (P.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O))) (pullbackSection τ (tensorPowerModule T L₀ d)
      (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl a))
  have l7 := hlam₁ ((T'.homOfLE hU' ≫ l) ⁻¹ᵁ O) (τ ⁻¹ᵁ (g ⁻¹ᵁ O)) h3 hV'
    ((tensorPowerModule T' L₁ d).val.map (homOfLE hr).op (cI.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O)))
      (P.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O))) (pullbackSection τ (tensorPowerModule T L₀ d)
        (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl a))))
  have l8 := AlgebraicGeometry.val_map_map (homOfLE hr).op (homOfLE hV').op
    (cI.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O))) (P.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O)))
      (pullbackSection τ (tensorPowerModule T L₀ d) (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl a)))
    (homOfLE hV).op
  unfold Stacks.AlgebraicGeometry.ModuleLimits.doublePullbackSection
  simp only [Stacks.AlgebraicGeometry.ModuleLimits.comp_val_app]
  rw [r1, r2, r3, r4, l1, l2, l3, l4, l4']
  refine (congrArg (lam₁.val.app (op (τ ⁻¹ᵁ (g ⁻¹ᵁ O))))
    (congrArg (((Scheme.Modules.pullback g').map Dh).val.app (op (τ ⁻¹ᵁ (g ⁻¹ᵁ O))))
      (l5.trans (congrArg (pullbackSection g' _ _ _ h3)
        (l5'.trans (congrArg (pullbackSection _ _ _ _ h4) l5'')))))).trans ?_
  rw [l6, l6', l7, l8]

/-- **The target coherence of the square of the scheme factor of the chart maps of `θ`**
(Stacks 0D2Z, 01O9): the hypothesis `hTgt` of
`AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq_of_factors`, for the square
`τ ≫ g = g' ≫ (U' ⊆ Usq) ≫ l` of sections `g`, `g'` of the opens `U ⊆ T`, `U' ⊆ T'`.  The factors
are variables with their values as equations: `Ch` is the degree-`d` component of
`…squareChainIso` assembled from the restrictions along `Usq ⊆ U₂ ⊆ U_χ` and a target
identification `S₄` along `j₂` in the shape of `…thetaTargetPieceIso` (with the comparison `I` of
the tensor powers), `Dh` the restriction along `U' ⊆ Usq` followed by a transport `D₂` along
`c : ℒ'^{⊗ d} ⟶ ℒ₁^{⊗ d}`, `λ₀`, `λ₁` the identifications `g^*(ℒ^{⊗ d}|_U) ≅ ℒ^{⊗ d}` (the shape of
`…GradedPowerMap.laurentOnSectionPieceIso`) and `ρ = I ≫ c`. -/
theorem chartScheme_target_coherence (τ : T' ⟶ T) (L₀ : T.Modules)
    [Stacks.Ample.IsInvertibleModule T L₀] (L₀' L₁ : T'.Modules)
    [Stacks.Ample.IsInvertibleModule T' L₀'] [Stacks.Ample.IsInvertibleModule T' L₁] (d : ℤ)
    (I : (Scheme.Modules.pullback τ).obj (tensorPowerModule T L₀ d) ≅ tensorPowerModule T' L₀' d)
    (cI : tensorPowerModule T' L₀' d ⟶ tensorPowerModule T' L₁ d)
    (U : T.Opens) (U' Usq U₂ Uχ : T'.Opens) (g : T ⟶ U.toScheme) (hg : g ≫ U.ι = 𝟙 T)
    (g' : T' ⟶ U'.toScheme) (hg' : g' ≫ U'.ι = 𝟙 T') (hU' : U' ≤ Usq)
    (l : Usq.toScheme ⟶ U.toScheme) (hl : l ≫ U.ι = Usq.ι ≫ τ)
    (hk : τ ≫ g = g' ≫ T'.homOfLE hU' ≫ l)
    (hsq₂ : Usq ≤ U₂) (h₂χ : U₂ ≤ Uχ) (hsqχ : Usq ≤ Uχ)
    (hkk : T'.homOfLE hsq₂ ≫ T'.homOfLE h₂χ = T'.homOfLE hsqχ)
    (j₂ : U₂.toScheme ⟶ U.toScheme) (hj₂ : T'.homOfLE hsq₂ ≫ j₂ = l) (hj₂ι : j₂ ≫ U.ι = U₂.ι ≫ τ)
    (S₁ : pullbackGradedAlgebra (T'.homOfLE hsqχ).toLRSHom.toShHom (laurentOn L₀' Uχ) ≅
      laurentOn L₀' Usq)
    (S₂ : pullbackGradedAlgebra (T'.homOfLE h₂χ).toLRSHom.toShHom (laurentOn L₀' Uχ) ≅
      laurentOn L₀' U₂)
    (S₄ : pullbackGradedAlgebra j₂.toLRSHom.toShHom (laurentOn L₀ U) ≅ laurentOn L₀' U₂)
    (hS₁ : S₁.hom.app d = (laurentOnHomOfLEPieceIso L₀' hsqχ d).hom)
    (hS₂ : S₂.inv.app d = (laurentOnHomOfLEPieceIso L₀' h₂χ d).inv)
    (hS₄ : S₄.hom.app d =
      (Scheme.Modules.pullback j₂).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app (tensorPowerModule T L₀ d)) ≫
        (Scheme.Modules.pullbackComp j₂ U.ι).hom.app (tensorPowerModule T L₀ d) ≫
        (Scheme.Modules.pullbackCongr hj₂ι).hom.app (tensorPowerModule T L₀ d) ≫
        (Scheme.Modules.pullbackComp U₂.ι τ).inv.app (tensorPowerModule T L₀ d) ≫
        (Scheme.Modules.pullback U₂.ι).map I.hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback U₂.ι).inv.app (tensorPowerModule T' L₀' d))
    (Ch : (Scheme.Modules.pullback l).obj ((laurentOn L₀ U).piece d) ⟶ (laurentOn L₀' Usq).piece d)
    (hCh : Ch = (squareChainIso hkk hj₂ S₁ S₂ S₄).hom.app d)
    (D₂ : (laurentOn L₀' U').piece d ⟶ (laurentOn L₁ U').piece d)
    (hD₂ : ∀ (W : U'.toScheme.Opens) (t : ((laurentOn L₀' U').piece d).val.obj (op W)),
      D₂.val.app (op W) t = cI.val.app (op (U'.ι ''ᵁ W)) t)
    (Dh : (Scheme.Modules.pullback (T'.homOfLE hU')).obj ((laurentOn L₀' Usq).piece d) ⟶
      (laurentOn L₁ U').piece d)
    (hDh : Dh = (laurentOnHomOfLEPieceIso L₀' hU' d).hom ≫ D₂)
    (lam₀ : (Scheme.Modules.pullback g).obj ((laurentOn L₀ U).piece d) ⟶ tensorPowerModule T L₀ d)
    (hlam₀ : lam₀ = (Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app (tensorPowerModule T L₀ d)) ≫
      (Scheme.Modules.pullbackComp g U.ι).hom.app (tensorPowerModule T L₀ d) ≫
      (Scheme.Modules.pullbackCongr hg).hom.app (tensorPowerModule T L₀ d) ≫
      (Scheme.Modules.pullbackId T).hom.app (tensorPowerModule T L₀ d))
    (lam₁ : (Scheme.Modules.pullback g').obj ((laurentOn L₁ U').piece d) ⟶ tensorPowerModule T' L₁
        d)
    (hlam₁ : lam₁ = (Scheme.Modules.pullback g').map
        ((Scheme.Modules.restrictFunctorIsoPullback U'.ι).hom.app (tensorPowerModule T' L₁ d)) ≫
      (Scheme.Modules.pullbackComp g' U'.ι).hom.app (tensorPowerModule T' L₁ d) ≫
      (Scheme.Modules.pullbackCongr hg').hom.app (tensorPowerModule T' L₁ d) ≫
      (Scheme.Modules.pullbackId T').hom.app (tensorPowerModule T' L₁ d))
    (ρ : (Scheme.Modules.pullback τ).obj (tensorPowerModule T L₀ d) ⟶ tensorPowerModule T' L₁ d)
    (hρ : ρ = I.hom ≫ cI) :
    ((Scheme.Modules.pullbackComp τ g).hom.app ((laurentOn L₀ U).piece d) ≫
        (Scheme.Modules.pullbackCongr hk).hom.app ((laurentOn L₀ U).piece d) ≫
        (Scheme.Modules.pullbackComp g' (T'.homOfLE hU' ≫ l)).inv.app ((laurentOn L₀ U).piece d) ≫
        (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullbackComp (T'.homOfLE hU') l).inv.app ((laurentOn L₀ U).piece d))) ≫
      (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback (T'.homOfLE hU')).map Ch) ≫
      (Scheme.Modules.pullback g').map Dh ≫ lam₁ =
    (Scheme.Modules.pullback τ).map lam₀ ≫ ρ := by
  -- the value of `Ch` on a pulled-back section
  have hChain : Ch = (Scheme.Modules.pullbackCongr hj₂).inv.app ((laurentOn L₀ U).piece d) ≫
      (Scheme.Modules.pullbackComp (T'.homOfLE hsq₂) j₂).inv.app ((laurentOn L₀ U).piece d) ≫
      (Scheme.Modules.pullback (T'.homOfLE hsq₂)).map (S₄.hom.app d) ≫
      (Scheme.Modules.pullback (T'.homOfLE hsq₂)).map (laurentOnHomOfLEPieceIso L₀' h₂χ d).inv ≫
      (Scheme.Modules.pullbackComp (T'.homOfLE hsq₂) (T'.homOfLE h₂χ)).hom.app
        ((laurentOn L₀' Uχ).piece d) ≫
      (Scheme.Modules.pullbackCongr hkk).hom.app ((laurentOn L₀' Uχ).piece d) ≫
      (laurentOnHomOfLEPieceIso L₀' hsqχ d).hom := by
    refine hCh.trans ((squareChainIso_hom_app hkk hj₂ S₁ S₂ S₄ d _ hS₁ _ hS₂ _ rfl).trans ?_)
    exact congrArg (fun m => (Scheme.Modules.pullbackCongr hj₂).inv.app ((laurentOn L₀ U).piece d) ≫
      (Scheme.Modules.pullbackComp (T'.homOfLE hsq₂) j₂).inv.app ((laurentOn L₀ U).piece d) ≫ m)
      ((congrArg (fun m => m ≫ (Scheme.Modules.pullbackComp (T'.homOfLE hsq₂) (T'.homOfLE
          h₂χ)).hom.app
        ((laurentOn L₀' Uχ).piece d) ≫
        (Scheme.Modules.pullbackCongr hkk).hom.app ((laurentOn L₀' Uχ).piece d) ≫
        (laurentOnHomOfLEPieceIso L₀' hsqχ d).hom)
        ((Scheme.Modules.pullback (T'.homOfLE hsq₂)).map_comp (S₄.hom.app d)
          (laurentOnHomOfLEPieceIso L₀' h₂χ d).inv)).trans (Category.assoc _ _ _))
  have hS₄v : ∀ (O : U.toScheme.Opens) (V : U₂.toScheme.Opens) (h4 : V ≤ j₂ ⁻¹ᵁ O)
      (t : ((laurentOn L₀ U).piece d).val.obj (op O)) (hV' : U₂.ι ''ᵁ V ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O)),
      (S₄.hom.app d).val.app (op V) (pullbackSection j₂ ((laurentOn L₀ U).piece d) O V h4 t) =
        (tensorPowerModule T' L₀' d).val.map (homOfLE hV').op (I.hom.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ
            O)))
          (pullbackSection τ (tensorPowerModule T L₀ d) (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl t))
              :=
    thetaTargetChain_val_app_of_eq τ L₀ L₀' d U U₂ j₂ hj₂ι I.hom (S₄.hom.app d) _ _ _ _ _ _ hS₄
      (fun O V h hO t => (Scheme.Modules.pullbackSection_naturality j₂
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app (tensorPowerModule T L₀ d)) O V h
          t).trans (congrArg (pullbackSection j₂ _ O V h)
            (restrictFunctorIsoPullback_hom_val_app U.ι (tensorPowerModule T L₀ d) O hO t)))
      (fun U₀ W V hg₀ hf h a => Scheme.Modules.pullbackSection_comp j₂ U.ι _ U₀ W V hg₀ hf h a)
      (fun U₀ V hf hg₀ a => Scheme.Modules.pullbackSection_congr hj₂ι _ U₀ V hf hg₀ a)
      (fun U₀ W₀ V hg₀ hf h a =>
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection U₂.ι τ _ U₀
            W₀ V
          hg₀ hf h a)
      (fun W₀ V h x => Scheme.Modules.pullbackSection_naturality U₂.ι I.hom W₀ V h x)
      (fun W₀ V h h' b => Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection U₂.ι _ W₀
          V h h' b)
  have hChv : ∀ (O : U.toScheme.Opens) (hc : Usq.ι ''ᵁ (l ⁻¹ᵁ O) ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O))
      (a : ((laurentOn L₀ U).piece d).val.obj (op O)),
      Ch.val.app (op (l ⁻¹ᵁ O)) (pullbackSection l ((laurentOn L₀ U).piece d) O (l ⁻¹ᵁ O) le_rfl
          a) =
        (tensorPowerModule T' L₀' d).val.map (homOfLE hc).op
          (I.hom.val.app (op (τ ⁻¹ᵁ (U.ι ''ᵁ O))) (pullbackSection τ (tensorPowerModule T L₀ d)
            (U.ι ''ᵁ O) (τ ⁻¹ᵁ (U.ι ''ᵁ O)) le_rfl a)) := by
    intro O hc a
    have hV3 : U₂.ι ''ᵁ (j₂ ⁻¹ᵁ O) ≤ τ ⁻¹ᵁ (U.ι ''ᵁ O) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨j₂.base x, hx, congrArg (fun f : U₂.toScheme ⟶ T => f.base x) hj₂ι⟩
    have h4 : j₂ ⁻¹ᵁ O ≤ T'.homOfLE h₂χ ⁻¹ᵁ (Uχ.ι ⁻¹ᵁ (τ ⁻¹ᵁ (U.ι ''ᵁ O))) := by
      intro x hx
      have e1 := congrArg (fun f : U₂.toScheme ⟶ T' => f.base x) (Scheme.homOfLE_ι T' h₂χ)
      exact ⟨j₂.base x, hx, (congrArg (fun f : U₂.toScheme ⟶ T => f.base x) hj₂ι).trans
        (congrArg τ.base e1.symm)⟩
    exact squareChain_val_app_of_eq L₀' d Usq U₂ Uχ hsq₂ h₂χ hsqχ hkk l j₂ hj₂
      ((laurentOn L₀ U).piece d) (laurentOnHomOfLEPieceIso L₀' h₂χ d)
      (fun O' V h4 t _ => laurentOnHomOfLEPieceIso_hom_pullbackSection L₀' h₂χ d O' V h4 t)
      (laurentOnHomOfLEPieceIso L₀' hsqχ d)
      (fun O' V h4 t _ => laurentOnHomOfLEPieceIso_hom_pullbackSection L₀' hsqχ d O' V h4 t)
      (S₄.hom.app d) _ (fun O V hf hg₀ a => pullbackSection_congr_inv hj₂ _ O V hf hg₀ a) _
      (fun O W₀ V hg₀ hf h a =>
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
          (T'.homOfLE hsq₂) j₂ _ O W₀ V hg₀ hf h a) _
      (fun U₀ W V hg₀ hf h a => Scheme.Modules.pullbackSection_comp (T'.homOfLE hsq₂)
        (T'.homOfLE h₂χ) _ U₀ W V hg₀ hf h a) _
      (fun U₀ V hf hg₀ a => Scheme.Modules.pullbackSection_congr hkk _ U₀ V hf hg₀ a)
      Ch hChain O a _ _ hV3 (hS₄v O (j₂ ⁻¹ᵁ O) le_rfl a hV3) h4 hc
  exact targetCoherence_of_values τ L₀ L₀' L₁ d U U' Usq g hg g' hg' hU' l hl hk _
    (fun O W V hg₀ hf h a => Scheme.Modules.pullbackSection_comp τ g _ O W V hg₀ hf h a) _
    (fun O V hf hg₀ a => Scheme.Modules.pullbackSection_congr hk _ O V hf hg₀ a) _
    (fun O W₀ V hg₀ hf h a =>
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection g'
        (T'.homOfLE hU' ≫ l) _ O W₀ V hg₀ hf h a) _
    (fun O W₁ W₀ hg₀ hf h a =>
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
        (T'.homOfLE hU') l _ O W₁ W₀ hg₀ hf h a)
    I.hom cI Ch hChv Dh
    (transportPiece_val_app_of_eq L₀' L₁ d hU' cI Dh _ D₂ hDh
      (fun O' V h4 t _ => laurentOnHomOfLEPieceIso_hom_pullbackSection L₀' hU' d O' V h4 t) hD₂)
    lam₁
    (fun W₀ V h hV t => by
      subst hlam₁
      exact sectionPieceChain_val_app_pullbackSection g' hg' _ W₀ V h hV t)
    lam₀
    (fun O W h hW a => by
      subst hlam₀
      exact sectionPieceChain_val_app_pullbackSection g hg _ O W h hW a)
    ρ (pullbackPiece_val_app_of_eq τ _ _ _ I.hom cI ρ hρ)

end TargetCoherence

end AlgebraicGeometry.Space

end

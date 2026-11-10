module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.OverBase

/-!
# The local datum of the relative `θ` of Stacks Tag 01O9 over an affine open of the base

Let `(S, 𝒜, f : T ⟶ S, ℒ, ψ)` be the data of [Stacks, Tag 01O8] and
`r = r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` the morphism of [Stacks, Tag 01O9]
(`…GradedPowerMap.globalMorphism`). Over the chart of [Stacks, Tag 01NQ] attached to an affine open
`V` of the base, this file builds the local datum of the pushforward form
`𝒪_{Proj_S(𝒜)}(n) ⟶ r_*(ℒ^{⊗ n}|_{U(ψ)})` of `θ`: [Stacks, Tag 01NK]'s `θ` for the induced datum
`…GradedPowerMap.affineDatum V`, read through [Stacks, Tag 01NR]'s chart identification on the
source and through `chartTargetHom` on the target.

The target comparison is available because `r` is a morphism over `S`
(`…GradedPowerMap.globalMorphism_comp_toBase`): the inverse image under `r` of the chart image over
`V` is then the piece of `U(ψ)` over `V`, so the restriction of `r_*(ℒ^{⊗ n}|_{U(ψ)})` to the chart
is the direct image along the leg out of that piece (`isIso_baseChange`).

## Main definitions

* `…GradedPowerMap.chartBaseChangeIso`: `(r_* K)|_{chart} ≅ (leg)_*(K|_{piece})`.
* `…GradedPowerMap.chartTargetHom`: the target comparison over the chart.
* `…GradedPowerMap.thetaLoc`: **the local datum over the chart of `V`.**
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (pushTheta)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

/-! ### Restricting a direct image along an open immersion of the target -/

section BaseChange

variable {X' Y Z Y' : Scheme.{u}} (c : Z ⟶ X') [IsOpenImmersion c] (r : Y ⟶ X')
  (j : Y' ⟶ Y) [IsOpenImmersion j] (pl : Y' ⟶ Z) (h : pl ≫ c = j ≫ r) (K : Y.Modules)

/-- The morphism `r_* K ⟶ c_* (pl_* (K|_{Y'}))` adjoint to the restriction to the open `Y'`:
`r_*` of the unit of `j^♭ ⊣ j_*`, read through `pl ≫ c = j ≫ r`. -/
def baseChangeAdj :
    (Scheme.Modules.pushforward r).obj K ⟶
      (Scheme.Modules.pushforward c).obj
        ((Scheme.Modules.pushforward pl).obj (K.restrict j)) :=
  (Scheme.Modules.pushforward r).map ((Scheme.Modules.restrictAdjunction j).unit.app K) ≫
    (Scheme.Modules.pushforwardComp j r).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr h.symm).hom.app _ ≫
    (Scheme.Modules.pushforwardComp pl c).inv.app _

/-- **The base change morphism** `(r_* K)|_{Z} ⟶ pl_* (K|_{Y'})` for a square `pl ≫ c = j ≫ r`
with `c` and `j` open immersions. -/
def baseChange :
    ((Scheme.Modules.pushforward r).obj K).restrict c ⟶
      (Scheme.Modules.pushforward pl).obj (K.restrict j) :=
  (Scheme.Modules.restrictFunctor c).map (baseChangeAdj c r j pl h K) ≫
    (Scheme.Modules.restrictAdjunction c).counit.app _

include h in
/-- The image under `j` of the preimage under `pl` of an open `W` of `Z` is contained in the
preimage under `r` of the image of `W` under `c`. -/
theorem image_preimage_le_preimage_image (W : Z.Opens) :
    j ''ᵁ (pl ⁻¹ᵁ W) ≤ r ⁻¹ᵁ (c ''ᵁ W) := by
  rintro _ ⟨y, hy, rfl⟩
  change (j ≫ r).base y ∈ c ''ᵁ W
  rw [← h]
  exact ⟨pl.base y, hy, rfl⟩

omit [IsOpenImmersion j] in
/-- The component of a restriction along an open immersion is the component at the image. -/
theorem restrictFunctor_map_app' {X₁ X₂ : Scheme.{u}} (f : X₁ ⟶ X₂) [IsOpenImmersion f]
    {M N : X₂.Modules} (φ : M ⟶ N) (U : X₁.Opens) :
    ((Scheme.Modules.restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U) := rfl

/-- **The base change morphism is a restriction map on sections.** -/
theorem baseChange_app (W : Z.Opens) :
    (baseChange c r j pl h K).app W
      = K.presheaf.map (homOfLE (image_preimage_le_preimage_image c r j pl h W)).op := by
  simp only [baseChange, baseChangeAdj, Scheme.Modules.Hom.comp_app, restrictFunctor_map_app',
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.restrictAdjunction_counit_app_app]
  have key : ∀ {A B C D : (Y.Opens)ᵒᵖ} (h₁ : A ⟶ B) (h₂ : B ⟶ C) (h₃ : C ⟶ D) (h₄ : A ⟶ D),
      (K.presheaf.map h₁ ≫ K.presheaf.map h₂) ≫ K.presheaf.map h₃ = K.presheaf.map h₄ := by
    intros
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  exact key _ _ _ _


include h in
/-- Under the range condition the two opens of `baseChange_app` agree. -/
theorem image_preimage_eq_preimage_image (hr : r ⁻¹ᵁ c.opensRange ≤ j.opensRange)
    (W : Z.Opens) : j ''ᵁ (pl ⁻¹ᵁ W) = r ⁻¹ᵁ (c ''ᵁ W) := by
  refine le_antisymm (image_preimage_le_preimage_image c r j pl h W) ?_
  intro y hy
  obtain ⟨w, hw, hwy⟩ := hy
  obtain ⟨y', rfl⟩ := hr (show y ∈ r ⁻¹ᵁ c.opensRange from ⟨w, hwy⟩)
  refine ⟨y', ?_, rfl⟩
  have h1 : c.base (pl.base y') = c.base w := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact hwy.symm
  rw [← c.isOpenEmbedding.injective h1] at hw
  exact hw

/-- **Under the range condition the base change morphism is an isomorphism.** -/
theorem isIso_baseChange (hr : r ⁻¹ᵁ c.opensRange ≤ j.opensRange) :
    IsIso (baseChange c r j pl h K) := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W => ?_
  rw [baseChange_app, show homOfLE (image_preimage_le_preimage_image c r j pl h W)
      = eqToHom (image_preimage_eq_preimage_image c r j pl h hr W) from Subsingleton.elim _ _]
  exact (K.presheaf.mapIso
    (eqToIso (image_preimage_eq_preimage_image c r j pl h hr W)).op).isIso_hom

end BaseChange

/-! ### The local datum of the relative `θ` over an affine open of the base -/

namespace GradedPowerMap

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- `ℒ^{⊗ n}|_{U(ψ)}`, the degree-`n` piece of the target of `θ`. -/
abbrev powK (n : ℤ) : P.coveringOpen.toScheme.Modules :=
  (tensorPowerModule T P.L n).restrict P.coveringOpen.ι

/-- `(r_{ℒ,ψ})_*(ℒ^{⊗ n}|_{U(ψ)})` on `Proj_S(𝒜)`, the target of the pushforward form of `θ`. -/
abbrev pushK (n : ℤ) : (relativeProj A).scheme.Modules :=
  (Scheme.Modules.pushforward (P.globalMorphism (relativeProj A))).obj (P.powK n)

/-- The inverse image of the part of `Proj_S(𝒜)` over `V` under `r_{ℒ,ψ}` is the piece of `U(ψ)`
over `V`. This is `r_{ℒ,ψ}` lying over the base. -/
theorem preimage_chart_opensRange_le (V : S.Opens) (hV : IsAffineOpen V) :
    P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).chart V hV).opensRange
      ≤ (P.toBase ⁻¹ᵁ V).ι.opensRange := by
  have h1 : ((relativeProj A).chart V hV).opensRange = (relativeProj A).toBase ⁻¹ᵁ V := by
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact RelativeProjTwistGlue.chart_image_top _ V hV
  rw [h1, ← Scheme.Hom.comp_preimage, P.globalMorphism_comp_toBase, Scheme.Opens.opensRange_ι]

/-- The comparison of the restriction to the chart over `V` of `(r_{ℒ,ψ})_* (ℒ^{⊗ n}|_{U(ψ)})`
with the direct image along the leg out of the piece over `V`; an isomorphism. -/
def chartBaseChange (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (P.pushK n).restrict ((relativeProj A).chart V hV) ⟶
      (Scheme.Modules.pushforward (P.pieceLeg V hV)).obj
        ((P.powK n).restrict (P.toBase ⁻¹ᵁ V).ι) :=
  baseChange ((relativeProj A).chart V hV) (P.globalMorphism (relativeProj A))
    (P.toBase ⁻¹ᵁ V).ι (P.pieceLeg V hV) (P.pieceLeg_comp_chart (relativeProj A) ⟨V, hV⟩)
    (P.powK n)

/-- `chartBaseChange` as an isomorphism. -/
def chartBaseChangeIso (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (P.pushK n).restrict ((relativeProj A).chart V hV) ≅
      (Scheme.Modules.pushforward (P.pieceLeg V hV)).obj
        ((P.powK n).restrict (P.toBase ⁻¹ᵁ V).ι) :=
  @asIso _ _ _ _ (P.chartBaseChange V hV n)
    (isIso_baseChange _ _ _ _ _ _ (P.preimage_chart_opensRange_le V hV))

/-- The forward morphism of `chartBaseChangeIso` is `chartBaseChange`. -/
@[simp] theorem chartBaseChangeIso_hom (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (P.chartBaseChangeIso V hV n).hom = P.chartBaseChange V hV n := rfl

/-- The comparison `(ℒ^{⊗ n})|_{f^{-1}(V)} ≅ (ℒ|_{f^{-1}(V)})^{⊗ n}` of [Stacks, Tag 01CU]'s
powers with restriction to an open subscheme. -/
def restrictPowIso (V : S.Opens) (n : ℤ) :
    (tensorPowerModule T P.L n).restrict (f ⁻¹ᵁ V).ι ≅
      tensorPowerModule (f ⁻¹ᵁ V).toScheme ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫ intPullIso (f ⁻¹ᵁ V).ι P.L n

/-- The two routes from the covering open of the induced datum into `T`. -/
theorem pieceIso_ι_ι (V : S.Opens) (hV : IsAffineOpen V) :
    ((P.pieceIso V hV).hom ≫ ((P.affineDatum V).coveringOpen).ι) ≫ (f ⁻¹ᵁ V).ι
      = (P.toBase ⁻¹ᵁ V).ι ≫ P.coveringOpen.ι :=
  (Category.assoc _ _ _).trans (P.pieceIso_comp_ι V hV)

/-- The target of the induced datum's `θ`, restricted along the identification of the piece,
compared with `ℒ^{⊗ n}|_{U(ψ)}` restricted to the piece. -/
def pieceTargetHom (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    ((P.affineDatum V).laurentPiece n).restrict (P.pieceIso V hV).hom ⟶
      (P.powK n).restrict (P.toBase ⁻¹ᵁ V).ι :=
  ((Scheme.Modules.restrictFunctorComp (P.pieceIso V hV).hom
      ((P.affineDatum V).coveringOpen).ι).app _).inv ≫
    (Scheme.Modules.restrictFunctor
      ((P.pieceIso V hV).hom ≫ ((P.affineDatum V).coveringOpen).ι)).map
        (P.restrictPowIso V n).inv ≫
    ((Scheme.Modules.restrictFunctorComp
      ((P.pieceIso V hV).hom ≫ ((P.affineDatum V).coveringOpen).ι) (f ⁻¹ᵁ V).ι).app _).inv ≫
    ((Scheme.Modules.restrictFunctorCongr (P.pieceIso_ι_ι V hV)).app _).hom ≫
    ((Scheme.Modules.restrictFunctorComp (P.toBase ⁻¹ᵁ V).ι P.coveringOpen.ι).app _).hom

/-- The same comparison, in adjoint form along the identification of the piece. -/
def pieceTargetAdj (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (P.affineDatum V).laurentPiece n ⟶
      (Scheme.Modules.pushforward (P.pieceIso V hV).hom).obj
        ((P.powK n).restrict (P.toBase ⁻¹ᵁ V).ι) :=
  (Scheme.Modules.restrictAdjunction (P.pieceIso V hV).hom).homEquiv _ _
    (P.pieceTargetHom V hV n)

/-- **The target comparison over an affine open `V` of the base**: the target of
[Stacks, Tag 01NK]'s `θ` for the induced datum, in pushforward form, into the restriction to the
chart of `(r_{ℒ,ψ})_*(ℒ^{⊗ n}|_{U(ψ)})`. -/
def chartTargetHom (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (P.affineDatum V).pushLaurent n ⟶ (P.pushK n).restrict ((relativeProj A).chart V hV) :=
  (Scheme.Modules.pushforward (P.affineDatum V).glued).map (P.pieceTargetAdj V hV n) ≫
    (Scheme.Modules.pushforwardComp (P.pieceIso V hV).hom (P.affineDatum V).glued).hom.app _ ≫
    (P.chartBaseChangeIso V hV n).inv

/-- **The local datum of the pushforward form of the relative `θ` over an affine open `V` of the
base**: [Stacks, Tag 01NK]'s `θ` for the induced datum, read through the chart identification of
[Stacks, Tag 01NR] on the source and `chartTargetHom` on the target. -/
def thetaLoc (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    Scheme.Modules.restrict ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece n)
        ((relativeProj A).chart V hV) ⟶
      (P.pushK n).restrict ((relativeProj A).chart V hV) :=
  ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso V hV n).hom ≫
    pushTheta (A.grading V) (P.affineDatum V) n ≫ P.chartTargetHom V hV n

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end

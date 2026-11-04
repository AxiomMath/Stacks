module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.BasePowerMap
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.PolarizationDegreeOne
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUniqueSections

/-!
# [Stacks, Tag 0D4F]: `θ'` is functorial in the deformation

For a morphism `φ : D₁ ⟶ D₂` of admissible deformations over `g : S'₁ ⟶ S'₂`, with total part
`g' : X'₁ ⟶ X'₂`, polarization `g'^* ℒ'₂ ≅ ℒ'₁` and the isomorphism
`M : Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` of `projBaseChangeHom` (with
`r'₁ ≫ M = g' ≫ r'₂`, `canonicalProjHom_comp_projBaseChangeHom`), the canonical maps
`θ'ᵢ : (r'ᵢ)^* 𝒪(1) ⟶ ℒ'ᵢ` are compatible with the map of Serre twists
`M^* 𝒪_{Proj_{S'₂}(𝒜'(D₂))}(1) ⟶ 𝒪_{Proj_{S'₁}(𝒜'(D₁))}(1)` of [Stacks, Tags 01O3, 07ZJ]
(`projBaseChangeTwistMap`) and the polarization.

Both composites `(g' ≫ r'₂)^* 𝒪(n) ⟶ (ℒ'₁)^{⊗ n}` are, in every degree, multiplicative on inverse
images of sections and carry the inverse image of the section `ψ(a)` of `𝒪(d)` attached to a
homogeneous `a` of `𝒜'_d(D₂)`, `d > 0`, to the pullback of `a` along `g'`; by [Stacks, Tag 01O9]
for the datum `basePowerMap φ` (whose morphism is `g' ≫ r'₂`) they agree.

## Main definitions

* `…AdmissibleDeformation.projBaseChangeTwistMap`.

## Main results

* `…AdmissibleDeformation.canonicalTwistMap_comp_polarization`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE sectionPull)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU Otw twD)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

namespace PolarizedFamily.AdmissibleDeformation

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

section Generic

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (Q : GradedPowerMap A f)

/-- The law of [Stacks, Tag 01O9] (1) for a family on inverse images, in positive degrees over the
affine opens of the base. -/
def PsiLaw (r : T ⟶ (relativeProj A).scheme) (hrf : r ≫ (relativeProj A).toBase = f)
    (Φ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (Otw A n) ⟶ tensorPowerModule T Q.L n) : Prop :=
  ∀ (V : S.Opens) (_ : IsAffineOpen V) (d : ℕ) (_ : 0 < d) (a : Γ(A.piece (d : ℤ), V)),
      (Φ d).app (r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
          (unitApp r (Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
        (tensorPowerModule T Q.L d).presheaf.map
          (homOfLE (GradedPowerMap.preimage_toBase_le_of_comp hrf V)).op
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare Q.L d).hom.app (f ⁻¹ᵁ V)
            (Q.value d V a))

/-- `GradedPowerMap.eq_of_unitApp_laws` with the multiplicativity stated as
`TwistSections.UnitMul`. -/
theorem eq_of_unitMul (hcov : Q.coveringOpen = ⊤) (r : T ⟶ (relativeProj A).scheme)
    (hr : Q.coveringOpen.ι ≫ r = Q.globalMorphism (relativeProj A))
    (hrf : r ≫ (relativeProj A).toBase = f)
    (Φ₁ Φ₂ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (Otw A n) ⟶ tensorPowerModule T Q.L n)
    (hM₁ : TwistSections.UnitMul Q.L r (twD A).algebra Φ₁)
    (hM₂ : TwistSections.UnitMul Q.L r (twD A).algebra Φ₂)
    (hP₁ : PsiLaw Q r hrf Φ₁) (hP₂ : PsiLaw Q r hrf Φ₂)
    (n : ℤ) : Φ₁ n = Φ₂ n :=
  Q.eq_of_unitApp_laws hcov r hr hrf Φ₁ Φ₂ hM₁ hM₂ hP₁ hP₂ n

end Generic

/-- The final chase of `canonicalTwistMap_comp_polarization`, with every object free. -/
theorem final_chase {C : Type*} [Category C] {D : Type*} [Category D] (F : D ⥤ C)
    {B B' Y₁ T₁ L₁ P₁ : C} {A₀ T₂₀ L₂₀ : D}
    (cH : F.obj A₀ ⟶ B) (cI : B ⟶ F.obj A₀) (hcI : cH ≫ cI = 𝟙 _)
    (t₂ : A₀ ⟶ T₂₀) (κ₂ : T₂₀ ⟶ L₂₀) (θ₂ : A₀ ⟶ L₂₀) (e₂ : θ₂ = t₂ ≫ κ₂)
    (pol : F.obj L₂₀ ⟶ L₁) (pp : F.obj T₂₀ ⟶ T₁) (κ₁ : T₁ ⟶ L₁)
    (hk : F.map κ₂ ≫ pol = pp ≫ κ₁)
    (cg : B ⟶ B') (cI' : B' ⟶ P₁) (Gτ : P₁ ⟶ Y₁) (t₁ : Y₁ ⟶ T₁) (θ₁ : Y₁ ⟶ L₁)
    (e₁ : θ₁ = t₁ ≫ κ₁)
    (h1 : cI ≫ F.map t₂ ≫ pp = cg ≫ cI' ≫ Gτ ≫ t₁) :
    F.map θ₂ ≫ pol = cH ≫ cg ≫ cI' ≫ Gτ ≫ θ₁ := by
  subst e₂ e₁
  rw [F.map_comp, Category.assoc, hk, ← Category.id_comp (F.map t₂), ← hcI]
  simp only [Category.assoc]
  rw [reassoc_of% h1]

/-- `pullbackCongr` at `rfl` is the identity. -/
theorem pullbackCongr_rfl_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ :=
  rfl

/-- `final_chase` transported along equalities of the morphisms involved. -/
theorem final_square {X₁ X₂ P₁ P₂ : Scheme.{u}} (q : X₁ ⟶ X₂) (r₁ r₁' : X₁ ⟶ P₁) (h₁ : r₁ = r₁')
    (r₂ r₂' : X₂ ⟶ P₂) (h₂ : r₂ = r₂') (M M' : P₁ ⟶ P₂) (hM : M = M')
    (hsq : q ≫ r₂ = r₁ ≫ M) (hsq' : q ≫ r₂' = r₁' ≫ M')
    {O₂ : P₂.Modules} {O₁ : P₁.Modules} {L₂ T₂ : X₂.Modules} {L₁ T₁ : X₁.Modules}
    (θ₂ : (Scheme.Modules.pullback r₂).obj O₂ ⟶ L₂) (t₂ : (Scheme.Modules.pullback r₂').obj O₂ ⟶ T₂)
    (κ₂ : T₂ ⟶ L₂) (e₂ : θ₂ = (Scheme.Modules.pullbackCongr h₂).hom.app O₂ ≫ t₂ ≫ κ₂)
    (θ₁ : (Scheme.Modules.pullback r₁).obj O₁ ⟶ L₁) (t₁ : (Scheme.Modules.pullback r₁').obj O₁ ⟶ T₁)
    (κ₁ : T₁ ⟶ L₁) (e₁ : θ₁ = (Scheme.Modules.pullbackCongr h₁).hom.app O₁ ≫ t₁ ≫ κ₁)
    (τ : (Scheme.Modules.pullback M).obj O₂ ⟶ O₁) (τ' : (Scheme.Modules.pullback M').obj O₂ ⟶ O₁)
    (eτ : τ = (Scheme.Modules.pullbackCongr hM).hom.app O₂ ≫ τ')
    (pol : (Scheme.Modules.pullback q).obj L₂ ⟶ L₁) (pp : (Scheme.Modules.pullback q).obj T₂ ⟶ T₁)
    (hk : (Scheme.Modules.pullback q).map κ₂ ≫ pol = pp ≫ κ₁)
    (h1 : (Scheme.Modules.pullbackComp q r₂').inv.app O₂ ≫ (Scheme.Modules.pullback q).map t₂ ≫ pp =
      (Scheme.Modules.pullbackCongr hsq').hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁' M').inv.app O₂ ≫
        (Scheme.Modules.pullback r₁').map τ' ≫ t₁) :
    (Scheme.Modules.pullback q).map θ₂ ≫ pol =
      (Scheme.Modules.pullbackComp q r₂).hom.app O₂ ≫
        (Scheme.Modules.pullbackCongr hsq).hom.app O₂ ≫
        (Scheme.Modules.pullbackComp r₁ M).inv.app O₂ ≫
        (Scheme.Modules.pullback r₁).map τ ≫ θ₁ := by
  subst h₁ h₂ hM e₂ e₁ eτ
  rw [pullbackCongr_rfl_hom_app r₂ O₂, pullbackCongr_rfl_hom_app M O₂,
    pullbackCongr_rfl_hom_app r₁ O₁]
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact final_chase (Scheme.Modules.pullback q) ((Scheme.Modules.pullbackComp q r₂).hom.app O₂)
    ((Scheme.Modules.pullbackComp q r₂).inv.app O₂)
    (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp q r₂) O₂) t₂ κ₂ (t₂ ≫ κ₂) rfl pol pp κ₁ hk
    ((Scheme.Modules.pullbackCongr hsq).hom.app O₂) ((Scheme.Modules.pullbackComp r₁ M).inv.app O₂)
    ((Scheme.Modules.pullback r₁).map τ') t₁ (t₁ ≫ κ₁) rfl h1

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ)
  (hd₀ : 0 < d₀) (hiso : ∀ n : ℤ, IsIso ((algebraPullbackHom φ d₀ hd₀).app n))

/-- **The map of Serre twists along `projBaseChangeHom`**:
`M^* 𝒪_{Proj_{S'₂}(𝒜'(D₂))}(1) ⟶ 𝒪_{Proj_{S'₁}(𝒜'(D₁))}(1)`, the comparison of twists of the base
change morphism of [Stacks, Tag 01O3] followed by the map of Serre twists of [Stacks, Tag 07ZJ]
for `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`. -/
def projBaseChangeTwistMap :
    (Scheme.Modules.pullback (projBaseChangeHom φ d₀ hd₀ hiso)).obj
        (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      relativeTwist (D₁.truncatedSectionAlgebra d₀ hd₀) 1 :=
  (baseChangeTwistHom (algebraPullbackSheafHom φ d₀ hd₀)
    (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso)).app 1

/-- `r'` as the composite it is defined to be, the spelling `canonicalTwistPow` is stated at. -/
abbrev canonicalProjHom' (D : P.AdmissibleDeformation) :
    D.X' ⟶ (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).scheme :=
  D.fullSectionProjHom D.isRelativelyAmple_L' ≫
    projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
      (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)

/-- `projBaseChangeHom` as the composite it is defined to be. -/
abbrev projBaseChangeHom' :
    (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).scheme ⟶
      (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).scheme :=
  projMapOfEventuallyIso (algebraPullbackSheafHom φ d₀ hd₀)
      (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso) ≫
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base

/-- `canonicalTwistMap` in terms of `canonicalTwistPow`, with the spelling `canonicalProjHom'`. -/
private theorem canonicalTwistMap_eq_congr (D : P.AdmissibleDeformation) :
    D.canonicalTwistMap d₀ hd₀ =
      (Scheme.Modules.pullbackCongr (rfl : D.canonicalProjHom d₀ hd₀ =
        canonicalProjHom' d₀ hd₀ D)).hom.app
          (relativeTwist (D.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        D.canonicalTwistPow d₀ hd₀ 1 ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D.L' 1).inv ≫ (λ_ D.L').hom := by
  rw [pullbackCongr_rfl_hom_app, Category.id_comp]
  exact D.canonicalTwistMap_eq d₀ hd₀

/-- `g' ≫ r'₂ = r'₁ ≫ M`, `canonicalProjHom_comp_projBaseChangeHom` in the primed spellings. -/
theorem total_comp_canonicalProjHom' :
    φ.total ≫ canonicalProjHom' d₀ hd₀ D₂ =
      canonicalProjHom' d₀ hd₀ D₁ ≫ projBaseChangeHom' φ d₀ hd₀ hiso :=
  (canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hiso).symm

/-- The first family: `θ'₂` pulled back along `g'` and read in the powers of `ℒ'₁`. -/
def twistFamily₁ (n : ℤ) :
    (Scheme.Modules.pullback (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)).obj
        (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ⟶ tensorPowerModule D₁.X' D₁.L' n :=
  TwistSections.comp₃ D₂.L' φ.total D₁.L' φ.polarization (canonicalProjHom' d₀ hd₀ D₂)
    (D₂.canonicalTwistPow d₀ hd₀) n

/-- The second family: the map of Serre twists along `projBaseChangeHom` pulled back along `r'₁`,
followed by `θ'₁`. -/
def twistFamily₂ (n : ℤ) :
    (Scheme.Modules.pullback (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)).obj
        (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ⟶ tensorPowerModule D₁.X' D₁.L' n :=
  TwistSections.congrFamily D₁.L' (total_comp_canonicalProjHom' φ d₀ hd₀ hiso)
    (TwistSections.comp₂ D₁.L' (canonicalProjHom' d₀ hd₀ D₁) (projBaseChangeHom' φ d₀ hd₀ hiso)
      (baseChangeTwistHom (algebraPullbackSheafHom φ d₀ hd₀)
        (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso))
      (D₁.canonicalTwistPow d₀ hd₀)) n

/-- The first family is multiplicative on inverse images of sections. -/
theorem twistFamily₁_unitMul :
    TwistSections.UnitMul D₁.L' (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
      (twistAlgebra (D₂.truncatedSectionAlgebra d₀ hd₀)) (twistFamily₁ φ d₀ hd₀) :=
  TwistSections.comp₃_unitMul D₂.L' φ.total D₁.L' φ.polarization _ _
    (D₂.canonicalTwistPow_unitMul d₀ hd₀)

/-- The second family is multiplicative on inverse images of sections. -/
theorem twistFamily₂_unitMul :
    TwistSections.UnitMul D₁.L' (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
      (twistAlgebra (D₂.truncatedSectionAlgebra d₀ hd₀)) (twistFamily₂ φ d₀ hd₀ hiso) :=
  TwistSections.congrFamily_unitMul D₁.L' _ _
    (TwistSections.comp₂_unitMul D₁.L' _ _ _ _ (D₁.canonicalTwistPow_unitMul d₀ hd₀))

/-- `g' ≫ r'₂` lies over `S'₂`. -/
theorem total_comp_canonicalProjHom'_toBase :
    (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂) ≫
        (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase =
      D₁.f' ≫ φ.base := by
  rw [Category.assoc, show canonicalProjHom' d₀ hd₀ D₂ ≫
      (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase = D₂.f' from
    D₂.canonicalProjHom_comp_toBase d₀ hd₀]
  exact φ.isPullback.w

/-- `sectionPull` along `g'` commutes with restriction, for a section of `ℒ'₂^{⊗ d}` over
`f'₂⁻¹ V`. -/
private theorem map_sectionPull_total (V : D₂.S'.Opens) (d : ℕ)
    (y : Γ(tensorPowerModule D₂.X' D₂.L' d, D₂.f' ⁻¹ᵁ V)) {W W' : D₁.X'.Opens}
    (hW : W ≤ φ.total ⁻¹ᵁ (D₂.f' ⁻¹ᵁ V)) (i : W' ≤ W) :
    (tensorPowerModule D₁.X' D₁.L' d).presheaf.map (homOfLE i).op
        (sectionPull φ.total D₂.L' D₁.L' φ.polarization (d : ℤ) (D₂.f' ⁻¹ᵁ V) W hW y) =
      sectionPull φ.total D₂.L' D₁.L' φ.polarization (d : ℤ) (D₂.f' ⁻¹ᵁ V) W' (i.trans hW) y :=
  Stacks.AlgebraicGeometry.SectionRingBaseChange.map_sectionPull φ.total D₂.L' D₁.L'
    φ.polarization (D₂.f' ⁻¹ᵁ V) (d : ℤ) hW i y

/-- The `powCompare` round trip on a pulled back section, restricted to the inverse image of
`V` under `g' ≫ r'₂`. -/
private theorem map_powCompare_hom_inv_sectionPull (V : D₂.S'.Opens) (d : ℕ)
    (y : Γ(tensorPowerModule D₂.X' D₂.L' d, D₂.f' ⁻¹ᵁ V)) :
    (tensorPowerModule D₁.X' D₁.L' d).presheaf.map
        (homOfLE (GradedPowerMap.preimage_toBase_le_of_comp
          (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) V)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' d).hom.app
          ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' d).inv.app
            ((D₁.f' ≫ φ.base) ⁻¹ᵁ V)
            (sectionPull φ.total D₂.L' D₁.L' φ.polarization (d : ℤ) (D₂.f' ⁻¹ᵁ V)
              ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) (preimage_comp_le_preimage_total φ V) y))) =
      sectionPull φ.total D₂.L' D₁.L' φ.polarization (d : ℤ) (D₂.f' ⁻¹ᵁ V) _
        ((GradedPowerMap.preimage_toBase_le_of_comp
          (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) V).trans
          (preimage_comp_le_preimage_total φ V)) y :=
  (congrArg _ (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app _ _ _)).trans
    (map_sectionPull_total φ V d y _ _)

/-- **The first family on the sections attached to homogeneous elements.** -/
theorem twistFamily₁_app_unitApp_psiU (V : D₂.S'.Opens) (d : ℕ)
    (a : Γ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ), V)) :
    (twistFamily₁ φ d₀ hd₀ d).app ((φ.total ≫ canonicalProjHom' d₀ hd₀ D₂) ⁻¹ᵁ
        ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V))
        (unitApp (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) d)
          ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
          (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)) =
      (tensorPowerModule D₁.X' (basePowerMap φ d₀ hd₀).L d).presheaf.map
        (homOfLE (GradedPowerMap.preimage_toBase_le_of_comp
          (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) V)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare
            (basePowerMap φ d₀ hd₀).L d).hom.app
          ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) ((basePowerMap φ d₀ hd₀).value d V a)) := by
  have e1 := TwistSections.comp₃_app D₂.L' φ.total D₁.L' φ.polarization
    (canonicalProjHom' d₀ hd₀ D₂) (D₂.canonicalTwistPow d₀ hd₀) d
    ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
    (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)
  have e2 := D₂.canonicalTwistPow_app_unitApp_psiU d₀ hd₀ d V a
  have e3 := TwistSections.sectionPull_map_source D₂.L' φ.total D₁.L' φ.polarization (d : ℤ)
    (D₂.canonicalProjHom_preimage_le d₀ hd₀ V) _ le_rfl
    (show Γ(tensorPowerModule D₂.X' D₂.L' d, D₂.f' ⁻¹ᵁ V) from
      ((D₂.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a)
  have e4 := basePowerMap_value φ d₀ hd₀ d V a
  refine e1.trans ?_
  rw [e2, e3, e4]
  exact (map_powCompare_hom_inv_sectionPull φ d₀ hd₀ V d _).symm

/-- **The second family on the sections attached to homogeneous elements.** -/
theorem twistFamily₂_app_unitApp_psiU (V : D₂.S'.Opens) (d : ℕ) (hd : d₀ ≤ d)
    (a : Γ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ), V)) :
    (twistFamily₂ φ d₀ hd₀ hiso d).app ((φ.total ≫ canonicalProjHom' d₀ hd₀ D₂) ⁻¹ᵁ
        ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V))
        (unitApp (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) d)
          ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
          (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)) =
      (tensorPowerModule D₁.X' (basePowerMap φ d₀ hd₀).L d).presheaf.map
        (homOfLE (GradedPowerMap.preimage_toBase_le_of_comp
          (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) V)).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare
            (basePowerMap φ d₀ hd₀).L d).hom.app
          ((D₁.f' ≫ φ.base) ⁻¹ᵁ V) ((basePowerMap φ d₀ hd₀).value d V a)) := by
  have e1 := TwistSections.congrFamily_app D₁.L' (total_comp_canonicalProjHom' φ d₀ hd₀ hiso)
    (TwistSections.comp₂ D₁.L' (canonicalProjHom' d₀ hd₀ D₁) (projBaseChangeHom' φ d₀ hd₀ hiso)
      (baseChangeTwistHom (algebraPullbackSheafHom φ d₀ hd₀)
        (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso)) (D₁.canonicalTwistPow d₀ hd₀)) d
    ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
    (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)
  have e2 := TwistSections.comp₂_app_eq D₁.L' (canonicalProjHom' d₀ hd₀ D₁)
    (projBaseChangeHom' φ d₀ hd₀ hiso) (baseChangeTwistHom (algebraPullbackSheafHom φ d₀ hd₀)
        (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso)) (D₁.canonicalTwistPow d₀ hd₀) d
    ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
    (psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V a)
    (psiU (D₁.truncatedSectionAlgebra d₀ hd₀) d (φ.base ⁻¹ᵁ V)
      (((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
      (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a)))
    (baseChangeTwist_preimage_le _ _ V) (baseChangeTwistHom_app_unitApp_psiU _ _ d V a)
  have e3 := D₁.canonicalTwistPow_app_unitApp_psiU d₀ hd₀ d (φ.base ⁻¹ᵁ V)
    (((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
      (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a))
  have e5 : Scheme.Modules.pullbackSection φ.base
      ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V (φ.base ⁻¹ᵁ V) le_rfl a =
      unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a :=
    Stacks.Conormal.pullbackSection_self φ.base _ V a
  have e4 := comparison_algebraPullbackSheafHom_pullbackSection φ d₀ hd₀
    (le_refl (φ.base ⁻¹ᵁ V)) d hd a
  have e4' : (show Γ(tensorPowerModule D₁.X' D₁.L' d, D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) from
      ((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
        (((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
      (unitApp φ.base ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ)) V a))) =
      sectionPull φ.total D₂.L' D₁.L' φ.polarization (d : ℤ) (D₂.f' ⁻¹ᵁ V)
        (D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) (preimage_comp_le_preimage_total φ V)
        (show Γ(tensorPowerModule D₂.X' D₂.L' d, D₂.f' ⁻¹ᵁ V) from
          ((D₂.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a) :=
    (congrArg (fun z => ((D₁.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V)
      (((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)).app (φ.base ⁻¹ᵁ V) z)) e5).symm.trans
      e4
  have t1 : twistFamily₂ φ d₀ hd₀ hiso d = TwistSections.congrFamily D₁.L'
      (total_comp_canonicalProjHom' φ d₀ hd₀ hiso)
      (TwistSections.comp₂ D₁.L' (canonicalProjHom' d₀ hd₀ D₁) (projBaseChangeHom' φ d₀ hd₀ hiso)
        (baseChangeTwistHom (algebraPullbackSheafHom φ d₀ hd₀)
        (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso))
        (D₁.canonicalTwistPow d₀ hd₀)) d := rfl
  have e6 := basePowerMap_value φ d₀ hd₀ d V a
  rw [t1]
  rw [e1]
  rw [e2, e3, e4', e6]
  have hW₁ : D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ V) ≤ φ.total ⁻¹ᵁ (D₂.f' ⁻¹ᵁ V) :=
    preimage_comp_le_preimage_total φ V
  have hc := D₁.canonicalProjHom_preimage_le d₀ hd₀ (φ.base ⁻¹ᵁ V)
  have hb : (canonicalProjHom' d₀ hd₀ D₁ ≫ projBaseChangeHom' φ d₀ hd₀ hiso) ⁻¹ᵁ
      ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V) ≤
      canonicalProjHom' d₀ hd₀ D₁ ⁻¹ᵁ
        ((relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ (φ.base ⁻¹ᵁ V)) :=
    (canonicalProjHom' d₀ hd₀ D₁).preimage_mono
    (baseChangeTwist_preimage_le (algebraPullbackSheafHom φ d₀ hd₀)
      (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso) V)
  have ha := TwistSections.preimage_le_of_eq (total_comp_canonicalProjHom' φ d₀ hd₀ hiso)
    ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
  let y := show Γ(tensorPowerModule D₂.X' D₂.L' d, D₂.f' ⁻¹ᵁ V) from
    ((D₂.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a
  have s1 := map_sectionPull_total φ V d y hW₁ hc
  have s2 := map_sectionPull_total φ V d y (hc.trans hW₁) hb
  have s3 := map_sectionPull_total φ V d y (hb.trans (hc.trans hW₁)) ha
  exact ((congrArg (fun z => (tensorPowerModule D₁.X' D₁.L' d).presheaf.map (homOfLE ha).op
    ((tensorPowerModule D₁.X' D₁.L' d).presheaf.map (homOfLE hb).op z)) s1).trans
    ((congrArg (fun z => (tensorPowerModule D₁.X' D₁.L' d).presheaf.map (homOfLE ha).op z) s2).trans
      s3)).trans (map_powCompare_hom_inv_sectionPull φ d₀ hd₀ V d y).symm

/-- The first family in degree `n`, unfolded: the inverse image of `θ'₂` along `g'` followed by
the polarization. -/
theorem twistFamily₁_eq_def (n : ℤ) :
    twistFamily₁ φ d₀ hd₀ n =
      (Scheme.Modules.pullbackComp φ.total (canonicalProjHom' d₀ hd₀ D₂)).inv.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ≫
        (Scheme.Modules.pullback φ.total).map (D₂.canonicalTwistPow d₀ hd₀ n) ≫
        TwistSections.polPow D₂.L' φ.total D₁.L' φ.polarization n :=
  by unfold twistFamily₁ TwistSections.comp₃; rfl

/-- The second family in degree `n`, unfolded: the comparison of inverse images along
`g' ≫ r'₂ = r'₁ ≫ M`, the inverse image along `r'₁` of the map of Serre twists, then `θ'₁`. -/
theorem twistFamily₂_eq_def (n : ℤ) :
    twistFamily₂ φ d₀ hd₀ hiso n =
      (Scheme.Modules.pullbackCongr (total_comp_canonicalProjHom' φ d₀ hd₀ hiso)).hom.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ≫
        (Scheme.Modules.pullbackComp (canonicalProjHom' d₀ hd₀ D₁)
          (projBaseChangeHom' φ d₀ hd₀ hiso)).inv.app
          (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) n) ≫
        (Scheme.Modules.pullback (canonicalProjHom' d₀ hd₀ D₁)).map
          ((baseChangeTwistHom (algebraPullbackSheafHom φ d₀ hd₀)
            (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso)).app n) ≫
        D₁.canonicalTwistPow d₀ hd₀ n :=
  by unfold twistFamily₂ TwistSections.congrFamily TwistSections.comp₂; rfl


section Irreducible

attribute [local irreducible] twistFamily₁ twistFamily₂

/-- The second family satisfies the law of [Stacks, Tag 01O9] (1) for `basePowerMap`. -/
theorem twistFamily₂_psiLaw : PsiLaw (basePowerMap φ d₀ hd₀) (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
    (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) (twistFamily₂ φ d₀ hd₀ hiso) := by
  intro V _ d hd a
  by_cases hnd : d₀ ≤ d
  · exact twistFamily₂_app_unitApp_psiU φ d₀ hd₀ hiso V d hnd a
  · have hy : a = 0 :=
      Stacks.AlgebraicGeometry.SectionAlgebra.eq_zero_of_tailPiece D₂.laurentPushforward d₀
        (show (d : ℤ) ≠ 0 by omega) (show ¬ (d₀ : ℤ) ≤ (d : ℤ) by omega) (op V) _
    subst hy
    have z1 : psiU (D₂.truncatedSectionAlgebra d₀ hd₀) d V 0 = 0 := map_zero _
    have z2 : unitApp (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
        (Otw (D₂.truncatedSectionAlgebra d₀ hd₀) d)
        ((relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V) 0 = 0 := map_zero _
    have z4 : (basePowerMap φ d₀ hd₀).value d V 0 = 0 := map_zero _
    rw [z1, z2, z4, map_zero, map_zero]
    exact (map_zero _).symm

/-- The first family satisfies the law of [Stacks, Tag 01O9] (1) for `basePowerMap`. -/
theorem twistFamily₁_psiLaw : PsiLaw (basePowerMap φ d₀ hd₀) (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂)
    (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) (twistFamily₁ φ d₀ hd₀) := by
  intro V _ d _ a
  exact twistFamily₁_app_unitApp_psiU φ d₀ hd₀ V d a

/-- **The two families agree in every degree**: [Stacks, Tag 01O9] for the datum `basePowerMap φ`,
whose morphism is `g' ≫ r'₂`. -/
theorem twistFamily₁_eq_twistFamily₂ (n : ℤ) :
    twistFamily₁ φ d₀ hd₀ n = twistFamily₂ φ d₀ hd₀ hiso n :=
  eq_of_unitMul (basePowerMap φ d₀ hd₀) (coveringOpen_basePowerMap φ d₀ hd₀)
    (φ.total ≫ canonicalProjHom' d₀ hd₀ D₂) (globalMorphism_basePowerMap φ d₀ hd₀)
    (total_comp_canonicalProjHom'_toBase φ d₀ hd₀) (twistFamily₁ φ d₀ hd₀)
    (twistFamily₂ φ d₀ hd₀ hiso) (twistFamily₁_unitMul φ d₀ hd₀)
    (twistFamily₂_unitMul φ d₀ hd₀ hiso) (twistFamily₁_psiLaw φ d₀ hd₀)
    (twistFamily₂_psiLaw φ d₀ hd₀ hiso) n

/-- **[Stacks, Tag 0D4F]: `θ'` is functorial in the deformation.** For a morphism `φ : D₁ ⟶ D₂` of
admissible deformations over `g : S'₁ ⟶ S'₂`, with total part `g' : X'₁ ⟶ X'₂` and polarization
`g'^* ℒ'₂ ≅ ℒ'₁`, and `M = projBaseChangeHom φ` (so that `r'₁ ≫ M = g' ≫ r'₂`), the square

`g'^* (r'₂)^* 𝒪(1) --g'^* θ'₂--> g'^* ℒ'₂ --polarization--> ℒ'₁`
`g'^* (r'₂)^* 𝒪(1) ≅ (r'₁ ≫ M)^* 𝒪(1) ≅ (r'₁)^* M^* 𝒪(1) --(r'₁)^* τ--> (r'₁)^* 𝒪(1) --θ'₁--> ℒ'₁`

commutes, where `τ : M^* 𝒪_{Proj_{S'₂}(𝒜'(D₂))}(1) ⟶ 𝒪_{Proj_{S'₁}(𝒜'(D₁))}(1)` is the map of Serre
twists of `projBaseChangeTwistMap` ([Stacks, Tags 01O3, 07ZJ]). -/
theorem canonicalTwistMap_comp_polarization :
    (Scheme.Modules.pullback φ.total).map (D₂.canonicalTwistMap d₀ hd₀) ≫ φ.polarization.hom =
      (Scheme.Modules.pullbackComp φ.total (D₂.canonicalProjHom d₀ hd₀)).hom.app _ ≫
        (Scheme.Modules.pullbackCongr
          (canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hiso).symm).hom.app _ ≫
        (Scheme.Modules.pullbackComp (D₁.canonicalProjHom d₀ hd₀)
          (projBaseChangeHom φ d₀ hd₀ hiso)).inv.app _ ≫
        (Scheme.Modules.pullback (D₁.canonicalProjHom d₀ hd₀)).map
          (projBaseChangeTwistMap φ d₀ hd₀ hiso) ≫
        D₁.canonicalTwistMap d₀ hd₀ := by
  have h1 := twistFamily₁_eq_twistFamily₂ φ d₀ hd₀ hiso 1
  rw [twistFamily₁_eq_def, twistFamily₂_eq_def] at h1
  have hk := TwistSections.pullback_kappa_comp φ.total D₂.L' D₁.L' φ.polarization
  have eτ : projBaseChangeTwistMap φ d₀ hd₀ hiso =
      (Scheme.Modules.pullbackCongr (rfl : projBaseChangeHom φ d₀ hd₀ hiso =
        projBaseChangeHom' φ d₀ hd₀ hiso)).hom.app
        (relativeTwist (D₂.truncatedSectionAlgebra d₀ hd₀) 1) ≫
        (baseChangeTwistHom (algebraPullbackSheafHom φ d₀ hd₀)
          (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso)).app 1 := by
    rw [pullbackCongr_rfl_hom_app]
    exact (Category.id_comp _).symm
  exact final_square φ.total (D₁.canonicalProjHom d₀ hd₀) (canonicalProjHom' d₀ hd₀ D₁) rfl
    (D₂.canonicalProjHom d₀ hd₀) (canonicalProjHom' d₀ hd₀ D₂) rfl
    (projBaseChangeHom φ d₀ hd₀ hiso) (projBaseChangeHom' φ d₀ hd₀ hiso) rfl
    (canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ hiso).symm
    (total_comp_canonicalProjHom' φ d₀ hd₀ hiso)
    (D₂.canonicalTwistMap d₀ hd₀) (D₂.canonicalTwistPow d₀ hd₀ 1) _
    (canonicalTwistMap_eq_congr d₀ hd₀ D₂)
    (D₁.canonicalTwistMap d₀ hd₀) (D₁.canonicalTwistPow d₀ hd₀ 1) _
    (canonicalTwistMap_eq_congr d₀ hd₀ D₁)
    (projBaseChangeTwistMap φ d₀ hd₀ hiso) _ eτ φ.polarization.hom
    (TwistSections.polPow D₂.L' φ.total D₁.L' φ.polarization 1) hk h1

end Irreducible

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end

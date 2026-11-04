module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.TargetChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleThetaBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.TwistComparison

/-!
# The map `θ` of Tag 01O9 under a change of the target

Let `hs : Y' ⟶ Y` be a morphism of schemes, `𝒜` a quasi-coherent graded `𝒪_Y`-algebra, `𝒜₁` one on
`Y'` with an isomorphism `Φ : 𝒜₁ ≅ hs^*𝒜`, `f₀ : X ⟶ Y'`, `ℒ` invertible on `X` and
`χ : f₀^*𝒜₁ ⟶ ⨁_d ℒ^{⊗ d}` a map of graded algebras.  Reading `χ` through `Φ` and through the
identification `f₀^*(hs^*𝒜) = (hs ∘ f₀)^*𝒜` of [Stacks, Tag 01NT] gives a map
`ζ : (hs ∘ f₀)^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` (`…RelativeProjInvertibleMorphism.changeTarget`), and
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/TargetChange.lean` compares the opens
and the morphisms of [Stacks, Tag 01O9] for `ζ` and `χ`.  This file compares the maps `θ` of
Tag 01O9 (`…RelativeProjInvertibleMorphism.theta_changeTarget`), from the following data:

* `U(ζ) = U(χ)` and `r_ζ = (U(ζ) ⊆ U(χ)) ≫ r_χ ≫ pc` for the comparison morphism
  `pc = Proj(Φ) ≫ (Proj_{Y'}(hs^*𝒜) ⟶ Proj_Y(𝒜))` of Stacks 084B (3)
  (`…coveringOpen_changeTarget`, `…homOfLE_globalMorphism_changeTarget`);
* the identification of the sources `(U(ζ) ⊆ U(χ))^* r_χ^*𝒪_{Proj(𝒜₁)}(*) ≅ r_ζ^*𝒪_{Proj(𝒜)}(*)`
  through the comparison of twists along `pc` (`…thetaChangeSourceIso`) and of the targets
  `(U₁ ⊆ U₂)^*(⨁_d ℒ^{⊗ d}|_{U₂}) ≅ ⨁_d ℒ^{⊗ d}|_{U₁}` (`…laurentOnHomOfLEIso`), with the
  degree components of the composite `thetaChangeSourceIso⁻¹ ≫ j^*θ_χ ≫ laurentOnHomOfLEIso`
  (`…thetaChange_app`);
* the three section-level facts the clause-(1) characterization of `θ_ζ` consumes: the comparison
  of twists carries the pullback of `ψ_{Proj(𝒜)}(a)` to `ψ_{Proj(𝒜₁)}(Φ^{-1}(hs^*a))`
  (`…congrBaseChangeTwistIso_hom_pullbackSection_psiU`), the value of `ζ` at `a` is the value of
  `χ` at `Φ^{-1}(hs^*a)` (`…valueSec_changeTarget`), and `θ_χ` restricted to a smaller open, on a
  pulled-back section, is its pushforward form (`…laurentOnHomOfLE_theta_pullbackSection`).

The identity `θ_ζ = thetaChangeSourceIso⁻¹ ≫ j^*θ_χ ≫ laurentOnHomOfLEIso` follows from these by
the clause-(1) characterization `…GradedPowerMap.eq_theta_of_clauseOne` of `θ_ζ`, after chasing a
pulled-back homogeneous section through the factors (`…thetaChange_app_pullbackUnit`).

## Main results

* `…RelativeProjInvertibleMorphism.theta_changeTarget`: **`θ_ζ` is `θ_χ` read through the
  comparison of twists along `pc`**.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### `⨁_d ℒ^{⊗ d}` restricted to a smaller open -/

section LaurentOn

variable {T : Scheme.{u}} (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]
  {U₁ U₂ : T.Opens} (h : U₁ ≤ U₂)

/-- For opens `U₁ ≤ U₂`, the inclusion `U₁ ⟶ U₂` followed by `U₂ ⟶ T` equals `U₁ ⟶ T` followed by
the identity of `T`. -/
theorem homOfLE_ι_eq_ι_comp_id : T.homOfLE h ≫ U₂.ι = U₁.ι ≫ 𝟙 T := by
  rw [Scheme.homOfLE_ι, Category.comp_id]

/-- `(U₁ ⊆ U₂)^*(ℒ^{⊗ n}|_{U₂}) ≅ ℒ^{⊗ n}|_{U₁}`. -/
def laurentOnHomOfLEPieceIso (n : ℤ) :
    (Scheme.Modules.pullback (T.homOfLE h)).obj ((laurentOn L U₂).piece n) ≅
      (laurentOn L U₁).piece n :=
  (Scheme.Modules.pullback (T.homOfLE h)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U₂.ι).app (tensorPowerModule T L n))
    ≪≫ (Scheme.Modules.pullbackComp (T.homOfLE h) U₂.ι).app _
    ≪≫ (Scheme.Modules.pullbackCongr (homOfLE_ι_eq_ι_comp_id h)).app _
    ≪≫ (Scheme.Modules.pullbackComp U₁.ι (𝟙 T)).symm.app _
    ≪≫ (Scheme.Modules.pullback U₁.ι).mapIso
          ((Scheme.Modules.pullbackId T).app (tensorPowerModule T L n))
    ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback U₁.ι).app _).symm

/-- The image of an open of `U₁` over `O' ⊆ U₂` lies in the image of `O'`. -/
theorem image_le_image_of_le_preimage_homOfLE (O' : U₂.toScheme.Opens) {V : U₁.toScheme.Opens}
    (h4 : V ≤ T.homOfLE h ⁻¹ᵁ O') : U₁.ι ''ᵁ V ≤ U₂.ι ''ᵁ O' := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(T.homOfLE h).base x, h4 hx,
    congrArg (fun g : U₁.toScheme ⟶ T => g.base x) (Scheme.homOfLE_ι T h)⟩

/-- **The identification on a pulled-back section is the restriction.** -/
theorem laurentOnHomOfLEPieceIso_hom_pullbackSection (n : ℤ) (O' : U₂.toScheme.Opens)
    (V : U₁.toScheme.Opens) (h4 : V ≤ T.homOfLE h ⁻¹ᵁ O')
    (t : Γ((tensorPowerModule T L n).restrict U₂.ι, O')) :
    (laurentOnHomOfLEPieceIso L h n).hom.val.app (op V)
        (pullbackSection (T.homOfLE h) _ O' V h4 t) =
      (tensorPowerModule T L n).val.map
        (homOfLE (image_le_image_of_le_preimage_homOfLE h O' h4)).op t := by
  have hV' : U₁.ι ''ᵁ V ≤ 𝟙 T ⁻¹ᵁ (U₂.ι ''ᵁ O') := image_le_image_of_le_preimage_homOfLE h O' h4
  refine (tgt_hom_pullbackSection (T.homOfLE h) U₂.ι U₁.ι (𝟙 T) (homOfLE_ι_eq_ι_comp_id h)
    (tensorPowerModule T L n) ((Scheme.Modules.pullbackId T).app (tensorPowerModule T L n))
    O' V h4 t hV').trans ?_
  refine congrArg ((tensorPowerModule T L n).val.map (homOfLE hV').op)
    (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pullbackId_hom_pullbackSection
      (tensorPowerModule T L n) (U₂.ι ''ᵁ O') _ le_rfl le_rfl t) |>.trans ?_
  exact map_map (tensorPowerModule T L n) _ _ _ t

/-- The identification on the image of a section under the unit of `j^* ⊣ j_*`. -/
theorem laurentOnHomOfLEPieceIso_hom_pullbackUnit (n : ℤ) (O' : U₂.toScheme.Opens)
    (t : Γ((tensorPowerModule T L n).restrict U₂.ι, O')) :
    (laurentOnHomOfLEPieceIso L h n).hom.val.app (op (T.homOfLE h ⁻¹ᵁ O'))
        (pullbackUnit (T.homOfLE h).toLRSHom.toShHom ((laurentOn L U₂).piece n) (op O') t) =
      (tensorPowerModule T L n).val.map
        (homOfLE (image_le_image_of_le_preimage_homOfLE h O' le_rfl)).op t :=
  (congrArg ((laurentOnHomOfLEPieceIso L h n).hom.val.app (op (T.homOfLE h ⁻¹ᵁ O')))
    (Stacks.Conormal.pullbackSection_self (T.homOfLE h) ((laurentOn L U₂).piece n) O' t).symm).trans
    (laurentOnHomOfLEPieceIso_hom_pullbackSection L h n O' _ le_rfl t)

/-- **The identification is multiplicative on the images of sections under the unit.** -/
theorem laurentOnHomOfLEPieceIso_hom_mul_pullbackUnit (i k : ℤ) (O' : U₂.toScheme.Opens)
    (a : Γ((tensorPowerModule T L i).restrict U₂.ι, O'))
    (b : Γ((tensorPowerModule T L k).restrict U₂.ι, O')) :
    (laurentOnHomOfLEPieceIso L h (i + k)).hom.val.app (op (T.homOfLE h ⁻¹ᵁ O'))
        (pullbackUnit (T.homOfLE h).toLRSHom.toShHom ((laurentOn L U₂).piece (i + k)) (op O')
          (Stacks.TensorPowerDivision.localMul L a b)) =
      Stacks.TensorPowerDivision.localMul L
        ((laurentOnHomOfLEPieceIso L h i).hom.val.app (op (T.homOfLE h ⁻¹ᵁ O'))
          (pullbackUnit (T.homOfLE h).toLRSHom.toShHom ((laurentOn L U₂).piece i) (op O') a))
        ((laurentOnHomOfLEPieceIso L h k).hom.val.app (op (T.homOfLE h ⁻¹ᵁ O'))
          (pullbackUnit (T.homOfLE h).toLRSHom.toShHom ((laurentOn L U₂).piece k) (op O') b)) := by
  refine (laurentOnHomOfLEPieceIso_hom_pullbackUnit L h (i + k) O' _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (Stacks.TensorPowerDivision.localMul L)
    (laurentOnHomOfLEPieceIso_hom_pullbackUnit L h i O' a).symm
    (laurentOnHomOfLEPieceIso_hom_pullbackUnit L h k O' b).symm)
  exact Stacks.TensorPowerDivision.map_localMul _ _ _ _

/-- **`(U₁ ⊆ U₂)^*(⨁_d ℒ^{⊗ d}|_{U₂}) ≅ ⨁_d ℒ^{⊗ d}|_{U₁}`** as sheaves of graded algebras. -/
def laurentOnHomOfLEIso :
    Stacks.Conormal.gradedPullback (T.homOfLE h) (laurentOn L U₂) ≅ laurentOn L U₁ :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso
    (A := Stacks.Conormal.gradedPullback (T.homOfLE h) (laurentOn L U₂))
    (B := laurentOn L U₁)
    (fun n => laurentOnHomOfLEPieceIso L h n)
    (fun i k U x y => map_mul_of_pullbackUnit (T.homOfLE h).toLRSHom.toShHom
      (A := laurentOn L U₂) (B := laurentOn L U₁)
      (fun n => (laurentOnHomOfLEPieceIso L h n).hom) i k
      (fun V a b => laurentOnHomOfLEPieceIso_hom_mul_pullbackUnit L h i k V a b) U x y)

end LaurentOn

/-! ### `θ` restricted to a smaller open, on a pulled-back section -/

section ThetaRestrict

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (χ : Twisting f (situationAlgebra A) 1 L) {U₁ : T.Opens}
  (h : U₁ ≤ (toGradedPowerMap χ).coveringOpen)

/-- **`θ` restricted to a smaller open `U₁ ⊆ U(χ)`, on a pulled-back section**: it is the
pushforward form of `θ` on the section, restricted. -/
theorem laurentOnHomOfLE_theta_pullbackSection (d : ℤ) (O : (relativeProj A).scheme.Opens)
    (V' : U₁.toScheme.Opens)
    (hV : V' ≤ T.homOfLE h ⁻¹ᵁ
      ((toGradedPowerMap χ).globalMorphism (relativeProj A) ⁻¹ᵁ O))
    (w : Γ(GradedPowerMap.Otw A d, O)) :
    (laurentOnHomOfLEPieceIso L h d).hom.val.app (op V')
      (((Scheme.Modules.pullback (T.homOfLE h)).map
          (X := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
            (relativeProj A))).obj (GradedPowerMap.Otw A d))
          (Y := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece d)
          ((toGradedPowerMap χ).theta.app d)).val.app (op V')
        (pullbackSection (T.homOfLE h)
          ((Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
            (relativeProj A))).obj (GradedPowerMap.Otw A d))
          ((toGradedPowerMap χ).globalMorphism (relativeProj A) ⁻¹ᵁ O) V' hV
          (pullbackSection ((toGradedPowerMap χ).globalMorphism (relativeProj A))
            (GradedPowerMap.Otw A d) O _ le_rfl w))) =
      (tensorPowerModule T L d).val.map
        (homOfLE (image_le_image_of_le_preimage_homOfLE h
          ((toGradedPowerMap χ).globalMorphism (relativeProj A) ⁻¹ᵁ O) hV)).op
        (((toGradedPowerMap χ).thetaPush d).app O w) := by
  have e7 := Scheme.Modules.pullbackSection_naturality (T.homOfLE h)
    (F := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
      (relativeProj A))).obj (GradedPowerMap.Otw A d))
    (G := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece d)
    ((toGradedPowerMap χ).theta.app d) _ V' hV
    (pullbackSection ((toGradedPowerMap χ).globalMorphism (relativeProj A))
      (GradedPowerMap.Otw A d) O _ le_rfl w)
  have e8 := (toGradedPowerMap χ).theta_app_pullbackSection d O w
  have e10 := laurentOnHomOfLEPieceIso_hom_pullbackSection L h d _ V' hV
    (((toGradedPowerMap χ).thetaPush d).app O w)
  rw [e7]
  refine (congrArg (fun z => (laurentOnHomOfLEPieceIso L h d).hom.val.app (op V')
    (pullbackSection (T.homOfLE h) ((laurentOn L (toGradedPowerMap χ).coveringOpen).piece d)
      ((toGradedPowerMap χ).globalMorphism (relativeProj A) ⁻¹ᵁ O) V' hV z)) e8).trans ?_
  exact e10

end ThetaRestrict

/-! ### The change of the target -/

section Change

variable {Y Y' T : Scheme.{u}} (A : SheafGradedAlgebra.{u} Y) (hs : Y' ⟶ Y)
  {A₁ : SheafGradedAlgebra.{u} Y'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback hs)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  {f₀ : T ⟶ Y'} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (χ : Twisting f₀ (situationAlgebra A₁) 1 L)

/-- **`χ : f₀^*𝒜₁ ⟶ ⨁ ℒ^{⊗ d}` read as a map `(hs ∘ f₀)^*𝒜 ⟶ ⨁ ℒ^{⊗ d}`**, through the isomorphism
`Φ : 𝒜₁ ≅ hs^*𝒜` and the identification `f₀^*(hs^*𝒜) = (hs ∘ f₀)^*𝒜` of [Stacks, Tag 01NT]. -/
def changeTarget : Twisting (f₀ ≫ hs) (situationAlgebra A) 1 L :=
  Twisting.baseChangeUp hs f₀ (situationAlgebra A) 1
    (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ)

/-- The comparison morphism `Proj_{Y'}(𝒜₁) ≅ Proj_{Y'}(hs^*𝒜) ⟶ Proj_Y(𝒜)`. -/
abbrev changeTargetProj : (relativeProj A₁).scheme ⟶ (relativeProj A).scheme :=
  (relativeProjCongr Φ hΦ).hom ≫ RelativeProjBaseChangeTwist.baseChangeHom A hs

/-- **`U(ζ) = U(χ)`.** -/
theorem coveringOpen_changeTarget :
    (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen =
      (toGradedPowerMap χ).coveringOpen :=
  (coveringOpen_baseChangeUp (B := A) hs
      (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ)).trans
    (coveringOpen_algebraTransport (A₁ := A.pullback hs) (A₂ := A₁) (unitalHomInverse Φ hΦ)
      (isIso_unitalHomInverse_app Φ hΦ) χ)

/-- **`r_ζ = r_χ ∘ pc`**, after a lift of an arbitrary morphism of schemes. -/
theorem lift_globalMorphism_changeTarget {W : Scheme.{u}} (q : W ⟶ T)
    (hq : q ⁻¹ᵁ (toGradedPowerMap χ).coveringOpen = ⊤) :
    liftOfPreimageEqTop _ q hq ≫ (toGradedPowerMap χ).globalMorphism (relativeProj A₁) ≫
        changeTargetProj A hs Φ hΦ =
      liftOfPreimageEqTop _ q
          ((congrArg (fun U => q ⁻¹ᵁ U) (coveringOpen_changeTarget A hs Φ hΦ χ)).trans hq) ≫
        (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) := by
  have hχ : q ⁻¹ᵁ (toGradedPowerMap (A := A.pullback hs)
      (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ)).coveringOpen = ⊤ :=
    (congrArg (fun U => q ⁻¹ᵁ U) (coveringOpen_algebraTransport (A₁ := A.pullback hs)
      (A₂ := A₁) _ (isIso_unitalHomInverse_app _ _) _)).trans hq
  have hinv := Twisting.algebraTransport_algebraTransport_unitalHomInverse Φ hΦ χ
  have s1 := lift_globalMorphism_algebraTransport (A₁ := A₁) (A₂ := A.pullback hs) Φ hΦ
    (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ) q hχ
  have s0 := lift_globalMorphism_congr hinv q
    ((congrArg (fun U => q ⁻¹ᵁ U) (coveringOpen_algebraTransport (A₁ := A₁)
      (A₂ := A.pullback hs) Φ hΦ _)).trans hχ)
  have s2 := lift_globalMorphism_baseChangeUp (B := A) hs
    (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ) q hχ
  have s1' := eq_whisker s1 (RelativeProjBaseChangeTwist.baseChangeHom A hs)
  simp only [Category.assoc] at s1'
  have s0' := eq_whisker s0 ((relativeProjCongr Φ hΦ).hom ≫
    RelativeProjBaseChangeTwist.baseChangeHom A hs)
  simp only [Category.assoc] at s0'
  exact s0'.trans (s1'.trans s2)

/-- `r_ζ = (U(ζ) ⊆ U(χ)) ≫ r_χ ≫ pc`. -/
theorem homOfLE_globalMorphism_changeTarget :
    (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
        (toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≫ changeTargetProj A hs Φ hΦ =
      (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) := by
  have hq : (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι ⁻¹ᵁ
      (toGradedPowerMap χ).coveringOpen = ⊤ := by
    rw [← coveringOpen_changeTarget A hs Φ hΦ χ]
    exact top_unique fun y _ => y.2
  have h1 : liftOfPreimageEqTop _ (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι hq =
      T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le := by
    rw [← cancel_mono (toGradedPowerMap χ).coveringOpen.ι, liftOfPreimageEqTop_ι,
      Scheme.homOfLE_ι]
  have h2 : liftOfPreimageEqTop _ (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι
      ((congrArg (fun U => (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι ⁻¹ᵁ U)
        (coveringOpen_changeTarget A hs Φ hΦ χ)).trans hq) = 𝟙 _ := by
    rw [← cancel_mono (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι,
      liftOfPreimageEqTop_ι, Category.id_comp]
  have key := lift_globalMorphism_changeTarget A hs Φ hΦ χ _ hq
  rw [h1, h2, Category.id_comp] at key
  rw [Category.assoc]
  exact key

/-- **`(U(ζ) ⊆ U(χ))^* r_χ^* 𝒪_{Proj(𝒜₁)}(*) ≅ r_ζ^* 𝒪_{Proj(𝒜)}(*)`**, through the comparison of
twists `pc^*𝒪_{Proj(𝒜)}(*) ≅ 𝒪_{Proj(𝒜₁)}(*)` along `pc`. -/
def thetaChangeSourceIso :
    Stacks.Conormal.gradedPullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)
        (Stacks.Conormal.gradedPullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (GradedPowerMap.twD A₁).algebra) ≅
      Stacks.Conormal.gradedPullback
        ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A))
        (GradedPowerMap.twD A).algebra :=
  pullbackGradedAlgebraMapIso
      (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le).toLRSHom.toShHom
      (pullbackGradedAlgebraMapIso
        ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)).toLRSHom.toShHom
        (RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
          (changeTargetProj A hs Φ hΦ) rfl).symm) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
      (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)
      ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
      (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
        (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
      (changeTargetProj A hs Φ hΦ) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _
      (homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ)

/-- `pc` lies over `hs`. -/
theorem changeTargetProj_comp_toBase :
    changeTargetProj A hs Φ hΦ ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ hs := by
  rw [changeTargetProj, Category.assoc, RelativeProjBaseChangeTwist.baseChangeHom_comp_toBase,
    ← Category.assoc, RelativeProjQcohSheaf.relativeProjCongr_hom_comp_toBase]

/-- `π₁^{-1}(hs^{-1}(V)) ⊆ pc^{-1}(π^{-1}(V))`. -/
theorem preimage_preimage_le_changeTargetProj (V : Y.Opens) :
    (relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V) ≤
      changeTargetProj A hs Φ hΦ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
  have h : changeTargetProj A hs Φ hΦ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) =
      (relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, changeTargetProj_comp_toBase, Scheme.Hom.comp_preimage]
  exact h.ge

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- **The comparison of twists along `pc` on a pulled-back homogeneous section**: it carries the
pullback along `pc` of `ψ_{Proj(𝒜)}(a)` to `ψ_{Proj(𝒜₁)}(Φ^{-1}(hs^*a))`. -/
theorem congrBaseChangeTwistIso_hom_pullbackSection_psiU (d : ℕ) (V : Y.Opens)
    (a : Γ(A.piece (d : ℤ), V)) :
    ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
        (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)).val.app
        (op ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)))
        (pullbackSection (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d)
          ((relativeProj A).toBase ⁻¹ᵁ V) _ (preimage_preimage_le_changeTargetProj A hs Φ hΦ V)
          (GradedPowerMap.psiU A d V a)) =
      GradedPowerMap.psiU A₁ d (hs ⁻¹ᵁ V)
        (((unitalHomInverse Φ hΦ).app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
          (pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a)) := by
  have key := congrArg (fun φ => φ.val.app (op (hs ⁻¹ᵁ V))
      (((unitalHomInverse Φ hΦ).app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
        (pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a)))
    (RelativeProjBaseChangeTwist.congrBaseChangePsi_comp_congrBaseChangeTwistIso A hs Φ hΦ
      (changeTargetProj A hs Φ hΦ) rfl (changeTargetProj_comp_toBase A hs Φ hΦ) d)
  refine Eq.trans ?_ key
  have hΦΦ : (Φ.app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
      (((unitalHomInverse Φ hΦ).app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
        (pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a)) =
      pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a := by
    have := hΦ (d : ℤ)
    change ((inv (Φ.app (d : ℤ)) ≫ Φ.app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))) _ = _
    rw [IsIso.inv_hom_id]
    rfl
  have hb := RelativeProjBaseChangeTwist.basePsi_pullbackSection (relativeProj A).toBase
    (relativeProj A₁).toBase hs (changeTargetProj A hs Φ hΦ)
    (changeTargetProj_comp_toBase A hs Φ hΦ) ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ d)
    V (hs ⁻¹ᵁ V) le_rfl (preimage_preimage_le_changeTargetProj A hs Φ hΦ V) a
  have hb2 : (RelativeProjBaseChangeTwist.basePsi (relativeProj A).toBase (relativeProj A₁).toBase
        hs (changeTargetProj A hs Φ hΦ) (changeTargetProj_comp_toBase A hs Φ hΦ)
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ d)).val.app (op (hs ⁻¹ᵁ V))
        (pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a) =
      pullbackSection (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d)
          ((relativeProj A).toBase ⁻¹ᵁ V) _ (preimage_preimage_le_changeTargetProj A hs Φ hΦ V)
          (GradedPowerMap.psiU A d V a) :=
    (congrArg (fun z => (RelativeProjBaseChangeTwist.basePsi (relativeProj A).toBase
        (relativeProj A₁).toBase hs (changeTargetProj A hs Φ hΦ)
        (changeTargetProj_comp_toBase A hs Φ hΦ)
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ d)).val.app (op (hs ⁻¹ᵁ V)) z)
      (Stacks.Conormal.pullbackSection_self hs (A.piece (d : ℤ)) V a).symm).trans hb
  change _ = ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
        (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)).val.app
        (op ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)))
      ((RelativeProjBaseChangeTwist.basePsi (relativeProj A).toBase (relativeProj A₁).toBase hs
        (changeTargetProj A hs Φ hΦ) (changeTargetProj_comp_toBase A hs Φ hΦ)
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ d)).val.app (op (hs ⁻¹ᵁ V))
        ((Φ.app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
          (((unitalHomInverse Φ hΦ).app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
            (pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a))))
  rw [hΦΦ]
  exact congrArg _ hb2.symm

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- A unital homomorphism out of a base-changed algebra commutes with the transport of the degree
on pulled-back sections. -/
theorem unitalHom_baseUnit_eqToHom {C : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf Y'.toRingedSpace)}
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom
      (baseAlgebra hs (situationAlgebra A)) C) {n m : ℤ} (h : n = m)
    (W : (Opens Y.toRingedSpace.carrier)ᵒᵖ) (x : ((situationAlgebra A).piece n).val.obj W) :
    (Ψ.app m).val.app _ (Twisting.baseUnit hs (situationAlgebra A) m W
        ((eqToHom (congrArg (situationAlgebra A).piece h)).val.app W x)) =
      (eqToHom (congrArg C.piece h)).val.app _
        ((Ψ.app n).val.app _ (Twisting.baseUnit hs (situationAlgebra A) n W x)) := by
  subst h
  rfl

/-- **The value of the changed map on a homogeneous section** is the value of `χ` on its pullback,
read through `Φ^{-1}`. -/
theorem valueSec_changeTarget (d : ℕ) (V : Y.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    valueSec (changeTarget A hs Φ hΦ χ) d V a =
      valueSec χ d (hs ⁻¹ᵁ V)
        (((unitalHomInverse Φ hΦ).app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
          (pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a)) := by
  unfold valueSec changeTarget
  refine congrArg ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L d).inv.app _) ?_
  refine (Twisting.baseChangeUp_sectionHom hs f₀ (situationAlgebra A) 1
    (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ) (d : ℤ) (op V) _).trans ?_
  refine (Twisting.algebraTransport_sectionHom (unitalHomInverse Φ hΦ) χ (d : ℤ) _ _).trans ?_
  exact congrArg (χ.sectionHom (d : ℤ) _)
    (unitalHom_baseUnit_eqToHom A hs (unitalHomInverse Φ hΦ) (mul_one (d : ℤ)).symm (op V) a)

/-- The degree-`d` component of `thetaChangeSourceIso⁻¹ ≫ j^*θ_χ ≫ laurentOnHomOfLEIso`. -/
theorem thetaChange_app (d : ℤ) :
    ((thetaChangeSourceIso A hs Φ hΦ χ).inv ≫
        pullbackGradedAlgebraMap
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le).toLRSHom.toShHom
          (toGradedPowerMap χ).theta ≫
        (laurentOnHomOfLEIso L (coveringOpen_changeTarget A hs Φ hΦ χ).le).hom).app d =
      (((Scheme.Modules.pullbackCongr (homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ)).inv.app
          (GradedPowerMap.Otw A d) ≫
        (Scheme.Modules.pullbackComp
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
            (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (changeTargetProj A hs Φ hΦ)).inv.app (GradedPowerMap.Otw A d)) ≫
        (Scheme.Modules.pullbackComp (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)
          ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).inv.app _ ≫
        (Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
          ((Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).map
            ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
              (changeTargetProj A hs Φ hΦ) rfl).hom.app d))) ≫
      (Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
        (X := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
          (relativeProj A₁))).obj (GradedPowerMap.Otw A₁ d))
        (Y := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece d)
        ((toGradedPowerMap χ).theta.app d) ≫
      (laurentOnHomOfLEPieceIso L (coveringOpen_changeTarget A hs Φ hΦ χ).le d).hom := by
  simp only [thetaChangeSourceIso, laurentOnHomOfLEIso,
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso,
    SheafOfModules.GradedAlgebra.categoryStruct_comp_app, Category.assoc]
  rfl

/-- The open `r_ζ^{-1}(π^{-1}(V))` lies over `π₁^{-1}(hs^{-1}(V))` along `U(ζ) ⊆ U(χ)` and
`r_χ`. -/
theorem preimage_le_changeTarget (V : Y.Opens) :
    (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ⁻¹ᵁ
        ((toGradedPowerMap χ).globalMorphism (relativeProj A₁) ⁻¹ᵁ
          ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V))) := by
  have hr := homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ
  have h1 : (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      ((T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
        (toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≫
        changeTargetProj A hs Φ hΦ) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
    rw [hr]
  refine h1.trans ?_
  rw [Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage (changeTargetProj A hs Φ hΦ),
    changeTargetProj_comp_toBase, Scheme.Hom.comp_preimage]
  exact le_rfl

/-- The section `Φ^{-1}(hs^*a)` of `𝒜₁` over `hs^{-1}(V)`. -/
abbrev changeTargetSection (d : ℕ) (V : Y.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    Γ(A₁.piece (d : ℤ), hs ⁻¹ᵁ V) :=
  ((unitalHomInverse Φ hΦ).app (d : ℤ)).val.app (op (hs ⁻¹ᵁ V))
    (pullbackUnit hs.toLRSHom.toShHom (A.piece (d : ℤ)) (op V) a)

/-- **The chase of a pulled-back homogeneous section** through the four factors of
`thetaChangeSourceIso⁻¹ ≫ j^*θ_χ ≫ laurentOnHomOfLEIso`. -/
theorem thetaChange_app_pullbackUnit (d : ℕ) (V : Y.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    (laurentOnHomOfLEPieceIso L (coveringOpen_changeTarget A hs Φ hΦ χ).le (d : ℤ)).hom.val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
          (X := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
            (relativeProj A₁))).obj (GradedPowerMap.Otw A₁ d))
          (Y := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece (d : ℤ))
          ((toGradedPowerMap χ).theta.app (d : ℤ))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
          ((Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).map
            ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
              (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackComp (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)
          ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).inv.app
          ((Scheme.Modules.pullback (changeTargetProj A hs Φ hΦ)).obj
            (GradedPowerMap.Otw A d))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackComp
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
            (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (changeTargetProj A hs Φ hΦ)).inv.app (GradedPowerMap.Otw A d)).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackCongr (homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ)).inv.app
          (GradedPowerMap.Otw A d)).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (pullbackUnit
        ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism
          (relativeProj A)).toLRSHom.toShHom
        (GradedPowerMap.Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
        (GradedPowerMap.psiU A d V a))))))) =
      (tensorPowerModule T L d).val.map
        (homOfLE (image_le_image_of_le_preimage_homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le
          _ (preimage_le_changeTarget A hs Φ hΦ χ V))).op
        (((toGradedPowerMap χ).thetaPush (d : ℤ)).app ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V))
          (((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
            (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)).val.app
            (op ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)))
            (pullbackSection (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d)
              ((relativeProj A).toBase ⁻¹ᵁ V) _ (preimage_preimage_le_changeTargetProj A hs Φ hΦ V)
              (GradedPowerMap.psiU A d V a)))) := by
  have hle := (coveringOpen_changeTarget A hs Φ hΦ χ).le
  have hr := homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ
  have hf' := preimage_le_changeTarget A hs Φ hΦ χ V
  have hf : (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      (T.homOfLE hle ≫ (toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ⁻¹ᵁ
        ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)) := hf'
  have h1 : (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      ((T.homOfLE hle ≫ (toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≫
        changeTargetProj A hs Φ hΦ) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) := by
    rw [hr]
  have e0 : pullbackUnit
        ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism
          (relativeProj A)).toLRSHom.toShHom
        (GradedPowerMap.Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
        (GradedPowerMap.psiU A d V a) =
      pullbackSection ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism
          (relativeProj A)) (GradedPowerMap.Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) _ le_rfl
        (GradedPowerMap.psiU A d V a) :=
    (Stacks.Conormal.pullbackSection_self
      ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A))
      (GradedPowerMap.Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V) (GradedPowerMap.psiU A d V a)).symm
  have e1 := pullbackSection_congr_inv hr (GradedPowerMap.Otw A d)
    ((relativeProj A).toBase ⁻¹ᵁ V) _ h1 le_rfl (GradedPowerMap.psiU A d V a)
  have e2 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
    (T.homOfLE hle ≫ (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
    (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d) ((relativeProj A).toBase ⁻¹ᵁ V)
    ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)) _
    (preimage_preimage_le_changeTargetProj A hs Φ hΦ V) hf h1 (GradedPowerMap.psiU A d V a)
  have e3 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection
    (T.homOfLE hle) ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))
    ((Scheme.Modules.pullback (changeTargetProj A hs Φ hΦ)).obj (GradedPowerMap.Otw A d))
    ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)) _ _ le_rfl hf' hf
    (pullbackSection (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d)
      ((relativeProj A).toBase ⁻¹ᵁ V) _ (preimage_preimage_le_changeTargetProj A hs Φ hΦ V)
      (GradedPowerMap.psiU A d V a))
  have e4 := Scheme.Modules.pullbackSection_naturality (T.homOfLE hle)
    (F := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).obj
      ((Scheme.Modules.pullback (changeTargetProj A hs Φ hΦ)).obj (GradedPowerMap.Otw A d)))
    (G := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).obj
      (GradedPowerMap.Otw A₁ d))
    ((Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).map
      ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
        (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ))) _ _ hf'
    (pullbackSection ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))
      ((Scheme.Modules.pullback (changeTargetProj A hs Φ hΦ)).obj (GradedPowerMap.Otw A d))
      ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)) _ le_rfl
      (pullbackSection (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d)
        ((relativeProj A).toBase ⁻¹ᵁ V) _ (preimage_preimage_le_changeTargetProj A hs Φ hΦ V)
        (GradedPowerMap.psiU A d V a)))
  have e5 := Scheme.Modules.pullbackSection_naturality
    ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))
    (F := (Scheme.Modules.pullback (changeTargetProj A hs Φ hΦ)).obj (GradedPowerMap.Otw A d))
    (G := GradedPowerMap.Otw A₁ d)
    ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
        (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)) _ _ le_rfl
    (pullbackSection (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d)
      ((relativeProj A).toBase ⁻¹ᵁ V) _ (preimage_preimage_le_changeTargetProj A hs Φ hΦ V)
      (GradedPowerMap.psiU A d V a))
  rw [e0, e1, e2, e3]
  refine (congrArg (fun z => (laurentOnHomOfLEPieceIso L hle (d : ℤ)).hom.val.app
      (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (T.homOfLE hle)).map
          (X := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
            (relativeProj A₁))).obj (GradedPowerMap.Otw A₁ d))
          (Y := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece (d : ℤ))
          ((toGradedPowerMap χ).theta.app (d : ℤ))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V))) z)) e4).trans ?_
  refine (congrArg (fun z => (laurentOnHomOfLEPieceIso L hle (d : ℤ)).hom.val.app
      (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (T.homOfLE hle)).map
          (X := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
            (relativeProj A₁))).obj (GradedPowerMap.Otw A₁ d))
          (Y := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece (d : ℤ))
          ((toGradedPowerMap χ).theta.app (d : ℤ))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
        (pullbackSection (T.homOfLE hle)
          ((Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).obj
            (GradedPowerMap.Otw A₁ d))
          ((toGradedPowerMap χ).globalMorphism (relativeProj A₁) ⁻¹ᵁ
            ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V))) _ hf' z))) e5).trans ?_
  have key := laurentOnHomOfLE_theta_pullbackSection χ hle (d : ℤ)
    ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)) _ hf'
    (((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
            (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)).val.app
            (op ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V)))
            (pullbackSection (changeTargetProj A hs Φ hΦ) (GradedPowerMap.Otw A d)
              ((relativeProj A).toBase ⁻¹ᵁ V) _ (preimage_preimage_le_changeTargetProj A hs Φ hΦ V)
              (GradedPowerMap.psiU A d V a)))
  with_reducible_and_instances exact key

attribute [local irreducible] laurentOnHomOfLEPieceIso

/-- `thetaChangeSourceIso⁻¹ ≫ j^*θ_χ ≫ laurentOnHomOfLEIso` in degree `d`, on a pulled-back
section, as its factors applied in turn. -/
theorem thetaChange_comp_apply (d : ℕ) (V : Y.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    ((((Scheme.Modules.pullbackCongr (homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ)).inv.app
          (GradedPowerMap.Otw A d) ≫
        (Scheme.Modules.pullbackComp
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
            (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (changeTargetProj A hs Φ hΦ)).inv.app (GradedPowerMap.Otw A d)) ≫
        (Scheme.Modules.pullbackComp (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)
          ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).inv.app
          ((Scheme.Modules.pullback (changeTargetProj A hs Φ hΦ)).obj (GradedPowerMap.Otw A d)) ≫
        (Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
          ((Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).map
            ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
              (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)))) ≫
      (Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
        (X := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
          (relativeProj A₁))).obj (GradedPowerMap.Otw A₁ d))
        (Y := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece (d : ℤ))
        ((toGradedPowerMap χ).theta.app (d : ℤ)) ≫
      (laurentOnHomOfLEPieceIso L (coveringOpen_changeTarget A hs Φ hΦ χ).le (d : ℤ)).hom).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (pullbackUnit
        ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism
          (relativeProj A)).toLRSHom.toShHom
        (GradedPowerMap.Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
        (GradedPowerMap.psiU A d V a)) =
    (laurentOnHomOfLEPieceIso L (coveringOpen_changeTarget A hs Φ hΦ χ).le (d : ℤ)).hom.val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
          (X := (Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism
            (relativeProj A₁))).obj (GradedPowerMap.Otw A₁ d))
          (Y := (laurentOn L (toGradedPowerMap χ).coveringOpen).piece (d : ℤ))
          ((toGradedPowerMap χ).theta.app (d : ℤ))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)).map
          ((Scheme.Modules.pullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).map
            ((RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
              (changeTargetProj A hs Φ hΦ) rfl).hom.app (d : ℤ)))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackComp (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)
          ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))).inv.app
          ((Scheme.Modules.pullback (changeTargetProj A hs Φ hΦ)).obj
            (GradedPowerMap.Otw A d))).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackComp
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
            (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (changeTargetProj A hs Φ hΦ)).inv.app (GradedPowerMap.Otw A d)).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (((Scheme.Modules.pullbackCongr (homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ)).inv.app
          (GradedPowerMap.Otw A d)).val.app
        (op ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism (relativeProj A) ⁻¹ᵁ
          ((relativeProj A).toBase ⁻¹ᵁ V)))
      (pullbackUnit
        ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).globalMorphism
          (relativeProj A)).toLRSHom.toShHom
        (GradedPowerMap.Otw A d) (op ((relativeProj A).toBase ⁻¹ᵁ V))
        (GradedPowerMap.psiU A d V a))))))) := rfl

/-- **`θ_ζ = θ_χ` under a change of the target.**  For the map `ζ` obtained from `χ` by
`changeTarget`, the map `θ_ζ : r_ζ^*(⨁_d 𝒪_{Proj_Y(𝒜)}(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ζ)}` of
[Stacks, Tag 01O9] is the inverse image of `θ_χ` along `U(ζ) = U(χ)`, read through the
comparison of twists along `pc = Proj(Φ) ≫ (Proj_{Y'}(hs^*𝒜) ⟶ Proj_Y(𝒜))`
(`thetaChangeSourceIso`) and the identification `laurentOnHomOfLEIso` of the targets. -/
theorem theta_changeTarget :
    (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).theta =
      (thetaChangeSourceIso A hs Φ hΦ χ).inv ≫
        pullbackGradedAlgebraMap
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le).toLRSHom.toShHom
          (toGradedPowerMap χ).theta ≫
        (laurentOnHomOfLEIso L (coveringOpen_changeTarget A hs Φ hΦ χ).le).hom := by
  refine ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).eq_theta_of_clauseOne
    fun V d a => ?_).symm
  rw [thetaChange_app]
  have m1 := thetaChange_comp_apply A hs Φ hΦ χ d V a
  have m2 := thetaChange_app_pullbackUnit A hs Φ hΦ χ d V a
  have e6 := congrBaseChangeTwistIso_hom_pullbackSection_psiU A hs Φ hΦ d V a
  have e9 := (toGradedPowerMap χ).thetaPush_psiU (hs ⁻¹ᵁ V) d
    (changeTargetSection A hs Φ hΦ d V a)
  have hv : (toGradedPowerMap (changeTarget A hs Φ hΦ χ)).value d V a =
      (toGradedPowerMap χ).value d (hs ⁻¹ᵁ V) (changeTargetSection A hs Φ hΦ d V a) :=
    (toGradedPowerMap_value _ d V a).trans ((valueSec_changeTarget A hs Φ hΦ χ d V a).trans
      (toGradedPowerMap_value _ d _ _).symm)
  refine (congrArg (((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).powK d).presheaf.map
    (eqToHom ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).toBase_preimage_eq V)).op)
    (m1.trans m2)).trans ?_
  refine (congrArg (fun z => ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).powK d).presheaf.map
    (eqToHom ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).toBase_preimage_eq V)).op
    ((tensorPowerModule T L d).val.map
      (homOfLE (image_le_image_of_le_preimage_homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le
        _ (preimage_le_changeTarget A hs Φ hΦ χ V))).op
      (((toGradedPowerMap χ).thetaPush (d : ℤ)).app ((relativeProj A₁).toBase ⁻¹ᵁ (hs ⁻¹ᵁ V))
        z))) e6).trans ?_
  refine (congrArg (fun z => ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).powK d).presheaf.map
    (eqToHom ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).toBase_preimage_eq V)).op
    ((tensorPowerModule T L d).val.map
      (homOfLE (image_le_image_of_le_preimage_homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le
        _ (preimage_le_changeTarget A hs Φ hΦ χ V))).op z)) e9).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (tensorPowerModule T L d).presheaf.map
    (homOfLE ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι.image_preimage_le
      ((f₀ ≫ hs) ⁻¹ᵁ V))).op
    ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L d).hom.app ((f₀ ≫ hs) ⁻¹ᵁ V) z))
    hv).symm
  exact map_map3 (tensorPowerModule T L d)
    (homOfLE ((toGradedPowerMap χ).image_preimage_preimage_le (hs ⁻¹ᵁ V))).op
    (homOfLE (image_le_image_of_le_preimage_homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le
      _ (preimage_le_changeTarget A hs Φ hΦ χ V))).op
    ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι.opensFunctor.map
      (eqToHom ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).toBase_preimage_eq V))).op
    (homOfLE ((toGradedPowerMap (changeTarget A hs Φ hΦ χ)).coveringOpen.ι.image_preimage_le
      ((f₀ ≫ hs) ⁻¹ᵁ V))).op
    ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L d).hom.app (f₀ ⁻¹ᵁ (hs ⁻¹ᵁ V))
      ((toGradedPowerMap χ).value d (hs ⁻¹ᵁ V) (changeTargetSection A hs Φ hΦ d V a)))

end Change

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end

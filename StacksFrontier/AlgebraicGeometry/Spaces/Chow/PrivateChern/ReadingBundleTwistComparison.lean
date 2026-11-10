module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleTwistPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesRightExactSequence

/-!
# The comparison of a reading bundle with the projective bundle pulls back the twist

Let `ℰ` be a finite locally free module on an algebraic space `X`, `π : 𝐏(ℰ) ⟶ X` its projective
bundle with tautological quotient `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`, and `ψ : T ⟶ X` a morphism from a scheme.
The comparison `κ : 𝐏(ℰ_ψ) ⟶ 𝐏(ℰ)` over `ψ`, from the projective bundle of the reading of `ℰ` on
`T`, pulls the tautological quotient of `𝐏(ℰ)` back to the tautological quotient of `𝐏(ℰ_ψ)`,
up to an isomorphism of the targets: `κ^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ_ψ)}(1)` compatibly with the quotients
of `κ^*π^*ℰ = ℰ_ψ` pulled back to `𝐏(ℰ_ψ)`.

Both are quotients of the same module, so it suffices to compare them after the étale surjective
cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_ψ)` with `T' = T ×_X U` for the presenting chart `U` of `X`. There `κ`
factors through the presenting chart bundle `𝐏(ℰ_U)` of `𝐏(ℰ)`, on which the tautological quotient
of `𝐏(ℰ)` restricts to the tautological quotient of `𝐏(ℰ_U)`, and the two quotients are both the
base change of a tautological quotient (Stacks 01O3).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.exists_iso_readingBundleSpaceMap_quotient`: the comparison
  `𝐏(ℰ_ψ) ⟶ 𝐏(ℰ)` pulls the tautological quotient back to the tautological quotient.

## Implementation notes

The presenting chart bundle of `𝐏(ℰ)` is the reading bundle over the presenting chart by
definition, but the two descriptions are unfolded only at the level of their objects and
morphisms: the comparisons of composites are taken factor by factor, and the morphisms into and
out of the chart are named once (`bundleCoverAtlasMap`, `bundleCoverMap`) with the algebraic
spaces they are read between. The constructions of the projective bundles of schemes and of the
inverse images of modules are not unfolded in this file.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

attribute [local irreducible] AlgebraicGeometry.Space.modulePullback
  Stacks.RelativeProj.symmetricSituationOfQuasicoherent
  Stacks.RelativeProj.symmetricSituation
  Stacks.RelativeProj.Situation.relativeProj
  Stacks.RelativeProj.Data.relativeProj
  SheafOfModules.sheafifiedSymmetricAlgebra
  presheafToSheaf
  Stacks.RelativeProj.Situation.relativeProjToBase
  Stacks.RelativeProj.Data.toBase
  AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace
  AlgebraicGeometry.Space.presentationOfAtlas
  AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison
  AlgebraicGeometry.Space.modulePullbackCompIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The reading bundle over the presenting chart lies over `X` as the presenting chart bundle
does. -/
theorem readingBundleSiteToBase_chart_comp :
    representedSpaceMap B S hS
        (readingBundleSiteToBase E hfree (chartToSpace B S hS X (bundleBaseChart X))) ≫
        chartToSpace B S hS X (bundleBaseChart X) =
      projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree :=
  representedSpaceMap_projectiveBundleChartProj_comp E hfree

/-- The chart quotient of `𝐏(ℰ)` reads as the tautological quotient of the reading bundle over the
presenting chart. -/
theorem quotientReadingHyp_projectiveBundle_reading :
    QuotientReadingHyp E hE (readingBundleSiteToBase_chart_comp E hfree)
      (Stacks.RelativeProj.tautologicalDatumUniv
        (schemeReading E (chartToSpace B S hS X (bundleBaseChart X))))
      (projectiveBundleChartTwistReadingIso E hfree)
      (projectiveBundleChartQuotient E hfree)
      (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
        (projectiveBundleProj E hfree) _ rfl E).symm :=
  quotientReadingHyp_projectiveBundle E hfree

/-- A chain of five factorizations through isomorphisms. -/
theorem exists_iso_comp_eq_of_chain {C : Type*} [Category C]
    {P a₀' a₁ a₂ a₃ a₄ a₅ : C}
    {s₀ : P ⟶ a₀'} {s₁ : P ⟶ a₁} {s₂ : P ⟶ a₂} {s₃ : P ⟶ a₃} {s₄ : P ⟶ a₄} {s₅ : P ⟶ a₅}
    (x₁ : a₀' ≅ a₁) (x₂ : a₁ ≅ a₂) (x₃ : a₂ ≅ a₃) (x₄ : a₃ ≅ a₄) (x₅ : a₄ ≅ a₅)
    (h₁ : s₀ ≫ x₁.hom = s₁) (h₂ : s₁ ≫ x₂.hom = s₂) (h₃ : s₂ ≫ x₃.hom = s₃)
    (h₄ : s₃ ≫ x₄.hom = s₄) (h₅ : s₄ ≫ x₅.hom = s₅) :
    ∃ θ : a₀' ≅ a₅, s₀ ≫ θ.hom = s₅ := by
  refine ⟨x₁ ≪≫ x₂ ≪≫ x₃ ≪≫ x₄ ≪≫ x₅, ?_⟩
  simp only [Iso.trans_hom]
  rw [← h₅, ← h₄, ← h₃, ← h₂, ← h₁]
  simp only [Category.assoc]

/-- Composites agree as soon as their factors do, read through equal objects. -/
theorem comp_eq_comp_of_heq {C : Type*} [Category C] {P Q Q' R R' : C} (a : P ⟶ Q)
    (a' : P ⟶ Q')
    (b : Q ⟶ R) (b' : Q' ⟶ R') (hQ : Q = Q') (hR : R = R') (ha : HEq a a') (hb : HEq b b') :
    HEq (a ≫ b) (a' ≫ b') := by
  subst hQ hR
  cases ha
  cases hb
  rfl

/-- The morphism `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U)` into the presenting chart, between the algebraic spaces as
which the cover and the presentation of `𝐏(ℰ)` are read. -/
abbrev bundleCoverAtlasMap {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    representedAlgebraicSpace B S hS (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶
      (projectiveBundleGroupoid E hfree).objects :=
  representedSpaceMap B S hS (bundleCoverToAtlas E hfree ψ)

/-- The cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_ψ)`, between the represented algebraic spaces. -/
abbrev bundleCoverMap {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    representedAlgebraicSpace B S hS (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶
      representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) :=
  representedSpaceMap B S hS (bundleCover ψ E hfree)

/-- **Stacks 01O3 along `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U)` into the presenting chart of `𝐏(ℰ)`**: the inverse
image of the chart quotient is the tautological quotient of `𝐏(ℰ_{T'})`, up to an isomorphism of
the targets. -/
theorem exists_iso_bundleCoverAtlasMap_projectiveBundleChartQuotient {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {vT : representedAlgebraicSpace B S hS
      (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶ X}
    (hvT : representedSpaceMap B S hS
      (readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ)) ≫ chartBaseChangeToSpace ψ = vT)
    (hm : bundleCoverAtlasMap E hfree ψ ≫
      (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) = vT) :
    ∃ θ : (modulePullback B S hS (bundleCoverAtlasMap E hfree ψ)).obj
        (projectiveBundleChartTwist E hfree) ≅
        readingBundleTwist E hfree (chartBaseChangeToSpace ψ),
      ((QuasiCoherentDescent.pullbackComparison B S hS (bundleCoverAtlasMap E hfree ψ)
          (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) vT hm E).hom ≫
        (modulePullback B S hS (bundleCoverAtlasMap E hfree ψ)).map
          ((QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
            (projectiveBundleProj E hfree) _ rfl E).symm.inv ≫
            projectiveBundleChartQuotient E hfree)) ≫ θ.hom =
        (Iso.refl _).inv ≫ readingBundleQuotient E hfree (chartBaseChangeToSpace ψ) hvT := by
  obtain ⟨θ, e⟩ := exists_iso_readingBundleSiteMap_quotient E hfree (chartBaseChangeToChart ψ)
    (chartBaseChange_w ψ) (readingBundleSiteToBase_chart_comp E hfree) hvT hm
    (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree)
    (projectiveBundleChartQuotient E hfree)
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl E).symm
    (projectiveBundleChartTwistReadingIso E hfree)
    (quotientReadingHyp_projectiveBundle_reading E hfree)
    (isQuasicoherentOnSite_readingBundleTwist E hfree _)
    (readingBundleQuotient E hfree (chartBaseChangeToSpace ψ) hvT) (Iso.refl _)
    (readingBundleTwistReadingIso E hfree _)
    (quotientReadingHyp_readingBundleQuotient E hfree (chartBaseChangeToSpace ψ) hvT)
  refine ⟨θ, Eq.trans ?_ (e.trans ?_)⟩
  · congr! (config := { closePre := false, closePost := false }) 1
    · rfl
    · refine eq_of_heq (comp_eq_comp_of_heq _ _ _ _ ?_ ?_ ?_ ?_)
      · rfl
      · rfl
      · exact HEq.rfl
      · exact HEq.rfl
    · rfl
  · refine eq_of_heq (comp_eq_comp_of_heq _ _ _ _ ?_ ?_ ?_ ?_)
    · rfl
    · rfl
    · exact HEq.rfl
    · exact HEq.rfl

/-- **The comparison `𝐏(ℰ_ψ) ⟶ 𝐏(ℰ)` pulls the tautological quotient back to the tautological
quotient, after the cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_ψ)`.** -/
theorem exists_iso_readingBundleSpaceMap_quotient_cover {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    (hκ : readingBundleSpaceMap E hfree ψ ≫ projectiveBundleProj E hfree = v)
    {vT : representedAlgebraicSpace B S hS
      (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶ X}
    (h₁ : bundleCoverMap E hfree ψ ≫ v = vT)
    (hvT : representedSpaceMap B S hS
      (readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ)) ≫ chartBaseChangeToSpace ψ =
        vT) :
    ∃ θ : (modulePullback B S hS (bundleCoverMap E hfree ψ)).obj
          ((modulePullback B S hS (readingBundleSpaceMap E hfree ψ)).obj
            (projectiveBundleTwist E hfree).obj) ≅
        readingBundleTwist E hfree (chartBaseChangeToSpace ψ),
      ((QuasiCoherentDescent.pullbackComparison B S hS (bundleCoverMap E hfree ψ) v vT h₁ E).hom ≫
        (modulePullback B S hS (bundleCoverMap E hfree ψ)).map
          ((QuasiCoherentDescent.pullbackComparison B S hS (readingBundleSpaceMap E hfree ψ)
              (projectiveBundleProj E hfree) v hκ E).hom ≫
            (modulePullback B S hS (readingBundleSpaceMap E hfree ψ)).map
              (projectiveBundleTautological E hfree).hom)) ≫ θ.hom =
        (Iso.refl _).inv ≫ readingBundleQuotient E hfree (chartBaseChangeToSpace ψ) hvT := by
  have hcm : bundleCoverMap E hfree ψ ≫ readingBundleSpaceMap E hfree ψ =
      bundleCoverAtlasMap E hfree ψ ≫ projectiveBundleAtlas E hfree :=
    representedSpaceMap_bundleCover_comp_readingBundleSpaceMap E hfree ψ
  have h1' : (bundleCoverMap E hfree ψ ≫ readingBundleSpaceMap E hfree ψ) ≫
      projectiveBundleProj E hfree = vT := by
    rw [Category.assoc, hκ, h₁]
  have hm' : (bundleCoverAtlasMap E hfree ψ ≫ projectiveBundleAtlas E hfree) ≫
      projectiveBundleProj E hfree = vT :=
    (congrArg (· ≫ projectiveBundleProj E hfree) hcm).symm.trans h1'
  have hm : bundleCoverAtlasMap E hfree ψ ≫
      (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) = vT :=
    (Category.assoc _ _ _).symm.trans hm'
  have e1 := pullbackComparison_hom_comp_map_pullbackComparison_hom_comp_map E
    (bundleCoverMap E hfree ψ) (readingBundleSpaceMap E hfree ψ) hκ h₁ h1'
    (projectiveBundleTautological E hfree).hom
  obtain ⟨θ₂, e2⟩ := exists_iso_pullbackComparison_hom_comp_map_of_eq E hcm h1' hm'
    (projectiveBundleTautological E hfree).hom
  have e3 := pullbackComparison_hom_comp_map_pullbackComparison_hom_comp_map E
    (bundleCoverAtlasMap E hfree ψ) (projectiveBundleAtlas E hfree) rfl hm hm'
    (projectiveBundleTautological E hfree).hom
  have e3' := comp_inv_app_eq_of_comp_hom_app_eq (modulePullbackCompIso B S hS
    (bundleCoverAtlasMap E hfree ψ) (projectiveBundleAtlas E hfree))
    (projectiveBundleTwist E hfree).obj _ _ e3
  obtain ⟨θ₄, e4⟩ := exists_iso_pullbackComparison_hom_comp_map_of_exists_iso E
    (bundleCoverAtlasMap E hfree ψ) hm (exists_iso_projectiveBundleTautological_atlas E hfree)
  obtain ⟨θ₅, e5⟩ := exists_iso_bundleCoverAtlasMap_projectiveBundleChartQuotient E hfree ψ hvT hm
  exact exists_iso_comp_eq_of_chain
    ((modulePullbackCompIso B S hS (bundleCoverMap E hfree ψ)
      (readingBundleSpaceMap E hfree ψ)).app (projectiveBundleTwist E hfree).obj) θ₂
    ((modulePullbackCompIso B S hS (bundleCoverAtlasMap E hfree ψ)
      (projectiveBundleAtlas E hfree)).app (projectiveBundleTwist E hfree).obj).symm θ₄ θ₅
    e1 e2 e3' e4 e5

/-- **Stacks 01O3 along the cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_ψ)`**, read through `bundleCoverMap`. -/
theorem exists_iso_bundleCoverMap_readingBundleQuotient {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ = v)
    {vT : representedAlgebraicSpace B S hS
      (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶ X}
    (h₁ : bundleCoverMap E hfree ψ ≫ v = vT)
    (hvT : representedSpaceMap B S hS
      (readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ)) ≫ chartBaseChangeToSpace ψ =
        vT) :
    ∃ θ : (modulePullback B S hS (bundleCoverMap E hfree ψ)).obj (readingBundleTwist E hfree ψ) ≅
        readingBundleTwist E hfree (chartBaseChangeToSpace ψ),
      ((QuasiCoherentDescent.pullbackComparison B S hS (bundleCoverMap E hfree ψ) v vT h₁ E).hom ≫
        (modulePullback B S hS (bundleCoverMap E hfree ψ)).map
          ((Iso.refl _).inv ≫ readingBundleQuotient E hfree ψ hv)) ≫ θ.hom =
        (Iso.refl _).inv ≫ readingBundleQuotient E hfree (chartBaseChangeToSpace ψ) hvT := by
  obtain ⟨θ, e⟩ := exists_iso_readingBundleSiteMap_quotient E hfree (chartBaseChangeToBase ψ)
    (ψ := ψ) rfl hv hvT h₁ (isQuasicoherentOnSite_readingBundleTwist E hfree ψ)
    (readingBundleQuotient E hfree ψ hv) (Iso.refl _) (readingBundleTwistReadingIso E hfree ψ)
    (quotientReadingHyp_readingBundleQuotient E hfree ψ hv)
    (isQuasicoherentOnSite_readingBundleTwist E hfree _)
    (readingBundleQuotient E hfree (chartBaseChangeToSpace ψ) hvT) (Iso.refl _)
    (readingBundleTwistReadingIso E hfree _)
    (quotientReadingHyp_readingBundleQuotient E hfree (chartBaseChangeToSpace ψ) hvT)
  refine ⟨θ, Eq.trans ?_ (e.trans ?_)⟩
  · refine eq_of_heq (comp_eq_comp_of_heq _ _ _ _ ?_ ?_ ?_ ?_)
    · rfl
    · rfl
    · refine comp_eq_comp_of_heq _ _ _ _ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · exact HEq.rfl
      · exact HEq.rfl
    · exact HEq.rfl
  · refine eq_of_heq (comp_eq_comp_of_heq _ _ _ _ ?_ ?_ ?_ ?_) <;> rfl

/-- The inverse of an isomorphism is an epimorphism. -/
private theorem epi_inv_of_iso {C : Type*} [Category C] {a b : C} (e : a ≅ b) : Epi e.inv :=
  inferInstance

/-- Two factorizations of one morphism through the same isomorphism `P` agree after it. -/
theorem comp_hom_eq_of_iso_comp {C : Type*} [Category C] {M' M A A' Z : C} (P : M' ≅ M)
    (a : M ⟶ A) (b : M ⟶ A') (θ₁ : A ≅ Z) (θ₂ : A' ≅ Z) {z : M' ⟶ Z}
    (h₁ : (P.hom ≫ a) ≫ θ₁.hom = z) (h₂ : (P.hom ≫ b) ≫ θ₂.hom = z) :
    a ≫ (θ₁ ≪≫ θ₂.symm).hom = b := by
  rw [← cancel_epi P.hom, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ← Category.assoc, h₁,
    ← h₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The reading bundle over `T'` lies over `X` through the cover of `𝐏(ℰ_ψ)`. -/
theorem representedSpaceMap_readingBundleSiteToBase_comp_chartBaseChangeToSpace
    {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    representedSpaceMap B S hS (readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ)) ≫
        chartBaseChangeToSpace ψ =
      bundleCoverMap E hfree ψ ≫
        (representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ) := by
  have h := congrArg (fun k => (schemeSpaceFunctor B S hS).map k ≫ ψ)
    (isPullback_readingBundleSiteMap E hfree (chartBaseChangeToBase ψ) (ψ := ψ) rfl).w
  simp only [Functor.map_comp] at h
  exact h.symm

/-- **The comparison `κ : 𝐏(ℰ_ψ) ⟶ 𝐏(ℰ)` over `ψ : T ⟶ X` pulls the tautological quotient of
`𝐏(ℰ)` back to the tautological quotient of `𝐏(ℰ_ψ)`**, up to an isomorphism of the targets. -/
theorem exists_iso_readingBundleSpaceMap_quotient {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {v : representedAlgebraicSpace B S hS (readingBundleSite E hfree ψ) ⟶ X}
    (hκ : readingBundleSpaceMap E hfree ψ ≫ projectiveBundleProj E hfree = v)
    (hv : representedSpaceMap B S hS (readingBundleSiteToBase E hfree ψ) ≫ ψ = v) :
    ∃ θ : (modulePullback B S hS (readingBundleSpaceMap E hfree ψ)).obj
        (projectiveBundleTwist E hfree).obj ≅ readingBundleTwist E hfree ψ,
      ((QuasiCoherentDescent.pullbackComparison B S hS (readingBundleSpaceMap E hfree ψ)
          (projectiveBundleProj E hfree) v hκ E).hom ≫
        (modulePullback B S hS (readingBundleSpaceMap E hfree ψ)).map
          (projectiveBundleTautological E hfree).hom) ≫ θ.hom =
        (Iso.refl _).inv ≫ readingBundleQuotient E hfree ψ hv := by
  have h₁ : bundleCoverMap E hfree ψ ≫ v = bundleCoverMap E hfree ψ ≫ v := rfl
  have hvT : representedSpaceMap B S hS
      (readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ)) ≫ chartBaseChangeToSpace ψ =
      bundleCoverMap E hfree ψ ≫ v := by
    rw [representedSpaceMap_readingBundleSiteToBase_comp_chartBaseChangeToSpace, hv]
  obtain ⟨θ₁, eK⟩ := exists_iso_readingBundleSpaceMap_quotient_cover E hfree ψ hκ h₁ hvT
  obtain ⟨θ₂, eR⟩ := exists_iso_bundleCoverMap_readingBundleQuotient E hfree ψ hv h₁ hvT
  have hloc := comp_hom_eq_of_iso_comp _ _ _ θ₁ θ₂ eK eR
  have hflat : IsFlat B S hS (bundleCoverMap E hfree ψ).hom :=
    isFlat_of_isEtale B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2
      (presheaf_etale_bundleCover ψ E hfree))
  have hsurj : IsJointlySurjective B S hS (fun _ : Unit =>
      (representedAlgebraicSpace B S hS (readingBundleSite E hfree (chartBaseChangeToSpace ψ))).1)
      (fun _ => (bundleCoverMap E hfree ψ).hom) :=
    (isJointlySurjective_const_iff B S hS _).2
      ((surjective_iff_surjective_pointsMap B S hS _ (isAlgebraicSpace_yoneda B S hS _) _ _).1
        (presheaf_surjective_bundleCover ψ E hfree))
  have hepi : Epi ((Iso.refl _).inv ≫ readingBundleQuotient E hfree ψ hv) := by
    refine epi_of_epi_representedZariski_map (isQuasicoherentOnSite_readingBundleTwist E hfree ψ)
      _ ?_
    change Epi ((readingFunctor (readingBundleSite E hfree ψ)).map _)
    rw [readingFunctor_map_inv_comp_readingBundleQuotient E hfree ψ hv]
    exact epi_comp' (epi_comp' (epi_inv_of_iso _)
      (Stacks.RelativeProj.epi_tautologicalDatumUniv _)) (epi_inv_of_iso _)
  have hepi' : Epi ((QuasiCoherentDescent.pullbackComparison B S hS
      (readingBundleSpaceMap E hfree ψ) (projectiveBundleProj E hfree) v hκ E).hom ≫
      (modulePullback B S hS (readingBundleSpaceMap E hfree ψ)).map
        (projectiveBundleTautological E hfree).hom) :=
    epi_comp' (IsIso.epi_of_iso _) (epi_modulePullback_map B S hS
      (readingBundleSpaceMap E hfree ψ) (projectiveBundleTautological E hfree).hom
      (epi_projectiveBundleTautological E hfree))
  obtain ⟨e, he⟩ := exists_iso_comp_eq_of_modulePullback (fun _ : Unit => bundleCoverMap E hfree ψ)
    (fun _ => hflat) hsurj _ _ (fun _ => ⟨_, hloc⟩)
  exact ⟨e, he⟩

end AlgebraicGeometry.Space.PrivateChern

end

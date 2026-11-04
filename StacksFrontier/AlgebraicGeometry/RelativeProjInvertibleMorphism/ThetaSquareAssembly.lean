module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaTargetChange

/-!
# The map `θ` of Tag 01O9 under rereading the base, and around a square

This file collects what is needed, beyond the comparison of `θ` under a change of the target
(`…RelativeProjInvertibleMorphism.theta_changeTarget`) and under base change of the source
(`…RelativeProjInvertibleMorphism.theta_pullback`), to compare the maps `θ` of
[Stacks, Tag 01O9] around a commutative square, as in the last assertion of clause (3) of
[Stacks, Tag 0D2Z].

* `…RelativeProjInvertibleMorphism.theta_changeTarget_of_eq`,
  `…RelativeProjInvertibleMorphism.theta_pullback_of_eq`: the two comparisons for a twisting
  that is only equal to the changed, resp. pulled-back, one after rereading the morphism to the
  base along an equality.
* `…RelativeProjInvertibleMorphism.pullbackGradedAlgebraMap_pullbackGradedAlgebraMap`,
  `…pullbackGradedAlgebraMap_congr`: the inverse image of a map of graded algebras along a
  composite, resp. along equal morphisms, through the pseudofunctoriality, resp. congruence,
  isomorphisms.
* `…RelativeProjInvertibleMorphism.eq_squareChainIso`: comparisons `θ₀ ~ k^*θ_χ`,
  `θ₂ ~ k₂^*θ_χ` and `θ₂ ~ j₂^*θ_ψ` assemble to `θ₀ ~ j^*θ_ψ` for `k = n ≫ k₂` and
  `j = n ≫ j₂`, through the identifications `…squareChainIso`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
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

/-! ### The change of the target, reread over an equal morphism to the base -/

section ChangeTargetOfEq

variable {Y Y' T : Scheme.{u}} (A : SheafGradedAlgebra.{u} Y) (hs : Y' ⟶ Y)
  {A₁ : SheafGradedAlgebra.{u} Y'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback hs)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  {f₀ : T ⟶ Y'} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (χ : Twisting f₀ (situationAlgebra A₁) 1 L) {f' : T ⟶ Y} (h : f₀ ≫ hs = f')
  {ζ : Twisting f' (situationAlgebra A) 1 L}
  (hζ : ζ = Twisting.congrBase h (changeTarget A hs Φ hΦ χ))

include hζ in
/-- `U(ζ) = U(χ)` for `ζ` the change of the target of `χ`, reread over `f₀ ≫ hs = f'`. -/
theorem coveringOpen_changeTarget_of_eq :
    (toGradedPowerMap ζ).coveringOpen = (toGradedPowerMap χ).coveringOpen := by
  subst hζ
  subst h
  exact coveringOpen_changeTarget A hs Φ hΦ χ

/-- `r_ζ = (U(ζ) ⊆ U(χ)) ≫ r_χ ≫ pc`. -/
theorem homOfLE_globalMorphism_changeTarget_of_eq :
    (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le ≫
        (toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≫ changeTargetProj A hs Φ hΦ =
      (toGradedPowerMap ζ).globalMorphism (relativeProj A) := by
  subst hζ
  subst h
  exact homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ

/-- `thetaChangeSourceIso` for `ζ`: `(U(ζ) ⊆ U(χ))^* r_χ^*𝒪_{Proj(𝒜₁)}(*) ≅ r_ζ^*𝒪_{Proj(𝒜)}(*)`
through the comparison of twists along `pc`. -/
def thetaChangeSourceIsoOfEq :
    Stacks.Conormal.gradedPullback (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le)
        (Stacks.Conormal.gradedPullback ((toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (GradedPowerMap.twD A₁).algebra) ≅
      Stacks.Conormal.gradedPullback ((toGradedPowerMap ζ).globalMorphism (relativeProj A))
        (GradedPowerMap.twD A).algebra :=
  pullbackGradedAlgebraMapIso
      (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le).toLRSHom.toShHom
      (pullbackGradedAlgebraMapIso
        ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)).toLRSHom.toShHom
        (RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
          (changeTargetProj A hs Φ hΦ) rfl).symm) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
      (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le)
      ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
      (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le ≫
        (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
      (changeTargetProj A hs Φ hΦ) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _
      (homOfLE_globalMorphism_changeTarget_of_eq A hs Φ hΦ χ h hζ)

/-- **`θ_ζ = θ_χ` under a change of the target, reread over an equal morphism to the base**:
`theta_changeTarget` for a twisting `ζ` equal to the change of the target of `χ` read over
`f₀ ≫ hs = f'`. -/
theorem theta_changeTarget_of_eq :
    (toGradedPowerMap ζ).theta =
      (thetaChangeSourceIsoOfEq A hs Φ hΦ χ h hζ).inv ≫
        pullbackGradedAlgebraMap
          (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le).toLRSHom.toShHom
          (toGradedPowerMap χ).theta ≫
        (laurentOnHomOfLEIso L (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le).hom := by
  subst hζ
  subst h
  exact theta_changeTarget A hs Φ hΦ χ

end ChangeTargetOfEq

/-! ### Base change of the source, reread over an equal morphism to the base -/

section PullbackOfEq

variable {S X W : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (ψ : Twisting f (situationAlgebra A) 1 L) (q : W ⟶ X) {f₂ : W ⟶ S} (h : q ≫ f = f₂)
  {χ₂ : Twisting f₂ (situationAlgebra A) 1 ((pullbackFunctor (ringedSpaceHom q)).obj L)}
  (hχ : χ₂ = Twisting.congrBase h (ψ.pullback q))

include hχ in
/-- `U(χ₂) = q^{-1}(U(ψ))` for `χ₂` the pullback `q^*ψ` reread over `q ≫ f = f₂`. -/
theorem coveringOpen_pullback_of_eq :
    (toGradedPowerMap χ₂).coveringOpen = q ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen := by
  subst hχ
  subst h
  exact coveringOpen_pullback ψ q

/-- The restriction `U(χ₂) ⟶ U(ψ)` of `q`. -/
def coveringOpenPullbackOfEq :
    (toGradedPowerMap χ₂).coveringOpen.toScheme ⟶ (toGradedPowerMap ψ).coveringOpen.toScheme :=
  q.resLE _ _ (coveringOpen_pullback_of_eq ψ q h hχ).le

/-- `r_{χ₂} = r_{ℒ,ψ} ∘ q|_{U(χ₂)}`. -/
theorem coveringOpenPullbackOfEq_globalMorphism :
    coveringOpenPullbackOfEq ψ q h hχ ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A) =
      (toGradedPowerMap χ₂).globalMorphism (relativeProj A) := by
  subst hχ
  subst h
  exact coveringOpenPullback_globalMorphism ψ q

/-- `thetaSourceIso` for `χ₂`. -/
def thetaSourceIsoOfEq :
    Stacks.Conormal.gradedPullback (coveringOpenPullbackOfEq ψ q h hχ)
        (Stacks.Conormal.gradedPullback ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
          (GradedPowerMap.twD A).algebra) ≅
      Stacks.Conormal.gradedPullback ((toGradedPowerMap χ₂).globalMorphism (relativeProj A))
        (GradedPowerMap.twD A).algebra :=
  GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso (GradedPowerMap.twD A).algebra
      (coveringOpenPullbackOfEq ψ q h hχ) ((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso (GradedPowerMap.twD A).algebra
      (coveringOpenPullbackOfEq_globalMorphism ψ q h hχ)

/-- `thetaTargetIso` for `χ₂`: `j^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁_d (q^*ℒ)^{⊗ d}|_{U(χ₂)}`, the
identification `thetaTargetIso` of `q^*ψ` transported along `χ₂ = q^*ψ`. -/
def thetaTargetIsoOfEq :
    Stacks.Conormal.gradedPullback (coveringOpenPullbackOfEq ψ q h hχ)
        (laurentOn L (toGradedPowerMap ψ).coveringOpen) ≅
      laurentOn ((pullbackFunctor (ringedSpaceHom q)).obj L)
        (toGradedPowerMap χ₂).coveringOpen := by
  subst hχ
  subst h
  exact thetaTargetIso ψ q

/-- **`θ` of `q^*ψ`, reread over an equal morphism to the base, is the pullback of `θ`**:
`theta_pullback` for a twisting `χ₂` equal to `q^*ψ` read over `q ≫ f = f₂`. -/
theorem theta_pullback_of_eq :
    (toGradedPowerMap χ₂).theta =
      (thetaSourceIsoOfEq ψ q h hχ).inv ≫
        pullbackGradedAlgebraMap (coveringOpenPullbackOfEq ψ q h hχ).toLRSHom.toShHom
          (toGradedPowerMap ψ).theta ≫
        (thetaTargetIsoOfEq ψ q h hχ).hom := by
  subst hχ
  subst h
  exact theta_pullback ψ q

end PullbackOfEq

/-! ### Inverse images of maps of graded algebras along composites and equal morphisms -/

section PullbackNaturality

/-- `b = i⁻¹ ≫ a ≫ j` from `a = i ≫ b ≫ j⁻¹`, for isomorphisms `i` and `j`. -/
private theorem eq_inv_comp_comp_hom_of_eq {C : Type*} [Category C] {A B A' B' : C}
    (i : A ≅ A') (j : B ≅ B') {a : A ⟶ B} {b : A' ⟶ B'} (h : a = i.hom ≫ b ≫ j.inv) :
    b = i.inv ≫ a ≫ j.hom := by
  rw [h]
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {X Y Z : Scheme.{u}}
  {G H : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z.toRingedSpace)} (θ : G ⟶ H)

/-- **`k^*h^*θ` is `(k ≫ h)^*θ` through the pseudofunctoriality isomorphisms.** -/
theorem pullbackGradedAlgebraMap_pullbackGradedAlgebraMap (k : X ⟶ Y) (h : Y ⟶ Z) :
    pullbackGradedAlgebraMap k.toLRSHom.toShHom (pullbackGradedAlgebraMap h.toLRSHom.toShHom θ) =
      (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G k h).hom ≫
        pullbackGradedAlgebraMap (k ≫ h).toLRSHom.toShHom θ ≫
        (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso H k h).inv := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  exact (NatIso.naturality_2 (Scheme.Modules.pullbackComp k h) (θ.app n)).symm

/-- `(k ≫ h)^*θ` is `k^*h^*θ` through the pseudofunctoriality isomorphisms. -/
theorem pullbackGradedAlgebraMap_comp_eq (k : X ⟶ Y) (h : Y ⟶ Z) :
    pullbackGradedAlgebraMap (k ≫ h).toLRSHom.toShHom θ =
      (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G k h).inv ≫
        pullbackGradedAlgebraMap k.toLRSHom.toShHom
          (pullbackGradedAlgebraMap h.toLRSHom.toShHom θ) ≫
        (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso H k h).hom := by
  exact eq_inv_comp_comp_hom_of_eq _ _ (pullbackGradedAlgebraMap_pullbackGradedAlgebraMap θ k h)

/-- **`f^*θ` is `f'^*θ` through the congruence isomorphisms**, for `f = f'`. -/
theorem pullbackGradedAlgebraMap_congr {f f' : X ⟶ Z} (hff : f = f') :
    pullbackGradedAlgebraMap f.toLRSHom.toShHom θ =
      (GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G hff).hom ≫
        pullbackGradedAlgebraMap f'.toLRSHom.toShHom θ ≫
        (GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso H hff).inv := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  exact (NatIso.naturality_2 (Scheme.Modules.pullbackCongr hff) (θ.app n)).symm

/-- `f'^*θ` is `f^*θ` through the congruence isomorphisms, for `f = f'`. -/
theorem pullbackGradedAlgebraMap_congr_eq {f f' : X ⟶ Z} (hff : f = f') :
    pullbackGradedAlgebraMap f'.toLRSHom.toShHom θ =
      (GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G hff).inv ≫
        pullbackGradedAlgebraMap f.toLRSHom.toShHom θ ≫
        (GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso H hff).hom := by
  exact eq_inv_comp_comp_hom_of_eq _ _ (pullbackGradedAlgebraMap_congr θ hff)

end PullbackNaturality

/-! ### Assembling the comparisons of `θ` around a square -/

section SquareAssembly

variable {U₀ U₂ Uχ Uψ : Scheme.{u}} {k : U₀ ⟶ Uχ} {n : U₀ ⟶ U₂} {k₂ : U₂ ⟶ Uχ}
  {j₂ : U₂ ⟶ Uψ} {j : U₀ ⟶ Uψ} (hk : n ≫ k₂ = k) (hj : n ≫ j₂ = j)

/-- **The identification `j^*𝒜_ψ ≅ 𝒜₀` assembled from three comparisons** along `k = n ≫ k₂` and
`j = n ≫ j₂`: the given identifications `k^*𝒜_χ ≅ 𝒜₀`, `k₂^*𝒜_χ ≅ 𝒜₂` and `j₂^*𝒜_ψ ≅ 𝒜₂`,
combined through the pseudofunctoriality and congruence isomorphisms of the inverse image of
graded algebras. -/
def squareChainIso
    {A₀ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₀.toRingedSpace)}
    {A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₂.toRingedSpace)}
    {Aχ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uχ.toRingedSpace)}
    {Aψ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uψ.toRingedSpace)}
    (S₁ : pullbackGradedAlgebra k.toLRSHom.toShHom Aχ ≅ A₀)
    (S₂ : pullbackGradedAlgebra k₂.toLRSHom.toShHom Aχ ≅ A₂)
    (S₄ : pullbackGradedAlgebra j₂.toLRSHom.toShHom Aψ ≅ A₂) :
    pullbackGradedAlgebra j.toLRSHom.toShHom Aψ ≅ A₀ :=
  (GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso Aψ hj).symm ≪≫
    (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso Aψ n j₂).symm ≪≫
    pullbackGradedAlgebraMapIso n.toLRSHom.toShHom (S₄ ≪≫ S₂.symm) ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso Aχ n k₂ ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso Aχ hk ≪≫ S₁

/-- **Three comparisons of maps of graded algebras assemble to one along `j`.**  If
`θ₀ = k^*θ_χ`, `θ₂ = k₂^*θ_χ` and `θ₂ = j₂^*θ_ψ`, each through given identifications of sources
and targets, then `θ₀ = j^*θ_ψ` through the identifications `squareChainIso` assembled from
them. -/
theorem eq_squareChainIso
    {A₀ B₀ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₀.toRingedSpace)}
    {A₂ B₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₂.toRingedSpace)}
    {Aχ Bχ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uχ.toRingedSpace)}
    {Aψ Bψ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uψ.toRingedSpace)}
    {S₁ : pullbackGradedAlgebra k.toLRSHom.toShHom Aχ ≅ A₀}
    {S₂ : pullbackGradedAlgebra k₂.toLRSHom.toShHom Aχ ≅ A₂}
    {S₄ : pullbackGradedAlgebra j₂.toLRSHom.toShHom Aψ ≅ A₂}
    {T₁ : pullbackGradedAlgebra k.toLRSHom.toShHom Bχ ≅ B₀}
    {T₂ : pullbackGradedAlgebra k₂.toLRSHom.toShHom Bχ ≅ B₂}
    {T₄ : pullbackGradedAlgebra j₂.toLRSHom.toShHom Bψ ≅ B₂}
    {θ₀ : A₀ ⟶ B₀} {θ₂ : A₂ ⟶ B₂} {θχ : Aχ ⟶ Bχ} {θψ : Aψ ⟶ Bψ}
    (E1 : θ₀ = S₁.inv ≫ pullbackGradedAlgebraMap k.toLRSHom.toShHom θχ ≫ T₁.hom)
    (E2 : θ₂ = S₂.inv ≫ pullbackGradedAlgebraMap k₂.toLRSHom.toShHom θχ ≫ T₂.hom)
    (E3 : θ₂ = S₄.inv ≫ pullbackGradedAlgebraMap j₂.toLRSHom.toShHom θψ ≫ T₄.hom) :
    θ₀ = (squareChainIso hk hj S₁ S₂ S₄).inv ≫
      pullbackGradedAlgebraMap j.toLRSHom.toShHom θψ ≫ (squareChainIso hk hj T₁ T₂ T₄).hom := by
  subst E1
  subst E2
  have h2 : pullbackGradedAlgebraMap k₂.toLRSHom.toShHom θχ =
      S₂.hom ≫ (S₄.inv ≫ pullbackGradedAlgebraMap j₂.toLRSHom.toShHom θψ ≫ T₄.hom) ≫ T₂.inv := by
    exact eq_inv_comp_comp_hom_of_eq S₂.symm T₂.symm E3.symm
  rw [pullbackGradedAlgebraMap_congr_eq θχ hk, pullbackGradedAlgebraMap_comp_eq θχ n k₂, h2]
  simp only [pullbackGradedAlgebraMap_comp]
  rw [pullbackGradedAlgebraMap_pullbackGradedAlgebraMap θψ n j₂,
    pullbackGradedAlgebraMap_congr θψ hj]
  simp only [squareChainIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    pullbackGradedAlgebraMapIso, pullbackGradedAlgebraMap_comp, Category.assoc]

end SquareAssembly

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end

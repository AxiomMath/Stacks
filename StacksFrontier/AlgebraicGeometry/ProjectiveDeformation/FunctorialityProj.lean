module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.ProjBaseChange
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.SectionPullRestrict
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedDegreewiseIso

/-!
# The canonical morphism `r'` of [Stacks, Tag 0D4F] is functorial in the deformation

For a morphism `φ : D₁ ⟶ D₂` of admissible deformations over `g : S'₁ ⟶ S'₂`, with total part
`g' : X'₁ ⟶ X'₂`, the square

```
X'₁ ---------- r'₁ ----------> Proj_{S'₁}(𝒜'(D₁))
 |g'                                 | projBaseChangeHom φ
 v                                   v
X'₂ ---------- r'₂ ----------> Proj_{S'₂}(𝒜'(D₂))
```

commutes, where `projBaseChangeHom φ` is `Proj` of `algebraPullbackHom φ : g^*𝒜'(D₂) ⟶ 𝒜'(D₁)`
followed by the base change morphism of [Stacks, Tag 01O3]. This is the functoriality of `r'` in
the data `(X', S', i, i', f', ℒ')` asserted by [Stacks, Tag 0D4F].

## The proof

Over affine opens `U' ⊆ g^{-1}(U)` of the two bases, both composites restricted to `f'₁^{-1}(U')`
are the morphism of [Stacks, Tag 01NK] for one graded map
`Γ(U, 𝒜'(D₂)) ⟶ Γ_*(f'₁^{-1}(U'), ℒ'₁)` followed by the chart over `U`
(`ι_canonicalProjHom`, `chart_comp_projBaseChangeHom`, and the functoriality of the morphism of
[Stacks, Tag 01NK] in the graded ring and in the scheme). The graded maps agree in positive
degrees up to isomorphisms of the tensor powers — both send a section to its pullback along
`f'₁^{-1}(U') ⟶ X'₁ ⟶ X'₂` (`SectionRingBaseChange.restrictPowSectionIso_sectionPull`,
`…pullbackRestrictIso_pullbackSection`) — which is all the morphism of [Stacks, Tag 01NK] sees
(`GradedSections.resLE_glued_of_degreewiseIsoVia`).

## Main results

* `…AdmissibleDeformation.canonicalProjHom_comp_projBaseChangeHom`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

section Sections

/-- **The adjoint transpose of `φ : F ⟶ g_* G` on a pulled-back section** is the restriction of
`φ` on the section. -/
theorem homEquiv_symm_app_pullbackSection {X Y : Scheme.{u}} (g : X ⟶ Y) {F : Y.Modules}
    {G : X.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : Y.Opens) (U' : X.Opens)
    (h : U' ≤ g ⁻¹ᵁ U) (y : Γ(F, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F G).symm φ).app U'
        (Scheme.Modules.pullbackSection g F U U' h y) =
      G.presheaf.map (homOfLE h).op (φ.app U y) := by
  have hφ : φ = (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F ≫
      (Scheme.Modules.pushforward g).map
        (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F G).symm φ) := by
    have := Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction g) F G
      (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F G).symm φ)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have e1 := Stacks.AlgebraicGeometry.SectionRingBaseChange.hom_app_map
    (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F G).symm φ) h
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp g F U y)
  refine e1.trans (congrArg (fun t => G.presheaf.map (homOfLE h).op t) ?_)
  conv_rhs => rw [hφ]
  rfl

end Sections

section Components

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- A homogeneous element of the section ring is the inclusion of its component. -/
private theorem coe_eq_of_componentEquiv (U : S.Opens) (n : ℕ) (a : A.grading U n) :
    (a : A.sectionRing U) = DirectSum.of (A.sectionPieces U) n (A.componentEquiv U n a) := by
  obtain ⟨y, hy⟩ := a.2
  have ha : (a : A.sectionRing U) = DirectSum.of (A.sectionPieces U) n y := hy.symm
  have hc : A.componentEquiv U n a = y := by
    rw [SheafGradedAlgebra.componentEquiv_apply, ha]; exact DirectSum.of_eq_same n y
  rw [hc, ha]

/-- The component of the image of a homogeneous element under `sectionHom`. -/
theorem componentEquiv_sectionHom (U : S.Opens) (n : ℕ) (a : A.grading U n) :
    B.componentEquiv U n ⟨ψ.sectionHom U (a : A.sectionRing U), (ψ.sectionHom U).map_mem a.2⟩ =
      (ψ.app (n : ℤ)).app U (A.componentEquiv U n a) := by
  show (ψ.sectionHom U (a : A.sectionRing U)) n = _
  rw [coe_eq_of_componentEquiv, SheafGradedAlgebraHom.sectionHom_of]
  exact DirectSum.of_eq_same n _

/-- The component of the image of a homogeneous element under the base change of the section
rings of [Stacks, Tag 01O3]. -/
theorem componentEquiv_sectionBaseChange {S' : Scheme.{u}} (g : S' ⟶ S)
    (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite) (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens)
    (n : ℕ) (a : A.grading U.toOpens n) :
    (A.pullback g).componentEquiv U'.toOpens n
        ⟨Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A g U U' h
          (a : A.sectionRing U.toOpens),
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A g U U'
            h).map_mem a.2⟩ =
      Scheme.Modules.pullbackSection g (A.piece (n : ℤ)) U.toOpens U'.toOpens h
        (A.componentEquiv U.toOpens n a) := by
  show (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A g U U' h
    (a : A.sectionRing U.toOpens)) n = _
  rw [coe_eq_of_componentEquiv,
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange_of]
  exact DirectSum.of_eq_same n _

end Components

/-- The diagram chase assembling the two descriptions of `projBaseChangeHom ∘ r'₁` and
`r'₂ ∘ g'` over an open of the source, stated in an arbitrary category so that it is checked on
atoms. -/
theorem chase {C : Type*} [Category C]
    {Xp X₁ X₂ RP₁ RP₂ χc ξc Ξc ψc Yp PA₁ MD PB PA₂ : C}
    {ι₁ : Xp ⟶ X₁} {r₁ : X₁ ⟶ RP₁} {Mb : RP₁ ⟶ RP₂} {e₁ : Xp ⟶ χc} {g₁ : χc ⟶ PA₁}
    {ch₁ : PA₁ ⟶ RP₁} {m : PA₁ ⟶ MD} {mh : MD ⟶ PB} {pm : PB ⟶ PA₂} {ch₂ : PA₂ ⟶ RP₂}
    {e : Xp ⟶ Ξc} {h₂ : Ξc ⟶ ξc} {h₁ : ξc ⟶ χc} {gξ : ξc ⟶ PB} {gΞ : Ξc ⟶ PA₂}
    {q : X₁ ⟶ X₂} {r₂ : X₂ ⟶ RP₂} {J : Xp ⟶ Yp} {ι₂ : Yp ⟶ X₂} {e₂ : Yp ⟶ ψc} {g₂ : ψc ⟶ PA₂}
    {res : Ξc ⟶ ψc}
    (hL1 : ι₁ ≫ r₁ = e₁ ≫ g₁ ≫ ch₁) (hL2 : ch₁ ≫ Mb = m ≫ mh ≫ pm ≫ ch₂)
    (hL3 : (h₁ ≫ g₁ ≫ m) ≫ mh = gξ) (hL4 : h₂ ≫ gξ ≫ pm = gΞ) (he₁ : e₁ = e ≫ h₂ ≫ h₁)
    (hJι : J ≫ ι₂ = ι₁ ≫ q) (hR1 : ι₂ ≫ r₂ = e₂ ≫ g₂ ≫ ch₂) (hJ : J ≫ e₂ = e ≫ res)
    (hglue : res ≫ g₂ = gΞ) :
    ι₁ ≫ r₁ ≫ Mb = ι₁ ≫ q ≫ r₂ := by
  calc ι₁ ≫ r₁ ≫ Mb = (ι₁ ≫ r₁) ≫ Mb := (Category.assoc _ _ _).symm
    _ = e ≫ h₂ ≫ h₁ ≫ g₁ ≫ ch₁ ≫ Mb := by rw [hL1, he₁]; simp only [Category.assoc]
    _ = e ≫ h₂ ≫ ((h₁ ≫ g₁ ≫ m) ≫ mh) ≫ pm ≫ ch₂ := by rw [hL2]; simp only [Category.assoc]
    _ = e ≫ gΞ ≫ ch₂ := by rw [hL3, ← hL4]; simp only [Category.assoc]
    _ = e ≫ res ≫ g₂ ≫ ch₂ := by rw [← hglue]; simp only [Category.assoc]
    _ = J ≫ e₂ ≫ g₂ ≫ ch₂ := by rw [← Category.assoc J, hJ]; simp only [Category.assoc]
    _ = J ≫ ι₂ ≫ r₂ := by rw [hR1]
    _ = ι₁ ≫ q ≫ r₂ := by rw [← Category.assoc, hJι, Category.assoc]

/-- Over the top open, the inclusion of an open has a section. -/
private theorem exists_section_ι_of_eq_top {X : Scheme.{u}} (W : X.Opens) (h : W = ⊤) :
    ∃ e : X ⟶ W.toScheme, e ≫ W.ι = 𝟙 _ :=
  ⟨X.topIso.inv ≫ (X.isoOfEq h.symm).hom, by
    simp only [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]⟩

namespace PolarizedFamily.AdmissibleDeformation

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ)
  (hd₀ : 0 < d₀)

/-- **Pulling back a section of `𝒜'_n(D₂)` and reading it in `⨁_{d ≥ 0} 𝒜'_d(D₁)` is pulling
back the section of `(ℒ'₂)^{⊗ n}`**: for `n ≥ d₀` and affine opens `U' ⊆ g^{-1}(U)`, the
comparison of `D₁` applied to `algebraPullbackHom` of the pullback of a section `y` of
`𝒜'_n(D₂)` over `U` is `sectionPull` of the comparison of `D₂` applied to `y`. -/
theorem comparison_algebraPullbackSheafHom_pullbackSection {U : D₂.S'.Opens} {U' : D₁.S'.Opens}
    (hUU' : U' ≤ φ.base ⁻¹ᵁ U) (n : ℕ) (hn : d₀ ≤ n)
    (y : Γ((D₂.truncatedSectionAlgebra d₀ hd₀).piece (n : ℤ), U)) :
    (show Γ(Stacks.AmpleProjectiveImmersion.tensorPowerModule D₁.X' D₁.L' (n : ℤ),
        D₁.f' ⁻¹ᵁ U') from
      ((D₁.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app U'
        (((algebraPullbackSheafHom φ d₀ hd₀).app (n : ℤ)).app U'
          (Scheme.Modules.pullbackSection φ.base _ U U' hUU' y))) =
      Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
        φ.polarization (n : ℤ) (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U')
        (Stacks.AlgebraicGeometry.SectionRingBaseChange.preimage_le_preimage φ.total D₂.f' D₁.f'
          φ.base φ.isPullback.w U U' hUU')
        (((D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app U y) := by
  have := D₁.finitePresentation.quasiCompact
  have := D₁.finitePresentation.quasiSeparated
  have := D₂.finitePresentation.quasiCompact
  have := D₂.finitePresentation.quasiSeparated
  have h0 : ¬ (n : ℤ) = 0 := by omega
  have hnt : (d₀ : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have e1 := homEquiv_symm_app_pullbackSection φ.base
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPushApp φ.total D₂.f' D₁.f' φ.base
      φ.isPullback.w D₂.L' D₁.L' φ.polarization d₀ hd₀ (n : ℤ)) U U' hUU' y
  have e2 := Stacks.AlgebraicGeometry.SectionRingBaseChange.hom_app_map
    ((D₁.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)) hUU'
    ((Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPushApp φ.total D₂.f' D₁.f' φ.base
      φ.isPullback.w D₂.L' D₁.L' φ.polarization d₀ hd₀ (n : ℤ)).app U y)
  have e3 := Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPushApp_app φ.total D₂.f' D₁.f'
    φ.base φ.isPullback.w D₂.L' D₁.L' φ.polarization d₀ hd₀ (n : ℤ) U y
  have e4 := e3.trans (Stacks.AlgebraicGeometry.SectionRingBaseChange.tailMapApp_tail h0 hnt y)
  have e5 : ∀ w : Γ(Stacks.AmpleProjectiveImmersion.tensorPowerModule D₁.X' D₁.L' (n : ℤ),
      D₁.f' ⁻¹ᵁ (φ.base ⁻¹ᵁ U)),
      ((D₁.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app (φ.base ⁻¹ᵁ U)
        ((eqToHom (Stacks.AlgebraicGeometry.SectionAlgebra.tailPiece_eq_piece
          (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra D₁.f'
            (Stacks.RelativeAmple.laurentPowers D₁.L')) d₀ hd₀ hnt).symm).val.app
          (op (φ.base ⁻¹ᵁ U)) w) = w := by
    intro w
    show Scheme.Modules.Hom.app (Stacks.AlgebraicGeometry.SectionAlgebra.tailCompApp
      D₁.laurentPushforward d₀ hd₀ (n : ℤ)) (φ.base ⁻¹ᵁ U) _ = w
    rw [Stacks.AlgebraicGeometry.SectionAlgebra.tailCompApp_eq_eqToHom _ _ _ h0 hnt
      (by omega)]
    have key : ∀ {M M' : D₁.S'.Modules} (e : M = M') (e' : M' = M) (z : Γ(M, φ.base ⁻¹ᵁ U)),
        (eqToHom e').app (φ.base ⁻¹ᵁ U) ((eqToHom e).app (φ.base ⁻¹ᵁ U) z) = z := by
      intro M M' e e' z
      subst e
      rfl
    exact key (Stacks.AlgebraicGeometry.SectionAlgebra.tailPiece_eq_piece
      (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra D₁.f'
        (Stacks.RelativeAmple.laurentPowers D₁.L')) d₀ hd₀ hnt).symm _ w
  have e6 : ((D₂.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app U y =
      (eqToHom (Stacks.AlgebraicGeometry.SectionAlgebra.tailPiece_eq_piece
          (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra D₂.f'
            (Stacks.RelativeAmple.laurentPowers D₂.L')) d₀ hd₀ hnt)).val.app (op U) y := by
    show Scheme.Modules.Hom.app (Stacks.AlgebraicGeometry.SectionAlgebra.tailCompApp
      D₂.laurentPushforward d₀ hd₀ (n : ℤ)) U y = _
    rw [Stacks.AlgebraicGeometry.SectionAlgebra.tailCompApp_eq_eqToHom _ _ _ h0 hnt
      (by omega)]
    rfl
  refine (congrArg (fun t => ((D₁.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app U' t)
    e1).trans ?_
  refine e2.trans ?_
  refine (congrArg (fun t => (D₁.fullSectionAlgebra.piece (n : ℤ)).presheaf.map (homOfLE hUU').op
    (((D₁.sectionAlgebraComparison d₀ hd₀).app (n : ℤ)).app (φ.base ⁻¹ᵁ U) t)) e4).trans ?_
  refine (congrArg (fun t => (D₁.fullSectionAlgebra.piece (n : ℤ)).presheaf.map (homOfLE hUU').op t)
    (e5 _)).trans ?_
  rw [e6]
  exact Stacks.AlgebraicGeometry.SectionRingBaseChange.map_sectionPull φ.total D₂.L' D₁.L'
    φ.polarization (D₂.f' ⁻¹ᵁ U) (n : ℤ)
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.preimage_le_preimage φ.total D₂.f' D₁.f'
      φ.base φ.isPullback.w U (φ.base ⁻¹ᵁ U) le_rfl) (D₁.f'.preimage_mono hUU') _

variable {U : D₂.S'.Opens} (hU : IsAffineOpen U) {U' : D₁.S'.Opens} (hU' : IsAffineOpen U')
  (hUU' : U' ≤ φ.base ⁻¹ᵁ U)

include hUU' in
/-- `f'₁^{-1}(U') ⊆ g'^{-1}(f'₂^{-1}(U))`. -/
theorem preimage_le_preimage_total :
    D₁.f' ⁻¹ᵁ U' ≤ φ.total ⁻¹ᵁ (D₂.f' ⁻¹ᵁ U) :=
  Stacks.AlgebraicGeometry.SectionRingBaseChange.preimage_le_preimage φ.total D₂.f' D₁.f'
    φ.base φ.isPullback.w U U' hUU'

/-- **The [Stacks, Tag 01NK] datum of `projBaseChangeHom ∘ r'₁` over `U' ⊆ g^{-1}(U)`**: the datum
of `r'₁` over `U'` read along `Γ(U, 𝒜'(D₂)) ⟶ Γ(U', g^*𝒜'(D₂)) ⟶ Γ(U', 𝒜'(D₁))`. -/
abbrev pairDatum :
    Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections
      ((D₂.truncatedSectionAlgebra d₀ hd₀).grading U)
      ((Scheme.Modules.pullback (D₁.f' ⁻¹ᵁ U').ι).obj D₁.sectionPowerMap.L) :=
  comap (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base ⟨U, hU⟩ ⟨U', hU'⟩ hUU')
    (comap ((algebraPullbackSheafHom φ d₀ hd₀).sectionHom U') (D₁.chartDatum d₀ hd₀ U'))

/-- **In positive degrees, the datum of `projBaseChangeHom ∘ r'₁` and the pullback along `g'` of
the datum of `r'₂` agree**, both being, up to the comparisons of the tensor powers, the inverse
image of the section along `f'₁^{-1}(U') ⟶ X'₁ ⟶ X'₂`. -/
theorem pairDatum_degreewiseIso (n : ℕ) (hn : 0 < n)
    (a : (D₂.truncatedSectionAlgebra d₀ hd₀).grading U n) :
    (Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso φ.total D₂.L' D₁.L'
        φ.polarization (D₁.f' ⁻¹ᵁ U') n).hom.app ⊤
        ((pairDatum φ d₀ hd₀ hU hU' hUU').toFun n a) =
      (Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
        (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U') (preimage_le_preimage_total φ hUU') n).hom.app ⊤
        (pullbackSectionHom (φ.total.resLE (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U')
            (preimage_le_preimage_total φ hUU'))
          (Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback (D₂.f' ⁻¹ᵁ U).ι).obj D₂.L') n)
          ⊤ ⊤ (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top _)
          ((D₂.chartDatum d₀ hd₀ U).toFun n a)) := by
  by_cases hnd : d₀ ≤ n
  · let y := (D₂.truncatedSectionAlgebra d₀ hd₀).componentEquiv U n a
    let sbc := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base ⟨U, hU⟩ ⟨U', hU'⟩ hUU'
    let Ψ := algebraPullbackSheafHom φ d₀ hd₀
    let c₁ := D₁.sectionAlgebraComparison d₀ hd₀
    let c₂ := D₂.sectionAlgebraComparison d₀ hd₀
    have k1 := componentEquiv_sectionBaseChange (A := D₂.truncatedSectionAlgebra d₀ hd₀) φ.base
      ⟨U, hU⟩ ⟨U', hU'⟩ hUU' n a
    have k2 := componentEquiv_sectionHom Ψ U' n
      ⟨sbc (a : (D₂.truncatedSectionAlgebra d₀ hd₀).sectionRing U), sbc.map_mem a.2⟩
    have k3 := componentEquiv_sectionHom c₁ U' n
      ⟨Ψ.sectionHom U' (sbc (a : (D₂.truncatedSectionAlgebra d₀ hd₀).sectionRing U)),
        (Ψ.sectionHom U').map_mem (sbc.map_mem a.2)⟩
    have k4 := comparison_algebraPullbackSheafHom_pullbackSection φ d₀ hd₀ hUU' n hnd y
    have hΞ : (pairDatum φ d₀ hd₀ hU hU' hUU').toFun n a =
        Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection D₁.L'
          (D₁.f' ⁻¹ᵁ U') n
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₁.L' n).inv.app
            (D₁.f' ⁻¹ᵁ U')
            (Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull φ.total D₂.L' D₁.L'
              φ.polarization (n : ℤ) (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U')
              (preimage_le_preimage_total φ hUU') ((c₂.app (n : ℤ)).app U y))) := by
      have key := k3.trans ((congrArg (fun t => (c₁.app (n : ℤ)).app U' t) k2).trans
        ((congrArg (fun t => (c₁.app (n : ℤ)).app U' ((Ψ.app (n : ℤ)).app U' t)) k1).trans k4))
      rw [← key]; rfl
    have k5 := componentEquiv_sectionHom c₂ U n a
    have hψ : (D₂.chartDatum d₀ hd₀ U).toFun n a =
        Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection D₂.L'
          (D₂.f' ⁻¹ᵁ U) n ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D₂.L' n).inv.app
            (D₂.f' ⁻¹ᵁ U) ((c₂.app (n : ℤ)).app U y)) := by
      rw [← k5]; rfl
    refine (congrArg (fun t => (Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso
      φ.total D₂.L' D₁.L' φ.polarization (D₁.f' ⁻¹ᵁ U') n).hom.app ⊤ t) hΞ).trans ?_
    refine (Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso_sectionPull
      φ.total D₂.L' D₁.L' φ.polarization (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U')
      (preimage_le_preimage_total φ hUU') n ((c₂.app (n : ℤ)).app U y)).trans ?_
    refine Eq.trans ?_ (congrArg (fun t =>
      (Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
        (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U') (preimage_le_preimage_total φ hUU') n).hom.app ⊤
        (pullbackSectionHom (φ.total.resLE (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U')
            (preimage_le_preimage_total φ hUU'))
          (Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback (D₂.f' ⁻¹ᵁ U).ι).obj D₂.L') n)
          ⊤ ⊤ (Stacks.AlgebraicGeometry.ProjChartRatioPullback.top_le_preimage_top _) t)) hψ).symm
    exact (Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso_pullbackSection
      φ.total D₂.L' (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U') (preimage_le_preimage_total φ hUU') n
      ((c₂.app (n : ℤ)).app U y)).symm
  · have hy : (D₂.truncatedSectionAlgebra d₀ hd₀).componentEquiv U n a = 0 :=
      Stacks.AlgebraicGeometry.SectionAlgebra.eq_zero_of_tailPiece D₂.laurentPushforward d₀
        (show (n : ℤ) ≠ 0 by omega) (show ¬ (d₀ : ℤ) ≤ (n : ℤ) by omega) (op U) _
    have ha : a = 0 := ((D₂.truncatedSectionAlgebra d₀ hd₀).componentEquiv U n).injective
      (hy.trans (map_zero _).symm)
    subst ha
    simp only [map_zero]
    refine (map_zero _).trans ?_
    refine Eq.trans ?_ (congrArg _ (map_zero _).symm)
    exact (map_zero _).symm

variable (hiso : ∀ n : ℤ, IsIso ((algebraPullbackHom φ d₀ hd₀).app n))

include hU hU' hUU' in
/-- **`projBaseChangeHom ∘ r'₁` and `r'₂ ∘ g'` agree over `f'₁^{-1}(U')`**, for affine opens
`U' ⊆ g^{-1}(U)`: both are the morphism of [Stacks, Tag 01NK] for `pairDatum` followed by the
chart over `U`. -/
theorem ι_canonicalProjHom_comp_projBaseChangeHom :
    (D₁.f' ⁻¹ᵁ U').ι ≫ D₁.canonicalProjHom d₀ hd₀ ≫ projBaseChangeHom φ d₀ hd₀ hiso =
      (D₁.f' ⁻¹ᵁ U').ι ≫ φ.total ≫ D₂.canonicalProjHom d₀ hd₀ := by
  -- the data
  have hV := preimage_le_preimage_total φ hUU'
  let J := φ.total.resLE (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U') hV
  let Ψ := algebraPullbackSheafHom φ d₀ hd₀
  have hΨ := eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso
  let sbc := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange
    (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base ⟨U, hU⟩ ⟨U', hU'⟩ hUU'
  have hsbc :=
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.irrelevant_le_map_sectionBaseChange
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base ⟨U, hU⟩ ⟨U', hU'⟩ hUU'
  let χ₁ := D₁.chartDatum d₀ hd₀ U'
  let ξ := comap (Ψ.sectionHom U') χ₁
  let Ξ := pairDatum φ d₀ hd₀ hU hU' hUU'
  let ψ₂ := D₂.chartDatum d₀ hd₀ U
  -- the open on which everything is defined is all of `f'₁^{-1}(U')`
  have hglue :=
    Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.resLE_glued_of_degreewiseIsoVia
    J ψ₂ Ξ _ (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso
      φ.total D₂.L' D₁.L' φ.polarization (D₁.f' ⁻¹ᵁ U') n)
    (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
      (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U') hV n)
    (pairDatum_degreewiseIso φ d₀ hd₀ hU hU' hUU')
  have hcov₂ : ψ₂.coveringOpen = ⊤ := D₂.coveringOpen_chartDatum d₀ hd₀ hU
  have hcov₁ : χ₁.coveringOpen = ⊤ := D₁.coveringOpen_chartDatum d₀ hd₀ hU'
  have hcov_eq := ProjChartFullGraded.GradedSections.coveringOpen_eq_preimage_of_degreewiseIsoVia
    J ψ₂ Ξ _ (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.restrictPowSectionIso
      φ.total D₂.L' D₁.L' φ.polarization (D₁.f' ⁻¹ᵁ U') n)
    (fun n => Stacks.AlgebraicGeometry.SectionRingBaseChange.pullbackRestrictIso φ.total D₂.L'
      (D₂.f' ⁻¹ᵁ U) (D₁.f' ⁻¹ᵁ U') hV n)
    (pairDatum_degreewiseIso φ d₀ hd₀ hU hU' hUU')
  have hcovΞ : Ξ.coveringOpen = ⊤ := by rw [hcov_eq, hcov₂]; simp
  have hdom : mapDomain (((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base).grading U')
      ((D₁.truncatedSectionAlgebra d₀ hd₀).grading U') (Ψ.sectionHom U') = ⊤ :=
    Stacks.AlgebraicGeometry.RelativeProjMapDomain.chartDomain_eq_top_of_eventually_isIso Ψ hΨ U'
  -- sections of the inclusions of the covering opens
  obtain ⟨e, he⟩ := exists_section_ι_of_eq_top _ hcovΞ
  obtain ⟨e₁, he₁⟩ := exists_section_ι_of_eq_top _ hcov₁
  obtain ⟨e₂, he₂⟩ := exists_section_ι_of_eq_top _ hcov₂
  obtain ⟨m, hm⟩ := exists_section_ι_of_eq_top _ hdom
  have hle₁ := Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.coveringOpen_le
    (Ψ.sectionHom U') χ₁
  have hle₂ := Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.coveringOpen_le sbc ξ
  -- the four steps on the left
  have hL1 := D₁.ι_canonicalProjHom d₀ hd₀ hU' e₁ he₁
  have hL2 := chart_comp_projBaseChangeHom φ d₀ hd₀ hiso hU hU' hUU' m hm
  have hL3 := Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.glued_comp_mapHom
    (Ψ.sectionHom U') χ₁ ((D₁.f' ⁻¹ᵁ U').toScheme.homOfLE hle₁ ≫ χ₁.glued ≫ m)
    (by rw [Category.assoc, Category.assoc, hm, Category.comp_id])
  have hL4 := Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projMap
    sbc hsbc ξ
  have he₁' : e₁ = e ≫ (D₁.f' ⁻¹ᵁ U').toScheme.homOfLE hle₂ ≫
      (D₁.f' ⁻¹ᵁ U').toScheme.homOfLE hle₁ := by
    rw [← cancel_mono χ₁.coveringOpen.ι, he₁]
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact he.symm
  -- the two steps on the right
  have hR1 := D₂.ι_canonicalProjHom d₀ hd₀ hU e₂ he₂
  have hJ : J ≫ e₂ = e ≫ J.resLE ψ₂.coveringOpen Ξ.coveringOpen hcov_eq.le := by
    rw [← cancel_mono ψ₂.coveringOpen.ι, Category.assoc, he₂, Category.comp_id, Category.assoc,
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, he, Category.id_comp]
  exact chase hL1 hL2 hL3 hL4 he₁' (Scheme.Hom.resLE_comp_ι φ.total hV) hR1 hJ hglue

omit hU hU' hUU' in
include hiso in
/-- **[Stacks, Tag 0D4F]: `r'` is functorial in the deformation.** For a morphism `φ : D₁ ⟶ D₂`
of admissible deformations over `g : S'₁ ⟶ S'₂`, with total part `g' : X'₁ ⟶ X'₂`, the canonical
isomorphisms `r'ᵢ : X'ᵢ ⟶ Proj_{S'ᵢ}(𝒜'(Dᵢ))` satisfy

`r'₁ ≫ projBaseChangeHom φ = g' ≫ r'₂`,

where `projBaseChangeHom φ : Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` is the morphism induced by
`algebraPullbackHom φ : g^*𝒜'(D₂) ⟶ 𝒜'(D₁)` ([Stacks, Tags 07ZG, 07ZJ]) followed by the base
change morphism of [Stacks, Tag 01O3]. -/
theorem canonicalProjHom_comp_projBaseChangeHom :
    D₁.canonicalProjHom d₀ hd₀ ≫ projBaseChangeHom φ d₀ hd₀ hiso =
      φ.total ≫ D₂.canonicalProjHom d₀ hd₀ := by
  let I := {p : D₁.S'.affineOpens × D₂.S'.affineOpens // p.1.1 ≤ φ.base ⁻¹ᵁ p.2.1}
  let W : I → D₁.X'.Opens := fun p => D₁.f' ⁻¹ᵁ p.1.1.1
  have hW : IsOpenCover W := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := D₂.S'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (φ.base.base (D₁.f'.base x))) isOpen_univ
    obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hle⟩ := D₁.S'.isBasis_affineOpens.exists_subset_of_mem_open
      (show D₁.f'.base x ∈ φ.base ⁻¹ᵁ V from hxV) (φ.base ⁻¹ᵁ V).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨V', hV'⟩, ⟨V, hV⟩), hle⟩, hxV'⟩
  refine Scheme.Cover.hom_ext (D₁.X'.openCoverOfIsOpenCover W hW) _ _ fun p => ?_
  exact ι_canonicalProjHom_comp_projBaseChangeHom φ d₀ hd₀ p.1.2.2 p.1.1.2 p.2 hiso

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end

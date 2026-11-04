module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaChartMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSourceMulShrink
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSourceUnitShrink
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSchemeThetaMulRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSchemeThetaUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSchemeThetaMulQcoh
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneOverSiteHone

/-!
# [Stacks, Tag 0D2Z] for an algebraic space `X`

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849, `θ : r^*𝒪(d) ⟶ ℒ^{⊗ d}|_{U(ψ)}` is descended along a presentation of
`U(ψ)` from the chart maps `χ_w = σ_w ≫ m_w ≫ τ_w` at the scheme points
(`…InvertibleTwistingRestriction.descendedTheta`).  This file shows that `θ` is a map of graded
algebras, from the multiplicativity and unitality of the three factors of the chart maps
(`AlgebraicGeometry.Space.mul_of_factor_squares`,
`AlgebraicGeometry.Space.mul_comp_pointFamilyDescendedHom`), and assembles the statement of the
tag.

## Main results

* `…InvertibleTwistingRestriction.chartTargetIso_hom_one`: the target factor of the chart maps is
  unital; `…representedUnitChartHom_comp_chartSchemeTheta_shrink`: the middle factor is unital,
  over the site of `s.shrink`.
* `…InvertibleTwistingRestriction.descendedTheta_mul`, `…descendedTheta_one`: `θ` is
  multiplicative and unital.
* `…InvertibleTwistingRestriction.descendedTheta_clauseOneSections`: clause (1), from clause (1)
  at the scheme points.
* `…InvertibleTwistingRestriction.eq_descendedTheta`: `θ` is the only map with the restrictions
  of clause (3) at the scheme points.
* `…InvertibleTwistingRestriction.tag0D2Z_space`: **[Stacks, Tag 0D2Z] for `X` an algebraic
  space**, clause (1) at the scheme points being
  `…InvertibleTwistingRestriction.modulePullback_map_clauseOneProjLeg_comp_chartMap`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

attribute [local instance] modulesMonoidalCategory

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (P : Presentation s.shrink.site s.shrink.base s.shrink.containsBase
    (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property)

/-! ### The unit of the middle factor over the site of `s.shrink` -/

/-- **The unit square of a map of quasi-coherent modules, transported from one spelling of the
site to another**: if `(𝒪 ≅ g^*𝒪 ⟶ g^*K) ≫ θ = ν` over the site `B₁`, then the attached modules
over `B₂ = B₁` satisfy `ν^a = (𝒪 ≅ g^*𝒪 ⟶ g^*K)^a ≫ θ^a`, for heterogeneously equal leaves. -/
theorem representedUnitChartHom_comp_map_hom_of_site_heq {B₁ B₂ : BigFppfSite.{u}}
    (hB : B₁ = B₂) {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁}
    {hS₂ : B₂.Contains S₂} {V₁ U₁ : BigFppfOver B₁ S₁ hS₁} {V₂ U₂ : BigFppfOver B₂ S₂ hS₂}
    {g₁ : V₁ ⟶ U₁} {g₂ : V₂ ⟶ U₂}
    {K₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj U₁).ringCatSheaf).FullSubcategory}
    {K₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj U₂).ringCatSheaf).FullSubcategory}
    {t₁ : quasicoherentUnitObj B₁ S₁ hS₁ U₁ ⟶ K₁} {t₂ : quasicoherentUnitObj B₂ S₂ hS₂ U₂ ⟶ K₂}
    {P₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj V₁).ringCatSheaf).FullSubcategory}
    {P₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj V₂).ringCatSheaf).FullSubcategory}
    {θ₁ : quasicoherentPullbackObj B₁ S₁ hS₁ g₁ K₁ ⟶ P₁}
    {θ₂ : quasicoherentPullbackObj B₂ S₂ hS₂ g₂ K₂ ⟶ P₂}
    {ν₁ : quasicoherentUnitObj B₁ S₁ hS₁ V₁ ⟶ P₁} {ν₂ : quasicoherentUnitObj B₂ S₂ hS₂ V₂ ⟶ P₂}
    (h : ((quasicoherentPullbackUnitIso B₁ S₁ hS₁ g₁).inv ≫
      quasicoherentPullbackMap B₁ S₁ hS₁ g₁ t₁) ≫ θ₁ = ν₁)
    (hV : HEq V₁ V₂) (hU : HEq U₁ U₂) (hg : HEq g₁ g₂) (hK : HEq K₁ K₂) (ht : HEq t₁ t₂)
    (hP : HEq P₁ P₂) (hθ : HEq θ₁ θ₂) (hν : HEq ν₁ ν₂) :
    representedUnitChartHom B₂ S₂ hS₂
        ((quasicoherentPullbackUnitIso B₂ S₂ hS₂ g₂).inv ≫
          quasicoherentPullbackMap B₂ S₂ hS₂ g₂ t₂) ≫
      ((representedQuasicoherentSchemeEquivalence B₂ S₂ hS₂ V₂).functor.map θ₂).hom =
    representedUnitChartHom B₂ S₂ hS₂ ν₂ := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hV hU
  subst hg hK
  subst ht hP
  subst hθ hν
  exact representedUnitChartHom_comp_map_hom_of_comp_eq _ _ _ h

variable {s f L ψ} in
/-- **The middle factor of the chart maps is unital, over the site of `s.shrink`**: the hypothesis
`hm` of `…InvertibleTwistingRestriction.modulePullback_map_thetaSourceUnit_chartMap_of_squares`,
from `…InvertibleTwistingRestriction.quasicoherentPullbackUnit_comp_chartSchemeTheta` over `s.site`
through `…representedUnitChartHom_comp_map_hom_of_site_heq`. -/
theorem representedUnitChartHom_comp_chartSchemeTheta_shrink
    {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    representedUnitChartHom s.shrink.site s.shrink.base s.shrink.containsBase
        ((quasicoherentPullbackUnitIso s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))).inv ≫
          quasicoherentPullbackMap s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceUnit T (locusPoint w ≫ f.hom))) ≫
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase T).functor.map
        (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) 0)).hom =
    representedUnitChartHom s.shrink.site s.shrink.base s.shrink.containsBase
      (pointLaurentPieceUnit L T (locusPoint w)) :=
  representedUnitChartHom_comp_map_hom_of_site_heq s.shrink_site.symm s.shrink_base.symm
    (quasicoherentPullbackUnit_comp_chartSchemeTheta s f L ψ (locusPoint w)
      (locusOpen_locusPoint w))
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

variable {s f L ψ} in
/-- **The target factor `τ_w = …chartTargetIso w` of the chart maps is unital**: the instance of
`AlgebraicGeometry.Space.pointTargetIso_symm_trans_hom_one_restrict` at the inclusion
`U(ψ) ⊆ X`, with the unit `…InvertibleTwistingRestriction.thetaTargetUnit` of the target. -/
theorem chartTargetIso_hom_one {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    type_of% (pointTargetIso_symm_trans_hom_one_restrict L (locusInclusionOfUnitalHom s f L ψ) w
      (locusPoint w) (pointHom_locusPoint w) (τ := chartTargetIso w 0)
      (chartTargetIso.eq_1 w 0 : _)) :=
  pointTargetIso_symm_trans_hom_one_restrict L (locusInclusionOfUnitalHom s f L ψ) w
    (locusPoint w) (pointHom_locusPoint w) (τ := chartTargetIso w 0) (chartTargetIso.eq_1 w 0 : _)

/-! ### `θ` is a map of graded algebras -/

variable {s f L ψ Px} in
/-- **`θ` is multiplicative**: the chart maps are multiplicative at every scheme point
(`…InvertibleTwistingRestriction.modulePullback_map_thetaSourceMul_comp_chartMap`), and
multiplicativity descends (`AlgebraicGeometry.Space.mul_comp_pointFamilyDescendedHom`). -/
theorem descendedTheta_mul (i j : ℤ) :
    (thetaSourceMul (ofUnitalHom s f L ψ) X.property Px i j :
        (thetaSourceOfUnitalHom s f L ψ Px i).obj ⊗ (thetaSourceOfUnitalHom s f L ψ Px j).obj ⟶
          (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj) ≫ descendedTheta Px P (i + j) =
      (descendedTheta Px P i ⊗ₘ descendedTheta Px P j) ≫ thetaTargetMul s f L ψ i j := by
  refine mul_comp_pointFamilyDescendedHom P (pointFamilyNatural_chartMap Px i)
    (pointFamilyNatural_chartMap Px j) (pointFamilyNatural_chartMap Px (i + j))
    (thetaSourceMul (ofUnitalHom s f L ψ) X.property Px i j :
      (thetaSourceOfUnitalHom s f L ψ Px i).obj ⊗ (thetaSourceOfUnitalHom s f L ψ Px j).obj ⟶
        (thetaSourceOfUnitalHom s f L ψ Px (i + j)).obj) (thetaTargetMul s f L ψ i j) ?_
  intro T w
  have h := modulePullback_map_thetaSourceMul_comp_chartMap w Px i j
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_))
    rfl

variable {s f L ψ Px} in
/-- **`θ` is unital**, from the unitality of the three factors of the chart maps
(`…chartSourceIso_hom_one_shrink`, `…representedUnitChartHom_comp_chartSchemeTheta`,
`…InvertibleTwistingRestriction.chartTargetIso_hom_one`). -/
theorem descendedTheta_one :
    thetaSourceUnit (ofUnitalHom s f L ψ) X.property Px ≫ descendedTheta Px P 0 =
      thetaTargetUnit s f L ψ := by
  have key := @comp_pointFamilyDescendedHom_eq _ _ _ _ P _ _ _ (pointFamilyNatural_chartMap Px 0) _
    (SheafOfModules.isQuasicoherentOnSite_unit _) _ _
    (fun _ w => modulePullback_map_thetaSourceUnit_chartMap_of_squares Px w
      (representedUnitChartHom_comp_chartSchemeTheta_shrink w) (chartTargetIso_hom_one w))
  exact key

variable {s f L ψ} in
/-- **Clause (1) of [Stacks, Tag 0D2Z] for `θ`**, from clause (1) at the scheme points. -/
theorem descendedTheta_clauseOneSections
    (hone : ∀ (d : ℕ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
    ClauseOneSections s f L ψ Px (thetaOfFamily P (pointFamilyNatural_chartMap Px)) :=
  clauseOneSections_thetaOfFamily P (pointFamilyNatural_chartMap Px) hone

variable {s f L ψ Px} in
/-- **`θ` is characterized by clause (3) at the scheme points**: a map with the same
restrictions to the scheme points of `U(ψ)` is `θ`. -/
theorem eq_descendedTheta
    (θ' : ∀ d : ℤ, (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj)
    (hθ' : ∀ (d : ℤ) {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (θ' d) =
        (chartSourceIso Px w (locusOpen_locusPoint w) d).hom ≫
          ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
              s.shrink.containsBase T).functor.map
            (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom ≫
          (chartTargetIso w d).hom) :
    θ' = descendedTheta Px P :=
  funext fun d => eq_thetaOfFamily P (pointFamilyNatural_chartMap Px) d (θ' d)
    (fun _ w => hθ' d w)

/-- **[Stacks, Tag 0D2Z] for `X` an algebraic space.**  In Situation 0849 let `f : X ⟶ Y` be a
morphism of algebraic spaces, `ℒ` an invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a
homomorphism of graded algebras.  Then `U(ψ)` is an open subspace of `X`, `r_{ℒ,ψ} : U(ψ) ⟶
Proj_Y(𝒜)` is a morphism over `Y` with clauses (2)(a), (2)(b), characterized by (2)(b), and
satisfying clause (3); and there is a map `θ : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` of graded
algebras with clause (1), whose restriction to every scheme point `w : W ⟶ U(ψ)` is `θ` of
[Stacks, Tag 01O9] for `w^*ψ`, which for every square `g ∘ f' = f ∘ g'` with `X'`, `Y'` schemes
restricts to the map `θ'` of the pullback `ψ'` on every scheme over `U(ψ') = (g')^{-1}(U(ψ))`
(clause (3)), and which is the only map with these restrictions. -/
@[stacks 0D2Z "the whole lemma, in Situation 0849 with Proj_Y(A) the relative Proj of Stacks 084B \
and X an algebraic space over the algebraic space Y: U(psi) an open subspace of X; the morphism \
r_{L,psi} : U(psi) -> Proj_Y(A) over Y with clauses (2)(a), (2)(b) and characterized by (2)(b); \
clause (3) for the open and the morphism; theta : r^*((+)_d O(d)) -> (+)_d L^d|_{U(psi)} a \
unital multiplicative map with clause (1), restricting at every scheme point of U(psi) to theta \
of Tag 01O9 and along every square with X', Y' schemes to the theta of the pulled-back psi \
(clause (3)), and the only map with these restrictions"]
theorem tag0D2Z_space :
    IsOpenSubspace s.site s.base s.containsBase (ofUnitalHom s f L ψ).locus ∧
    (ofUnitalHom s f L ψ).invertibleMorphism ≫ s.relativeProjπ =
      (ofUnitalHom s f L ψ).locus.ι ≫ f.hom ∧
    (∀ {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X.1) {k : ℕ}
      (_ : 0 < k) [Epi (((ofUnitalHom s f L ψ).twisting W w).app (k : ℤ))],
      yonedaEquiv w ∈ (ofUnitalHom s f L ψ).locus.obj (Opposite.op W)) ∧
    (∀ {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X.1) {k : ℕ}
      (hk : 0 < k) [Epi (((ofUnitalHom s f L ψ).twisting W w).app (k : ℤ))],
      (ofUnitalHom s f L ψ).factor w (mem_locus_ofUnitalHom_of_epi s f L ψ w hk) ≫
          (ofUnitalHom s f L ψ).invertibleMorphism =
        (ofUnitalHom s f L ψ).quadruplePoint w hk) ∧
    (∀ Φ : (ofUnitalHom s f L ψ).locus.toFunctor ⟶ s.relativeProjFunctor,
      Φ ≫ s.relativeProjπ = (ofUnitalHom s f L ψ).locus.ι ≫ f.hom →
      (∀ {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X.1) {k : ℕ}
        (hk : 0 < k) [Epi (((ofUnitalHom s f L ψ).twisting W w).app (k : ℤ))],
        (ofUnitalHom s f L ψ).factor w (mem_locus_ofUnitalHom_of_epi s f L ψ w hk) ≫ Φ =
          (ofUnitalHom s f L ψ).quadruplePoint w hk) →
      Φ = (ofUnitalHom s f L ψ).invertibleMorphism) ∧
    (∀ {X' Y' : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X.1)
      (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f.hom),
      (ofUnitalHom s f L ψ).locus.preimage g' = subspaceOfOpens s.site s.base s.containsBase X'
          (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen ∧
      ∀ {T : BigFppfOver s.site s.base s.containsBase} (t : T ⟶ X')
        (ht : yonedaEquiv (yoneda.map t ≫ g') ∈ (ofUnitalHom s f L ψ).locus.obj (Opposite.op T)),
        (s.relativeProjPoints.pointEquivProjOver Y' g (t ≫ f')
            ⟨(ofUnitalHom s f L ψ).factor (yoneda.map t ≫ g') ht ≫
                (ofUnitalHom s f L ψ).invertibleMorphism,
              (ofUnitalHom s f L ψ).factor_invertibleMorphism_comp_π g' f' g hsq t ht⟩).1 =
          Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.liftOfPreimageEqTop _
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map t)
              ((ofUnitalHom s f L ψ).preimage_coveringOpen_squarePsi_eq_top g' f' g hsq t ht) ≫
            (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).globalMorphism
              (relativeProj
                (s.relativeProjPoints.algebra Y' g))) ∧
    ∃ θ : ∀ d : ℤ,
        (thetaSourceOfUnitalHom s f L ψ (basePresentation s) d).obj ⟶ (thetaTarget s f L ψ d).obj,
      (∀ i j : ℤ,
        thetaSourceMul (ofUnitalHom s f L ψ) X.property (basePresentation s) i j ≫ θ (i + j) =
          (θ i ⊗ₘ θ j) ≫ thetaTargetMul s f L ψ i j) ∧
      thetaSourceUnit (ofUnitalHom s f L ψ) X.property (basePresentation s) ≫ θ 0 =
        thetaTargetUnit s f L ψ ∧
      ClauseOneSections s f L ψ (basePresentation s) θ ∧
      (∀ (d : ℤ) {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
        (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
            (θ d) =
          (chartSourceIso (basePresentation s) w (locusOpen_locusPoint w) d).hom ≫
            ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
                s.shrink.containsBase T).functor.map
              (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom ≫
            (chartTargetIso w d).hom) ∧
      (∀ {X' Y' : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X.1)
        (f' : X' ⟶ Y') (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f.hom)
        (d : ℤ) {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase} (t : T ⟶ X')
        (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)
        (hw : yoneda.map t ≫ g' = locusPoint w)
        (k : (BigFppfOver.toScheme s.site s.base s.containsBase).obj T ⟶
          (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen.toScheme)
        (hk : k ≫ (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen.ι =
          (BigFppfOver.toScheme s.site s.base s.containsBase).map t),
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
            (θ d) =
          (chartSourceIso (basePresentation s) w (locusOpen_locusPoint w) d).hom ≫
            ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
                s.shrink.containsBase T).functor.map
              (eqToHom (chartSchemeThetaSource_congr s f L ψ hw
                  (locusOpen_comp_eq_top_of_eq g' t w hw) (locusOpen_locusPoint w) d).symm ≫
                squarePointChartTheta s f L ψ g' f' g hsq t
                  (locusOpen_comp_eq_top_of_eq g' t w hw) k hk d ≫
                eqToHom (congrArg (fun z => pointLaurentPieceQcoh L T z d) hw))).hom ≫
            (chartTargetIso w d).hom) ∧
      (∀ θ' : ∀ d : ℤ,
          (thetaSourceOfUnitalHom s f L ψ (basePresentation s) d).obj ⟶ (thetaTarget s f L ψ d).obj,
        (∀ (d : ℤ) {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
          (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
          (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
              (θ' d) =
            (chartSourceIso (basePresentation s) w (locusOpen_locusPoint w) d).hom ≫
              ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
                  s.shrink.containsBase T).functor.map
                (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom ≫
              (chartTargetIso w d).hom) →
        θ' = θ) := by
  refine ⟨isOpenSubspace_locus_ofUnitalHom s f L ψ, invertibleMorphism_comp_π_ofUnitalHom s f L ψ,
    ?_, ?_, fun Φ hΦπ hΦ => eq_invertibleMorphism_ofUnitalHom s f L ψ Φ hΦπ hΦ,
    fun g' f' g hsq => invertibleMorphism_baseChange_square_ofUnitalHom s f L ψ g' f' g hsq,
    descendedTheta (basePresentation s) (locusPresentation s f L ψ),
    descendedTheta_mul (locusPresentation s f L ψ),
    descendedTheta_one (locusPresentation s f L ψ),
    descendedTheta_clauseOneSections (basePresentation s) (locusPresentation s f L ψ)
      (fun d _ w => modulePullback_map_clauseOneProjLeg_comp_chartMap (basePresentation s) w d),
    fun d _ w => modulePullback_map_pointHom_descendedTheta (basePresentation s)
      (locusPresentation s f L ψ) d w,
    fun {_ _} g' f' g hsq d {_} t w hw k hk => modulePullback_map_pointHom_descendedTheta_square
      (basePresentation s) (locusPresentation s f L ψ) g' f' g hsq d t w hw k hk,
    fun θ' hθ' => eq_descendedTheta (locusPresentation s f L ψ) θ' hθ'⟩
  · intro W w k hk _
    exact mem_locus_ofUnitalHom_of_epi s f L ψ w hk
  · intro W w k hk _
    exact factor_invertibleMorphism_ofUnitalHom_of_epi s f L ψ w hk

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end

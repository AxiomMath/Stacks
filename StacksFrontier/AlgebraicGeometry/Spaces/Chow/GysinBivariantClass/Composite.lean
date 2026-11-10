module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupCanonicalIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.Cap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupMapOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinDivisorKeyFormulaCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackSquareCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinMemberRuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardSectionDivisorDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinCommutativity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionOfGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafModuleMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# The Gysin cap along composites: axioms (1) and (2) of Stacks 0ERJ

A part of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass`: the component cycles
of the pulled-back section, the pulled-back triple along a composite, and the naturality of
`AlgebraicGeometry.Space.gysinBivariantCap` for proper pushforward (Stacks 0ER5) and for flat
pullback (Stacks 0ER6).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] pointTopology

section Vanishing

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (σ : L.sections) (hL : IsInvertibleSheaf D p hp L)
    (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (q : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)

include hL in
/-- An invertible sheaf in the spelling of Stacks 0ER1 is an invertible module in the spelling of
`AlgebraicGeometry.Space.canonicalDivisorCycleAt`. -/
private theorem isInvertibleModule_of_isInvertibleSheaf :
    IsInvertibleModule (B := D.site) ⟨X, hp.1⟩ L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL

end Vanishing

/-! ### The component cycles of the pulled-back section -/

section Component

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (σ : L.sections) (hL : IsInvertibleSheaf D p hp L)
    (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (q : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hqB : q.hom ≫ p = p') (hq : IsProper D.site D.base D.base_mem q.hom) (k : ℤ)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (h : W'.subspace.toFunctor ⟶ (chernImage D hp' hp q W').subspace.toFunctor)
    (hh : h ≫ (chernImage D hp' hp q W').subspace.ι = W'.subspace.ι ≫ q.hom)

include hL in
/-- `σ|_W` is a regular meromorphic section of `ℒ|_W` on an integral closed subspace `W ⊄ E`. -/
private theorem isRegularMeromorphicSection_integralClosedSubspaceRestrictSection
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L σ).1) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      W.isClosedSubspace.1 (integralClosedSubspaceRestrict D p hp L W)
      (globalSectionMeromorphic D.site D.base D.base_mem _ _
        (integralClosedSubspaceRestrictSection D p hp L σ W)) :=
  isRegularMeromorphicSection_of_ne_zero_of_isGood D (W.subspace.ι ≫ p)
    (isGood_integralClosedSubspace D p hp W) W.isIntegralSpace
    (integralClosedSubspaceRestrict D p hp L W)
    (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W)
    (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D _
      (isGood_integralClosedSubspace D p hp W) _
      (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W)
      (closedSubspaceRestrictSection_ne_zero D p hp L σ hL ⟨W.subspace, W.isClosedSubspace⟩ hWE))

include hL in
/-- **The rule off `E`, read on `W` as an integral closed subspace.**  Off `E = Z(σ)` the value of
`AlgebraicGeometry.Space.restrictedSectionChernRule` is the Weil divisor of
`σ|_W = integralClosedSubspaceRestrictSection σ W`, with the invertibility of `ℒ|_W` given as
that of an inverse image (`AlgebraicGeometry.Space.modulePullbackInvertible`). -/
private theorem restrictedSectionChernRule_of_not_le_eq
    (chern : FirstChernComponentCycleRule D p k)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L σ).1)
    (hLm : IsInvertibleModule (B := D.site) ⟨X, hp.1⟩ L)
    (hk : deltaDimensionClosed D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    restrictedSectionChernRule D p hp L σ hL k chern W hW =
      canonicalDivisorCycleAt D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        W.isIntegralSpace (integralClosedSubspaceRestrict D p hp L W)
        (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hp.1 W.subspace
          W.isClosedSubspace) L hLm)
        (globalSectionMeromorphic D.site D.base D.base_mem _ _
          (integralClosedSubspaceRestrictSection D p hp L σ W))
        (isRegularMeromorphicSection_integralClosedSubspaceRestrictSection D p hp L σ hL hWE)
        hk := by
  rw [restrictedSectionChernRule, dite_eq_right hWE]
  rfl

/-- **Weil divisors carried along an isomorphism, with the carried section named.**  If
`e : M ≅ M'` carries `τ` to `τ'`, the Weil divisors of `τ` and `τ'` agree
(`AlgebraicGeometry.Space.canonicalDivisorCycleAt_sectionsMap_iso`). -/
private theorem canonicalDivisorCycleAt_eq_of_sectionsMap_iso
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y)
    {M M' : Modules.{u, u} D.site D.base D.base_mem Y hY.1}
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (hM' : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M') (e : M ≅ M')
    {τ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M}
    {τ' : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M'}
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ)
    (hτ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M' τ')
    (he : SheafOfModules.sectionsMap
      (meromorphicSectionSheafMap D.site D.base D.base_mem Y hY.1 e.hom) τ = τ') {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalDivisorCycleAt D sY hY hint M hM τ hτ hk =
      canonicalDivisorCycleAt D sY hY hint M' hM' τ' hτ' hk := by
  subst he
  exact (canonicalDivisorCycleAt_sectionsMap_iso D sY hY hint M M' hM hM' e τ hτ hτ' hk).symm

/-- **The identification `g^*f^*ℳ ≅ g'^*f'^*ℳ` along a commuting square carries `g^*(f^*s)` to
`g'^*(f'^*s)`**: it is the composite of the comparisons of Stacks 03LU, which carry iterated
inverse images of sections to inverse images along composites. -/
private theorem sectionsMap_modulePullbackCompIso_trans_hom
    {A B B' C : AlgebraicSpaces D.site D.base D.base_mem}
    (g : A ⟶ B) (f : B ⟶ C) (g' : A ⟶ B') (f' : B' ⟶ C) (hgf : g ≫ f = g' ≫ f')
    (M : Modules.{u, u} D.site D.base D.base_mem C.1 C.2) (s : M.sections) :
    SheafOfModules.sectionsMap ((modulePullbackCompIso D.site D.base D.base_mem g f).app M ≪≫
        eqToIso (congrArg (fun k => (modulePullback D.site D.base D.base_mem k).obj M) hgf) ≪≫
          ((modulePullbackCompIso D.site D.base D.base_mem g' f').app M).symm).hom
        (modulePullbackSections D.site D.base D.base_mem g _
          (modulePullbackSections D.site D.base D.base_mem f M s)) =
      modulePullbackSections D.site D.base D.base_mem g' _
        (modulePullbackSections D.site D.base D.base_mem f' M s) := by
  rw [Iso.trans_hom, Iso.trans_hom, SheafOfModules.sectionsMap_comp,
    SheafOfModules.sectionsMap_comp, Iso.app_hom,
    sectionsMap_modulePullbackCompIso_modulePullbackSections, eqToIso.hom,
    sectionsMap_eqToHom_modulePullbackSections D.site D.base D.base_mem M hgf, Iso.symm_hom,
    Iso.app_inv, sectionsMap_modulePullbackCompIso_inv_modulePullbackSections]

/-- **The identification `t^*a^*b^*ℳ ≅ t^*c^*ℳ` for `a ≫ b = c` carries `t^*(a^*(b^*s))` to
`t^*(c^*s)`**: it is a composite of the comparisons of Stacks 03LU, which carry iterated inverse
images of sections to inverse images along composites. -/
private theorem sectionsMap_modulePullbackCompIso_trans_comp_hom
    {A B C E : AlgebraicSpaces D.site D.base D.base_mem}
    (t : A ⟶ B) (a : B ⟶ C) (b : C ⟶ E) (c : B ⟶ E) (hc : (t ≫ a) ≫ b = t ≫ c)
    (M : Modules.{u, u} D.site D.base D.base_mem E.1 E.2) (s : M.sections) :
    SheafOfModules.sectionsMap ((modulePullbackCompIso D.site D.base D.base_mem t a).app
        ((modulePullback D.site D.base D.base_mem b).obj M) ≪≫
        ((modulePullbackCompIso D.site D.base D.base_mem (t ≫ a) b).app M ≪≫
          eqToIso (congrArg (fun k => (modulePullback D.site D.base D.base_mem k).obj M) hc) ≪≫
            ((modulePullbackCompIso D.site D.base D.base_mem t c).app M).symm)).hom
        (modulePullbackSections D.site D.base D.base_mem t _
          (modulePullbackSections D.site D.base D.base_mem a _
            (modulePullbackSections D.site D.base D.base_mem b M s))) =
      modulePullbackSections D.site D.base D.base_mem t _
        (modulePullbackSections D.site D.base D.base_mem c M s) := by
  rw [Iso.trans_hom, SheafOfModules.sectionsMap_comp, Iso.app_hom,
    sectionsMap_modulePullbackCompIso_modulePullbackSections,
    sectionsMap_modulePullbackCompIso_trans_hom D (t ≫ a) b t c hc M s]

end Component

/-! ### The projection formula for the restricted-section rules (Stacks 0ER5, after `i_*`) -/

section Projection

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (σ : L.sections) (hL : IsInvertibleSheaf D p hp L)
    (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (q : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hqB : q.hom ≫ p = p') (hq : IsProper D.site D.base D.base_mem q.hom) (k : ℤ)

include hL in
/-- **Clause (1)(b) of Stacks 0ER1 against the canonical rule of Stacks 0EQJ**: on every `W` the
Weil divisor of the section of Stacks 0EPQ and that of the canonical section of `ℒ|_W` differ by
a principal divisor (Stacks 0EPT). -/
private theorem isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_sub
    (hLm : IsInvertibleModule (B := D.site) ⟨X, hp.1⟩ L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k + 1) :
    IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      W.isIntegralSpace k
      (restrictedDivisorCycle D p hp L k hL W hW - canonicalFirstChernRule D p hp L hLm k W hW) :=
  isPrincipalDivisorCycleOfGood_canonicalDivisorCycleAt_sub D _
    (isGood_integralClosedSubspace D p hp W) W.isIntegralSpace _
    (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W) _ _
    (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem
      (isGood_integralClosedSubspace D p hp W).1 W.isIntegralSpace
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D p hp W)) _
      (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W))
    (isRegularMeromorphicSection_componentMeromorphicSection p hp
      (subspaceDivisorSetupOfIsGood D p hp) L hLm W) _

end Projection

/-! ### The pulled-back triple along a composite (Stacks 0ERP, the glue of 0ERJ (1) and (2)) -/

section Composite

variable (D : BaseSpaceDimensionSituation.{u})

/-- Pushing a cycle on a closed subspace `A` forward to an equal closed subspace `B` along
`eqToHom` and then into the ambient space is pushing it from `A` into the ambient space. -/
private theorem cycleGroupClosedPushforward_properCyclePushforward_eqToHom {Y : D.Ambient}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {A B : ClosedSubspaces D.site D.base D.base_mem Y}
    (hAB : A.1 = B.1) (hA : D.IsGood (A.1.ι ≫ sY)) (hB : D.IsGood (B.1.ι ≫ sY))
    (hfB : eqToHom (congrArg Subfunctor.toFunctor hAB) ≫ B.1.ι ≫ sY = A.1.ι ≫ sY)
    (hqc : IsQuasiCompact D.site D.base D.base_mem (eqToHom (congrArg Subfunctor.toFunctor hAB)))
    (k : ℤ) (β : CycleGroup D (A.1.ι ≫ sY) k) :
    cycleGroupClosedPushforward D hY.1 B.2.1 (D.isDecentSpace_of_isGood sY hY) B.2.2 sY hY.2.2
        (B.1.ι ≫ sY) rfl k (properCyclePushforward D (A.1.ι ≫ sY) hA (B.1.ι ≫ sY) hB hfB hqc k β) =
      cycleGroupClosedPushforward D hY.1 A.2.1 (D.isDecentSpace_of_isGood sY hY) A.2.2 sY hY.2.2
        (A.1.ι ≫ sY) rfl k β := by
  obtain ⟨A, hA'⟩ := A
  obtain ⟨B, hB'⟩ := B
  obtain rfl : A = B := hAB
  rw [properCyclePushforward_congr D _ hA _ hB (eqToHom_refl _ _) hfB hqc (Category.id_comp _)
    (eqToHom_refl A.toFunctor (congrArg Subfunctor.toFunctor rfl) ▸ hqc) k β,
    properCyclePushforward_id]

/-- Proper pushforward of cycles commutes with the transport of `Z_a` to `Z_b` along `a = b`. -/
private theorem properCyclePushforward_degree_cast {Y Z : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) {f : Y ⟶ Z} (hfB : f ≫ sZ = sY)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) {a b : ℤ} (hab : a = b)
    (α : CycleGroup D sY a) :
    (hab ▸ properCyclePushforward D sY hY sZ hZ hfB hf a α : CycleGroup D sZ b) =
      properCyclePushforward D sY hY sZ hZ hfB hf b (hab ▸ α) := by
  subst hab
  rfl

/-- If `[e_* G₁] = [G₂]`, then `[j_* G₂] = [(e ≫ j)_* G₁]` (Stacks 0EQC and Stacks 0EP2). -/
private theorem chowClassCanonical_properCyclePushforward_comp_of_eq
    {A C P : D.Ambient} (sA : A ⟶ D.space) (sC : C ⟶ D.space) (sP : P ⟶ D.space)
    (hA : D.IsGood sA) (hC : D.IsGood sC) (hP : D.IsGood sP) {e : A ⟶ C} {j : C ⟶ P}
    (heB : e ≫ sC = sA) (hjB : j ≫ sP = sC) (he : IsProper D.site D.base D.base_mem e)
    (hj : IsProper D.site D.base D.base_mem j) (k : ℤ) (G₁ : CycleGroup D sA k)
    (G₂ : CycleGroup D sC k)
    (hG : chowClassCanonical.{u + 1} D sC hC k
        (properCyclePushforward D sA hA sC hC heB he.2.1.2 k G₁) =
      chowClassCanonical.{u + 1} D sC hC k G₂) :
    chowClassCanonical.{u + 1} D sP hP k (properCyclePushforward D sC hC sP hP hjB hj.2.1.2 k G₂) =
      chowClassCanonical.{u + 1} D sP hP k (properCyclePushforward D sA hA sP hP
        (by rw [Category.assoc, hjB, heB])
        (isProper_comp D.site D.base D.base_mem hA.1 hC.1 hP.1 e j he hj).2.1.2 k G₁) := by
  rw [← chowGroupCanonicalProperPushforward_chowClassCanonical D sC hC sP hP hjB hj, ← hG,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_comp D sA sC sP hA hC hP heB hjB he hj]

/-- **Bookkeeping of proper pushforwards of classes around a square.**  If `ψ ≫ i = e ≫ j ≫ h'`
for proper morphisms, `[x] = [ψ_* G₁]` and `[e_* G₁] = [G₂]`, then `[i_* x] = [h'_* j_* G₂]`
(Stacks 0EQC and Stacks 0EP2). -/
private theorem chowClassCanonical_properCyclePushforward_of_comp_eq
    {A B C P Q : D.Ambient} (sA : A ⟶ D.space) (sB : B ⟶ D.space) (sC : C ⟶ D.space)
    (sP : P ⟶ D.space) (sQ : Q ⟶ D.space) (hA : D.IsGood sA) (hB : D.IsGood sB)
    (hC : D.IsGood sC) (hP : D.IsGood sP) (hQ : D.IsGood sQ) {ψ : A ⟶ B} {i : B ⟶ Q}
    {e : A ⟶ C} {j : C ⟶ P} {h' : P ⟶ Q} (hψB : ψ ≫ sB = sA) (hiB : i ≫ sQ = sB)
    (heB : e ≫ sC = sA) (hjB : j ≫ sP = sC) (hh'B : h' ≫ sQ = sP)
    (hψ : IsProper D.site D.base D.base_mem ψ) (hi : IsProper D.site D.base D.base_mem i)
    (he : IsProper D.site D.base D.base_mem e) (hj : IsProper D.site D.base D.base_mem j)
    (hh' : IsProper D.site D.base D.base_mem h') (hsq : ψ ≫ i = e ≫ j ≫ h') (k : ℤ)
    (x : CycleGroup D sB k) (G₁ : CycleGroup D sA k) (G₂ : CycleGroup D sC k)
    (hx : chowClassCanonical.{u + 1} D sB hB k x =
      chowClassCanonical.{u + 1} D sB hB k (properCyclePushforward D sA hA sB hB hψB hψ.2.1.2 k G₁))
    (hG : chowClassCanonical.{u + 1} D sC hC k
        (properCyclePushforward D sA hA sC hC heB he.2.1.2 k G₁) =
      chowClassCanonical.{u + 1} D sC hC k G₂) :
    chowClassCanonical.{u + 1} D sQ hQ k (properCyclePushforward D sB hB sQ hQ hiB hi.2.1.2 k x) =
      chowClassCanonical.{u + 1} D sQ hQ k (properCyclePushforward D sP hP sQ hQ hh'B hh'.2.1.2 k
        (properCyclePushforward D sC hC sP hP hjB hj.2.1.2 k G₂)) := by
  have hjh' := isProper_comp D.site D.base D.base_mem hC.1 hP.1 hQ.1 j h' hj hh'
  have hjh'B : (j ≫ h') ≫ sQ = sC := by rw [Category.assoc, hh'B, hjB]
  rw [← chowGroupCanonicalProperPushforward_chowClassCanonical D sB hB sQ hQ hiB hi, hx,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_comp D sA sB sQ hA hB hQ hψB hiB hψ hi,
    properCyclePushforward_congr D sA hA sQ hQ hsq _ _
      (by rw [Category.assoc, hjh'B, heB])
      (isProper_comp D.site D.base D.base_mem hA.1 hC.1 hQ.1 e (j ≫ h') he hjh').2.1.2,
    ← chowClassCanonical_properCyclePushforward_comp_of_eq D sA sC sQ hA hC hQ heB hjh'B he hjh' k
      G₁ G₂ hG,
    properCyclePushforward_comp D sC sP sQ hC hP hQ hjB hh'B hj hh']

/-- Pushing forward along `f` and then along a left inverse `f'` of `f` is the identity on cycles
(Stacks 0EP2). -/
private theorem properCyclePushforward_properCyclePushforward_of_comp_eq_id {A B : D.Ambient}
    (sA : A ⟶ D.space) (hA : D.IsGood sA) (sB : B ⟶ D.space) (hB : D.IsGood sB) {f : A ⟶ B}
    {f' : B ⟶ A} (hff' : f ≫ f' = 𝟙 A) (hfB : f ≫ sB = sA) (hf'B : f' ≫ sA = sB)
    (hf : IsProper D.site D.base D.base_mem f) (hf' : IsProper D.site D.base D.base_mem f')
    (k : ℤ) (x : CycleGroup D sA k) :
    properCyclePushforward D sB hB sA hA hf'B hf'.2.1.2 k
      (properCyclePushforward D sA hA sB hB hfB hf.2.1.2 k x) = x := by
  rw [properCyclePushforward_comp D sA sB sA hA hB hA hfB hf'B hf hf',
    properCyclePushforward_congr D sA hA sA hA hff' _ _ (Category.id_comp sA)
      (isProper_of_isIso D.site D.base D.base_mem (𝟙 A)).2.1.2, properCyclePushforward_id]

/-- Flat pullback of cycles commutes with the transport of degrees along `k = k'`, `n = n'`. -/
private theorem flatPullbackMap_degree_cast {Y Z : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) {f : Y ⟶ Z} (hfB : f ≫ sZ = sY)
    (r : ℕ) (hf : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) {k n k' n' : ℤ} (hk : k = k')
    (hn : n = n') (hkn : k + (r : ℤ) = n) (hkn' : k' + (r : ℤ) = n') (x : CycleGroup D sZ k) :
    (hn ▸ flatPullbackMap D sY hY sZ hZ f hfB r hf hr k n hkn x : CycleGroup D sY n') =
      flatPullbackMap D sY hY sZ hZ f hfB r hf hr k' n' hkn' (hk ▸ x) := by
  subst hk hn
  rfl

/-- **Bookkeeping of flat pullbacks and isomorphism pushforwards of classes around a square.**
If `ψ ≫ i = e ≫ j ≫ h'` with `i`, `e`, `j` isomorphisms and `ψ`, `h'` flat of relative
dimension `r`, `[G₁] = [ψ^* y]` and `[e_* G₁] = [G₂]`, then `[j_* G₂] = [h'^* i_* y]`: the square
is cartesian, so this is Stacks 0EPD. -/
private theorem chowClassCanonical_flatPullbackMap_of_comp_eq
    {A B C P Q : D.Ambient} (sA : A ⟶ D.space) (sB : B ⟶ D.space) (sC : C ⟶ D.space)
    (sP : P ⟶ D.space) (sQ : Q ⟶ D.space) (hA : D.IsGood sA) (hB : D.IsGood sB)
    (hC : D.IsGood sC) (hP : D.IsGood sP) (hQ : D.IsGood sQ) {ψ : A ⟶ B} {i : B ⟶ Q}
    {e : A ⟶ C} {j : C ⟶ P} {h' : P ⟶ Q} [IsIso i] [IsIso e] [IsIso j] (hψB : ψ ≫ sB = sA)
    (hiB : i ≫ sQ = sB) (heB : e ≫ sC = sA) (hjB : j ≫ sP = sC) (hh'B : h' ≫ sQ = sP) (r : ℕ)
    (hψf : IsFlat D.site D.base D.base_mem ψ)
    (hψr : HasRelativeDimension r D.site D.base D.base_mem ψ)
    (hh'f : IsFlat D.site D.base D.base_mem h')
    (hh'r : HasRelativeDimension r D.site D.base D.base_mem h') (hsq : ψ ≫ i = e ≫ j ≫ h')
    (k m : ℤ) (hkm : k + (r : ℤ) = m) (y : CycleGroup D sB k) (G₁ : CycleGroup D sA m)
    (G₂ : CycleGroup D sC m)
    (hG : chowClassCanonical.{u + 1} D sA hA m G₁ =
      chowClassCanonical.{u + 1} D sA hA m
        (flatPullbackMap D sA hA sB hB ψ hψB r hψf hψr k m hkm y))
    (hT : chowClassCanonical.{u + 1} D sC hC m (properCyclePushforward D sA hA sC hC heB
        (isProper_of_isIso D.site D.base D.base_mem e).2.1.2 m G₁) =
      chowClassCanonical.{u + 1} D sC hC m G₂) :
    chowClassCanonical.{u + 1} D sP hP m (properCyclePushforward D sC hC sP hP hjB
        (isProper_of_isIso D.site D.base D.base_mem j).2.1.2 m G₂) =
      chowClassCanonical.{u + 1} D sP hP m (flatPullbackMap D sP hP sQ hQ h' hh'B r hh'f hh'r k m
        hkm (properCyclePushforward D sB hB sQ hQ hiB
          (isProper_of_isIso D.site D.base D.base_mem i).2.1.2 k y)) := by
  have he := isProper_of_isIso D.site D.base D.base_mem e
  have hj := isProper_of_isIso D.site D.base D.base_mem j
  have hej := isProper_comp D.site D.base D.base_mem hA.1 hC.1 hP.1 e j he hj
  have hejB : (e ≫ j) ≫ sP = sA := by rw [Category.assoc, hjB, heB]
  have hsq' : IsPullback ψ (e ≫ j) i h' :=
    IsPullback.of_vert_isIso ⟨by rw [hsq, Category.assoc]⟩
  rw [chowClassCanonical_properCyclePushforward_comp_of_eq D sA sC sP hA hC hP heB hjB he hj m
      G₁ G₂ hT,
    ← chowGroupCanonicalProperPushforward_chowClassCanonical D sA hA sP hP hejB hej, hG,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    flatPullback_properPushforward_unconditional D sA hA sB hB sP hP sQ hQ hψB hejB hiB hh'B r
      hh'f hh'r hsq' (isProper_of_isIso D.site D.base D.base_mem i) k m hkm y]

variable {X Y' Y'' : D.Ambient} (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ p)) (h : Y'' ⟶ Y')
    (hY'' : D.IsGood ((h ≫ g) ≫ p))

/-- `g^*ℒ` on `Y'`. -/
local notation "𝕃g" => pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L
/-- `g^*σ`. -/
local notation "𝕤g" => pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ
/-- `h^*(g^*ℒ)` on `Y''`. -/
local notation "𝕃₁" => pullbackSheaf D (g ≫ p) hY' ((h ≫ g) ≫ p) hY'' (ObjectProperty.homMk h)
  (pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L)
/-- `h^*(g^*σ)`. -/
local notation "𝕤₁" => pullbackGlobalSection D (g ≫ p) hY' ((h ≫ g) ≫ p) hY''
  (ObjectProperty.homMk h) (pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L)
  (pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ)
/-- `(h ≫ g)^*ℒ` on `Y''`. -/
local notation "𝕃₂" => pullbackSheaf D p hp ((h ≫ g) ≫ p) hY'' (ObjectProperty.homMk (h ≫ g)) L
/-- `(h ≫ g)^*σ`. -/
local notation "𝕤₂" => pullbackGlobalSection D p hp ((h ≫ g) ≫ p) hY''
  (ObjectProperty.homMk (h ≫ g)) L σ
/-- `h^*(g^*ℒ)` is invertible. -/
local notation "h𝕃₁" => isInvertibleSheaf_pullbackSheaf D (g ≫ p) hY' ((h ≫ g) ≫ p) hY''
  (ObjectProperty.homMk h) (pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L)
  (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY'
    (ObjectProperty.homMk g) L hL)
/-- `(h ≫ g)^*ℒ` is invertible. -/
local notation "h𝕃₂" => isInvertibleSheaf_pullbackSheaf D p hp ((h ≫ g) ≫ p) hY''
  (ObjectProperty.homMk (h ≫ g)) L hL

/-- `Z(h^*(g^*σ)) ⊆ Y''`. -/
local notation "𝔼₁" => vanishingLocus D ((h ≫ g) ≫ p) hY'' 𝕃₁ 𝕤₁
/-- `Z((h ≫ g)^*σ) ⊆ Y''`. -/
local notation "𝔼₂" => vanishingLocus D ((h ≫ g) ≫ p) hY'' 𝕃₂ 𝕤₂

include hL in
/-- **`Z(h^*(g^*σ)) = Z((h ≫ g)^*σ)`**: both are the inverse image of `Z(σ)` along `h ≫ g`
(`AlgebraicGeometry.Space.vanishingLocus_pullbackGlobalSection`, Stacks 0ER3). -/
theorem vanishingLocus_pullbackGlobalSection_comp :
    𝔼₁.1 =
      (𝔼₂).1 := by
  rw [vanishingLocus_pullbackGlobalSection D (g ≫ p) hY' _ _
      (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L hL)
      ((h ≫ g) ≫ p) hY'' (ObjectProperty.homMk h),
    vanishingLocus_pullbackGlobalSection D p hp L σ hL (g ≫ p) hY' (ObjectProperty.homMk g),
    vanishingLocus_pullbackGlobalSection D p hp L σ hL ((h ≫ g) ≫ p) hY''
      (ObjectProperty.homMk (h ≫ g))]
  exact (Subfunctor.preimage_comp _ h g).symm

include hL in
/-- **Off the vanishing locus the two rules agree**: at `T ⊄ Z((h ≫ g)^*σ)` the Weil divisor of
`(h^*(g^*σ))|_T` is that of `((h ≫ g)^*σ)|_T`, both being the Weil divisor of `σ` pulled back
along `T ⟶ Y'' ⟶ Y' ⟶ X` (Stacks 03LU and
`AlgebraicGeometry.Space.canonicalDivisorCycleAt_sectionsMap_iso`). -/
private theorem restrictedSectionChernRule_pullbackSheaf_comp_of_not_le (k : ℤ)
    (chern₁ chern₂ : FirstChernComponentCycleRule D ((h ≫ g) ≫ p) k)
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y'')
    (hT : deltaDimension D ((h ≫ g) ≫ p) T = k + 1)
    (hTE : ¬ T.subspace ≤ (𝔼₂).1) :
    restrictedSectionChernRule D ((h ≫ g) ≫ p) hY'' 𝕃₁ 𝕤₁ h𝕃₁ k chern₁ T hT =
      restrictedSectionChernRule D ((h ≫ g) ≫ p) hY'' 𝕃₂ 𝕤₂ h𝕃₂ k chern₂ T hT := by
  have hZ := vanishingLocus_pullbackGlobalSection_comp D p hp L σ hL g hY' h hY''
  have hTE₁ : ¬ T.subspace ≤ 𝔼₁.1 := by
    rwa [hZ]
  have hTg := isGood_integralClosedSubspace D ((h ≫ g) ≫ p) hY'' T
  have hk : deltaDimensionClosed D (T.subspace.ι ≫ (h ≫ g) ≫ p) hTg Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D _ hY'' T, hT]
  have hL₁m := isInvertibleModule_of_isInvertibleSheaf D ((h ≫ g) ≫ p) hY'' 𝕃₁ h𝕃₁
  have hL₂m := isInvertibleModule_of_isInvertibleSheaf D ((h ≫ g) ≫ p) hY'' 𝕃₂ h𝕃₂
  have hc : (closedSubspaceHom D.site D.base D.base_mem hY''.1 T.subspace T.isClosedSubspace ≫
        (ObjectProperty.homMk h : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨Y', hY'.1⟩)) ≫
        (ObjectProperty.homMk g : (⟨Y', hY'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨X, hp.1⟩) =
      closedSubspaceHom D.site D.base D.base_mem hY''.1 T.subspace T.isClosedSubspace ≫
        (ObjectProperty.homMk (h ≫ g) : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base
          D.base_mem) ⟶ ⟨X, hp.1⟩) :=
    ObjectProperty.hom_ext _ (Category.assoc _ _ _)
  have hsec := (sectionsMap_meromorphicSectionSheafMap_globalSectionMeromorphic D.site D.base
    D.base_mem hTg.1 _ _).trans (congrArg (globalSectionMeromorphic D.site D.base D.base_mem
      hTg.1 _) (sectionsMap_modulePullbackCompIso_trans_comp_hom D _ _ _ _ hc L σ))
  rw [restrictedSectionChernRule_of_not_le_eq D _ hY'' 𝕃₁ 𝕤₁ h𝕃₁ k chern₁ hT hTE₁ hL₁m hk,
    restrictedSectionChernRule_of_not_le_eq D _ hY'' 𝕃₂ 𝕤₂ h𝕃₂ k chern₂ hT hTE hL₂m hk,
    canonicalDivisorCycleAt_eq_of_sectionsMap_iso D _ hTg T.isIntegralSpace
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hY''.1 T.subspace
        T.isClosedSubspace) 𝕃₁ hL₁m)
      (modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hY''.1 T.subspace
        T.isClosedSubspace) 𝕃₂ hL₂m) _
      (isRegularMeromorphicSection_integralClosedSubspaceRestrictSection D _ hY'' 𝕃₁ 𝕤₁ h𝕃₁
        hTE₁)
      (isRegularMeromorphicSection_integralClosedSubspaceRestrictSection D _ hY'' 𝕃₂ 𝕤₂ h𝕃₂ hTE)
      hsec hk]

include hL in
/-- **On the vanishing locus the two rules differ by a principal divisor**: at `T` both are
Weil divisors of regular meromorphic sections of `h^*(g^*ℒ)|_T` and of `(h ≫ g)^*ℒ|_T`, which
are isomorphic through Stacks 03LU (Stacks 0EPT,
`AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_sub_of_iso`). -/
private theorem isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_pullbackSheaf_comp (k : ℤ)
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y'')
    (hT : deltaDimension D ((h ≫ g) ≫ p) T = k + 1) :
    IsPrincipalDivisorCycleOfGood D (T.subspace.ι ≫ (h ≫ g) ≫ p)
      (isGood_integralClosedSubspace D ((h ≫ g) ≫ p) hY'' T) T.isIntegralSpace k
      (restrictedDivisorCycle D ((h ≫ g) ≫ p) hY'' 𝕃₁ k h𝕃₁ T hT -
        restrictedDivisorCycle D ((h ≫ g) ≫ p) hY'' 𝕃₂ k h𝕃₂ T hT) := by
  have hLm := isInvertibleModule_of_isInvertibleSheaf D p hp L hL
  have hL₁m := isInvertibleModule_of_isInvertibleSheaf D ((h ≫ g) ≫ p) hY'' 𝕃₁ h𝕃₁
  have hL₂m := isInvertibleModule_of_isInvertibleSheaf D ((h ≫ g) ≫ p) hY'' 𝕃₂ h𝕃₂
  have h1 := isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_sub D ((h ≫ g) ≫ p) hY'' 𝕃₁
    h𝕃₁ k hL₁m T hT
  have h2 := isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_sub D ((h ≫ g) ≫ p) hY'' 𝕃₂
    h𝕃₂ k hL₂m T hT
  have h3 : IsPrincipalDivisorCycleOfGood D (T.subspace.ι ≫ (h ≫ g) ≫ p)
      (isGood_integralClosedSubspace D ((h ≫ g) ≫ p) hY'' T) T.isIntegralSpace k
      (canonicalFirstChernRule D ((h ≫ g) ≫ p) hY'' 𝕃₁ hL₁m k T hT -
        canonicalFirstChernRule D ((h ≫ g) ≫ p) hY'' 𝕃₂ hL₂m k T hT) := by
    have hhg : (ObjectProperty.homMk h : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base
          D.base_mem) ⟶ ⟨Y', hY'.1⟩) ≫
        (ObjectProperty.homMk g : (⟨Y', hY'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨X, hp.1⟩) =
        (ObjectProperty.homMk (h ≫ g) : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base
          D.base_mem) ⟶ ⟨X, hp.1⟩) :=
      ObjectProperty.hom_ext _ rfl
    have e : 𝕃₁ ≅ 𝕃₂ := (modulePullbackCompIso D.site D.base D.base_mem
        (ObjectProperty.homMk h : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨Y', hY'.1⟩)
        (ObjectProperty.homMk g : (⟨Y', hY'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨X, hp.1⟩)).app L ≪≫
      eqToIso (congrArg (fun q : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨X, hp.1⟩ => (modulePullback D.site D.base D.base_mem q).obj L) hhg)
    have h := isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_sub_of_iso hY'' 𝕃₂ 𝕃₁ hL₂m
      hL₁m e.symm k T hT 1
    rw [one_smul] at h
    obtain ⟨_, _, f, heq⟩ := h
    exact ⟨f, f.isUnit, heq⟩
  convert (h1.sub h2).add h3 using 1
  abel

/-- The identification `Z(h^*(g^*σ)) = Z((h ≫ g)^*σ)` as a morphism. -/
local notation "𝕖" => eqToHom (congrArg Subfunctor.toFunctor
  (vanishingLocus_pullbackGlobalSection_comp D p hp L σ hL g hY' h hY''))

include hL in
theorem vanishingLocus_pullbackGlobalSection_comp_hom_structure :
    𝕖 ≫ (𝔼₂).1.ι ≫ (h ≫ g) ≫ p =
      𝔼₁.1.ι ≫ (h ≫ g) ≫ p := by
  rw [← Category.assoc, eqToHom_comp_ι_of_eq D
    (vanishingLocus_pullbackGlobalSection_comp D p hp L σ hL g hY' h hY'')]

include hL in
/-- **The Gysin classes of `h^*(g^*ℒ, g^*σ)` and of `((h ≫ g)^*ℒ, (h ≫ g)^*σ)` agree** in
`CH_k(Z((h ≫ g)^*σ))`, read through `Z(h^*(g^*σ)) = Z((h ≫ g)^*σ)`: pushed into `Y''` both are
cap products of Stacks 0EQJ at restricted-section rules (Stacks 0ER9, step 3), which agree off
the vanishing locus and differ by principal divisors on it, and the rational equivalence descends
(`isRationallyEquivalentToZeroWithinCanonical_preimage_of_closedPushforward`). -/
theorem chowClassCanonical_gysinCycleMap_pullbackSheaf_comp (k : ℤ)
    (α : CycleGroup D ((h ≫ g) ≫ p) (k + 1)) :
    chowClassCanonical.{u + 1} D ((𝔼₂).1.ι ≫
        (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _) k
        (properCyclePushforward D (𝔼₁.1.ι ≫
          (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _)
          ((𝔼₂).1.ι ≫ (h ≫ g) ≫ p)
          (isGood_vanishingLocus D _ hY'' _ _)
          (vanishingLocus_pullbackGlobalSection_comp_hom_structure D p hp L σ hL g hY' h hY'')
          (isProper_of_isIso D.site D.base D.base_mem 𝕖).2.1.2 k
          (gysinCycleMap D ((h ≫ g) ≫ p) 𝔼₁
            (isGood_vanishingLocus D _ hY'' _ _) k
            (sectionGysinRule D ((h ≫ g) ≫ p) hY'' 𝕃₁ 𝕤₁ k h𝕃₁) α)) =
      chowClassCanonical.{u + 1} D ((𝔼₂).1.ι ≫
        (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _) k
        (gysinCycleMap D ((h ≫ g) ≫ p) (𝔼₂)
          (isGood_vanishingLocus D _ hY'' _ _) k
          (sectionGysinRule D ((h ≫ g) ≫ p) hY'' 𝕃₂ 𝕤₂ k h𝕃₂) α) := by
  have hZ := vanishingLocus_pullbackGlobalSection_comp D p hp L σ hL g hY' h hY''
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  refine (isRationallyEquivalentToZeroWithinCanonical_preimage_of_closedPushforward D
    ((h ≫ g) ≫ p) hY'' (𝔼₂).1
    (𝔼₂).2 k subset_rfl ?_
    ).isRationallyEquivalentToZeroCanonical
  rw [map_sub, cycleGroupClosedPushforward_properCyclePushforward_eqToHom D _ hY'' hZ,
    sectionGysinRule, sectionGysinRule,
    cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D _ hY'' 𝕃₁ 𝕤₁ h𝕃₁ k,
    cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D _ hY'' 𝕃₂ 𝕤₂ h𝕃₂ k]
  refine isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_sub D _ hY'' k _ _ α _
    fun T hT _ hne => ?_
  by_cases hTE : T.subspace ≤ (𝔼₂).1
  · have hTE₁ : T.subspace ≤ 𝔼₁.1 := hZ ▸ hTE
    rw [restrictedSectionChernRule_of_le D _ hY'' 𝕃₁ 𝕤₁ h𝕃₁ k
        (restrictedDivisorCycle D ((h ≫ g) ≫ p) hY'' 𝕃₁ k h𝕃₁) hT hTE₁,
      restrictedSectionChernRule_of_le D _ hY'' 𝕃₂ 𝕤₂ h𝕃₂ k
        (restrictedDivisorCycle D ((h ≫ g) ≫ p) hY'' 𝕃₂ k h𝕃₂) hT hTE]
    exact ⟨isPrincipalDivisorCycleOfGood_restrictedDivisorCycle_pullbackSheaf_comp D p hp L hL g
      hY' h hY'' k T hT, subspacePointSet_mono_of_le D hTE⟩
  · exact absurd (restrictedSectionChernRule_pullbackSheaf_comp_of_not_le D p hp L σ hL g hY' h
      hY'' k (restrictedDivisorCycle D ((h ≫ g) ≫ p) hY'' 𝕃₁ k h𝕃₁)
      (restrictedDivisorCycle D ((h ≫ g) ≫ p) hY'' 𝕃₂ k h𝕃₂) T hT hTE) hne

include hL in
/-- **`chowClassCanonical_gysinCycleMap_pullbackSheaf_comp` read in the other direction**: the
class of the Gysin cycle of `h^*(g^*ℒ, g^*σ)` is the pushforward of the one of
`((h ≫ g)^*ℒ, (h ≫ g)^*σ)` along `Z((h ≫ g)^*σ) = Z(h^*(g^*σ))`. -/
private theorem exists_chowClassCanonical_gysinCycleMap_pullbackSheaf_comp (k : ℤ)
    (α : CycleGroup D ((h ≫ g) ≫ p) (k + 1)) :
    ∃ (e : (𝔼₂).1.toFunctor ⟶ 𝔼₁.1.toFunctor) (he : e ≫ 𝔼₁.1.ι = (𝔼₂).1.ι)
      (hep : IsProper D.site D.base D.base_mem e),
      chowClassCanonical.{u + 1} D (𝔼₁.1.ι ≫ (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _) k
          (gysinCycleMap D ((h ≫ g) ≫ p) 𝔼₁ (isGood_vanishingLocus D _ hY'' _ _) k
            (sectionGysinRule D ((h ≫ g) ≫ p) hY'' 𝕃₁ 𝕤₁ k h𝕃₁) α) =
        chowClassCanonical.{u + 1} D (𝔼₁.1.ι ≫ (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _) k
          (properCyclePushforward D ((𝔼₂).1.ι ≫ (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _)
            (𝔼₁.1.ι ≫ (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _)
            (by rw [← Category.assoc, he]) hep.2.1.2 k
            (gysinCycleMap D ((h ≫ g) ≫ p) (𝔼₂) (isGood_vanishingLocus D _ hY'' _ _) k
              (sectionGysinRule D ((h ≫ g) ≫ p) hY'' 𝕃₂ 𝕤₂ k h𝕃₂) α)) := by
  have hZ := vanishingLocus_pullbackGlobalSection_comp D p hp L σ hL g hY' h hY''
  refine ⟨eqToHom (congrArg Subfunctor.toFunctor hZ.symm), eqToHom_comp_ι_of_eq D hZ.symm,
    isProper_of_isIso D.site D.base D.base_mem _, ?_⟩
  have h1 := congrArg (chowGroupCanonicalProperPushforward.{u + 1} D
    ((𝔼₂).1.ι ≫ (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _)
    (𝔼₁.1.ι ≫ (h ≫ g) ≫ p) (isGood_vanishingLocus D _ hY'' _ _)
    (by rw [← Category.assoc, eqToHom_comp_ι_of_eq D hZ.symm])
    (isProper_of_isIso D.site D.base D.base_mem (eqToHom (congrArg Subfunctor.toFunctor hZ.symm)))
    k) (chowClassCanonical_gysinCycleMap_pullbackSheaf_comp D p hp L σ hL g hY' h hY'' k α)
  refine Eq.trans ?_ h1
  exact congrArg (chowClassCanonical.{u + 1} D _ (isGood_vanishingLocus D _ hY'' _ _) k)
    (properCyclePushforward_properCyclePushforward_of_comp_eq_id D _
      (isGood_vanishingLocus D _ hY'' _ _) _ (isGood_vanishingLocus D _ hY'' _ _)
      (by rw [eqToHom_trans, eqToHom_refl])
      (vanishingLocus_pullbackGlobalSection_comp_hom_structure D p hp L σ hL g hY' h hY'') _
      (isProper_of_isIso D.site D.base D.base_mem _) (isProper_of_isIso D.site D.base D.base_mem _)
      k _).symm

section CompositeEq

variable (s₁ : Y' ⟶ D.space) (hY₁ : D.IsGood s₁) (c : Y'' ⟶ X) (hYc : D.IsGood (c ≫ p))

/-- `g^*ℒ` on `Y'`, over the structure morphism `s₁`. -/
local notation "𝕃s" => pullbackSheaf D p hp s₁ hY₁ (ObjectProperty.homMk g) L
/-- `g^*σ`, over `s₁`. -/
local notation "𝕤s" => pullbackGlobalSection D p hp s₁ hY₁ (ObjectProperty.homMk g) L σ
/-- `Z(h^*(g^*σ)) ⊆ Y''`, over `c ≫ p`. -/
local notation "ℤh" => vanishingLocus D (c ≫ p) hYc
  (pullbackSheaf D s₁ hY₁ (c ≫ p) hYc (ObjectProperty.homMk h) 𝕃s)
  (pullbackGlobalSection D s₁ hY₁ (c ≫ p) hYc (ObjectProperty.homMk h) 𝕃s 𝕤s)
/-- `Z(c^*σ) ⊆ Y''`. -/
local notation "ℤc" => vanishingLocus D (c ≫ p) hYc
  (pullbackSheaf D p hp (c ≫ p) hYc (ObjectProperty.homMk c) L)
  (pullbackGlobalSection D p hp (c ≫ p) hYc (ObjectProperty.homMk c) L σ)

include hL in
/-- **The comparison `chowClassCanonical_gysinCycleMap_pullbackSheaf_comp` along any morphism
`c = h ≫ g` and any structure morphism `s₁ = g ≫ p` of the intermediate space**, read in the other
direction: the class of the Gysin cycle of `h^*(g^*ℒ, g^*σ)` is the pushforward of the one of
`(c^*ℒ, c^*σ)` along the identification of the two vanishing loci (Stacks 0ER3). -/
theorem exists_chowClassCanonical_gysinCycleMap_pullbackSheaf_comp_of_eq (k : ℤ)
    (hs₁ : g ≫ p = s₁) (hc : h ≫ g = c) (α : CycleGroup D (c ≫ p) (k + 1)) :
    ∃ (e : (ℤc).1.toFunctor ⟶ (ℤh).1.toFunctor) (he : e ≫ (ℤh).1.ι = (ℤc).1.ι)
      (hep : IsProper D.site D.base D.base_mem e),
      chowClassCanonical.{u + 1} D ((ℤh).1.ι ≫ c ≫ p)
          (isGood_vanishingLocus D (c ≫ p) hYc _ _) k
          (gysinCycleMap D (c ≫ p) ℤh (isGood_vanishingLocus D (c ≫ p) hYc _ _) k
            (sectionGysinRule D (c ≫ p) hYc _ _ k
              (isInvertibleSheaf_pullbackSheaf D s₁ hY₁ (c ≫ p) hYc (ObjectProperty.homMk h) 𝕃s
                (isInvertibleSheaf_pullbackSheaf D p hp s₁ hY₁ (ObjectProperty.homMk g) L hL)))
            α) =
        chowClassCanonical.{u + 1} D ((ℤh).1.ι ≫ c ≫ p)
          (isGood_vanishingLocus D (c ≫ p) hYc _ _) k
          (properCyclePushforward D ((ℤc).1.ι ≫ c ≫ p) (isGood_vanishingLocus D (c ≫ p) hYc _ _)
            ((ℤh).1.ι ≫ c ≫ p) (isGood_vanishingLocus D (c ≫ p) hYc _ _)
            (by rw [← Category.assoc, he]) hep.2.1.2 k
            (gysinCycleMap D (c ≫ p) ℤc (isGood_vanishingLocus D (c ≫ p) hYc _ _) k
              (sectionGysinRule D (c ≫ p) hYc _ _ k
                (isInvertibleSheaf_pullbackSheaf D p hp (c ≫ p) hYc (ObjectProperty.homMk c) L hL))
              α)) := by
  subst hs₁ hc
  exact exists_chowClassCanonical_gysinCycleMap_pullbackSheaf_comp D p hp L σ hL g hY₁ h hYc k α

end CompositeEq

/-- `E = Z(σ) ⊆ X`. -/
local notation "𝔼" => vanishingLocus D p hp L σ

include hL in
/-- **The square of Stacks 0ER3 for `h ≫ g` against the one for `g`.**  For `ψ : Z(h^*g^*σ) ⟶
Z(g^*σ)` over `h` and `h' : E ×_X Y'' ⟶ E ×_X Y'` over `h`, the two routes
`Z(h^*g^*σ) ⟶ E ×_X Y'` agree: `pullback.snd` is a monomorphism. -/
private theorem comp_gysinTestVanishingLocusIso_hom_eq
    (h' : Limits.pullback 𝔼.1.ι (h ≫ g) ⟶ Limits.pullback 𝔼.1.ι g)
    (hsq : h' ≫ Limits.pullback.snd 𝔼.1.ι g = Limits.pullback.snd 𝔼.1.ι (h ≫ g) ≫ h)
    (ψ : 𝔼₁.1.toFunctor ⟶ (vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g).1.toFunctor)
    (hψ : ψ ≫ (vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g).1.ι = 𝔼₁.1.ι ≫ h) :
    ψ ≫ (gysinTestVanishingLocusIso D p hp L σ hL g hY').hom =
      𝕖 ≫ (gysinTestVanishingLocusIso D p hp L σ hL (h ≫ g) hY'').hom ≫ h' := by
  rw [← cancel_mono (Limits.pullback.snd 𝔼.1.ι g), Category.assoc ψ,
    gysinTestVanishingLocusIso_hom_snd, hψ, Category.assoc (eqToHom _),
    Category.assoc (gysinTestVanishingLocusIso D p hp L σ hL (h ≫ g) hY'').hom, hsq,
    ← Category.assoc (gysinTestVanishingLocusIso D p hp L σ hL (h ≫ g) hY'').hom,
    gysinTestVanishingLocusIso_hom_snd, ← Category.assoc (eqToHom _),
    eqToHom_comp_ι_of_eq D (vanishingLocus_pullbackGlobalSection_comp D p hp L σ hL g hY' h hY'')]

include hL in
/-- **Stacks 0ERJ (1) for the Gysin class of Stacks 0ERP: the cap operation commutes with proper
pushforward.**  For a test space `g : Y' ⟶ X`, a proper `h : Y'' ⟶ Y'` and the base change
`h' : E ×_X Y'' ⟶ E ×_X Y'`, the cap of the class of `α ∈ Z_k(Y'')` along `h ≫ g` is the class
of a cycle `β` with `c ∩ [h_* α] = [h'_* β]` on `Y'`: Stacks 0ER5 for the pulled-back triple
`(g^*ℒ, g^*σ)` along `h`
(`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_properCyclePushforward`), the
comparison of `h^*(g^*ℒ, g^*σ)` with `((h ≫ g)^*ℒ, (h ≫ g)^*σ)`
(`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_pullbackSheaf_comp`) and the square
`AlgebraicGeometry.Space.comp_gysinTestVanishingLocusIso_hom_eq`. -/
theorem gysinBivariantCap_proper_naturality
    (hX' : D.IsGood (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p))
    (hX'' : D.IsGood (Limits.pullback.fst 𝔼.1.ι (h ≫ g) ≫ 𝔼.1.ι ≫ p))
    (hh : IsProper D.site D.base D.base_mem h)
    (h' : Limits.pullback 𝔼.1.ι (h ≫ g) ⟶ Limits.pullback 𝔼.1.ι g)
    (sq : IsPullback (Limits.pullback.snd 𝔼.1.ι (h ≫ g)) h' h (Limits.pullback.snd 𝔼.1.ι g))
    (hfst : h' ≫ Limits.pullback.fst 𝔼.1.ι g = Limits.pullback.fst 𝔼.1.ι (h ≫ g))
    (hh' : IsProper D.site D.base D.base_mem h') (k : ℤ)
    (α : CycleGroup D ((h ≫ g) ≫ p) k) :
    ∃ β : CycleGroup D (Limits.pullback.fst 𝔼.1.ι (h ≫ g) ≫ 𝔼.1.ι ≫ p) (k - 1),
      gysinBivariantCap D p hp L σ hL (h ≫ g) hY'' hX'' k
          (chowClassCanonical.{u + 1} D ((h ≫ g) ≫ p) hY'' k α) =
        chowClassCanonical.{u + 1} D _ hX'' (k - 1) β ∧
      gysinBivariantCap D p hp L σ hL g hY' hX' k
          (chowClassCanonical.{u + 1} D (g ≫ p) hY' k
            (properCyclePushforward D ((h ≫ g) ≫ p) hY'' (g ≫ p) hY'
              (Category.assoc h g p).symm hh.2.1.2 k α)) =
        chowClassCanonical.{u + 1} D _ hX' (k - 1)
          (properCyclePushforward D (Limits.pullback.fst 𝔼.1.ι (h ≫ g) ≫ 𝔼.1.ι ≫ p) hX''
            (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX' (by rw [← Category.assoc, hfst])
            hh'.2.1.2 (k - 1) β) := by
  have hLg := isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L hL
  refine ⟨_, gysinBivariantCap_chowClassCanonical D p hp L σ hL (h ≫ g) hY'' hX'' k α, ?_⟩
  rw [gysinBivariantCap_chowClassCanonical, properCyclePushforward_degree_cast]
  obtain ⟨ψ, hψ⟩ := exists_isPullback_vanishingLocus_pullbackSheaf D (g ≫ p) hY' ((h ≫ g) ≫ p)
    hY'' (ObjectProperty.homMk h : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y', hY'.1⟩) 𝕃g 𝕤g hLg
  exact chowClassCanonical_properCyclePushforward_of_comp_eq D _ _ _ _ _
    (isGood_vanishingLocus D _ hY'' _ _) (isGood_vanishingLocus D _ hY' _ _)
    (isGood_vanishingLocus D _ hY'' _ _) hX'' hX'
    (vanishingLocusHom_comp_structure D (g ≫ p) hY' 𝕃g 𝕤g ((h ≫ g) ≫ p) hY''
      (ObjectProperty.homMk h) (Category.assoc h g p).symm ψ hψ.w) _
    (vanishingLocus_pullbackGlobalSection_comp_hom_structure D p hp L σ hL g hY' h hY'') _ _
    (isProper_vanishingLocusHom D (g ≫ p) hY' 𝕃g 𝕤g ((h ≫ g) ≫ p) hY''
      (ObjectProperty.homMk h) hh ψ hψ.w)
    (isProper_of_isIso D.site D.base D.base_mem _) (isProper_of_isIso D.site D.base D.base_mem _)
    (isProper_of_isIso D.site D.base D.base_mem _) hh'
    (comp_gysinTestVanishingLocusIso_hom_eq D p hp L σ hL g hY' h hY'' h' sq.w.symm ψ hψ.w)
    (k - 1) _ _ _
    (chowClassCanonical_gysinCycleMap_properCyclePushforward D (g ≫ p) hY' 𝕃g 𝕤g hLg
      ((h ≫ g) ≫ p) hY'' (ObjectProperty.homMk h) (Category.assoc h g p).symm hh (k - 1) ψ hψ.w
      _)
    (chowClassCanonical_gysinCycleMap_pullbackSheaf_comp D p hp L σ hL g hY' h hY'' (k - 1) _)

include hL in
/-- **Stacks 0ERJ (2) for the Gysin class of Stacks 0ERP: the cap operation commutes with flat
pullback.**  For a test space `g : Y' ⟶ X`, a flat `h : Y'' ⟶ Y'` of relative dimension `r` and
its base change `h' : E ×_X Y'' ⟶ E ×_X Y'`, the cap of the class of `α ∈ Z_k(Y')` along `g` is
the class of a cycle `β` with `c ∩ [h^* α] = [h'^* β]` on `Y''`: Stacks 0ER6 for the
pulled-back triple `(g^*ℒ, g^*σ)` along `h`
(`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback`), the
comparison of `h^*(g^*ℒ, g^*σ)` with `((h ≫ g)^*ℒ, (h ≫ g)^*σ)`
(`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_pullbackSheaf_comp`), the square
`AlgebraicGeometry.Space.comp_gysinTestVanishingLocusIso_hom_eq` and Stacks 0EPD. -/
theorem gysinBivariantCap_flat_naturality
    (hX' : D.IsGood (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p))
    (hX'' : D.IsGood (Limits.pullback.fst 𝔼.1.ι (h ≫ g) ≫ 𝔼.1.ι ≫ p))
    (hh : IsFlat D.site D.base D.base_mem h) (r : ℕ)
    (hr : HasRelativeDimension r D.site D.base D.base_mem h)
    (h' : Limits.pullback 𝔼.1.ι (h ≫ g) ⟶ Limits.pullback 𝔼.1.ι g)
    (sq : IsPullback (Limits.pullback.snd 𝔼.1.ι (h ≫ g)) h' h (Limits.pullback.snd 𝔼.1.ι g))
    (hfst : h' ≫ Limits.pullback.fst 𝔼.1.ι g = Limits.pullback.fst 𝔼.1.ι (h ≫ g))
    (hh' : IsFlat D.site D.base D.base_mem h')
    (hr' : HasRelativeDimension r D.site D.base D.base_mem h') (k : ℤ)
    (α : CycleGroup D (g ≫ p) k) :
    ∃ β : CycleGroup D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) (k - 1),
      gysinBivariantCap D p hp L σ hL g hY' hX' k
          (chowClassCanonical.{u + 1} D (g ≫ p) hY' k α) =
        chowClassCanonical.{u + 1} D _ hX' (k - 1) β ∧
      gysinBivariantCap D p hp L σ hL (h ≫ g) hY'' hX'' (k + (r : ℤ))
          (chowClassCanonical.{u + 1} D ((h ≫ g) ≫ p) hY'' (k + (r : ℤ))
            (flatPullbackMap D ((h ≫ g) ≫ p) hY'' (g ≫ p) hY' h (Category.assoc h g p).symm r hh
              hr k (k + (r : ℤ)) rfl α)) =
        chowClassCanonical.{u + 1} D _ hX'' (k + (r : ℤ) - 1)
          (flatPullbackMap D (Limits.pullback.fst 𝔼.1.ι (h ≫ g) ≫ 𝔼.1.ι ≫ p) hX''
            (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX' h' (by rw [← Category.assoc, hfst]) r
            hh' hr' (k - 1) (k + (r : ℤ) - 1) (by omega) β) := by
  have hLg := isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L hL
  refine ⟨_, gysinBivariantCap_chowClassCanonical D p hp L σ hL g hY' hX' k α, ?_⟩
  rw [gysinBivariantCap_chowClassCanonical,
    flatPullbackMap_degree_cast D _ hY'' _ hY' (Category.assoc h g p).symm r hh hr
      (sub_add_cancel k 1).symm (sub_add_cancel (k + (r : ℤ)) 1).symm rfl (by omega) α]
  obtain ⟨ψ, hψ⟩ := exists_isPullback_vanishingLocus_pullbackSheaf D (g ≫ p) hY' ((h ≫ g) ≫ p)
    hY'' (ObjectProperty.homMk h : (⟨Y'', hY''.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y', hY'.1⟩) 𝕃g 𝕤g hLg
  have hψfr := isFlat_and_hasRelativeDimension_gysinPullbackProjection D (g ≫ p) hY'
    ((h ≫ g) ≫ p) hY'' (Category.assoc h g p).symm r hh hr 𝕃g 𝕤g hψ
  exact chowClassCanonical_flatPullbackMap_of_comp_eq D _ _ _ _ _
    (isGood_vanishingLocus D _ hY'' _ _) (isGood_vanishingLocus D _ hY' _ _)
    (isGood_vanishingLocus D _ hY'' _ _) hX'' hX'
    (comp_structure_of_isPullback D (g ≫ p) ((h ≫ g) ≫ p) (Category.assoc h g p).symm hψ) _
    (vanishingLocus_pullbackGlobalSection_comp_hom_structure D p hp L σ hL g hY' h hY'') _ _ r
    hψfr.1 hψfr.2 hh' hr'
    (comp_gysinTestVanishingLocusIso_hom_eq D p hp L σ hL g hY' h hY'' h' sq.w.symm ψ hψ.w)
    (k - 1) (k + (r : ℤ) - 1) (by omega) _ _ _
    (chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback D (g ≫ p) hY' ((h ≫ g) ≫ p) hY''
      (Category.assoc h g p).symm r hh hr 𝕃g 𝕤g hLg hψ (k - 1) (k + (r : ℤ) - 1) (by omega)
      (by omega) _)
    (chowClassCanonical_gysinCycleMap_pullbackSheaf_comp D p hp L σ hL g hY' h hY''
      (k + (r : ℤ) - 1) _)

end Composite

end AlgebraicGeometry.Space

end

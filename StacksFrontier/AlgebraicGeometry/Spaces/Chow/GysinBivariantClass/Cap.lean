module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupCanonicalIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
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
# The cap operation of the Gysin bivariant class (Stacks 0ERP)

A part of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass`: the vanishing locus
`Z(f^*s) = f^{-1}(Z(s))` of a pulled-back section (Stacks 0ER3), the projection formula for the
restricted-section rules (Stacks 0ER5, after `i_*`), and the cap operation
`AlgebraicGeometry.Space.gysinBivariantCap` of the class of Stacks 0ERP on a test space.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] pointTopology

/-! ### The vanishing locus of a pulled-back section -/

section Vanishing

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (σ : L.sections) (hL : IsInvertibleSheaf D p hp L)
    (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (q : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)

include hL in
/-- **Stacks 0ER3: `Z(f^*s) = f^{-1}(Z(s))`.**  The vanishing locus of the pulled-back section
of Stacks 0ER3 is, as a subfunctor, the inverse image of the vanishing locus of `s`: the
underlying subfunctors of `AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`. -/
theorem vanishingLocus_pullbackGlobalSection :
    (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' q L)
        (pullbackGlobalSection D p hp p' hp' q L σ)).1 =
      (vanishingLocus D p hp L σ).1.preimage q.hom :=
  (congrArg Subtype.val (pullbackDivisor_eq_vanishingLocus D p hp p' hp' q L σ hL)).symm

end Vanishing

/-! ### Changing clause (1)(b) of the Gysin rule by principal divisors -/

section RuleChange

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (σ : L.sections) (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

end RuleChange

/-! ### Stacks 0EQS on a component, for any regular section of `ℒ|_W` -/

section PulledDivisor

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    (q : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (g : W.subspace.toFunctor ⟶ (chernImage D hX hY q W).subspace.toFunctor)
    (hg : g ≫ (chernImage D hX hY q W).subspace.ι = W.subspace.ι ≫ q.hom) (k : ℤ)
    (hqB : q.hom ≫ sY = sX) (hq : IsProper D.site D.base D.base_mem q.hom)
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem
      (chernImage D hX hY q W).subspace.toFunctor (chernImage D hX hY q W).isClosedSubspace.1
      (chernImageModule D hX hY q L W))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem
      (chernImage D hX hY q W).subspace.toFunctor (chernImage D hX hY q W).isClosedSubspace.1
      (chernImageModule D hX hY q L W) τ)

end PulledDivisor

/-! ### The projection formula for the restricted-section rules (Stacks 0ER5, after `i_*`) -/

section Projection

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (σ : L.sections) (hL : IsInvertibleSheaf D p hp L)
    (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (q : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hqB : q.hom ≫ p = p') (hq : IsProper D.site D.base D.base_mem q.hom) (k : ℤ)

include hqB in
theorem vanishingLocusHom_comp_structure
    (g : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.toFunctor ⟶ (vanishingLocus D p hp L
        σ).1.toFunctor) (hg : g ≫ (vanishingLocus D p hp L σ).1.ι = (vanishingLocus D p' hp'
          (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.ι ≫ q.hom) :
    g ≫ (vanishingLocus D p hp L σ).1.ι ≫ p = (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp'
      q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.ι ≫ p' := by
  rw [← Category.assoc, hg, Category.assoc, hqB]

include hq in
/-- The morphism `g : E' ⟶ E` of the square of Stacks 0ER3 over a proper `f` is proper. -/
theorem isProper_vanishingLocusHom
    (g : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.toFunctor ⟶ (vanishingLocus D p hp L
        σ).1.toFunctor) (hg : g ≫ (vanishingLocus D p hp L σ).1.ι = (vanishingLocus D p' hp'
          (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.ι ≫ q.hom) :
    IsProper D.site D.base D.base_mem g := by
  have hE := isGood_vanishingLocus D p hp L σ
  have hE' := isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' q L)
    (pullbackGlobalSection D p hp p' hp' q L σ)
  refine isProper_of_comp_of_isSeparated D.site D.base D.base_mem hE'.1 hE.1 hp.1 g (vanishingLocus
    D p hp L σ).1.ι ?_
    (isSeparated_of_isClosedImmersion D.site D.base D.base_mem _ (vanishingLocus D p hp L σ).2.2)
  rw [hg]
  exact isProper_comp D.site D.base D.base_mem hE'.1 hp'.1 hp.1 _ _
    (isProper_of_isClosedImmersion D.site D.base D.base_mem hE'.1 hp'.1 _ (vanishingLocus D p' hp'
      (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).2.2) hq

include hL hqB hq in
/-- **Stacks 0ER5 over the constructed Chow groups, at any map `g : E' ⟶ E` over `f`.**  In
Situation 0EDT let `f : X' ⟶ X` be proper between good spaces, `(ℒ, σ, i : E → X)` a triple as in
Stacks 0ER1 and `(f^*ℒ, f^*σ, i' : E' → X')` its pullback (Stacks 0ER3).  For every `g : E' ⟶ E`
with `g ≫ i = i' ≫ f` and every `α' ∈ Z_{k+1}(X')`, `i^* f_* α' = g_* (i')^* α'` in `CH_k(E)`.
The inclusion `i` is a monomorphism, so `g` is the projection
`AlgebraicGeometry.Space.pullbackVanishingLocusProjection`, and this is Stacks 0ER5,
`AlgebraicGeometry.Space.chowClassCanonical_sectionGysin_properPushforward_eq`. -/
theorem chowClassCanonical_gysinCycleMap_properCyclePushforward
    (g : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.toFunctor ⟶ (vanishingLocus D p hp L
        σ).1.toFunctor) (hg : g ≫ (vanishingLocus D p hp L σ).1.ι = (vanishingLocus D p' hp'
          (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.ι ≫ q.hom)
    (α' : CycleGroup D p' (k + 1)) :
    chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p) (isGood_vanishingLocus D p
      hp L σ) k
        (gysinCycleMap D p (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
          (sectionGysinRule D p hp L σ k hL)
          (properCyclePushforward D p' hp' p hp hqB hq.2.1.2 (k + 1) α')) =
      chowClassCanonical.{u + 1} D ((vanishingLocus D p hp L σ).1.ι ≫ p) (isGood_vanishingLocus D p
        hp L σ) k
        (properCyclePushforward D ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)).1.ι ≫ p') (isGood_vanishingLocus D p' hp' _ _)
        ((vanishingLocus D p hp L σ).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L σ)
          (vanishingLocusHom_comp_structure D p hp L σ p' hp' q hqB g hg)
          (isProper_vanishingLocusHom D p hp L σ p' hp' q hq g hg).2.1.2 k
          (gysinCycleMap D p' (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' q L)
      (pullbackGlobalSection D p hp p' hp' q L σ)) (isGood_vanishingLocus D p' hp' _ _) k
            (sectionGysinRule D p' hp' _ (pullbackGlobalSection D p hp p' hp' q L σ) k
              (isInvertibleSheaf_pullbackSheaf D p hp p' hp' q L hL)) α')) := by
  have he : g = pullbackVanishingLocusProjection D p hp p' hp' q L σ hL :=
    (cancel_mono (vanishingLocus D p hp L σ).1.ι).1
      (hg.trans (pullbackVanishingLocusProjection_comm D p hp p' hp' q L σ hL).symm)
  subst he
  exact chowClassCanonical_sectionGysin_properPushforward_eq D p hp p' hp' q hqB hq L σ hL k α'

end Projection

/-! ### The cap operation of the Gysin bivariant class (Stacks 0ERP) -/

section Cap

variable (D : BaseSpaceDimensionSituation.{u})

/-- An equality of subfunctors identifies their inclusions. -/
theorem eqToHom_comp_ι_of_eq {F : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {A B : Subfunctor F} (h : A = B) :
    eqToHom (congrArg Subfunctor.toFunctor h) ≫ B.ι = A.ι := by
  subst h
  exact Category.id_comp _

/-- The class of a cycle transported along an equality of degrees. -/
private theorem chowGroupCanonicalDegreeCongr_chowClassCanonical {Y : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {k l : ℤ} (h : k = l) (α : CycleGroup D sY k) :
    chowGroupCanonicalDegreeCongr D sY hY h (chowClassCanonical.{u + 1} D sY hY k α) =
      chowClassCanonical.{u + 1} D sY hY l (h ▸ α) := by
  subst h
  rfl

variable {X X' : D.Ambient} (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (g : X' ⟶ X) (hX' : D.IsGood (g ≫ p))

/-- The vanishing locus `Z(g^*σ) ⊆ X'` of the pulled-back triple on a test space `g : X' ⟶ X`. -/
local notation "ℤg" => vanishingLocus D (g ≫ p) hX'
  (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
  (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)

/-- **Stacks 0ER3: `Z(g^*σ) = X' ×_X E`.**  The identification of the vanishing locus of the
pulled-back section with the fibre product, through `Z(g^*σ) = g^{-1}(E)`
(`AlgebraicGeometry.Space.vanishingLocus_pullbackGlobalSection`) and the cartesian square of an
inverse image (`CategoryTheory.Subfunctor.isPullback_preimage`). -/
noncomputable def gysinTestVanishingLocusIso :
    (ℤg).1.toFunctor ≅
      Limits.pullback (vanishingLocus D p hp L σ).1.ι g :=
  eqToIso (congrArg Subfunctor.toFunctor (vanishingLocus_pullbackGlobalSection D p hp L σ hL
      (g ≫ p) hX' (ObjectProperty.homMk g))) ≪≫
    (Subfunctor.isPullback_preimage g (vanishingLocus D p hp L σ).1).isoPullback

theorem gysinTestVanishingLocusIso_hom_snd :
    (gysinTestVanishingLocusIso D p hp L σ hL g hX').hom ≫
        Limits.pullback.snd (vanishingLocus D p hp L σ).1.ι g =
      (ℤg).1.ι := by
  rw [gysinTestVanishingLocusIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd,
    eqToIso.hom]
  exact eqToHom_comp_ι_of_eq D (vanishingLocus_pullbackGlobalSection D p hp L σ hL (g ≫ p) hX'
    (ObjectProperty.homMk g))

theorem gysinTestVanishingLocusIso_hom_comp_structure :
    (gysinTestVanishingLocusIso D p hp L σ hL g hX').hom ≫
        Limits.pullback.fst (vanishingLocus D p hp L σ).1.ι g ≫
          (vanishingLocus D p hp L σ).1.ι ≫ p =
      (ℤg).1.ι ≫ g ≫ p := by
  rw [← Category.assoc (Limits.pullback.fst _ _), Limits.pullback.condition, Category.assoc,
    ← Category.assoc, gysinTestVanishingLocusIso_hom_snd]

/-- **The cap operation of Stacks 0ERP on a test space.**  For `g : X' ⟶ X` good over the base,
`(i')^* : CH_k(X') ⟶ CH_{k-1}(E')`, `E' = E ×_X X'`: the Gysin homomorphism of Stacks 0ERA of
the pulled-back triple `(g^*ℒ, g^*σ, Z(g^*σ) → X')` of Stacks 0ER3
(`AlgebraicGeometry.Space.sectionGysinChowGroupMap`), carried from `Z(g^*σ)` to the fibre product
along `AlgebraicGeometry.Space.gysinTestVanishingLocusIso` (an isomorphism is proper, so this is a
proper pushforward of Stacks 0EQC), after the transport `k = (k - 1) + 1` of degrees. -/
noncomputable def gysinBivariantCap
    (hE' : D.IsGood (Limits.pullback.fst (vanishingLocus D p hp L σ).1.ι g ≫
      (vanishingLocus D p hp L σ).1.ι ≫ p)) (k : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ p) hX' k →+
      chowGroupCanonical.{u + 1} D (Limits.pullback.fst (vanishingLocus D p hp L σ).1.ι g ≫
        (vanishingLocus D p hp L σ).1.ι ≫ p) hE' (k - 1) :=
  (chowGroupCanonicalProperPushforward.{u + 1} D _
      (isGood_vanishingLocus D (g ≫ p) hX' _ _) _ hE'
      (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL g hX')
      (isProper_of_isIso D.site D.base D.base_mem _) (k - 1)).comp
    ((sectionGysinChowGroupMap D (g ≫ p) hX'
        (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
        (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)
        (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L hL)
        (k - 1)).comp
      (chowGroupCanonicalDegreeCongr D (g ≫ p) hX' (sub_add_cancel k 1).symm).toAddMonoidHom)

/-- **The cap operation of Stacks 0ERP on the class of a cycle**: the class of the proper
pushforward along `Z(g^*σ) ≅ E ×_X X'` of the Gysin cycle of Stacks 0ER1 of the pulled-back
triple, at its own rule `AlgebraicGeometry.Space.sectionGysinRule`. -/
theorem gysinBivariantCap_chowClassCanonical
    (hE' : D.IsGood (Limits.pullback.fst (vanishingLocus D p hp L σ).1.ι g ≫
      (vanishingLocus D p hp L σ).1.ι ≫ p)) (k : ℤ) (α : CycleGroup D (g ≫ p) k) :
    gysinBivariantCap D p hp L σ hL g hX' hE' k (chowClassCanonical.{u + 1} D (g ≫ p) hX' k α) =
      chowClassCanonical.{u + 1} D _ hE' (k - 1)
        (properCyclePushforward D _ (isGood_vanishingLocus D (g ≫ p) hX' _ _) _ hE'
          (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL g hX')
          (isProper_of_isIso D.site D.base D.base_mem _).2.1.2 (k - 1)
          (gysinCycleMap D (g ≫ p) (ℤg)
            (isGood_vanishingLocus D (g ≫ p) hX' _ _) (k - 1)
            (sectionGysinRule D (g ≫ p) hX' _
              (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ) (k - 1)
              (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L
                hL))
            ((sub_add_cancel k 1).symm ▸ α))) := by
  simp only [gysinBivariantCap, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    chowGroupCanonicalDegreeCongr_chowClassCanonical]
  rfl

end Cap

end AlgebraicGeometry.Space

end

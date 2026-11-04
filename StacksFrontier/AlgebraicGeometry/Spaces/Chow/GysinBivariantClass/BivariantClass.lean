module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupCanonicalIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.Cap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.Composite
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass.GysinComm
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
# Stacks 0ERP: the Gysin map of a triple is a bivariant class of degree 1

A part of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass`: axiom (3) of Stacks 0ERJ
for the cap operation `AlgebraicGeometry.Space.gysinBivariantCap` (from Stacks 0ERC on the test
space and Stacks 0ER5 into the vanishing locus), and the bivariant class
`AlgebraicGeometry.Space.exists_bivariantClassCanonical_gysin` of Stacks 0ERP.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] pointTopology

section ClosedImmersion

variable (D : BaseSpaceDimensionSituation.{u})

/-- The transport of cycles along an equality of degrees is the cast. -/
private theorem cycleGroupDegreeCongr_eq_cast {Y : D.Ambient} (sY : Y ⟶ D.space) {a b : ℤ}
    (h : a = b) (x : CycleGroup D sY a) : cycleGroupDegreeCongr D sY h x = h ▸ x := by
  subst h
  rfl

end ClosedImmersion

section GysinAssembly

variable (D : BaseSpaceDimensionSituation.{u})

/-- Whiskering a triple composite on the right. -/
private theorem comp_comp_comp_eq_of_comp_comp_eq {𝒞 : Type*} [Category 𝒞] {A B C E F G : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ F} {d : A ⟶ E} {d' : E ⟶ F} (h : a ≫ b ≫ c = d ≫ d')
    (s : F ⟶ G) : a ≫ b ≫ c ≫ s = d ≫ d' ≫ s := by
  rw [← Category.assoc b, ← Category.assoc a, h, Category.assoc]

end GysinAssembly

section GysinBivariantSquare

variable (D : BaseSpaceDimensionSituation.{u}) {X Y Y' Z : D.Ambient} (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (f : X ⟶ Y) (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (Limits.pullback.fst f g ≫ sX))
    (M : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (t : M.sections)
    (hM : IsInvertibleSheaf D (g ≫ sY) hY' M) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ)
    (q : Z ⟶ Limits.pullback f g)

/-- `𝒩' = (X' ⟶ Y')^*ℳ` on `X' = pullback f g`, spelled out. -/
local notation "𝕄u" => pullbackSheaf D (g ≫ sY) hY' (Limits.pullback.fst f g ≫ sX) hX'
  (ObjectProperty.homMk (Limits.pullback.snd f g)) M
/-- `t'`, spelled out. -/
local notation "𝕥u" => pullbackGlobalSection D (g ≫ sY) hY' (Limits.pullback.fst f g ≫ sX) hX'
  (ObjectProperty.homMk (Limits.pullback.snd f g)) M t
/-- `Z(q^*t') ⊆ Z`. -/
local notation "ℤq" => vanishingLocus D sZ hZ
  (pullbackSheaf D (Limits.pullback.fst f g ≫ sX) hX' sZ hZ (ObjectProperty.homMk q)
    (pullbackSheaf D (g ≫ sY) hY' (Limits.pullback.fst f g ≫ sX) hX'
      (ObjectProperty.homMk (Limits.pullback.snd f g)) M))
  (pullbackGlobalSection D (Limits.pullback.fst f g ≫ sX) hX' sZ hZ (ObjectProperty.homMk q)
    (pullbackSheaf D (g ≫ sY) hY' (Limits.pullback.fst f g ≫ sX) hX'
      (ObjectProperty.homMk (Limits.pullback.snd f g)) M)
    (pullbackGlobalSection D (g ≫ sY) hY' (Limits.pullback.fst f g ≫ sX) hX'
      (ObjectProperty.homMk (Limits.pullback.snd f g)) M t))
/-- `Z(t') ⊆ X'`, as Stacks 0ERJ (3) spells it. -/
local notation "𝕋u" => bivariantPullbackVanishingLocus D sX sY f g hY' hX' M t

include hM in
/-- **Stacks 0ER5 into the vanishing locus `Z(t')` of Stacks 0ERJ (3).**  For the base change
`X' = X ×_Y Y'` of `f` along a test space `g`, a pair `(ℳ, t)` on `Y'` with inverse image
`(𝒩', t')` on `X'`, and a proper `q : Z ⟶ X'` over the base, the square of Stacks 0ER3 for
`q^*(𝒩', t')` gives a proper `ψ : Z(q^*t') ⟶ Z(t')` over `q` with `(t')^* q_* α = ψ_* (q^*t')^* α`
in `CH_k(Z(t'))` for every `α ∈ Z_{k+1}(Z)`
(`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_properCyclePushforward`).  The vanishing
locus, the sheaf and the section on `X'` are spelled as Stacks 0ERJ (3) spells them
(`AlgebraicGeometry.Space.bivariantPullbackVanishingLocus`). -/
private theorem exists_chowClassCanonical_gysinCycleMap_properCyclePushforward_bivariant
    (hqB : q ≫ Limits.pullback.fst f g ≫ sX = sZ) (hq : IsProper D.site D.base D.base_mem q)
    (k : ℤ) (α : CycleGroup D sZ (k + 1)) :
    ∃ (ψ : (ℤq).1.toFunctor ⟶ (𝕋u).1.toFunctor) (_hψ : ψ ≫ (𝕋u).1.ι = (ℤq).1.ι ≫ q)
      (hψB : ψ ≫ (𝕋u).1.ι ≫ Limits.pullback.fst f g ≫ sX = (ℤq).1.ι ≫ sZ)
      (hψp : IsProper D.site D.base D.base_mem ψ),
      chowClassCanonical.{u + 1} D ((𝕋u).1.ι ≫ Limits.pullback.fst f g ≫ sX)
          (isGood_vanishingLocus D (Limits.pullback.fst f g ≫ sX) hX'
            (bivariantPullbackSheaf D sX sY f g hY' hX' M)
            (bivariantPullbackSection D sX sY f g hY' hX' M t)) k
          (gysinCycleMap D (Limits.pullback.fst f g ≫ sX) 𝕋u
            (isGood_vanishingLocus D (Limits.pullback.fst f g ≫ sX) hX'
              (bivariantPullbackSheaf D sX sY f g hY' hX' M)
              (bivariantPullbackSection D sX sY f g hY' hX' M t)) k
            (sectionGysinRule D (Limits.pullback.fst f g ≫ sX) hX'
              (bivariantPullbackSheaf D sX sY f g hY' hX' M)
              (bivariantPullbackSection D sX sY f g hY' hX' M t) k
              (isInvertibleSheaf_bivariantPullbackSheaf D sX sY f g hY' hX' M hM))
            (properCyclePushforward D sZ hZ (Limits.pullback.fst f g ≫ sX) hX' hqB hq.2.1.2
              (k + 1) α)) =
        chowClassCanonical.{u + 1} D ((𝕋u).1.ι ≫ Limits.pullback.fst f g ≫ sX)
          (isGood_vanishingLocus D (Limits.pullback.fst f g ≫ sX) hX'
            (bivariantPullbackSheaf D sX sY f g hY' hX' M)
            (bivariantPullbackSection D sX sY f g hY' hX' M t)) k
          (properCyclePushforward D ((ℤq).1.ι ≫ sZ) (isGood_vanishingLocus D sZ hZ _ _)
            ((𝕋u).1.ι ≫ Limits.pullback.fst f g ≫ sX)
            (isGood_vanishingLocus D (Limits.pullback.fst f g ≫ sX) hX'
              (bivariantPullbackSheaf D sX sY f g hY' hX' M)
              (bivariantPullbackSection D sX sY f g hY' hX' M t)) hψB hψp.2.1.2 k
            (gysinCycleMap D sZ ℤq (isGood_vanishingLocus D sZ hZ _ _) k
              (sectionGysinRule D sZ hZ _ _ k
                (isInvertibleSheaf_pullbackSheaf D (Limits.pullback.fst f g ≫ sX) hX' sZ hZ
                  (ObjectProperty.homMk q) 𝕄u
                  (isInvertibleSheaf_pullbackSheaf D (g ≫ sY) hY' (Limits.pullback.fst f g ≫ sX)
                    hX' (ObjectProperty.homMk (Limits.pullback.snd f g)) M hM))) α)) := by
  have hM' := isInvertibleSheaf_pullbackSheaf D (g ≫ sY) hY' (Limits.pullback.fst f g ≫ sX) hX'
    (ObjectProperty.homMk (Limits.pullback.snd f g)) M hM
  obtain ⟨ψ, hψ⟩ := exists_isPullback_vanishingLocus_pullbackSheaf D
    (Limits.pullback.fst f g ≫ sX) hX' sZ hZ (ObjectProperty.homMk q) 𝕄u 𝕥u hM'
  exact ⟨ψ, hψ.w, vanishingLocusHom_comp_structure D (Limits.pullback.fst f g ≫ sX) hX' 𝕄u 𝕥u sZ
      hZ (ObjectProperty.homMk q) hqB ψ hψ.w,
    isProper_vanishingLocusHom D (Limits.pullback.fst f g ≫ sX) hX' 𝕄u 𝕥u sZ hZ
      (ObjectProperty.homMk q) hq ψ hψ.w,
    chowClassCanonical_gysinCycleMap_properCyclePushforward D (Limits.pullback.fst f g ≫ sX) hX'
      𝕄u 𝕥u hM' sZ hZ (ObjectProperty.homMk q) hqB hq k ψ hψ.w α⟩

end GysinBivariantSquare

section GysinNaturality

variable (D : BaseSpaceDimensionSituation.{u}) {X Y' : D.Ambient} (p : X ⟶ D.space)
    (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ p))
    (hX' : D.IsGood (Limits.pullback.fst (vanishingLocus D p hp L σ).1.ι g ≫
      (vanishingLocus D p hp L σ).1.ι ≫ p))
    (M : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (t : M.sections)
    (hM : IsInvertibleSheaf D (g ≫ p) hY' M)

/-- `E = Z(σ) ⊆ X`. -/
local notation "𝔼" => vanishingLocus D p hp L σ
/-- `D' = Z(t) ⊆ Y'`. -/
local notation "𝔽" => vanishingLocus D (g ≫ p) hY' M t
/-- `Z(t') ⊆ E ×_X Y'`, `t'` the inverse image of `t`. -/
local notation "𝕋" => bivariantPullbackVanishingLocus D
  (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p) p
  (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ))) g hY' hX' M t
/-- `g^*ℒ` on `Y'`. -/
local notation "𝕃g" => pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L
/-- `g^*σ`. -/
local notation "𝕤g" => pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ
/-- `Z(g^*σ) ⊆ Y'`. -/
local notation "ℤμ" => vanishingLocus D (g ≫ p) hY'
  (pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L)
  (pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ)
/-- `Z((ι ≫ g)^*σ) ⊆ D'`, `ι : D' ⟶ Y'`. -/
local notation "ℤσF" => vanishingLocus D
  ((Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g) ≫ p)
  (isGood_vanishingLocus D (g ≫ p) hY' M t)
  (pullbackSheaf D p hp ((Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g) ≫ p)
    (isGood_vanishingLocus D (g ≫ p) hY' M t)
    (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g)) L)
  (pullbackGlobalSection D p hp
    ((Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g) ≫ p)
    (isGood_vanishingLocus D (g ≫ p) hY' M t)
    (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g))
    L σ)
/-- `𝒩' = (E ×_X Y' ⟶ Y')^*ℳ`, spelled out. -/
local notation "𝕄'" => pullbackSheaf D (g ≫ p) hY'
  (Limits.pullback.fst (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ))) g ≫
    Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p) hX'
  (ObjectProperty.homMk (Limits.pullback.snd (Subfunctor.ι (Subtype.val
    (vanishingLocus D p hp L σ))) g)) M
/-- `t'`, spelled out. -/
local notation "𝕥'" => pullbackGlobalSection D (g ≫ p) hY'
  (Limits.pullback.fst (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ))) g ≫
    Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p) hX'
  (ObjectProperty.homMk (Limits.pullback.snd (Subfunctor.ι (Subtype.val
    (vanishingLocus D p hp L σ))) g)) M t

/-- `Z(σ_g|_{D'}) ⊆ D'`, over the structure morphism `ι ≫ g ≫ p` of `D'` (as Stacks 0ERC on `Y'`
spells it). -/
local notation "ℤ₁F" => vanishingLocus D
  (Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g ≫ p)
  (isGood_vanishingLocus D (g ≫ p) hY' M t)
  (pullbackSheaf D (g ≫ p) hY'
    (Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g ≫ p)
    (isGood_vanishingLocus D (g ≫ p) hY' M t)
    (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)))) 𝕃g)
  (pullbackGlobalSection D (g ≫ p) hY'
    (Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)) ≫ g ≫ p)
    (isGood_vanishingLocus D (g ≫ p) hY' M t)
    (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D (g ≫ p) hY' M t)))) 𝕃g 𝕤g)

include hL in
/-- **The pair `σ` restricted to `D' = Z(t)` in two steps and in one, carried into a target over
`Y'`.**  For a cycle `x` on `D'`, the class of the Gysin cycle of `(ι ≫ g)^*σ` pushed along `j`
equals that of `ι^*(g^*σ)` pushed along `j'`, whenever `j` and `j'` agree with the inclusions
after a monomorphism `m₀ : T ⟶ Y'`: `chowClassCanonical_gysinCycleMap_pullbackSheaf_comp` and the
two spellings of the structure morphism of `D'`
(`exists_properCyclePushforward_gysinCycleMap_structure_eq`). -/
private theorem chowClassCanonical_properCyclePushforward_gysin_pullbackSheaf_comp_of_mono
    {T : D.Ambient} (sT : T ⟶ D.space) (hT : D.IsGood sT) (m₀ : T ⟶ Y') [Mono m₀]
    (j : (ℤσF).1.toFunctor ⟶ T) (hjB : j ≫ sT = (ℤσF).1.ι ≫ ((𝔽).1.ι ≫ g) ≫ p)
    (hj : IsProper D.site D.base D.base_mem j) (hjm : j ≫ m₀ = (ℤσF).1.ι ≫ (𝔽).1.ι)
    (j' : (ℤ₁F).1.toFunctor ⟶ T) (hj'B : j' ≫ sT = (ℤ₁F).1.ι ≫ (𝔽).1.ι ≫ g ≫ p)
    (hj' : IsProper D.site D.base D.base_mem j') (hj'm : j' ≫ m₀ = (ℤ₁F).1.ι ≫ (𝔽).1.ι) (m : ℤ)
    (x : CycleGroup D ((𝔽).1.ι ≫ g ≫ p) (m + 1)) :
    chowClassCanonical.{u + 1} D sT hT m
        (properCyclePushforward D ((ℤσF).1.ι ≫ ((𝔽).1.ι ≫ g) ≫ p)
          (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) sT hT hjB
          hj.2.1.2 m
          (gysinCycleMap D (((𝔽).1.ι ≫ g) ≫ p) ℤσF
            (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) m
            (sectionGysinRule D (((𝔽).1.ι ≫ g) ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' M t) _
              (pullbackGlobalSection D p hp (((𝔽).1.ι ≫ g) ≫ p)
                (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk ((𝔽).1.ι ≫ g))
                L σ) m
              (isInvertibleSheaf_pullbackSheaf D p hp (((𝔽).1.ι ≫ g) ≫ p)
                (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk ((𝔽).1.ι ≫ g))
                L hL)) x)) =
      chowClassCanonical.{u + 1} D sT hT m
        (properCyclePushforward D ((ℤ₁F).1.ι ≫ (𝔽).1.ι ≫ g ≫ p)
          (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) sT hT hj'B
          hj'.2.1.2 m
          (gysinCycleMap D ((𝔽).1.ι ≫ g ≫ p) ℤ₁F
            (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) m
            (sectionGysinRule D ((𝔽).1.ι ≫ g ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _ m
              (isInvertibleSheaf_pullbackSheaf D (g ≫ p) hY' ((𝔽).1.ι ≫ g ≫ p)
                (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk (𝔽).1.ι) 𝕃g
                (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L
                  hL))) x)) := by
  have hFg := isGood_vanishingLocus D (g ≫ p) hY' M t
  have hLg := isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L hL
  have hT1 := chowClassCanonical_gysinCycleMap_pullbackSheaf_comp D p hp L σ hL g hY' (𝔽).1.ι hFg
    m x
  have hεB := vanishingLocus_pullbackGlobalSection_comp_hom_structure D p hp L σ hL g hY'
    (𝔽).1.ι hFg
  have hει := eqToHom_comp_ι_of_eq D
    (vanishingLocus_pullbackGlobalSection_comp D p hp L σ hL g hY' (𝔽).1.ι hFg)
  have H1 := exists_properCyclePushforward_gysinCycleMap_structure_eq D (g ≫ p)
    hY' 𝕃g 𝕤g hLg (𝔽).1.ι (((𝔽).1.ι ≫ g) ≫ p) ((𝔽).1.ι ≫ g ≫ p) hFg hFg
    (Category.assoc (𝔽).1.ι g p) m x x HEq.rfl
  refine H1.elim fun δ H1 => H1.elim fun hδ H1 => H1.elim fun hδp hδx => ?_
  have hδB := ((Category.assoc δ _ _).symm.trans (eq_whisker hδ ((𝔽).1.ι ≫ g ≫ p))).trans
    (whisker_eq _ (Category.assoc (𝔽).1.ι g p)).symm
  exact chowClassCanonical_properCyclePushforward_of_comp_eq_comp_of_mono D _ _ _ _ _ _ _ _ m₀
    hεB hjB hδB hj'B (isProper_of_isIso D.site D.base D.base_mem _) hj hδp hj' hjm hει hδ hj'm
    m _ _ _ hT1 hδx

section Comm

variable (i₀ : (vanishingLocus D (g ≫ p) hY'
    (pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L)
    (pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ)).1.toFunctor ⟶
  Limits.pullback (vanishingLocus D p hp L σ).1.ι g)

/-- `Z(i₀^*t') ⊆ Z(g^*σ)`, for `i₀ : Z(g^*σ) ⟶ E ×_X Y'`. -/
local notation "ℤq" => vanishingLocus D (Subfunctor.ι (Subtype.val ℤμ) ≫ g ≫ p)
  (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g)
  (pullbackSheaf D (Limits.pullback.fst (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ))) g ≫
      Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p) hX'
    (Subfunctor.ι (Subtype.val ℤμ) ≫ g ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g)
    (ObjectProperty.homMk i₀) 𝕄')
  (pullbackGlobalSection D
    (Limits.pullback.fst (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ))) g ≫
      Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p) hX'
    (Subfunctor.ι (Subtype.val ℤμ) ≫ g ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g)
    (ObjectProperty.homMk i₀) 𝕄' 𝕥')

include hL hM in
/-- **Stacks 0ERC on `Y'`, carried into a target over `Y'`.**  For `α ∈ Z_{m+2}(Y')` and
`ψ : Z(i₀^*t') ⟶ T` agreeing with the inclusion after a monomorphism `m₀ : T ⟶ Y'`, there is a
proper `j' : Z(σ_g|_{D'}) ⟶ T` agreeing with the inclusion after `m₀`, such that the class of
`σ_g` applied after `t`, pushed along `j'`, equals the class of `i₀^*t'` applied after `σ_g`,
pushed along `ψ`.  This is Stacks 0ERC
(`chowClassCanonical_properCyclePushforward_gysin_gysin_eq`) for the pairs `(ℳ, t)` and
`(g^*ℒ, g^*σ)` and the comparison of the iterated with the direct inverse image of `t`
(`exists_chowClassCanonical_gysinCycleMap_pullbackSheaf_comp_of_eq`). -/
private theorem exists_chowClassCanonical_properCyclePushforward_gysin_comm_of_mono
    (hi₀snd : i₀ ≫ Limits.pullback.snd 𝔼.1.ι g = (ℤμ).1.ι) {T : D.Ambient}
    (sT : T ⟶ D.space) (hT : D.IsGood sT) (m₀ : T ⟶ Y') (ψ : (ℤq).1.toFunctor ⟶ T)
    (hψB : ψ ≫ sT = (ℤq).1.ι ≫ (ℤμ).1.ι ≫ g ≫ p) (hψp : IsProper D.site D.base D.base_mem ψ)
    (hψm : ψ ≫ m₀ = (ℤq).1.ι ≫ (ℤμ).1.ι) (m : ℤ) (α : CycleGroup D (g ≫ p) (m + 1 + 1)) :
    ∃ (j' : (ℤ₁F).1.toFunctor ⟶ T) (hj'B : j' ≫ sT = (ℤ₁F).1.ι ≫ (𝔽).1.ι ≫ g ≫ p)
      (hj' : IsProper D.site D.base D.base_mem j') (_ : j' ≫ m₀ = (ℤ₁F).1.ι ≫ (𝔽).1.ι),
      chowClassCanonical.{u + 1} D sT hT m
          (properCyclePushforward D ((ℤ₁F).1.ι ≫ (𝔽).1.ι ≫ g ≫ p)
            (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) sT hT hj'B
            hj'.2.1.2 m
            (gysinCycleMap D ((𝔽).1.ι ≫ g ≫ p) ℤ₁F
              (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) m
              (sectionGysinRule D ((𝔽).1.ι ≫ g ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' M t) _
                _ m
                (isInvertibleSheaf_pullbackSheaf D (g ≫ p) hY' ((𝔽).1.ι ≫ g ≫ p)
                  (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk (𝔽).1.ι) 𝕃g
                  (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g)
                    L hL)))
              (gysinCycleMap D (g ≫ p) 𝔽 (isGood_vanishingLocus D (g ≫ p) hY' M t) (m + 1)
                (sectionGysinRule D (g ≫ p) hY' M t (m + 1) hM) α))) =
        chowClassCanonical.{u + 1} D sT hT m
          (properCyclePushforward D ((ℤq).1.ι ≫ (ℤμ).1.ι ≫ g ≫ p)
            (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g) _ _) sT hT
            hψB hψp.2.1.2 m
            (gysinCycleMap D ((ℤμ).1.ι ≫ g ≫ p) ℤq
              (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g) _ _) m
              (sectionGysinRule D ((ℤμ).1.ι ≫ g ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g)
                _ _ m
                (isInvertibleSheaf_pullbackSheaf D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX'
                  ((ℤμ).1.ι ≫ g ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g)
                  (ObjectProperty.homMk i₀) 𝕄'
                  (isInvertibleSheaf_pullbackSheaf D (g ≫ p) hY'
                    (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX'
                    (ObjectProperty.homMk (Limits.pullback.snd 𝔼.1.ι g)) M hM)))
              (gysinCycleMap D (g ≫ p) ℤμ (isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g) (m + 1)
                (sectionGysinRule D (g ≫ p) hY' 𝕃g 𝕤g (m + 1)
                  (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L
                    hL)) α))) := by
  have hLg := isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L hL
  have hZμ := isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g
  have hs₁ : Limits.pullback.snd 𝔼.1.ι g ≫ g ≫ p = Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc]
  have H1 := exists_chowClassCanonical_gysinCycleMap_pullbackSheaf_comp_of_eq D
    (g ≫ p) hY' M t hM (Limits.pullback.snd 𝔼.1.ι g) i₀
    (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX' (ℤμ).1.ι hZμ m hs₁ hi₀snd
    (gysinCycleMap D (g ≫ p) ℤμ hZμ (m + 1) (sectionGysinRule D (g ≫ p) hY' 𝕃g 𝕤g (m + 1) hLg) α)
  refine H1.elim fun e H1 => H1.elim fun he H1 => H1.elim fun hep h1g => ?_
  have heB := (Category.assoc e _ _).symm.trans (eq_whisker he ((ℤμ).1.ι ≫ g ≫ p))
  -- Stacks 0ERC on `Y'` for the pairs `(ℳ, t)` and `(g^*ℒ, g^*σ)`
  refine (exists_gysinComm_hom D (g ≫ p) hY' M t hM 𝕃g 𝕤g hLg).elim fun h H2 =>
    H2.elim fun hh hhp => ?_
  have hGC := chowClassCanonical_properCyclePushforward_gysin_gysin_eq D (g ≫ p) hY' M t hM 𝕃g 𝕤g
    hLg m h hh hhp α
  have hhB := comp_comp_comp_eq_of_comp_comp_eq hh (g ≫ p)
  exact chowClassCanonical_properCyclePushforward_comp_comp_of_mono D _ _ _ _ _ _ _ _ m₀ hhB heB
    hψB hhp hep hψp hh he hψm m _ _ _ hGC h1g
end Comm

include hL hM in
/-- **Stacks 0ERJ (3) for the Gysin class of Stacks 0ERP, at the level of classes.**  For a test
space `g : Y' ⟶ X`, a pair `(ℳ, t)` on `Y'` with `D' = Z(t)` and the identification
`E ×_X (D' ×_{Y'} Y') ≅ Z(t')` of the axiom, the two ways of applying the Gysin map of `σ` and of
`t` to `α ∈ Z_{m+2}(Y')` give the same class in `CH_m(Z(t'))`.  This is Stacks 0ERC on `Y'` for
the pairs `(ℳ, t)` and `(g^*ℒ, g^*σ)`
(`chowClassCanonical_properCyclePushforward_gysin_gysin_eq`), Stacks 0ER5 along
`Z(g^*σ) ≅ E ×_X Y'` (`chowClassCanonical_gysinCycleMap_properCyclePushforward`), and the
comparisons of iterated with direct inverse images of the two pairs. -/
private theorem chowClassCanonical_gysinBivariantCap_gysin_comm
    (hXd : D.IsGood (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p))
    (iso : Limits.pullback 𝔼.1.ι ((𝔽).1.ι ≫ g) ≅ (𝕋).1.toFunctor)
    (hiso : iso.hom ≫ (𝕋).1.ι = bivariantBaseChangeMap D 𝔼.1.ι g (𝔽).1.ι)
    (hbase : iso.hom ≫ ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) =
      Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom) (m : ℤ)
    (α : CycleGroup D (g ≫ p) (m + 1 + 1)) :
    chowClassCanonical.{u + 1} D ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
        (isGood_vanishingLocus D _ hX' _ _) m
        (properCyclePushforward D (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p) hXd
          ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
          (isGood_vanishingLocus D _ hX' _ _) hbase hisoProper.2.1.2 m
          (properCyclePushforward D
            ((ℤσF).1.ι ≫ ((𝔽).1.ι ≫ g) ≫ p)
            (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) _ hXd
            (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL ((𝔽).1.ι ≫ g)
              (isGood_vanishingLocus D (g ≫ p) hY' M t))
            (isProper_of_isIso D.site D.base D.base_mem _).2.1.2 m
            (gysinCycleMap D (((𝔽).1.ι ≫ g) ≫ p)
              ℤσF
              (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) m
              (sectionGysinRule D (((𝔽).1.ι ≫ g) ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' M t) _
                (pullbackGlobalSection D p hp (((𝔽).1.ι ≫ g) ≫ p)
                  (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk ((𝔽).1.ι ≫ g))
                  L σ) m
                (isInvertibleSheaf_pullbackSheaf D p hp (((𝔽).1.ι ≫ g) ≫ p)
                  (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk ((𝔽).1.ι ≫ g))
                  L hL))
              (gysinCycleMap D (g ≫ p) 𝔽 (isGood_vanishingLocus D (g ≫ p) hY' M t) (m + 1)
                (sectionGysinRule D (g ≫ p) hY' M t (m + 1) hM) α)))) =
      chowClassCanonical.{u + 1} D ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
        (isGood_vanishingLocus D _ hX' _ _) m
        (gysinCycleMap D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) 𝕋
          (isGood_vanishingLocus D _ hX' _ _) m
          (sectionGysinRule D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX' _ _ m
            (isInvertibleSheaf_bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M hM))
          (properCyclePushforward D ((ℤμ).1.ι ≫ g ≫ p)
            (isGood_vanishingLocus D (g ≫ p) hY' _ _) _ hX'
            (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL g hY')
            (isProper_of_isIso D.site D.base D.base_mem _).2.1.2 (m + 1)
            (gysinCycleMap D (g ≫ p) ℤμ
              (isGood_vanishingLocus D (g ≫ p) hY' _ _) (m + 1)
              (sectionGysinRule D (g ≫ p) hY' _
                (pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ) (m + 1)
                (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L
                  hL)) α))) := by
  have hZμ := isGood_vanishingLocus D (g ≫ p) hY' 𝕃g 𝕤g
  have hFg := isGood_vanishingLocus D (g ≫ p) hY' M t
  refine (⟨_, rfl⟩ : ∃ i, i = gysinTestVanishingLocusIso D p hp L σ hL g hY').elim
    fun i₀ hi₀ => ?_
  have hi₀snd : i₀.hom ≫ Limits.pullback.snd 𝔼.1.ι g = (ℤμ).1.ι :=
    hi₀ ▸ gysinTestVanishingLocusIso_hom_snd D p hp L σ hL g hY'
  have hi₀B : i₀.hom ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p = (ℤμ).1.ι ≫ g ≫ p :=
    hi₀ ▸ gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL g hY'
  -- Stacks 0ER5 along `Z(g^*σ) ≅ E ×_X Y'` for the pair `(𝒩', t')`
  have H5 :=
    exists_chowClassCanonical_gysinCycleMap_properCyclePushforward_bivariant D (𝔼.1.ι ≫ p) p
      𝔼.1.ι g hY' hX' M t hM ((ℤμ).1.ι ≫ g ≫ p) hZμ i₀.hom hi₀B
      (isProper_of_isIso D.site D.base D.base_mem i₀.hom) m
      (gysinCycleMap D (g ≫ p) ℤμ hZμ (m + 1)
        (sectionGysinRule D (g ≫ p) hY' 𝕃g 𝕤g (m + 1)
          (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L hL)) α)
  refine H5.elim fun ψ H5 => H5.elim fun hψw H5 => H5.elim fun hψB H5 =>
    H5.elim fun hψp h5 => ?_
  have hψm := ((Category.assoc ψ _ _).symm.trans (eq_whisker hψw _)).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ hi₀snd))
  refine (⟨_, rfl⟩ : ∃ i, i = gysinTestVanishingLocusIso D p hp L σ hL ((𝔽).1.ι ≫ g) hFg).elim
    fun i₂ hi₂ => ?_
  have hA : iso.hom ≫ (𝕋).1.ι ≫ Limits.pullback.snd 𝔼.1.ι g =
      Limits.pullback.snd 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ (𝔽).1.ι := by
    rw [← Category.assoc, hiso]
    simp [bivariantBaseChangeMap]
  have hB : i₂.hom ≫ Limits.pullback.snd 𝔼.1.ι ((𝔽).1.ι ≫ g) = (ℤσF).1.ι :=
    hi₂ ▸ gysinTestVanishingLocusIso_hom_snd D p hp L σ hL ((𝔽).1.ι ≫ g) hFg
  have hjm : (i₂.hom ≫ iso.hom) ≫ (𝕋).1.ι ≫ Limits.pullback.snd 𝔼.1.ι g =
      (ℤσF).1.ι ≫ (𝔽).1.ι := by
    rw [Category.assoc i₂.hom iso.hom, hA, ← Category.assoc i₂.hom, hB]
  have hjB : (i₂.hom ≫ iso.hom) ≫ (𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p =
      (ℤσF).1.ι ≫ ((𝔽).1.ι ≫ g) ≫ p := by
    rw [Category.assoc i₂.hom iso.hom, hbase, hi₂]
    exact gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL ((𝔽).1.ι ≫ g) hFg
  have hj := isProper_comp D.site D.base D.base_mem
    (isGood_vanishingLocus D (((𝔽).1.ι ≫ g) ≫ p) hFg _ _).1 hXd.1
    (isGood_vanishingLocus D _ hX' _ _).1 i₂.hom iso.hom
    (isProper_of_isIso D.site D.base D.base_mem i₂.hom) hisoProper
  have HP2 :=
    exists_chowClassCanonical_properCyclePushforward_gysin_comm_of_mono D p hp L σ hL g hY' hX'
      M t hM i₀.hom hi₀snd _ (isGood_vanishingLocus D _ hX' _ _)
      ((𝕋).1.ι ≫ Limits.pullback.snd 𝔼.1.ι g) ψ hψB hψp hψm m α
  refine HP2.elim fun j' HP2 => HP2.elim fun hj'B HP2 => HP2.elim fun hj' HP2 =>
    HP2.elim fun hj'm hP2 => ?_
  have hP1 := chowClassCanonical_properCyclePushforward_gysin_pullbackSheaf_comp_of_mono D p hp L
    σ hL g hY' M t _ (isGood_vanishingLocus D _ hX' _ _)
    ((𝕋).1.ι ≫ Limits.pullback.snd 𝔼.1.ι g) (i₂.hom ≫ iso.hom) hjB hj hjm j' hj'B hj' hj'm m
    (gysinCycleMap D (g ≫ p) 𝔽 hFg (m + 1) (sectionGysinRule D (g ≫ p) hY' M t (m + 1) hM) α)
  subst hi₀ hi₂
  rw [properCyclePushforward_comp D _ _ _ _ hXd _
    (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL ((𝔽).1.ι ≫ g) hFg) hbase
    (isProper_of_isIso D.site D.base D.base_mem _) hisoProper m]
  exact (hP1.trans hP2).trans h5.symm

include hL hM in
/-- `chowClassCanonical_gysinBivariantCap_gysin_comm` with the degrees written as the cap operation
of Stacks 0ERP writes them: `b + 1 = a` for the Gysin map of `t` followed by the cap at
`D' ⟶ X`, and `b + 1 = c`, `a + 1 = c + 1` for the cap at `Y' ⟶ X` followed by the Gysin map of
`t'`. -/
private theorem chowClassCanonical_gysinBivariantCap_gysin_comm_of_eq
    (hXd : D.IsGood (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p))
    (iso : Limits.pullback 𝔼.1.ι ((𝔽).1.ι ≫ g) ≅ (𝕋).1.toFunctor)
    (hiso : iso.hom ≫ (𝕋).1.ι = bivariantBaseChangeMap D 𝔼.1.ι g (𝔽).1.ι)
    (hbase : iso.hom ≫ ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) =
      Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom) {a b c : ℤ} (hab : b + 1 = a)
    (hbc : b + 1 = c) (hc : a + 1 = c + 1) (α : CycleGroup D (g ≫ p) (a + 1)) :
    chowClassCanonical.{u + 1} D ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
        (isGood_vanishingLocus D _ hX' _ _) b
        (properCyclePushforward D (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p) hXd
          ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
          (isGood_vanishingLocus D _ hX' _ _) hbase hisoProper.2.1.2 b
          (properCyclePushforward D ((ℤσF).1.ι ≫ ((𝔽).1.ι ≫ g) ≫ p)
            (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) _ hXd
            (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL ((𝔽).1.ι ≫ g)
              (isGood_vanishingLocus D (g ≫ p) hY' M t))
            (isProper_of_isIso D.site D.base D.base_mem _).2.1.2 b
            (gysinCycleMap D (((𝔽).1.ι ≫ g) ≫ p) ℤσF
              (isGood_vanishingLocus D _ (isGood_vanishingLocus D (g ≫ p) hY' M t) _ _) b
              (sectionGysinRule D (((𝔽).1.ι ≫ g) ≫ p) (isGood_vanishingLocus D (g ≫ p) hY' M t) _
                (pullbackGlobalSection D p hp (((𝔽).1.ι ≫ g) ≫ p)
                  (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk ((𝔽).1.ι ≫ g))
                  L σ) b
                (isInvertibleSheaf_pullbackSheaf D p hp (((𝔽).1.ι ≫ g) ≫ p)
                  (isGood_vanishingLocus D (g ≫ p) hY' M t) (ObjectProperty.homMk ((𝔽).1.ι ≫ g))
                  L hL))
              (hab.symm ▸ gysinCycleMap D (g ≫ p) 𝔽 (isGood_vanishingLocus D (g ≫ p) hY' M t) a
                (sectionGysinRule D (g ≫ p) hY' M t a hM) α)))) =
      chowClassCanonical.{u + 1} D ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
        (isGood_vanishingLocus D _ hX' _ _) b
        (gysinCycleMap D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) 𝕋
          (isGood_vanishingLocus D _ hX' _ _) b
          (sectionGysinRule D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX' _ _ b
            (isInvertibleSheaf_bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M hM))
          ((cycleGroupDegreeCongr D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hbc).symm
            (properCyclePushforward D ((ℤμ).1.ι ≫ g ≫ p)
              (isGood_vanishingLocus D (g ≫ p) hY' _ _) _ hX'
              (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL g hY')
              (isProper_of_isIso D.site D.base D.base_mem _).2.1.2 c
              (gysinCycleMap D (g ≫ p) ℤμ (isGood_vanishingLocus D (g ≫ p) hY' _ _) c
                (sectionGysinRule D (g ≫ p) hY' _
                  (pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ) c
                  (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L
                    hL)) (hc ▸ α))))) := by
  subst hab hbc
  exact chowClassCanonical_gysinBivariantCap_gysin_comm D p hp L σ hL g hY' hX' M t hM hXd iso
    hiso hbase hisoProper b α

include hL hM in
/-- **Stacks 0ERJ (3) for the Gysin class of Stacks 0ERP**, in the shape of the field
`gysin_naturality` of `AlgebraicGeometry.Space.BivariantClassCanonical`: the cap of `α` is the
class of `β`, the cap of `j^* α` is the class of `γ`, and `[iso_* γ] = [(t')^* β]` in
`CH_{k-1}(Z(t'))` (`chowClassCanonical_gysinBivariantCap_gysin_comm`). -/
private theorem gysinBivariantCap_gysin_naturality
    (hXd : D.IsGood (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p))
    (iso : Limits.pullback 𝔼.1.ι ((𝔽).1.ι ≫ g) ≅ (𝕋).1.toFunctor)
    (hiso : iso.hom ≫ (𝕋).1.ι = bivariantBaseChangeMap D 𝔼.1.ι g (𝔽).1.ι)
    (hbase : iso.hom ≫ ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) =
      Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom) (k : ℤ)
    (α : CycleGroup D (g ≫ p) (k + 1)) :
    ∃ (β : CycleGroup D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) (k - 1 + 1))
      (γ : CycleGroup D (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p) (k - 1)),
      gysinBivariantCap D p hp L σ hL g hY' hX' (k + 1)
            (chowClassCanonical.{u + 1} D (g ≫ p) hY' (k + 1) α) =
          chowClassCanonical.{u + 1} D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX' (k + 1 - 1)
            (cycleGroupDegreeCongr D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) (by omega) β) ∧
        gysinBivariantCap D p hp L σ hL ((𝔽).1.ι ≫ g) (isGood_vanishingLocus D (g ≫ p) hY' M t)
              hXd k
              (chowClassCanonical.{u + 1} D ((𝔽).1.ι ≫ g ≫ p)
                (isGood_vanishingLocus D (g ≫ p) hY' M t) k
                (gysinCycleMap D (g ≫ p) 𝔽 (isGood_vanishingLocus D (g ≫ p) hY' M t) k
                  (sectionGysinRule D (g ≫ p) hY' M t k hM) α)) =
            chowClassCanonical.{u + 1} D
              (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p) hXd (k - 1) γ ∧
          chowClassCanonical.{u + 1} D ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
              (isGood_vanishingLocus D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX'
                (bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M)
                (bivariantPullbackSection D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M t)) (k - 1)
              (properCyclePushforward D
                (Limits.pullback.fst 𝔼.1.ι ((𝔽).1.ι ≫ g) ≫ 𝔼.1.ι ≫ p) hXd
                ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
                (isGood_vanishingLocus D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX'
                  (bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M)
                  (bivariantPullbackSection D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M t)) hbase
                hisoProper.2.1.2 (k - 1) γ) =
            chowClassCanonical.{u + 1} D ((𝕋).1.ι ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p)
              (isGood_vanishingLocus D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX'
                (bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M)
                (bivariantPullbackSection D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M t)) (k - 1)
              (gysinCycleMap D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) 𝕋
                (isGood_vanishingLocus D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX'
                  (bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M)
                  (bivariantPullbackSection D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M t)) (k - 1)
                (sectionGysinRule D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hX'
                  (bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M)
                  (bivariantPullbackSection D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M t) (k - 1)
                  (isInvertibleSheaf_bivariantPullbackSheaf D (𝔼.1.ι ≫ p) p 𝔼.1.ι g hY' hX' M
                    hM)) β) := by
  have hbc : k - 1 + 1 = k + 1 - 1 := by omega
  refine ⟨(cycleGroupDegreeCongr D (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p) hbc).symm
      (properCyclePushforward D ((ℤμ).1.ι ≫ g ≫ p)
        (isGood_vanishingLocus D (g ≫ p) hY' _ _) _ hX'
        (gysinTestVanishingLocusIso_hom_comp_structure D p hp L σ hL g hY')
        (isProper_of_isIso D.site D.base D.base_mem _).2.1.2 (k + 1 - 1)
        (gysinCycleMap D (g ≫ p) ℤμ (isGood_vanishingLocus D (g ≫ p) hY' _ _) (k + 1 - 1)
          (sectionGysinRule D (g ≫ p) hY' _
            (pullbackGlobalSection D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L σ) (k + 1 - 1)
            (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hY' (ObjectProperty.homMk g) L
              hL)) ((sub_add_cancel (k + 1) 1).symm ▸ α))), _, ?_,
    gysinBivariantCap_chowClassCanonical D p hp L σ hL ((𝔽).1.ι ≫ g)
      (isGood_vanishingLocus D (g ≫ p) hY' M t) hXd k
      (gysinCycleMap D (g ≫ p) 𝔽 (isGood_vanishingLocus D (g ≫ p) hY' M t) k
        (sectionGysinRule D (g ≫ p) hY' M t k hM) α),
    chowClassCanonical_gysinBivariantCap_gysin_comm_of_eq D p hp L σ hL g hY' hX' M t hM hXd iso
      hiso hbase hisoProper (sub_add_cancel k 1) hbc (sub_add_cancel (k + 1) 1).symm α⟩
  rw [gysinBivariantCap_chowClassCanonical, AddEquiv.apply_symm_apply]

end GysinNaturality

/-! ### Stacks 0ERP -/

section Registration

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (p : X ⟶ D.space)
    (hp : D.IsGood p) (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L)

/-- `E = Z(σ) ⊆ X`. -/
local notation "𝔼" => vanishingLocus D p hp L σ

include hL in
/-- **The defining equation of the Gysin class of Stacks 0ERP.**  On the class of `α ∈ Z_k(X')`
the cap operation is the class of the Gysin cycle of Stacks 0ER1 of the pulled-back triple
`(g^*ℒ, g^*σ)` at its own rule, carried from `Z(g^*σ)` to `E ×_X X'` along any identification `e`
over `X'`: `pullback.snd` is a monomorphism, so `e` is the identification of Stacks 0ER3, and
along an isomorphism the transport of Chow groups is proper pushforward
(`properCyclePushforward_eq_cycleGroupClosedPushforward`). -/
private theorem gysinBivariantCap_chowClassCanonical_eq_pushforwardOfIso {X' : D.Ambient}
    (g : X' ⟶ X) (hX' : D.IsGood (g ≫ p))
    (hE' : D.IsGood (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p))
    (e : (vanishingLocus D (g ≫ p) hX'
        (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
        (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)).1.toFunctor ≅
      Limits.pullback 𝔼.1.ι g)
    (he : e.hom ≫ Limits.pullback.snd 𝔼.1.ι g =
      (vanishingLocus D (g ≫ p) hX'
        (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
        (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)).1.ι)
    (hcomp : e.hom ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p =
      (vanishingLocus D (g ≫ p) hX'
        (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
        (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)).1.ι ≫ g ≫ p)
    (k : ℤ) (α : CycleGroup D (g ≫ p) k) :
    gysinBivariantCap D p hp L σ hL g hX' hE' k (chowClassCanonical.{u + 1} D (g ≫ p) hX' k α) =
      chowGroupCanonicalPushforwardOfIso.{u + 1} D _ (isGood_vanishingLocus D (g ≫ p) hX' _ _) _
        hE' e hcomp (k - 1)
        (chowClassCanonical.{u + 1} D _ (isGood_vanishingLocus D (g ≫ p) hX' _ _) (k - 1)
          (gysinCycleMap D (g ≫ p) (vanishingLocus D (g ≫ p) hX'
              (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
              (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ))
            (isGood_vanishingLocus D (g ≫ p) hX' _ _) (k - 1)
            (sectionGysinRule D (g ≫ p) hX' _
              (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ) (k - 1)
              (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L
                hL))
            (cycleGroupDegreeCongr D (g ≫ p) (sub_add_cancel k 1).symm α))) := by
  have hei : e = gysinTestVanishingLocusIso D p hp L σ hL g hX' :=
    Iso.ext ((cancel_mono (Limits.pullback.snd 𝔼.1.ι g)).1
      (he.trans (gysinTestVanishingLocusIso_hom_snd D p hp L σ hL g hX').symm))
  subst hei
  rw [gysinBivariantCap_chowClassCanonical, chowGroupCanonicalPushforwardOfIso_chowClassCanonical,
    cycleGroupDegreeCongr_eq_cast, properCyclePushforward_eq_cycleGroupClosedPushforward D _ _ _ hE'
      (isClosedImmersion_of_isIso D.site D.base D.base_mem _)]

include hL in
/-- **Stacks 0ERP.**  In Situation 0EDT let `X/B` be good and `(ℒ, σ, i : E → X)` a triple as in
Stacks 0ER1: `ℒ` an invertible `𝒪_X`-module, `σ` a global section and `E = Z(σ)` its vanishing
locus.  Then the rule that to `g : X' ⟶ X` assigns the Gysin map
`(i')^* : CH_k(X') ⟶ CH_{k-1}(E')`, `E' = E ×_X X'`, is a bivariant class of degree `1` for
`i : E ⟶ X` (`AlgebraicGeometry.Space.BivariantClassCanonical`, Stacks 0ERJ).

The cap operation of the class is pinned down on the class of every `k`-cycle `α` on every test
space: it is the class of the Gysin cycle of Stacks 0ER1 of the pulled-back triple
`(g^*ℒ, g^*σ, Z(g^*σ) → X')` (Stacks 0ER3) at its own rule, carried to `E ×_X X'` along the
identification `e : Z(g^*σ) ≅ E ×_X X'` over `X'` (`chowGroupCanonicalPushforwardOfIso`).  The
three axioms of Stacks 0ERJ are Stacks 0ER5, Stacks 0ER6 and Stacks 0ERC for the pulled-back
triples, as in the source's proof. -/
@[stacks 0ERP "the rule g : X' → X ↦ (i')^* : CH_k(X') → CH_{k-1}(E'), E' = E ×_X X', for X/B \
good and (L, s, i : E → X) a triple as in 0ER1, is a bivariant class of degree 1 for i; the cap \
operation is pinned to the Gysin map of the pulled-back triple carried along Z(g^*s) ≅ E ×_X X'"]
theorem exists_bivariantClassCanonical_gysin :
    ∃ c : BivariantClassCanonical.{u + 1} D (𝔼.1.ι ≫ p) (isGood_vanishingLocus D p hp L σ) p hp
        𝔼.1.ι rfl 1,
      ∀ {X' : D.Ambient} (g : X' ⟶ X) (hX' : D.IsGood (g ≫ p))
        (hE' : D.IsGood (Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p))
        (e : (vanishingLocus D (g ≫ p) hX'
            (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
            (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)).1.toFunctor ≅
          Limits.pullback 𝔼.1.ι g)
        (_he : e.hom ≫ Limits.pullback.snd 𝔼.1.ι g =
          (vanishingLocus D (g ≫ p) hX'
            (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
            (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)).1.ι)
        (hcomp : e.hom ≫ Limits.pullback.fst 𝔼.1.ι g ≫ 𝔼.1.ι ≫ p =
          (vanishingLocus D (g ≫ p) hX'
            (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
            (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)).1.ι ≫
            g ≫ p)
        (k : ℤ) (α : CycleGroup D (g ≫ p) k),
        c.cap g hX' hE' k (chowClassCanonical.{u + 1} D (g ≫ p) hX' k α) =
          chowGroupCanonicalPushforwardOfIso.{u + 1} D _
            (isGood_vanishingLocus D (g ≫ p) hX' _ _) _ hE' e hcomp (k - 1)
            (chowClassCanonical.{u + 1} D _ (isGood_vanishingLocus D (g ≫ p) hX' _ _) (k - 1)
              (gysinCycleMap D (g ≫ p) (vanishingLocus D (g ≫ p) hX'
                  (pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L)
                  (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ))
                (isGood_vanishingLocus D (g ≫ p) hX' _ _) (k - 1)
                (sectionGysinRule D (g ≫ p) hX' _
                  (pullbackGlobalSection D p hp (g ≫ p) hX' (ObjectProperty.homMk g) L σ)
                  (k - 1)
                  (isInvertibleSheaf_pullbackSheaf D p hp (g ≫ p) hX' (ObjectProperty.homMk g)
                    L hL))
                (cycleGroupDegreeCongr D (g ≫ p) (sub_add_cancel k 1).symm α))) :=
  ⟨{ cap := fun g hX' hE' k => gysinBivariantCap D p hp L σ hL g hX' hE' k
     proper_naturality := fun g hY' hX' h hY'' hX'' hh h' sq hfst hh' k α =>
       gysinBivariantCap_proper_naturality D p hp L σ hL g hY' h hY'' hX' hX'' hh h' sq hfst hh'
         k α
     flat_naturality := fun g hY' hX' h hY'' hX'' hh r hr h' sq hfst hh' hr' k α =>
       gysinBivariantCap_flat_naturality D p hp L σ hL g hY' h hY'' hX' hX'' hh r hr h' sq hfst
         hh' hr' k α
     gysin_naturality := fun g hY' hX' M t hM hXd iso hiso hbase hisoProper k α =>
       gysinBivariantCap_gysin_naturality D p hp L σ hL g hY' hX' M t hM hXd iso hiso hbase
         hisoProper k α },
    fun g hX' hE' e he hcomp k α =>
      gysinBivariantCap_chowClassCanonical_eq_pushforwardOfIso D p hp L σ hL g hX' hE' e he hcomp
        k α⟩

end Registration

end AlgebraicGeometry.Space

end

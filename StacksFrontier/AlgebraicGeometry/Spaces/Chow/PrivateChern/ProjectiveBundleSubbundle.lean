module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.MorphismSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleEmbeddingTwist
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentKernels

/-!
# `𝐏(ℱ)` inside the zero scheme of the section of `𝒪_{𝐏(ℰ)}(1) ⊗ π^*ℒ^{-1}`

Let `X` be an algebraic space, `q : ℰ ⟶ ℱ` a surjection of finite locally free `𝒪_X`-modules,
surjective on every étale chart, `ℒ` an invertible `𝒪_X`-module and `i : ℒ ⟶ ℰ` with `i ≫ q = 0`.
On the projective bundle `π : 𝐏(ℰ) ⟶ X` the composite

  `s : π^*ℒ ⟶ π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`

is a global section `σ` of `𝒪(1) ⊗ π^*ℒ^{-1}`
(`AlgebraicGeometry.Space.PrivateChern.morphismSection`). Its restriction to `𝐏(ℱ)` along the
morphism `ι : 𝐏(ℱ) ⟶ 𝐏(ℰ)` vanishes: by
`AlgebraicGeometry.Space.PrivateChern.exists_projectiveBundleEmbedding_twistIso`,
`ι^*s` is, up to isomorphisms, `π_ℱ^*(i ≫ q) ≫ τ_ℱ = 0`. So `ι` factors through the zero scheme
`Z(σ) ⊆ 𝐏(ℰ)` (Stacks 0846 (2)).

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.subbundleMorphism`: `s : π^*ℒ ⟶ 𝒪(1)`.
* `AlgebraicGeometry.Space.PrivateChern.subbundleZeroScheme`: the zero scheme `Z(σ)`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.modulePullback_map_subbundleMorphism_eq_zero`: `ι^*s = 0`.
* `AlgebraicGeometry.Space.PrivateChern.exists_subbundleZeroScheme_lift`: `ι` factors through
  `Z(σ)`. The factorization `𝐏(ℱ) ⟶ Z(σ)` is produced existentially rather than as a named
  definition, together with the identity exhibiting it as a factorization of `ι`.

## References

* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {E F L : Modules.{u, u} B S hS X.1 X.2}
  [hE : E.IsQuasicoherentOnSite] [hF : F.IsQuasicoherentOnSite]
  (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V)) (i : L ⟶ E)
  (hL : IsInvertibleModule X L)

/-- **The composite `s : π^*ℒ ⟶ π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`.** -/
def subbundleMorphism :
    (modulePullback B S hS (projectiveBundleProj E hfreeE)).obj L ⟶
      (projectiveBundleTwist E hfreeE).obj :=
  (modulePullback B S hS (projectiveBundleProj E hfreeE)).map i ≫
    (projectiveBundleTautological E hfreeE).hom

include hF in
/-- **The restriction of `s` to `𝐏(ℱ)` vanishes**: `ι^*s = 0`. -/
theorem modulePullback_map_subbundleMorphism_eq_zero [Epi q] (hiq : i ≫ q = 0) :
    (modulePullback B S hS (projectiveBundleEmbedding hfreeE hfreeF q hq)).map
      (subbundleMorphism hfreeE i) = 0 := by
  obtain ⟨e, he⟩ := exists_projectiveBundleEmbedding_twistIso hfreeE hfreeF q hq
  have h2 := congrArg (fun k => (modulePullback B S hS (projectiveBundleProj F hfreeF)).map i ≫
    k ≫ e.inv) he
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
  refine ((Iso.eq_inv_comp (QuasiCoherentDescent.pullbackComparison B S hS
    (projectiveBundleEmbedding hfreeE hfreeF q hq) (projectiveBundleProj E hfreeE)
    (projectiveBundleProj F hfreeF) (projectiveBundleEmbedding_comp_proj hfreeE hfreeF q hq)
    L)).2 ?_).trans comp_zero
  have := preservesZeroMorphisms_modulePullback B S hS (projectiveBundleProj F hfreeF)
  rw [subbundleMorphism, Functor.map_comp, ← Category.assoc,
    ← QuasiCoherentDescent.pullbackComparison_naturality, Category.assoc, h2,
    ← Functor.map_comp_assoc, hiq, Functor.map_zero, zero_comp]

include hL in
/-- `π^*ℒ` is invertible. -/
theorem isInvertibleModule_subbundleSource :
    IsInvertibleModule (projectiveBundle E hfreeE)
      ((modulePullback B S hS (projectiveBundleProj E hfreeE)).obj L) :=
  modulePullbackInvertible _ L hL

/-- **The zero scheme `Z(σ) ⊆ 𝐏(ℰ)`** of the section of `𝒪(1) ⊗ π^*ℒ^{-1}` attached to `s`. -/
abbrev subbundleZeroScheme : ClosedSubspaces B S hS (projectiveBundle E hfreeE).1 :=
  zeroScheme B S hS (projectiveBundle E hfreeE)
    (morphismSectionModule (isInvertibleModule_subbundleSource hfreeE hL)
      (projectiveBundleTwist E hfreeE).obj)
    (morphismSection (isInvertibleModule_subbundleSource hfreeE hL) (subbundleMorphism hfreeE i))

include hF in
/-- `ι : 𝐏(ℱ) ⟶ 𝐏(ℰ)` factors through `Z(σ)`. -/
theorem exists_subbundleZeroScheme_lift [Epi q] (hiq : i ≫ q = 0) :
    ∃ h : projectiveBundle F hfreeF ⟶ (⟨(subbundleZeroScheme hfreeE i hL).1.toFunctor,
        (subbundleZeroScheme hfreeE i hL).2.1⟩ : AlgebraicSpaces B S hS),
      h ≫ ObjectProperty.homMk (subbundleZeroScheme hfreeE i hL).1.ι =
        projectiveBundleEmbedding hfreeE hfreeF q hq :=
  (exists_comp_eq_zeroScheme_morphismSection_iff (isInvertibleModule_subbundleSource hfreeE hL)
    (subbundleMorphism hfreeE i) (isInvertibleModule_projectiveBundleTwist E hfreeE) _).2
    (modulePullback_map_subbundleMorphism_eq_zero hfreeE hfreeF q hq i hiq)

omit hE hF in
/-- The readings of `i` and `q` compose to zero. -/
theorem moduleReadingMap_comp_moduleReadingMap_eq_zero (hiq : i ≫ q = 0)
    {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    moduleReadingMap i ψ ≫ moduleReadingMap q ψ = 0 := by
  have := preservesZeroMorphisms_modulePullback B S hS ψ
  have : (representedSmallEtaleModuleEquivalence B S hS T).inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).PreservesZeroMorphisms :=
    have := (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
        T.left.property).isRightAdjoint
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  simp only [moduleReadingMap, ← Functor.map_comp, hiq, Functor.map_zero]

omit hE hF in
/-- **The reading of a short exact sequence with quasi-coherent kernel along an étale chart is
short exact**: the inverse image along an étale morphism is exact (Stacks 03LV) and the
restriction from the small étale site to the small Zariski site is exact on sequences with
quasi-coherent kernel (Stacks 06VE). -/
theorem shortExact_moduleReadingMap (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite)
    {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    (hψ : IsEtale B S hS ψ.hom) :
    (ShortComplex.mk (moduleReadingMap i ψ) (moduleReadingMap q ψ)
      (moduleReadingMap_comp_moduleReadingMap_eq_zero q i hiq ψ)).ShortExact := by
  let : Limits.HasZeroMorphisms (SheafOfModules.{u}
      (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)) :=
    Preadditive.preadditiveHasZeroMorphisms
  have hex : exactFunctor (Modules.{u, u} B S hS X.1 X.2)
      (Modules.{u, u} B S hS (representedAlgebraicSpace B S hS T).1
        (representedAlgebraicSpace B S hS T).2) (modulePullback B S hS ψ) :=
    modulePullback_exact B S hS ψ hψ
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp hex
  have h₁ : ((ShortComplex.mk i q hiq).map (modulePullback B S hS ψ)).ShortExact :=
    hC.map_of_exact (modulePullback B S hS ψ)
  let C' : ShortComplex (SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) :=
    ShortComplex.mk ((modulePullback B S hS ψ).map i) ((modulePullback B S hS ψ).map q)
      (((modulePullback B S hS ψ).map_comp i q).symm.trans
        ((congrArg (modulePullback B S hS ψ).map hiq).trans (Functor.map_zero _ _ _)))
  have h₁' : C'.ShortExact := h₁
  have h₃ := isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T _
      (isQuasicoherentOnSite_modulePullback_schemeReading L hLq ψ)
  have hz : (representedSmallEtaleModuleEquivalence B S hS T).inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hl : PreservesFiniteLimits (representedSmallEtaleModuleEquivalence B S hS T).inverse :=
    inferInstance
  have hc : PreservesFiniteColimits (representedSmallEtaleModuleEquivalence B S hS T).inverse :=
    inferInstance
  have h4 := @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ h₁'
      (representedSmallEtaleModuleEquivalence B S hS T).inverse _ _ _
  have h5 := _root_.AlgebraicGeometry.SmallEtale.shortExact_restrictModule_map _ _ _ h4 h₃
  refine ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)) h5

end AlgebraicGeometry.Space.PrivateChern

end

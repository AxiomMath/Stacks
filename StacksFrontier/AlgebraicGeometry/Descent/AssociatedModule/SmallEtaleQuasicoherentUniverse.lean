module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcohUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeFlatPullbackExact
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallAffineEtaleCartesianAcyclic
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCoherentExactSequences

/-!
# Quasi-coherent modules on the small étale site form a weak Serre subcategory, at section
# universe `u + 1`

Let `S` be a scheme contained in a big étale site `B`.  This file proves that the quasi-coherent
sheaves of modules on the small étale site `S_étale`, with sections in `Type (u + 1)`, are closed
under kernels, cokernels and extensions: Stacks 06VE (10) and Stacks 0GNB at the section universe
of the higher direct images of Stacks 0765.  At section universe `u` this is
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentWeakSerre`, whose
route goes through Mathlib's quasi-coherent modules on a scheme and is pinned to `u`.

## The route

Everything is read through the cartesian criterion of Descent, Proposition 03DX (2)
(`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_bijective_restrictionBaseChange_succ`):
a sheaf of modules is quasi-coherent exactly when, for every morphism `T ⟶ T'` of affine objects,
the base-change comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.  That comparison is a
natural transformation between two functors of `𝒢`, sections over `T'` followed by extension of
scalars and sections over `T`.

* **Kernels.**  Both functors preserve finite limits — the first because `Γ(T)` is flat over
  `Γ(T')` — so the comparison is an isomorphism at a kernel when it is one at the source and the
  target (`CategoryTheory.NatTrans.isIso_app_limit`).
* **Descent, Proposition 03DW.**  An epimorphism whose kernel is cartesian is surjective on the
  sections over an affine object: restricted to the small affine étale site the short exact
  sequence stays short exact, the kernel has no first cohomology there
  (`AlgebraicGeometry.SmallAffineEtale.isZero_rightDerived_evaluation_of_isCartesian`), and the
  long exact sequence concludes.
* **Extensions and quotients.**  Over affine objects a short exact sequence with cartesian first
  term therefore has short exact sections, extension of scalars along the flat restriction map
  keeps it so, and the five lemma compares the two rows.
* **Cokernels.**  The coimage of `f : 𝒢 ⟶ 𝒢'` is a quotient of `𝒢` by the kernel, it is the
  image, and the cokernel is the quotient of `𝒢'` by the image.

## Main results

* `AlgebraicGeometry.SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite_succ`,
  `AlgebraicGeometry.SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite_succ` and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_X₂_of_shortExact_succ`: **quasi-coherence
  on `S_étale`, at section universe `u + 1`, is closed under kernels, cokernels and extensions.**
* `AlgebraicGeometry.SmallEtale.surjective_val_app_of_epi_of_cartesian_kernel`: **Descent,
  Proposition 03DW at section universe `u + 1`**, in the form an epimorphism with cartesian kernel
  is surjective on affine sections.
* `AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_kernel` and
  `AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_X₂_iff_X₃_of_shortExact`: the
  base-change comparison along kernels and along short exact sequences.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

-- The ambient-universe instances on sheaves of modules state their module universe as a `max`
-- pattern which the module universe `u + 1` below does not match syntactically; the abelian
-- structure used is the one from the explicit sheafification instances.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.ChaoticComparison

universe u m

namespace ModuleCat

/-- **The quotient case of the five lemma for short exact sequences of modules.**  A morphism of
short exact sequences of modules which is an isomorphism on the first two terms is one on the
third. -/
theorem isIso_τ₃_of_shortExact {R : Type*} [Ring R] {S₁ S₂ : ShortComplex (ModuleCat.{m} R)}
    (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [IsIso φ.τ₁] [IsIso φ.τ₂] :
    IsIso φ.τ₃ := by
  have hex₂ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₂).1 h₂.exact
  have hb₂ := ConcreteCategory.bijective_of_isIso φ.τ₂
  have c₁₂ : ∀ x, φ.τ₂ (S₁.f x) = S₂.f (φ.τ₁ x) := fun x => by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.comm₁₂]
  have c₂₃ : ∀ x, φ.τ₃ (S₁.g x) = S₂.g (φ.τ₂ x) := fun x => by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.comm₂₃]
  refine (ConcreteCategory.isIso_iff_bijective _).2
    ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := h₁.moduleCat_surjective_g z
    obtain ⟨a, ha⟩ := (hex₂ (φ.τ₂ w)).1 (by rw [← c₂₃, hz])
    obtain ⟨a', rfl⟩ := (ConcreteCategory.bijective_of_isIso φ.τ₁).2 a
    obtain rfl : w = S₁.f a' := hb₂.1 (by rw [c₁₂, ha])
    exact congrArg (fun k => (ConcreteCategory.hom k) a') S₁.zero
  · obtain ⟨x, rfl⟩ := h₂.moduleCat_surjective_g y
    obtain ⟨x', rfl⟩ := hb₂.2 x
    exact ⟨S₁.g x', c₂₃ x'⟩

end ModuleCat

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The restriction map of global functions along a morphism of objects of `S_étale` with affine
underlying schemes is flat: the morphism is étale. -/
theorem flat_commStructurePresheaf_map {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T')) (g : T ⟶ T') :
    ((commStructurePresheaf B S hS).map g.op).hom.Flat := by
  have h := flat_affineChartRings_map B S hS
    ((SmallAffineEtale.inclusion B S hS).preimage
      (X := (⟨T, hT⟩ : SmallAffineEtale B S hS)) (Y := ⟨T', hT'⟩) g)
  change ((commStructurePresheaf B S hS).map ((SmallAffineEtale.inclusion B S hS).map
    ((SmallAffineEtale.inclusion B S hS).preimage
      (X := (⟨T, hT⟩ : SmallAffineEtale B S hS)) (Y := ⟨T', hT'⟩) g)).op).hom.Flat at h
  rwa [Functor.map_preimage] at h

/-- **The base-change comparison of a kernel.**  For a morphism `φ : 𝒢 ⟶ 𝒢'` of sheaves of
modules on `S_étale`, with sections in any universe containing `u`, and a morphism `g : T ⟶ T'`
of objects with affine underlying schemes, the comparison
`Γ(T) ⊗_{Γ(T')} (ker φ)(T') ⟶ (ker φ)(T)` is an isomorphism as soon as those of `𝒢` and `𝒢'`
are.  It is the component at the kernel of a natural transformation between two functors which
preserve finite limits, `Γ(T)` being flat over `Γ(T')`. -/
theorem isIso_restrictionBaseChange_kernel
    {G G' : SheafOfModules.{max m u} (structureSheaf B S hS)} (φ : G ⟶ G')
    {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T')) (g : T ⟶ T')
    (hG : IsIso (restrictionBaseChange.{u + 1, u, u, max m u}
      (R := commStructurePresheaf B S hS) G.val g.op))
    (hG' : IsIso (restrictionBaseChange.{u + 1, u, u, max m u}
      (R := commStructurePresheaf B S hS) G'.val g.op)) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m u}
      (R := commStructurePresheaf B S hS) (kernel φ).val g.op) := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max m u}
      ((commStructurePresheaf B S hS).map g.op).hom) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, max m u} _
      (flat_commStructurePresheaf_map B S hS hT hT' g)
  have h₁ : PreservesLimitsOfShape WalkingParallelPair
      (SheafOfModules.forget.{max m u} (structureSheaf B S hS)) := inferInstance
  have h₂ : ∀ X, PreservesLimitsOfShape WalkingParallelPair
      (PresheafOfModules.evaluation.{max m u}
        (commStructurePresheaf B S hS ⋙ forget₂ CommRingCat RingCat) X) := fun _ => inferInstance
  have h₃ : PreservesLimitsOfShape WalkingParallelPair
      (ModuleCat.extendScalars.{u, u, max m u}
        ((commStructurePresheaf B S hS).map g.op).hom) := inferInstance
  let η := Functor.whiskerLeft (SheafOfModules.forget.{max m u} (structureSheaf B S hS))
    (restrictionBaseChangeNatTrans.{u + 1, u, u, max m u} (commStructurePresheaf B S hS) g.op)
  have hΦ := @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
    (SheafOfModules.forget.{max m u} (structureSheaf B S hS)) _ h₁
    (@comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ (h₂ (op T')) h₃)
  have hΨ := @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
    (SheafOfModules.forget.{max m u} (structureSheaf B S hS)) _ h₁ (h₂ (op T))
  exact @NatTrans.isIso_app_limit _ _ _ _ _ _ _ _ η (parallelPair φ 0) _ hΦ hΨ
    (by rintro (_ | _) <;> assumption)

/-- **The kernel of a morphism of quasi-coherent modules on `S_étale` is quasi-coherent**, with
sections in `Type (u + 1)`.  Both modules are cartesian between affine objects, by Descent,
Proposition 03DX (2), hence so is the kernel, by
`AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_kernel`, and a cartesian module is
quasi-coherent, by the converse half of Descent, Proposition 03DX (2). -/
theorem isQuasicoherentOnSite_kernel_succ
    {G G' : SheafOfModules.{u + 1} (structureSheaf B S hS)} (φ : G ⟶ G')
    (hG : G.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite) :
    (kernel φ).IsQuasicoherentOnSite := by
  rw [isQuasicoherentOnSite_iff_bijective_restrictionBaseChange_succ] at hG hG' ⊢
  intro T T' g hT hT'
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_restrictionBaseChange_kernel.{u, u + 1} B S hS φ hT hT' g
      ((ConcreteCategory.isIso_iff_bijective _).2 (hG g hT hT'))
      ((ConcreteCategory.isIso_iff_bijective _).2 (hG' g hT hT')))

/-- **Quasi-coherence on `S_étale` is closed under kernels**, with sections in
`Type (u + 1)`. -/
theorem isClosedUnderKernels_isQuasicoherentOnSite_succ :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (structureSheaf B S hS)).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      (isQuasicoherentOnSite_kernel_succ B S hS f hM hN)

/-- The restriction of the structure sheaf of `S_étale` to the affine objects is the sheaf of
global functions of the underlying affine schemes. -/
theorem ringRestriction_structureSheaf_eq :
    ((SmallAffineEtale.inclusion B S hS).sheafPushforwardContinuous RingCat.{u}
        (SmallAffineEtale.topology B S hS) (topology B S hS)).obj (structureSheaf B S hS) =
      Stacks.AffineSiteBaseChange.ringsSheaf (SmallAffineEtale.isFlatCofinal B S hS) :=
  rfl

/-- **The pushforward of sheaves of modules along a continuous functor preserves limits of small
shape**, with the universes of the module sections and of the coefficient rings independent:
limits of sheaves of modules are computed on sections, and pushforward is precomposition followed
by restriction of scalars. -/
theorem preservesLimit_sheafOfModules_pushforward.{u₁, v₁, u₂, v₂}
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [Functor.IsContinuous F J K] {R₁ : Sheaf J RingCat.{u}} {R₂ : Sheaf K RingCat.{u}}
    (φ : R₁ ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R₂)
    {Kc : Type} [SmallCategory Kc] (G : Kc ⥤ SheafOfModules.{m} R₂) :
    PreservesLimit G (SheafOfModules.pushforward.{m} φ) := by
  have h₁ : PreservesLimit (G ⋙ SheafOfModules.forget R₂)
      (PresheafOfModules.pushforward.{m} φ.hom) := ⟨fun {c} hc => ⟨by
      refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X => ?_
      have : PreservesLimit (G ⋙ SheafOfModules.forget R₂)
          (PresheafOfModules.pushforward.{m} φ.hom ⋙ PresheafOfModules.evaluation R₁.obj X) := by
        change PreservesLimit _ (PresheafOfModules.evaluation R₂.obj (F.op.obj X) ⋙
          ModuleCat.restrictScalars (RingCat.Hom.hom (φ.hom.app X)))
        infer_instance
      exact isLimitOfPreserves (PresheafOfModules.pushforward.{m} φ.hom ⋙
        PresheafOfModules.evaluation R₁.obj X) hc⟩⟩
  have : PreservesLimit G (SheafOfModules.pushforward.{m} φ ⋙ SheafOfModules.forget R₁) := by
    change PreservesLimit G (SheafOfModules.forget R₂ ⋙ PresheafOfModules.pushforward.{m} φ.hom)
    exact comp_preservesLimit _ _
  exact preservesLimit_of_reflects_of_preserves _ (SheafOfModules.forget R₁)

/-- Restriction of sheaves of modules on `S_étale` to the small affine étale site, over the
sheaf of global functions of the underlying affine schemes. -/
noncomputable abbrev sheafAffineRestrictionSucc :
    SheafOfModules.{u + 1} (structureSheaf B S hS) ⥤
      SheafOfModules.{u + 1}
        (Stacks.AffineSiteBaseChange.ringsSheaf (SmallAffineEtale.isFlatCofinal B S hS)) :=
  haveI : (SmallAffineEtale.inclusion B S hS).IsContinuous
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    have := (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
    inferInstance
  SheafOfModules.pushforward.{u + 1} (F := SmallAffineEtale.inclusion B S hS)
    (𝟙 (Stacks.AffineSiteBaseChange.ringsSheaf (SmallAffineEtale.isFlatCofinal B S hS)))

/-- The restriction to the small affine étale site of a sheaf of modules on `S_étale` which is
cartesian between affine objects is cartesian. -/
theorem isCartesianPresheaf_affineRestriction (G : SheafOfModules.{u + 1} (structureSheaf B S hS))
    (hG : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
          G.val g.op)) :
    IsCartesianPresheaf ((sheafAffineRestrictionSucc B S hS).obj G).val := by
  refine (isCartesianPresheaf_iff_isIso_restrictionBaseChange.{u + 1, u + 1, u, u}
    (R := affineChartRings B S hS) ((sheafAffineRestrictionSucc B S hS).obj G).val).2 ?_
  intro X Y f
  exact hG ((SmallAffineEtale.inclusion B S hS).map f.unop) Y.unop.2 X.unop.2

attribute [local instance] HasDerivedCategory.standard
  Stacks.SheafOfModulesEvaluation.evaluation_additive

/-- **Descent, Proposition 03DW, in the form used for the cokernel and extension clauses, at
section universe `u + 1`.**  An epimorphism `q : 𝒫 ⟶ 𝒬` of sheaves of modules on `S_étale` whose
kernel is cartesian between affine objects is surjective on the sections over every object with
affine underlying scheme.

Restricted to the small affine étale site, the short exact sequence `0 → ker q → 𝒫 → 𝒬 → 0`
stays short exact, and its first term is cartesian, hence has no first cohomology over an affine
object (`AlgebraicGeometry.SmallAffineEtale.isZero_rightDerived_evaluation_of_isCartesian`); the
long exact cohomology sequence then makes `𝒫(W) ⟶ 𝒬(W)` surjective. -/
theorem surjective_val_app_of_epi_of_cartesian_kernel
    {P Q : SheafOfModules.{u + 1} (structureSheaf B S hS)} (q : P ⟶ Q) [Epi q]
    (hK : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
          (kernel q).val g.op))
    {W : SmallEtale B S hS} (hW : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj W)) :
    Function.Surjective (q.val.app (op W)) := by
  let R' := Stacks.AffineSiteBaseChange.ringsSheaf (SmallAffineEtale.isFlatCofinal B S hS)
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
  let := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
    u} (topology B S hS)
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1}
    (SmallAffineEtale.topology B S hS)
  let := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
    u} (SmallAffineEtale.topology B S hS)
  let := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, 0} R'
  have hcc : (SmallAffineEtale.inclusion B S hS).IsCocontinuous
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).1
  have hcont : (SmallAffineEtale.inclusion B S hS).IsContinuous
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    have := (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
    inferInstance
  let res := sheafAffineRestrictionSucc B S hS
  let W' : SmallAffineEtale B S hS := ⟨W, hW⟩
  -- the restricted sequence is short exact
  have hepi : Epi (res.map q) := by
    refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ?_
    have h₀ := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi q
    exact Presheaf.isLocallySurjective_whisker (SmallAffineEtale.topology B S hS)
      (topology B S hS) (SmallAffineEtale.inclusion B S hS)
      ((PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).map q.val)
  have : res.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hpres : PreservesLimit (parallelPair q 0) res :=
    preservesLimit_sheafOfModules_pushforward _ _
  let T : ShortComplex (SheafOfModules.{u + 1} R') :=
    ShortComplex.mk (res.map (kernel.ι q)) (res.map q)
      (by rw [← res.map_comp, kernel.condition, res.map_zero])
  have hlim : IsLimit (KernelFork.ofι (res.map (kernel.ι q)) T.zero) :=
    (isLimitMapConeForkEquiv' res (kernel.condition q)) (isLimitOfPreserves res (kernelIsKernel q))
  have hT : T.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel T hlim) (Fork.IsLimit.mono hlim) hepi
  -- its first term is cartesian
  have h₁ := SmallAffineEtale.isZero_rightDerived_evaluation_of_isCartesian B S hS
    (res.obj (kernel q)) (isCartesianPresheaf_affineRestriction B S hS (kernel q) hK) W' 1 one_pos
  have := Stacks.SheafOfModulesEvaluation.evaluation_additive.{u + 1, u, u + 1, u} R' (op W')
  have : PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1} R' (op W')) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits.{u + 1} (R := R') (op W')
  exact (ModuleCat.epi_iff_surjective _).1
    (Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one
      (SheafOfModules.evaluation R' (op W')) hT h₁)

/-- On the sections over an object with affine underlying scheme, a short exact sequence of
sheaves of modules on `S_étale`, with sections in `Type (u + 1)`, whose first term is cartesian
between affine objects stays short exact. -/
theorem shortExact_map_evaluation_of_cartesian
    {Sc : ShortComplex (SheafOfModules.{u + 1} (structureSheaf B S hS))} (hSc : Sc.ShortExact)
    (hX₁ : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
          Sc.X₁.val g.op))
    {W : SmallEtale B S hS} (hW : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj W)) :
    (Sc.map (SheafOfModules.evaluation.{u + 1} (structureSheaf B S hS) (op W))).ShortExact := by
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
  let := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
    u} (topology B S hS)
  have := hSc.epi_g
  let e : Sc.X₁ ≅ kernel Sc.g := IsLimit.conePointUniqueUpToIso hSc.fIsKernel (limit.isLimit _)
  have hK : ∀ {T₀ T₀' : SmallEtale B S hS} (g : T₀ ⟶ T₀'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T₀) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T₀') →
        IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
          (kernel Sc.g).val g.op) := fun g h h' =>
    @isIso_restrictionBaseChange_of_iso.{u + 1, u, u, u + 1} _ _ _ _ _
      ((SheafOfModules.forget _).mapIso e) _ _ g.op (hX₁ g h h')
  exact ModuleCat.shortComplex_shortExact _
    (SheafOfModules.exact_val_app_of_shortExact hSc (op W))
    (SheafOfModules.injective_f_val_app_of_shortExact hSc (op W))
    (surjective_val_app_of_epi_of_cartesian_kernel B S hS Sc.g hK hW)

/-- Extension of scalars along the restriction map of global functions between objects with
affine underlying schemes is a left adjoint which preserves finite limits, the restriction map
being flat. -/
theorem extendScalars_isLeftAdjoint_preservesFiniteLimits {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T')) (g : T ⟶ T') :
    (ModuleCat.extendScalars.{u, u, u + 1}
        ((commStructurePresheaf B S hS).map g.op).hom).PreservesZeroMorphisms ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1}
        ((commStructurePresheaf B S hS).map g.op).hom) := by
  refine ⟨?_, extendScalars_preservesFiniteLimits_of_flat'.{u, u + 1} _
    (flat_commStructurePresheaf_map B S hS hT hT' g)⟩
  have := (ModuleCat.extendRestrictScalarsAdj.{u + 1}
    ((commStructurePresheaf B S hS).map g.op).hom).isLeftAdjoint
  exact Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- **The base-change comparison along a short exact sequence whose first term is cartesian.**
For a short exact sequence `0 → 𝒢₁ → 𝒢₂ → 𝒢₃ → 0` of sheaves of modules on `S_étale`, with
sections in `Type (u + 1)`, whose first term is cartesian between affine objects, and a morphism
`g : T ⟶ T'` of objects with affine underlying schemes, the comparison for `𝒢₂` along `g` is an
isomorphism exactly when the comparison for `𝒢₃` is.

Over `T` and `T'` the sequence of sections is short exact, by Descent, Proposition 03DW in the
form `AlgebraicGeometry.SmallEtale.surjective_val_app_of_epi_of_cartesian_kernel`; extension of
scalars along the flat map `Γ(T') ⟶ Γ(T)` keeps the second one short exact; and the comparisons
form a morphism between the two short exact sequences, to which the five lemma applies. -/
theorem isIso_restrictionBaseChange_X₂_iff_X₃_of_shortExact
    {Sc : ShortComplex (SheafOfModules.{u + 1} (structureSheaf B S hS))} (hSc : Sc.ShortExact)
    (hX₁ : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
          Sc.X₁.val g.op))
    {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T')) (g : T ⟶ T') :
    IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
        Sc.X₂.val g.op) ↔
      IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
        Sc.X₃.val g.op) := by
  have hE := extendScalars_isLeftAdjoint_preservesFiniteLimits B S hS hT hT' g
  let := hE.1
  let := hE.2
  have : PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, u + 1} ((commStructurePresheaf B S hS).map g.op).hom) :=
    have := (ModuleCat.extendRestrictScalarsAdj.{u + 1}
      ((commStructurePresheaf B S hS).map g.op).hom).leftAdjoint_preservesColimits.{0, 0}
    PreservesColimitsOfSize.preservesFiniteColimits _
  let ev (T₀ : SmallEtale B S hS) : SheafOfModules.{u + 1} (structureSheaf B S hS) ⥤
      ModuleCat.{u + 1} ((commStructurePresheaf B S hS).obj (op T₀)) :=
    SheafOfModules.forget.{u + 1} (structureSheaf B S hS) ⋙
      PresheafOfModules.evaluation (commStructurePresheaf B S hS ⋙ forget₂ CommRingCat RingCat)
        (op T₀)
  let E := ModuleCat.extendScalars.{u, u, u + 1} (R := (commStructurePresheaf B S hS).obj (op T'))
    (S := (commStructurePresheaf B S hS).obj (op T)) ((commStructurePresheaf B S hS).map g.op).hom
  have : ∀ T₀, (ev T₀).PreservesZeroMorphisms := fun _ => ⟨fun _ _ => rfl⟩
  have h₁ : (Sc.map (ev T' ⋙ E)).ShortExact :=
    ShortComplex.ShortExact.map_of_exact (S := Sc.map (ev T'))
      (shortExact_map_evaluation_of_cartesian B S hS hSc hX₁ hT') E
  have h₂ : (Sc.map (ev T)).ShortExact := shortExact_map_evaluation_of_cartesian B S hS hSc hX₁ hT
  let η : ev T' ⋙ E ⟶ ev T :=
    Functor.whiskerLeft (SheafOfModules.forget.{u + 1} (structureSheaf B S hS))
    (restrictionBaseChangeNatTrans.{u + 1, u, u, u + 1} (commStructurePresheaf B S hS) g.op)
  have : (ev T' ⋙ E).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp (ev T') E
  let φ := Sc.mapNatTrans η
  have i₁ : IsIso φ.τ₁ := hX₁ g hT hT'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsIso φ.τ₂ := h
    exact ModuleCat.isIso_τ₃_of_shortExact φ h₁ h₂
  · have : IsIso φ.τ₃ := h
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂

/-- A sheaf of modules on `S_étale` with sections in `Type (u + 1)` which is quasi-coherent has
invertible base-change comparisons between affine objects. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite_succ
    {G : SheafOfModules.{u + 1} (structureSheaf B S hS)} (hG : G.IsQuasicoherentOnSite)
    {T T' : SmallEtale B S hS} (g : T ⟶ T')
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T')) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
      G.val g.op) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ((isQuasicoherentOnSite_iff_bijective_restrictionBaseChange_succ B S hS G).1 hG g hT hT')

/-- A sheaf of modules on `S_étale` with sections in `Type (u + 1)` whose base-change
comparisons between affine objects are invertible is quasi-coherent. -/
theorem isQuasicoherentOnSite_of_isIso_restrictionBaseChange_succ
    {G : SheafOfModules.{u + 1} (structureSheaf B S hS)}
    (hG : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') →
        IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
          G.val g.op)) :
    G.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_bijective_restrictionBaseChange_succ B S hS G).2
    fun g hT hT' => (ConcreteCategory.isIso_iff_bijective _).1 (hG g hT hT')

/-- The base-change comparisons of the two other terms of a short exact sequence with
quasi-coherent first term are invertible simultaneously. -/
private theorem isIso_restrictionBaseChange_X₂_iff_X₃_of_isQuasicoherentOnSite
    {Sc : ShortComplex (SheafOfModules.{u + 1} (structureSheaf B S hS))} (hSc : Sc.ShortExact)
    (h₁ : Sc.X₁.IsQuasicoherentOnSite) {T T' : SmallEtale B S hS} (g : T ⟶ T')
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T')) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
        Sc.X₂.val g.op) ↔
      IsIso (restrictionBaseChange.{u + 1, u, u, u + 1} (R := commStructurePresheaf B S hS)
        Sc.X₃.val g.op) :=
  isIso_restrictionBaseChange_X₂_iff_X₃_of_shortExact B S hS hSc
    (fun g hT hT' => isIso_restrictionBaseChange_of_isQuasicoherentOnSite_succ B S hS h₁ g hT hT')
    hT hT' g

/-- **Stacks 06VE (10) at `τ = étale`, at section universe `u + 1`: an extension of two
quasi-coherent modules on `S_étale` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_X₂_of_shortExact_succ
    {Sc : ShortComplex (SheafOfModules.{u + 1} (structureSheaf B S hS))} (hSc : Sc.ShortExact)
    (h₁ : Sc.X₁.IsQuasicoherentOnSite) (h₃ : Sc.X₃.IsQuasicoherentOnSite) :
    Sc.X₂.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isIso_restrictionBaseChange_succ B S hS fun g hT hT' =>
    (isIso_restrictionBaseChange_X₂_iff_X₃_of_isQuasicoherentOnSite B S hS hSc h₁ g hT hT').2
      (isIso_restrictionBaseChange_of_isQuasicoherentOnSite_succ B S hS h₃ g hT hT')

/-- **The quotient in a short exact sequence of modules on `S_étale` whose two other terms are
quasi-coherent is quasi-coherent**, at section universe `u + 1`. -/
theorem isQuasicoherentOnSite_X₃_of_shortExact_succ
    {Sc : ShortComplex (SheafOfModules.{u + 1} (structureSheaf B S hS))} (hSc : Sc.ShortExact)
    (h₁ : Sc.X₁.IsQuasicoherentOnSite) (h₂ : Sc.X₂.IsQuasicoherentOnSite) :
    Sc.X₃.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isIso_restrictionBaseChange_succ B S hS fun g hT hT' =>
    (isIso_restrictionBaseChange_X₂_iff_X₃_of_isQuasicoherentOnSite B S hS hSc h₁ g hT hT').1
      (isIso_restrictionBaseChange_of_isQuasicoherentOnSite_succ B S hS h₂ g hT hT')

/-- **The cokernel of a morphism of quasi-coherent modules on `S_étale` is quasi-coherent**, at
section universe `u + 1`.  The coimage of `f : 𝒢 ⟶ 𝒢'` is the quotient of `𝒢` by the kernel,
which is quasi-coherent; the coimage is the image; and the cokernel is the quotient of `𝒢'` by
the image. -/
theorem isQuasicoherentOnSite_cokernel_succ
    {G G' : SheafOfModules.{u + 1} (structureSheaf B S hS)} (f : G ⟶ G')
    (hG : G.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite) :
    (cokernel f).IsQuasicoherentOnSite := by
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
  let := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
    u} (topology B S hS)
  have hcoim : (cokernel (kernel.ι f)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_X₃_of_shortExact_succ B S hS (Abelian.shortExact_coimage f)
      (isQuasicoherentOnSite_kernel_succ B S hS f hG hG') hG
  have him : (kernel (cokernel.π f)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (Abelian.coimageIsoImage f) hcoim
  exact isQuasicoherentOnSite_X₃_of_shortExact_succ B S hS (Abelian.shortExact_image f) him hG'

/-- **Quasi-coherence on `S_étale` is closed under cokernels**, with sections in
`Type (u + 1)`. -/
theorem isClosedUnderCokernels_isQuasicoherentOnSite_succ :
    letI := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
    letI := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
      u} (topology B S hS)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (structureSheaf B S hS)).IsClosedUnderCokernels := by
  let := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} (topology B S hS)
  let := AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1,
    u} (topology B S hS)
  refine ⟨?_⟩
  rintro _ ⟨f, k, hk, hM, hN⟩
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
    (isQuasicoherentOnSite_cokernel_succ B S hS f hM hN)

end AlgebraicGeometry.SmallEtale

end

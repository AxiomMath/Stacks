module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules

/-!
# The coherator of the presheaf-level flat base change modules, over chart data

This file is **not** a formalization of **Stacks 0779**. That lemma, for the coherator
`Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳)` of **Stacks 0778** and the sheaf-level flat base change
property of **Stacks 0762**, is proved unconditionally, all three parts, in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/CoheratorCanonical.lean`
(in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`:
`isZero_coherator_obj_iff_isParasitic`,
`isParasitic_kernel_and_cokernel_coheratorAdjunction_counit`,
`preservesLimitsOfSize_lqcohSheafFbc_ι_comp_coherator`,
`preservesColimitsOfShape_lqcohSheafFbc_ι_comp_coherator` and
`preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator`).

What is here concerns a different functor, `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`
of `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Coherator.lean`: the right adjoint of
`QCoh(𝒪_𝒳) → locallyQuasicoherentFlatBaseChangeModules`, the category of étale modules with the
*presheaf-level* flat base change property
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`.
That property is strictly stronger than **Stacks 0762**, so this category is smaller than
`LQCoh^fbc(𝒪_𝒳)`, and the hypothesis `hinc` that every quasi-coherent module lies in it fails
already for `𝒳 = ℙ¹` and `𝒪(-1)` (see
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafFlatBaseChangeProperty.lean`). The
results below are therefore vacuous for such `𝒳`.

They are formal consequences of the adjunction together with hypotheses on an auxiliary functor
`r : locallyQuasicoherentFlatBaseChangeModules ⥤ 𝒜`, modelled on the restriction to a chart:

* `hrpar` — `r 𝓕 = 0` if and only if `𝓕` is parasitic (at `SiteKind.etale`). Given `hrcounit`
  and `hreq` this is *equivalent* to the conclusion of
  `AlgebraicGeometry.Stack.isZero_flatBaseChangeQuasicoherator_iff_isParasitic`, so that result
  only transports `hrpar`.
* `hrcounit` — the counit `Q 𝓕 ⟶ 𝓕` becomes an isomorphism under `r`.
* `hreq` — `i ⋙ r` is an equivalence.
* `hrcolim`, `hrfincolim` — `r` commutes with colimits, respectively finite colimits.

Only the preservation of limits is free of the `r`-hypotheses; it still depends on `hinc`.

## Main results

* `AlgebraicGeometry.Stack.isZero_flatBaseChangeQuasicoherator_iff_isParasitic`: the kernel of
  `flatBaseChangeQuasicoherator`, transported from `hrpar` along the counit.
* `AlgebraicGeometry.Stack.isParasitic_of_isLimit_kernelFork_flatBaseChangeQuasicoherator` and
  `AlgebraicGeometry.Stack.isParasitic_of_isColimit_cokernelCofork_flatBaseChangeQuasicoherator`:
  the kernel and the cokernel of its counit, under the same hypotheses.
* `AlgebraicGeometry.Stack.exact_flatBaseChangeQuasicoherator`,
  `AlgebraicGeometry.Stack.preservesLimitsOfSize_flatBaseChangeQuasicoherator` and
  `AlgebraicGeometry.Stack.preservesColimitsOfSize_flatBaseChangeQuasicoherator`: its exactness
  and its commuting with limits and colimits, the colimit halves under `hrfincolim`, `hrcolim`.

## Implementation notes

The kernel and the cokernel of the counit are taken as an arbitrary limit kernel fork and an
arbitrary colimit cokernel cofork, so that nothing is assumed about
`locallyQuasicoherentFlatBaseChangeModules` having kernels or cokernels.

Exactness is delivered as the pair `CategoryTheory.Limits.PreservesFiniteLimits` and
`CategoryTheory.Limits.PreservesFiniteColimits`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe vA uA vJ uJ vC uC vD uD u w

namespace AlgebraicGeometry.Stack

section Coreflection

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {A : Type uA} [Category.{vA} A]

/-- An equivalence both preserves and reflects zero objects: reflection is
`CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero`, and preservation is the same
statement for the inverse, read through the unit isomorphism. -/
private theorem isZero_obj_iff_of_isEquivalence (F : C ⥤ A) [F.IsEquivalence] (X : C) :
    IsZero (F.obj X) ↔ IsZero X := by
  refine ⟨IsZero.of_full_of_faithful_of_isZero F X, fun hX => ?_⟩
  exact IsZero.of_full_of_faithful_of_isZero F.inv (F.obj X)
    (hX.of_iso (F.asEquivalence.unitIso.app X).symm)

/-- The counit of the adjunction, whiskered by `r`, is a natural isomorphism `Q ⋙ i ⋙ r ≅ r`
as soon as each of its components is invertible. -/
private def whiskerCounitIso {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) (r : D ⥤ A)
    (hrcounit : ∀ F : D, IsIso (r.map (adj.counit.app F))) : Q ⋙ i ⋙ r ≅ r :=
  have : ∀ F : D, IsIso ((Functor.whiskerRight adj.counit r).app F) := hrcounit
  have : IsIso (Functor.whiskerRight adj.counit r) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerRight adj.counit r) ≪≫ Functor.leftUnitor r

/-- `Q` is `r` followed by the inverse of the equivalence `i ⋙ r`: whiskering
`AlgebraicGeometry.Stack.whiskerCounitIso` with that inverse and using the unit isomorphism of
the equivalence. -/
private def rightAdjointIsoCompInv {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) (r : D ⥤ A)
    (hrcounit : ∀ F : D, IsIso (r.map (adj.counit.app F))) [(i ⋙ r).IsEquivalence] :
    Q ≅ r ⋙ (i ⋙ r).inv :=
  (Functor.rightUnitor Q).symm ≪≫ Functor.isoWhiskerLeft Q (i ⋙ r).asEquivalence.unitIso ≪≫
    Functor.isoWhiskerRight (whiskerCounitIso adj r hrcounit) (i ⋙ r).inv

/-- An object is in the kernel of `Q` exactly when it is killed by `r`: the counit identifies
`r (i (Q F))` with `r F`, and `i ⋙ r` reflects zero objects. -/
private theorem isZero_obj_iff_isZero_map_obj {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q)
    (r : D ⥤ A) (hrcounit : ∀ F : D, IsIso (r.map (adj.counit.app F)))
    [(i ⋙ r).IsEquivalence] (F : D) : IsZero (Q.obj F) ↔ IsZero (r.obj F) := by
  rw [← isZero_obj_iff_of_isEquivalence (i ⋙ r) (Q.obj F)]
  exact Iso.isZero_iff (@asIso _ _ _ _ _ (hrcounit F))

end Coreflection

section Counit

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) [i.Full] [i.Faithful]

omit [i.Full] [i.Faithful] in
include adj in
/-- A right adjoint preserves zero morphisms, so kernel forks and cokernel coforks can be
transported along `Q`. -/
private theorem preservesZeroMorphisms_rightAdjoint : Q.PreservesZeroMorphisms :=
  have : Q.IsRightAdjoint := adj.isRightAdjoint
  inferInstance

include adj in
/-- The kernel of the adjunction map `Q F ⟶ F` is killed by `Q`.  The left adjoint is fully
faithful, so `Q` applied to the counit is invertible, in particular a monomorphism; and `Q`
preserves the kernel fork, being a right adjoint. -/
private theorem isZero_obj_pt_of_isLimit_kernelFork {F : D}
    {c : KernelFork (adj.counit.app F)} (hc : IsLimit c) : IsZero (Q.obj c.pt) :=
  have := preservesZeroMorphisms_rightAdjoint adj
  have : PreservesLimitsOfSize.{0, 0} Q := adj.rightAdjoint_preservesLimits
  KernelFork.IsLimit.isZero_of_mono (KernelFork.mapIsLimit c hc Q)

include adj in
/-- The cokernel of the adjunction map `Q F ⟶ F` is killed by `Q`, once `Q` is known to be
right exact: `Q` applied to the counit is invertible, in particular an epimorphism. -/
private theorem isZero_obj_pt_of_isColimit_cokernelCofork [PreservesFiniteColimits Q] {F : D}
    {c : CokernelCofork (adj.counit.app F)} (hc : IsColimit c) : IsZero (Q.obj c.pt) :=
  have := preservesZeroMorphisms_rightAdjoint adj
  CokernelCofork.IsColimit.isZero_of_epi (CokernelCofork.mapIsColimit c hc Q)

end Counit

section Stacks

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)
  [EssentiallySmall.{u} 𝒳.val.val.obj]
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .etale).obj F).val)
  (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
  (hpres : PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc))
  (hls : LocallySmall.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hlsD : LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))
  (hwp : WellPowered.{u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)ᵒᵖ)
  (hsep : HasSeparator (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids))

/-- `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` commutes with all limits, being a
right adjoint. It depends on the hypothesis `hinc`, which fails for `ℙ¹` (see the module
documentation); **Stacks 0779** (3) is
`AlgebraicGeometry.Stack.AlgebraicStacks.preservesLimitsOfSize_lqcohSheafFbc_ι_comp_coherator`. -/
theorem preservesLimitsOfSize_flatBaseChangeQuasicoherator :
    PreservesLimitsOfSize.{vJ, uJ}
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) :=
  (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp
    hsep).rightAdjoint_preservesLimits

/-- `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` is left exact: a special case of
`AlgebraicGeometry.Stack.preservesLimitsOfSize_flatBaseChangeQuasicoherator`. -/
theorem preservesFiniteLimits_flatBaseChangeQuasicoherator :
    PreservesFiniteLimits
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) :=
  have : PreservesLimitsOfSize.{0, 0}
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) :=
    preservesLimitsOfSize_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls
      hlsD hwp hsep
  inferInstance

variable {𝒜 : Type uA} [Category.{vA} 𝒜]
  (r : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids ⥤ 𝒜)
  (hrpar : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsZero (r.obj F) ↔ IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val)
  (hrcounit : ∀ F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids,
    IsIso (r.map ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)))
  (hreq : (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc ⋙ r).IsEquivalence)

include hinc hrpar hrcounit hreq in
/-- Over the hypotheses `hinc`, `hrpar`, `hrcounit` and `hreq`, an object of
`locallyQuasicoherentFlatBaseChangeModules` is killed by
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` exactly when it is parasitic. The counit
identifies `r (i (Q 𝓕))` with `r 𝓕` and `i ⋙ r` reflects zero objects, so the statement is
`hrpar` transported; it is not **Stacks 0779** (1), which is
`AlgebraicGeometry.Stack.AlgebraicStacks.isZero_coherator_obj_iff_isParasitic`. -/
theorem isZero_flatBaseChangeQuasicoherator_iff_isParasitic
    (F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    IsZero ((flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).obj F) ↔
      IsParasitic.{u, w, u} B S hS 𝒳 .etale F.obj.val := by
  have := hreq
  exact (isZero_obj_iff_isZero_map_obj (flatBaseChangeQuasicoheratorAdjunction B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) r
    hrcounit F).trans (hrpar F)

include hinc hrcounit hreq in
/-- `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` commutes with the colimits `r`
commutes with, through the identification `Q ≅ r ⋙ (i ⋙ r)⁻¹` which the counit and `hreq`
supply. It is not **Stacks 0779** (3), which is
`AlgebraicStacks.preservesColimitsOfShape_lqcohSheafFbc_ι_comp_coherator`. -/
theorem preservesColimitsOfSize_flatBaseChangeQuasicoherator
    (hrcolim : PreservesColimitsOfSize.{vJ, uJ} r) :
    PreservesColimitsOfSize.{vJ, uJ}
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) := by
  have := hreq
  have := hrcolim
  exact preservesColimits_of_natIso (rightAdjointIsoCompInv
    (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) r hrcounit).symm

include hinc hrcounit hreq in
/-- `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` is right exact when `r` is, through
the identification `Q ≅ r ⋙ (i ⋙ r)⁻¹`. -/
theorem preservesFiniteColimits_flatBaseChangeQuasicoherator
    (hrfincolim : PreservesFiniteColimits r) :
    PreservesFiniteColimits
      (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        hinc hclosed hpres hls hlsD hwp hsep) := by
  have := hreq
  have := hrfincolim
  have := comp_preservesFiniteColimits r
    (quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc ⋙ r).inv
  exact preservesFiniteColimits_of_natIso (rightAdjointIsoCompInv
    (flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) r hrcounit).symm

include hinc hrcounit hreq in
/-- `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` preserves finite limits and, when
`r` is right exact, finite colimits. It is not **Stacks 0779** (3), which is
`AlgebraicStacks.preservesFiniteLimits_and_preservesFiniteColimits_lqcohSheafFbc_ι_comp_coherator`.
-/
theorem exact_flatBaseChangeQuasicoherator (hrfincolim : PreservesFiniteColimits r) :
    PreservesFiniteLimits
        (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          hinc hclosed hpres hls hlsD hwp hsep) ∧
      PreservesFiniteColimits
        (flatBaseChangeQuasicoherator B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          hinc hclosed hpres hls hlsD hwp hsep) :=
  ⟨preservesFiniteLimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls
      hlsD hwp hsep,
    preservesFiniteColimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed hpres hls
      hlsD hwp hsep r hrcounit hreq hrfincolim⟩

include hinc hrpar hrcounit hreq in
/-- Over the hypotheses of
`AlgebraicGeometry.Stack.isZero_flatBaseChangeQuasicoherator_iff_isParasitic`, a kernel of the
counit `Q 𝓕 ⟶ 𝓕` of `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` is parasitic: `Q`
kills it, `Q` of the counit being invertible and `Q` preserving the kernel fork. It is not
**Stacks 0779** (2), which is
`AlgebraicStacks.isParasitic_kernel_and_cokernel_coheratorAdjunction_counit`. -/
theorem isParasitic_of_isLimit_kernelFork_flatBaseChangeQuasicoherator
    {F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids}
    {c : KernelFork ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)}
    (hc : IsLimit c) : IsParasitic.{u, w, u} B S hS 𝒳 .etale c.pt.obj.val := by
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).full
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).faithful
  refine (isZero_flatBaseChangeQuasicoherator_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres
    hls hlsD hwp hsep r hrpar hrcounit hreq c.pt).1 ?_
  exact isZero_obj_pt_of_isLimit_kernelFork (flatBaseChangeQuasicoheratorAdjunction B E h S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep) hc

include hinc hrpar hrcounit hreq in
/-- Over the hypotheses of
`AlgebraicGeometry.Stack.isZero_flatBaseChangeQuasicoherator_iff_isParasitic` and `hrfincolim`,
a cokernel of the counit `Q 𝓕 ⟶ 𝓕` of `AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator` is
parasitic. It is not **Stacks 0779** (2), which is
`AlgebraicStacks.isParasitic_kernel_and_cokernel_coheratorAdjunction_counit`. -/
theorem isParasitic_of_isColimit_cokernelCofork_flatBaseChangeQuasicoherator
    (hrfincolim : PreservesFiniteColimits r)
    {F : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids}
    {c : CokernelCofork ((flatBaseChangeQuasicoheratorAdjunction B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp hsep).counit.app F)}
    (hc : IsColimit c) : IsParasitic.{u, w, u} B S hS 𝒳 .etale c.pt.obj.val := by
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).full
  have := (fullyFaithful_quasicoherentToFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids hinc).faithful
  have := preservesFiniteColimits_flatBaseChangeQuasicoherator B E h S hS 𝒳 hinc hclosed
    hpres hls hlsD hwp hsep r hrcounit hreq hrfincolim
  refine (isZero_flatBaseChangeQuasicoherator_iff_isParasitic B E h S hS 𝒳 hinc hclosed hpres
    hls hlsD hwp hsep r hrpar hrcounit hreq c.pt).1 ?_
  exact isZero_obj_pt_of_isColimit_cokernelCofork (flatBaseChangeQuasicoheratorAdjunction
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hinc hclosed hpres hls hlsD hwp
    hsep) hc

end Stacks

end AlgebraicGeometry.Stack

end

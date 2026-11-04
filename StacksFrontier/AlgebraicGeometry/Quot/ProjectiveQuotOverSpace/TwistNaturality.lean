/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistQuotients
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.SubobjectPullback
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Opposite
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.KernelTwistCounit
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImageEpiFibre

/-!
# Twisting quotients commutes with base change (Stacks 0DP7 as a statement about functors)

The identification `Subobject 𝒢 ≃ Subobject 𝒢(d)` of
`AlgebraicGeometry.ProjectiveQuotOverSpace.twistSubobjectEquiv` commutes with the base change of
subobjects along `ℙⁿ_{T'} ⟶ ℙⁿ_T`, the two base changes being read through an identification
`𝒢' ≅ g^*𝒢` and its twist followed by `(g^*𝒢)(d) ≅ g^*(𝒢(d))`
(`AlgebraicGeometry.ProjectiveQuot.twistPullbackIso`).  The proof reads every subobject involved
as the kernel subobject of a map: the twist of a kernel subobject is the kernel subobject of the
twisted map, the base change of the kernel subobject of an epimorphism is the kernel subobject of
its base change, and `twistPullbackIso` is natural.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistSubobjectEquiv_kernelSubobject`
* `AlgebraicGeometry.ProjectiveQuotOverSpace.subobjectPullback_kernelSubobject`
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistSubobjectEquiv_subobjectPullback`

## References

* [Stacks Project, Tag 0DP7](https://stacks.math.columbia.edu/tag/0DP7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {n : ℕ}

/-- The image of a kernel subobject under an equivalence is the kernel subobject of the image of
the map. -/
theorem transportEquiv_refl_kernelSubobject {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (E : C ≌ D) {X Y : C} (f : X ⟶ Y) :
    Subobject.transportEquiv E (Iso.refl _) (kernelSubobject f) =
      kernelSubobject (E.functor.map f) := by
  show Subobject.transportEquiv E (Iso.refl _) (Subobject.mk (kernel.ι f)) =
    Subobject.mk (kernel.ι (E.functor.map f))
  rw [Subobject.transportEquiv_mk]
  have hk := isLimitForkMapOfIsLimit' E.functor (kernel.condition f) (kernelIsKernel f)
  refine Subobject.mk_eq_mk_of_comm _ _
    (IsLimit.conePointUniqueUpToIso hk (limit.isLimit _)) ?_
  rw [Iso.refl_hom, Category.comp_id]
  exact IsLimit.conePointUniqueUpToIso_hom_comp hk (limit.isLimit _) WalkingParallelPair.zero

/-- **The twist of a kernel subobject is the kernel subobject of the twisted map.** -/
theorem twistSubobjectEquiv_kernelSubobject {T : Scheme.{u}} (d : ℤ)
    {G Q : (projectiveSpaceOver n T).Modules} (f : G ⟶ Q) :
    twistSubobjectEquiv d G (kernelSubobject f) = kernelSubobject (twistMap d f) := by
  rw [twistMap_eq_twistFunctor_map]
  exact transportEquiv_refl_kernelSubobject (twistFunctor n T d).asEquivalence f

/-- **The base change of the kernel subobject of an epimorphism is the kernel subobject of its
base change.** -/
theorem subobjectPullback_kernelSubobject {T' T : Scheme.{u}} (g : T' ⟶ T)
    {G Q : (projectiveSpaceOver n T).Modules} {G' : (projectiveSpaceOver n T').Modules}
    (e : G' ≅ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj G) (f : G ⟶ Q) [Epi f] :
    subobjectPullback g e (kernelSubobject f) =
      kernelSubobject (e.hom ≫ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map f) := by
  refine subobjectPullback_eq_kernelSubobject g e _ _
    ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
      (Abelian.cokernelKernelSubobjectIso f).hom) ?_
  rw [subobjectPullbackProjection, Category.assoc, ← Functor.map_comp,
    ← Abelian.cokernelKernelSubobjectIso_inv_comp f, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Twisting commutes with base change of the kernel subobject of an epimorphism. -/
theorem twistSubobjectEquiv_subobjectPullback_kernelSubobject {T' T : Scheme.{u}} (g : T' ⟶ T)
    (d : ℤ) {G Q : (projectiveSpaceOver n T).Modules} {G' : (projectiveSpaceOver n T').Modules}
    (e : G' ≅ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj G) (f : G ⟶ Q) [Epi f] :
    twistSubobjectEquiv d G' (subobjectPullback g e (kernelSubobject f)) =
      subobjectPullback g ((twistFunctor n T' d).mapIso e ≪≫ twistPullbackIso g d G)
        (twistSubobjectEquiv d G (kernelSubobject f)) := by
  have : Epi (twistMap d f) := epi_twistMap d f
  rw [subobjectPullback_kernelSubobject, twistSubobjectEquiv_kernelSubobject,
    twistSubobjectEquiv_kernelSubobject, subobjectPullback_kernelSubobject]
  have hmap : ((twistFunctor n T' d).mapIso e ≪≫ twistPullbackIso g d G).hom ≫
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (twistMap d f) =
      twistMap d (e.hom ≫ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map f) ≫
        (twistPullbackIso g d Q).hom := by
    rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← twistPullbackIso_hom_naturality,
      ← Category.assoc, twistMap_eq_twistFunctor_map, twistMap_eq_twistFunctor_map]
    simp only [Functor.map_comp]
  simp only [hmap]
  rw [kernelSubobject_comp_mono]

/-- **Twisting commutes with base change of subobjects** (Stacks 0DP7, naturality). -/
theorem twistSubobjectEquiv_subobjectPullback {T' T : Scheme.{u}} (g : T' ⟶ T) (d : ℤ)
    {G : (projectiveSpaceOver n T).Modules} {G' : (projectiveSpaceOver n T').Modules}
    (e : G' ≅ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj G) (K : Subobject G) :
    twistSubobjectEquiv d G' (subobjectPullback g e K) =
      subobjectPullback g ((twistFunctor n T' d).mapIso e ≪≫ twistPullbackIso g d G)
        (twistSubobjectEquiv d G K) := by
  have h := twistSubobjectEquiv_subobjectPullback_kernelSubobject g d e (cokernel.π K.arrow)
  rwa [kernelSubobject_cokernel_π] at h

end AlgebraicGeometry.ProjectiveQuotOverSpace

end

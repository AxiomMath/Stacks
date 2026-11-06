module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
/-!
# The degreewise right derived functors of a composite

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories with `𝒜` and
`ℬ` having enough injectives.  If `F` carries injective objects of `𝒜` to objects right acyclic
for `G`, the canonical map `R(G ∘ F) ⟶ RG ∘ RF` of bounded below derived functors is invertible;
at an object `M` of `𝒜` which is itself right acyclic for `F` this descends to an isomorphism
`R^n(G ∘ F)(M) ≅ R^nG(F(M))` of the `ℕ`-indexed right derived functors, in every degree.

The left exactness that the acyclicity criterion needs is also supplied here, in the form of
the statement that the kernel of a transformation of left exact functors is left exact.

## Main results

* `Stacks.Cohomology.LerayDegreewise.preservesFiniteLimits_kernel`: the kernel of a
  transformation of left exact additive functors between abelian categories is left exact.
* `Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived`: for a left exact
  functor, right acyclicity of an object is vanishing of all its higher `ℕ`-indexed right
  derived functors.
* `Stacks.Cohomology.LerayDegreewise.rightDerivedFunctorPlusSingleObjIso`: for an object right
  acyclic for `F`, the bounded below derived functor `RF` sends `M[0]` to `F(M)[0]`.
* `Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso`: the degreewise isomorphism
  `R^n(G ∘ F)(M) ≅ R^nG(F(M))`.

## Implementation notes

A kernel in a functor category is computed pointwise, so `(ker α).obj X` is the kernel of
`α.app X`; this is what `kernelAppIsLimit` records, and it is obtained by applying evaluation
at `X` to the kernel fork in the functor category.  Left exactness is then checked on kernels
(`CategoryTheory.Functor.preservesFiniteLimits_tfae`): a map into `(ker α).obj X` killed by
`(ker α).map f` is, after composing with the pointwise inclusion into `F.obj X`, killed by
`F.map f`, hence factors through `F.obj (ker f)`; that factorization is killed by
`α.app (ker f)` because `G.map (kernel.ι f)` is a monomorphism, so it factors once more through
`(ker α).obj (ker f)`.

The degreewise isomorphism is pointwise in `M` rather than a natural isomorphism of functors:
the identification `RF(M[0]) ≅ F(M)[0]` is the inverse of a component of the unit of `RF`, and
it is invertible exactly at the objects right acyclic for `F`.  The two comparisons between the
`ℕ`-indexed and the `ℤ`-indexed right derived functors are the components of
`Stacks.DerivedIndexing.rightDerivedIso`, and the canonical isomorphism
`R(G ∘ F) ≅ RG ∘ RF` is
`Stacks.Cohomology.DerivedPushforwardSections.compIso`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.LerayDegreewise

/-! ### The kernel of a transformation of left exact functors -/

section Kernel

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  {F G : A ⥤ B} (α : F ⟶ G)

omit [Abelian A] in
/-- The pointwise inclusion of the kernel of `α` into `F` is killed by `α`. -/
theorem kernelι_app_comp (Z : A) : (kernel.ι α).app Z ≫ α.app Z = 0 := by
  simpa only [NatTrans.comp_app, zero_app] using NatTrans.congr_app (kernel.condition α) Z

/-- A kernel in a functor category is computed pointwise: the value of `ker α` at `Z` is the
kernel of `α.app Z`. -/
def kernelAppIsLimit (Z : A) :
    IsLimit (KernelFork.ofι ((kernel.ι α).app Z) (kernelι_app_comp α Z)) :=
  KernelFork.mapIsLimit (c := KernelFork.ofι (kernel.ι α) (kernel.condition α))
    (kernelIsKernel α) ((evaluation A B).obj Z)

/-- **The kernel of a transformation of left exact functors is left exact.**  For additive
functors `F`, `G` between abelian categories which preserve finite limits and a transformation
`α : F ⟶ G`, the functor `ker α` preserves finite limits. -/
theorem preservesFiniteLimits_kernel [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    [(kernel α).Additive] : PreservesFiniteLimits (kernel α) := by
  refine ((Functor.preservesFiniteLimits_tfae (kernel α)).out 3 4 :).mp fun X Y f => ?_
  refine preservesLimit_of_preserves_limit_cone (kernelIsKernel f) ?_
  refine (isLimitMapConeForkEquiv' (kernel α) (kernel.condition f)).2 ?_
  have hιX : Mono ((kernel.ι α).app X) := (NatTrans.mono_iff_mono_app _).1 inferInstance X
  have hFker : IsLimit (KernelFork.ofι (F.map (kernel.ι f))
      (show F.map (kernel.ι f) ≫ F.map f = 0 by
        rw [← F.map_comp, kernel.condition, F.map_zero])) :=
    KernelFork.mapIsLimit (c := KernelFork.ofι (kernel.ι f) (kernel.condition f))
      (kernelIsKernel f) F
  have hmono : Mono ((kernel α).map (kernel.ι f)) := by
    have : Mono ((kernel α).map (kernel.ι f) ≫ (kernel.ι α).app X) := by
      rw [(kernel.ι α).naturality]
      infer_instance
    exact mono_of_mono _ ((kernel.ι α).app X)
  refine KernelFork.IsLimit.ofι' _ _ ?_
  intro W k hk
  have hu : (k ≫ (kernel.ι α).app X) ≫ F.map f = 0 := by
    rw [Category.assoc, ← (kernel.ι α).naturality f, ← Category.assoc, hk, zero_comp]
  obtain ⟨v, hv⟩ := KernelFork.IsLimit.lift' hFker _ hu
  simp only [Fork.ι_ofι] at hv
  have hvα : v ≫ α.app (kernel f) = 0 := by
    rw [← cancel_mono (G.map (kernel.ι f)), Category.assoc, ← α.naturality (kernel.ι f),
      ← Category.assoc, hv, zero_comp, Category.assoc, kernelι_app_comp, comp_zero]
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (kernelAppIsLimit α (kernel f)) _ hvα
  simp only [Fork.ι_ofι] at hl
  refine ⟨l, ?_⟩
  rw [← cancel_mono ((kernel.ι α).app X), Category.assoc, (kernel.ι α).naturality,
    ← Category.assoc, hl, hv]

end Kernel

/-! ### Right acyclicity and the degreewise comparison -/

section Comparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

omit [EnoughInjectives D] in
/-- **Right acyclicity of an object for a left exact functor is vanishing of all its higher
right derived functors.**  This is [Stacks, Tag 015C] part (2) read through the comparison of
the `ℕ`-indexed and the `ℤ`-indexed right derived functors. -/
theorem rightAcyclic_iff_isZero_rightDerived [PreservesFiniteLimits F] (M : C) :
    F.rightAcyclic M ↔ ∀ p : ℕ, 0 < p → IsZero ((F.rightDerived p).obj M) := by
  rw [(F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus M).2 inferInstance]
  refine ⟨fun h p hp => ?_, fun h i hi => ?_⟩
  · exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff F p M).2
      (h (p : ℤ) (by exact_mod_cast hp))
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff F p M).1
      (h p (by exact_mod_cast hi))

/-- An additive functor carries the complex `X[n]` of the bounded below homotopy category to the
complex `F(X)[n]`. -/
def mapHomotopyCategoryPlusSingleObjIso (n : ℤ) (X : C) :
    F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor C n).obj X) ≅
      (HomotopyCategory.Plus.singleFunctor D n).obj (F.obj X) :=
  (HomotopyCategory.Plus.ι D).preimageIso
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app X))

/-- **An object right acyclic for `F` is computed by `F` itself.**  If `M` is right acyclic for
`F` then the bounded below right derived functor `RF` carries `M[0]` to `F(M)[0]`: the unit of
`RF` is invertible there by definition of right acyclicity, and `F` carries `M[0]` to
`F(M)[0]`. -/
def rightDerivedFunctorPlusSingleObjIso (M : C) (hM : F.rightAcyclic M) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (F.obj M) :=
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := by
    have hM' : IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := hM
    have hφ := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C))
      (HomotopyCategory.Plus.quasiIso C) F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith).1 inferInstance
    rw [← Functor.rightDerived_fac_app _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C))
      (HomotopyCategory.Plus.quasiIso C) F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith ((HomotopyCategory.Plus.singleFunctor C 0).obj M)]
    infer_instance
  F.rightDerivedFunctorPlus.mapIso
      ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).app M) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M))).symm ≪≫
    DerivedCategory.Plus.Qh.mapIso (mapHomotopyCategoryPlusSingleObjIso F 0 M) ≪≫
    ((Functor.singleFunctorPlusIsoCompQh (A := D) 0).app (F.obj M)).symm

/-- **The degreewise right derived functors of a composite.**  Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞`
be additive functors between abelian categories with `𝒜` and `ℬ` having enough injectives.  If
`F` carries every injective object of `𝒜` to an object right acyclic for `G`, and `M` is an
object of `𝒜` right acyclic for `F`, then `R^n(G ∘ F)(M) ≅ R^nG(F(M))` in every degree `n`. -/
def rightDerivedCompObjIso (hFG : ∀ I : C, Injective I → G.rightAcyclic (F.obj I))
    (M : C) (hM : F.rightAcyclic M) (n : ℕ) :
    ((F ⋙ G).rightDerived n).obj M ≅ (G.rightDerived n).obj (F.obj M) :=
  (Stacks.DerivedIndexing.rightDerivedIso (F ⋙ G) n).app M ≪≫
    (DerivedCategory.Plus.homologyFunctor E (n : ℤ)).mapIso
      ((Stacks.Cohomology.DerivedPushforwardSections.compIso F G hFG).app
        ((DerivedCategory.Plus.singleFunctor C 0).obj M)) ≪≫
    (DerivedCategory.Plus.homologyFunctor E (n : ℤ)).mapIso
      (G.rightDerivedFunctorPlus.mapIso (rightDerivedFunctorPlusSingleObjIso F M hM)) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso G n).app (F.obj M)).symm

end Comparison

end Stacks.Cohomology.LerayDegreewise

end

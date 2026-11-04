module

public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage

/-!
# The inverse image of a weak Serre class along a left exact functor

`CategoryTheory.ObjectProperty.isWeakSerreClass_inverseImage` pulls a weak Serre class back
along an *exact* functor.  The comparison functor from fppf to étale sheaves of modules, along
which [Stacks, Tag 0771] (2) transports the weak Serre property of `LQCoh^fbc`, is only left
exact.  What replaces right exactness is the extension step of the source: for a short exact
sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` whose first term lies in the class, the image of `X₂ ⟶ X₃` is an
epimorphism.  Under that hypothesis the image of such a short exact sequence is short exact, so
the class is closed under extensions and, factoring a morphism through its coimage, under
cokernels.

## Main results

* `CategoryTheory.ObjectProperty.isWeakSerreClass_inverseImage_of_epi`.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **The inverse image of a weak Serre class along a left exact functor which is right exact on
the short exact sequences starting in the class is a weak Serre class.**  The hypothesis `hepi`
makes the image of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `F X₁ ∈ P` short exact;
that gives closure under extensions, and closure under cokernels follows by applying it to
`0 ⟶ ker f ⟶ X ⟶ coim f ⟶ 0` and `0 ⟶ im f ⟶ Y ⟶ coker f ⟶ 0`. -/
theorem isWeakSerreClass_inverseImage_of_epi (P : ObjectProperty D) [P.IsWeakSerreClass]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    (hepi : ∀ {T : ShortComplex C}, T.ShortExact → P (F.obj T.X₁) → Epi (F.map T.g)) :
    (P.inverseImage F).IsWeakSerreClass := by
  have hSE : ∀ {T : ShortComplex C}, T.ShortExact → P (F.obj T.X₁) → (T.map F).ShortExact := by
    intro T hT h₁
    have := hT.mono_f
    have : Epi (T.map F).g := hepi hT h₁
    have hk : IsLimit (KernelFork.ofι (T.map F).f (T.map F).zero) :=
      (KernelFork.isLimitMapConeEquiv _ F) (isLimitOfPreserves F hT.fIsKernel)
    have : Mono (T.map F).f := Fork.IsLimit.mono hk
    exact ⟨ShortComplex.exact_of_f_is_kernel _ hk⟩
  have hX₃ : ∀ {T : ShortComplex C}, T.ShortExact → P (F.obj T.X₁) → P (F.obj T.X₂) →
      P (F.obj T.X₃) := fun hT h₁ h₂ =>
    P.prop_of_isColimit_cokernelCofork (hSE hT h₁).gIsCokernel h₁ h₂
  have : (P.inverseImage F).IsClosedUnderKernels := isClosedUnderKernels_inverseImage P F
  have : (P.inverseImage F).IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have hker : P (F.obj (kernel f)) := (P.inverseImage F).prop_kernel f hX hY
    have h₁ : P (F.obj (cokernel (kernel.ι f))) :=
      hX₃ (T := ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (cokernel.condition _))
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (kernel.ι f)) }
        hker hX
    have h₂ : P (F.obj (kernel (cokernel.π f))) :=
      P.prop_of_iso (F.mapIso (Abelian.coimageIsoImage f)) h₁
    have h₃ : P (F.obj (cokernel f)) :=
      hX₃ (T := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _))
        { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π f)) } h₂ hY
    exact P.prop_of_iso (F.mapIso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk))
      h₃⟩
  have : (P.inverseImage F).IsClosedUnderExtensions :=
    ⟨fun {T} hT h₁ h₃ => P.prop_X₂_of_shortExact (hSE hT h₁) h₁ h₃⟩
  exact {}

end CategoryTheory.ObjectProperty

end

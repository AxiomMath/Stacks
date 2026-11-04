module

public import StacksFrontier.Algebra.Module.Pure.Injective
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.InjectiveObjects

/-!
# Enough injectives among the adequate functors

Every adequate module-valued functor on the commutative `A`-algebras embeds into the extension of
scalars `B ↦ B ⊗[A] I` of a pure injective `A`-module `I`: a kernel presentation embeds it into an
extended module, and every module injects universally into a pure injective one.

Since the extension of a pure injective module is an injective object among the adequate
functors, those embeddings are injective presentations and the adequate functors have enough
injectives.

## Main results

* `AdequateFunctor.exists_pureInjective_mono_moduleExtension` — every adequate functor admits a
  monomorphism into the extension of a pure injective module.
* `AdequateFunctor.enoughInjectives_adequate_of_injective_moduleExtension` — the adequate functors
  have enough injectives if the extension of every pure injective module is injective.
* `AdequateFunctor.adequateFunctor_enoughInjectives` — the adequate functors have enough
  injectives, part (5) of [Stacks, Tag 06Z7].

## Implementation notes

The source obtains enough injectives in the adequate functors from the right adjoint to their
inclusion into all module-valued functors. Here the embeddings into extensions of pure injective
modules are produced directly, and the injectivity of those extensions is
`AdequateFunctor.injective_moduleExtension_of_pureInjective`, which is proved by a pushout
argument inside the adequate functors rather than from enough injectives; so no circularity
arises.

## References

* [Stacks Project, Tag 0700](https://stacks.math.columbia.edu/tag/0700)
* [Stacks Project, Tag 06Z7](https://stacks.math.columbia.edu/tag/06Z7)
* [Stacks Project, Tag 0708](https://stacks.math.columbia.edu/tag/0708)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AdequateFunctor

/-- Every adequate module-valued functor admits a monomorphism into the extension of a pure
injective `A`-module: a kernel presentation of the functor embeds it into the extension of a
module, that module injects universally into a pure injective module, and extension carries a
universally injective map to a monomorphism. -/
public theorem exists_pureInjective_mono_moduleExtension {A : Type u} [CommRing A]
    (F : (adequate.{u, v, max u v w} A).FullSubcategory) :
    ∃ (I : ModuleCat.{max u v w} A)
      (φ : F ⟶ (⟨(moduleExtensionFunctor.{max u v w, v} A).obj I,
        isAdequate_moduleExtension I⟩ : (adequate.{u, v, max u v w} A).FullSubcategory)),
      Module.PureInjective A I ∧ Mono φ := by
  obtain ⟨M, _, d, hd⟩ := F.property
  have he : F.obj ≅ kernel ((moduleExtensionFunctor.{max u v w, v} A).map d) :=
    Classical.choice ((isKernelPresentation_iff F.obj d).mp hd)
  choose I _ hIadd hImod _ _ f _ _ _ _ hfu hI using
    Module.exists_pureInjective_universallyExact_extension A M
  let _ : AddCommGroup I := hIadd
  let _ : Module A I := hImod
  let j : M ⟶ ModuleCat.of A I := ModuleCat.ofHom f
  have hj : Mono ((moduleExtensionFunctor.{max u v w, v} A).map j) :=
    mono_moduleExtension_map_of_universallyInjective j hfu
  refine ⟨ModuleCat.of A I, ObjectProperty.homMk
    (he.hom ≫ kernel.ι _ ≫ (moduleExtensionFunctor.{max u v w, v} A).map j), hI, ?_⟩
  apply (adequate.{u, v, max u v w} A).ι.mono_of_mono_map
  simpa using mono_comp he.hom (kernel.ι _ ≫ (moduleExtensionFunctor.{max u v w, v} A).map j)

/-- The adequate module-valued functors have enough injectives as soon as the extension of every
pure injective `A`-module is an injective object among them, because every adequate functor
embeds into such an extension. -/
public theorem enoughInjectives_adequate_of_injective_moduleExtension {A : Type u} [CommRing A]
    (h : ∀ I : ModuleCat.{max u v w} A, Module.PureInjective A I →
      Injective (⟨(moduleExtensionFunctor.{max u v w, v} A).obj I,
        isAdequate_moduleExtension I⟩ : (adequate.{u, v, max u v w} A).FullSubcategory)) :
    EnoughInjectives ((adequate.{u, v, max u v w} A).FullSubcategory) where
  presentation F := by
    obtain ⟨I, φ, hI, hφ⟩ := exists_pureInjective_mono_moduleExtension.{u, v, w} F
    exact ⟨{ J := _, injective := h I hI, f := φ, mono := hφ }⟩

/-- **Stacks Project, Tag 06Z7.** The adequate module-valued functors on the commutative
`A`-algebras have enough injectives: every one of them embeds into the extension of a pure
injective `A`-module, and such an extension is an injective object. -/
@[stacks 06Z7 "adequate_functors_enough_injectives"]
public instance adequateFunctor_enoughInjectives {A : Type u} [CommRing A] :
    EnoughInjectives ((adequate.{u, v, max u v w} A).FullSubcategory) :=
  enoughInjectives_adequate_of_injective_moduleExtension.{u, v, w}
    fun I hI => injective_moduleExtension_of_pureInjective I hI

end AdequateFunctor

end

module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubsheafRange

/-!
# Monomorphy of a morphism of sheaves of modules is local on the base

`Stacks.AlgebraicGeometry.ReflexiveModules.injective_app_of_mono` says that a monomorphism of
`𝒪_X`-modules is injective on the sections over every open, and
`Stacks.AlgebraicGeometry.Subsheaf.mono_of_injective_app` is the converse. This file proves that
injectivity on sections is **local** and deduces that **monomorphy is local**: a morphism of
`𝒪_X`-modules whose restrictions along a jointly surjective family of open immersions are
monomorphisms is a monomorphism.

This is the companion, for monomorphy, of
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover` for equality of morphisms and
of `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover` for
invertibility. Like the first of those, only the separatedness half of the sheaf condition is
used, through `TopCat.Presheaf.IsSheaf.section_ext`; no quasi-coherence and no affineness is
needed.

## Main results

* `Stacks.AlgebraicGeometry.Modules.injective_app_of_cover`: **injectivity on sections is
  local.** If the sections map is injective over every open contained in a member of an open
  covering, it is injective over every open.
* `Stacks.AlgebraicGeometry.Modules.mono_of_mono_restrict_cover` and
  `Stacks.AlgebraicGeometry.Modules.mono_of_mono_pullback_cover`: **monomorphy is local**, in the
  restriction and in the inverse-image spelling.

## Implementation notes

The sections of the restriction of `M` to an open `W` over an open `V` of `W` are the sections of
`M` over `W.ι ''ᵁ V`, and `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity, so
the sections map of a restricted morphism *is* a sections map of the original morphism, at the
image open. That identification is definitional and is used here through a type ascription, the
same way `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover` uses it; the open
`W.ι ''ᵁ (W.ι ⁻¹ᵁ V)` is then rewritten to `V` by
`Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le`.

The covering hypothesis is the pointwise one, `∀ x, ∃ a, x ∈ W a`, rather than
`AlgebraicGeometry.IsOpenCover` or `iSup W = ⊤`: it is what the proof uses and what the
consumers — covering statements such as
`AlgebraicGeometry.exists_mem_range_blowupChartι` for the charts of a blowup — produce.

## References

* [Stacks Project, Tag 01AD](https://stacks.math.columbia.edu/tag/01AD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- **Injectivity on sections is local.** If the sections map of `φ` is injective over every open
contained in a member of an open covering of `X`, then it is injective over every open: a section
killed by `φ` is killed on each member of the induced covering, hence is zero by separatedness of
the source. -/
theorem injective_app_of_cover {M N : X.Modules} (φ : M ⟶ N) {ι : Type*} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (h : ∀ (a : ι) (V : X.Opens), V ≤ W a → Function.Injective (Scheme.Modules.Hom.app φ V))
    (U : X.Opens) : Function.Injective (Scheme.Modules.Hom.app φ U) := by
  intro m m' hmm'
  refine M.isSheaf.section_ext (U := op U) ?_
  intro x hx
  obtain ⟨a, ha⟩ := hW x
  refine ⟨U ⊓ W a, inf_le_left, ⟨hx, ha⟩, h a (U ⊓ W a) inf_le_right ?_⟩
  rw [← ModuleLimits.Hom_app_presheaf_map φ inf_le_left m,
    ← ModuleLimits.Hom_app_presheaf_map φ inf_le_left m', hmm']

/-- **Monomorphy of a morphism of sheaves of modules is local on the base.** If the restrictions
of `φ` along a jointly surjective family of open immersions into `X` are monomorphisms, then `φ`
is a monomorphism.

The restriction of `φ` along `j a` is injective on the sections over every open of its source,
that is, `φ` is injective on the sections over every open contained in the image of `j a`;
injectivity on sections is local, and a morphism injective on all sections is a monomorphism. -/
theorem mono_of_mono_restrict_cover {M N : X.Modules} (φ : M ⟶ N) {ι : Type*}
    {Y : ι → Scheme.{u}} (j : ∀ a, Y a ⟶ X) [∀ a, IsOpenImmersion (j a)]
    (hcov : ∀ x : X, ∃ (a : ι) (y : Y a), (j a) y = x)
    (h : ∀ a, Mono ((Scheme.Modules.restrictFunctor (j a)).map φ)) : Mono φ := by
  refine Subsheaf.mono_of_injective_app φ (injective_app_of_cover φ (fun a => (j a).opensRange)
    (fun x => by obtain ⟨a, y, hy⟩ := hcov x; exact ⟨a, y, hy⟩) fun a V hV => ?_)
  have := h a
  have hV' : (j a) ''ᵁ ((j a) ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hV
  have h₁ : Function.Injective
      (Scheme.Modules.Hom.app φ ((j a) ''ᵁ ((j a) ⁻¹ᵁ V))) :=
    ReflexiveModules.injective_app_of_mono
      ((Scheme.Modules.restrictFunctor (j a)).map φ) ((j a) ⁻¹ᵁ V)
  rwa [hV'] at h₁

/-- **Monomorphy is local, in the inverse-image spelling.** The restriction functor along an open
immersion is isomorphic to the inverse-image functor
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), so a morphism whose inverse
images along a jointly surjective family of open immersions are monomorphisms is a
monomorphism. -/
theorem mono_of_mono_pullback_cover {M N : X.Modules} (φ : M ⟶ N) {ι : Type*}
    {Y : ι → Scheme.{u}} (j : ∀ a, Y a ⟶ X) [∀ a, IsOpenImmersion (j a)]
    (hcov : ∀ x : X, ∃ (a : ι) (y : Y a), (j a) y = x)
    (h : ∀ a, Mono ((Scheme.Modules.pullback (j a)).map φ)) : Mono φ := by
  refine mono_of_mono_restrict_cover φ j hcov fun a => ?_
  have key : (Scheme.Modules.restrictFunctor (j a)).map φ =
      (Scheme.Modules.restrictFunctorIsoPullback (j a)).hom.app M ≫
        (Scheme.Modules.pullback (j a)).map φ ≫
          (Scheme.Modules.restrictFunctorIsoPullback (j a)).inv.app N := by
    rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback (j a)).hom.naturality φ,
      Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, Category.comp_id]
  have := h a
  rw [key]
  infer_instance

end Stacks.AlgebraicGeometry.Modules

end

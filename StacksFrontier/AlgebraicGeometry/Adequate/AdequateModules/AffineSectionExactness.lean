module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCokernels
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFiniteFreeLift
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainKernels
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Sheafification

/-!
# The affine-section functor and exactness on the algebras of a big site

An affine-section functor of a sheaf of modules on one of the five big `τ`-sites over a scheme
`S` is defined only on the algebras whose spectra belong to the site. This module states the
closure properties of adequacy on that restricted domain of algebras, proves those for kernels,
cokernels and finite products, and proves the exactness of the pushforward of presheaves of
modules that computes the affine-section functors.

## Main definitions

* `Stacks.Adequate.AffineLocalAdequacy` — the conclusion of [Stacks, Tag 06VI] for every
  adequate sheaf of modules at once: its affine-section functor is adequate at every affine
  scheme of the site.
* `Stacks.Adequate.AffineAdequateKernels`, `Stacks.Adequate.AffineAdequateCokernels`,
  `Stacks.Adequate.AffineAdequateFiniteProducts`, `Stacks.Adequate.AffineAdequateColimits`
  and `Stacks.Adequate.AffineAdequateExtensions` — the closure properties of adequacy for
  module-valued functors on the algebras *of the site*, namely [Stacks, Tags 06V3, 06V2, 06VB,
  06V4 and 06V8] on that domain of algebras.

## Main results

* `Stacks.Adequate.affineAdequateKernels` — `Stacks.Adequate.AffineAdequateKernels` holds, i.e.
  [Stacks, Tag 06V3] on the site's domain of algebras.
* `Stacks.Adequate.affineAdequateKernels_of_isLinearlyAdequate` — the same for a *linearly*
  adequate source, by a route that needs no [Stacks, Tag 06V1].
* `Stacks.Adequate.affineAdequateCokernels` — `Stacks.Adequate.AffineAdequateCokernels` holds,
  i.e. [Stacks, Tag 06V2] on the site's domain of algebras.
* `Stacks.Adequate.affineAdequateFiniteProducts` —
  `Stacks.Adequate.AffineAdequateFiniteProducts` holds, i.e. [Stacks, Tag 06VB] on the site's
  domain of algebras.
* `Stacks.Adequate.BigSite.cutoff_isStrongPrelimit` — the cutoff of a chosen big site is a
  strong prelimit cardinal.
* `Stacks.Adequate.pushforward_preservesFiniteLimits` and
  `Stacks.Adequate.pushforward_preservesColimitsOfShape` — pushforward of presheaves of modules
  along a morphism of presheaves of rings over a functor of sites is computed on sections, so it
  is exact.

## Implementation notes

The closure properties of adequacy for module-valued functors on the algebras of the site are
named as `Prop`-valued abbreviations. [Stacks, Tags 06V3, 06V2, 06VB, 06V4 and 06V8] are proved
for module-valued functors on *all* algebras over the base ring
(`AdequateFunctor.isAdequate_kernel`, `AdequateFunctor.isAdequate_cokernel`,
`AdequateFunctor.adequate_isClosedUnderFiniteProducts`, `AdequateFunctor.isAdequate_colimit`
and `AdequateFunctor.isAdequate_of_shortExact`), while an affine-section functor is defined
only on the algebras whose spectra belong to the site.

Finite products need no closure property on the site's domain at all: a kernel presentation of
each factor is a map of modules over the base ring, and the biproduct of those maps presents the
product.

Kernels and cokernels are [Stacks, Tags 06V3 and 06V2] carried to the site's domain,
`AdequateFunctor.isAdequate_kernel_site` and `AdequateFunctor.isAdequate_cokernel_site`. Their
non-generic inputs are fullness of extension of scalars there
(`AdequateFunctor.full_moduleExtensionFunctorOn`) and [Stacks, Tag 06V1] there
(`AdequateFunctor.isAdequate_cokernel_to_moduleExtension_on`), whose own non-generic inputs are
[Stacks, Tags 06V0 and 06UX] on that domain,
`AdequateFunctor.exists_lift_from_finite_free_kernel_site` and
`AdequateFunctor.exists_coproduct_linearlyAdequate_surjective_on`. Full 06V2 is *not* needed
for kernels: the proof of 06V3 applies `AdequateFunctor.isAdequate_cokernel` only to a mono into
a module extension, which is the shape of 06V1.

There is a second route when the source is *linearly* adequate,
`Stacks.Adequate.affineAdequateKernels_of_isLinearlyAdequate`: there
`AdequateFunctor.isAdequate_kernel_of_moduleExtensionLift` reduces the statement to a single map
of modules `t : M₁ ⟶ M₂` whose base change extends `Ker(E a) ⟶ Ker(E b) ↪ E M₂` along
`Ker(E a) ↪ E M₁`, and 06V0 on the site's domain supplies it directly, no 06V1 entering. That
reduction does *not* reach a general adequate source: 06V0 lifts only along a map of finite free
module extensions, and a general adequate functor is only a pointwise *quotient* of a coproduct
of linearly adequate ones ([Stacks, Tag 06UX]), whose pieces' lifts are existence-only and do
not glue to a single `t`.

## References

* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
* [Stacks Project, Tag 06V4](https://stacks.math.columbia.edu/tag/06V4)
* [Stacks Project, Tag 06V8](https://stacks.math.columbia.edu/tag/06V8)
* [Stacks Project, Tag 06VB](https://stacks.math.columbia.edu/tag/06VB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m u₃ v₃ w w₂ u₁ v₁ u₂ v₂ v

namespace Stacks.Adequate

/-! ### Exactness of the pushforward of presheaves of modules -/

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {Φ : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{w₂}} {R₀ : Cᵒᵖ ⥤ RingCat.{w₂}} (φ : R₀ ⟶ Φ.op ⋙ R)

/-- Evaluating the pushforward of presheaves of modules at an object is evaluation at its image
followed by restriction of scalars. -/
public noncomputable def pushforwardCompEvaluationIso (X : Cᵒᵖ) :
    PresheafOfModules.pushforward.{w} φ ⋙ PresheafOfModules.evaluation R₀ X ≅
      PresheafOfModules.evaluation R (Φ.op.obj X) ⋙
        ModuleCat.restrictScalars (φ.app X).hom :=
  Iso.refl _

/-- Every map of presheaves of modules has a cokernel. -/
public instance hasCokernel_presheafOfModules {F G : PresheafOfModules.{max w₂ w} R₀}
    (g : F ⟶ G) : HasColimit (parallelPair g 0) :=
  have h : HasColimitsOfShape WalkingParallelPair (PresheafOfModules.{max w₂ w} R₀) :=
    PresheafOfModules.hasColimitsOfShape _ _
  h.has_colimit _

/-- Pushforward of presheaves of modules preserves zero morphisms. -/
public instance pushforward_preservesZeroMorphisms :
    (PresheafOfModules.pushforward.{w} φ).PreservesZeroMorphisms :=
  ⟨by intro X Y; ext Z x; rfl⟩

/-- Pushforward of presheaves of modules preserves finite limits, being computed on sections
by restriction of scalars. -/
public noncomputable instance pushforward_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{w} φ) := by
  refine ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsLimits
    (K ⋙ PresheafOfModules.pushforward φ) _ fun X => ?_
  refine IsLimit.ofIsoLimit (isLimitOfPreserves
    (PresheafOfModules.evaluation R (Φ.op.obj X) ⋙
      ModuleCat.restrictScalars (φ.app X).hom) hc) ?_
  exact (Cone.ext (Iso.refl _) (by intro j; simp)).symm

/-- Pushforward of presheaves of modules preserves colimits of any shape admitted by abelian
groups, being computed on sections by restriction of scalars. -/
public noncomputable instance pushforward_preservesColimitsOfShape (J : Type u₃)
    [Category.{v₃} J] [HasColimitsOfShape J AddCommGrpCat.{max w₂ w}] :
    PreservesColimitsOfShape J (PresheafOfModules.pushforward.{max w₂ w} φ) := by
  refine ⟨fun {K} => ⟨fun {c} hc => ⟨?_⟩⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsColimits
    (K ⋙ PresheafOfModules.pushforward φ) _ fun X => ?_
  refine IsColimit.ofIsoColimit (isColimitOfPreserves
    (PresheafOfModules.evaluation R (Φ.op.obj X) ⋙
      ModuleCat.restrictScalars (φ.app X).hom) hc) ?_
  exact (Cocone.ext (Iso.refl _) (by intro j; simp)).symm

end Pushforward

end Stacks.Adequate

namespace AdequateFunctor

open scoped ZeroObject

/-- A zero module-valued functor on any domain of algebras is adequate: it is the kernel of the
identity of the zero module. -/
public lemma isAdequate_of_isZero {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
    (ι : C ⥤ CommAlgCat.{max u v} A) {F : ModuleValuedFunctorOn.{w} ι} (hF : IsZero F) :
    IsAdequate ι F := by
  let M : ModuleCat.{max u v w} A := 0
  refine ⟨M, M, 𝟙 M, ⟨IsZero.iso (Functor.map_isZero _ hF) ?_⟩⟩
  have : Mono ((moduleExtensionFunctorOn ι).map (𝟙 M)) := by
    rw [(moduleExtensionFunctorOn ι).map_id]; infer_instance
  exact isZero_kernel_of_mono _

end AdequateFunctor

namespace Stacks.Adequate

open scoped ZeroObject

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-! ### The affine-section functor -/

/-- Affine sections of a presheaf of modules are the value of the pushforward along the scalar
identification. -/
public theorem presheafAffineSectionFunctor_eq (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (P : PresheafOfModules.{max u m} B.structureSheaf.obj) :
    presheafAffineSectionFunctor B P A f =
      (PresheafOfModules.pushforward (affineRingMap B A f)).obj P := rfl

/-- Sections of a sheaf of modules on the site are created from its underlying presheaf of
modules, so they preserve finite limits. -/
public noncomputable instance forget_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.forget.{max u m} B.structureSheaf) :=
  SheafOfModules.Finite.forgetPreservesFiniteLimits (R := B.structureSheaf)

/-- Sections of a sheaf of modules on the site preserve zero morphisms. -/
public instance forget_preservesZeroMorphisms :
    (SheafOfModules.forget.{max u m} B.structureSheaf).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- The affine-section functor preserves zero morphisms. -/
public instance affineSectionsFunctor_preservesZeroMorphisms (A : CommRingCat.{u})
    (f : Spec A ⟶ S) :
    (affineSectionsFunctor.{u, max u m} B A f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_comp _ _

/-! ### Adequacy at every affine of the site -/

/-- The conclusion of [Stacks, Tag 06VI] for every adequate sheaf of modules at once: the
affine-section functor of an adequate sheaf of modules is adequate at every affine scheme of
the site over `S`. -/
public abbrev AffineLocalAdequacy : Prop :=
  ∀ F : SheafOfModules.{max u m} B.structureSheaf, IsAdequate B F →
    ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S), schemeSizeBelow B.cutoff (Spec A) →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
        (affineSectionFunctor B F A f)

/-! ### Exactness on the algebras of the site -/

/-- Adequacy of module-valued functors on the algebras of the site over an affine scheme of the
site is closed under kernels: [Stacks, Tag 06V3] on the site's domain of algebras. -/
public abbrev AffineAdequateKernels : Prop :=
  ∀ (A : CommRingCat.{u}), schemeSizeBelow B.cutoff (Spec A) →
    ∀ {F G : AdequateFunctor.ModuleValuedFunctorOn.{max u m}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))} (φ : F ⟶ G),
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) F →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) G →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) (kernel φ)

/-- Adequacy of module-valued functors on the algebras of the site over an affine scheme of the
site is closed under cokernels: [Stacks, Tag 06V2] on the site's domain of algebras. -/
public abbrev AffineAdequateCokernels : Prop :=
  ∀ (A : CommRingCat.{u}), schemeSizeBelow B.cutoff (Spec A) →
    ∀ {F G : AdequateFunctor.ModuleValuedFunctorOn.{max u m}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))} (φ : F ⟶ G),
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) F →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) G →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) (cokernel φ)

/-- Adequacy of module-valued functors on the algebras of the site over an affine scheme of the
site is closed under finite products: [Stacks, Tag 06VB] on the site's domain of algebras. -/
public abbrev AffineAdequateFiniteProducts : Prop :=
  ∀ (A : CommRingCat.{u}), schemeSizeBelow B.cutoff (Spec A) →
    ∀ (J : Type) (_ : Finite J)
      (K : Discrete J ⥤ AdequateFunctor.ModuleValuedFunctorOn.{max u m}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))
      (c : Cone K), IsLimit c →
      (∀ j, AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) (K.obj j)) →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) c.pt

/-- `Stacks.Adequate.AffineAdequateFiniteProducts` holds: adequacy of module-valued functors on
the algebras of the site is closed under finite products. A kernel presentation of each factor
is a map of `A`-modules, and the biproduct of those maps presents the product, because
extension of scalars is additive and the kernel of a biproduct of two morphisms is the
biproduct of their kernels. -/
public theorem affineAdequateFiniteProducts : AffineAdequateFiniteProducts.{u, m} B := by
  intro A _ J hJ K c hc hK
  have := hJ
  exact AdequateFunctor.isAdequate_of_isLimit_discrete _ J K hc hK

/-- The cutoff of a chosen big site is a strong prelimit cardinal. -/
public theorem BigSite.cutoff_isStrongPrelimit : Cardinal.IsStrongPrelimit B.cutoff := by
  obtain ⟨cut, base_mem, J, isSheaf, chosen⟩ := B
  rcases chosen with ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ |
    ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩
  · subst he; exact C.schemeCardinal_isStrongPrelimit
  · subst he; exact C.cutoff_isStrongPrelimit
  · subst he; exact C.cutoff_isStrongPrelimit
  · subst he; exact C.cutoff_isStrongPrelimit
  · subst he; exact C.cutoff_isStrongPrelimit

/-- The cutoff of a big site exceeds `ℵ₀` once it bounds the size of some affine scheme. -/
private theorem aleph0_lt_cutoff {A : CommRingCat.{u}} (hA : schemeSizeBelow B.cutoff (Spec A)) :
    Cardinal.aleph0 < B.cutoff :=
  lt_of_le_of_lt (Scheme.aleph0_le_size (Spec A)) hA

/-- `Stacks.Adequate.AffineAdequateKernels` holds whenever the source of the morphism is
*linearly* adequate: [Stacks, Tag 06V3] on the site's domain of algebras in that case. -/
public theorem affineAdequateKernels_of_isLinearlyAdequate (A : CommRingCat.{u})
    (hA : schemeSizeBelow B.cutoff (Spec A))
    {F G : AdequateFunctor.ModuleValuedFunctorOn.{max u m}
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))} (φ : F ⟶ G)
    (hF : AdequateFunctor.IsLinearlyAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) F)
    (hG : AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) G) :
    AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) (kernel φ) :=
  AdequateFunctor.isAdequate_kernel_of_isLinearlyAdequate_site
    (aleph0_lt_cutoff B hA)
    B.cutoff_isStrongPrelimit A hA φ hF hG

/-- `Stacks.Adequate.AffineAdequateKernels` holds: adequacy of module-valued functors on the
algebras of the site over an affine scheme of the site is closed under kernels. This is
[Stacks, Tag 06V3] on the site's domain of algebras. -/
public theorem affineAdequateKernels : AffineAdequateKernels.{u, m} B := by
  intro A hA F G φ hF hG
  exact AdequateFunctor.isAdequate_kernel_site.{m}
    (aleph0_lt_cutoff B hA)
    B.cutoff_isStrongPrelimit A hA φ hF hG

/-- `Stacks.Adequate.AffineAdequateCokernels` holds: adequacy of module-valued functors on the
algebras of the site over an affine scheme of the site is closed under cokernels. This is
[Stacks, Tag 06V2] on the site's domain of algebras. -/
public theorem affineAdequateCokernels : AffineAdequateCokernels.{u, m} B := by
  intro A hA F G φ hF hG
  exact AdequateFunctor.isAdequate_cokernel_site.{m}
    (aleph0_lt_cutoff B hA)
    B.cutoff_isStrongPrelimit A hA φ hF hG

/-- Adequacy of module-valued functors on the algebras of the site over an affine scheme of the
site is closed under extensions: [Stacks, Tag 06V8] on the site's domain of algebras. -/
public abbrev AffineAdequateExtensions : Prop :=
  ∀ (A : CommRingCat.{u}), schemeSizeBelow B.cutoff (Spec A) →
    ∀ T : ShortComplex (AdequateFunctor.ModuleValuedFunctorOn.{max u m}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))),
      T.ShortExact →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) T.X₁ →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) T.X₃ →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) T.X₂

/-- Adequacy of module-valued functors on the algebras of the site over an affine scheme of the
site is closed under colimits of shape `J`: [Stacks, Tag 06V4] on the site's domain of
algebras. -/
public abbrev AffineAdequateColimits (J : Type (max u m)) [Category.{max u m} J] : Prop :=
  ∀ (A : CommRingCat.{u}), schemeSizeBelow B.cutoff (Spec A) →
    ∀ (K : J ⥤ AdequateFunctor.ModuleValuedFunctorOn.{max u m}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))
      (c : Cocone K), IsColimit c →
      (∀ j, AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) (K.obj j)) →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) c.pt

end Stacks.Adequate

end

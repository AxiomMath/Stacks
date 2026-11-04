module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# The base change comparison of a kernel, and flatness of the étale charts

Let `F` be an algebraic space, let `φ : G ⟶ G'` be a morphism of `𝒪_F`-modules on the small
étale site of `F` and let `f : V ⟶ U` be a morphism of étale charts.  The base change
comparison `AlgebraicGeometry.Space.sectionsBaseChange`

`𝒪_F(V) ⊗_{𝒪_F(U)} G(U) ⟶ G(V)`

is bijective for `G` and for `G'` exactly when both are *cartesian* over `f`, which for affine
charts is the criterion of Stacks 03DX(2) for quasi-coherence.  This file proves that the
comparison for `ker φ` is then bijective too, and that the flatness hypothesis the argument
needs holds automatically between affine charts because étale morphisms are flat.

The kernel is the one of the six closure operations of Stacks 03M1 that this criterion can see.
Sections of a sheaf of modules take kernels to kernels, so the cartesian condition on `ker φ`
is a statement about the module-theoretic kernels of the maps on sections over `U` and over
`V`; cokernels, direct sums and colimits of sheaves are not computed on sections, and for them
no such reduction exists.  Flatness is what makes the reduction work: tensoring the exact
sequence `0 → (ker φ)(U) → G(U) → G'(U)` with `𝒪_F(V)` keeps it exact, and the comparison maps
identify its last two terms with `0 → (ker φ)(V) → G(V) → G'(V)`.

Flatness is also not removable.  On a site whose restriction maps are *not* flat the cartesian
condition genuinely fails to be stable under kernels:
`ChaoticQCoh.KernelCounterexample.not_quasicoherent_closed_under_kernels` in
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentKernelCounterexample` is the
two-object site with `𝒪(V) = ℤ`, `𝒪(U) = ℤ/2` and reduction as its restriction map, where
multiplication by `2` on the structure sheaf has a non-cartesian kernel.  That restriction map
is the standard example of a non-flat ring map, and
`AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine` is exactly what rules it out on an
algebraic space.

## Main results

* `AlgebraicGeometry.Space.chartRestrict_eq_appTop`: restriction of regular functions along a
  chart morphism is the map on global functions of the underlying morphism of schemes.
* `AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine`: **between affine étale charts the
  restriction map of regular functions is flat.**  This is the geometric input, Stacks 06VE(5)
  via Stacks 02GS: a morphism of étale charts is étale on the underlying schemes, an étale
  morphism is flat, and a flat morphism of affine schemes is a flat map of global functions.
* `AlgebraicGeometry.Space.bijective_baseChange_of_exact`: the commutative-algebra step.  Given
  a flat algebra `A` over `R`, an exact sequence `0 → K → G → G'` of `R`-modules, an exact
  sequence `0 → K' → G₁ → G₁'` of `A`-modules and comparison maps from the base changes which
  are bijective at `G` and at `G'`, the comparison at `K` is bijective.
* `SheafOfModules.exact_kernel_ι_val_app`: the sections of a kernel of a morphism of sheaves of
  modules are the kernel of the map on sections.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_kernel`: the base change comparison for
  `ker φ` over a chart morphism with flat restriction map, from the comparisons for `G` and
  `G'`.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`: **being cartesian on affine charts
  is stable under kernels**, with no hypothesis beyond the two modules, the flatness being
  supplied by `flat_chartRestrict_of_isAffine`.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isLimit`: the same for the left term of
  a short exact sequence of `𝒪_F`-modules.

## Implementation notes

No `@[stacks 03M1]` attribute is claimed, and no part of Stacks 03M1 is proved here.  Stacks
03M1(3) is a statement about `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6), which is
the existence of local global presentations; `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`
is the base change criterion of Stacks 03DX(2).  The two are equivalent for an algebraic space,
and that equivalence is Stacks 03DX, which needs Stacks 03DT (the fpqc sheaf condition for the
cartesian presheaf of a module) together with flatness of the chart restrictions and a finite
affine refinement of an étale covering of an affine chart — *not* Stacks 03DW; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSections`.  What is proved here is the kernel clause
*for the criterion*, together with the geometric fact that the criterion's own flatness
requirement is automatic.

`AlgebraicGeometry.Space.chartRestrict_eq_appTop` holds by `rfl`: the structure sheaf of the
small étale site of `F` is `AlgebraicGeometry.Space.structurePresheaf`, which is
`CategoryTheory.Functor.op` of the canonical functor to schemes composed with
`AlgebraicGeometry.Scheme.Γ`, and `AlgebraicGeometry.Scheme.Γ_map_op` identifies the latter's
action on morphisms with `AlgebraicGeometry.Scheme.Hom.appTop`.

`AlgebraicGeometry.Space.bijective_baseChange_of_exact` is stated with the comparison maps as
hypotheses rather than constructed, because the comparison that the application needs is
`AlgebraicGeometry.Space.sectionsBaseChange`, whose compatibility with a morphism of modules is
the already available `AlgebraicGeometry.Space.app_sectionsBaseChange`.  Both halves of its
conclusion use flatness, and they use it in its two forms: injectivity of `A ⊗ ι` for the
injectivity of the comparison (`Module.Flat.lTensor_preserves_injective_linearMap`) and
exactness of `A ⊗ ι, A ⊗ φ` for its surjectivity (`Module.Flat.lTensor_exact`).

`SheafOfModules.exact_kernel_ι_val_app` is proved from the fact that
`SheafOfModules.evaluation` preserves finite limits, through
`CategoryTheory.Limits.kernelComparison` and `ModuleCat.kernelIsoKer`, rather than from the
existing `SheafOfModules.exists_kernel_val_app`: that lemma states the same surjectivity but
only for modules in the universe `max m w` of the ring sheaf's universe `w`, because its proof
maps in a rank-one free module, and the module universe here is free.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 02GS](https://stacks.math.columbia.edu/tag/02GS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **The sections of a kernel are the kernel of the sections.**  For a morphism `b : M ⟶ N` of
sheaves of modules on a site and an object `X`, the maps on sections over `X` induced by the
inclusion of `kernel b` and by `b` form an exact pair.

Evaluation at `X` preserves finite limits, so it carries the kernel of `b` to the kernel of the
map on sections, which in `ModuleCat` is the module-theoretic kernel. -/
theorem exact_kernel_ι_val_app {M N : SheafOfModules.{m} R} (b : M ⟶ N) (X : Cᵒᵖ) :
    Function.Exact ((kernel.ι b).val.app X) (b.val.app X) := by
  set E := SheafOfModules.evaluation.{m} R X
  set e : E.obj (kernel b) ≅ ModuleCat.of (R.obj.obj X) (E.map b).hom.ker :=
    PreservesKernel.iso E b ≪≫ ModuleCat.kernelIsoKer (E.map b) with he
  have hcomp : e.hom ≫ ModuleCat.ofHom (E.map b).hom.ker.subtype = E.map (kernel.ι b) := by
    rw [he, Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  have hval : ∀ y : (kernel b).val.obj X, ((e.hom y).1 : M.val.obj X) =
      (kernel.ι b).val.app X y :=
    fun y => congrFun (congrArg (fun g => (ConcreteCategory.hom g : _ → _)) hcomp) y
  have hbij : Function.Bijective (ConcreteCategory.hom e.hom) :=
    ConcreteCategory.bijective_of_isIso _
  intro x
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨y, (hval y).symm.trans (congrArg Subtype.val hy)⟩
  · rintro ⟨y, rfl⟩
    rw [← hval y]
    exact (e.hom y).2

end SheafOfModules

namespace AlgebraicGeometry.Space

/-! ### The commutative-algebra step -/

/-- **Base change of an exact sequence along a flat algebra, read through comparison maps.**
Let `A` be a flat `R`-algebra, let `0 → K → G → G'` be an exact sequence of `R`-modules and let
`0 → K' → G₁ → G₁'` be an exact sequence of `A`-modules.  Suppose given `A`-linear comparison
maps from the base changes `A ⊗_R K`, `A ⊗_R G`, `A ⊗_R G'` to `K'`, `G₁`, `G₁'` which commute
with the two sequences.  If the comparisons at `G` and at `G'` are bijective, so is the one
at `K`.

Injectivity comes from injectivity of `A ⊗ ι`, surjectivity from exactness of `A ⊗ ι, A ⊗ φ`;
both are flatness of `A`. -/
theorem bijective_baseChange_of_exact
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    {K G G' : Type*} [AddCommGroup K] [Module R K] [AddCommGroup G] [Module R G]
    [AddCommGroup G'] [Module R G']
    {K' G₁ G₁' : Type*} [AddCommGroup K'] [Module A K'] [AddCommGroup G₁] [Module A G₁]
    [AddCommGroup G₁'] [Module A G₁']
    {ιU : K →ₗ[R] G} {φU : G →ₗ[R] G'} {ιV : K' →ₗ[A] G₁} {φV : G₁ →ₗ[A] G₁'}
    {cK : TensorProduct R A K →ₗ[A] K'} {cG : TensorProduct R A G →ₗ[A] G₁}
    {cG' : TensorProduct R A G' →ₗ[A] G₁'}
    (hιU : Function.Injective ιU) (hexU : Function.Exact ιU φU)
    (hιV : Function.Injective ιV) (hexV : Function.Exact ιV φV)
    (hsqK : ∀ z, ιV (cK z) = cG (LinearMap.lTensor A ιU z))
    (hsqG : ∀ z, φV (cG z) = cG' (LinearMap.lTensor A φU z))
    (hcG : Function.Bijective cG) (hcG' : Function.Bijective cG') :
    Function.Bijective cK := by
  refine ⟨fun z w h => ?_, fun y => ?_⟩
  · refine Module.Flat.lTensor_preserves_injective_linearMap ιU hιU (hcG.1 ?_)
    rw [← hsqK, ← hsqK, h]
  · obtain ⟨w, hw⟩ := hcG.2 (ιV y)
    have hw' : LinearMap.lTensor A φU w = 0 := by
      refine hcG'.1 ?_
      rw [← hsqG, hw, hexV.apply_apply_eq_zero y, map_zero]
    obtain ⟨z, hz⟩ := (Module.Flat.lTensor_exact A hexU w).mp hw'
    exact ⟨z, hιV (by rw [hsqK, hz, hw])⟩

/-! ### Flatness of the restriction maps between affine charts -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Restriction of regular functions along a morphism of étale charts of `F` is the map on
global functions of the underlying morphism of schemes.

The structure sheaf of the small étale site of `F` is global regular functions on the
underlying schemes, so this holds by definition. -/
theorem chartRestrict_eq_appTop {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    chartRestrict (hF := hF) f =
      ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map f)).appTop.hom := rfl

/-- **Between affine étale charts of an algebraic space the restriction map of regular
functions is flat.**

This is the geometric input of the kernel clause.  A morphism of étale charts is étale on the
underlying schemes (`AlgebraicGeometry.Space.etale_toScheme_toOver_map`), an étale morphism of
schemes is flat (Stacks 02GS), and for a flat morphism between affine schemes the induced map
of global functions is a flat ring map. -/
theorem flat_chartRestrict_of_isAffine {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    RingHom.Flat (chartRestrict (hF := hF) f) := by
  have hfl : Flat ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f)) :=
    (Etale.iff_flat_and_formallyUnramified.1 (etale_toScheme_toOver_map B S hS F f)).1
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) := hU
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)) := hV
  rw [chartRestrict_eq_appTop]
  exact HasRingHomProperty.appTop (P := @Flat) _ hfl

/-- The sections of `𝒪_F` over the smaller of two étale charts form a flat algebra over the
sections over the larger one, when both charts are affine.

This is `AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine` read through
`AlgebraicGeometry.Space.chartAlgebra`, whose algebra map is the restriction map. -/
theorem moduleFlat_chartRing_of_isAffine {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    letI := chartAlgebra (hF := hF) f
    Module.Flat (chartRing B S hS F hF U) (chartRing B S hS F hF V) :=
  flat_chartRestrict_of_isAffine f hU hV

/-! ### The base change comparison of a kernel -/

/-- **The base change comparison of a kernel.**  Let `φ : G ⟶ G'` be a morphism of
`𝒪_F`-modules and let `f : V ⟶ U` be a morphism of étale charts along which the restriction map
of regular functions is flat.  If the sections of `G` and of `G'` over `V` are the base changes
of their sections over `U`, then so are the sections of `ker φ`.

Sections take the kernel of `φ` to the kernel of the map on sections
(`SheafOfModules.exact_kernel_ι_val_app`), the comparison is compatible with the inclusion of
the kernel (`AlgebraicGeometry.Space.app_sectionsBaseChange`), and flatness carries the
resulting exact sequence through the base change. -/
theorem bijective_sectionsBaseChange_kernel {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G')
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hflat : RingHom.Flat (chartRestrict (hF := hF) f))
    (hG : Function.Bijective (sectionsBaseChange G f))
    (hG' : Function.Bijective (sectionsBaseChange G' f)) :
    Function.Bijective (sectionsBaseChange (kernel φ) f) := by
  let _ := chartAlgebra (hF := hF) f
  have _ : Module.Flat (chartRing B S hS F hF U) (chartRing B S hS F hF V) := hflat
  exact bijective_baseChange_of_exact
    (ιU := ((kernel.ι φ).val.app (op U)).hom) (φU := (φ.val.app (op U)).hom)
    (ιV := ((kernel.ι φ).val.app (op V)).hom) (φV := (φ.val.app (op V)).hom)
    (SheafOfModules.kernel_ι_val_app_injective φ (op U))
    (SheafOfModules.exact_kernel_ι_val_app φ (op U))
    (SheafOfModules.kernel_ι_val_app_injective φ (op V))
    (SheafOfModules.exact_kernel_ι_val_app φ (op V))
    (app_sectionsBaseChange (kernel.ι φ) f) (app_sectionsBaseChange φ f) hG hG'

/-- **Being cartesian on affine charts is stable under kernels.**  If the sections of `G` and of
`G'` over every affine étale chart are the base change of their sections over any larger affine
étale chart, then the same holds for `ker φ`.

There is no flatness hypothesis: it is discharged by
`AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine`, since both charts are affine and a
morphism of étale charts is étale.  This is the kernel clause of Stacks 03M1(3) for the base
change criterion of Stacks 03DX(2); see the implementation notes for why it is not that clause
of Stacks 03M1 itself. -/
theorem isCartesianOnAffineCharts_kernel {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G')
    (hG : IsCartesianOnAffineCharts G) (hG' : IsCartesianOnAffineCharts G') :
    IsCartesianOnAffineCharts (kernel φ) :=
  fun U V hU hV f => bijective_sectionsBaseChange_kernel φ f
    (flat_chartRestrict_of_isAffine f hU hV) (hG U V hU hV f) (hG' U V hU hV f)

/-- **The left term of a short exact sequence of `𝒪_F`-modules is cartesian on affine charts as
soon as the other two are.**  Here `ι : K ⟶ G` is asked to exhibit `K` as a kernel of
`φ : G ⟶ G'`, which for a short exact sequence `0 → K → G → G' → 0` it does.

This is `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel` transported along the
canonical isomorphism `K ≅ ker φ` by
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts.of_iso`. -/
theorem isCartesianOnAffineCharts_of_isLimit {K G G' : Modules.{u, m} B S hS F hF} {ι : K ⟶ G}
    {φ : G ⟶ G'} (h : ι ≫ φ = 0) (hl : IsLimit (KernelFork.ofι ι h))
    (hG : IsCartesianOnAffineCharts G) (hG' : IsCartesianOnAffineCharts G') :
    IsCartesianOnAffineCharts K :=
  IsCartesianOnAffineCharts.of_iso
    (IsLimit.conePointUniqueUpToIso hl (kernelIsKernel φ)).symm
    (isCartesianOnAffineCharts_kernel φ hG hG')

end AlgebraicGeometry.Space

end

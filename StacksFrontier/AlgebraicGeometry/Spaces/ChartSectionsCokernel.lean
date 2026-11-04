module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison

/-!
# The base change comparison of a cokernel

Let `F` be an algebraic space, let `φ : G ⟶ G'` be a morphism of `𝒪_F`-modules on the small
étale site of `F`, let `π : G' ⟶ T` be a morphism killing the image of `φ`, and let `f : V ⟶ U`
be a morphism of étale charts.  This file proves that the base change comparison
`AlgebraicGeometry.Space.sectionsBaseChange`

`𝒪_F(V) ⊗_{𝒪_F(U)} T(U) ⟶ T(V)`

is bijective as soon as it is for `G'`, surjective for `G`, and the sections of `T` over the two
charts are the cokernels of the maps on sections.

The arithmetic is the exact mirror image of the kernel clause in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel`, and the two differ in precisely one
way, which is worth recording because it is the shape of the whole of Stacks 03M1.  Sections of
a sheaf of modules are left exact but not right exact — `SheafOfModules.evaluation` preserves
finite limits and does *not* preserve finite colimits, since a cokernel of sheaves is the
sheafification of the cokernel of presheaves.  So for the kernel the sections-level input is
free and flatness of the restriction map is what the proof needs
(`AlgebraicGeometry.Space.bijective_baseChange_of_exact`), whereas for the cokernel flatness is
*not* needed at all — tensoring is right exact over any base — and what the proof needs instead
is the sections-level input, which is therefore carried as a hypothesis.

That hypothesis is not a technicality but the whole mathematical content, and it is false over a
general chart: surjectivity of `π` on the sections over a chart `W` is the vanishing of the
first étale cohomology on `W` of the image of `φ`, which holds for `W` affine (Stacks 03DW) and
fails in general.  It is stated here only over affine charts for that reason, which is also the
only form in which `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` consumes it.

## Main results

* `AlgebraicGeometry.Space.bijective_baseChange_of_rightExact`: the commutative-algebra step.
  Given an `R`-algebra `A`, a right exact sequence `G → G' → T → 0` of `R`-modules, a right
  exact sequence `G₁ → G₁' → T₁ → 0` of `A`-modules and comparison maps from the base changes
  which commute with the two sequences, the comparison at `T` is bijective as soon as the one at
  `G'` is bijective and the one at `G` is surjective.  **No flatness hypothesis**: the
  surjections make right exactness of the tensor product sufficient.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_cokernel`: the base change comparison of
  `T` over a chart morphism, from the comparisons for `G` and `G'` together with the
  sections-level cokernel property of `π` over the two charts.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel`: **being cartesian on affine
  charts is stable under cokernels, granted that the cokernel is computed on the sections over
  affine charts.**

## Implementation notes

No `@[stacks]` attribute is claimed and no part of Stacks 03M1 is proved here.  Stacks 03M1(3)
is a statement about `SheafOfModules.IsQuasicoherentOnSite`, the existence of local global
presentations of Stacks 03DL(6), while
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` is the base change criterion of Stacks
03DX(2); passing between the two is Stacks 03DX, which is not available in the tree.  What is
proved here is the cokernel clause *for the criterion*, and only granted its sections-level
input.

`AlgebraicGeometry.Space.bijective_sectionsBaseChange_cokernel` takes `π` as a bare morphism of
modules with the two sections-level hypotheses, rather than a cokernel cofork of `φ` or
`CategoryTheory.Limits.cokernel φ`: the hypotheses already carry everything the proof uses, and
`CategoryTheory.Limits.cokernel φ` does not exist at a module universe independent of the
universe of the schemes, because cokernels of sheaves of modules need sheafification of
`AddCommGrpCat`-valued presheaves at the module universe.  Keeping `π` abstract therefore keeps
the module universe free, as it is in the rest of the chart-sections files, and the statements
apply to `CategoryTheory.Limits.cokernel φ` where that exists.

The right exactness used is Mathlib's `lTensor_exact` and `LinearMap.lTensor_surjective`, which
is why the flatness hypothesis of the kernel clause is absent; the kernel clause cannot avoid
it, see the module documentation there.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

/-! ### The commutative-algebra step -/

/-- **Base change of a right exact sequence, read through comparison maps.**  Let `A` be an
`R`-algebra, let `G → G' → T → 0` be a right exact sequence of `R`-modules and let
`G₁ → G₁' → T₁ → 0` be a right exact sequence of `A`-modules.  Suppose given `A`-linear
comparison maps from the base changes `A ⊗_R G`, `A ⊗_R G'`, `A ⊗_R T` to `G₁`, `G₁'`, `T₁`
which commute with the two sequences.  If the comparison at `G'` is bijective and the one at `G`
is surjective, then the one at `T` is bijective.

There is no flatness hypothesis, in contrast with
`AlgebraicGeometry.Space.bijective_baseChange_of_exact`: surjectivity comes from surjectivity of
`A ⊗ πU`, and injectivity from exactness of `A ⊗ φU, A ⊗ πU`, both of which are right exactness
of the tensor product and need nothing of `A`. -/
theorem bijective_baseChange_of_rightExact
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {G G' T : Type*} [AddCommGroup G] [Module R G] [AddCommGroup G'] [Module R G']
    [AddCommGroup T] [Module R T]
    {G₁ G₁' T₁ : Type*} [AddCommGroup G₁] [Module A G₁] [AddCommGroup G₁'] [Module A G₁']
    [AddCommGroup T₁] [Module A T₁]
    {φU : G →ₗ[R] G'} {πU : G' →ₗ[R] T} {φV : G₁ →ₗ[A] G₁'} {πV : G₁' →ₗ[A] T₁}
    {cG : TensorProduct R A G →ₗ[A] G₁} {cG' : TensorProduct R A G' →ₗ[A] G₁'}
    {cT : TensorProduct R A T →ₗ[A] T₁}
    (hπU : Function.Surjective πU) (hexU : Function.Exact φU πU)
    (hπV : Function.Surjective πV) (hexV : Function.Exact φV πV)
    (hsqG : ∀ z, φV (cG z) = cG' (LinearMap.lTensor A φU z))
    (hsqG' : ∀ z, πV (cG' z) = cT (LinearMap.lTensor A πU z))
    (hcG : Function.Surjective cG) (hcG' : Function.Bijective cG') :
    Function.Bijective cT := by
  have hexA : Function.Exact (LinearMap.lTensor A φU) (LinearMap.lTensor A πU) :=
    _root_.lTensor_exact A hexU hπU
  refine ⟨(injective_iff_map_eq_zero cT).2 fun w hw => ?_, fun t => ?_⟩
  · obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective A hπU w
    obtain ⟨x, hx⟩ := (hexV (cG' z)).mp ((hsqG' z).trans hw)
    obtain ⟨s, hs⟩ := hcG x
    have hz : z = LinearMap.lTensor A φU s := hcG'.1 (by rw [← hsqG, hs, hx])
    rw [hz]
    exact hexA.apply_apply_eq_zero s
  · obtain ⟨y, hy⟩ := hπV t
    obtain ⟨z, hz⟩ := hcG'.2 y
    exact ⟨LinearMap.lTensor A πU z, by rw [← hsqG' z, hz, hy]⟩

/-! ### The base change comparison of a cokernel -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The base change comparison of a cokernel.**  Let `φ : G ⟶ G'` and `π : G' ⟶ T` be
morphisms of `𝒪_F`-modules and let `f : V ⟶ U` be a morphism of étale charts.  Assume that over
each of the two charts the sections of `T` are the cokernel of the map on sections, that is,
that `π` is surjective on sections there with kernel the image of `φ`.  If the sections of `G'`
over `V` are the base change of its sections over `U`, and those of `G` are at least generated
by them, then the sections of `T` over `V` are the base change of its sections over `U`.

No flatness of the restriction map is required.  The comparison is compatible with a morphism of
modules by `AlgebraicGeometry.Space.app_sectionsBaseChange`, and right exactness of the tensor
product carries the two sections-level cokernels into one another. -/
theorem bijective_sectionsBaseChange_cokernel {G G' T : Modules.{u, m} B S hS F hF}
    (φ : G ⟶ G') (π : G' ⟶ T) {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hπU : Function.Surjective (π.val.app (op U)))
    (hexU : Function.Exact (φ.val.app (op U)) (π.val.app (op U)))
    (hπV : Function.Surjective (π.val.app (op V)))
    (hexV : Function.Exact (φ.val.app (op V)) (π.val.app (op V)))
    (hG : Function.Surjective (sectionsBaseChange G f))
    (hG' : Function.Bijective (sectionsBaseChange G' f)) :
    Function.Bijective (sectionsBaseChange T f) := by
  let _ := chartAlgebra (hF := hF) f
  exact bijective_baseChange_of_rightExact
    (φU := (φ.val.app (op U)).hom) (πU := (π.val.app (op U)).hom)
    (φV := (φ.val.app (op V)).hom) (πV := (π.val.app (op V)).hom)
    hπU hexU hπV hexV
    (app_sectionsBaseChange φ f) (app_sectionsBaseChange π f) hG hG'

/-- **Being cartesian on affine charts is stable under cokernels, granted that the cokernel is
computed on the sections over affine charts.**  If `π : G' ⟶ T` is surjective on the sections
over every affine étale chart with kernel there the image of `φ : G ⟶ G'`, and if `G` and `G'`
are cartesian on affine charts, then so is `T`.

Unlike `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`, which is unconditional
because sections take kernels to kernels, this clause needs the sections-level hypothesis: a
cokernel of sheaves of modules is the sheafification of the cokernel of presheaves, so its
sections over a chart are not the cokernel of the sections.  Over an affine chart that
discrepancy is the first étale cohomology of the image of `φ`, which vanishes by Stacks 03DW;
that vanishing is not available in the tree and is exactly what the two hypotheses `hπ` and
`hex` package.  Flatness of the restriction maps, the geometric input of the kernel clause, is
not used. -/
theorem isCartesianOnAffineCharts_cokernel {G G' T : Modules.{u, m} B S hS F hF}
    (φ : G ⟶ G') (π : G' ⟶ T)
    (hπ : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective (π.val.app (op U)))
    (hex : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Exact (φ.val.app (op U)) (π.val.app (op U)))
    (hG : IsCartesianOnAffineCharts G) (hG' : IsCartesianOnAffineCharts G') :
    IsCartesianOnAffineCharts T :=
  fun U V hU hV f => bijective_sectionsBaseChange_cokernel φ π f
    (hπ U hU) (hex U hU) (hπ V hV) (hex V hV) (hG U V hU hV f).2 (hG' U V hU hV f)

end AlgebraicGeometry.Space

end

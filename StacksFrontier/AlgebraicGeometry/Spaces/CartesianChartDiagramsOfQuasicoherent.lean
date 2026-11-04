module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent

/-!
# The sections of a presented module over an affine chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `M` be
a quasi-coherent `𝒪_F`-module with a global presentation `P` in the sense of
`SheafOfModules.Presentation`: a family of generating sections, and a family of sections
generating the kernel of the map they induce.  Over an *affine* étale chart the sections of `M`
are then the cokernel of the sections of the presenting map, which is the sections-level right
exactness that a cokernel of sheaves of modules does not have over a general chart.

The surjectivity of the generators and of the relations on the sections over an affine chart is
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isCartesianOnAffineCharts`, by faithfully
flat descent and with no cohomology; the two modules it needs cartesian are a free module
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_free`) and, for the relations, the kernel of
the generating map (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`).

## Main results

* `AlgebraicGeometry.Space.nonempty_linearEquiv_baseChange_of_rightExact`: the algebra step.
  Given right exact sequences `G → G' → T → 0` of `R`-modules and `G₁ → G₁' → T₁ → 0` of
  `A`-modules and comparison maps from the base changes which commute with the first map, the
  base change of `T` is isomorphic to `T₁` as soon as the comparison at `G'` is bijective and
  the one at `G` is surjective.  The comparison at `T` is *constructed*, not assumed.
* `AlgebraicGeometry.Space.surjective_generators_app_of_isAffine` and
  `AlgebraicGeometry.Space.surjective_relations_app_of_isAffine`: the two surjectivities.
* `AlgebraicGeometry.Space.exact_app_of_presentation`: **the sections of a presented
  quasi-coherent module over an affine étale chart are the cokernel of the sections of the
  presenting map.**

## Implementation notes

`AlgebraicGeometry.Space.bijective_baseChange_of_rightExact` takes the comparison at `T` as an
input and concludes that it is bijective.  The variant proved here constructs it, which is what
a consumer comparing two modules on *different* algebraic spaces needs: there the comparison is
not given by `AlgebraicGeometry.Space.sectionsBaseChange` and there is nothing to supply.  It is
well defined because `πV ∘ cG'` kills the kernel of `LinearMap.lTensor A πU`, which right
exactness of the tensor product identifies with the range of `LinearMap.lTensor A φU`, and the
first commuting square carries that range into the range of `φV`.

The presenting map is `P.relations.π ≫ kernel.ι P.generators.π`, the relations followed by the
inclusion of the kernel of the generators; its exactness with the generators is
`SheafOfModules.exact_kernel_ι_val_app`, which holds over every object, together with
surjectivity of the relations over an affine chart, which is what fills the kernel.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u m

namespace AlgebraicGeometry.Space

/-! ### The algebra step, with the comparison constructed -/

/-- **The base change of the right-hand term of a right exact sequence, with the comparison
constructed rather than assumed.**

Let `A` be an `R`-algebra, let `G → G' → T → 0` be a right exact sequence of `R`-modules and
`G₁ → G₁' → T₁ → 0` one of `A`-modules, and let comparison maps from the base changes of `G`
and `G'` to `G₁` and `G₁'` commute with the first map of each sequence.  If the comparison at
`G'` is bijective and the one at `G` is surjective, then the base change of `T` is isomorphic
to `T₁`.

This is `AlgebraicGeometry.Space.bijective_baseChange_of_rightExact` with its comparison at `T`
supplied: `πV ∘ cG'` vanishes on the kernel of `LinearMap.lTensor A πU`, so it descends along
that surjection. -/
theorem nonempty_linearEquiv_baseChange_of_rightExact
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {G G' T : Type*} [AddCommGroup G] [Module R G] [AddCommGroup G'] [Module R G']
    [AddCommGroup T] [Module R T]
    {G₁ G₁' T₁ : Type*} [AddCommGroup G₁] [Module A G₁] [AddCommGroup G₁'] [Module A G₁']
    [AddCommGroup T₁] [Module A T₁]
    {φU : G →ₗ[R] G'} {πU : G' →ₗ[R] T} {φV : G₁ →ₗ[A] G₁'} {πV : G₁' →ₗ[A] T₁}
    {cG : TensorProduct R A G →ₗ[A] G₁} {cG' : TensorProduct R A G' →ₗ[A] G₁'}
    (hπU : Function.Surjective πU) (hexU : Function.Exact φU πU)
    (hπV : Function.Surjective πV) (hexV : Function.Exact φV πV)
    (hsqG : ∀ z, φV (cG z) = cG' (LinearMap.lTensor A φU z))
    (hcG : Function.Surjective cG) (hcG' : Function.Bijective cG') :
    Nonempty (TensorProduct R A T ≃ₗ[A] T₁) := by
  -- the `A`-linear spelling of `LinearMap.lTensor A πU`, whose kernel is an `A`-submodule
  have hptπ : ∀ z : TensorProduct R A G', πU.baseChange A z = LinearMap.lTensor A πU z :=
    fun _ => rfl
  have hexA : Function.Exact (LinearMap.lTensor A φU) (LinearMap.lTensor A πU) :=
    _root_.lTensor_exact A hexU hπU
  have hsurjA : Function.Surjective (πU.baseChange A) := by
    intro t
    obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective A hπU t
    exact ⟨z, (hptπ z).trans hz⟩
  have hker : LinearMap.ker (πU.baseChange A) ≤ LinearMap.ker (πV ∘ₗ cG') := by
    intro z hz
    obtain ⟨s, hs⟩ := (hexA z).mp ((hptπ z).symm.trans (LinearMap.mem_ker.mp hz))
    refine LinearMap.mem_ker.2 ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← hs, ← hsqG s]
    exact hexV.apply_apply_eq_zero _
  set e := LinearMap.quotKerEquivOfSurjective (πU.baseChange A) hsurjA with he
  refine ⟨LinearEquiv.ofBijective
    ((LinearMap.ker (πU.baseChange A)).liftQ (πV ∘ₗ cG') hker ∘ₗ e.symm.toLinearMap)
    (bijective_baseChange_of_rightExact hπU hexU hπV hexV hsqG (fun z => ?_) hcG hcG')⟩
  have hz : e.symm (LinearMap.lTensor A πU z) = Submodule.Quotient.mk z := by
    refine e.symm_apply_eq.2 ?_
    rw [he, LinearMap.quotKerEquivOfSurjective_apply_mk, hptπ]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [hz, Submodule.liftQ_apply]
  rfl

/-! ### The sections of a presented module over an affine chart -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The generating sections of a global presentation are surjective on the sections over an
affine étale chart.**  A free module is cartesian on affine charts and so is a quasi-coherent
module, and an epimorphism between two such is surjective on the sections over an affine
chart. -/
theorem surjective_generators_app_of_isAffine {M : Modules.{u, u} B S hS F hF}
    (hM : M.IsQuasicoherentOnSite) (P : M.Presentation) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (P.generators.π.val.app (op W)) :=
  surjective_val_app_of_epi_of_isCartesianOnAffineCharts P.generators.π inferInstance
    (isCartesianOnAffineCharts_free _)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M hM) W hW

/-- **The relations of a global presentation are surjective on the sections of the kernel of the
generators, over an affine étale chart.**  The kernel of the generating map is cartesian on
affine charts by the kernel clause, which is unconditional, and the relations are an
epimorphism onto it from a free module. -/
theorem surjective_relations_app_of_isAffine {M : Modules.{u, u} B S hS F hF}
    (hM : M.IsQuasicoherentOnSite) (P : M.Presentation) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (P.relations.π.val.app (op W)) :=
  surjective_val_app_of_epi_of_isCartesianOnAffineCharts P.relations.π inferInstance
    (isCartesianOnAffineCharts_free _)
    (isCartesianOnAffineCharts_kernel P.generators.π (isCartesianOnAffineCharts_free _)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M hM)) W hW

/-- **The sections of a presented quasi-coherent module over an affine étale chart are the
cokernel of the sections of the presenting map.**

The presenting map is the relations followed by the inclusion of the kernel of the generators.
Exactness of that inclusion with the generators holds over every object of the site, by
`SheafOfModules.exact_kernel_ι_val_app`; what the affineness supplies is that the relations fill
the kernel, which is
`AlgebraicGeometry.Space.surjective_relations_app_of_isAffine`. -/
theorem exact_app_of_presentation {M : Modules.{u, u} B S hS F hF}
    (hM : M.IsQuasicoherentOnSite) (P : M.Presentation) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Exact ((P.relations.π ≫ kernel.ι P.generators.π).val.app (op W))
      (P.generators.π.val.app (op W)) := by
  have h0 := SheafOfModules.exact_kernel_ι_val_app P.generators.π (op W)
  have hrel := surjective_relations_app_of_isAffine B S hS F hF hM P W hW
  intro y
  refine ⟨fun hy => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := (h0 y).mp hy
    obtain ⟨x, hx⟩ := hrel z
    refine ⟨x, ?_⟩
    have hcomp : (P.relations.π ≫ kernel.ι P.generators.π).val.app (op W) x =
        (kernel.ι P.generators.π).val.app (op W) (P.relations.π.val.app (op W) x) := rfl
    rw [hcomp, hx, hz]
  · rintro ⟨x, rfl⟩
    refine (h0 _).mpr ⟨P.relations.π.val.app (op W) x, ?_⟩
    rfl

end AlgebraicGeometry.Space

end

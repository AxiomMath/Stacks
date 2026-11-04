module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares

/-!
# `QCoh(𝒪_𝒳)` is abelian, and its kernels on flat objects

For an algebraic stack `𝒳`, `QCoh(𝒪_𝒳)` is coreflective in the weak Serre subcategory
`LQCoh^fbc(𝒪_𝒳)` of `Mod(𝒪_𝒳)` (**Stacks 0771** part (2), **Stacks 0778**), and the coreflector,
the coherator `Q`, is right exact there (**Stacks 0779** part (3)).  So `QCoh(𝒪_𝒳)` is abelian
(**Stacks 06WV** part (2)), by `CategoryTheory.DeltaFunctor.abelianOfCoreflectionOnClass`.

The kernel of a map `φ : 𝓕 ⟶ 𝓖` of quasi-coherent modules is `Q(Ker φ)`, the kernel being taken
in `Mod(𝒪_𝒳)` (**Stacks 0GQL** part (3)).  Its sections at a flat object `x` are those of
`Ker φ`, that is the kernel of `φ` on sections at `x`: the adjunction map `Q(Ker φ) ⟶ Ker φ` has
parasitic kernel and cokernel by **Stacks 0779** part (2), and so is bijective on sections at
`x`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.instAbelianQuasicoherentModules`: the abelian
  structure on `QCoh(𝒪_𝒳)` (**Stacks 0GQL**, the abelian assertion).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.injective_and_range_eq_ker_of_isLimit_kernelFork`:
  for any kernel of `φ` in `QCoh(𝒪_𝒳)` and any flat object `x`, the sections of the kernel at `x`
  map injectively onto the kernel of `φ` on sections at `x`.

## Implementation notes

The weak Serre subcategory `LQCoh^fbc(𝒪_𝒳)` is the one attached to the big étale site
`AlgebraicGeometry.associatedBigEtaleSite B` of the big fppf site, which has the same cutoff.  The
abelian structure only enters through its kernels, cokernels and exactness, which do not depend on
that choice.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0GQL**: `QCoh(𝒪_𝒳)` is abelian, for every algebraic stack `𝒳` (also **Stacks 06WV**
part (2)). It is coreflective in the weak Serre subcategory `LQCoh^fbc(𝒪_𝒳)` of `Mod(𝒪_𝒳)`, with
the coherator, right exact there, as coreflector. -/
@[stacks 0GQL "the category QCoh(𝒪_𝒳) is abelian, for every algebraic stack 𝒳"]
instance instAbelianQuasicoherentModules : Abelian (quasicoherentModules B S hS 𝒳) :=
  haveI := preservesFiniteColimits_lqcohSheafFbc_ι_comp B (associatedBigEtaleSite B) rfl S hS 𝒳
    (coheratorAdjunction B S hS 𝒳)
  abelianQuasicoherentModulesOfInputs B S hS (associatedBigEtaleSite B) rfl
    (hasSeparator_quasicoherentModules B S hS 𝒳)
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B (associatedBigEtaleSite B) rfl S hS 𝒳)

/-- **Sections of a kernel of modules.** The kernel of a map of modules on the fppf site of an
algebraic stack is computed objectwise: at every object, its sections map injectively onto the
kernel of the map on sections. -/
theorem kernel_ι_app_injective_and_range {M N : Stack.fppfModules B S hS 𝒳} (g : M ⟶ N)
    (x : 𝒳.val.val.obj) :
    Function.Injective ((kernel.ι g).val.app (op x)).hom ∧
      LinearMap.range ((kernel.ι g).val.app (op x)).hom =
        LinearMap.ker (g.val.app (op x)).hom := by
  let G := SheafOfModules.forget
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) ⋙
    PresheafOfModules.evaluation _ (op x)
  have hl : IsLimit ((KernelFork.ofι (kernel.ι g) (kernel.condition g)).map G) :=
    KernelFork.mapIsLimit _ (kernelIsKernel g) G
  have hE : (ShortComplex.mk _ _
      ((KernelFork.ofι (kernel.ι g) (kernel.condition g)).map_condition G)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hl
  exact ⟨(ModuleCat.mono_iff_injective _).1 (mono_of_isLimit_fork hl), hE.moduleCat_range_eq_ker⟩

/-- **The kernel of a map of quasi-coherent modules, on a flat object.**  For a map
`φ : 𝓕 ⟶ 𝓖` in `QCoh(𝒪_𝒳)`, a kernel of `φ` in `QCoh(𝒪_𝒳)`, and an object `x` of `𝒳` which is
flat, the sections of the kernel at `x` map injectively onto the kernel of `φ` on sections at
`x`.  The kernel is `Q(Ker φ)` with `Ker φ` computed in `Mod(𝒪_𝒳)`, and the adjunction map
`Q(Ker φ) ⟶ Ker φ` is bijective on sections at a flat object by **Stacks 0779** part (2). -/
theorem injective_and_range_eq_ker_of_isLimit_kernelFork
    {F G : quasicoherentModules B S hS 𝒳} (φ : F ⟶ G) {c : KernelFork φ} (hc : IsLimit c)
    (x : 𝒳.val.val.obj) (hx : flatObject B S hS 𝒳.val x) :
    Function.Injective (c.ι.hom.val.app (op x)).hom ∧
      LinearMap.range (c.ι.hom.val.app (op x)).hom =
        LinearMap.ker (φ.hom.val.app (op x)).hom := by
  let E := associatedBigEtaleSite B
  have h : E.cutoff = B.cutoff := rfl
  have hpar := isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳 E h
  let adj := coheratorAdjunction B S hS 𝒳
  have := preservesFiniteColimits_lqcohSheafFbc_ι_comp B E h S hS 𝒳 adj
  have := adj.right_adjoint_additive
  let i := quasicoherentInclusion B S hS 𝒳
  let L := lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
  let T : ShortComplex (quasicoherentModules B S hS 𝒳) := ShortComplex.mk c.ι φ c.condition
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel _
    (hc.ofIsoLimit (Fork.ext (Iso.refl _) (Category.id_comp _)))
  have : Mono T.f := mono_of_isLimit_fork hc
  have hQk := DeltaFunctor.isIso_map_coreflectionComparison_of_exact adj L
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) hT
  let k := DeltaFunctor.coreflectionComparison (i := i) T
  let K := (DeltaFunctor.coreflectionKernelSequence (i := i) T).X₁
  have hK : L K := DeltaFunctor.prop_coreflectionKernelSequence_X₁ L
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) T
  let t := adj.homEquiv _ _ k
  have hfac : i.map t ≫ adj.counit.app K = k :=
    (adj.homEquiv_counit _ _ t).symm.trans ((adj.homEquiv _ _).symm_apply_apply k)
  have : IsIso t := by
    dsimp only [t]
    rw [adj.homEquiv_unit]
    infer_instance
  have : IsIso (i.map t).val := (SheafOfModules.forget _).map_isIso (i.map t)
  have h1 : Function.Bijective ((i.map t).val.app (op x)) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    exact (PresheafOfModules.evaluation _ (op x)).map_isIso (i.map t).val
  have h2 : Function.Bijective ((adj.counit.app K).val.app (op x)) :=
    isIso_app_of_isParasitic_kernel_cokernel B S hS _ (hpar _ hK).1 (hpar _ hK).2 x hx
  have hk : Function.Bijective (k.val.app (op x)) := by
    rw [← hfac, SheafOfModules.comp_val, PresheafOfModules.comp_app, CategoryTheory.hom_comp]
    exact h2.comp h1
  obtain ⟨hinj, hrange⟩ := kernel_ι_app_injective_and_range B S hS 𝒳 (i.map φ) x
  have hcomp : c.ι.hom.val.app (op x) =
      k.val.app (op x) ≫ (kernel.ι (i.map φ)).val.app (op x) := by
    rw [← PresheafOfModules.comp_app, ← SheafOfModules.comp_val]
    exact congrArg (fun g => g.val.app (op x))
      (DeltaFunctor.coreflectionComparison_ι (i := i) T).symm
  rw [hcomp]
  refine ⟨hinj.comp hk.1, ?_⟩
  rwa [ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 hk.2)]

end AlgebraicGeometry.Stack.AlgebraicStacks

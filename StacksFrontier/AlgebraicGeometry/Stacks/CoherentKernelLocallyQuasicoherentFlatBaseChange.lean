module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentAbelianLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafWeakSerre

/-!
# The kernel of a map of coherent modules is in `LQCoh^fbc` (Stacks 0GR9 (3))

Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of coherent
`𝒪_𝒳`-modules. Part (3) of **Stacks 0GR9** says that the kernel `Ker φ` computed in
`Mod(𝒪_𝒳)` may not be coherent, but it lies in `LQCoh^fbc(𝒪_𝒳)`, and `Q(Ker φ)` is coherent and
is the kernel of `φ` in `Coh(𝒪_𝒳)`.

`LQCoh^fbc(𝒪_𝒳)` is, as in the proof of **Stacks 0765**, the full subcategory of
`Mod(𝒳_étale, 𝒪_𝒳)` of the modules which are locally quasi-coherent (**Stacks 06WJ**,
`AlgebraicGeometry.Stack.IsLocallyQuasicoherent`) and have the flat base change property
(**Stacks 0762**), read with the inverse image of sheaves of modules on the small étale sites
as the source reads it (`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`). The kernel
computed in the fppf modules is an étale sheaf with the same underlying presheaf of modules
(`AlgebraicGeometry.Stack.etaleModuleOfFppf`).

## The argument

* Local quasi-coherence: the kernel is cartesian along every arrow over an étale morphism of
  affine schemes, `ℱ` and `𝒢` being quasi-coherent hence cartesian between affine objects, so the
  cartesian criterion applies
  (`AlgebraicGeometry.Stack.isLocallyQuasicoherent_kernel_of_isCartesianBetweenAffines`).
* Flat base change: `ℱ` and `𝒢` have it, being cartesian between affine objects
  (`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isCartesianBetweenAffines`). The
  kernel computed in the fppf modules is the kernel computed in the étale modules, kernels of
  sheaves of modules being computed on presheaves; and the étale modules with the flat base
  change property are closed under kernels, the inverse image `a_{small}^*` along a flat morphism
  being left exact (Stacks 0764 (2),
  `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_kernel`).
* `Q(Ker φ)` coherent and the kernel of `φ` in `Coh(𝒪_𝒳)`:
  `AlgebraicGeometry.Stack.isCoherent_coherator_kernel_and_isLimit`.

## Main results

* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_kernel_of_isCartesianBetweenAffines`:
  the kernel of a map of fppf modules cartesian between affine objects has the flat base change
  property as an étale module.
* `AlgebraicGeometry.Stack.kernel_mem_lqcohFbc_and_isCoherent_coherator_kernel`:
  **Stacks 0GR9 (3)**.

## References

* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

section Kernel

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Reading an fppf sheaf of modules as an étale sheaf of modules, as a functor: neither the
underlying presheaves of modules nor the maps change. -/
def etaleModuleOfFppfFunctor :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl) ⥤
      SheafOfModules.{u}
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) where
  obj F := etaleModuleOfFppf B S hS p hp F
  map f := ⟨f.val⟩

/-- Reading fppf sheaves of modules as étale sheaves of modules preserves zero morphisms. -/
instance : (etaleModuleOfFppfFunctor B S hS p hp).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **The kernel computed in the fppf modules is the kernel computed in the étale modules**:
reading fppf sheaves as étale sheaves preserves kernels, both being computed on presheaves of
modules. -/
instance {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    (φ : F ⟶ G) : PreservesLimit (parallelPair φ 0) (etaleModuleOfFppfFunctor B S hS p hp) :=
  have : PreservesLimit (parallelPair φ 0)
      (etaleModuleOfFppfFunctor B S hS p hp ⋙ SheafOfModules.forget _) :=
    preservesLimit_of_preserves_limit_cone (kernelIsKernel φ)
      (isLimitOfPreserves (SheafOfModules.forget _) (kernelIsKernel φ))
  preservesLimit_of_reflects_of_preserves _ (SheafOfModules.forget _)

/-- **The kernel of a map of fppf modules cartesian between affine objects has the flat base
change property** (Stacks 0762) as an étale module, in the source's reading on sheaves. -/
theorem hasFlatBaseChangePropertySheaf_kernel_of_isCartesianBetweenAffines
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp B.topology le_rfl)}
    (hF : IsCartesianBetweenAffines hp F) (hG : IsCartesianBetweenAffines hp G) (φ : F ⟶ G) :
    HasFlatBaseChangePropertySheafUnivLE.{u, v, w, u} B E h S hS p hp
      (etaleModuleOfFppf B S hS p hp (kernel φ)) :=
  hasFlatBaseChangePropertySheafUnivLE_of_iso B E h S hS p hp
    (PreservesKernel.iso (etaleModuleOfFppfFunctor B S hS p hp) φ).symm
    (hasFlatBaseChangePropertySheaf_kernel B E h S hS p hp
      (fun φ' hflat => preservesFiniteLimits_sheafifiedPullbackComparison B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) φ' hflat)
      ((etaleModuleOfFppfFunctor B S hS p hp).map φ)
      (hasFlatBaseChangePropertySheaf_of_isCartesianBetweenAffines B E h S hS p hp F hF)
      (hasFlatBaseChangePropertySheaf_of_isCartesianBetweenAffines B E h S hS p hp G hG))

end Kernel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

attribute [local instance] FlatFppf.hasSheafify_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of coherent
`𝒪_𝒳`-modules, and let `Ker φ` be its kernel computed in `Mod(𝒪_𝒳)`. Then

* `Ker φ` is in `LQCoh^fbc(𝒪_𝒳)`: read as an étale sheaf of modules, it is locally
  quasi-coherent (Stacks 06WJ) and has the flat base change property (Stacks 0762, with the
  inverse image of sheaves of modules on the small étale sites); and
* `Q(Ker φ)` is coherent and `Q(Ker φ) ⟶ Ker φ ⟶ ℱ` is a kernel of `φ` in `Coh(𝒪_𝒳)`.

Here `Q = g_!g^{-1}` with its counit is the coherator: composing with `Q(K) ⟶ K` is a bijection on
maps out of quasi-coherent modules
(`AlgebraicGeometry.Stack.FlatFppf.bijective_comp_coheratorCounit`). The source's remark that
`Ker φ` may not be coherent is not part of the assertion. The small étale sites are those of a
big étale site `E` with the same cutoff as the big fppf site `B`. -/
@[stacks 0GR9 "part (3): the kernel Ker(φ) computed in Mod(O_X) of a map of coherent modules is \
  in LQCoh^fbc(O_X) -- locally quasi-coherent and with the flat base change property, the latter \
  read with the inverse image of sheaves of modules as in the source -- and Q(Ker φ) is coherent \
  and is the kernel of φ in Coh(O_X)"]
theorem kernel_mem_lqcohFbc_and_isCoherent_coherator_kernel
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : _root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)}
    (hF : IsCoherent B S hS 𝒳 F) (hG : IsCoherent B S hS 𝒳 G) (φ : F ⟶ G) :
    (IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (kernel φ).val ∧
      HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u} B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids
        (etaleModuleOfFppf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (kernel φ))) ∧
    ∃ hK : IsCoherent B S hS 𝒳
        ((FlatFppf.lowerShriekInverseImageCoherator B S hS 𝒳).obj (kernel φ)),
      Nonempty (IsLimit (KernelFork.ofι
        (f := ((coherentModules.{u, u, w} B S hS 𝒳).homMk φ : (⟨F, hF⟩ : Coh B S hS 𝒳) ⟶ ⟨G, hG⟩))
        ((coherentModules.{u, u, w} B S hS 𝒳).homMk
          ((FlatFppf.coheratorCounit B S hS 𝒳).app (kernel φ) ≫ kernel.ι φ) :
            (⟨_, hK⟩ : Coh B S hS 𝒳) ⟶ ⟨F, hF⟩)
        (by ext1; exact (FlatFppf.isRelKernel_coherator_kernel B S hS 𝒳 φ).1))) := by
  have hFc := isCartesianBetweenAffines_of_isQuasicoherentOnSite 𝒳.val.isFiberedInGroupoids F
    hF.1.1
  have hGc := isCartesianBetweenAffines_of_isQuasicoherentOnSite 𝒳.val.isFiberedInGroupoids G
    hG.1.1
  exact ⟨⟨isLocallyQuasicoherent_kernel_of_isCartesianBetweenAffines B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hFc hGc φ,
    hasFlatBaseChangePropertySheaf_kernel_of_isCartesianBetweenAffines B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids hFc hGc φ⟩,
    isCoherent_coherator_kernel_and_isLimit 𝒳 h𝒳 hF hG φ⟩

end AlgebraicGeometry.Stack

end

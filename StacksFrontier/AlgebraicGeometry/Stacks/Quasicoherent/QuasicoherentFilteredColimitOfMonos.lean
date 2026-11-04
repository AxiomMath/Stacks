module

public import StacksFrontier.CategoryTheory.Abelian.KernelOfColimitDesc
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ChartSectionsDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentKernelImageCokernel

/-!
# A filtered system of quasi-coherent submodules exhausting a chart is a colimit

Let `𝒳` be an algebraic stack with a smooth surjective chart `a : (Sch/U) ⟶ 𝒳`, `U` affine, and
`u = a(id_U)`.  Let `αⱼ : Dⱼ ⟶ ℱ` be a cocone of monomorphisms of `QCoh(𝒪_𝒳)` over a small
filtered category such that every section of `ℱ` over `u` comes from some `Dⱼ`.  Then `ℱ` is the
colimit of the `Dⱼ` in `QCoh(𝒪_𝒳)`.

The map `colim Dⱼ ⟶ ℱ` vanishes after composition with its cokernel on the sections over `u`,
hence is an epimorphism (quasi-coherent modules are detected on the chart).  It is a monomorphism
because it is injective on the sections over the flat object `u`: in `Mod(𝒪_𝒳)`, which is
Grothendieck abelian, its kernel is the colimit of the kernels of the `αⱼ` (AB5), and these are
parasitic (a monomorphism of `QCoh(𝒪_𝒳)` is injective over flat objects, Stacks 0779); restriction
to the flat-fppf site is a left adjoint, so a colimit of parasitic modules is parasitic.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isZero_moduleRestriction_kernel_of_mono`
* `AlgebraicGeometry.Stack.AlgebraicStacks.isColimit_of_mono_of_forall_mem_range`

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.FibredSite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **A monomorphism of quasi-coherent modules is injective over flat objects.** -/
theorem injective_app_of_mono {P F : quasicoherentModules B S hS 𝒳} (φ : P ⟶ F) [Mono φ]
    {x : 𝒳.val.val.obj} (hx : flatObject B S hS 𝒳.val x) :
    Function.Injective (φ.hom.val.app (op x)) := by
  have h := injective_and_range_eq_ker_of_isLimit_kernelFork B S hS 𝒳 φ (kernelIsKernel φ) x hx
  have h0 : kernel.ι φ = 0 := (cancel_mono φ).1 (by rw [kernel.condition, zero_comp])
  rw [← LinearMap.ker_eq_bot, ← h.2]
  show LinearMap.range ((kernel.ι φ).hom.val.app (op x)).hom = ⊥
  rw [h0]
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_bot]
  constructor
  · rintro ⟨z, rfl⟩; rfl
  · rintro rfl; exact ⟨0, map_zero _⟩

variable (B S hS 𝒳) in
/-- **Restriction to the flat-fppf site preserves colimits**: it is the pullback of sheaves of
modules along the flat-fppf morphism of ringed topoi (Stacks 0788), a left adjoint (Stacks 03D7).
-/
theorem preservesColimitsOfSize_moduleRestriction :
    PreservesColimitsOfSize.{u, u} (FlatFppf.moduleRestriction B S hS 𝒳) := by
  have := FlatFppf.hasSheafify_addCommGrpCat B S hS 𝒳
  have := FlatFppf.wEqualsLocallyBijective_addCommGrpCat B S hS 𝒳
  have := (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    (FlatFppf.ringedToposModulesHom B S hS 𝒳)).leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso (FlatFppf.modulePullbackIso B S hS 𝒳)

/-- A module all of whose sections over flat objects vanish restricts to zero on the flat-fppf
site. -/
theorem isZero_moduleRestriction_of_subsingleton (M : Stack.fppfModules B S hS 𝒳)
    (h : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x → Subsingleton (M.val.obj (op x))) :
    IsZero ((FlatFppf.moduleRestriction B S hS 𝒳).obj M) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext X x
  have := (FlatFppf.subsingleton_moduleRestriction_obj_iff B S hS 𝒳 M X.unop).2
    (h X.unop.obj X.unop.property)
  exact Subsingleton.elim _ _

/-- **The kernel in `Mod(𝒪_𝒳)` of a monomorphism of `QCoh(𝒪_𝒳)` vanishes over flat objects.** -/
theorem subsingleton_kernel_of_mono {P F : quasicoherentModules B S hS 𝒳}
    (φ : P ⟶ F) [Mono φ] {x : 𝒳.val.val.obj} (hx : flatObject B S hS 𝒳.val x) :
    Subsingleton ((kernel ((quasicoherentInclusion B S hS 𝒳).map φ)).val.obj (op x)) := by
  obtain ⟨hinj, hrange⟩ := kernel_ι_app_injective_and_range B S hS 𝒳
    ((quasicoherentInclusion B S hS 𝒳).map φ) x
  have hφ : Function.Injective (φ.hom.val.app (op x)) := injective_app_of_mono φ hx
  have hz : ∀ s, (kernel.ι ((quasicoherentInclusion B S hS 𝒳).map φ)).val.app (op x) s = 0 := by
    intro s
    have hs : (kernel.ι ((quasicoherentInclusion B S hS 𝒳).map φ)).val.app (op x) s ∈
        LinearMap.ker (((quasicoherentInclusion B S hS 𝒳).map φ).val.app (op x)).hom := by
      rw [← hrange]; exact LinearMap.mem_range_self _ s
    exact hφ ((LinearMap.mem_ker.1 hs).trans (map_zero _).symm)
  exact ⟨fun s t => hinj ((hz s).trans (hz t).symm)⟩

/-- **A map of modules on the fppf site whose kernel restricts to zero on the flat-fppf site is
injective over flat objects.** -/
theorem injective_app_of_isZero_moduleRestriction_kernel {M N : Stack.fppfModules B S hS 𝒳}
    (g : M ⟶ N) (hg : IsZero ((FlatFppf.moduleRestriction B S hS 𝒳).obj (kernel g)))
    {x : 𝒳.val.val.obj} (hx : flatObject B S hS 𝒳.val x) :
    Function.Injective (g.val.app (op x)) := by
  obtain ⟨-, hrange⟩ := kernel_ι_app_injective_and_range B S hS 𝒳 g x
  have hsub : Subsingleton ((kernel g).val.obj (op x)) := by
    refine (FlatFppf.subsingleton_moduleRestriction_obj_iff B S hS 𝒳 (kernel g) ⟨x, hx⟩).1 ?_
    refine ⟨fun s t => ?_⟩
    have h0 := (IsZero.iff_id_eq_zero _).1 hg
    have hs : s = 0 := congrArg (fun f => f.val.app (op (⟨x, hx⟩ : FlatFppf B S hS 𝒳)) s) h0
    have ht : t = 0 := congrArg (fun f => f.val.app (op (⟨x, hx⟩ : FlatFppf B S hS 𝒳)) t) h0
    rw [hs, ht]
  rw [← LinearMap.ker_eq_bot, ← hrange, eq_bot_iff]
  rintro _ ⟨s, rfl⟩
  rw [Submodule.mem_bot, Subsingleton.elim s 0, map_zero]

variable {U : BigFppfOver B S hS} {a : schemeStack.{u, w} B S hS U ⟶ 𝒳}

/-- **A filtered system of quasi-coherent submodules whose sections over a smooth affine chart
exhaust those of `ℱ` has `ℱ` as its colimit** in `QCoh(𝒪_𝒳)`. -/
def isColimit_of_mono_of_forall_mem_range (hsm : AlgebraicStacks.IsSmooth B S hS a)
    (hsurj : IsSurjective B S hS a)
    (hu : IsAffineOver B S hS (𝒳.val.val.p.obj (chartObject a)))
    {J : Type u} [SmallCategory J] [IsFiltered J] {D : J ⥤ quasicoherentModules B S hS 𝒳}
    {F : quasicoherentModules B S hS 𝒳} (α : D ⟶ (Functor.const J).obj F)
    [∀ j, Mono (α.app j)]
    (hex : ∀ f : F.obj.val.obj (op (chartObject a)),
      ∃ (j : J) (y : (D.obj j).obj.val.obj (op (chartObject a))),
        (α.app j).hom.val.app (op (chartObject a)) y = f) :
    IsColimit (Cocone.mk F α) := by
  have huflat : flatObject B S hS 𝒳.val (chartObject a) :=
    FlatFppf.flatObject_map B S hS a (AlgebraicStacks.isFlat_of_isSmooth B S hS a hsm)
      ⟨Over.mk (𝟙 U), flatObject_schemeStack_id.{u, w} B S hS U⟩
  haveI := hasColimitsOfSize_quasicoherentModules B S hS 𝒳
  let hc := colimit.isColimit D
  let m := hc.desc (Cocone.mk F α)
  suffices IsIso m from IsColimit.ofPointIso hc
  have hfac : ∀ j, colimit.ι D j ≫ m = α.app j := hc.fac (Cocone.mk F α)
  have hepi : Epi m := by
    refine Abelian.epi_of_cokernel_π_eq_zero m (ObjectProperty.hom_ext _ ?_)
    refine hom_eq_zero_of_chart hsm hsurj hu F.property _ fun f => ?_
    obtain ⟨j, y, rfl⟩ := hex f
    have h : α.app j ≫ cokernel.π m = 0 := by
      rw [← hfac, Category.assoc, cokernel.condition, Limits.comp_zero]
    exact congrArg (fun g => g.hom.val.app (op (chartObject a)) y) h
  -- injectivity over the chart, through `Mod(𝒪_𝒳)`
  let ι := quasicoherentInclusion B S hS 𝒳
  have := preservesColimitsOfSize_quasicoherentInclusion B S hS 𝒳
  let hc' := isColimitOfPreserves ι hc
  let α' : D ⋙ ι ⟶ (Functor.const J).obj (ι.obj F) :=
    Functor.whiskerRight α ι ≫ (Functor.constComp J F ι).hom
  have hm' : ι.map m = hc'.desc (Cocone.mk _ α') := by
    refine hc'.hom_ext fun j => ?_
    rw [hc'.fac]
    simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, ← Functor.map_comp, hfac, α',
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.constComp_hom_app, Category.comp_id]
  have := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    .fppf
  have := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p .fppf
  have := isGrothendieckAbelian_fppfModules B S hS 𝒳
  have := preservesColimitsOfSize_moduleRestriction B S hS 𝒳
  let R := FlatFppf.moduleRestriction B S hS 𝒳
  have hK : IsZero (R.obj (kernel (hc'.desc (Cocone.mk _ α')))) := by
    refine IsZero.of_iso ?_ (R.mapIso (kernelDescIsoColimitKernel hc' α'))
    refine IsZero.of_iso ?_ (preservesColimitIso R (kernel α'))
    refine isZero_colimit_of_forall_isZero fun j => ?_
    refine IsZero.of_iso ?_ (R.mapIso (PreservesKernel.iso ((evaluation J _).obj j) α'))
    exact isZero_moduleRestriction_of_subsingleton _ fun x hx =>
      subsingleton_kernel_of_mono (α.app j) hx
  have hinj : Function.Injective (m.hom.val.app (op (chartObject a))) :=
    injective_app_of_isZero_moduleRestriction_kernel (ι.map m) (hm' ▸ hK) huflat
  have hmono : Mono m := by
    refine Preadditive.mono_of_kernel_zero (ObjectProperty.hom_ext _ ?_)
    refine hom_eq_zero_of_chart hsm hsurj hu (kernel m).property _ fun x => hinj ?_
    have h := congrArg (fun g => g.hom.val.app (op (chartObject a)) x) (kernel.condition m)
    exact h.trans (map_zero _).symm
  exact isIso_of_mono_of_epi m

end AlgebraicGeometry.Stack.AlgebraicStacks

end

module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentKernelsFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFromSheafFlatBaseChange

/-!
# The functors `c` and `d` of Stacks 0GQS along a flat 1-morphism

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism from the algebraic stack of an algebraic space `U` to an
algebraic stack `𝒳`, and let `c : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` and
`d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` be the functors of Stacks 0GQS
(`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcSpaceRestriction` and
`AlgebraicGeometry.Stack.AlgebraicStacks.qcohSpaceRestriction`). This file proves items (5), (6)
and (7) of Stacks 0GQS, for flat `f`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteLimits_qcohSpaceRestriction_of_isFlat`:
  item (5), `d` is left exact (with its right exactness, `d` is exact).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isZero_lqcohFbcSpaceRestriction_obj_of_isParasitic`:
  item (6), `c` kills parasitic objects.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorCompQcohSpaceRestrictionIso`: item
  (7), `c ≅ d ∘ Q` for the coherator
  `Q = AlgebraicGeometry.Stack.AlgebraicStacks.etaleLqcohFbcCoherator` of Stacks 0779, with
  components the restrictions of the counit `Q(ℱ) ⟶ ℱ`
  (`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorCompQcohSpaceRestrictionIso_hom_app`).

## Implementation notes

All three are proved on sections. The sections of `c(ℱ)` or `d(ℱ)` over an étale chart `V` of `U`
are those of `ℱ` over the object `f(V)` of `𝒳`, and `f(V)` is a flat object when `f` is flat
(`AlgebraicGeometry.Stack.FlatFppf.flatObject_map_chartObject`).

* For (5) the source combines Stacks 076X with Stacks 0GQD. The sectionwise route is taken
  instead, because `d` is not stated as a composite of `f^*` with a restriction
  `QCoh(𝒪_𝒰) ⥤ QCoh(U_étale, 𝒪_U)`, and identifying it with one would be a detour: a kernel in
  `QCoh(𝒪_𝒳)` is a kernel on the sections over every flat object
  (`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentKernelsOnFlatObjects`, the input of the
  proof of 076X), so its image under `d` is a kernel on the sections over every étale chart,
  hence a kernel of sheaves of modules on `U_étale`
  (`SheafOfModules.nonempty_isLimit_of_app`), hence one in the full subcategory
  `QCoh(U_étale, 𝒪_U)`.
* For (6) the source's route is followed: a parasitic module has zero sections at `f(V)`.
* For (7) the source argues with (3) and (6). The direct sectionwise argument is used instead: the
  counit `Q(ℱ) ⟶ ℱ` has parasitic kernel and cokernel (Stacks 0779 (2)), so it is bijective on
  sections over every flat object
  (`AlgebraicGeometry.Stack.isIso_app_of_isParasitic_kernel_cokernel`), in particular over every
  `f(V)`. This is the same content as the source's argument, without passing through the exactness
  of `c`.

The parasitic condition of (6) is `AlgebraicGeometry.Stack.IsParasitic` for the étale site, on
the underlying presheaf of modules of `ℱ`; the condition does not depend on the site (it is about
sections at flat objects only).

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 076X](https://stacks.math.columbia.edu/tag/076X)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- A sheaf of modules all of whose modules of sections vanish is a zero object. -/
theorem _root_.SheafOfModules.isZero_of_subsingleton {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R)
    (h : ∀ X, Subsingleton (M.val.obj X)) : IsZero M where
  unique_to N := ⟨⟨⟨0⟩, fun φ => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]))⟩⟩
  unique_from N := ⟨⟨⟨0⟩, fun φ => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _))⟩⟩

section KernelSections

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : SheafOfModules.{u} R}

/-- The kernel of a map of sheaves of modules is computed sectionwise: on every object, its
sections map injectively onto the kernel of the map on sections. -/
theorem _root_.SheafOfModules.kernel_ι_app_injective_and_range (g : M ⟶ N) (X : Cᵒᵖ) :
    Function.Injective ((kernel.ι g).val.app X).hom ∧
      LinearMap.range ((kernel.ι g).val.app X).hom = LinearMap.ker (g.val.app X).hom := by
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation _ X
  have hl : IsLimit ((KernelFork.ofι (kernel.ι g) (kernel.condition g)).map G) :=
    KernelFork.mapIsLimit _ (kernelIsKernel g) G
  have hE : (ShortComplex.mk _ _
      ((KernelFork.ofι (kernel.ι g) (kernel.condition g)).map_condition G)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hl
  exact ⟨(ModuleCat.mono_iff_injective _).1 (mono_of_isLimit_fork hl), hE.moduleCat_range_eq_ker⟩

/-- **A kernel fork of sheaves of modules which is a kernel on sections is a kernel.** If on every
object the sections of the fork map injectively onto the kernel of the map on sections, the fork
is a limit: its comparison map to the kernel is bijective on every module of sections. -/
theorem _root_.SheafOfModules.nonempty_isLimit_of_app {g : M ⟶ N} (c : KernelFork g)
    (h : ∀ X, Function.Injective (c.ι.val.app X) ∧
      ∀ s : M.val.obj X, g.val.app X s = 0 → ∃ k : c.pt.val.obj X, c.ι.val.app X k = s) :
    Nonempty (IsLimit c) := by
  let m := kernel.lift g c.ι c.condition
  have hm : m ≫ kernel.ι g = c.ι := kernel.lift_ι _ _ _
  have hι : ∀ X (k : c.pt.val.obj X),
      (kernel.ι g).val.app X (m.val.app X k) = c.ι.val.app X k := fun X k =>
    congrArg (fun φ : c.pt ⟶ M => φ.val.app X k) hm
  have hbij : ∀ X, IsIso (m.val.app X) := fun X => by
    obtain ⟨hinj, hrange⟩ := SheafOfModules.kernel_ι_app_injective_and_range g X
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab => (h X).1 ?_, fun k => ?_⟩
    · rw [← hι, ← hι, hab]
    · have hk : g.val.app X ((kernel.ι g).val.app X k) = 0 := by
        have := LinearMap.mem_range_self ((kernel.ι g).val.app X).hom k
        rw [hrange] at this
        exact this
      obtain ⟨a, ha⟩ := (h X).2 _ hk
      exact ⟨a, hinj (by rw [hι, ha])⟩
  have : IsIso ((SheafOfModules.forget R).map m) := PresheafOfModules.isIso_of_isIso_app _ hbij
  have : IsIso m := isIso_of_reflects_iso _ (SheafOfModules.forget R)
  exact ⟨IsLimit.ofIsoLimit (kernelIsKernel g) (Fork.ext (asIso m) hm :
    c ≅ KernelFork.ofι (kernel.ι g) (kernel.condition g)).symm⟩

end KernelSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- The sections of `c(ℱ)` over an étale chart `V` of `U` are the sections of `ℱ` over the object
`f(V)` of `𝒳`. -/
theorem lqcohFbcSpaceRestriction_obj_val_obj (F : lqcohFbcModules B S hS 𝒳)
    (V : Space.SmallEtale B S hS U) :
    (((lqcohFbcSpaceRestriction B S hS 𝒳 U hU f).obj F).obj.val.obj (op V) : Type u) =
      F.obj.val.obj (op ((CatFiberedInGroupoids.homFunctor f.hom).obj
        (FlatFppf.chartObject.{u, w} B S hS U hU V))) :=
  rfl

/-- **Stacks 0GQS, item (6).** For flat `f`, the functor `c` kills parasitic objects: the sections
of `c(ℱ)` over an étale chart `V` are those of `ℱ` over `f(V)`, a flat object of `𝒳`, where a
parasitic `ℱ` has no sections. -/
theorem isZero_lqcohFbcSpaceRestriction_obj_of_isParasitic
    (hf : AlgebraicStacks.IsFlat B S hS f) (F : lqcohFbcModules B S hS 𝒳)
    (hF : IsParasitic B S hS 𝒳 .etale F.obj.val) :
    IsZero ((lqcohFbcSpaceRestriction B S hS 𝒳 U hU f).obj F) := by
  have hsub : ∀ V : (Space.SmallEtale B S hS U)ᵒᵖ,
      Subsingleton (((lqcohFbcSpaceRestriction B S hS 𝒳 U hU f).obj F).obj.val.obj V) :=
    fun V => (congrArg Subsingleton
      (lqcohFbcSpaceRestriction_obj_val_obj B S hS 𝒳 U hU f F V.unop)).mpr
      (hF _ (FlatFppf.flatObject_map_chartObject B S hS 𝒳 U hU f hf V.unop))
  exact IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
    (SheafOfModules.isZero_of_subsingleton _ hsub)

/-- The functor `d` is additive: on sections it does nothing. -/
instance additive_qcohSpaceRestriction : (qcohSpaceRestriction B S hS 𝒳 U hU f).Additive where
  map_add {_ _ _ _} := ObjectProperty.hom_ext _ (SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)))

/-- **Stacks 0GQS, item (5).** For flat `f`, the functor `d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)`
preserves finite limits; with its right exactness, `d` is exact.

The route is sectionwise rather than the source's (Stacks 076X and 0GQD): a kernel in
`QCoh(𝒪_𝒳)` is a kernel on sections over flat objects, the objects `f(V)` attached to the étale
charts `V` of `U` are flat, so `d` of it is a kernel on the sections over every étale chart, which
is a kernel of `𝒪_U`-modules and so of quasi-coherent ones. -/
theorem preservesFiniteLimits_qcohSpaceRestriction_of_isFlat
    (hf : AlgebraicStacks.IsFlat B S hS f) :
    PreservesFiniteLimits (qcohSpaceRestriction B S hS 𝒳 U hU f) := by
  let d := qcohSpaceRestriction B S hS 𝒳 U hU f
  have hker : ∀ {M N : AlgebraicStacks.quasicoherentModules B S hS 𝒳} (φ : M ⟶ N),
      PreservesLimit (parallelPair φ 0) d := fun φ => by
    obtain ⟨c, ⟨hc⟩, hcf⟩ := quasicoherentKernelsOnFlatObjects B S hS 𝒳 φ
    obtain ⟨hι⟩ := SheafOfModules.nonempty_isLimit_of_app ((c.map d).map (ObjectProperty.ι _))
      fun V => hcf ((CatFiberedInGroupoids.homFunctor f.hom).obj
        (FlatFppf.chartObject.{u, w} B S hS U hU V.unop))
        (FlatFppf.flatObject_map_chartObject B S hS 𝒳 U hU f hf V.unop)
    have hd : IsLimit (c.map d) :=
      isLimitOfReflects (ObjectProperty.ι _) ((KernelFork.isLimitMapConeEquiv _ _).symm hι)
    exact preservesLimit_of_preserves_limit_cone hc ((KernelFork.isLimitMapConeEquiv c _).symm hd)
  have : HasFiniteProducts (AlgebraicStacks.quasicoherentModules B S hS 𝒳) :=
    hasFiniteProducts_of_hasFiniteBiproducts _
  exact Functor.preservesFiniteLimits_of_preservesKernels _

section Coherator

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

/-- A member of `LQCoh^fbc(𝒪_𝒳)` as a module on the fppf site of `𝒳` (Stacks 0771 (1)),
functorially: `AlgebraicGeometry.Stack.fppfModuleOfLqcohSheafFbc`, with the same morphisms of
presheaves of modules. -/
def lqcohFbcToFppfModules : lqcohFbcModules B S hS 𝒳 ⥤ Stack.fppfModules B S hS 𝒳 where
  obj F := (fppfModuleOfLqcohSheafFbc B (associatedBigEtaleSite B) rfl S hS 𝒳 F.obj
    F.property).obj
  map φ := ⟨φ.hom.val⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The coherator `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of Stacks 0779**: a member of
`LQCoh^fbc(𝒪_𝒳)`, read as a module on the fppf site of `𝒳` (Stacks 0771 (1)), followed by the
coherator `AlgebraicGeometry.Stack.AlgebraicStacks.coherator` of Stacks 0778.

It is defined on `LQCoh^fbc(𝒪_𝒳)` read inside the étale modules, the category `c` is defined
on, whereas `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoherator` is the right adjoint of
`QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` read inside the fppf modules. -/
def etaleLqcohFbcCoherator :
    lqcohFbcModules B S hS 𝒳 ⥤ AlgebraicStacks.quasicoherentModules B S hS 𝒳 :=
  lqcohFbcToFppfModules B S hS 𝒳 ⋙ AlgebraicStacks.coherator B S hS 𝒳

/-- The counit `Q(ℱ) ⟶ ℱ` of the coherator, read on the étale site of `𝒳` as a morphism of
`LQCoh(𝒪_𝒳)`. -/
def lqcohFbcCoheratorCounit :
    etaleLqcohFbcCoherator B S hS 𝒳 ⋙ qcohToLqcoh B S hS 𝒳 ⟶ lqcohFbcToLqcoh B S hS 𝒳 where
  app F := ObjectProperty.homMk ⟨((coheratorAdjunction B S hS 𝒳).counit.app
    ((lqcohFbcToFppfModules B S hS 𝒳).obj F)).val⟩
  naturality _ _ φ := ObjectProperty.hom_ext _ (SheafOfModules.hom_ext
    (congrArg (fun g => g.val) ((coheratorAdjunction B S hS 𝒳).counit.naturality
      ((lqcohFbcToFppfModules B S hS 𝒳).map φ))))

/-- For flat `f`, the restriction to `U_étale` of the counit `Q(ℱ) ⟶ ℱ` is an isomorphism: its
sections over an étale chart `V` are those of the counit over the flat object `f(V)`, where the
counit is bijective since its kernel and cokernel are parasitic (Stacks 0779 (2)). -/
theorem isIso_lqcohSpaceRestriction_map_lqcohFbcCoheratorCounit_app
    (hf : AlgebraicStacks.IsFlat B S hS f) (F : lqcohFbcModules B S hS 𝒳) :
    IsIso ((lqcohSpaceRestriction B S hS 𝒳 U hU f).map
      ((lqcohFbcCoheratorCounit B S hS 𝒳).app F)) := by
  have hpar := isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒳
    (associatedBigEtaleSite B) rfl ((lqcohFbcToFppfModules B S hS 𝒳).obj F) F.property
  let m := (ObjectProperty.ι _).map ((lqcohSpaceRestriction B S hS 𝒳 U hU f).map
    ((lqcohFbcCoheratorCounit B S hS 𝒳).app F))
  have h : ∀ V : (Space.SmallEtale B S hS U)ᵒᵖ, IsIso (m.val.app V) := fun V =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (isIso_app_of_isParasitic_kernel_cokernel B S hS _ hpar.1 hpar.2
        ((CatFiberedInGroupoids.homFunctor f.hom).obj
          (FlatFppf.chartObject.{u, w} B S hS U hU V.unop))
        (FlatFppf.flatObject_map_chartObject B S hS 𝒳 U hU f hf V.unop))
  have : IsIso ((SheafOfModules.forget _).map m) := PresheafOfModules.isIso_of_isIso_app _ h
  have : IsIso m := isIso_of_reflects_iso _ (SheafOfModules.forget _)
  exact isIso_of_fully_faithful (ObjectProperty.ι _) _

/-- **Stacks 0GQS, item (7): `c = d ∘ Q` for flat `f`.** The restriction `d(Q(ℱ)) ⟶ c(ℱ)` of the
counit of the coherator is an isomorphism, naturally in `ℱ ∈ LQCoh^fbc(𝒪_𝒳)`. -/
def lqcohFbcCoheratorCompQcohSpaceRestrictionIso (hf : AlgebraicStacks.IsFlat B S hS f) :
    etaleLqcohFbcCoherator B S hS 𝒳 ⋙ qcohSpaceRestriction B S hS 𝒳 U hU f ≅
      lqcohFbcSpaceRestriction B S hS 𝒳 U hU f :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ ((lqcohSpaceRestriction B S hS 𝒳 U hU f).map
      ((lqcohFbcCoheratorCounit B S hS 𝒳).app F))
      (isIso_lqcohSpaceRestriction_map_lqcohFbcCoheratorCounit_app B S hS 𝒳 U hU f hf F))
    (fun φ => (Functor.whiskerRight (lqcohFbcCoheratorCounit B S hS 𝒳)
      (lqcohSpaceRestriction B S hS 𝒳 U hU f)).naturality φ)

/-- The components of the isomorphism `d ∘ Q ≅ c` of
`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorCompQcohSpaceRestrictionIso` are the
restrictions of the counit `Q(ℱ) ⟶ ℱ` of the coherator. -/
theorem lqcohFbcCoheratorCompQcohSpaceRestrictionIso_hom_app
    (hf : AlgebraicStacks.IsFlat B S hS f) (F : lqcohFbcModules B S hS 𝒳) :
    (lqcohFbcCoheratorCompQcohSpaceRestrictionIso B S hS 𝒳 U hU f hf).hom.app F =
      (lqcohSpaceRestriction B S hS 𝒳 U hU f).map ((lqcohFbcCoheratorCounit B S hS 𝒳).app F) :=
  rfl

end Coherator

end AlgebraicGeometry.Stack.AlgebraicStacks

end

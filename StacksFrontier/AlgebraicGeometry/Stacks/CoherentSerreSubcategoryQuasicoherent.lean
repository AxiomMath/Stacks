module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentAbelianLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.QuasicoherentCokernelsAndDirectSums
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleQuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteEpi
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentCokernelLocallyNoetherian

/-!
# `Coh(𝒪_𝒳)` is a Serre subcategory of `QCoh(𝒪_𝒳)` (Stacks 0GRB)

Let `𝒳` be a locally Noetherian algebraic stack. Stacks 0GRB says that `Coh(𝒪_𝒳)` is a Serre
subcategory of `QCoh(𝒪_𝒳)`, and that for a map `φ : ℱ ⟶ 𝒢` of quasi-coherent modules

1. if `ℱ` is coherent and `φ` surjective, then `𝒢` is coherent;
2. if `ℱ` is coherent, then `Im(φ)` is coherent;
3. if `𝒢` is coherent and `Ker(φ)` is parasitic, then `ℱ` is coherent.

The modules are the `𝒪_𝒳`-modules on the big fppf site with sections in the universe of the
schemes, coherence is `AlgebraicGeometry.Stack.IsCoherent` (Stacks 0GR6) and
`QCoh(𝒪_𝒳)` is the full subcategory `AlgebraicGeometry.Stack.FlatFppf.qcohModules`.

## The abelian structure on `QCoh(𝒪_𝒳)`

For a map `φ` of quasi-coherent modules the coherator `Q(Ker φ) = g_!g^{-1}(Ker φ)` is
quasi-coherent (`AlgebraicGeometry.Stack.FlatFppf.isQuasicoherentOnSite_coherator_kernel`): over a
flat object `y` lying over an affine scheme the restriction of `Ker φ` to the flat-fppf site of
that scheme is the module attached to `Ker(φ)(y)`, sections of quasi-coherent modules and of their
kernels base changing along flat maps. With the closure of quasi-coherence under cokernels
(Stacks 06WV) this gives `CategoryTheory.ObjectProperty.RelKernelData` for the quasi-coherent
modules, hence the abelian structure `AlgebraicGeometry.Stack.FlatFppf.abelianQCoh`, whose
kernels are the `Q(Ker φ)` and whose cokernels are those of `Mod(𝒪_𝒳)` (Stacks 0GQL), and the
restriction to the flat objects is exact on it.

## The proof

Everything runs through one criterion,
`AlgebraicGeometry.Stack.FlatFppf.isCoherent_of_moduleFinite_sections`: a quasi-coherent module
whose sections over every flat object lying over a Noetherian affine scheme are a finite module is
coherent. This is where local Noetherianity enters, through the covering
`AlgebraicGeometry.Stack.FlatFppf.noetherianFlatSieve_mem`, and it is the source's "compare with
the proof of Lemma 0GR9": over such an object the sections are finitely presented, so the
cartesian property gives a finite presentation on the slice.

* Subobjects: a monomorphism of `QCoh(𝒪_𝒳)` is injective on sections over flat objects, the
  restriction to flat objects being left exact; a submodule of a finite module over a Noetherian
  ring is finite.
* Quotients and part (1): an epimorphism of `QCoh(𝒪_𝒳)` is one of `Mod(𝒪_𝒳)`; finite type passes
  to quotients, and on a locally Noetherian stack a quasi-coherent module of finite type is
  coherent (Stacks 0GR5).
* Extensions: sections over a flat object are left exact on short exact sequences of
  `QCoh(𝒪_𝒳)`, and an extension of a finite module by a submodule of a finite module over a
  Noetherian ring is finite.
* Part (2): the image of `φ` in `QCoh(𝒪_𝒳)` is a quotient of `ℱ` there. The image computed in
  `Mod(𝒪_𝒳)` need not be quasi-coherent
  (`AlgebraicGeometry.Stack.exists_not_isCoherent_image_of_isCoherent`).
* Part (3): if `Ker(φ)` is parasitic, `φ` is injective on sections over flat objects.

## Main results

* `AlgebraicGeometry.Stack.isSerreClass_coh_qcoh`: **Stacks 0GRB**, the Serre subcategory.
* `AlgebraicGeometry.Stack.FlatFppf.isCoherent_of_epi`: **Stacks 0GRB (1)**.
* `AlgebraicGeometry.Stack.isCoherent_image_qcoh`: **Stacks 0GRB (2)**.
* `AlgebraicGeometry.Stack.isCoherent_of_isParasitic_kernel`: **Stacks 0GRB (3)**, with
  `Ker(φ)` computed in `Mod(𝒪_𝒳)`; `AlgebraicGeometry.Stack.isCoherent_of_isParasitic_kernel_qcoh`
  with the kernel computed in `QCoh(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0GRB](https://stacks.math.columbia.edu/tag/0GRB)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

namespace FlatFppf

attribute [local instance] hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

/-- **The local computation, without finiteness.** For a map `φ : ℱ ⟶ 𝒢` of modules cartesian
between affine objects and a flat object `y` lying over an affine scheme, the restriction
`(f')^{-1}g^{-1}Ker φ` of `Ker φ` to the flat-fppf site of the scheme below `y` has a global
presentation: it is the module attached to the `𝒪(y)`-module `Ker(φ)(y)`, whose sections base
change along flat maps. -/
theorem isPresentedByGlobalSections_restrictedModuleRestrictionAlong_kernel
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)} (φ : F ⟶ G)
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F)
    (hG : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids G) (y : FlatFppf B S hS 𝒳)
    (hyaff : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj)) :
    ((restrictedModuleRestrictionAlong B S hS (ambientSliceMorphism B S hS y)
      (isFlat_ambientSliceMorphism B S hS y)).obj
        ((moduleInverseImageU B S hS 𝒳).obj (kernel φ))).IsPresentedByGlobalSections := by
  classical
  let p := 𝒳.val.val.p
  let hp := 𝒳.val.isFiberedInGroupoids
  let f := ambientSliceMorphism B S hS y
  let hf := isFlat_ambientSliceMorphism B S hS y
  let 𝒵 := schemeStack.{u, w} B S hS (p.obj y.obj)
  have : (primedSiteFunctor B S hS f hf).IsContinuous (topology B S hS 𝒵)
      (topology B S hS 𝒳) := siteFunctor_isContinuous B S hS f hf
  let Fn : FlatFppf B S hS 𝒵 ⥤ 𝒳.val.val.obj :=
    primedSiteFunctor B S hS f hf ⋙ (objectProperty B S hS 𝒳).ι
  have : Fn.IsContinuous (topology B S hS 𝒵) (associatedTopology B S hS p B.topology) :=
    Functor.isContinuous_comp _ _ _ (topology B S hS 𝒳) _
  let K := kernel φ
  let t : FlatFppf B S hS 𝒵 := ⟨Over.mk (𝟙 _), flatObject_schemeStack_id.{u, w} B S hS _⟩
  let ht : IsTerminal t := ObjectProperty.isTerminalFullSubcategory _ (Over.isTerminalMkId _) _
  have hpobj : ∀ V : FlatFppf B S hS 𝒵, p.obj (Fn.obj V) = V.obj.left := fun V ↦
    Functor.congr_obj f.hom.hom.w V.obj
  have hpmap : ∀ {V W : FlatFppf B S hS 𝒵} (h : V ⟶ W),
      p.map (Fn.map h) = eqToHom (hpobj V) ≫ h.hom.left ≫ eqToHom (hpobj W).symm :=
    fun h ↦ Functor.congr_hom f.hom.hom.w h.hom
  have haffV : ∀ V : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj V.obj)) →
      IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (Fn.obj V)) := fun V hV ↦ by
    change IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj V)))
    rwa [hpobj V]
  have hy₀aff : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (Fn.obj t)) := by
    change IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj t)))
    rwa [hpobj t]
  have hflat : ∀ V : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj V.obj)) →
      let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from V))
      Module.Flat (fibredSectionRing B S hS p (Fn.obj t))
        (fibredSectionRing B S hS p (Fn.obj V)) := by
    intro V hV
    have hm : Flat ((BigFppfOver.toScheme B S hS).map (p.map (Fn.map (ht.from V)))) :=
      flat_toScheme_map_of_eq B S hS (hpobj V) (hpobj t) _ _ (hpmap _)
        (flat_of_flatObject_schemeStack.{u, w} B S hS _ V.obj V.property)
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj V))) := haffV V hV
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj t))) := hy₀aff
    exact Scheme.Hom.flat_appTop _
  let A := fibredSectionRing B S hS p (Fn.obj t)
  let := fibredSectionsModule hp K (Fn.obj t)
  let s : K.val.obj (op (Fn.obj t)) → K.val.obj (op (Fn.obj t)) := id
  have hs : Submodule.span A (Set.range s) = ⊤ := by
    rw [show Set.range s = Set.univ from Set.range_id, Submodule.span_univ]
  let N := LinearMap.ker (Finsupp.linearCombination A s)
  let ρ : N → K.val.obj (op (Fn.obj t)) →₀ A := fun i ↦ i.1
  have hρspan : Submodule.span A (Set.range ρ) = N := by
    rw [show Set.range ρ = (N : Set _) from Subtype.range_coe, Submodule.span_eq]
  have hρ : ∀ i, ((ρ i).sum fun j r ↦ r • s j) = 0 := fun i ↦ by
    have hi := i.2
    rwa [LinearMap.mem_ker, Finsupp.linearCombination_apply] at hi
  have hbc : ∀ W : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj W.obj)) →
      Function.Bijective (fibredSectionsBaseChange hp K (Fn.map (ht.from W))) := fun W hW ↦
    bijective_fibredSectionsBaseChange_kernel hp φ (Fn.map (ht.from W))
      (hF _ hy₀aff (haffV W hW)) (hG _ hy₀aff (haffV W hW)) (hflat W hW)
  have := hasSheafify_addCommGrpCat B S hS 𝒵
  have := wEqualsLocallyBijective_addCommGrpCat B S hS 𝒵
  have h : (Fn.sheafPushforwardContinuous RingCat.{u} (topology B S hS 𝒵)
      (associatedTopology B S hS p B.topology)).obj (ambientRingStructureSheaf B S hS 𝒳) =
      subsiteRingStructureSheaf B S hS 𝒵 := inverseImageRing_primedSiteFunctor B S hS f hf
  have main :=
    (Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_pushforward_of_terminal
    Fn h K t ht (K.val.obj (op (Fn.obj t))) N s ρ hρ ?_ ?_).1
  · refine Stacks.SheafOfModules.isPresentedByGlobalSections_of_iso ?_ main
    exact ((_root_.SheafOfModules.pushforwardComp (F := primedSiteFunctor B S hS f hf)
      (G := (objectProperty B S hS 𝒳).ι)
      (eqToHom (inverseImageRing_primedSiteFunctor B S hS f hf).symm)
      (𝟙 (((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous RingCat.{u}
        (topology B S hS 𝒳) (associatedTopology B S hS p B.topology)).obj
          (ambientRingStructureSheaf B S hS 𝒳)))).app K ≪≫
      (_root_.SheafOfModules.pushforwardCongr
        (by rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _)).app K).symm
  · intro V x
    obtain ⟨T, hT, haff⟩ := FlatFppf.isCoveringFamily_isAffine B S hS 𝒵 V
    refine ⟨T, hT, fun W g hg ↦ ?_⟩
    let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from W))
    let := fibredSectionsModule hp K (Fn.obj W)
    let := fibredSectionsModuleOver hp K (Fn.map (ht.from W))
    have : IsScalarTower A (fibredSectionRing B S hS p (Fn.obj W)) (K.val.obj (op (Fn.obj W))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange_of_span
      (fibredSectionsRestrict hp K (Fn.map (ht.from W))) s hs (hbc W (haff hg)).2
      (K.val.map (Fn.map g).op x)
  · intro V c hc
    obtain ⟨T, hT, haff⟩ := FlatFppf.isCoveringFamily_isAffine B S hS 𝒵 V
    refine ⟨T, hT, fun W g hg ↦ ?_⟩
    let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from W))
    let := fibredSectionsModule hp K (Fn.obj W)
    let := fibredSectionsModuleOver hp K (Fn.map (ht.from W))
    have : IsScalarTower A (fibredSectionRing B S hS p (Fn.obj W)) (K.val.obj (op (Fn.obj W))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let c' : K.val.obj (op (Fn.obj t)) →₀ fibredSectionRing B S hS p (Fn.obj W) :=
      c.mapRange (fibredSectionRestrict (Fn.map g)) (map_zero _)
    have hc' :
        (c'.sum fun i r ↦ r • fibredSectionsRestrict hp K (Fn.map (ht.from W)) (s i)) = 0 := by
      have h0 := (Stacks.SheafOfModules.FreeSheafification.map_finsupp_sum_smul K.val
        (Fn.map g).op c
        (fun i ↦ (show K.val.obj (op (Fn.obj V)) from
          K.val.map (Fn.map (ht.from V)).op (s i)))).symm.trans
        ((congrArg (fun m ↦ K.val.map (Fn.map g).op m) hc).trans (map_zero _))
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
      refine congrArg (c' i • ·) ?_
      refine (K.val.congr_map_apply (congrArg (fun m ↦ (Fn.map m).op)
        (ht.hom_ext (ht.from W) (g ≫ ht.from V))) (s i)).trans ?_
      rw [Functor.map_comp, op_comp]
      exact K.val.map_comp_apply _ _ (s i)
    exact Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange_of_span
      (fibredSectionsRestrict hp K (Fn.map (ht.from W))) s hs ρ hρspan (hbc W (haff hg)) c' hc'

variable {𝒳} in
/-- **`Q(Ker φ)` is quasi-coherent** for a map `φ : ℱ ⟶ 𝒢` of quasi-coherent modules on an
algebraic stack: over every object lying over an affine scheme and mapping to a flat object
lying over an affine scheme it has a global presentation, and those objects cover. -/
theorem isQuasicoherentOnSite_coherator_kernel
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) (φ : F ⟶ G) :
    ((lowerShriekInverseImageCoherator B S hS 𝒳).obj (kernel φ)).IsQuasicoherentOnSite := by
  refine ⟨fun U ↦ ⟨Σ w : 𝒳.val.val.obj, {g : w ⟶ U // goodPresieve 𝒳 U g}, fun i ↦ i.1,
    fun i ↦ i.2.1, ?_, fun i ↦ ?_⟩⟩
  · refine GrothendieckTopology.superset_covering _ ?_ (goodPresieve_generate_mem 𝒳 U)
    rintro Z h ⟨Y', h', g, hg, rfl⟩
    exact ⟨Y', h', g, Presieve.ofArrows.mk (⟨Y', g, hg⟩ :
      Σ w : 𝒳.val.val.obj, {g : w ⟶ U // goodPresieve 𝒳 U g}), rfl⟩
  · obtain ⟨w, g, -, y, hy, hyaff, ⟨c⟩⟩ := i
    exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap _ c
      (Stacks.SheafOfModules.hasGlobalPresentation_of_isPresentedByGlobalSections
        (isPresentedByGlobalSections_over_moduleLowerShriekU B S hS ⟨y, hy⟩ _
          (isPresentedByGlobalSections_restrictedModuleRestrictionAlong_kernel 𝒳 φ
            (isCartesianBetweenAffines_of_isQuasicoherentOnSite _ F hF)
            (isCartesianBetweenAffines_of_isQuasicoherentOnSite _ G hG) ⟨y, hy⟩ hyaff)))

/-- The quasi-coherent `𝒪_𝒳`-modules, as a property of the `𝒪_𝒳`-modules on the big fppf site
with sections in the universe of the schemes. -/
abbrev qcohModules :
    ObjectProperty (_root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :=
  _root_.SheafOfModules.isQuasicoherentOnSite (ambientRingStructureSheaf B S hS 𝒳)

/-- The quasi-coherent modules are closed under cokernels in `Mod(𝒪_𝒳)` (Stacks 06WV). -/
theorem isClosedUnderCokernels_qcohModules : (qcohModules 𝒳).IsClosedUnderCokernels :=
  FibredSite.isClosedUnderCokernels_isQuasicoherentOnSite B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids

/-- The quasi-coherent modules are closed under binary products in `Mod(𝒪_𝒳)`: a binary product
is a binary coproduct, and finite direct sums of quasi-coherent modules are quasi-coherent. -/
theorem isClosedUnderBinaryProducts_qcohModules : (qcohModules 𝒳).IsClosedUnderBinaryProducts := by
  refine ⟨fun X ⟨p⟩ ↦ ?_⟩
  have ht := (IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).symm p.isLimit
  have hc := binaryBiconeIsBilimitOfLimitConeOfIsLimit ht
  exact ObjectProperty.prop_of_isColimit_binaryCofan _ hc.isColimit
    (p.prop_diag_obj ⟨WalkingPair.left⟩) (p.prop_diag_obj ⟨WalkingPair.right⟩)

/-- The quasi-coherent modules are closed under finite products in `Mod(𝒪_𝒳)`. -/
theorem isClosedUnderFiniteProducts_qcohModules : (qcohModules 𝒳).IsClosedUnderFiniteProducts := by
  have : HasFiniteProducts (_root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :=
    Abelian.has_finite_products
  have := isClosedUnderBinaryProducts_qcohModules 𝒳
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- **The quasi-coherent modules satisfy the hypotheses of `RelKernelData`** relative to
themselves and the restriction `g^{-1}` to the flat-fppf site: the kernel of a map of
quasi-coherent modules in `QCoh(𝒪_𝒳)` is `Q(Ker φ)`. -/
theorem relKernelData_qcohModules :
    ObjectProperty.RelKernelData (qcohModules 𝒳) (qcohModules 𝒳)
      (moduleInverseImageU B S hS 𝒳) := by
  have hcok := isClosedUnderCokernels_qcohModules 𝒳
  have : PreservesLimitsOfSize.{u, u} (moduleInverseImageU B S hS 𝒳) :=
    (moduleLowerShriekAdjunctionU B S hS 𝒳).rightAdjoint_preservesLimits
  have hL : PreservesFiniteLimits (moduleInverseImageU B S hS 𝒳) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  have hC : PreservesFiniteColimits (moduleInverseImageU B S hS 𝒳) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact
  { le := le_rfl
    isClosedUnderIsomorphisms := inferInstance
    containsZero := inferInstance
    isClosedUnderFiniteProducts := isClosedUnderFiniteProducts_qcohModules 𝒳
    prop_cokernel := fun f hX hY ↦ ObjectProperty.prop_cokernel _ f hX hY
    exists_relKernel := fun f hX hY ↦ ⟨_, _, isRelKernel_coherator_kernel B S hS 𝒳 f,
      isQuasicoherentOnSite_coherator_kernel hX hY f, ⟨isLimitMapCoheratorKernel B S hS 𝒳 f⟩⟩
    preservesFiniteLimits := hL
    preservesFiniteColimits := hC
    reflects := fun g hX hY hg ↦ isIso_of_isIso_moduleInverseImageU_map 𝒳 g hX hY hg }

/-- **`QCoh(𝒪_𝒳)` is abelian** (Stacks 06WV (2), at the universe of the schemes): the
abelian structure on the full subcategory of quasi-coherent modules supplied by
`AlgebraicGeometry.Stack.FlatFppf.relKernelData_qcohModules`. Its preadditive structure is the one
of the full subcategory, its cokernels are computed in `Mod(𝒪_𝒳)` and its kernels are the
`Q(Ker φ)`. -/
@[instance_reducible]
def abelianQCoh : Abelian (qcohModules 𝒳).FullSubcategory := by
  have hd := relKernelData_qcohModules 𝒳
  haveI : HasFiniteProducts (_root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :=
    Abelian.has_finite_products
  haveI := hd.hasKernels
  haveI := hd.isClosedUnderCokernels
  haveI := hd.isClosedUnderFiniteProducts
  haveI := fun {X Y : (qcohModules 𝒳).FullSubcategory} (f : X ⟶ Y) ↦
    hd.isIso_coimageImageComparison f
  exact Abelian.ofCoimageImageComparisonIsIso

/-- The coherent modules, as a property of the quasi-coherent modules. -/
abbrev cohInQCoh : ObjectProperty (qcohModules 𝒳).FullSubcategory :=
  fun M ↦ IsCoherent B S hS 𝒳 M.obj

/-- The restriction `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳) ⥤ Mod(flat-fppf)` to the flat objects. -/
abbrev qcohRestriction :
    (qcohModules 𝒳).FullSubcategory ⥤
      _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳) :=
  (qcohModules 𝒳).ι ⋙ moduleInverseImageU B S hS 𝒳

/-- The restriction to the flat objects carries kernels in `QCoh(𝒪_𝒳)` to kernels. -/
theorem preservesKernel_qcohRestriction {X Y : (qcohModules 𝒳).FullSubcategory} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) (qcohRestriction 𝒳) :=
  (relKernelData_qcohModules 𝒳).preservesKernel_ι_comp f

/-- The restriction to the flat objects carries cokernels in `QCoh(𝒪_𝒳)` to cokernels. -/
theorem preservesCokernel_qcohRestriction {X Y : (qcohModules 𝒳).FullSubcategory} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (qcohRestriction 𝒳) :=
  (relKernelData_qcohModules 𝒳).preservesCokernel_ι_comp f


/-- Sections at a flat object of the quasi-coherent modules: the restriction to the flat objects
followed by evaluation. -/
abbrev qcohSectionsAt (y : FlatFppf B S hS 𝒳) :
    (qcohModules 𝒳).FullSubcategory ⥤
      ModuleCat.{u} ((subsiteRingStructureSheaf B S hS 𝒳).obj.obj (op y)) :=
  qcohRestriction 𝒳 ⋙ _root_.SheafOfModules.evaluation _ (op y)

/-- **Sections at a flat object carry kernels in `QCoh(𝒪_𝒳)` to kernels.** If `f` is a kernel of
`g` in `QCoh(𝒪_𝒳)` then, at every flat object `y`, `ℱ(y) ⟶ 𝒢(y) ⟶ ℋ(y)` is left exact. This is
where the kernel `Q(Ker φ)` of `QCoh(𝒪_𝒳)` is used: `g^{-1}Q = g^{-1}`. -/
theorem injective_and_exact_sections_of_isLimit (y : FlatFppf B S hS 𝒳)
    {X Y Z : (qcohModules 𝒳).FullSubcategory} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0)
    (hc : IsLimit (KernelFork.ofι f w)) :
    Function.Injective ((qcohSectionsAt 𝒳 y).map f) ∧
      ∀ x, (qcohSectionsAt 𝒳 y).map g x = 0 → ∃ x', (qcohSectionsAt 𝒳 y).map f x' = x := by
  have := preservesKernel_qcohRestriction 𝒳 g
  have hl := (KernelFork.isLimitMapConeEquiv _ (qcohSectionsAt 𝒳 y))
    (isLimitOfPreserves (qcohSectionsAt 𝒳 y) hc)
  let T := ShortComplex.mk ((qcohSectionsAt 𝒳 y).map f) ((qcohSectionsAt 𝒳 y).map g)
    (by rw [← Functor.map_comp, w, Functor.map_zero])
  have hex : T.Exact := T.exact_of_f_is_kernel hl
  have hmono : Mono T.f := mono_of_isLimit_fork hl
  exact ⟨(ModuleCat.mono_iff_injective _).1 hmono, T.moduleCat_exact_iff.1 hex⟩

/-- A map of quasi-coherent modules is injective on sections over a flat object `y` once the
sections of its kernel inclusion vanish. -/
private theorem injective_qcohSectionsAt_map_of_kernel_ι_eq_zero
    [Abelian (qcohModules 𝒳).FullSubcategory] (y : FlatFppf B S hS 𝒳)
    {X Y : (qcohModules 𝒳).FullSubcategory} (f : X ⟶ Y)
    (h : ∀ z, ((qcohSectionsAt 𝒳 y).map (kernel.ι f)).hom z = 0) :
    Function.Injective ((qcohSectionsAt 𝒳 y).map f) := by
  obtain ⟨-, hex⟩ :=
    injective_and_exact_sections_of_isLimit 𝒳 y (kernel.condition f) (kernelIsKernel f)
  refine (injective_iff_map_eq_zero ((qcohSectionsAt 𝒳 y).map f).hom).2 fun x hx ↦ ?_
  obtain ⟨x', rfl⟩ := hex x hx
  exact h x'

/-- The sections of a coherent module over an object lying over an affine scheme are a finite
module. -/
theorem moduleFinite_sections_of_isCoherent
    {M : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (hM : IsCoherent B S hS 𝒳 M) {x : 𝒳.val.val.obj}
    (hx : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj x)) :
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M x
    Module.Finite (fibredSectionRing B S hS 𝒳.val.val.p x) (M.val.obj (op x)) :=
  moduleFinite_sections_of_isFiniteTypeOnSite_fibred 𝒳.val.isFiberedInGroupoids M
    (isCartesianBetweenAffines_of_isQuasicoherentOnSite _ M hM.1.1) hM.1.2 hx

variable {𝒳} in
/-- **A coherence criterion on a locally Noetherian algebraic stack.** A quasi-coherent module
whose sections over every flat object lying over a Noetherian affine scheme form a finite module
is coherent: over such an object `y` its sections are finitely presented, so by the cartesian
property it has a finite global presentation on the slice at `y`, and on a locally Noetherian
stack the objects mapping to such `y` cover. -/
theorem isCoherent_of_moduleFinite_sections
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {M : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (hM : M.IsQuasicoherentOnSite)
    (hfin : ∀ y : FlatFppf B S hS 𝒳,
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj) →
      IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p y.obj) →
      letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M y.obj
      Module.Finite (fibredSectionRing B S hS 𝒳.val.val.p y.obj) (M.val.obj (op y.obj))) :
    IsCoherent B S hS 𝒳 M := by
  have hcart := isCartesianBetweenAffines_of_isQuasicoherentOnSite _ M hM
  refine (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).2 ⟨fun U ↦ ?_⟩
  refine ⟨Σ w : 𝒳.val.val.obj, {g : w ⟶ U // noetherianFlatSieve 𝒳 U g}, fun i ↦ i.1,
    fun i ↦ i.2.1, ?_, fun i ↦ ?_⟩
  · refine GrothendieckTopology.superset_covering _ ?_ (noetherianFlatSieve_mem 𝒳 h𝒳 U)
    intro Y h hh
    exact ⟨Y, 𝟙 Y, h, Presieve.ofArrows.mk (⟨Y, h, hh⟩ :
      Σ w : 𝒳.val.val.obj, {g : w ⟶ U // noetherianFlatSieve 𝒳 U g}), Category.id_comp h⟩
  · obtain ⟨w, g, y, hyaff, hnoeth, ⟨c⟩⟩ := i
    let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M y.obj
    have := hfin y hyaff hnoeth
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap _ c
      (hasFiniteGlobalPresentation_over_of_finitePresentation _ M hcart hyaff
        (Module.finitePresentation_of_finite _ _))

variable {𝒳} in
/-- **A submodule of a finite module over a Noetherian ring, read on sections.** If a map of
modules is injective on the sections over a flat object `y` lying over a Noetherian affine scheme
and its target is coherent, the sections of its source over `y` are a finite module. -/
theorem moduleFinite_sections_of_injective
    {M N : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)} (φ : M ⟶ N)
    (hN : IsCoherent B S hS 𝒳 N) (y : FlatFppf B S hS 𝒳)
    (hyaff : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj))
    (hnoeth : IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p y.obj))
    (hinj : Function.Injective (φ.val.app (op y.obj))) :
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M y.obj
    Module.Finite (fibredSectionRing B S hS 𝒳.val.val.p y.obj) (M.val.obj (op y.obj)) := by
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids M y.obj
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids N y.obj
  have := moduleFinite_sections_of_isCoherent 𝒳 hN hyaff
  have : _root_.IsNoetherian (fibredSectionRing B S hS 𝒳.val.val.p y.obj)
      (N.val.obj (op y.obj)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let φL : M.val.obj (op y.obj) →ₗ[fibredSectionRing B S hS 𝒳.val.val.p y.obj]
      N.val.obj (op y.obj) := (φ.val.app (op y.obj)).hom
  exact Module.Finite.of_injective φL hinj

variable {𝒳} in
/-- **Closure under subobjects.** On a locally Noetherian algebraic stack, a subobject in
`QCoh(𝒪_𝒳)` of a coherent module is coherent. -/
theorem isCoherent_of_mono_qcoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {X Y : (qcohModules 𝒳).FullSubcategory} (m : X ⟶ Y) [Mono m]
    (hY : IsCoherent B S hS 𝒳 Y.obj) : IsCoherent B S hS 𝒳 X.obj := by
  let := abelianQCoh 𝒳
  refine isCoherent_of_moduleFinite_sections h𝒳 X.2 fun y hyaff hnoeth ↦
    moduleFinite_sections_of_injective m.hom hY y hyaff hnoeth ?_
  have hz : kernel.ι m = 0 := (isZero_kernel_of_mono m).eq_of_src _ _
  exact injective_qcohSectionsAt_map_of_kernel_ι_eq_zero 𝒳 y m fun z ↦ by
    rw [hz, Functor.map_zero]
    rfl

variable {𝒳} in
/-- **Stacks 0GRB, part (1).** Let `𝒳` be a locally Noetherian algebraic stack and
`φ : ℱ ⟶ 𝒢` a surjective map of quasi-coherent `𝒪_𝒳`-modules. If `ℱ` is coherent, so is `𝒢`.

Surjectivity is `CategoryTheory.Epi` in `Mod(𝒪_𝒳)`, i.e. local surjectivity; an epimorphism of
`QCoh(𝒪_𝒳)` is one of `Mod(𝒪_𝒳)` (`AlgebraicGeometry.Stack.FlatFppf.epi_hom_of_epi_qcoh`), so
this is also the statement for surjections in `QCoh(𝒪_𝒳)`. Coherence is
`AlgebraicGeometry.Stack.IsCoherent` (Stacks 0GR6). Finite type passes to quotients and, on a
locally Noetherian stack, a quasi-coherent module of finite type is coherent (Stacks 0GR5). -/
@[stacks 0GRB "part (1): if F is coherent and φ : F → G is a surjection of quasi-coherent \
  modules then G is coherent"]
theorem isCoherent_of_epi
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)} (φ : F ⟶ G) [Epi φ]
    (hF : IsCoherent B S hS 𝒳 F) (hG : G.IsQuasicoherentOnSite) :
    IsCoherent B S hS 𝒳 G :=
  ((isCoherent_tfae B S hS 𝒳 h𝒳 G).out 1 2).2
    (show IsQuasicoherentFiniteTypeModule B S hS 𝒳 G from
      ⟨hG, Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi φ hF.1.2⟩)

variable {𝒳} in
/-- An epimorphism of `QCoh(𝒪_𝒳)` is an epimorphism of `Mod(𝒪_𝒳)`: the cokernel computed in
`Mod(𝒪_𝒳)` is quasi-coherent (Stacks 0GQL (1)), so its projection vanishes. -/
theorem epi_hom_of_epi_qcoh {X Y : (qcohModules 𝒳).FullSubcategory} (e : X ⟶ Y) [Epi e] :
    Epi e.hom := by
  have hcok := isClosedUnderCokernels_qcohModules 𝒳
  let c : Y ⟶ ⟨cokernel e.hom, ObjectProperty.prop_cokernel _ e.hom X.2 Y.2⟩ :=
    (qcohModules 𝒳).homMk (cokernel.π e.hom)
  have hc : c = 0 := (cancel_epi e).1 (by ext1; simp [c])
  exact Abelian.epi_of_cokernel_π_eq_zero _ (congrArg (fun t ↦ t.hom) hc)

variable {𝒳} in
/-- **Closure under quotients.** On a locally Noetherian algebraic stack, a quotient in
`QCoh(𝒪_𝒳)` of a coherent module is coherent. -/
theorem isCoherent_of_epi_qcoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {X Y : (qcohModules 𝒳).FullSubcategory} (e : X ⟶ Y) [Epi e]
    (hX : IsCoherent B S hS 𝒳 X.obj) : IsCoherent B S hS 𝒳 Y.obj :=
  have := epi_hom_of_epi_qcoh e
  isCoherent_of_epi h𝒳 e.hom hX Y.2

variable {𝒳} in
/-- **Closure under extensions.** On a locally Noetherian algebraic stack, the middle term of a
short exact sequence in `QCoh(𝒪_𝒳)` with coherent outer terms is coherent. -/
theorem isCoherent_X₂_of_shortExact_qcoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {T : ShortComplex (qcohModules 𝒳).FullSubcategory} (hT : T.ShortExact)
    (h₁ : IsCoherent B S hS 𝒳 T.X₁.obj) (h₃ : IsCoherent B S hS 𝒳 T.X₃.obj) :
    IsCoherent B S hS 𝒳 T.X₂.obj := by
  let := abelianQCoh 𝒳
  refine isCoherent_of_moduleFinite_sections h𝒳 T.X₂.2 fun y hyaff hnoeth ↦ ?_
  obtain ⟨-, hex⟩ := injective_and_exact_sections_of_isLimit 𝒳 y T.zero hT.fIsKernel
  let A := fibredSectionRing B S hS 𝒳.val.val.p y.obj
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids T.X₁.obj y.obj
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids T.X₂.obj y.obj
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids T.X₃.obj y.obj
  have h1 := moduleFinite_sections_of_isCoherent 𝒳 h₁ hyaff
  have := moduleFinite_sections_of_isCoherent 𝒳 h₃ hyaff
  have : _root_.IsNoetherian A (T.X₃.obj.val.obj (op y.obj)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let fL : T.X₁.obj.val.obj (op y.obj) →ₗ[A] T.X₂.obj.val.obj (op y.obj) :=
    ((qcohSectionsAt 𝒳 y).map T.f).hom
  let gL : T.X₂.obj.val.obj (op y.obj) →ₗ[A] T.X₃.obj.val.obj (op y.obj) :=
    ((qcohSectionsAt 𝒳 y).map T.g).hom
  have hker : ⊤ ⊓ LinearMap.ker gL = Submodule.map fL ⊤ := by
    rw [top_inf_eq, ← LinearMap.range_eq_map]
    refine le_antisymm (fun x hx ↦ hex x hx) ?_
    rintro _ ⟨x, rfl⟩
    change ((qcohSectionsAt 𝒳 y).map T.f ≫ (qcohSectionsAt 𝒳 y).map T.g) x = 0
    rw [← Functor.map_comp, T.zero, Functor.map_zero]
    rfl
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker gL (IsNoetherian.noetherian _) ?_⟩
  rw [hker]
  exact h1.fg_top.map fL

variable {𝒳} in
/-- A coherent zero object of `QCoh(𝒪_𝒳)`: the cokernel of the identity of `𝒪_𝒳`. -/
theorem containsZero_cohInQCoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (cohInQCoh 𝒳).ContainsZero := by
  have hcoh := isCoherent_cokernel_id_unit h𝒳
  exact ⟨⟨⟨_, hcoh.1.1⟩, IsZero.of_full_of_faithful_of_isZero (qcohModules 𝒳).ι
    ⟨_, hcoh.1.1⟩ (isZero_cokernel_of_epi _), hcoh⟩⟩

end FlatFppf

attribute [local instance] FlatFppf.hasSheafify_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0GRB: `Coh(𝒪_𝒳)` is a Serre subcategory of `QCoh(𝒪_𝒳)`**, for a locally
Noetherian algebraic stack `𝒳`. Here `QCoh(𝒪_𝒳)` is the full subcategory of the quasi-coherent
`𝒪_𝒳`-modules on the big fppf site, with the abelian structure
`AlgebraicGeometry.Stack.FlatFppf.abelianQCoh` (its kernels are the `Q(Ker φ)`, its cokernels are
computed in `Mod(𝒪_𝒳)`), and `Coh(𝒪_𝒳)` is cut out by `AlgebraicGeometry.Stack.IsCoherent`
(Stacks 0GR6). `CategoryTheory.ObjectProperty.IsSerreClass` is the Serre-subcategory condition:
a coherent zero object, and closure under subobjects, quotients and extensions in `QCoh(𝒪_𝒳)`. -/
@[stacks 0GRB "Coh(O_X) is a Serre subcategory of QCoh(O_X)"]
theorem isSerreClass_coh_qcoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    letI := FlatFppf.abelianQCoh 𝒳
    (FlatFppf.cohInQCoh 𝒳).IsSerreClass := by
  let := FlatFppf.abelianQCoh 𝒳
  have := FlatFppf.containsZero_cohInQCoh h𝒳
  exact
  { prop_of_mono := fun m _ hY ↦ FlatFppf.isCoherent_of_mono_qcoh h𝒳 m hY
    prop_of_epi := fun e _ hX ↦ FlatFppf.isCoherent_of_epi_qcoh h𝒳 e hX
    prop_X₂_of_shortExact := fun hT h₁ h₃ ↦ FlatFppf.isCoherent_X₂_of_shortExact_qcoh h𝒳 hT h₁ h₃ }

/-- **Stacks 0GRB, part (2).** Let `𝒳` be a locally Noetherian algebraic stack and
`φ : ℱ ⟶ 𝒢` a map of quasi-coherent `𝒪_𝒳`-modules with `ℱ` coherent. Then the image of `φ` is
coherent.

The image is the image of `φ` in the abelian category `QCoh(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.FlatFppf.abelianQCoh`), which is the reading of Stacks 0GQL (2) the
source's Remark sets up; it is a quotient of `ℱ` in `QCoh(𝒪_𝒳)`. The image computed in
`Mod(𝒪_𝒳)` need not be quasi-coherent, already for `2 : 𝒪 ⟶ 𝒪` on `Spec ℤ`
(`AlgebraicGeometry.Stack.exists_not_isCoherent_image_of_isCoherent`), so it is not the object of
the clause. -/
@[stacks 0GRB "part (2): if F is coherent then the image of φ : F → G in QCoh(O_X) is coherent; \
  the image computed in Mod(O_X) need not be quasi-coherent \
  (exists_not_isCoherent_image_of_isCoherent)"]
theorem isCoherent_image_qcoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : (FlatFppf.qcohModules 𝒳).FullSubcategory} (φ : F ⟶ G)
    (hF : IsCoherent B S hS 𝒳 F.obj) :
    letI := FlatFppf.abelianQCoh 𝒳
    IsCoherent B S hS 𝒳 (Limits.image φ).obj := by
  let := FlatFppf.abelianQCoh 𝒳
  exact FlatFppf.isCoherent_of_epi_qcoh h𝒳 (factorThruImage φ) hF

/-- **Stacks 0GRB, part (3).** Let `𝒳` be a locally Noetherian algebraic stack and
`φ : ℱ ⟶ 𝒢` a map of quasi-coherent `𝒪_𝒳`-modules. If `𝒢` is coherent and `Ker(φ)` is parasitic
(Stacks 0773), then `ℱ` is coherent.

Here `Ker(φ)` is the kernel computed in `Mod(𝒪_𝒳)`, as in Stacks 0GR9 and 0GQL. The variant with
the kernel taken in `QCoh(𝒪_𝒳)` is `AlgebraicGeometry.Stack.isCoherent_of_isParasitic_kernel_qcoh`.
On sections over a flat object the map `φ` is injective, its kernel there vanishing; so over a
flat object lying over a Noetherian affine scheme the sections of `ℱ` form a submodule of a finite
module, which suffices on a locally Noetherian stack
(`AlgebraicGeometry.Stack.FlatFppf.isCoherent_of_moduleFinite_sections`). -/
@[stacks 0GRB "part (3): if G is coherent and Ker(φ), computed in Mod(O_X), is parasitic, then F \
  is coherent"]
theorem isCoherent_of_isParasitic_kernel
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : _root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)}
    (hF : F.IsQuasicoherentOnSite) (φ : F ⟶ G) (hG : IsCoherent B S hS 𝒳 G)
    (hK : IsParasitic B S hS 𝒳 .fppf (kernel φ).val) :
    IsCoherent B S hS 𝒳 F := by
  refine FlatFppf.isCoherent_of_moduleFinite_sections h𝒳 hF fun y hyaff hnoeth ↦
    FlatFppf.moduleFinite_sections_of_injective φ hG y hyaff hnoeth ?_
  refine (injective_iff_map_eq_zero (φ.val.app (op y.obj)).hom).2 fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := _root_.SheafOfModules.exists_kernel_val_app φ (op y.obj) x hx
  have := hK y.obj y.property
  rw [Subsingleton.elim z 0, map_zero]

/-- **Stacks 0GRB, part (3), with the kernel taken in `QCoh(𝒪_𝒳)`.** Let `𝒳` be a locally
Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of quasi-coherent `𝒪_𝒳`-modules. If `𝒢` is
coherent and the kernel of `φ` in the abelian category `QCoh(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.FlatFppf.abelianQCoh`, kernel `Q(Ker φ)`) is parasitic, then `ℱ` is
coherent. -/
@[stacks 0GRB "part (3), the kernel read in QCoh(O_X): if G is coherent and the kernel of φ in \
  QCoh(O_X) is parasitic, then F is coherent"]
theorem isCoherent_of_isParasitic_kernel_qcoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : (FlatFppf.qcohModules 𝒳).FullSubcategory} (φ : F ⟶ G)
    (hG : IsCoherent B S hS 𝒳 G.obj) :
    letI := FlatFppf.abelianQCoh 𝒳
    IsParasitic B S hS 𝒳 .fppf (kernel φ).obj.val → IsCoherent B S hS 𝒳 F.obj := by
  let := FlatFppf.abelianQCoh 𝒳
  intro hK
  refine FlatFppf.isCoherent_of_moduleFinite_sections h𝒳 F.2 fun y hyaff hnoeth ↦
    FlatFppf.moduleFinite_sections_of_injective φ.hom hG y hyaff hnoeth ?_
  refine FlatFppf.injective_qcohSectionsAt_map_of_kernel_ι_eq_zero 𝒳 y φ fun z ↦ ?_
  have hz : z = 0 := @Subsingleton.elim _ (hK y.obj y.property) z 0
  rw [hz, map_zero]

end AlgebraicGeometry.Stack

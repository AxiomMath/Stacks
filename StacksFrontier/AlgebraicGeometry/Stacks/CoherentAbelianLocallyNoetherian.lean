module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfKernelPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentCokernelLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentExtensionLocallyNoetherian

/-!
# `Coh(𝒪_𝒳)` is abelian on a locally Noetherian algebraic stack

Let `𝒳` be a locally Noetherian algebraic stack. The coherent modules satisfy the hypotheses of
`CategoryTheory.ObjectProperty.RelKernelData` inside `Mod(𝒪_𝒳)`, relative to the quasi-coherent
modules and the restriction `g^{-1}` to the flat-fppf site:

* they are closed under cokernels (`AlgebraicGeometry.Stack.isCoherent_cokernel`), under
  isomorphisms and finite biproducts, and contain a zero object;
* for a map `φ` of coherent modules, `Q(Ker φ) ⟶ ℱ` is a kernel of `φ` relative to the
  quasi-coherent modules (`AlgebraicGeometry.Stack.FlatFppf.isRelKernel_coherator_kernel`), with
  `Q(Ker φ)` coherent (`AlgebraicGeometry.Stack.FlatFppf.isCoherent_coherator_kernel`) and carried
  by `g^{-1}` to a kernel of `g^{-1}φ`;
* `g^{-1}` is exact and reflects isomorphisms between quasi-coherent modules.

Hence `Coh(𝒪_𝒳)` is abelian, its kernels are the `Q(Ker φ)`, its cokernels are computed in
`Mod(𝒪_𝒳)`, its images are the `Q(Im φ)`, and `Coh(𝒪_𝒳) → QCoh(𝒪_𝒳)` preserves kernels and
cokernels.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.relKernelData_coherentModules`: the coherent modules satisfy
  the hypotheses of `CategoryTheory.ObjectProperty.RelKernelData`.
* `AlgebraicGeometry.Stack.nonempty_abelian_coh`: `Coh(𝒪_𝒳)` is abelian.
* `AlgebraicGeometry.Stack.preservesFiniteLimits_preservesFiniteColimits_coh_qcoh`:
  `Coh(𝒪_𝒳) → QCoh(𝒪_𝒳)` is exact.
* `AlgebraicGeometry.Stack.isCoherent_coherator_kernel_and_isLimit`: the kernel of a map of
  coherent modules in `Coh(𝒪_𝒳)` is `Q(Ker φ)`.
* `AlgebraicGeometry.Stack.isCoherent_coherator_image`: the image of a map of coherent modules in
  `Coh(𝒪_𝒳)` is `Q(Im φ)`.

## References

* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

namespace FlatFppf

attribute [local instance] hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- `g^{-1}` reflects isomorphisms between quasi-coherent modules. -/
theorem isIso_of_isIso_moduleInverseImageU_map
    {X Y : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)} (g : X ⟶ Y)
    (hX : X.IsQuasicoherentOnSite) (hY : Y.IsQuasicoherentOnSite)
    (hg : IsIso ((moduleInverseImageU B S hS 𝒳).map g)) : IsIso g := by
  refine isIso_of_isQuasicoherentOnSite_of_bijective_flat 𝒳 g hX hY fun y hy ↦ ?_
  have := Functor.map_isIso (_root_.SheafOfModules.evaluation _ (op (⟨y, hy⟩ :
    FlatFppf B S hS 𝒳))) ((moduleInverseImageU B S hS 𝒳).map g)
  exact ConcreteCategory.bijective_of_isIso
    ((_root_.SheafOfModules.evaluation _ (op (⟨y, hy⟩ : FlatFppf B S hS 𝒳))).map
      ((moduleInverseImageU B S hS 𝒳).map g))

variable {𝒳}
variable (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
  (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
include h𝒳

/-- A zero object of `Mod(𝒪_𝒳)` which is coherent: the cokernel of the identity of `𝒪_𝒳`. -/
theorem isCoherent_cokernel_id_unit :
    IsCoherent B S hS 𝒳 (cokernel (𝟙 (_root_.SheafOfModules.unit
      (ambientRingStructureSheaf B S hS 𝒳)))) :=
  isCoherent_cokernel B S hS 𝒳 h𝒳 (isCoherent_unit B S hS 𝒳 h𝒳) (isCoherent_unit B S hS 𝒳 h𝒳) _

/-- Coherent modules are closed under isomorphisms. -/
theorem isClosedUnderIsomorphisms_coherentModules :
    (coherentModules.{u, u, w} B S hS 𝒳).IsClosedUnderIsomorphisms :=
  ⟨fun e hM ↦ (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).2
    (SheafOfModules.IsFinitePresentationOnSite.of_iso e
      ((isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).1 hM))⟩

/-- Coherent modules contain a zero object. -/
theorem containsZero_coherentModules : (coherentModules.{u, u, w} B S hS 𝒳).ContainsZero :=
  ⟨⟨_, isZero_cokernel_of_epi _, isCoherent_cokernel_id_unit h𝒳⟩⟩

/-- Coherent modules are closed under binary products. -/
theorem isClosedUnderBinaryProducts_coherentModules :
    (coherentModules.{u, u, w} B S hS 𝒳).IsClosedUnderBinaryProducts := by
  refine ⟨fun X ⟨p⟩ ↦ ?_⟩
  have ht := (IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).symm p.isLimit
  let c := BinaryBicone.ofLimitCone ht
  have hc := binaryBiconeIsBilimitOfLimitConeOfIsLimit ht
  exact isCoherent_X₂_of_kernel_cokernel B S hS 𝒳 h𝒳 c.inl_snd
    (BinaryBicone.isLimitSndKernelFork hc.isLimit)
    (BinaryBicone.isColimitInlCokernelCofork hc.isColimit)
    (p.prop_diag_obj ⟨WalkingPair.left⟩) (p.prop_diag_obj ⟨WalkingPair.right⟩)

/-- The coherent modules satisfy the hypotheses of `RelKernelData` relative to the
quasi-coherent modules and the restriction `g^{-1}` to the flat-fppf site. -/
theorem relKernelData_coherentModules :
    ObjectProperty.RelKernelData
      (_root_.SheafOfModules.isQuasicoherentOnSite (ambientRingStructureSheaf B S hS 𝒳) :
        ObjectProperty (_root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)))
      (coherentModules.{u, u, w} B S hS 𝒳)
      (moduleInverseImageU B S hS 𝒳) := by
  have := isClosedUnderIsomorphisms_coherentModules h𝒳
  have := containsZero_coherentModules h𝒳
  have := isClosedUnderBinaryProducts_coherentModules h𝒳
  have : HasFiniteProducts (_root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :=
    Abelian.has_finite_products
  have hfp : (coherentModules.{u, u, w} B S hS 𝒳).IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  have : PreservesLimitsOfSize.{u, u} (moduleInverseImageU B S hS 𝒳) :=
    (moduleLowerShriekAdjunctionU B S hS 𝒳).rightAdjoint_preservesLimits
  have hL : PreservesFiniteLimits (moduleInverseImageU B S hS 𝒳) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  have hC : PreservesFiniteColimits (moduleInverseImageU B S hS 𝒳) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact
  { le := fun M hM ↦ hM.1.1
    isClosedUnderIsomorphisms := inferInstance
    containsZero := inferInstance
    isClosedUnderFiniteProducts := hfp
    prop_cokernel := fun f hX hY ↦ isCoherent_cokernel B S hS 𝒳 h𝒳 hX hY f
    exists_relKernel := fun f hX hY ↦ ⟨_, _, isRelKernel_coherator_kernel B S hS 𝒳 f,
      isCoherent_coherator_kernel 𝒳 h𝒳 hX hY f, ⟨isLimitMapCoheratorKernel B S hS 𝒳 f⟩⟩
    preservesFiniteLimits := hL
    preservesFiniteColimits := hC
    reflects := fun g hX hY hg ↦ isIso_of_isIso_moduleInverseImageU_map 𝒳 g hX hY hg }

end FlatFppf

attribute [local instance] FlatFppf.hasSheafify_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- The category of coherent `𝒪_𝒳`-modules is abelian, for a locally Noetherian algebraic stack
`𝒳`. Its kernels are the `Q(Ker φ)` and its cokernels are computed in
`Mod(𝒪_𝒳)` (`AlgebraicGeometry.Stack.FlatFppf.relKernelData_coherentModules`). -/
@[stacks 0GR9 "the category Coh(O_X) of coherent modules (Stacks 0GR6) on a locally Noetherian \
  algebraic stack is abelian, with kernels Q(Ker φ) and cokernels computed in Mod(O_X)"]
theorem nonempty_abelian_coh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    Nonempty (Abelian (Coh.{u, u, w} B S hS 𝒳)) :=
  (FlatFppf.relKernelData_coherentModules h𝒳).nonempty_abelian

/-- The inclusion `Coh(𝒪_𝒳) → QCoh(𝒪_𝒳)` is exact, for a locally Noetherian algebraic stack `𝒳`:
it preserves finite limits and finite colimits. Here `QCoh(𝒪_𝒳)` is the full subcategory of
`Mod(𝒪_𝒳)` of the quasi-coherent modules. -/
@[stacks 0GR9 "the inclusion functor Coh(O_X) → QCoh(O_X) is exact"]
theorem preservesFiniteLimits_preservesFiniteColimits_coh_qcoh
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    PreservesFiniteLimits
        (ObjectProperty.ιOfLE (FlatFppf.relKernelData_coherentModules h𝒳).le) ∧
      PreservesFiniteColimits
        (ObjectProperty.ιOfLE (FlatFppf.relKernelData_coherentModules h𝒳).le) := by
  let hd := FlatFppf.relKernelData_coherentModules h𝒳
  have := hd.hasKernels
  have := hd.isClosedUnderCokernels
  have := hd.isClosedUnderFiniteProducts
  have := hd.containsZero
  have : (_root_.SheafOfModules.isQuasicoherentOnSite
      (FlatFppf.ambientRingStructureSheaf B S hS 𝒳) : ObjectProperty
        (_root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳))).ContainsZero :=
    ⟨⟨_, isZero_cokernel_of_epi _, (FlatFppf.isCoherent_cokernel_id_unit h𝒳).1.1⟩⟩
  have : HasEqualizers (Coh.{u, u, w} B S hS 𝒳) := Preadditive.hasEqualizers_of_hasKernels
  have : HasCoequalizers (Coh.{u, u, w} B S hS 𝒳) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  have : HasFiniteProducts
      (_root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)) :=
    Abelian.has_finite_products
  have : HasFiniteProducts (Coh.{u, u, w} B S hS 𝒳) :=
    inferInstanceAs (HasFiniteProducts (coherentModules.{u, u, w} B S hS 𝒳).FullSubcategory)
  have : HasFiniteBiproducts (coherentModules.{u, u, w} B S hS 𝒳).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts (coherentModules.{u, u, w} B S hS 𝒳).FullSubcategory :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : (ObjectProperty.ιOfLE hd.le).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have hk := fun {X Y : Coh.{u, u, w} B S hS 𝒳} (f : X ⟶ Y) ↦ hd.preservesKernel_ιOfLE f
  have hc := fun {X Y : Coh.{u, u, w} B S hS 𝒳} (f : X ⟶ Y) ↦ hd.preservesCokernel_ιOfLE f
  exact ⟨Functor.preservesFiniteLimits_of_preservesKernels _,
    Functor.preservesFiniteColimits_of_preservesCokernels _⟩

/-- For a map `φ : ℱ ⟶ 𝒢` of coherent modules on a locally Noetherian algebraic stack, `Q(Ker φ)`
is coherent and `Q(Ker φ) ⟶ Ker φ ⟶ ℱ` is a kernel of `φ` in `Coh(𝒪_𝒳)`. Here `Q = g_!g^{-1}` with
its counit is the coherator: composing with `Q(K) ⟶ K` is a bijection on maps out of quasi-coherent
modules (`AlgebraicGeometry.Stack.FlatFppf.bijective_comp_coheratorCounit`). -/
theorem isCoherent_coherator_kernel_and_isLimit
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : _root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)}
    (hF : IsCoherent B S hS 𝒳 F) (hG : IsCoherent B S hS 𝒳 G) (φ : F ⟶ G) :
    ∃ hK : IsCoherent B S hS 𝒳 ((FlatFppf.lowerShriekInverseImageCoherator B S hS 𝒳).obj (kernel
        φ)),
      Nonempty (IsLimit (KernelFork.ofι
        (f := ((coherentModules.{u, u, w} B S hS 𝒳).homMk φ : (⟨F, hF⟩ : Coh B S hS 𝒳) ⟶ ⟨G, hG⟩))
        ((coherentModules.{u, u, w} B S hS 𝒳).homMk
          ((FlatFppf.coheratorCounit B S hS 𝒳).app (kernel φ) ≫ kernel.ι φ) :
            (⟨_, hK⟩ : Coh B S hS 𝒳) ⟶ ⟨F, hF⟩)
        (by ext1; exact (FlatFppf.isRelKernel_coherator_kernel B S hS 𝒳 φ).1))) :=
  ⟨FlatFppf.isCoherent_coherator_kernel 𝒳 h𝒳 hF hG φ,
    ⟨(FlatFppf.isRelKernel_coherator_kernel B S hS 𝒳 φ).isLimitFullSubcategory
      (FlatFppf.relKernelData_coherentModules h𝒳).le hF hG _⟩⟩

/-- Let `φ : ℱ ⟶ 𝒢` be a map of coherent modules on a locally Noetherian algebraic stack and
`Im φ = Ker(𝒢 ⟶ Coker φ)` its image computed in `Mod(𝒪_𝒳)`. Then `Q(Im φ)` is coherent and
`Q(Im φ) ⟶ Im φ ⟶ 𝒢` is the image of `φ` in `Coh(𝒪_𝒳)`, i.e. a kernel in `Coh(𝒪_𝒳)` of the cokernel
`𝒢 ⟶ Coker φ`, which is coherent.

`Im φ` itself need not be coherent
(`AlgebraicGeometry.Stack.exists_not_isCoherent_image_of_isCoherent`). -/
@[stacks 0GR9 "part (2), corrected reading: the image computed in Mod(O_X) need not be coherent \
  (exists_not_isCoherent_image_of_isCoherent); Q(Im φ) is coherent and is the image of φ in \
  Coh(O_X)"]
theorem isCoherent_coherator_image
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : _root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)}
    (hF : IsCoherent B S hS 𝒳 F) (hG : IsCoherent B S hS 𝒳 G) (φ : F ⟶ G) :
    ∃ (hC : IsCoherent B S hS 𝒳 (cokernel φ))
      (hK : IsCoherent B S hS 𝒳 ((FlatFppf.lowerShriekInverseImageCoherator B S hS 𝒳).obj
        (kernel (cokernel.π φ)))),
      Nonempty (IsLimit (KernelFork.ofι
        (f := ((coherentModules.{u, u, w} B S hS 𝒳).homMk (cokernel.π φ) :
          (⟨G, hG⟩ : Coh B S hS 𝒳) ⟶ ⟨cokernel φ, hC⟩))
        ((coherentModules.{u, u, w} B S hS 𝒳).homMk
          ((FlatFppf.coheratorCounit B S hS 𝒳).app (kernel (cokernel.π φ)) ≫
            kernel.ι (cokernel.π φ)) : (⟨_, hK⟩ : Coh B S hS 𝒳) ⟶ ⟨G, hG⟩)
        (by ext1; exact (FlatFppf.isRelKernel_coherator_kernel B S hS 𝒳 (cokernel.π φ)).1))) :=
  have hC := isCoherent_cokernel B S hS 𝒳 h𝒳 hF hG φ
  ⟨hC, isCoherent_coherator_kernel_and_isLimit 𝒳 h𝒳 hG hC (cokernel.π φ)⟩

end AlgebraicGeometry.Stack

end

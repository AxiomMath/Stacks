module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfQuasicoherentLowerShriek
public import StacksFrontier.CategoryTheory.Abelian.CoreflectedKernels

/-!
# The coherator `Q = g_!g^{-1}` of an algebraic stack (Stacks 0779, 0GQK)

Let `𝒳` be an algebraic stack, `g^{-1}` the restriction of sheaves of `𝒪_𝒳`-modules to the
flat-fppf site and `g_!` its left adjoint (Stacks 0789 (2)). The functor `Q = g_!g^{-1}` with the
counit `Q ⟶ id` of `g_! ⊣ g^{-1}` is the coherator: for every `𝒪_𝒳`-module `K` and every
quasi-coherent `Z`, composing with the counit `Q(K) ⟶ K` is a bijection
`Hom(Z, Q(K)) ≃ Hom(Z, K)` (`AlgebraicGeometry.Stack.FlatFppf.bijective_comp_coheratorCounit`).
Wherever `Q(K)` is quasi-coherent it is therefore the coreflection of `K` into quasi-coherent
modules, the defining property of the right adjoint `Q` of Stacks 0778 / 0781 (2). On a
quasi-coherent module the counit is an isomorphism (Stacks 0779 (1),
`AlgebraicGeometry.Stack.FlatFppf.isIso_moduleLowerShriekAdjunctionU_counit_app`), and `g^{-1}`
of the counit is always an isomorphism (`g^{-1}Q = g^{-1}`, the parasitic discrepancy of
Stacks 0779 (2) being invisible on flat objects).

For a map `φ : ℱ ⟶ 𝒢` the composite `Q(Ker φ) ⟶ Ker φ ⟶ ℱ` is a kernel of `φ` relative to the
quasi-coherent modules (`AlgebraicGeometry.Stack.FlatFppf.isRelKernel_coherator_kernel`) and is
carried by `g^{-1}` to a kernel of `g^{-1}φ`: this is the shape of the kernel clause of Stacks 0GQL
(3) and 0GR9 (3).

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0GQK](https://stacks.math.columbia.edu/tag/0GQK)
* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

namespace FlatFppf

attribute [local instance] hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The coherator `Q = g_!g^{-1}`** on `𝒪_𝒳`-modules, `g` the flat-fppf morphism of topoi of
Stacks 0788 (2). -/
abbrev lowerShriekInverseImageCoherator :
    _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) :=
  moduleInverseImageU B S hS 𝒳 ⋙ moduleLowerShriekU B S hS 𝒳

/-- The counit `Q ⟶ id` of the coherator: the counit of `g_! ⊣ g^{-1}`. -/
abbrev coheratorCounit : lowerShriekInverseImageCoherator B S hS 𝒳 ⟶ 𝟭 _ :=
  (moduleLowerShriekAdjunctionU B S hS 𝒳).counit

/-- **`g^{-1}Q = g^{-1}`**: the restriction of the counit to the flat objects is an isomorphism, by
the triangle identity and `g^{-1}g_! = id`. -/
instance isIso_moduleInverseImageU_map_coheratorCounit_app
    (K : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :
    IsIso ((moduleInverseImageU B S hS 𝒳).map ((coheratorCounit B S hS 𝒳).app K)) := by
  have hu := isIso_moduleLowerShriekAdjunctionU_unit B S hS 𝒳
  have h := (moduleLowerShriekAdjunctionU B S hS 𝒳).right_triangle_components K
  have : IsIso ((moduleLowerShriekAdjunctionU B S hS 𝒳).unit.app
      ((moduleInverseImageU B S hS 𝒳).obj K) ≫ (moduleInverseImageU B S hS 𝒳).map
        ((moduleLowerShriekAdjunctionU B S hS 𝒳).counit.app K)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left ((moduleLowerShriekAdjunctionU B S hS 𝒳).unit.app
    ((moduleInverseImageU B S hS 𝒳).obj K)) _

/-- **Stacks 0779 (1)**: on a quasi-coherent module the counit `Q(H) ⟶ H` is an isomorphism. -/
theorem isIso_coheratorCounit_app
    (H : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hH : H.IsQuasicoherentOnSite) : IsIso ((coheratorCounit B S hS 𝒳).app H) :=
  isIso_moduleLowerShriekAdjunctionU_counit_app B S hS H hH

/-- **The coreflection property of the coherator**: for a quasi-coherent `Z` and any `K`,
composing with the counit `Q(K) ⟶ K` is a bijection `Hom(Z, Q(K)) ≃ Hom(Z, K)`. -/
theorem bijective_comp_coheratorCounit
    {Z K : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (hZ : Z.IsQuasicoherentOnSite) :
    Function.Bijective (fun t : Z ⟶ (lowerShriekInverseImageCoherator B S hS 𝒳).obj K ↦
      t ≫ (coheratorCounit B S hS 𝒳).app K) := by
  have := isIso_coheratorCounit_app B S hS 𝒳 Z hZ
  refine ⟨fun t₁ t₂ h ↦ ?_, fun t ↦ ⟨inv ((coheratorCounit B S hS 𝒳).app Z) ≫
    (lowerShriekInverseImageCoherator B S hS 𝒳).map t, ?_⟩⟩
  · have e := congrArg (fun x ↦ (moduleInverseImageU B S hS 𝒳).map x) h
    simp only [Functor.map_comp] at e
    have h' : (moduleInverseImageU B S hS 𝒳).map t₁ = (moduleInverseImageU B S hS 𝒳).map t₂ :=
      calc (moduleInverseImageU B S hS 𝒳).map t₁
          = ((moduleInverseImageU B S hS 𝒳).map t₁ ≫ (moduleInverseImageU B S hS 𝒳).map
              ((coheratorCounit B S hS 𝒳).app K)) ≫ inv ((moduleInverseImageU B S hS 𝒳).map
              ((coheratorCounit B S hS 𝒳).app K)) := by simp
        _ = ((moduleInverseImageU B S hS 𝒳).map t₂ ≫ (moduleInverseImageU B S hS 𝒳).map
              ((coheratorCounit B S hS 𝒳).app K)) ≫ inv ((moduleInverseImageU B S hS 𝒳).map
              ((coheratorCounit B S hS 𝒳).app K)) := by rw [e]
        _ = (moduleInverseImageU B S hS 𝒳).map t₂ := by simp
    exact hom_ext_of_isQuasicoherentOnSite_of_flat 𝒳 hZ fun y hy ↦
      congrArg (fun φ ↦ φ.val.app (op (⟨y, hy⟩ : FlatFppf B S hS 𝒳))) h'
  · change (inv ((coheratorCounit B S hS 𝒳).app Z) ≫ (lowerShriekInverseImageCoherator B S hS
      𝒳).map t) ≫
      (coheratorCounit B S hS 𝒳).app K = t
    have hn : (lowerShriekInverseImageCoherator B S hS 𝒳).map t ≫ (coheratorCounit B S hS 𝒳).app K =
        (coheratorCounit B S hS 𝒳).app Z ≫ t := (coheratorCounit B S hS 𝒳).naturality t
    rw [Category.assoc, hn]
    exact IsIso.inv_hom_id_assoc _ _

/-- **`Q(Ker φ) ⟶ ℱ` is a kernel of `φ` relative to the quasi-coherent modules**: every map from
a quasi-coherent module killed by `φ` factors uniquely through it. -/
theorem isRelKernel_coherator_kernel
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)} (φ : F ⟶ G) :
    ObjectProperty.IsRelKernel
      (fun M : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳) ↦
        M.IsQuasicoherentOnSite) φ
      ((coheratorCounit B S hS 𝒳).app (kernel φ) ≫ kernel.ι φ) := by
  refine ⟨by simp, fun Z hZ g hg ↦ ?_⟩
  obtain ⟨t, ht⟩ := (bijective_comp_coheratorCounit B S hS 𝒳 (K := kernel φ) hZ).2
    (kernel.lift φ g hg)
  have ht₁ : t ≫ (coheratorCounit B S hS 𝒳).app (kernel φ) = kernel.lift φ g hg := ht
  refine ⟨t, ?_, fun t' ht' ↦ (bijective_comp_coheratorCounit B S hS 𝒳 (K := kernel φ) hZ).1 ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ kernel.ι φ) ht₁).trans (kernel.lift_ι φ g hg))
  · have ht₂ : (t' ≫ (coheratorCounit B S hS 𝒳).app (kernel φ)) ≫ kernel.ι φ =
        kernel.lift φ g hg ≫ kernel.ι φ :=
      (Category.assoc _ _ _).trans (ht'.trans (kernel.lift_ι φ g hg).symm)
    exact ((cancel_mono (kernel.ι φ)).1 ht₂).trans ht₁.symm

/-- **`g^{-1}` carries `Q(Ker φ) ⟶ ℱ` to a kernel of `g^{-1}φ`**: `g^{-1}` preserves kernels,
being a right adjoint, and `g^{-1}` of the counit is an isomorphism. -/
def isLimitMapCoheratorKernel
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)} (φ : F ⟶ G) :
    IsLimit (KernelFork.ofι ((moduleInverseImageU B S hS 𝒳).map
      ((coheratorCounit B S hS 𝒳).app (kernel φ) ≫ kernel.ι φ))
      (((moduleInverseImageU B S hS 𝒳).map_comp _ _).symm.trans
        ((congrArg (moduleInverseImageU B S hS 𝒳).map
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (kernel.condition φ)).trans
            comp_zero))).trans ((moduleInverseImageU B S hS 𝒳).map_zero _ _)))) := by
  have : PreservesLimitsOfSize.{u, u} (moduleInverseImageU B S hS 𝒳) :=
    (moduleLowerShriekAdjunctionU B S hS 𝒳).rightAdjoint_preservesLimits
  have hk := isLimitOfPreserves (moduleInverseImageU B S hS 𝒳) (kernelIsKernel φ)
  refine IsLimit.ofIsoLimit ((KernelFork.isLimitMapConeEquiv _ _) hk) ?_
  refine Fork.ext (asIso ((moduleInverseImageU B S hS 𝒳).map
    ((coheratorCounit B S hS 𝒳).app (kernel φ)))).symm ?_
  change inv ((moduleInverseImageU B S hS 𝒳).map ((coheratorCounit B S hS 𝒳).app (kernel φ))) ≫
      (moduleInverseImageU B S hS 𝒳).map
        ((coheratorCounit B S hS 𝒳).app (kernel φ) ≫ kernel.ι φ) =
    (moduleInverseImageU B S hS 𝒳).map (kernel.ι φ)
  rw [Functor.map_comp, IsIso.inv_hom_id_assoc]

end FlatFppf

end AlgebraicGeometry.Stack

end

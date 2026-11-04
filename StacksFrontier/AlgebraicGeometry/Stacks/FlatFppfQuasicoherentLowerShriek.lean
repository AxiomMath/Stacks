module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleLowerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CartesianAffinePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectConservativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SubsiteLowerShriekQuasicoherent

/-!
# `g_!g^{-1}H = H` for a quasi-coherent module `H` (towards Stacks 07B0 (2) and 0GR9)

Let `𝒳` be an algebraic stack, `g^{-1}` the restriction of sheaves of modules to the flat-fppf
site and `g_!` its left adjoint (Stacks 0789 (2)). For a quasi-coherent `𝒪_𝒳`-module `H` and a
flat object `y` of `𝒳` lying over an affine scheme, `(g_!g^{-1}H)|_{𝒳/y}` has a global
presentation: `H|_{𝒳/y}` has one at the universe of the sections
(`AlgebraicGeometry.Stack.isPresentedByGlobalSections_over_of_isCartesianBetweenAffines`), it is
carried to the inverse image `y^{-1}H` on `(Sch/T)_{fppf}` and to its restriction to the flat
objects there, which is `(f')^{-1}g^{-1}H`, and `g_!` carries presentations along by
`AlgebraicGeometry.Stack.FlatFppf.isPresentedByGlobalSections_over_moduleLowerShriekU`.

## References

* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

namespace Stacks.SheafOfModules

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ r

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}
  {J₄ : GrothendieckTopology C₄}

/-- Direct images along equal functors with matching ring maps agree. -/
def pushforwardIsoOfEq {F F' : C₁ ⥤ C₄} [F.IsContinuous J₁ J₄] [F'.IsContinuous J₁ J₄]
    (h : F = F') {R : Sheaf J₄ RingCat.{r}} {R₁ : Sheaf J₁ RingCat.{r}}
    (ψ : R₁ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J₁ J₄).obj R)
    (ψ' : R₁ ⟶ (F'.sheafPushforwardContinuous RingCat.{r} J₁ J₄).obj R)
    (hψ : ψ ≫ eqToHom (by subst h; rfl) = ψ') :
    _root_.SheafOfModules.pushforward.{r} ψ ≅ _root_.SheafOfModules.pushforward.{r} ψ' := by
  subst h
  exact _root_.SheafOfModules.pushforwardCongr (by simpa using hψ)

/-- **Direct images along the two sides of a commutative square of functors agree.** -/
def pushforwardSquareIso (F₁ : C₁ ⥤ C₂) (G₁ : C₂ ⥤ C₄) (F₂ : C₁ ⥤ C₃) (G₂ : C₃ ⥤ C₄)
    [F₁.IsContinuous J₁ J₂] [G₁.IsContinuous J₂ J₄] [F₂.IsContinuous J₁ J₃]
    [G₂.IsContinuous J₃ J₄] (hsq : F₁ ⋙ G₁ = F₂ ⋙ G₂)
    {R₁ : Sheaf J₁ RingCat.{r}} {R₂ : Sheaf J₂ RingCat.{r}} {R₃ : Sheaf J₃ RingCat.{r}}
    {R₄ : Sheaf J₄ RingCat.{r}}
    (ψ₁ : R₁ ⟶ (F₁.sheafPushforwardContinuous RingCat.{r} J₁ J₂).obj R₂)
    (ψ₂ : R₂ ⟶ (G₁.sheafPushforwardContinuous RingCat.{r} J₂ J₄).obj R₄)
    (ψ₃ : R₁ ⟶ (F₂.sheafPushforwardContinuous RingCat.{r} J₁ J₃).obj R₃)
    (ψ₄ : R₃ ⟶ (G₂.sheafPushforwardContinuous RingCat.{r} J₃ J₄).obj R₄)
    (h' : (F₁.sheafPushforwardContinuous RingCat.{r} J₁ J₂).obj
        ((G₁.sheafPushforwardContinuous RingCat.{r} J₂ J₄).obj R₄) =
      (F₂.sheafPushforwardContinuous RingCat.{r} J₁ J₃).obj
        ((G₂.sheafPushforwardContinuous RingCat.{r} J₃ J₄).obj R₄))
    (hψ : (ψ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{r} J₁ J₂).map ψ₂) ≫ eqToHom h' =
      ψ₃ ≫ (F₂.sheafPushforwardContinuous RingCat.{r} J₁ J₃).map ψ₄)
    (M : _root_.SheafOfModules.{r} R₄) :
    (_root_.SheafOfModules.pushforward.{r} ψ₁).obj
        ((_root_.SheafOfModules.pushforward.{r} ψ₂).obj M) ≅
      (_root_.SheafOfModules.pushforward.{r} ψ₃).obj
        ((_root_.SheafOfModules.pushforward.{r} ψ₄).obj M) :=
  haveI := Functor.isContinuous_comp F₁ G₁ J₁ J₂ J₄
  haveI := Functor.isContinuous_comp F₂ G₂ J₁ J₃ J₄
  (_root_.SheafOfModules.pushforwardComp ψ₁ ψ₂).app M ≪≫
    (pushforwardIsoOfEq hsq _ _ hψ).app M ≪≫
      ((_root_.SheafOfModules.pushforwardComp ψ₃ ψ₄).app M).symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

universe u w

namespace FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

attribute [local instance] instIsContinuousHomFunctorFppf instIsContinuousPrimedSiteFunctor

/-- **Restrictions commute**: `(f')^{-1}g^{-1} = g^{-1}f^{-1}` on sheaves of modules, the square
of site functors `f' ⋙ ι = ι ⋙ f` commuting on the nose. -/
def restrictedModuleRestrictionAlongInverseImageIso
    (M : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒴)) :
    (restrictedModuleRestrictionAlong B S hS f hf).obj ((moduleInverseImageU B S hS 𝒴).obj M) ≅
      (moduleInverseImageU B S hS 𝒳).obj ((moduleRestrictionAlong B S hS f).obj M) :=
  pushforwardSquareIso (primedSiteFunctor B S hS f hf) (objectProperty B S hS 𝒴).ι
    (objectProperty B S hS 𝒳).ι f.hom.hom.toFunctor
    (SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)) _ _ _ _
    ((inverseImageRing_primedSiteFunctor B S hS f hf).trans
      (congrArg ((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous RingCat.{u}
        (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)).obj
        (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl f)).symm)
    (by simp [eqToHom_map]) M

end Square

attribute [local instance] instHasPointwiseRightKanExtensionSmall

section Presentation

variable (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The restriction `g^{-1}` to the flat-fppf site preserves colimits: it is left adjoint to the
direct image. -/
instance preservesColimitsOfSize_moduleInverseImageU :
    PreservesColimitsOfSize.{u, u} (moduleInverseImageU B S hS 𝒵) :=
  (inverseImagePushforwardCocontinuousTautologicalAdjunction (objectProperty B S hS 𝒵).ι
    (ambientRingStructureSheaf B S hS 𝒵)).leftAdjoint_preservesColimits

/-- The restriction `g^{-1}` to the flat-fppf site preserves zero morphisms. -/
instance preservesZeroMorphisms_moduleInverseImageU :
    (moduleInverseImageU B S hS 𝒵).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩

/-- **`g^{-1}` carries a global presentation to one**: it preserves colimits and the structure
sheaf. -/
theorem isPresentedByGlobalSections_moduleInverseImageU
    {M : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒵)}
    (hM : M.IsPresentedByGlobalSections) :
    ((moduleInverseImageU B S hS 𝒵).obj M).IsPresentedByGlobalSections :=
  Stacks.Sheaves.LocalizedPullback.isPresentedByGlobalSections_map (moduleInverseImageU B S hS 𝒵)
    (Iso.refl _) (Iso.refl _) hM

/-- **`g^{-1}` carries a finite global presentation to one.** -/
theorem isFinitelyPresentedByGlobalSections_moduleInverseImageU
    {M : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒵)}
    (hM : M.IsFinitelyPresentedByGlobalSections) :
    ((moduleInverseImageU B S hS 𝒵).obj M).IsFinitelyPresentedByGlobalSections := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩ := hM
  have : PreservesColimitsOfSize.{0, 0} (moduleInverseImageU B S hS 𝒵) :=
    preservesColimitsOfSize_shrink _
  let G := moduleInverseImageU B S hS 𝒵
  exact ⟨n, k, G.obj P, G.obj Q, _, _,
    ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap G (Iso.refl _) ι hP⟩,
    ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap G (Iso.refl _) κ hQ⟩,
    G.map a, G.map b, by rw [← G.map_comp, hab, G.map_zero],
    ⟨isColimitCoforkMapOfIsColimit' G hab hc⟩⟩

end Presentation

section Quasicoherent

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **`(g_!g^{-1}H)|_{𝒳/y}` has a global presentation** for a quasi-coherent `H` and a flat object
`y` of `𝒳` lying over an affine scheme. -/
theorem isPresentedByGlobalSections_over_moduleLowerShriekU_inverseImage
    (H : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hH : H.IsQuasicoherentOnSite) (y : FlatFppf B S hS 𝒳)
    (hy : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj)) :
    (((moduleLowerShriekU B S hS 𝒳).obj ((moduleInverseImageU B S hS 𝒳).obj H)).over
      y.obj).IsPresentedByGlobalSections := by
  have h1 := isPresentedByGlobalSections_over_of_isCartesianBetweenAffines B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids H
    (isCartesianBetweenAffines_of_isQuasicoherentOnSite _ H hH) hy
  have h2 := (isPresentedByGlobalSections_over_iff B S hS y H).1 h1
  have h3 := isPresentedByGlobalSections_moduleInverseImageU B S hS _ h2
  have h4 := Stacks.SheafOfModules.isPresentedByGlobalSections_of_iso
    (restrictedModuleRestrictionAlongInverseImageIso B S hS (ambientSliceMorphism B S hS y)
      (isFlat_ambientSliceMorphism B S hS y) H).symm h3
  exact isPresentedByGlobalSections_over_moduleLowerShriekU B S hS y _ h4


/-- **`g_!g^{-1}H` is quasi-coherent for a quasi-coherent `H`**: over every object lying over an
affine scheme and mapping to a flat object lying over an affine scheme it has a global
presentation, and those objects cover (`AlgebraicGeometry.Stack.goodPresieve_generate_mem`). -/
theorem isQuasicoherentOnSite_moduleLowerShriekU_inverseImage
    (H : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hH : H.IsQuasicoherentOnSite) :
    ((moduleLowerShriekU B S hS 𝒳).obj
      ((moduleInverseImageU B S hS 𝒳).obj H)).IsQuasicoherentOnSite := by
  refine ⟨fun U ↦ ⟨Σ w : 𝒳.val.val.obj, {g : w ⟶ U // goodPresieve 𝒳 U g}, fun i ↦ i.1,
    fun i ↦ i.2.1, ?_, fun i ↦ ?_⟩⟩
  · refine GrothendieckTopology.superset_covering _ ?_ (goodPresieve_generate_mem 𝒳 U)
    rintro Z h ⟨Y', h', g, hg, rfl⟩
    exact ⟨Y', h', g, Presieve.ofArrows.mk (⟨Y', g, hg⟩ :
      Σ w : 𝒳.val.val.obj, {g : w ⟶ U // goodPresieve 𝒳 U g}), rfl⟩
  · obtain ⟨w, g, -, y, hy, hyaff, ⟨φ⟩⟩ := i
    exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap _ φ
      (Stacks.SheafOfModules.hasGlobalPresentation_of_isPresentedByGlobalSections
        (isPresentedByGlobalSections_over_moduleLowerShriekU_inverseImage B S hS H hH ⟨y, hy⟩
          hyaff))

/-- **`g_!g^{-1}H = H` for a quasi-coherent `H`**: the counit of `g_! ⊣ g^{-1}` is an isomorphism
at every quasi-coherent module. Both sides are quasi-coherent and the counit is bijective on
flat objects, by the triangle identity and `g^{-1}g_! = id`; restriction to the flat objects
reflects isomorphisms between quasi-coherent modules. -/
theorem isIso_moduleLowerShriekAdjunctionU_counit_app
    (H : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hH : H.IsQuasicoherentOnSite) :
    IsIso ((moduleLowerShriekAdjunctionU B S hS 𝒳).counit.app H) := by
  refine isIso_of_isQuasicoherentOnSite_of_bijective_flat 𝒳 _
    (isQuasicoherentOnSite_moduleLowerShriekU_inverseImage B S hS H hH) hH fun y hy ↦ ?_
  have hu := isIso_moduleLowerShriekAdjunctionU_unit B S hS 𝒳
  have hiso : IsIso ((moduleInverseImageU B S hS 𝒳).map
      ((moduleLowerShriekAdjunctionU B S hS 𝒳).counit.app H)) := by
    exact IsIso.of_isIso_fac_left
      ((moduleLowerShriekAdjunctionU B S hS 𝒳).right_triangle_components H)
  have := hiso
  exact ConcreteCategory.bijective_of_isIso
    ((_root_.SheafOfModules.evaluation _ (op (⟨y, hy⟩ : FlatFppf B S hS 𝒳))).map
      ((moduleInverseImageU B S hS 𝒳).map
        ((moduleLowerShriekAdjunctionU B S hS 𝒳).counit.app H)))

end Quasicoherent

end FlatFppf

end AlgebraicGeometry.Stack

end

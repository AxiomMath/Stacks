module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectSliceEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PresentationOfSections

/-!
# `g_!` carries global presentations to global presentations, locally at flat objects

Let `𝒳` be an algebraic stack and `g_!` the left adjoint of the restriction `g^{-1}` of sheaves
of modules to the flat-fppf site (Stacks 0789 (2)). This file proves the two steps of the
source's proof of Stacks 07B0 (2) which involve `g_!`:

* on the stack of a scheme `T` the object `id_T` is flat and terminal, so the restriction of
  maps out of the structure sheaf is bijective and the counit `g_!O = g_!g^{-1}O ⟶ O` is an
  isomorphism (Stacks 078A for the stack of a scheme); hence `g_!` carries a (finite) global
  presentation to one (`g_!` is fully faithful and preserves colimits);
* for a flat object `y` of `𝒳` over `T`, Stacks 07AT (2) on modules
  (`AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekUCompRestrictionAlongIso`) and the
  equivalence of sites `(Sch/T)_{fppf} ≌ 𝒳_{fppf}/y` (Stacks 06WI) show that `(g_!N)|_{𝒳/y}` has
  a (finite) global presentation as soon as the restriction `(f')^{-1}N` of `N` to the flat-fppf
  site of `T` has one.

## References

* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 078A](https://stacks.math.columbia.edu/tag/078A)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite


namespace AlgebraicGeometry.Stack

universe u w

namespace FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Terminal

variable (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) (t : (objectProperty B S hS 𝒵).FullSubcategory)
  (ht : IsTerminal t.obj)

include ht in
/-- **Stacks 078A when the flat site contains a terminal object of the big site**: the counit
`g_!g^{-1}O ⟶ O` of `g_! ⊣ g^{-1}` at the structure sheaf is an isomorphism. -/
theorem isIso_moduleLowerShriekAdjunctionU_counit_unit :
    IsIso ((moduleLowerShriekAdjunctionU B S hS 𝒵).counit.app
      (_root_.SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒵))) := by
  refine isIso_of_coyoneda_map_bijective _ fun M ↦ ?_
  have hb := Stacks.SheafOfModules.bijective_pushforward_map_unit (J' := topology B S hS 𝒵)
    (objectProperty B S hS 𝒵).ι
    (ambientRingStructureSheaf B S hS 𝒵) t ht M
  have : (fun x : _root_.SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒵) ⟶ M ↦
      (moduleLowerShriekAdjunctionU B S hS 𝒵).counit.app
        (_root_.SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒵)) ≫ x) =
      ((moduleLowerShriekAdjunctionU B S hS 𝒵).homEquiv _ _).symm ∘
        (fun x : _root_.SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒵) ⟶ M ↦
          (moduleInverseImageU B S hS 𝒵).map x) := by
    funext x
    simp only [Function.comp_apply, Adjunction.homEquiv_counit]
    exact ((moduleLowerShriekAdjunctionU B S hS 𝒵).counit.naturality x).symm
  exact (congrArg Function.Bijective this).mpr
    (((moduleLowerShriekAdjunctionU B S hS 𝒵).homEquiv _ _).symm.bijective.comp hb)

/-- **`g_!O = O`** on the flat-fppf site of an algebraic stack whose flat site contains a
terminal object of the big site. -/
def moduleLowerShriekUUnitIso (t : (objectProperty B S hS 𝒵).FullSubcategory)
    (ht : IsTerminal t.obj) :
    (moduleLowerShriekU B S hS 𝒵).obj
        (_root_.SheafOfModules.unit (subsiteRingStructureSheaf B S hS 𝒵)) ≅
      _root_.SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒵) :=
  (moduleLowerShriekU B S hS 𝒵).mapIso
      (Iso.refl _ : _root_.SheafOfModules.unit (subsiteRingStructureSheaf B S hS 𝒵) ≅
        (moduleInverseImageU B S hS 𝒵).obj
          (_root_.SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒵))) ≪≫
    @asIso _ _ _ _ ((moduleLowerShriekAdjunctionU B S hS 𝒵).counit.app
      (_root_.SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒵)))
      (isIso_moduleLowerShriekAdjunctionU_counit_unit B S hS 𝒵 t ht)

/-- The unit of `g_! ⊣ g^{-1}` is an isomorphism. -/
local instance : IsIso (moduleLowerShriekAdjunctionU B S hS 𝒵).unit :=
  isIso_moduleLowerShriekAdjunctionU_unit B S hS 𝒵

/-- `g_!` is full, its adjunction having an invertible unit. -/
local instance : (moduleLowerShriekU B S hS 𝒵).Full :=
  (Adjunction.fullyFaithfulLOfIsIsoUnit (moduleLowerShriekAdjunctionU B S hS 𝒵)).full

/-- `g_!` is faithful, its adjunction having an invertible unit. -/
local instance : (moduleLowerShriekU B S hS 𝒵).Faithful :=
  (Adjunction.fullyFaithfulLOfIsIsoUnit (moduleLowerShriekAdjunctionU B S hS 𝒵)).faithful

/-- `g_!` preserves colimits, being a left adjoint. -/
local instance : PreservesColimitsOfSize.{u, u} (moduleLowerShriekU B S hS 𝒵) :=
  (moduleLowerShriekAdjunctionU B S hS 𝒵).leftAdjoint_preservesColimits.{u, u}

include ht in
/-- **`g_!` carries a global presentation to one** on an algebraic stack whose flat site contains
a terminal object of the big site. -/
theorem isPresentedByGlobalSections_moduleLowerShriekU
    {N : _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒵)}
    (hN : N.IsPresentedByGlobalSections) :
    ((moduleLowerShriekU B S hS 𝒵).obj N).IsPresentedByGlobalSections :=
  (Stacks.Sheaves.GlobalTypeComparison.isPresentedByGlobalSections_iff _
    (moduleLowerShriekUUnitIso B S hS 𝒵 t ht) N).1 hN

include ht in
/-- **`g_!` carries a finite global presentation to one** on an algebraic stack whose flat site
contains a terminal object of the big site. -/
theorem isFinitelyPresentedByGlobalSections_moduleLowerShriekU
    {N : _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒵)}
    (hN : N.IsFinitelyPresentedByGlobalSections) :
    ((moduleLowerShriekU B S hS 𝒵).obj N).IsFinitelyPresentedByGlobalSections :=
  (Stacks.Sheaves.GlobalTypeComparison.isFinitelyPresentedByGlobalSections_iff _
    (moduleLowerShriekUUnitIso B S hS 𝒵 t ht) N).1 hN

end Terminal

section Slice

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (y : FlatFppf B S hS 𝒳)

/-- The terminal flat object `id_T` of the stack of the scheme `T` below `y`. -/
abbrev sliceTerminal : (objectProperty B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).FullSubcategory :=
  ⟨Over.mk (𝟙 _), flatObject_schemeStack_id.{u, w} B S hS _⟩

/-- **`(g_!N)|_{𝒳/y}` has a global presentation when `(f')^{-1}N` has one**, for a flat object
`y` of `𝒳` lying over `T` and `f : (Sch/T) ⟶ 𝒳` the 1-morphism it names: by Stacks 07AT (2),
`f^{-1}g_!N = g'_!(f')^{-1}N`, `g'_!` preserves presentations on the stack of a scheme, and
`(g_!N)|_{𝒳/y}` is `f^{-1}g_!N` read through `(Sch/T) ≌ 𝒳/y`. -/
theorem isPresentedByGlobalSections_over_moduleLowerShriekU
    (N : _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳))
    (hN : ((restrictedModuleRestrictionAlong B S hS (ambientSliceMorphism B S hS y)
      (isFlat_ambientSliceMorphism B S hS y)).obj N).IsPresentedByGlobalSections) :
    (((moduleLowerShriekU B S hS 𝒳).obj N).over y.obj).IsPresentedByGlobalSections :=
  (isPresentedByGlobalSections_over_iff B S hS y _).2
    (Stacks.SheafOfModules.isPresentedByGlobalSections_of_iso
      ((moduleLowerShriekUCompRestrictionAlongIso B S hS (ambientSliceMorphism B S hS y)
        (isFlat_ambientSliceMorphism B S hS y)).app N).symm
      (isPresentedByGlobalSections_moduleLowerShriekU B S hS _ (sliceTerminal B S hS y)
        Over.mkIdTerminal hN))

/-- **`(g_!N)|_{𝒳/y}` has a finite global presentation when `(f')^{-1}N` has one**, for a flat
object `y` of `𝒳`. -/
theorem isFinitelyPresentedByGlobalSections_over_moduleLowerShriekU
    (N : _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳))
    (hN : ((restrictedModuleRestrictionAlong B S hS (ambientSliceMorphism B S hS y)
      (isFlat_ambientSliceMorphism B S hS y)).obj N).IsFinitelyPresentedByGlobalSections) :
    (((moduleLowerShriekU B S hS 𝒳).obj N).over y.obj).IsFinitelyPresentedByGlobalSections :=
  (isFinitelyPresentedByGlobalSections_over_iff B S hS y _).2
    (Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_iso
      ((moduleLowerShriekUCompRestrictionAlongIso B S hS (ambientSliceMorphism B S hS y)
        (isFlat_ambientSliceMorphism B S hS y)).app N).symm
      (isFinitelyPresentedByGlobalSections_moduleLowerShriekU B S hS _ (sliceTerminal B S hS y)
        Over.mkIdTerminal hN))

end Slice

end FlatFppf

end AlgebraicGeometry.Stack

end

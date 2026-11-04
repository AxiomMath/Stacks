module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemePullback

/-!
# The points of the zero scheme of a section, and vanishing read on schemes

Let `X` be an algebraic space over `S`, `L` an invertible `𝒪_X`-module and `s` a global section of
`L`. By Stacks 0846 (2) a point `x ∈ X(b)` of an object `b` of the site lies in the zero scheme
`Z(s)` exactly when the inverse image of `s` along `x : b ⟶ X` vanishes. This file records that in
the form of morphisms of modules: `x ∈ Z(s)(b)` exactly when the inverse image along `x` of the
morphism `𝒪_X ⟶ L` given by `s` vanishes
(`AlgebraicGeometry.Space.mem_zeroScheme_iff_modulePullback_map_eq_zero`).

It also records how such a vanishing is read on schemes: along a morphism `g : T' ⟶ T` of the
site, the inverse image of a morphism `φ` of quasi-coherent modules on the represented space of `T`
vanishes exactly when the inverse image along the morphism of schemes `g` of the reading of `φ`
on the scheme `T` vanishes
(`AlgebraicGeometry.Space.modulePullback_representedSpaceMap_map_eq_zero_iff`).

## Main results

* `AlgebraicGeometry.Space.modulePullbackSections_eq_zero_iff`.
* `AlgebraicGeometry.Space.modulePullback_comp_map_eq_zero_iff`.
* `AlgebraicGeometry.Space.modulePullback_representedSpaceMap_map_eq_zero_iff`.
* `AlgebraicGeometry.Space.mem_zeroScheme_iff_modulePullback_map_eq_zero`.

## Implementation notes

The zero morphisms of modules on the small étale site are taken from the abelian structure
`AlgebraicGeometry.Space.smallEtaleModulesAbelian`, as in
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback`.

## References

* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] smallEtaleModulesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The global section of the zero morphism out of the structure sheaf is zero. -/
theorem unitHomEquiv_zero {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2) :
    M.unitHomEquiv 0 = 0 := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  rfl

/-- **The inverse image of a global section vanishes exactly when the inverse image of the
morphism from the structure sheaf it defines does.** -/
theorem modulePullbackSections_eq_zero_iff {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections) :
    modulePullbackSections B S hS f L s = 0 ↔
      (modulePullback B S hS f).map (L.unitHomEquiv.symm s) = 0 := by
  rw [modulePullbackSections, ← unitHomEquiv_zero B S hS ((modulePullback B S hS f).obj L),
    Equiv.apply_eq_iff_eq]
  exact ⟨fun h => (Iso.cancel_iso_inv_left _ _ _).1 (h.trans comp_zero.symm), fun h => by
    rw [h, comp_zero]⟩

/-- The inverse image of a morphism of modules along a composite vanishes exactly when the
iterated inverse image does. -/
theorem modulePullback_comp_map_eq_zero_iff {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    (modulePullback B S hS (f ≫ g)).map φ = 0 ↔
      (modulePullback B S hS f).map ((modulePullback B S hS g).map φ) = 0 := by
  have n := (modulePullbackCompIso B S hS f g).hom.naturality φ
  simp only [Functor.comp_map] at n
  refine ⟨fun h => (Iso.cancel_iso_hom_right _ _ ((modulePullbackCompIso B S hS f g).app N)).1 ?_,
    fun h => (Iso.cancel_iso_hom_left ((modulePullbackCompIso B S hS f g).app M) _ _).1 ?_⟩
  · rw [Iso.app_hom, n, h, comp_zero, zero_comp]
  · rw [Iso.app_hom, ← n, h, zero_comp, comp_zero]

/-- The reading on the scheme of `T` of a morphism of modules on the represented space of `T` is
injective on morphisms out of a quasi-coherent module and carries zero to zero, so it detects
vanishing. -/
theorem representedZariski_map_eq_zero_iff {T : BigFppfOver B S hS}
    {M N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hM : M.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map φ) = 0 ↔ φ = 0 := by
  have : (representedSmallEtaleModuleEquivalence B S hS T).inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hz : (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map (0 : M ⟶ N)) = 0 :=
    (congrArg _ (Functor.map_zero _ _ _)).trans (Functor.map_zero _ _ _)
  exact ⟨fun h => (QuasiCoherentDescent.bijective_representedZariski_map B S hS M N hM).1
    (h.trans hz.symm), by rintro rfl; exact hz⟩

/-- **Vanishing of an inverse image along a morphism of the site, read on schemes.** For
`g : T' ⟶ T` in the site and a morphism `φ` of quasi-coherent modules on the represented space of
`T`, the inverse image of `φ` along `g` vanishes exactly when the inverse image along the
morphism of schemes `g` of the reading of `φ` on the scheme `T` does. -/
theorem modulePullback_representedSpaceMap_map_eq_zero_iff {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T)
    {M N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map φ = 0 ↔
      (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map
        ((SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map φ)) = 0 := by
  have nat := representedZariskiModulePullbackIso_naturality B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) hM hN φ
  have hR := representedZariski_map_eq_zero_iff B S hS
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS g) M hM)
    ((modulePullback B S hS (representedSpaceMap B S hS g)).map φ)
  refine ⟨fun h => (Iso.cancel_iso_hom_right _ _ (representedZariskiModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) N hN)).1 ?_,
    fun h => hR.1 ((Iso.cancel_iso_hom_left (representedZariskiModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) M hM) _ _).1 ?_)⟩
  · rw [nat, hR.2 h, comp_zero, zero_comp]
  · rw [← nat, h, zero_comp, comp_zero]

/-- The range of the morphism from a representable presheaf given by a section lies in a
subfunctor exactly when the section does. -/
theorem range_yonedaEquiv_symm_le_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor F)
    {b : BigFppfOver B S hS} (x : F.obj (op b)) :
    Subfunctor.range (yonedaEquiv.symm x) ≤ Z ↔ x ∈ Z.obj (op b) := by
  refine ⟨fun h => h (op b) ⟨𝟙 b, yonedaEquiv.apply_symm_apply x⟩, ?_⟩
  rintro hx U _ ⟨g, rfl⟩
  exact Z.map g.op hx

/-- **The points of the zero scheme of a section**: a point `x ∈ X(b)` lies in `Z(s)` exactly when
the inverse image along `x` of the morphism `𝒪_X ⟶ L` given by `s` vanishes (Stacks 0846 (2)). -/
theorem mem_zeroScheme_iff_modulePullback_map_eq_zero (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (s : L.sections) {b : BigFppfOver B S hS} (x : X.1.obj (op b)) :
    x ∈ (zeroScheme B S hS X L s).1.obj (op b) ↔
      (modulePullback B S hS (ObjectProperty.homMk (yonedaEquiv.symm x) :
        representedAlgebraicSpace B S hS b ⟶ X)).map (L.unitHomEquiv.symm s) = 0 := by
  rw [← modulePullbackSections_eq_zero_iff,
    modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme B S hS X
      (representedAlgebraicSpace B S hS b) L hinv s,
    exists_comp_eq_iff_range_le B S hS (zeroScheme B S hS X L s)]
  exact (range_yonedaEquiv_symm_le_iff B S hS _ x).symm

end AlgebraicGeometry.Space

end

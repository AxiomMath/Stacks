module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ConeNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.BaseChangeData
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso

/-!
# The closed immersion `C_ZX ⟶ N` under base change

Let `i : Z ⟶ X` be a closed immersion, `h : X' ⟶ X` a morphism, `i' : Z' = Z ×_X X' ⟶ X'` the base
change with `g : Z' ⟶ Z`, and `𝒩` a virtual normal bundle for `i`, with base change
`𝒩' = g^*𝒩` (Stacks 0FBJ). The vector bundles `N = 𝐕(𝒩^∨)` and `N' = 𝐕(𝒩'^∨)` are related by
the morphism

  `Ψ : N' = 𝐕((g^*𝒩)^∨) ≅ 𝐕(g^*(𝒩^∨)) = N ×_Z Z' ⟶ N`.

This file proves that the closed immersions `C_ZX ⟶ N` of the construction preceding Stacks 0FBK
are compatible with `Ψ` and the morphisms of normal cones and of special fibres of the
deformation spaces. This is the commutative diagram in the proof of the base change clause of
Stacks 0FBK, read on the opens `C_{Z'}X' ⊆ W'_∞` and `C_ZX ⊆ W_∞`.

## Main results

* `Stacks.Chow.VirtualNormalBundle.Comparison` — a comparison of virtual normal bundles over a
  cartesian square, of which the virtual normal sheaf `g^*𝒩` of Stacks 0FBJ is the basic example.
* `Stacks.Chow.VirtualNormalBundle.Comparison.comm_degreeOne` — the surjection of `𝒩'` is the
  pullback of that of `𝒩` followed by the canonical map of Stacks 0634.
* `Stacks.Chow.VirtualNormalBundle.normalConeMapOfSquare_comp_coneEmbedding` — the square of
  normal cones and vector bundles commutes.
* `Stacks.Chow.VirtualNormalBundle.Comparison.specialFibreEmbedding_comp_bundleMap` — the square
  of special fibres and vector bundles commutes.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.Conormal (coborderIdeal)

universe u

namespace Stacks.Chow.VirtualNormalBundle

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X'}
  [IsClosedImmersion i'] {g : Z' ⟶ Z} {h : X' ⟶ X} (sq : IsPullback i' g h i)
  (𝒩 : VirtualNormalBundle i)

/-- The virtual normal bundle `𝒩' = g^*𝒩` of the base change `Z' = Z ×_X X' ⟶ X'`, Stacks 0FBJ. -/
abbrev baseChangeAlong : VirtualNormalBundle i' :=
  𝒩.baseChange i i' g h sq

/-- The pullback along `g` of the dual of the bundle of `𝒩` is quasi-coherent. -/
instance isQuasicoherent_pullback_dualSheaf :
    ((Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _

/-- **A comparison of virtual normal bundles over a cartesian square**: an isomorphism
`g^*(𝒩^∨) ≅ 𝒩'^∨` under which the surjection of `𝒩'` is the pullback of the surjection of `𝒩`
followed by the canonical map `g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of Stacks 01R4. The virtual normal sheaf
`g^*𝒩` of Stacks 0FBJ carries one (`Stacks.Chow.VirtualNormalBundle.Comparison.ofBaseChange`). -/
structure Comparison (𝒩' : VirtualNormalBundle i') where
  /-- The isomorphism `g^*(𝒩^∨) ≅ 𝒩'^∨`. -/
  map : (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle) ⟶ dualSheaf 𝒩'.bundle
  isIso : IsIso map
  /-- The compatibility with the surjections onto the conormal sheaves. -/
  comm : map ≫ 𝒩'.surjection =
    (Scheme.Modules.pullback g).map 𝒩.surjection ≫
      Stacks.Immersion.immersionConormalSheafMap i' i g h (Stacks.Immersion.toShHom_square sq.w)

attribute [instance] Comparison.isIso

/-- The virtual normal sheaf `g^*𝒩` of Stacks 0FBJ compares to `𝒩` through the dual base-change
isomorphism. -/
def Comparison.ofBaseChange : Comparison sq 𝒩 (𝒩.baseChangeAlong sq) where
  map := pullbackDualMap g 𝒩.bundle
  isIso := pullbackDualMap_isIso g 𝒩.bundle 𝒩.isFiniteLocallyFree
  comm := Iso.hom_inv_id_assoc (@asIso _ _ _ _ (pullbackDualMap g 𝒩.bundle)
    (pullbackDualMap_isIso g 𝒩.bundle 𝒩.isFiniteLocallyFree)) _

variable {sq 𝒩} {𝒩' : VirtualNormalBundle i'} (Φ : Comparison sq 𝒩 𝒩')

/-- The compatibility of a comparison with the surjections, in degree one of the conormal
algebras: it is the canonical map `g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of Stacks 0634. -/
theorem Comparison.comm_degreeOne : Φ.map ≫ 𝒩'.surjectionDegreeOne =
    (Scheme.Modules.pullback g).map 𝒩.surjectionDegreeOne ≫
      Stacks.Conormal.canonicalPullbackHomOne i' i g h sq.w.symm := by
  have hD := Stacks.Immersion.immersionConormalSheafMap_eq_degreeOne i' i g h sq.w
  have := Stacks.Conormal.conormalDegreeOneHom_isIso i'
  change Φ.map ≫ 𝒩'.surjection ≫ Stacks.Conormal.conormalDegreeOneHom i' =
    (modulePullback g.toLRSHom.toShHom).map
        (𝒩.surjection ≫ Stacks.Conormal.conormalDegreeOneHom i) ≫
      (AlgebraicGeometry.canonicalPullbackHom i' i g h sq.w.symm).hom 1
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ Stacks.Conormal.conormalDegreeOneHom i') Φ.comm).trans ?_
  rw [hD]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((modulePullback g.toLRSHom.toShHom).map 𝒩.surjection ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
      ((congrArg _ (IsIso.inv_hom_id _)).trans (Category.comp_id _)))))).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    ((modulePullback g.toLRSHom.toShHom).map_comp _ _).symm)

/-- **The morphism `Ψ : N' ⟶ N` of vector bundles of a comparison**:
`N' = 𝐕(𝒩'^∨) ≅ 𝐕(g^*(𝒩^∨)) = N ×_Z Z' ⟶ N`, the first arrow induced by the comparison
isomorphism and the second the projection. -/
def Comparison.bundleMap :
    Scheme.Modules.vectorBundle Z' (dualSheaf 𝒩'.bundle) ⟶
      Scheme.Modules.vectorBundle Z (dualSheaf 𝒩.bundle) :=
  (Scheme.Modules.vectorBundleMap Z'
      (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
      (G := dualSheaf 𝒩'.bundle) Φ.map).left ≫
    Scheme.Modules.vectorBundleBaseChangeMap g (dualSheaf 𝒩.bundle)

/-- **The closed immersions `C_ZX ⟶ N` are compatible with base change**: the morphism of normal
cones `C_{Z'}X' ⟶ C_ZX` followed by `C_ZX ⟶ N` is `C_{Z'}X' ⟶ N'` followed by `Ψ : N' ⟶ N`. -/
theorem normalConeMapOfSquare_comp_coneEmbedding :
    Stacks.Conormal.normalConeMapOfSquare i' i g h sq.w.symm ≫ 𝒩.coneEmbedding =
      𝒩'.coneEmbedding ≫ Φ.bundleMap := by
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g
    (Stacks.Conormal.conormalSheafDegreeOne i)
  have hg2 := Stacks.Conormal.normalConeMapOfSquare_comp_normalConeToNormalBundle
    i' i g h sq.w.symm
  have hnat := Scheme.Modules.vectorBundleMap_pullback_comp_vectorBundleBaseChangeMap
    g (dualSheaf 𝒩.bundle) 𝒩.surjectionDegreeOne
  have hc1 := Scheme.Modules.vectorBundleMap_comp Z'
    ((Scheme.Modules.pullback g).map 𝒩.surjectionDegreeOne)
    (Stacks.Conormal.canonicalPullbackHomOne i' i g h sq.w.symm)
  have hc2 := Scheme.Modules.vectorBundleMap_comp Z'
    (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
    (G := dualSheaf 𝒩'.bundle) Φ.map 𝒩'.surjectionDegreeOne
  have hc2' := (congrArg (Scheme.Modules.vectorBundleMap Z'
    (F := (Scheme.Modules.pullback g).obj (dualSheaf 𝒩.bundle))
    (G := Stacks.Conormal.conormalSheafDegreeOne i')) Φ.comm_degreeOne).symm.trans hc2
  have hc := congrArg (fun φ => φ.left) (hc1.symm.trans hc2')
  simp only [Over.comp_left] at hc
  rw [coneEmbedding, coneEmbedding, bundleEmbedding, bundleEmbedding, Comparison.bundleMap,
    ← Category.assoc, hg2, Category.assoc, Category.assoc, ← hnat]
  exact (congrArg (Stacks.Conormal.normalConeToNormalBundle i' ≫ ·)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc).trans
      (Category.assoc _ _ _)))).trans (Category.assoc _ _ _).symm

omit Φ in
include sq in
/-- **The special fibres of the deformation spaces under base change**: a morphism
`χ : Z(t'⁻¹) ⟶ Z(t⁻¹)` of special fibres lying over `D(Z' ⊆ X') ⟶ D(Z ⊆ X)` is the morphism of
normal cones `C_{Z'}X' ⟶ C_ZX`. -/
theorem specialFibreIsoNormalCone_hom_comp_normalConeMapOfSquare
    (χ : (Stacks.Deformation.specialFibre i').subscheme ⟶
      (Stacks.Deformation.specialFibre i).subscheme)
    (hχ : χ ≫ (Stacks.Deformation.specialFibre i).subschemeι =
      (Stacks.Deformation.specialFibre i').subschemeι ≫
        Stacks.Deformation.deformationMapOver sq) :
    (Stacks.Deformation.specialFibreIsoNormalCone i').hom ≫
        Stacks.Conormal.normalConeMapOfSquare i' i g h
          sq.w.symm =
      χ ≫ (Stacks.Deformation.specialFibreIsoNormalCone i).hom := by
  have hg1 := Stacks.Deformation.normalConeToDeformation_comp_deformationMap
    i' i g h sq.w.symm
    (Stacks.Deformation.coborderMapOver i i' h) (Stacks.Deformation.coborderMapOver_ι i i' h)
    (Stacks.Deformation.coborderIdeal_baseChange sq).le
  refine (cancel_mono (Stacks.Deformation.normalConeToDeformation i)).1 ?_
  rw [Category.assoc, ← hg1, ← Category.assoc,
    Stacks.Deformation.specialFibreIsoNormalCone_hom_comp, Category.assoc,
    Stacks.Deformation.specialFibreIsoNormalCone_hom_comp]
  exact hχ.symm

/-- **The square of the proof of the base change clause of Stacks 0FBK commutes**: for a morphism
`χ : Z(t'⁻¹) ⟶ Z(t⁻¹)` of special fibres over `D(Z' ⊆ X') ⟶ D(Z ⊆ X)`, the closed immersion
`Z(t'⁻¹) ≅ C_{Z'}X' ⟶ N'` followed by `Ψ : N' ⟶ N` is `χ` followed by `Z(t⁻¹) ≅ C_ZX ⟶ N`. -/
theorem Comparison.specialFibreEmbedding_comp_bundleMap
    (χ : (Stacks.Deformation.specialFibre i').subscheme ⟶
      (Stacks.Deformation.specialFibre i).subscheme)
    (hχ : χ ≫ (Stacks.Deformation.specialFibre i).subschemeι =
      (Stacks.Deformation.specialFibre i').subschemeι ≫
        Stacks.Deformation.deformationMapOver sq) :
    𝒩'.specialFibreEmbedding ≫ Φ.bundleMap = χ ≫ 𝒩.specialFibreEmbedding := by
  rw [specialFibreEmbedding, specialFibreEmbedding, Category.assoc,
    ← normalConeMapOfSquare_comp_coneEmbedding, ← Category.assoc,
    specialFibreIsoNormalCone_hom_comp_normalConeMapOfSquare χ hχ, Category.assoc]

end Stacks.Chow.VirtualNormalBundle

end

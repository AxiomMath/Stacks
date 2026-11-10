module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.BottomDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import
  StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.ProperSmoothStructureSheafDirectImage
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.LocalUnitSections

/-!
# The bottom de Rham differential of a proper smooth morphism

Let `f : X ⟶ S` be a proper smooth morphism of schemes. The degree-zero differential of the
relative de Rham complex vanishes on the sections over `f⁻¹V` for every open `V` of `S`; that is,

`f_*d : f_*𝒪_X ⟶ f_*Ω¹_{X/S}`

is zero. Over an affine open `V` small enough the `Γ(S, V)`-algebra `Γ(X, f⁻¹V)` is étale, hence
unramified, so it carries no nonzero `Γ(S, V)`-derivation; the degree-zero de Rham differential on
sections over `f⁻¹V` is the universal relative derivation, so it vanishes there, and the general
case follows because `Ω¹_{X/S}` is a sheaf.

## Main results

* `AlgebraicGeometry.deRhamComplex_d_zero_app_preimage_eq_zero_of_formallyUnramified`: if
  `Γ(S, W) ⟶ Γ(X, f⁻¹W)` is formally unramified, the degree-zero de Rham differential vanishes on
  sections over `f⁻¹W`.
* `AlgebraicGeometry.deRhamComplex_d_zero_app_preimage_eq_zero`: for `f` proper and smooth, the
  degree-zero de Rham differential vanishes on sections over `f⁻¹V` for every open `V` of `S`.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.BottomDifferential`, the statements
are made for an arbitrary package `B` of the three algebras of Stacks Section 17.21 on the sheaf of
relative differentials and an arbitrary de Rham differential `D` on it, so that they apply to the
canonical complex `AlgebraicGeometry.Scheme.Hom.deRhamComplex`, which is the only one. The
`Γ(S, W)`-algebra structure on the sections of `f⁻¹𝒪_S` over `f⁻¹W` is the unit of the adjunction
`f⁻¹ ⊣ f_*`, and its compatibility with `f.app W` is the triangle identity, which is how
`AlgebraicGeometry.inverseImageStructureMap` is defined.

## References

* [Stacks Project, Tag 0G8H](https://stacks.math.columbia.edu/tag/0G8H)
* [Stacks Project, Tag 0G7Y](https://stacks.math.columbia.edu/tag/0G7Y)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The degree-zero de Rham differential vanishes over an open with unramified functions.** If
`Γ(S, W) ⟶ Γ(X, f⁻¹W)` is formally unramified, the degree-zero differential of the relative de
Rham complex of `f` is zero on sections over `f⁻¹W`. -/
theorem deRhamComplex_d_zero_app_preimage_eq_zero_of_formallyUnramified {X S : Scheme.{u}}
    (f : X ⟶ S) (W : S.Opens) (hW : (f.app W).hom.FormallyUnramified)
    (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier)
      (SheafOfModules.moduleOfDifferentials.{u, u, u} (inverseImageStructureMap f)))
    (D : SheafOfModules.DeRhamDifferential B) :
    ((SheafOfModules.deRhamComplex B D).d 0 1).val.app (op (f ⁻¹ᵁ W)) = 0 := by
  let A := (TopCat.Sheaf.pullback CommRingCat f.base).obj S.sheaf
  let φ := inverseImageStructureMap f
  let U := op (f ⁻¹ᵁ W)
  let : Algebra Γ(S, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  -- The `Γ(S, W)`-algebra structure on the sections of `f⁻¹ 𝒪_S` over `f⁻¹W`.
  let baseAdjunction := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  let baseUnit := baseAdjunction.unit.app S.sheaf
  let structureMap : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := ⟨f.c⟩
  let α : Γ(S, W) →+* A.obj.obj U := (baseUnit.hom.app (op W)).hom
  have hcompatible (r : Γ(S, W)) :
      (φ.hom.app U).hom (α r) = algebraMap Γ(S, W) Γ(X, f ⁻¹ᵁ W) r := by
    have htriangle : baseUnit ≫ (TopCat.Sheaf.pushforward CommRingCat f.base).map φ =
        structureMap := by
      change baseAdjunction.homEquiv S.sheaf X.sheaf φ = structureMap
      exact (baseAdjunction.homEquiv S.sheaf X.sheaf).apply_symm_apply structureMap
    exact congrArg (fun morphism => (morphism.hom.app (op W)).hom r) htriangle
  let : Algebra Γ(S, W) (A.obj.obj U) := α.toAlgebra
  -- The universal relative derivation vanishes on every function on `f⁻¹W`.
  let universal := (SheafOfModules.universalDerivation φ).app U
  have huniversal : ∀ z : X.sheaf.obj.obj U, universal.d z = 0 := by
    let : Algebra Γ(S, W) (X.sheaf.obj.obj U) := (f.app W).hom.toAlgebra
    have : Algebra.FormallyUnramified Γ(S, W) (X.sheaf.obj.obj U) := hW
    exact fun z => SheafOfModules.derivation_eq_zero_of_formallyUnramified
      (φ.hom.app U) hcompatible universal z
  ext ω
  have hvalue : ((SheafOfModules.deRhamComplex B D).d 0 1).val.app U ω =
      SheafOfModules.exactOne B U (B.exteriorPieceZeroIsoUnit.hom.val.app U ω) :=
    eq_of_heq (SheafOfModules.deRhamComplex_degreeZero_apply B D U ω)
  rw [hvalue]
  change (B.exteriorGenerator.val.app U)
    (universal.d (B.exteriorPieceZeroIsoUnit.hom.val.app U ω)) = 0
  exact (congrArg (fun z => (B.exteriorGenerator.val.app U) z) (huniversal _)).trans (map_zero _)

/-- **The bottom de Rham differential of a proper smooth morphism vanishes after direct image.**
For `f : X ⟶ S` proper and smooth and every open `V` of `S`, the degree-zero differential of the
relative de Rham complex of `f` is zero on sections over `f⁻¹V`: the morphism
`f_*d : f_*𝒪_X ⟶ f_*Ω¹_{X/S}` is zero. -/
theorem deRhamComplex_d_zero_app_preimage_eq_zero {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [Smooth f] (V : S.Opens)
    (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier)
      (SheafOfModules.moduleOfDifferentials.{u, u, u} (inverseImageStructureMap f)))
    (D : SheafOfModules.DeRhamDifferential B) :
    ((SheafOfModules.deRhamComplex B D).d 0 1).val.app (op (f ⁻¹ᵁ V)) = 0 := by
  ext ω
  refine Stacks.Topology.sheafOfModules_eq_of_locally_eq ((SheafOfModules.deRhamComplex B D).X 1)
    _ _ fun x hx => ?_
  open Stacks.AlgebraicGeometry.ProperFlatGlobalSections in
  obtain ⟨G, hsG, r, b, H⟩ := exists_nhds_globalFunctions_finiteEtale_and_split f (f x)
  obtain ⟨W, hW, hxW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := f x) (U := G ⊓ V) ⟨hsG, hx⟩
  obtain ⟨X', f', j, hsq, ⟨hEt, hFin⟩, -⟩ := H W hW (fun y hy => (hWle hy).1)
  have hWV : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V := fun y hy => (hWle hy).2
  refine ⟨f ⁻¹ᵁ W, hxW, hWV, ?_⟩
  rw [← PresheafOfModules.naturality_apply,
    deRhamComplex_d_zero_app_preimage_eq_zero_of_formallyUnramified f W
      (etale_and_finite_app_of_isPullback hW hsq hEt hFin).1.formallyUnramified B D]
  exact (map_zero _).symm

end AlgebraicGeometry

end

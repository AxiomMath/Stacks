module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent

/-!
# Finite type of a quasi-coherent module along a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes and let `F` be a quasi-coherent
`𝒪_X`-module.  This file proves that `F` is of finite type exactly when its direct image
`f_* F` is.

A finite morphism is affine, so the statement is local on `Y`: the preimages of the affine
opens of `Y` form an affine open cover of `X`, and over an affine open `V = Spec A` of `Y` the
preimage is an affine `Spec B` with `A ⟶ B` finite.  There `Γ(f_* F, V)` and `Γ(F, f ⁻¹ᵁ V)`
are the *same* abelian group, carrying the `A`-module structure and the `B`-module structure
respectively, and a module over a finite `A`-algebra `B` is finite over `A` if and only if it
is finite over `B`.  Finiteness of the sections on affine opens is then transported back to
finite type of the module by [Stacks, Tag 01PB] in one direction and by condition (4) of
[Stacks, Tag 01XZ] in the other.

## Main results

* `AlgebraicGeometry.isFiniteType_of_pushforward_isFiniteType`: the direct image along a
  finite morphism detects finite type, i.e. the converse of
  `Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isFinite`.
* `AlgebraicGeometry.isFiniteType_iff_pushforward_isFiniteType`: the two halves combined.

## Implementation notes

The direct image of modules is Mathlib's `AlgebraicGeometry.Scheme.Modules.pushforward`, for
which `Γ((Scheme.Modules.pushforward f).obj F, V)` and `Γ(F, f ⁻¹ᵁ V)` are definitionally
equal as types; only the scalars differ.  The `Γ(Y, V)`-action on the former is the
restriction of the `Γ(X, f ⁻¹ᵁ V)`-action along `f.app V`, which is what makes the scalar
tower below hold by `rfl`.

## References

* [Stacks Project, Tag 05B3](https://stacks.math.columbia.edu/tag/05B3)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

universe u

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Finiteness of the sections descends along a finite morphism.**  Over an affine open `V`
of the target the sections of `F` on `f ⁻¹ᵁ V` are a finite module over `Γ(X, f ⁻¹ᵁ V)` as
soon as the sections of the direct image are a finite module over `Γ(Y, V)`. -/
private theorem finite_sections_preimage_of_finite_pushforward (f : X ⟶ Y) [IsFinite f]
    (F : X.Modules) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : Module.Finite Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V)) :
    Module.Finite Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V) := by
  let _ : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  let _ : Module Γ(Y, V) Γ(F, f ⁻¹ᵁ V) :=
    inferInstanceAs (Module Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V))
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite Γ(Y, V) Γ(F, f ⁻¹ᵁ V) := h
  exact Module.Finite.of_restrictScalars_finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)

/-- **The direct image along a finite morphism detects finite type.**  If the direct image of a
quasi-coherent module along a finite morphism is of finite type, so is the module itself.

This is the converse of
`Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isFinite`. -/
theorem isFiniteType_of_pushforward_isFiniteType (f : X ⟶ Y) [IsFinite f] (F : X.Modules)
    [F.IsQuasicoherent]
    (h : ((Scheme.Modules.pushforward f).obj F).IsFiniteType) : F.IsFiniteType := by
  have hW (V : Y.affineOpens) : IsAffineOpen (f ⁻¹ᵁ (V : Y.Opens)) :=
    IsAffineHom.isAffine_preimage _ V.2
  refine CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn F
    (fun V : Y.affineOpens ↦ f ⁻¹ᵁ (V : Y.Opens))
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)) hW fun V ↦ ?_
  have hsec : Module.Finite Γ(X, f ⁻¹ᵁ (V : Y.Opens)) Γ(F, f ⁻¹ᵁ (V : Y.Opens)) :=
    finite_sections_preimage_of_finite_pushforward f F V.2
      (CoherentFinite.finite_sections ((Scheme.Modules.pushforward f).obj F) V.2)
  exact CoherentTFAE.isFiniteTildeOn_of_finite_specModule F _ (hW V)
    (Module.Finite.equiv (CoherentFinite.specSectionsEquiv F (hW V)).symm)

/-- A quasi-coherent module on the source of a finite morphism is of finite type if and only if
its direct image is of finite type. -/
@[stacks 05B3]
theorem isFiniteType_iff_pushforward_isFiniteType (f : X ⟶ Y) [IsFinite f] (F : X.Modules)
    [F.IsQuasicoherent] :
    F.IsFiniteType ↔ ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
  ⟨fun _ ↦ PushforwardCoherent.isFiniteType_pushforward_of_isFinite f F,
    isFiniteType_of_pushforward_isFiniteType f F⟩

end AlgebraicGeometry

end

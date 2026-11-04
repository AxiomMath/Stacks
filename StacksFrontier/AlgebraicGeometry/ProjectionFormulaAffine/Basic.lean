module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Modules.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# Localizing the affine projection formula

Let `h : T ⟶ S` be an affine morphism of schemes, `G` a quasi-coherent sheaf of `𝒪_T`-modules
and `H` a quasi-coherent sheaf of `𝒪_S`-modules, and consider the projection-formula map

`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap h G H :`
`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`.

It is invertible if and only if its restriction to each member of an open covering of `S` is,
and, on an affine `S`, if and only if it is invertible on global sections.

## Main results

* `Stacks.ProjectionFormula.isQuasicoherent_projectionFormulaMap_source` and
  `Stacks.ProjectionFormula.isQuasicoherent_projectionFormulaMap_target`: for an affine `h`
  and quasi-coherent `G` and `H`, both the source and the target of the projection-formula map
  are quasi-coherent.
* `Stacks.ProjectionFormula.isIso_projectionFormulaMap_iff_forall_restrict`: the
  projection-formula map is invertible if and only if its restriction to each member of an
  open covering of `S` is invertible.
* `Stacks.ProjectionFormula.isIso_projectionFormulaMap_iff_forall_affineOpen`: the same over
  the covering of `S` by its affine opens.
* `Stacks.ProjectionFormula.isIso_projectionFormulaMap_iff_isIso_moduleSpecΓ`: over an affine
  base `Spec R`, the projection-formula map is invertible if and only if the induced map of
  `R`-modules on global sections is invertible.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.ProjectionFormula

open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula

universe u

/-! ### Moving `IsIso` between the two spellings of the category of modules -/

/-- A morphism of sheaves of modules on the ringed space underlying a scheme `S` which is
invertible there is invertible as a morphism of `S.Modules`. -/
lemma isIso_schemeModules {S : Scheme.{u}}
    {M N : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} {f : M ⟶ N} (hf : IsIso f) :
    @IsIso S.Modules _ (M : S.Modules) (N : S.Modules) f := hf

/-- The converse direction of `isIso_schemeModules`. -/
lemma isIso_sheafOfModules {S : Scheme.{u}}
    {M N : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} {f : M ⟶ N}
    (hf : @IsIso S.Modules _ (M : S.Modules) (N : S.Modules) f) : IsIso f := hf

/-! ### Quasi-coherence of the two sides -/

variable {T S : Scheme.{u}} (h : T ⟶ S)
  (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))

/-- For an affine morphism `h` and quasi-coherent `G` and `H`, the source `h_*G ⊗_{𝒪_S} H` of
the projection-formula map is quasi-coherent. -/
lemma isQuasicoherent_projectionFormulaMap_source [IsAffineHom h]
    (hG : G.IsQuasicoherent) (hH : H.IsQuasicoherent) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩).obj
        (((modulePushforward h.toLRSHom.toShHom).obj G))).obj (H))).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent _ _ _
    (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom h G hG) hH

/-- For an affine morphism `h` and quasi-coherent `G` and `H`, the target
`h_*(G ⊗_{𝒪_T} h^*H)` of the projection-formula map is quasi-coherent. -/
lemma isQuasicoherent_projectionFormulaMap_target [IsAffineHom h]
    (hG : G.IsQuasicoherent) (hH : H.IsQuasicoherent) :
    ((modulePushforward h.toLRSHom.toShHom).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((T.toRingedSpace)).presheaf, ((T.toRingedSpace)).IsSheaf⟩).obj (G)).obj
          (((modulePullback h.toLRSHom.toShHom).obj H))))).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom h _
    (@AlgebraicGeometry.tensorSheaf_isQuasicoherent _ _ _ hG
      (Stacks.Modules.isQuasicoherent_pullback h H hH))

/-! ### Invertibility of the projection-formula map is local on the base -/

/-- The projection-formula map is invertible exactly when its restriction to each member of an
open covering of `S` is invertible. -/
theorem isIso_projectionFormulaMap_iff_forall_restrict
    {I : Type*} (V : I → S.Opens) (hV : IsOpenCover V) :
    IsIso (projectionFormulaMap h G H) ↔
      ∀ i, IsIso ((Scheme.Modules.restrictFunctor (V i).ι).map
        (projectionFormulaMap h G H)) := by
  refine ⟨fun hiso i ↦ ?_, fun hi ↦ ?_⟩
  · have := isIso_schemeModules hiso
    exact Functor.map_isIso (Scheme.Modules.restrictFunctor (V i).ι) _
  · exact isIso_sheafOfModules
      (Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict
        (projectionFormulaMap h G H) V hV hi)

/-- The projection-formula map is invertible exactly when its restriction to every affine open
of `S` is invertible. -/
theorem isIso_projectionFormulaMap_iff_forall_affineOpen :
    IsIso (projectionFormulaMap h G H) ↔
      ∀ V : S.affineOpens, IsIso ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).map
        (projectionFormulaMap h G H)) :=
  isIso_projectionFormulaMap_iff_forall_restrict h G H (fun V : S.affineOpens ↦ (V : S.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top S))

/-! ### The affine criterion -/

/-- For an affine morphism `h : T ⟶ Spec R` and quasi-coherent `G` and `H`, the
projection-formula map is invertible exactly when the induced map of `R`-modules on global
sections is invertible. -/
theorem isIso_projectionFormulaMap_iff_isIso_moduleSpecΓ {R : CommRingCat.{u}} {T : Scheme.{u}}
    (h : T ⟶ Spec R) [IsAffineHom h]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) (hG : G.IsQuasicoherent)
    (H : SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) (hH : H.IsQuasicoherent) :
    IsIso (projectionFormulaMap h G H) ↔
      IsIso (moduleSpecΓFunctor.map (projectionFormulaMap h G H)) := by
  refine ⟨fun hiso ↦ ?_, fun hΓ ↦ ?_⟩
  · have := isIso_schemeModules hiso
    exact Functor.map_isIso (moduleSpecΓFunctor (R := R)) _
  · exact isIso_sheafOfModules
      (@Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ R _ _
        (isQuasicoherent_projectionFormulaMap_source h G H hG hH)
        (isQuasicoherent_projectionFormulaMap_target h G H hG hH)
        (projectionFormulaMap h G H) hΓ)

end Stacks.ProjectionFormula

end

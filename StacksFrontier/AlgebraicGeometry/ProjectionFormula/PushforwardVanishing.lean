module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree

/-!
# Consequences of the projection formula at a finite locally free module

For a morphism of schemes `f : Z ⟶ X`, a module `𝒢` on `Z` and a finite locally free module `ℋ`
on `X`, the projection formula of
`StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteLocallyFree` gives
`f_*(𝒢 ⊗ f^*ℋ) ≅ f_*𝒢 ⊗ ℋ`. This file states it as an isomorphism, with finite local freeness in
the form `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, and deduces that
`f_*(𝒢 ⊗ f^*ℋ) = 0` as soon as `f_*𝒢 = 0`. It also shows that a biproduct with all summands but
one zero is that summand.

## Main results

* `Stacks.AffineProjectionFormula.exists_openRestrict_iso_free`: a finite locally free module is
  free of finite rank near every point.
* `Stacks.AffineProjectionFormula.pushforwardTensorPullbackIso`: the projection formula
  `f_*(𝒢 ⊗ f^*ℋ) ≅ f_*𝒢 ⊗ ℋ` at a finite locally free `ℋ`.
* `Stacks.AffineProjectionFormula.isZero_tensorSheaf_of_isZero_left`: `0 ⊗ ℬ = 0`.
* `Stacks.AffineProjectionFormula.isZero_pushforward_tensor_pullback`: `f_*(𝒢 ⊗ f^*ℋ) = 0` if
  `f_*𝒢 = 0`.
* `CategoryTheory.Limits.biproductIsoOfIsZero`: a biproduct all of whose summands but one are
  zero is that summand.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AffineProjectionFormula

/-- **The tensor product of sheaves of modules with a zero first factor is zero.** -/
theorem isZero_tensorSheaf_of_isZero_left {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {A : SheafOfModules.{u} (structureRingSheaf X)} (hA : IsZero A)
    (B : SheafOfModules.{u} (structureRingSheaf X)) :
    IsZero ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj (A, B)) := by
  rw [IsZero.iff_id_eq_zero]
  have h0 : ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
        ((0 : A ⟶ A) ×ₘ 𝟙 B) = 0 := by
    have h := tensorSheaf_map_add_left (0 : A ⟶ A) (0 : A ⟶ A) (𝟙 B)
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  rw [← h0, ← hA.eq_of_src (𝟙 A) 0, ← CategoryTheory.Functor.map_id]
  rfl

/-- **A finite locally free module on a scheme is free of finite rank near every point**: every
point `x` has an open neighbourhood `V` on which the restriction is isomorphic to a free module
on a finite type. -/
theorem exists_openRestrict_iso_free {X : Scheme.{u}} (H : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) H]
    (x : X.carrier) :
    ∃ (V : X.Opens) (_ : x ∈ V) (I : Type u) (_ : Finite I),
      Nonempty (openRestrictModule V H ≅ SheafOfModules.free.{u} I) := by
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  obtain ⟨i, hi, ⟨e⟩⟩ := Stacks.Modules.exists_restrict_iso_free H q hq x
  exact ⟨q.X i, hi, (q.generators i).I, (hfin.isFiniteType i).finite, ⟨e⟩⟩

variable {Z X : Scheme.{u}} (f : Z ⟶ X)

/-- **The projection formula at a finite locally free module, as an isomorphism**:
`f_*(𝒢 ⊗ f^*ℋ) ≅ f_*𝒢 ⊗ ℋ`, the inverse of the canonical projection-formula map. -/
def pushforwardTensorPullbackIso (G : Z.Modules) (H : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) H] :
    (pushforwardFunctor f.toLRSHom.toShHom).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.toRingedSpace.sheaf)).obj
          (G, (pullbackFunctor f.toLRSHom.toShHom).obj H)) ≅
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf)).obj
          ((pushforwardFunctor f.toLRSHom.toShHom).obj G, H) :=
  haveI := isIso_projectionFormulaMap_of_isFiniteLocallyFree f G H
    (exists_openRestrict_iso_free H)
  (asIso (projectionFormulaMap f.toLRSHom.toShHom G H)).symm

/-- **`f_*(𝒢 ⊗ f^*ℋ) = 0` when `f_*𝒢 = 0`**, for `ℋ` finite locally free. -/
theorem isZero_pushforward_tensor_pullback (G : Z.Modules) (H : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) H]
    (hG : IsZero ((Scheme.Modules.pushforward f).obj G)) :
    IsZero ((pushforwardFunctor f.toLRSHom.toShHom).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.toRingedSpace.sheaf)).obj
          (G, (pullbackFunctor f.toLRSHom.toShHom).obj H))) :=
  IsZero.of_iso (isZero_tensorSheaf_of_isZero_left hG H) (pushforwardTensorPullbackIso f G H)

end Stacks.AffineProjectionFormula

namespace CategoryTheory.Limits

/-- A biproduct all of whose summands but one are zero is that summand. -/
def biproductIsoOfIsZero {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    [DecidableEq J] (F : J → C) [HasBiproduct F] (j₀ : J) (h : ∀ j, j ≠ j₀ → IsZero (F j)) :
    ⨁ F ≅ F j₀ where
  hom := biproduct.π F j₀
  inv := biproduct.ι F j₀
  hom_inv_id := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    by_cases hj : j = j₀
    · subst hj; simp
    · exact (h j hj).eq_of_src _ _
  inv_hom_id := by simp

end CategoryTheory.Limits

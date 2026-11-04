module

public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Eilenberg–Watts: an `R`-linear cocontinuous functor on modules is a tensor product

For an `R`-linear functor `F : ModuleCat R ⥤ ModuleCat R` preserving colimits, the canonical
comparison map `F(R) ⊗[R] M ⟶ F(M)` of `Stacks.EilenbergWatts.wattsMap` is an isomorphism,
naturally in `M`.

## Main definitions

* `Stacks.EilenbergWatts.freeCover`: the canonical epimorphism onto `M` from a coproduct of
  copies of `R`, one for each element of `M`.
* `Stacks.EilenbergWatts.wattsIso`: the isomorphism of functors `F(R) ⊗ - ≅ F`.

## Main results

* `Stacks.EilenbergWatts.isIso_app_of_isColimit`: a natural transformation between two functors
  preserving a given colimit, invertible at every object of the diagram, is invertible at the
  colimit.
* `Stacks.EilenbergWatts.isIso_wattsMap`: the Eilenberg–Watts theorem.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace Stacks.EilenbergWatts

/-- A natural transformation between two functors preserving a colimit, which is an isomorphism at
every object of the diagram, is an isomorphism at the colimit. -/
theorem isIso_app_of_isColimit {C D : Type*} [Category C] [Category D]
    {G F : C ⥤ D} (α : G ⟶ F) {J : Type*} [Category J] {K : J ⥤ C} {c : Cocone K}
    (hc : IsColimit c) [PreservesColimit K G] [PreservesColimit K F]
    (h : ∀ j, IsIso (α.app (K.obj j))) : IsIso (α.app c.pt) := by
  have hG : IsColimit (G.mapCocone c) := isColimitOfPreserves G hc
  have hF : IsColimit (F.mapCocone c) := isColimitOfPreserves F hc
  let β : K ⋙ G ≅ K ⋙ F :=
    NatIso.ofComponents (fun j => @asIso _ _ _ _ (α.app (K.obj j)) (h j))
      (fun f => α.naturality (K.map f))
  have key : α.app c.pt = (IsColimit.coconePointsIsoOfNatIso hG hF β).hom := by
    refine hG.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact α.naturality (c.ι.app j)
  rw [key]
  infer_instance

variable {R : Type u} [CommRing R] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
  [F.Additive] [F.Linear R]

/-- The Eilenberg–Watts comparison map, as a natural transformation `F(R) ⊗ - ⟶ F`. -/
def wattsNatTrans : tensorLeft (F.obj (ModuleCat.of R R)) ⟶ F where
  app M := wattsMap F M
  naturality _ _ f := wattsMap_naturality F f

/-- The components of `wattsNatTrans F` are the comparison maps `wattsMap F M`. -/
@[simp]
theorem wattsNatTrans_app (M : ModuleCat.{u} R) : (wattsNatTrans F).app M = wattsMap F M := rfl

/-- The comparison map is an isomorphism at `R`. -/
instance isIso_wattsMap_unit : IsIso (wattsMap F (ModuleCat.of R R)) := by
  rw [wattsMap_unit]
  exact (TensorProduct.rid R (F.obj (ModuleCat.of R R))).toModuleIso.isIso_hom

/-- Tensoring on the left with an `R`-module preserves colimits. -/
instance preservesColimits_tensorLeft (A : ModuleCat.{u} R) :
    PreservesColimits (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

/-- The canonical epimorphism onto `M` from a coproduct of copies of `R`, one for each element of
`M`. -/
def freeCover (M : ModuleCat.{u} R) : (∐ fun _ : M => ModuleCat.of R R) ⟶ M :=
  Sigma.desc fun m => ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)

/-- `freeCover M` is an epimorphism. -/
instance epi_freeCover (M : ModuleCat.{u} R) : Epi (freeCover M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨(Sigma.ι (fun _ : M => ModuleCat.of R R) m).hom (1 : R), ?_⟩
  have h : (Sigma.ι (fun _ : M => ModuleCat.of R R) m ≫ freeCover M).hom (1 : R) = m := by
    rw [freeCover, Sigma.ι_desc]
    simp
  simpa using h

variable [PreservesColimits F]

/-- The comparison map is an isomorphism at a coproduct of copies of `R`. -/
theorem isIso_wattsMap_coproduct (ι : Type u) :
    IsIso (wattsMap F (∐ fun _ : ι => ModuleCat.of R R)) :=
  isIso_app_of_isColimit (wattsNatTrans F)
    (colimit.isColimit (Discrete.functor fun _ : ι => ModuleCat.of R R))
    fun ⟨_⟩ => isIso_wattsMap_unit F

/-- Eilenberg–Watts: for an `R`-linear, colimit-preserving functor `F` on `R`-modules the canonical
comparison map `F(R) ⊗[R] M ⟶ F(M)` is an isomorphism, for every `M`. -/
instance isIso_wattsMap (M : ModuleCat.{u} R) : IsIso (wattsMap F M) :=
  have : Epi (freeCover (kernel (freeCover M))) := epi_freeCover _
  isIso_app_of_isColimit (wattsNatTrans F)
    (isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (freeCover M)))
      (freeCover (kernel (freeCover M))) rfl)
    fun j => by cases j <;> exact isIso_wattsMap_coproduct F _

/-- Eilenberg–Watts, as an isomorphism of functors: an `R`-linear colimit-preserving functor on
`R`-modules is tensoring with `F(R)`. -/
def wattsIso : tensorLeft (F.obj (ModuleCat.of R R)) ≅ F :=
  NatIso.ofComponents (fun M => asIso (wattsMap F M)) (fun f => wattsMap_naturality F f)

example (M : ModuleCat.{u} R) : IsIso (wattsMap (𝟭 (ModuleCat.{u} R)) M) := inferInstance

end Stacks.EilenbergWatts

end

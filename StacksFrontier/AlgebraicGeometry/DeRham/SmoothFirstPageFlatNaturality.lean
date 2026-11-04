module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatCohomologyNaturality

/-!
# Naturality of the tiny argument of [Stacks, Tag 0FMN]

`Stacks.DeRhamSmooth.flatDegenerateDerivedTensor` identifies `H^t(M ⊗^𝐋_{𝒪_Y} K)` with
`M ⊗_{𝒪_Y} H^t(K)` for `K` with flat cohomology sheaves. This file proves that the identification
is natural in the module `M`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

/-- Conjugating a commutative square by isomorphisms. -/
theorem inv_comp_eq_comp_inv_of_hom {C : Type*} [Category C] {A B A' B' : C} (e : A ≅ B)
    (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ e'.hom = e.hom ≫ b) :
    e.inv ≫ a = b ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h]

/-- **The tiny argument `flatDegenerateDerivedTensor` is natural in the module**, in the direction
of its forward map. -/
theorem flatDegenerateDerivedTensor_hom_naturality (Y : Scheme.{u}) {M M' : Y.Modules}
    (φ : M ⟶ M') (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace))
    (hK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) i).obj K)) (t : ℤ) :
    (DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) t).map
        (((Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.map
          ((DerivedCategory.singleFunctor _ 0).map φ)).app K) ≫
        (flatDegenerateDerivedTensor Y M' K hK t).hom =
      (flatDegenerateDerivedTensor Y M K hK t).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map φ).app _ := by
  have h := Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology_hom_naturality
    (R := Y.toRingedSpace.sheaf) φ K hK t
  have e : ∀ N : Y.Modules, (flatDegenerateDerivedTensor Y N K hK t).hom =
      (Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology
        (R := Y.toRingedSpace.sheaf) N K hK t).hom := fun N =>
    (congrArg (· ≫ (Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology
        (R := Y.toRingedSpace.sheaf) N K hK t).hom)
      ((congrArg (fun x => (DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) t).map (NatTrans.app x K))
          ((Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.map_id
            ((DerivedCategory.singleFunctor _ 0).obj N))).trans
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) t).map_id _))).trans
      (Category.id_comp _)
  exact ((congrArg (_ ≫ ·) (e M')).trans h).trans (congrArg (· ≫ _) (e M).symm)

/-- **The tiny argument `flatDegenerateDerivedTensor` is natural in the module**, in the direction
of its inverse. -/
theorem flatDegenerateDerivedTensor_inv_naturality (Y : Scheme.{u}) {M M' : Y.Modules}
    (φ : M ⟶ M') (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace))
    (hK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) i).obj K)) (t : ℤ) :
    (flatDegenerateDerivedTensor Y M K hK t).inv ≫
        (DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) t).map
          (((Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.map
            ((DerivedCategory.singleFunctor _ 0).map φ)).app K) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map φ).app _ ≫
        (flatDegenerateDerivedTensor Y M' K hK t).inv :=
  inv_comp_eq_comp_inv_of_hom _ _ _ _ (flatDegenerateDerivedTensor_hom_naturality Y φ K hK t)

end Stacks.DeRhamSmooth

end

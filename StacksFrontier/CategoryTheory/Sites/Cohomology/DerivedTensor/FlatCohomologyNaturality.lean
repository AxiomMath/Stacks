module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatCohomology

/-!
# Naturality of the derived tensor product with an object with flat cohomology

For a sheaf of `O`-modules `A` and an object `E` of `D(O)` with flat cohomology sheaves,
`Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology` identifies
`H^t(A[0] ⊗^𝐋_O E)` with `A ⊗_O H^t(E)`. This file proves that the identification is natural in
the module `A`, with no hypothesis on `A`.

## Main results

* `Stacks.DerivedTensor.RingedSite.homologyShiftedTensorIso_hom_naturality_left`: the shift
  bookkeeping `H^c(K ⊗^𝐋 L⟦-c⟧) ≅ H^0(K ⊗^𝐋 L)` is natural in `K`.
* `Stacks.DerivedTensor.RingedSite.degreeSingleTensorIso_hom_naturality`: the read-off
  `H^c(A[0] ⊗^𝐋 G[c]) ≅ A ⊗ G` is natural in `A`.
* `Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology_hom_naturality`:
  `H^t(A[0] ⊗^𝐋 E) ≅ A ⊗ H^t(E)` is natural in `A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedTensor.RingedSite

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **The shift bookkeeping `H^c(K ⊗^𝐋 L⟦-c⟧) ≅ H^0(K ⊗^𝐋 L)` is natural in `K`.** -/
theorem homologyShiftedTensorIso_hom_naturality_left (T : DerivedTensorProduct R)
    {K K' : DerivedModules R} (β : K ⟶ K') (L : DerivedModules R) (c : ℤ) :
    (homologyFunctor (Modules R) c).map ((T.tensor.map β).app (L⟦-c⟧)) ≫
        (homologyShiftedTensorIso R T K' L c).hom =
      (homologyShiftedTensorIso R T K L c).hom ≫
        (homologyFunctor (Modules R) 0).map ((T.tensor.map β).app L) := by
  have h₁ := NatTrans.shift_app_comm (T.tensor.map β) (-c) L
  have h₂ := (Stacks.HomologyShift.homologyShiftIso (Modules R) (-c) c 0 (by lia)).hom.naturality
    ((T.tensor.map β).app L)
  dsimp only [homologyShiftedTensorIso, tensorShiftRightIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom] at h₂ ⊢
  rw [← Functor.map_comp_assoc, ← h₁, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ h₂

/-- **The read-off `H^c(A[0] ⊗^𝐋 G[c]) ≅ A ⊗ G` is natural in `A`.** -/
theorem degreeSingleTensorIso_hom_naturality (G : Modules R) {A A' : Modules R} (a : A ⟶ A')
    (c : ℤ) :
    (homologyFunctor (Modules R) c).map
          (((derivedTensorProductFunctor R).map
            (Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map a))).app
            ((singleFunctor (Modules R) c).obj G)) ≫
        (degreeSingleTensorIso R G A' c).hom =
      (degreeSingleTensorIso R G A c).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app G := by
  set α := (derivedTensorProductFunctor R).map
    (Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map a))
  have h₁ := α.naturality (singleShiftIso R G c).hom
  have h₂ := homologyShiftedTensorIso_hom_naturality_left (canonicalDerivedTensorProduct R)
    (Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map a))
    (Q.obj (sg R G)) c
  have h₃ := degreeZeroTensorMap_naturality R G a
  dsimp only [degreeSingleTensorIso, degreeShiftedTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    degreeZeroTensorIso_hom]
  rw [← Functor.map_comp_assoc, ← h₁, Functor.map_comp_assoc, reassoc_of% h₂, Category.assoc,
    Category.assoc]
  exact congrArg _ (congrArg _ h₃)

/-- **`H^t(A[0] ⊗^𝐋 E) ≅ A ⊗ H^t(E)` is natural in the module `A`**, for `E` with flat cohomology
sheaves. -/
theorem tensorHomologyIsoOfHasFlatHomology_hom_naturality {A A' : Modules R} (a : A ⟶ A')
    (E : DerivedModules R) (hE : HasFlatHomology R E) (t : ℤ) :
    (homologyFunctor (Modules R) t).map
          (((derivedTensorProductFunctor R).map
            (Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map a))).app E) ≫
        (tensorHomologyIsoOfHasFlatHomology A' E hE t).hom =
      (tensorHomologyIsoOfHasFlatHomology A E hE t).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app
          ((homologyFunctor (Modules R) t).obj E) := by
  set α := (derivedTensorProductFunctor R).map
    (Q.map ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map a))
  have := isIso_homologyMap_singleTensor_truncLTι A E hE t
  have := isIso_homologyMap_singleTensor_truncLTι A' E hE t
  have hnat {X Y : DerivedModules R} (f : X ⟶ Y) :
      (homologyFunctor (Modules R) t).map (α.app X) ≫
        (homologyFunctor (Modules R) t).map ((singleTensor R A').map f) =
      (homologyFunctor (Modules R) t).map ((singleTensor R A).map f) ≫
        (homologyFunctor (Modules R) t).map (α.app Y) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (α.naturality f).symm
  have h₁ : (homologyFunctor (Modules R) t).map (α.app E) ≫
      inv ((homologyFunctor (Modules R) t).map
        ((singleTensor R A').map ((TStructure.t.truncLTι (t + 1)).app E))) =
      inv ((homologyFunctor (Modules R) t).map
        ((singleTensor R A).map ((TStructure.t.truncLTι (t + 1)).app E))) ≫
        (homologyFunctor (Modules R) t).map (α.app _) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact (hnat _).symm
  have h₄ := degreeSingleTensorIso_hom_naturality ((homologyFunctor (Modules R) t).obj E) a t
  dsimp only [tensorHomologyIsoOfHasFlatHomology, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% (hnat ((TStructure.t.truncGEπ t).app _)),
    reassoc_of% (hnat ((truncGELTIsoHomologyFunctorCompSingleFunctor t).app E).hom), h₄]

end Stacks.DerivedTensor.RingedSite

end

module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeTrace
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapComp

/-!
# Equation 48.8.0.1 for a composite

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of quasi-compact and quasi-separated
schemes with `h = f ≫ g` and right adjoints `a`, `b`, `c` of `Rf_*`, `Rg_*`, `Rh_*` on `D_QCoh`,
the maps `Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` of Equation 48.8.0.1 for `f`, `g` and `h` are compatible with
`Lh^* = Lf^* ∘ Lg^*` and `c = a ∘ b` ([Stacks, Tag 0B6R]).

## Main results

* `Stacks.Duality.twistedInverseImageCompareWithPullback_comp`: the maps of Equation 48.8.0.1
  for `f`, `g` and `f ≫ g` are compatible with `Lh^* = Lf^* ∘ Lg^*` and `c = a ∘ b`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality


section Helpers

variable {C : Type*} [Category C] [MonoidalCategory C] (T : C ⥤ C ⥤ C) (ι : T ≅ curriedTensor C)

/-- Naturality of an identification of a bifunctor with the tensor product, first variable. -/
@[reassoc]
lemma tensorIso_hom_naturality_left {A A' : C} (p : A ⟶ A') (B : C) :
    (T.map p).app B ≫ (ι.hom.app A').app B = (ι.hom.app A).app B ≫ p ▷ B :=
  congrArg (fun t => t.app B) (ι.hom.naturality p)

/-- Naturality of an identification of a bifunctor with the tensor product, second variable. -/
@[reassoc]
lemma tensorIso_hom_naturality_right (A : C) {B B' : C} (x : B ⟶ B') :
    (T.obj A).map x ≫ (ι.hom.app A).app B' = (ι.hom.app A).app B ≫ A ◁ x :=
  (ι.hom.app A).naturality x

/-- The components of an identification of a bifunctor with the tensor product compose to the
identity: inverse followed by hom. -/
@[reassoc]
lemma tensorIso_inv_hom_app_app (A B : C) : (ι.inv.app A).app B ≫ (ι.hom.app A).app B = 𝟙 _ := by
  rw [← NatTrans.comp_app, Iso.inv_hom_id_app, NatTrans.id_app]

/-- The inverse-then-hom identity for an identification of a bifunctor with the tensor product,
whiskered on the right by `Z`. -/
@[reassoc]
lemma tensorIso_inv_hom_app_app_whiskerRight (A B Z : C) :
    (ι.inv.app A).app B ▷ Z ≫ (ι.hom.app A).app B ▷ Z = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, tensorIso_inv_hom_app_app,
    MonoidalCategory.id_whiskerRight]

/-- The inverse-then-hom identity for an identification of a bifunctor with the tensor product,
whiskered on the left by `Z`. -/
@[reassoc]
lemma tensorIso_inv_hom_app_app_whiskerLeft (Z A B : C) :
    Z ◁ (ι.inv.app A).app B ≫ Z ◁ (ι.hom.app A).app B = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, tensorIso_inv_hom_app_app,
    MonoidalCategory.whiskerLeft_id]

end Helpers

/-- The comparison map at a unit-like `U`, followed by the right unitor, is natural in the first
variable. -/
@[reassoc]
lemma comparisonMap_whiskerUnit_naturality {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.OplaxMonoidal] [∀ (K : C) (M : D), IsIso (adj.projectionMap K M)] {a : C ⥤ D}
    (b : G ⊣ a) {U : C} (w : U ⟶ 𝟙_ C) {X X' : C} (h : X ⟶ X') :
    adj.comparisonMap b X U ≫ a.map (X ◁ w) ≫ a.map (ρ_ X).hom ≫ a.map h =
      F.map h ▷ a.obj U ≫ adj.comparisonMap b X' U ≫ a.map (X' ◁ w) ≫ a.map (ρ_ X').hom := by
  rw [Adjunction.comparisonMap_naturality_left_assoc]
  simp only [← Functor.map_comp]
  congr 2
  rw [← whisker_exchange_assoc, MonoidalCategory.rightUnitor_naturality]

variable {X Y Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composite of the derived adjunctions of `g` and `f` on `D_QCoh`, read through the
composition formulas for derived pullback and derived direct image, has the counit of the derived
adjunction of `f ≫ g`. -/
theorem map_quasiCoherentDerivedPushforwardCompIso_comp_counit
    (M : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedPullback' (f ≫ g)).map
        ((quasiCoherentDerivedPushforwardCompIso f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).hom.app M) ≫
      (quasiCoherentDerivedAdjunction (f ≫ g) (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).counit.app M =
    (quasiCoherentDerivedPullbackCompIso f g).inv.app _ ≫
      ((quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).comp
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))).counit.app M := by
  apply ObjectProperty.hom_ext
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft (derivedPullbackCompIso f g))
    (derivedAdjunction (f ≫ g)) M.obj
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_counit_app] at h
  simp only [ObjectProperty.FullSubcategory.comp_hom, Adjunction.comp_counit_app,
    quasiCoherentDerivedPullback_map_hom, quasiCoherentDerivedAdjunction_counit_app_hom,
    quasiCoherentDerivedPullbackCompIso_inv_app_hom,
    quasiCoherentDerivedPushforwardCompIso_hom_app_hom]
  exact h

/-- The twisted inverse image of `f ≫ g` is that of `g` followed by that of `f`, compatibly with
the counits through the composition formula for derived direct image. -/
theorem map_twistedInverseImageCompIso_inv_comp_counit (L : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPushforward (f ≫ g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).map
        ((twistedInverseImageCompIso f g (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).symm.hom.app L) ≫
      (twistedInverseImageAdjunction (f ≫ g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).counit.app L =
    (quasiCoherentDerivedPushforwardCompIso f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).inv.app _ ≫
      ((twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).comp
        (twistedInverseImageAdjunction g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))).counit.app L := by
  rw [twistedInverseImageCompIso, Iso.symm_hom, Adjunction.rightAdjointUniq_inv_app,
    Adjunction.rightAdjointUniq_hom_app_counit, Adjunction.ofNatIsoLeft_counit]
  rfl

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of quasi-compact and quasi-separated schemes,
`h = f ≫ g`, and `a`, `b`, `c` the right adjoints of `Rf_*`, `Rg_*`, `Rh_*` on `D_QCoh`. For
`K ∈ D_QCoh(𝒪_Z)` the diagram

```
Lf^*(Lg^*K ⊗ᴸ b(𝒪_Z)) ⊗ᴸ a(𝒪_Y) ──→ a(Lg^*K ⊗ᴸ b(𝒪_Z)) ──→ a(b(K))
            ‖                                                  ‖
Lh^*K ⊗ᴸ (Lf^*b(𝒪_Z) ⊗ᴸ a(𝒪_Y)) ──→ Lh^*K ⊗ᴸ c(𝒪_Z) ──────→ c(K)
```

commutes, where the arrows are Equation 48.8.0.1 (for `f` at `Lg^*K ⊗ᴸ b(𝒪_Z)`, `a` of that for
`g` at `K`; `Lh^*K` tensored with that for `f` at `b(𝒪_Z)`, then that for `h` at `K`), the left
identification is the tensor comparison of `Lf^*`, the associator and `Lf^* ∘ Lg^* = Lh^*`, and
`c = a ∘ b` is `Stacks.Duality.twistedInverseImageCompIso`. -/
@[stacks 0B6R]
theorem twistedInverseImageCompareWithPullback_comp (K : quasiCoherentDerivedCategory Z) :
    twistedInverseImageCompareWithPullback f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedTensorRightUnitor Y)
        (((quasiCoherentDerivedTensor Y).obj ((quasiCoherentDerivedPullback' g).obj K)).obj
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
            (DerivedPushforward.derivedStructureSheaf Z))) ≫
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
        (twistedInverseImageCompareWithPullback g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (quasiCoherentDerivedPullbackTensorIso g).hom (quasiCoherentDerivedTensorRightUnitor Z)
          K) ≫
      (twistedInverseImageCompIso f g (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).inv.app K =
    (((quasiCoherentDerivedTensor X).map ((quasiCoherentDerivedPullbackTensorIso f).hom.app
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
            (DerivedPushforward.derivedStructureSheaf Z),
          (quasiCoherentDerivedPullback' g).obj K))).app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y)) ≫
      ((quasiCoherentDerivedTensorIsoCurriedTensor X).hom.app _).app _ ≫
      ((quasiCoherentDerivedTensorIsoCurriedTensor X).hom.app
          ((quasiCoherentDerivedPullback' f).obj ((quasiCoherentDerivedPullback' g).obj K))).app
          ((quasiCoherentDerivedPullback' f).obj
            ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
              (DerivedPushforward.derivedStructureSheaf Z))) ▷ _ ≫
      (α_ _ _ _).hom ≫
      _ ◁ ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app _).app _ ≫
      ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app _).app _ ≫
      ((quasiCoherentDerivedTensor X).map
          ((quasiCoherentDerivedPullbackCompIso f g).hom.app K)).app _) ≫
      ((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' (f ≫ g)).obj K)).map
        (twistedInverseImageCompareWithPullback f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedTensorRightUnitor Y)
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
            (DerivedPushforward.derivedStructureSheaf Z)) ≫
          (twistedInverseImageCompIso f g (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).inv.app
            (DerivedPushforward.derivedStructureSheaf Z)) ≫
      twistedInverseImageCompareWithPullback (f ≫ g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))
        (quasiCoherentDerivedPullbackTensorIso (f ≫ g)).hom
        (quasiCoherentDerivedTensorRightUnitor Z) K := by
  have key := CategoryTheory.Adjunction.comparisonMap_unit_comp
    (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (twistedInverseImageAdjunction g (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (quasiCoherentDerivedAdjunction (f ≫ g) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g)))
    (twistedInverseImageAdjunction (f ≫ g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g)))
    (quasiCoherentDerivedPullbackCompIso f g)
    (quasiCoherentDerivedPushforwardCompIso f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g)))
    (twistedInverseImageCompIso f g (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).symm
    (NatTrans.IsMonoidal.δ_comp_tensorHom (quasiCoherentDerivedPullbackCompIso f g).hom)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f g)
    (map_twistedInverseImageCompIso_inv_comp_counit f g)
    (tensorUnit_quasiCoherentDerivedCategory Z) (tensorUnit_quasiCoherentDerivedCategory Y) K
  simp only [Iso.symm_hom] at key
  rw [twistedInverseImageCompareWithPullback_eq_comparisonMap f,
    twistedInverseImageCompareWithPullback_eq_comparisonMap g,
    twistedInverseImageCompareWithPullback_eq_comparisonMap f,
    twistedInverseImageCompareWithPullback_eq_comparisonMap (f ≫ g),
    quasiCoherentDerivedPullbackTensorIso_hom_app]
  simp only [Functor.map_comp, Category.assoc, MonoidalCategory.whiskerLeft_comp] at key
  dsimp only [Functor.comp_obj] at key
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.prod_obj, CategoryTheory.Prod.swap_obj,
    Functor.uncurry_obj_obj]
  simp only [tensorIso_hom_naturality_left_assoc, tensorIso_hom_naturality_right_assoc,
    tensorIso_inv_hom_app_app_assoc, tensorIso_inv_hom_app_app_whiskerRight_assoc]
  rw [whisker_exchange_assoc, tensorIso_inv_hom_app_app_whiskerLeft_assoc,
    comparisonMap_whiskerUnit_naturality_assoc]
  dsimp only [curriedTensor_obj_obj]
  rw [key]

end Stacks.Duality

end

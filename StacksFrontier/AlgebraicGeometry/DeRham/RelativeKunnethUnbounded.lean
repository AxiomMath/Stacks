module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMapUnbounded
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.Relative
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate
import StacksCore.Tactic.StacksAttribute

/-!
# The relative Künneth map of the box product for unbounded complexes

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y`, `f = p ∘ a`, and let
`𝓕^•` on `X/S` and `𝓖^•` on `Y/S` be `ℤ`-indexed complexes whose differentials are differential
operators of finite order. When the total complex `Tot(𝓕^• ⊠ 𝓖^•)` is formed over `f^{-1}𝒪_S`,
which has all direct sums, the relative Künneth map of [Stacks, Tag 0G4B]

`Ra_*(𝓕^•) ⊗^𝐋_{𝒪_S} Rb_*(𝓖^•) ⟶ Rf_*(Tot(𝓕^• ⊠ 𝓖^•))`

exists for arbitrary complexes, with no boundedness. This file defines it and proves that it is
natural in both complexes along morphisms of complexes. The naturality is the input that a
dévissage over the complexes needs.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMapUnbounded`: the map. It is the Künneth map of
  [Stacks, Tag 0FLP] for the inverse-image ringed spaces, followed by `Rf_*` of
  `Stacks.Cohomology.BoxKunneth.boxTotalComplexDerivedComparison`.

## Main results

* `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMapUnbounded_natural_left` and
  `relativeBoxKunnethMapUnbounded_natural_right`: **naturality in each complex**.
* `Stacks.Cohomology.BoxKunneth.boxTotalComplexDerivedComparison_naturality_right` (the left one is
  the base's `Stacks.Cohomology.BoxKunnethFlat.boxTotalComplexDerivedComparison_naturality_left`):
  the naturality of steps (4) and (5).
* `Stacks.Cohomology.BoxKunneth.pullbackComplexComparison_naturality`: the naturality of the
  derived-to-degreewise inverse image comparison.

## Implementation notes

*Everything that is rewritten is stated over variables.* The two total complexes in steps (4) and
(5) are spelled through two presentations of the structure sheaf of `(W, f^{-1}𝒪_S)`. At those
spellings the concrete goals are type-correct only at default transparency, so a rewrite in a
concrete goal either fails or exhausts the heartbeat budget, as the notes of
`StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparisonExists` record. Each composite is
therefore handled by a lemma over variables:
* `CategoryTheory.Functor.mapBifunctorMap_comp_total_map_homMk` for a total morphism built from
  degreewise data;
* `CategoryTheory.Functor.bifunctor_comp_four_naturality_left` and `_right` for steps (4)
  and (5);
* `CategoryTheory.Functor.comp_map_naturality` for the composite with `Rf_*`.
Each such lemma is then applied by unification.

## References

* [Stacks Project, Tag 0G4B](https://stacks.math.columbia.edu/tag/0G4B)
* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.DerivedTensor.RingedSite

universe d

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules R)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]

/-- Naturality of the canonical map to the total tensor complex in the right variable alone. -/
theorem DerivedTensorProduct.toTensor_naturality_right (T : DerivedTensorProduct.{d, u} R)
    (K : CochainComplex (Modules R) ℤ) {L L' : CochainComplex (Modules R) ℤ} (g : L ⟶ L') :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫ T.toTensor K L' =
      T.toTensor K L ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) g
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)) := by
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using
    T.toTensor_naturality (𝟙 K) g

end Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

section Pullback

variable {Z Z' : RingedSpace.{u, u}} (g : Z ⟶ Z')

/-- **The comparison `Lg^*K ⟶ g^*K` is natural in the complex `K`**: it is built from the counit
of the left derived functor `Lg^*` and the two identifications of the localization functors, each
of which is natural. -/
theorem pullbackComplexComparison_naturality
    {C C' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ} (ψ : C ⟶ C') :
    (derivedPullback.{u, u + 1, u + 1} g).map (DerivedCategory.Q.map ψ) ≫
        pullbackComplexComparison g C' =
      pullbackComplexComparison g C ≫
        DerivedCategory.Q.map (((RingedSpaceModuleAdjunction.modulePullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ψ) := by
  have h₁ := (DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (structureSheafRing Z'))).inv.naturality ψ
  have h₂ := (derivedPullbackComparison g).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ψ)
  have h₃ := (DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (structureSheafRing Z))).hom.naturality
      (((RingedSpaceModuleAdjunction.modulePullback g).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ψ)
  dsimp only [Functor.comp_map] at h₁ h₂ h₃
  rw [pullbackComplexComparison, pullbackComplexComparison, ← Functor.map_comp_assoc, h₁,
    Functor.map_comp, Category.assoc]
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h₂).trans (Category.assoc _ _ _)))).trans ?_
  exact (congrArg (fun t => _ ≫ _ ≫ t) h₃).trans
    ((Category.assoc _ _ _).trans (congrArg (CategoryStruct.comp
      ((derivedPullback.{u, u + 1, u + 1} g).map
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (structureSheafRing Z'))).inv.app C)))
      (Category.assoc _ _ _))).symm

end Pullback

section Generic

open CategoryTheory.Functor

/-- **Naturality of a total morphism built from degreewise data.** Let `φ¹` and `φ²` be
degreewise maps `T(K'^i, L'^j) ⟶ B(K^i, L^j)` for two quadruples of complexes, and let `u, v, x,
y` be morphisms of complexes between them such that, in each bidegree, `T(u, v)` followed by `φ²`
is `φ¹` followed by `B(x, y)`. Then the induced square of total complexes commutes. -/
theorem _root_.CategoryTheory.Functor.mapBifunctorMap_comp_total_map_homMk
    {C₁ C₂ M D : Type*} [Category* C₁] [Category* C₂] [Category* M] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms M] [Preadditive D]
    (T : M ⥤ M ⥤ D) [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (B : C₁ × C₂ ⥤ D) [(curryObj B).PreservesZeroMorphisms]
    [∀ X, ((curryObj B).obj X).PreservesZeroMorphisms]
    {K'₁ K'₂ L'₁ L'₂ : CochainComplex M ℤ} {K₁ K₂ : CochainComplex C₁ ℤ}
    {L₁ L₂ : CochainComplex C₂ ℤ}
    [HomologicalComplex.HasMapBifunctor K'₁ L'₁ T (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K'₂ L'₂ T (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K₁ L₁ (curryObj B) (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K₂ L₂ (curryObj B) (ComplexShape.up ℤ)]
    (u : K'₁ ⟶ K'₂) (v : L'₁ ⟶ L'₂) (x : K₁ ⟶ K₂) (y : L₁ ⟶ L₂)
    (φ₁ : ∀ i j, (T.obj (K'₁.X i)).obj (L'₁.X j) ⟶ B.obj (K₁.X i, L₁.X j))
    (h₁₁ : ∀ i j, (T.map (K'₁.d i (i + 1))).app (L'₁.X j) ≫ φ₁ (i + 1) j =
      φ₁ i j ≫ B.map (X := (K₁.X i, L₁.X j)) (Y := (K₁.X (i + 1), L₁.X j))
        (K₁.d i (i + 1), 𝟙 (L₁.X j)))
    (h₁₂ : ∀ i j, (T.obj (K'₁.X i)).map (L'₁.d j (j + 1)) ≫ φ₁ i (j + 1) =
      φ₁ i j ≫ B.map (X := (K₁.X i, L₁.X j)) (Y := (K₁.X i, L₁.X (j + 1)))
        (𝟙 (K₁.X i), L₁.d j (j + 1)))
    (φ₂ : ∀ i j, (T.obj (K'₂.X i)).obj (L'₂.X j) ⟶ B.obj (K₂.X i, L₂.X j))
    (h₂₁ : ∀ i j, (T.map (K'₂.d i (i + 1))).app (L'₂.X j) ≫ φ₂ (i + 1) j =
      φ₂ i j ≫ B.map (X := (K₂.X i, L₂.X j)) (Y := (K₂.X (i + 1), L₂.X j))
        (K₂.d i (i + 1), 𝟙 (L₂.X j)))
    (h₂₂ : ∀ i j, (T.obj (K'₂.X i)).map (L'₂.d j (j + 1)) ≫ φ₂ i (j + 1) =
      φ₂ i j ≫ B.map (X := (K₂.X i, L₂.X j)) (Y := (K₂.X i, L₂.X (j + 1)))
        (𝟙 (K₂.X i), L₂.d j (j + 1)))
    (hnat : ∀ i j, (T.map (u.f i)).app (L'₁.X j) ≫ (T.obj (K'₂.X i)).map (v.f j) ≫ φ₂ i j =
      φ₁ i j ≫ B.map (X := (K₁.X i, L₁.X j)) (Y := (K₂.X i, L₂.X j)) (x.f i, y.f j)) :
    HomologicalComplex.mapBifunctorMap u v T (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (mapBifunctorHomologicalComplexHomMk T B K'₂ L'₂ K₂ L₂ φ₂ h₂₁ h₂₂) (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
          (mapBifunctorHomologicalComplexHomMk T B K'₁ L'₁ K₁ L₁ φ₁ h₁₁ h₁₂) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap x y (curryObj B) (ComplexShape.up ℤ) := by
  dsimp only [HomologicalComplex.mapBifunctorMap]
  rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
  congr 1
  ext i j
  simp only [HomologicalComplex.comp_f, mapBifunctorHomologicalComplexHomMk_f_f,
    Category.assoc]
  refine (hnat i j).trans ?_
  congr 1
  simp only [Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f]
  change _ = B.map (X := (K₁.X i, L₁.X j)) (Y := (K₂.X i, L₁.X j)) (x.f i, 𝟙 _) ≫
    B.map (X := (K₂.X i, L₁.X j)) (Y := (K₂.X i, L₂.X j)) (𝟙 _, y.f j)
  rw [← B.map_comp]
  congr 1
  simp

/-- The case of `mapBifunctorMap_comp_total_map_homMk` in which only the first complex moves. -/
theorem _root_.CategoryTheory.Functor.mapBifunctorMap_comp_total_map_homMk_left
    {C₁ C₂ M D : Type*} [Category* C₁] [Category* C₂] [Category* M] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms M] [Preadditive D]
    (T : M ⥤ M ⥤ D) [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (B : C₁ × C₂ ⥤ D) [(curryObj B).PreservesZeroMorphisms]
    [∀ X, ((curryObj B).obj X).PreservesZeroMorphisms]
    {K'₁ K'₂ L' : CochainComplex M ℤ} {K₁ K₂ : CochainComplex C₁ ℤ} {L : CochainComplex C₂ ℤ}
    [HomologicalComplex.HasMapBifunctor K'₁ L' T (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K'₂ L' T (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K₁ L (curryObj B) (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K₂ L (curryObj B) (ComplexShape.up ℤ)]
    (u : K'₁ ⟶ K'₂) (x : K₁ ⟶ K₂)
    (φ₁ : ∀ i j, (T.obj (K'₁.X i)).obj (L'.X j) ⟶ B.obj (K₁.X i, L.X j))
    (h₁₁ : ∀ i j, (T.map (K'₁.d i (i + 1))).app (L'.X j) ≫ φ₁ (i + 1) j =
      φ₁ i j ≫ B.map (X := (K₁.X i, L.X j)) (Y := (K₁.X (i + 1), L.X j))
        (K₁.d i (i + 1), 𝟙 (L.X j)))
    (h₁₂ : ∀ i j, (T.obj (K'₁.X i)).map (L'.d j (j + 1)) ≫ φ₁ i (j + 1) =
      φ₁ i j ≫ B.map (X := (K₁.X i, L.X j)) (Y := (K₁.X i, L.X (j + 1)))
        (𝟙 (K₁.X i), L.d j (j + 1)))
    (φ₂ : ∀ i j, (T.obj (K'₂.X i)).obj (L'.X j) ⟶ B.obj (K₂.X i, L.X j))
    (h₂₁ : ∀ i j, (T.map (K'₂.d i (i + 1))).app (L'.X j) ≫ φ₂ (i + 1) j =
      φ₂ i j ≫ B.map (X := (K₂.X i, L.X j)) (Y := (K₂.X (i + 1), L.X j))
        (K₂.d i (i + 1), 𝟙 (L.X j)))
    (h₂₂ : ∀ i j, (T.obj (K'₂.X i)).map (L'.d j (j + 1)) ≫ φ₂ i (j + 1) =
      φ₂ i j ≫ B.map (X := (K₂.X i, L.X j)) (Y := (K₂.X i, L.X (j + 1)))
        (𝟙 (K₂.X i), L.d j (j + 1)))
    (hnat : ∀ i j, (T.map (u.f i)).app (L'.X j) ≫ φ₂ i j =
      φ₁ i j ≫ B.map (X := (K₁.X i, L.X j)) (Y := (K₂.X i, L.X j)) (x.f i, 𝟙 (L.X j))) :
    HomologicalComplex.mapBifunctorMap u (𝟙 L') T (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (mapBifunctorHomologicalComplexHomMk T B K'₂ L' K₂ L φ₂ h₂₁ h₂₂) (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
          (mapBifunctorHomologicalComplexHomMk T B K'₁ L' K₁ L φ₁ h₁₁ h₁₂) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap x (𝟙 L) (curryObj B) (ComplexShape.up ℤ) :=
  mapBifunctorMap_comp_total_map_homMk T B u (𝟙 L') x (𝟙 L) φ₁ h₁₁ h₁₂ φ₂ h₂₁ h₂₂
    (fun i j => by simpa using hnat i j)

/-- The case of `mapBifunctorMap_comp_total_map_homMk` in which only the second complex moves. -/
theorem _root_.CategoryTheory.Functor.mapBifunctorMap_comp_total_map_homMk_right
    {C₁ C₂ M D : Type*} [Category* C₁] [Category* C₂] [Category* M] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms M] [Preadditive D]
    (T : M ⥤ M ⥤ D) [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (B : C₁ × C₂ ⥤ D) [(curryObj B).PreservesZeroMorphisms]
    [∀ X, ((curryObj B).obj X).PreservesZeroMorphisms]
    {K' L'₁ L'₂ : CochainComplex M ℤ} {K : CochainComplex C₁ ℤ} {L₁ L₂ : CochainComplex C₂ ℤ}
    [HomologicalComplex.HasMapBifunctor K' L'₁ T (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' L'₂ T (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K L₁ (curryObj B) (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K L₂ (curryObj B) (ComplexShape.up ℤ)]
    (v : L'₁ ⟶ L'₂) (y : L₁ ⟶ L₂)
    (φ₁ : ∀ i j, (T.obj (K'.X i)).obj (L'₁.X j) ⟶ B.obj (K.X i, L₁.X j))
    (h₁₁ : ∀ i j, (T.map (K'.d i (i + 1))).app (L'₁.X j) ≫ φ₁ (i + 1) j =
      φ₁ i j ≫ B.map (X := (K.X i, L₁.X j)) (Y := (K.X (i + 1), L₁.X j))
        (K.d i (i + 1), 𝟙 (L₁.X j)))
    (h₁₂ : ∀ i j, (T.obj (K'.X i)).map (L'₁.d j (j + 1)) ≫ φ₁ i (j + 1) =
      φ₁ i j ≫ B.map (X := (K.X i, L₁.X j)) (Y := (K.X i, L₁.X (j + 1)))
        (𝟙 (K.X i), L₁.d j (j + 1)))
    (φ₂ : ∀ i j, (T.obj (K'.X i)).obj (L'₂.X j) ⟶ B.obj (K.X i, L₂.X j))
    (h₂₁ : ∀ i j, (T.map (K'.d i (i + 1))).app (L'₂.X j) ≫ φ₂ (i + 1) j =
      φ₂ i j ≫ B.map (X := (K.X i, L₂.X j)) (Y := (K.X (i + 1), L₂.X j))
        (K.d i (i + 1), 𝟙 (L₂.X j)))
    (h₂₂ : ∀ i j, (T.obj (K'.X i)).map (L'₂.d j (j + 1)) ≫ φ₂ i (j + 1) =
      φ₂ i j ≫ B.map (X := (K.X i, L₂.X j)) (Y := (K.X i, L₂.X (j + 1)))
        (𝟙 (K.X i), L₂.d j (j + 1)))
    (hnat : ∀ i j, (T.obj (K'.X i)).map (v.f j) ≫ φ₂ i j =
      φ₁ i j ≫ B.map (X := (K.X i, L₁.X j)) (Y := (K.X i, L₂.X j)) (𝟙 (K.X i), y.f j)) :
    HomologicalComplex.mapBifunctorMap (𝟙 K') v T (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (mapBifunctorHomologicalComplexHomMk T B K' L'₂ K L₂ φ₂ h₂₁ h₂₂) (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
          (mapBifunctorHomologicalComplexHomMk T B K' L'₁ K L₁ φ₁ h₁₁ h₁₂) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K) y (curryObj B) (ComplexShape.up ℤ) :=
  mapBifunctorMap_comp_total_map_homMk T B (𝟙 K') v (𝟙 K) y φ₁ h₁₁ h₁₂ φ₂ h₂₁ h₂₂
    (fun i j => by simpa using hnat i j)

/-- **A four-step composite through a bifunctor is natural**, over variables: if each of its
four factors commutes with the given maps, so does the composite. This is the shape of steps
(4) and (5) of [Stacks, Tag 0G4A] as a function of the first complex. -/
theorem _root_.CategoryTheory.Functor.bifunctor_comp_four_naturality_left
    {D E : Type*} [Category* D] [Category* E] (T : D ⥤ D ⥤ D) (G : E ⥤ D)
    {A₁ A₂ X X' Y Y' : D} {Z₁ Z₂ W₁ W₂ : E}
    (α : A₁ ⟶ A₂) (a₁ : A₁ ⟶ X) (a₂ : A₂ ⟶ X') (ξ : X ⟶ X') (b : Y ⟶ Y')
    (c₁ : (T.obj X).obj Y' ⟶ G.obj Z₁) (c₂ : (T.obj X').obj Y' ⟶ G.obj Z₂) (ζ : Z₁ ⟶ Z₂)
    (e₁ : Z₁ ⟶ W₁) (e₂ : Z₂ ⟶ W₂) (ω : W₁ ⟶ W₂)
    (hp : α ≫ a₂ = a₁ ≫ ξ) (ht : (T.map ξ).app Y' ≫ c₂ = c₁ ≫ G.map ζ)
    (hc : ζ ≫ e₂ = e₁ ≫ ω) :
    (T.map α).app Y ≫ ((T.map a₂).app Y ≫ (T.obj X').map b ≫ c₂ ≫ G.map e₂) =
      ((T.map a₁).app Y ≫ (T.obj X).map b ≫ c₁ ≫ G.map e₁) ≫ G.map ω := by
  rw [← NatTrans.comp_app_assoc, ← T.map_comp, hp, T.map_comp, NatTrans.comp_app_assoc,
    ← NatTrans.naturality_assoc, reassoc_of% ht, ← G.map_comp, hc, G.map_comp]
  simp only [Category.assoc]

/-- The same as a function of the second complex. -/
theorem _root_.CategoryTheory.Functor.bifunctor_comp_four_naturality_right
    {D E : Type*} [Category* D] [Category* E] (T : D ⥤ D ⥤ D) (G : E ⥤ D)
    {A X Y₁ Y₂ Y₁' Y₂' : D} {Z₁ Z₂ W₁ W₂ : E}
    (a : A ⟶ X) (β : Y₁ ⟶ Y₂) (b₁ : Y₁ ⟶ Y₁') (b₂ : Y₂ ⟶ Y₂') (η : Y₁' ⟶ Y₂')
    (c₁ : (T.obj X).obj Y₁' ⟶ G.obj Z₁) (c₂ : (T.obj X).obj Y₂' ⟶ G.obj Z₂) (ζ : Z₁ ⟶ Z₂)
    (e₁ : Z₁ ⟶ W₁) (e₂ : Z₂ ⟶ W₂) (ω : W₁ ⟶ W₂)
    (hp : β ≫ b₂ = b₁ ≫ η) (ht : (T.obj X).map η ≫ c₂ = c₁ ≫ G.map ζ)
    (hc : ζ ≫ e₂ = e₁ ≫ ω) :
    (T.obj A).map β ≫ ((T.map a).app Y₂ ≫ (T.obj X).map b₂ ≫ c₂ ≫ G.map e₂) =
      ((T.map a).app Y₁ ≫ (T.obj X).map b₁ ≫ c₁ ≫ G.map e₁) ≫ G.map ω := by
  rw [NatTrans.naturality_assoc, ← Functor.map_comp_assoc, hp, Functor.map_comp_assoc,
    reassoc_of% ht, ← G.map_comp, hc, G.map_comp]
  simp only [Category.assoc]

/-- **A composite with the image of a natural map under a functor is natural**, over variables:
`x ≫ k' = k ≫ R(y)` and `y ≫ b' = b ≫ z` give `x ≫ (k' ≫ R(b')) = (k ≫ R(b)) ≫ R(z)`. -/
theorem _root_.CategoryTheory.Functor.comp_map_naturality {C D : Type*} [Category* C]
    [Category* D] (R : C ⥤ D) {A A' : D} {B B' Z Z' : C} (x : A ⟶ A') (k : A ⟶ R.obj B)
    (k' : A' ⟶ R.obj B') (y : B ⟶ B') (b : B ⟶ Z) (b' : B' ⟶ Z') (z : Z ⟶ Z')
    (hk : x ≫ k' = k ≫ R.map y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (k' ≫ R.map b') = (k ≫ R.map b) ≫ R.map z := by
  rw [reassoc_of% hk, ← R.map_comp, hb, R.map_comp, Category.assoc]

end Generic

section Complexes

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- `p^{-1}` of a morphism of complexes of differential operators on `X/S`, as a morphism of the
complexes of `f^{-1}𝒪_S`-modules on `X ×_S Y`. -/
abbrev leftInverseImageMap {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ}
    (φ : K ⟶ K') : leftInverseImageComplex a b K ⟶ leftInverseImageComplex a b K' :=
  ((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)

/-- `q^{-1}` of a morphism of complexes of differential operators on `Y/S`. -/
abbrev rightInverseImageMap {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ}
    (φ : L ⟶ L') : rightInverseImageComplex a b L ⟶ rightInverseImageComplex a b L' :=
  ((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)

/-- The degreewise comparison `p^{-1}𝓕^i ⊗ q^{-1}𝓖^j ⟶ 𝓕^i ⊠ 𝓖^j` is natural in a morphism of
complexes `𝓕^• ⟶ 𝓕'^•`, at the spelling of the inverse image of a morphism of complexes. -/
theorem relativeBoxComparison_naturality_leftInverseImageMap
    {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ} (φ : K ⟶ K')
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (i j : ℤ) :
    ((inverseImageSheafTensor a b).map ((leftInverseImageMap a b φ).f i)).app
        ((rightInverseImageComplex a b L).X j) ≫ relativeBoxComparison a b (K'.X i) (L.X j) =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        (boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K'.X i, L.X j))
          (φ.f i, 𝟙 (L.X j)) :=
  relativeBoxComparison_naturality_fst a b (φ.f i) (L.X j)

/-- Step (5) is the total map of the morphism of double complexes given by the degreewise
comparisons. -/
theorem boxTotalComplexComparison_eq_total_map
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    boxTotalComplexComparison a b K L = HomologicalComplex₂.total.map
      (Functor.mapBifunctorHomologicalComplexHomMk (inverseImageSheafTensor a b)
        (boxProductRelative a b) (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
        K L (fun i j => relativeBoxComparison a b (K.X i) (L.X j))
        (relativeBoxComparison_naturality_d_fst a b K L)
        (relativeBoxComparison_naturality_d_snd a b K L)) (ComplexShape.up ℤ) :=
  rfl

/-- **Step (5) of [Stacks, Tag 0G4A] is natural in the first complex.** -/
theorem boxTotalComplexComparison_naturality_left
    {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ} (φ : K ⟶ K')
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    HomologicalComplex.mapBifunctorMap (leftInverseImageMap a b φ)
        (𝟙 (rightInverseImageComplex a b L)) (inverseImageSheafTensor a b) (ComplexShape.up ℤ) ≫
        boxTotalComplexComparison a b K' L =
      boxTotalComplexComparison a b K L ≫
        HomologicalComplex.mapBifunctorMap φ (𝟙 L) (boxProductRelativeCurried a b)
          (ComplexShape.up ℤ) := by
  rw [boxTotalComplexComparison_eq_total_map, boxTotalComplexComparison_eq_total_map]
  apply Functor.mapBifunctorMap_comp_total_map_homMk_left
  exact relativeBoxComparison_naturality_leftInverseImageMap a b φ L

/-- The degreewise comparison is natural in a morphism of complexes `𝓖^• ⟶ 𝓖'^•`. -/
theorem relativeBoxComparison_naturality_rightInverseImageMap
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (φ : L ⟶ L') (i j : ℤ) :
    ((inverseImageSheafTensor a b).obj ((leftInverseImageComplex a b K).X i)).map
        ((rightInverseImageMap a b φ).f j) ≫ relativeBoxComparison a b (K.X i) (L'.X j) =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        (boxProductRelative a b).map (X := (K.X i, L.X j)) (Y := (K.X i, L'.X j))
          (𝟙 (K.X i), φ.f j) :=
  relativeBoxComparison_naturality_snd a b (K.X i) (φ.f j)

/-- **Step (5) of [Stacks, Tag 0G4A] is natural in the second complex.** -/
theorem boxTotalComplexComparison_naturality_right
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (φ : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap (𝟙 (leftInverseImageComplex a b K))
        (rightInverseImageMap a b φ) (inverseImageSheafTensor a b) (ComplexShape.up ℤ) ≫
        boxTotalComplexComparison a b K L' =
      boxTotalComplexComparison a b K L ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K) φ (boxProductRelativeCurried a b)
          (ComplexShape.up ℤ) := by
  rw [boxTotalComplexComparison_eq_total_map, boxTotalComplexComparison_eq_total_map]
  apply Functor.mapBifunctorMap_comp_total_map_homMk_right
  exact relativeBoxComparison_naturality_rightInverseImageMap a b K φ

/-- **Steps (4) and (5) of [Stacks, Tag 0G4A] are natural in the second complex.** -/
theorem boxTotalComplexDerivedComparison_naturality_right
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (φ : L ⟶ L') :
    ((derivedTensorProductFunctor.{u, u + 1}
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          ((derivedPullback.{u, u + 1, u + 1} (fstProjection a b)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).map
        ((derivedPullback.{u, u + 1, u + 1} (sndProjection a b)).map
          (DerivedCategory.Q.map
            (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))) ≫
        boxTotalComplexDerivedComparison a b K L' =
      boxTotalComplexDerivedComparison a b K L ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) φ
          (boxProductRelativeCurried a b) (ComplexShape.up ℤ)) :=
  Functor.bifunctor_comp_four_naturality_right _ DerivedCategory.Q _ _ _ _ _ _ _ _ _ _ _
    (pullbackComplexComparison_naturality (sndProjection a b)
      (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))
    ((canonicalDerivedTensorProduct
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality_right
        (leftInverseImageComplex a b K) (rightInverseImageMap a b φ))
    (boxTotalComplexComparison_naturality_right a b K φ)

end Complexes

/-! ### The relative Künneth map for unbounded complexes -/

section Unbounded

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The relative cup product of [Stacks, Tag 0G4B]**

`Ra_*(𝓕^•) ⊗^𝐋_{𝒪_S} Rb_*(𝓖^•) ⟶ Rf_*(Tot(𝓕^• ⊠ 𝓖^•))`

in `D(𝒪_S)`, for `𝓕^•` on `X/S` and `𝓖^•` on `Y/S` arbitrary `ℤ`-indexed complexes of
quasi-coherent modules whose differentials are differential operators of finite order, with no
boundedness condition, and `f` the structure morphism of `X ×_S Y`. The total complex is the
direct-sum totalization of the double complex `𝓕^i ⊠ 𝓖^j`, whose maps are `f^{-1}𝒪_S`-linear, so
it is formed over `f^{-1}𝒪_S`. The map is the composite of the five maps of the source: the
Künneth map of [Stacks, Tag 0FLP] for the inverse-image ringed spaces, which is the two pullback
maps and the relative cup product of [Stacks, Remark 0B68], followed by `Rf_*` of steps (4)
and (5), `boxTotalComplexDerivedComparison`. -/
@[stacks 0G4B "the map, for arbitrary complexes `F^•`, `G^•` as in the source: the composite of \
the five maps of the source, steps (1) to (3) being the Künneth map of Tag 0FLP for the \
inverse-image ringed spaces (the pullbacks `Lp^*`, which computes `p^{-1}` along \
`(X ×_S Y, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)`), steps (4) and (5) being \
`boxTotalComplexDerivedComparison`; `Tot(F^• ⊠ G^•)` is the direct-sum total complex, formed over \
`f^{-1}𝒪_S`"]
def relativeBoxKunnethMapUnbounded
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      (derivedPushforward.{u, u + 1, u + 1}
          (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K L
          (boxProductRelativeCurried a b) (ComplexShape.up ℤ))) :=
  Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a))
      (fstProjection_comp a b) (sndProjection_comp a b)
      (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (boxTotalComplexDerivedComparison a b K L)

/-- **The unbounded relative Künneth map is natural in the first complex.** -/
theorem relativeBoxKunnethMapUnbounded_natural_left
    {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ} (φ : K ⟶ K')
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).map
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).map
            (DerivedCategory.Q.map
              (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)))).app
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ≫
        relativeBoxKunnethMapUnbounded a b K' L =
      relativeBoxKunnethMapUnbounded a b K L ≫
        (derivedPushforward.{u, u + 1, u + 1}
            (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
            (boxProductRelativeCurried a b) (ComplexShape.up ℤ))) :=
  Functor.comp_map_naturality _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left _ _ _ _ _
      (fstProjection_comp a b) (sndProjection_comp a b) _ _)
    (Stacks.Cohomology.BoxKunnethFlat.boxTotalComplexDerivedComparison_naturality_left a b φ L)

/-- **The unbounded relative Künneth map is natural in the second complex.** -/
theorem relativeBoxKunnethMapUnbounded_natural_right
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (φ : L ⟶ L') :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).map
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).map
          (DerivedCategory.Q.map
            (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))) ≫
        relativeBoxKunnethMapUnbounded a b K L' =
      relativeBoxKunnethMapUnbounded a b K L ≫
        (derivedPushforward.{u, u + 1, u + 1}
            (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) φ
            (boxProductRelativeCurried a b) (ComplexShape.up ℤ))) :=
  Functor.comp_map_naturality _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right _ _ _ _ _
      (fstProjection_comp a b) (sndProjection_comp a b) _ _)
    (boxTotalComplexDerivedComparison_naturality_right a b K φ)

end Unbounded

end Stacks.Cohomology.BoxKunneth

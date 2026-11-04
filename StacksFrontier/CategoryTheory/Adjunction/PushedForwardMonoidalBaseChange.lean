module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import StacksFrontier.CategoryTheory.Adjunction.PushedForwardTwistedBaseChange
public import StacksFrontier.CategoryTheory.Monoidal.FunctorTensorIso
import StacksFrontier.CategoryTheory.Adjunction.CounitHomExt

/-!
# The pushed-forward base change maps for monoidal functors

The constructions of `StacksFrontier/CategoryTheory/Adjunction/PushedForwardBaseChange.lean` and
`StacksFrontier/CategoryTheory/Adjunction/PushedForwardTwistedBaseChange.lean` take bifunctors on the
four corners of a square with comparisons along the four functors. Here the bifunctors are
tensor products, read through the swapped bifunctors `(N, P) ↦ T(P, N)` for bifunctors `T`
identified with `curriedTensor`, and the comparisons are the tensorators of monoidal functors,
`Functor.Monoidal.swapTensorIso`. Then the compatibility of the comparisons around the square
holds as soon as the identifications of the composites are monoidal, the unit compatibility is the
unitality of the tensorator, and the projection-formula map at the unit `Rg 𝟙 ⊗ M ⟶ Rg(Lg M)` is
invertible when the projection formula is and `Lg` is compatible with braidings.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.swapLeftUnitor` — the left unitor `T(𝟙, N) ⟶ N`.

## Main results

* `Stacks.CategoryTheory.BaseChange.tensorComparisonCompatible_swapTensorIso` — the four
  tensorators are compatible around a square with monoidal identifications.
* `Stacks.CategoryTheory.BaseChange.swapTensorIso_comp_map_swapLeftUnitor` — unit compatibility.
* `Stacks.CategoryTheory.BaseChange.isIso_unitProjection_of_isIso` — the projection-formula map at
  the unit is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

section Unitor

variable {C : Type*} [Category C] [MonoidalCategory C] {TC : C ⥤ C ⥤ C}
  (eC : TC ≅ curriedTensor C)

/-- **The left unitor** `T(𝟙, N) ⟶ N` of a bifunctor `T` identified with `curriedTensor`, read on
the swapped bifunctor `(N, P) ↦ T(P, N)` at `P = 𝟙`. -/
def swapLeftUnitor :
    Functor.prod' (𝟭 C) ((Functor.const C).obj (𝟙_ C)) ⋙
        (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC) ⟶ 𝟭 C where
  app N := (eC.hom.app (𝟙_ C)).app N ≫ (λ_ N).hom
  naturality N N' h := by
    have h₁ := (eC.hom.app (𝟙_ C)).naturality h
    change ((TC.map (𝟙 (𝟙_ C))).app N ≫ (TC.obj (𝟙_ C)).map h) ≫
        (eC.hom.app (𝟙_ C)).app N' ≫ (λ_ N').hom = ((eC.hom.app (𝟙_ C)).app N ≫ (λ_ N).hom) ≫ h
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, reassoc_of% h₁]
    change (eC.hom.app (𝟙_ C)).app N ≫ 𝟙_ C ◁ h ≫ (λ_ N').hom = _
    rw [leftUnitor_naturality, Category.assoc]

/-- The component of `swapLeftUnitor eC` at `N` is the identification `T(𝟙, N) ⟶ 𝟙 ⊗ N` followed
by the left unitor of `C`. -/
theorem swapLeftUnitor_app (N : C) :
    (swapLeftUnitor eC).app N = (eC.hom.app (𝟙_ C)).app N ≫ (λ_ N).hom :=
  rfl

end Unitor

section Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D} (eC : TC ≅ curriedTensor C) (eD : TD ≅ curriedTensor D)
  (F : C ⥤ D) [F.Monoidal]

omit [MonoidalCategory C] in
/-- The swapped bifunctor of `T` acts on a pair of morphisms through the two variables of `T`. -/
theorem swap_uncurry_map {P P' Q Q' : C} (p : P ⟶ P') (q : Q ⟶ Q') :
    (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC).map (p ×ₘ q) =
      (TC.map q).app P ≫ (TC.obj Q').map p :=
  rfl

/-- The swapped bifunctor of `T`, followed by the identification with the tensor product. -/
theorem swap_uncurry_map_comp_hom {P P' Q Q' : C} (p : P ⟶ P') (q : Q ⟶ Q') :
    (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC).map (p ×ₘ q) ≫ (eC.hom.app Q').app P' =
      (eC.hom.app Q).app P ≫ (q ⊗ₘ p) := by
  rw [swap_uncurry_map, Category.assoc, (eC.hom.app Q').naturality p,
    ← NatTrans.comp_app_assoc, eC.hom.naturality q]
  change ((eC.hom.app Q).app P ≫ q ▷ P) ≫ Q' ◁ p = _
  rw [Category.assoc, ← tensorHom_def]

/-- The inverse identification with the tensor product, followed by the swapped bifunctor. -/
theorem inv_comp_swap_uncurry_map {P P' Q Q' : C} (p : P ⟶ P') (q : Q ⟶ Q') :
    (eC.inv.app Q).app P ≫ (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC).map (p ×ₘ q) =
      (q ⊗ₘ p) ≫ (eC.inv.app Q').app P' := by
  rw [← cancel_mono ((eC.hom.app Q').app P'), Category.assoc, swap_uncurry_map_comp_hom,
    Category.assoc, Iso.inv_hom_id_app_app_assoc, Iso.inv_hom_id_app_app]
  exact (Category.comp_id _).symm

/-- **Unit compatibility of the tensorator.** The tensorator of `F` at `(X, 𝟙)`, followed by the
counit `η : F 𝟙 ⟶ 𝟙` in the second variable and the left unitor, is `F` of the left unitor. -/
theorem swapTensorIso_comp_map_swapLeftUnitor (X : C) :
    (Functor.Monoidal.swapTensorIso F eC eD).hom.app (X, 𝟙_ C) ≫
        (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD).map (𝟙 (F.obj X) ×ₘ η F) ≫
          (swapLeftUnitor eD).app (F.obj X) =
      F.map ((swapLeftUnitor eC).app X) := by
  rw [Functor.Monoidal.swapTensorIso_hom_app, swapLeftUnitor_app, swapLeftUnitor_app,
    Category.assoc, Category.assoc, ← Category.assoc ((CategoryTheory.Prod.swap D D ⋙ _).map _),
    swap_uncurry_map_comp_hom]
  dsimp only
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_app_assoc, tensorHom_id, left_unitality_hom, F.map_comp]

end Functor

section Square

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  [MonoidalCategory S] [MonoidalCategory T] [MonoidalCategory S'] [MonoidalCategory T']
  {TS : S ⥤ S ⥤ S} {TT : T ⥤ T ⥤ T} {TS' : S' ⥤ S' ⥤ S'} {TT' : T' ⥤ T' ⥤ T'}
  (eS : TS ≅ curriedTensor S) (eT : TT ≅ curriedTensor T) (eS' : TS' ≅ curriedTensor S')
  (eT' : TT' ≅ curriedTensor T')
  {Lf : S ⥤ T} {Lf' : S' ⥤ T'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  [Lf.Monoidal] [Lf'.Monoidal] [Lg.Monoidal] [Lg'.Monoidal] [Lc.Monoidal]
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) [NatTrans.IsMonoidal eg.hom]
  [NatTrans.IsMonoidal ef.hom]

/-- A monoidal natural transformation between monoidal functors commutes with the tensorators. -/
theorem app_tensor_comp_δ {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G)
    [NatTrans.IsMonoidal τ] (X Y : C) :
    τ.app (X ⊗ Y) ≫ δ G X Y = δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) := by
  rw [← cancel_epi (Functor.LaxMonoidal.μ F X Y), Functor.Monoidal.μ_δ_assoc,
    NatTrans.IsMonoidal.tensor_assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- **The four tensorators are compatible around a square** whose two composites are identified
by monoidal natural isomorphisms. -/
theorem tensorComparisonCompatible_swapTensorIso (M N : S) :
    TensorComparisonCompatible eg ef (CategoryTheory.Prod.swap S S ⋙ Functor.uncurry.obj TS)
      (CategoryTheory.Prod.swap S' S' ⋙ Functor.uncurry.obj TS')
      (CategoryTheory.Prod.swap T T ⋙ Functor.uncurry.obj TT)
      (CategoryTheory.Prod.swap T' T' ⋙ Functor.uncurry.obj TT')
      (Functor.Monoidal.swapTensorIso Lf eS eT).hom
      (Functor.Monoidal.swapTensorIso Lf' eS' eT').hom
      (Functor.Monoidal.swapTensorIso Lg eS eS').hom
      (Functor.Monoidal.swapTensorIso Lg' eT eT').hom M N := by
  have hsq : (squareCompositeIso eg ef).hom = eg.hom ≫ ef.inv := rfl
  have hδ : (squareCompositeIso eg ef).hom.app (N ⊗ M) ≫ Lg'.map (δ Lf N M) ≫
      δ Lg' (Lf.obj N) (Lf.obj M) =
      Lf'.map (δ Lg N M) ≫ δ Lf' (Lg.obj N) (Lg.obj M) ≫
        ((squareCompositeIso eg ef).hom.app N ⊗ₘ (squareCompositeIso eg ef).hom.app M) := by
    have h₁ := app_tensor_comp_δ eg.hom N M
    have h₂ := app_tensor_comp_δ ef.inv N M
    simp only [Functor.OplaxMonoidal.comp_δ] at h₁ h₂
    rw [hsq, NatTrans.comp_app, Category.assoc, h₂, reassoc_of% h₁, NatTrans.comp_app,
      NatTrans.comp_app, tensorHom_comp_tensorHom]
  rw [TensorComparisonCompatible]
  simp only [Functor.Monoidal.swapTensorIso_hom_app, Functor.map_comp, Category.assoc]
  rw [inv_comp_swap_uncurry_map, ← Functor.map_comp_assoc Lf' ((eS'.inv.app _).app _),
    ← NatTrans.comp_app, Iso.inv_hom_id_app, NatTrans.id_app, Lf'.map_id, Category.id_comp,
    ← Functor.map_comp_assoc Lg' ((eT.inv.app _).app _), ← NatTrans.comp_app,
    Iso.inv_hom_id_app, NatTrans.id_app, Lg'.map_id, Category.id_comp,
    ← reassoc_of% hδ]
  have hn : Lf'.map (Lg.map ((eS.hom.app N).app M)) ≫
      (squareCompositeIso eg ef).hom.app (N ⊗ M) =
      (squareCompositeIso eg ef).hom.app ((TS.obj N).obj M) ≫
        Lg'.map (Lf.map ((eS.hom.app N).app M)) :=
    (squareCompositeIso eg ef).hom.naturality ((eS.hom.app N).app M)
  rw [reassoc_of% hn]
  rfl

end Square

section Projection

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D]
  {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D} (eC : TC ≅ curriedTensor C) (eD : TD ≅ curriedTensor D)
  {F : C ⥤ D} {G : D ⥤ C} [F.Monoidal] (adj : F ⊣ G)
  (hbr : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
include hbr

/-- The braiding of `C`, read on a bifunctor identified with `curriedTensor`. -/
abbrev swapBraiding (M N : C) : (TC.obj M).obj N ⟶ (TC.obj N).obj M :=
  (eC.hom.app M).app N ≫ (β_ M N).hom ≫ (eC.inv.app N).app M

/-- The braiding `T(M, N) ⟶ T(N, M)` is an isomorphism. -/
instance (M N : C) : IsIso (swapBraiding eC M N) := by
  unfold swapBraiding
  infer_instance

/-- **The projection-formula map at the unit in the other variable.** Composed with the braiding,
the map `Φ_M : G 𝟙 ⊗ M ⟶ G(F M)` of `unitProjection` is the projection-formula map of `F ⊣ G`
at `(𝟙, M)` followed by the right unitor. -/
theorem swapBraiding_comp_unitProjection (M : C) :
    swapBraiding eC M (G.obj (𝟙_ D)) ≫
        unitProjection adj (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD)
          (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
          (Functor.Monoidal.swapTensorIso F eC eD).hom (𝟙_ D) (swapLeftUnitor eD) M =
      adjunctionTensorMap adj (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
          (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD)
          (Functor.Monoidal.swapTensorIso F eC eD).hom (𝟙_ D) M ≫
        G.map ((eD.hom.app (F.obj M)).app (𝟙_ D) ≫ (ρ_ (F.obj M)).hom) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj
  have hΦ : F.map (unitProjection adj (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD)
      (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
      (Functor.Monoidal.swapTensorIso F eC eD).hom (𝟙_ D) (swapLeftUnitor eD) M) ≫
        adj.counit.app (F.obj M) =
      (Functor.Monoidal.swapTensorIso F eC eD).hom.app (M, G.obj (𝟙_ D)) ≫
        (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD).map
          (𝟙 (F.obj M) ×ₘ adj.counit.app (𝟙_ D)) ≫ (swapLeftUnitor eD).app (F.obj M) :=
    (adj.homEquiv_counit _ _ _).symm.trans (homEquiv_symm_unitProjection adj _ _ _ _ _ M)
  have hP := map_adjunctionTensorMap_comp_counit adj (CategoryTheory.Prod.swap C C ⋙
    Functor.uncurry.obj TC) (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD)
    (Functor.Monoidal.swapTensorIso F eC eD).hom (𝟙_ D) M
  rw [F.map_comp, Category.assoc, hΦ]
  conv_rhs => rw [F.map_comp, Category.assoc, ← Functor.comp_map G F, adj.counit.naturality,
    Functor.id_map, ← Category.assoc, hP]
  simp only [Functor.Monoidal.swapTensorIso_hom_app, swapLeftUnitor_app, Functor.map_comp,
    Category.assoc, swapBraiding]
  have e₁ := swap_uncurry_map_comp_hom eD (𝟙 (F.obj M)) (adj.counit.app (𝟙_ D))
  have e₂ := swap_uncurry_map_comp_hom eD (adj.counit.app (𝟙_ D)) (𝟙 (F.obj M))
  simp only [Functor.id_obj, Functor.comp_obj] at e₁ e₂
  rw [← Category.assoc ((CategoryTheory.Prod.swap D D ⋙ _).map _), e₁,
    ← Category.assoc ((CategoryTheory.Prod.swap D D ⋙ _).map _), e₂]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_app_assoc, Iso.inv_hom_id_app_app_assoc,
    ← Functor.map_comp_assoc F ((eC.inv.app _).app _), Iso.inv_hom_id_app_app, F.map_id,
    Category.id_comp, reassoc_of% (hbr _ _), tensorHom_id, id_tensorHom,
    ← BraidedCategory.braiding_naturality_right_assoc, braiding_leftUnitor (C := D) (F.obj M)]

/-- **The projection-formula map at the unit `G 𝟙 ⊗ M ⟶ G(F M)` is invertible** when the
projection-formula map of `F ⊣ G` at `(𝟙, M)` is and `F` is compatible with the braidings. -/
theorem isIso_unitProjection_of_isIso (M : C)
    [IsIso (adjunctionTensorMap adj (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
      (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD)
      (Functor.Monoidal.swapTensorIso F eC eD).hom (𝟙_ D) M)] :
    IsIso (unitProjection adj (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD)
      (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
      (Functor.Monoidal.swapTensorIso F eC eD).hom (𝟙_ D) (swapLeftUnitor eD) M) := by
  have : IsIso (swapBraiding eC M (G.obj (𝟙_ D)) ≫
      unitProjection adj (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj TD)
        (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj TC)
        (Functor.Monoidal.swapTensorIso F eC eD).hom (𝟙_ D) (swapLeftUnitor eD) M) := by
    rw [swapBraiding_comp_unitProjection eC eD adj hbr M]
    infer_instance
  exact IsIso.of_isIso_comp_left (swapBraiding eC M (G.obj (𝟙_ D))) _

end Projection

end Stacks.CategoryTheory.BaseChange

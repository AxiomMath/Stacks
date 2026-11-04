module

public import StacksFrontier.CategoryTheory.KanExtension.ExtendExactness
public import StacksFrontier.CategoryTheory.KanExtension.ExtendMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.BraidedEquivalenceInverse

/-! # The extension of a braided monoidal functor from compact generators is braided monoidal

Let `P` be a monoidal property of objects of a monoidal category `C` cutting out a locally
`w`-small full subcategory of categorically compact objects such that every object of `C` is a
`w`-filtered colimit of `P`-objects, and let `D` be a monoidal category in which tensoring on
either side commutes with `w`-filtered colimits. The extension `G : C ⥤ D` of a right exact tensor
functor `F'` out of the `P`-objects (`CategoryTheory.ObjectProperty.existsUnique_tensorExtension`,
Stacks 0FWY) carries only the data of a functor of monoidal categories in the sense of
Stacks 0FFL, `CategoryTheory.Functor.TensorStructure`: a tensorator and its associativity, and the
property that `G(𝟙)` is a unit. When `F'` is a (braided) monoidal functor in the sense of Mathlib,
this file upgrades `G` to one: the unit morphism of `G` is that of `F'` transported along the
identification `e : G|_P ≅ F'`, and the unit laws, as well as the compatibility with the
braidings, hold everywhere because they hold on `P`-objects and both sides commute with filtered
colimits (`CategoryTheory.ObjectProperty.app_eq_of_preservesFilteredColimits` and
`CategoryTheory.ObjectProperty.tensor_app_eq_of_preservesFilteredColimits`). The identification
`e` is then a monoidal natural isomorphism.

This is the form in which the proof of Stacks 0GRR uses Stacks 0GRJ: a right exact tensor functor
`Coh(𝒪_𝒳) ⥤ Mod^{fg}_B` extends to a right exact (braided monoidal) tensor functor
`QCoh(𝒪_𝒳) ⥤ Mod_B` commuting with all colimits.

## Main definitions

* `CategoryTheory.ObjectProperty.coreMonoidalOfIsCompatible`: the monoidal structure on `G`.
* `CategoryTheory.ObjectProperty.braidedOfIsCompatible`: the braided monoidal structure on `G`.

## Main results

* `CategoryTheory.ObjectProperty.isMonoidal_of_isCompatible`: `e` is monoidal.
* `CategoryTheory.ObjectProperty.exists_braided_extension_of_equivalence`: a right exact braided
  monoidal functor out of a braided monoidal category equivalent to the `P`-objects extends to a
  right exact braided monoidal functor out of `C` commuting with all `w`-small colimits.

## References

* [Stacks Project, Tag 0FWY](https://stacks.math.columbia.edu/tag/0FWY)
* [Stacks Project, Tag 0FFL](https://stacks.math.columbia.edu/tag/0FFL)
* [Stacks Project, Tag 0GRJ](https://stacks.math.columbia.edu/tag/0GRJ)
* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits MonoidalCategory Functor.LaxMonoidal

universe w v v' v'' u u' u''

namespace CategoryTheory.ObjectProperty

section Upgrade

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (P : ObjectProperty C)
  [MonoidalCategory C] [MonoidalCategory D] [P.IsMonoidal]
  [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  (G : C ⥤ D) [PreservesFilteredColimitsOfSize.{w, w} G] (hG : G.TensorStructure)

section Monoidal

variable {F' : P.FullSubcategory ⥤ D} [F'.Monoidal] (e : P.ι ⋙ G ≅ F')
  (he : (hG.restrict P).IsCompatible (Functor.Monoidal.toTensorStructure F') e)

omit [LocallySmall.{w} P.FullSubcategory]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [PreservesFilteredColimitsOfSize.{w, w} G] in
include he in
/-- On two `P`-objects, a tensorator compatible with the one of a monoidal functor `F'` along
`e` is the tensorator of `F'` transported along `e`. -/
theorem μIso_hom_eq_of_isCompatible (X Y : P.FullSubcategory) :
    (hG.μIso X.obj Y.obj).hom = (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ F' X Y ≫ e.inv.app (X ⊗ Y) := by
  rw [← cancel_mono (e.hom.app (X ⊗ Y)), assoc, assoc, Iso.inv_hom_id_app, comp_id]
  exact he X Y

include hP hgen he in
/-- **The monoidal structure on the extension of a monoidal functor.** Let `G : C ⥤ D` commute
with filtered colimits and carry a structure `hG` of functor of monoidal categories (Stacks 0FFL)
compatible, along `e : G|_P ≅ F'`, with a monoidal functor `F'` out of the `P`-objects. Then `G`
is a monoidal functor with tensorator that of `hG` and unit morphism that of `F'` transported
along `e`. The unit laws hold on `P`-objects, where they are those of `F'`, hence everywhere. -/
def coreMonoidalOfIsCompatible : G.CoreMonoidal where
  εIso := Functor.Monoidal.εIso F' ≪≫ (e.app (𝟙_ P.FullSubcategory)).symm
  μIso := hG.μIso
  μIso_hom_natural_left f X' := hG.μIso_natural_left f X'
  μIso_hom_natural_right X' f := hG.μIso_natural_right X' f
  associativity X Y Z := by
    rw [← cancel_epi (α_ (G.obj X) (G.obj Y) (G.obj Z)).inv, Iso.inv_hom_id_assoc]
    have h := congrArg (· ≫ G.map (α_ X Y Z).hom) (hG.associativity X Y Z)
    simp only [assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, comp_id] at h
    exact h.symm
  left_unitality X := by
    refine app_eq_of_preservesFilteredColimits P hP hgen (G ⋙ tensorLeft (𝟙_ D)) G
      (fun X ↦ (λ_ (G.obj X)).hom)
      (fun X ↦ (Functor.Monoidal.εIso F' ≪≫ (e.app (𝟙_ P.FullSubcategory)).symm).hom ▷
        G.obj X ≫ (hG.μIso (𝟙_ C) X).hom ≫ G.map (λ_ X).hom)
      (fun f ↦ leftUnitor_naturality (G.map f)) (fun {X Y} f ↦ ?_) (fun X ↦ ?_) X
    · change _ ◁ G.map f ≫ _ = _
      have h : G.obj (𝟙_ C) ◁ G.map f ≫ (hG.μIso (𝟙_ C) Y).hom ≫ G.map (λ_ Y).hom =
          (hG.μIso (𝟙_ C) X).hom ≫ G.map (λ_ X).hom ≫ G.map f := by
        rw [hG.μIso_natural_right_assoc, ← G.map_comp, ← G.map_comp, leftUnitor_naturality]
      simp only [assoc]
      rw [whisker_exchange_assoc]
      exact congrArg (_ ≫ ·) h
    · have hμ : (hG.μIso (𝟙_ C) X.obj).hom = (e.hom.app (𝟙_ _) ⊗ₘ e.hom.app X) ≫
          μ F' (𝟙_ _) X ≫ e.inv.app (𝟙_ _ ⊗ X) :=
        μIso_hom_eq_of_isCompatible P G hG e he (𝟙_ _) X
      have hn : e.inv.app (𝟙_ _ ⊗ X) ≫ G.map (λ_ X.obj).hom =
          F'.map (λ_ X).hom ≫ e.inv.app X := (e.inv.naturality (λ_ X).hom).symm
      change (λ_ (G.obj X.obj)).hom = (ε F' ≫ e.inv.app (𝟙_ _)) ▷ G.obj X.obj ≫
        (hG.μIso (𝟙_ C) X.obj).hom ≫ G.map (λ_ X.obj).hom
      rw [hμ, assoc, assoc, hn, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, assoc,
        Iso.inv_hom_id_app, comp_id, tensorHom_def', assoc,
        ← Functor.LaxMonoidal.left_unitality_assoc, id_comp, leftUnitor_naturality_assoc,
        Iso.hom_inv_id_app]
      exact (comp_id _).symm
  right_unitality X := by
    refine app_eq_of_preservesFilteredColimits P hP hgen (G ⋙ tensorRight (𝟙_ D)) G
      (fun X ↦ (ρ_ (G.obj X)).hom)
      (fun X ↦ G.obj X ◁ (Functor.Monoidal.εIso F' ≪≫ (e.app (𝟙_ P.FullSubcategory)).symm).hom ≫
        (hG.μIso X (𝟙_ C)).hom ≫ G.map (ρ_ X).hom)
      (fun f ↦ rightUnitor_naturality (G.map f)) (fun {X Y} f ↦ ?_) (fun X ↦ ?_) X
    · change G.map f ▷ _ ≫ _ = _
      have h : G.map f ▷ G.obj (𝟙_ C) ≫ (hG.μIso Y (𝟙_ C)).hom ≫ G.map (ρ_ Y).hom =
          (hG.μIso X (𝟙_ C)).hom ≫ G.map (ρ_ X).hom ≫ G.map f := by
        rw [hG.μIso_natural_left_assoc, ← G.map_comp, ← G.map_comp, rightUnitor_naturality]
      simp only [assoc]
      rw [← whisker_exchange_assoc]
      exact congrArg (_ ≫ ·) h
    · have hμ : (hG.μIso X.obj (𝟙_ C)).hom = (e.hom.app X ⊗ₘ e.hom.app (𝟙_ _)) ≫
          μ F' X (𝟙_ _) ≫ e.inv.app (X ⊗ 𝟙_ _) :=
        μIso_hom_eq_of_isCompatible P G hG e he X (𝟙_ _)
      have hn : e.inv.app (X ⊗ 𝟙_ _) ≫ G.map (ρ_ X.obj).hom =
          F'.map (ρ_ X).hom ≫ e.inv.app X := (e.inv.naturality (ρ_ X).hom).symm
      change (ρ_ (G.obj X.obj)).hom = G.obj X.obj ◁ (ε F' ≫ e.inv.app (𝟙_ _)) ≫
        (hG.μIso X.obj (𝟙_ C)).hom ≫ G.map (ρ_ X.obj).hom
      rw [hμ, assoc, assoc, hn, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, assoc,
        Iso.inv_hom_id_app, comp_id, id_comp, MonoidalCategory.tensorHom_def, assoc,
        ← Functor.LaxMonoidal.right_unitality_assoc, rightUnitor_naturality_assoc,
        Iso.hom_inv_id_app]
      exact (comp_id _).symm

include hP hgen he in
/-- The tensorator of `coreMonoidalOfIsCompatible` is the tensorator of `hG`. -/
theorem coreMonoidalOfIsCompatible_μIso (X Y : C) :
    (coreMonoidalOfIsCompatible P hP hgen G hG e he).μIso X Y = hG.μIso X Y :=
  rfl

include hP hgen he in
/-- The unit morphism of `coreMonoidalOfIsCompatible` is the unit morphism of `F'` followed by the
inverse of `e` at the monoidal unit of `P.FullSubcategory`. -/
theorem coreMonoidalOfIsCompatible_εIso_hom :
    (coreMonoidalOfIsCompatible P hP hgen G hG e he).εIso.hom =
      ε F' ≫ e.inv.app (𝟙_ P.FullSubcategory) :=
  rfl

include hP hgen he in
/-- **The identification of the restriction of the extension with `F'` is monoidal**, for the
monoidal structure `CategoryTheory.ObjectProperty.coreMonoidalOfIsCompatible` on `G`. -/
theorem isMonoidal_of_isCompatible :
    letI := (coreMonoidalOfIsCompatible P hP hgen G hG e he).toMonoidal
    NatTrans.IsMonoidal e.hom := by
  let := (coreMonoidalOfIsCompatible P hP hgen G hG e he).toMonoidal
  refine ⟨?_, fun X Y ↦ ?_⟩
  · have hε : ε G = ε F' ≫ e.inv.app (𝟙_ P.FullSubcategory) := rfl
    rw [Functor.LaxMonoidal.comp_ε, ι_ε, G.map_id, comp_id, hε, assoc, Iso.inv_hom_id_app,
      comp_id]
  · have hμ : μ G (P.ι.obj X) (P.ι.obj Y) = (hG.μIso X.obj Y.obj).hom := rfl
    rw [Functor.LaxMonoidal.comp_μ, ι_μ, G.map_id, comp_id, hμ,
      μIso_hom_eq_of_isCompatible P G hG e he, assoc, assoc, Iso.inv_hom_id_app, comp_id]

end Monoidal

section Braided

variable [BraidedCategory C] [BraidedCategory D]
  {F' : P.FullSubcategory ⥤ D} [F'.Braided] (e : P.ι ⋙ G ≅ F')
  (he : (hG.restrict P).IsCompatible (Functor.Monoidal.toTensorStructure F') e)

include hP hgen he in
/-- **The braided monoidal structure on the extension of a braided monoidal functor**: the
monoidal structure `CategoryTheory.ObjectProperty.coreMonoidalOfIsCompatible` is braided, since
the compatibility with the braidings holds on pairs of `P`-objects, where it is that of `F'`. -/
@[instance_reducible]
def braidedOfIsCompatible : G.Braided :=
  { (coreMonoidalOfIsCompatible P hP hgen G hG e he).toMonoidal with
    braided X Y := by
      change (hG.μIso X Y).hom ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫
        (hG.μIso Y X).hom
      refine tensor_app_eq_of_preservesFilteredColimits P hP hgen G G
        ((curriedTensor C).flip ⋙ (Functor.whiskeringRight C C D).obj G)
        (fun X Y ↦ (hG.μIso X Y).hom ≫ G.map (β_ X Y).hom)
        (fun X Y ↦ (β_ (G.obj X) (G.obj Y)).hom ≫ (hG.μIso Y X).hom)
        (fun {X X'} f Y ↦ ?_) (fun X {Y Y'} g ↦ ?_) (fun {X X'} f Y ↦ ?_) (fun X {Y Y'} g ↦ ?_)
        (fun X Y ↦ ?_) X Y
      · dsimp
        rw [hG.μIso_natural_left_assoc, ← G.map_comp, BraidedCategory.braiding_naturality_left,
          G.map_comp, assoc]
      · dsimp
        rw [hG.μIso_natural_right_assoc, ← G.map_comp, BraidedCategory.braiding_naturality_right,
          G.map_comp, assoc]
      · dsimp
        rw [BraidedCategory.braiding_naturality_left_assoc, hG.μIso_natural_right, assoc]
      · dsimp
        rw [BraidedCategory.braiding_naturality_right_assoc, hG.μIso_natural_left, assoc]
      · have hn : e.inv.app (X ⊗ Y) ≫ G.map (β_ X.obj Y.obj).hom =
            F'.map (β_ X Y).hom ≫ e.inv.app (Y ⊗ X) := (e.inv.naturality (β_ X Y).hom).symm
        rw [μIso_hom_eq_of_isCompatible P G hG e he X Y,
          μIso_hom_eq_of_isCompatible P G hG e he Y X]
        simp only [assoc]
        rw [hn, Functor.LaxBraided.braided_assoc, BraidedCategory.braiding_naturality_assoc]
        rfl }

include hP hgen he in
/-- The monoidal functor structure underlying `braidedOfIsCompatible` is that of
`coreMonoidalOfIsCompatible`. -/
theorem braidedOfIsCompatible_toMonoidal :
    (braidedOfIsCompatible P hP hgen G hG e he).toMonoidal =
      (coreMonoidalOfIsCompatible P hP hgen G hG e he).toMonoidal :=
  rfl

end Braided

end Upgrade

section Extension

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (P : ObjectProperty C)
  [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D] [P.IsMonoidal]
  [Preadditive C] [Preadditive D] [HasColimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} D]
  [HasFiniteColimits C] [HasFiniteColimits D] [HasZeroObject C] [HasZeroObject D]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
  {A : Type u''} [Category.{v''} A] [MonoidalCategory A] [BraidedCategory A] [Preadditive A]
  (E : A ≌ P.FullSubcategory) [E.functor.Braided] [E.functor.Additive]

include hP hgen in
/-- **A right exact braided monoidal functor out of compact generators extends to a right exact
braided monoidal functor commuting with all colimits.** Let `C` and `D` be preadditive braided
monoidal categories with `w`-small colimits, in which tensoring on either side commutes with
filtered colimits, and let `P` be a monoidal property of objects of `C` closed under finite
coproducts and cokernels, cutting out a locally `w`-small full subcategory of categorically compact
objects, such that every object of `C` is a `w`-filtered colimit of `P`-objects. Let `E` be an
equivalence from a preadditive braided monoidal category `A` to the `P`-objects whose functor is
additive and braided monoidal. Then every additive braided monoidal functor `F : A ⥤ D`
preserving finite colimits is, by a monoidal isomorphism `e`, the restriction along `E.functor`
of an additive braided monoidal functor `G : C ⥤ D` preserving finite colimits and all `w`-small
colimits.

The functor `G` is the extension of `CategoryTheory.ObjectProperty.existsUnique_tensorExtension`
(Stacks 0FWY) of `F` composed with `E.inverse`, with the braided monoidal structure of
`CategoryTheory.ObjectProperty.braidedOfIsCompatible`. -/
theorem exists_braided_extension_of_equivalence (F : A ⥤ D) [F.Additive] [F.Braided]
    [PreservesFiniteColimits F] :
    ∃ (G : C ⥤ D) (_ : G.Braided) (e : E.functor ⋙ P.ι ⋙ G ≅ F),
      G.Additive ∧ PreservesFiniteColimits G ∧ PreservesColimitsOfSize.{w, w} G ∧
        NatTrans.IsMonoidal e.hom := by
  let : E.inverse.Braided := Equivalence.inverseBraided E
  have : PreservesFiniteColimits (E.inverse ⋙ F) := comp_preservesFiniteColimits _ _
  obtain ⟨G, e, hG, ⟨h₁, h₂, h₃, hc⟩, -⟩ :=
    existsUnique_tensorExtension P hP hgen (E.inverse ⋙ F)
      (Functor.Monoidal.toTensorStructure (E.inverse ⋙ F))
  have : PreservesFilteredColimitsOfSize.{w, w} G := inferInstance
  let := braidedOfIsCompatible P hP hgen G hG e hc
  have : NatTrans.IsMonoidal e.hom := isMonoidal_of_isCompatible P hP hgen G hG e hc
  refine ⟨G, inferInstance, Functor.isoWhiskerLeft E.functor e ≪≫
    (Functor.associator E.functor E.inverse F).symm ≪≫ Functor.isoWhiskerRight E.unitIso.symm F ≪≫
      F.leftUnitor, h₁, h₂, h₃, ?_⟩
  exact inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerLeft E.functor e.hom ≫
    (Functor.associator E.functor E.inverse F).inv ≫ Functor.whiskerRight E.unitIso.inv F ≫
      F.leftUnitor.hom))

end Extension

end CategoryTheory.ObjectProperty

module

public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The abelian germ model is the inverse image of abelian sheaves

For a continuous map `g : Z ⟶ Y` and a sheaf of abelian groups `F` on `Y`, the abelian germ model
`GermPullback.abelianSheaf` of the inverse image `g⁻¹F` is isomorphic to Mathlib's
`TopCat.Sheaf.pullback AddCommGrpCat`, the sheafification of the presheaf pullback.

## Main definitions

* `GermPullback.abelianSheafPullbackComparison`: the transpose of the germ-model unit
  `GermPullback.toPushforward` across `TopCat.Sheaf.pullbackPushforwardAdjunction`.
* `GermPullback.abelianSheafPullbackComparisonInv`: the morphism in the other direction,
  supplied by the universal property of the germ model applied to the unit of that adjunction.
* `GermPullback.abelianSheafPullbackIso`: **the abelian germ model is Mathlib's sheaf pullback.**

## Main results

* `GermPullback.existsUnique_mapOutSheaf`: the mapping-out half of the abelian germ-model
  adjunction, read in the category of abelian sheaves and with Mathlib's
  `TopCat.Sheaf.pushforward`.
* `GermPullback.unit_comp_map_abelianSheafPullbackComparison` and
  `GermPullback.toPushforward_comp_map_abelianSheafPullbackComparisonInv`: each comparison
  transposes back to the unit it was built from.
* `GermPullback.isIso_abelianSheafPullbackComparison`: the comparison is an isomorphism.

## References

* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace GermPullback

variable {Y Z : TopCat.{u}} (g : Z ⟶ Y)

/-- **The mapping-out half of the abelian germ-model adjunction, in the category of abelian
sheaves.** For every abelian sheaf `H` on `Z` and every morphism `φ : F ⟶ g _* H` there is a
unique morphism `ψ : g⁻¹F ⟶ H` of abelian sheaves whose composite with the unit
`GermPullback.toPushforward` is `φ`. -/
theorem existsUnique_mapOutSheaf (F : Y.Sheaf AddCommGrpCat.{u}) (H : Z.Sheaf AddCommGrpCat.{u})
    (φ : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).obj H) :
    ∃! ψ : abelianSheaf (ConcreteCategory.hom g) F.presheaf ⟶ H,
      toPushforward g F ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map ψ = φ := by
  obtain ⟨ψ, hψ, huniq⟩ :=
    existsUnique_mapOut g (𝒢 := F.presheaf) (H := H.presheaf) φ.1 H.2
  refine ⟨⟨ψ⟩, Sheaf.hom_ext hψ, fun ρ hρ ↦ ?_⟩
  exact Sheaf.hom_ext (huniq ρ.1 (congrArg (fun k ↦ k.1) hρ))

/-- **The comparison of the abelian germ model with Mathlib's sheaf pullback**: the transpose of
the germ-model unit `GermPullback.toPushforward` across the pullback–pushforward adjunction. It
is an isomorphism, `GermPullback.abelianSheafPullbackIso`. -/
def abelianSheafPullbackComparison (F : Y.Sheaf AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F ⟶
      abelianSheaf (ConcreteCategory.hom g) F.presheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv F _).symm
    (toPushforward g F)

/-- The comparison transposes back to the germ-model unit. -/
lemma unit_comp_map_abelianSheafPullbackComparison (F : Y.Sheaf AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map
          (abelianSheafPullbackComparison g F) =
      toPushforward g F :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv F
    (abelianSheaf (ConcreteCategory.hom g) F.presheaf)).apply_symm_apply (toPushforward g F)

/-- The morphism in the other direction, supplied by the universal property of the abelian germ
model applied to the unit of the pullback–pushforward adjunction. -/
def abelianSheafPullbackComparisonInv (F : Y.Sheaf AddCommGrpCat.{u}) :
    abelianSheaf (ConcreteCategory.hom g) F.presheaf ⟶
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F :=
  (existsUnique_mapOutSheaf g F ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app F)).choose

/-- The defining property of `GermPullback.abelianSheafPullbackComparisonInv`. -/
lemma toPushforward_comp_map_abelianSheafPullbackComparisonInv
    (F : Y.Sheaf AddCommGrpCat.{u}) :
    toPushforward g F ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map
        (abelianSheafPullbackComparisonInv g F) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app F :=
  (existsUnique_mapOutSheaf g F ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app F)).choose_spec.1

/-- **The abelian germ model is Mathlib's sheaf pullback.** For a continuous map `g : Z ⟶ Y` and
a sheaf of abelian groups `F` on `Y`, the comparison of the abelian germ-model inverse image
`g⁻¹F` with `TopCat.Sheaf.pullback`, the sheafification of the presheaf pullback, is an
isomorphism. -/
@[ega "0 3.7.1" "special case"]
instance isIso_abelianSheafPullbackComparison (F : Y.Sheaf AddCommGrpCat.{u}) :
    IsIso (abelianSheafPullbackComparison g F) := by
  obtain ⟨ρ, -, huniq⟩ := existsUnique_mapOutSheaf g F
    (abelianSheaf (ConcreteCategory.hom g) F.presheaf) (toPushforward g F)
  have h1 : toPushforward g F ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map
      (abelianSheafPullbackComparisonInv g F ≫ abelianSheafPullbackComparison g F) =
      toPushforward g F := by
    rw [Functor.map_comp, ← Category.assoc,
      toPushforward_comp_map_abelianSheafPullbackComparisonInv,
      unit_comp_map_abelianSheafPullbackComparison]
  have h2 : toPushforward g F ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map
      (𝟙 (abelianSheaf (ConcreteCategory.hom g) F.presheaf)) = toPushforward g F := by
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  refine ⟨abelianSheafPullbackComparisonInv g F, ?_, (huniq _ h1).trans (huniq _ h2).symm⟩
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv F _).injective
    ?_
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    unit_comp_map_abelianSheafPullbackComparison,
    toPushforward_comp_map_abelianSheafPullbackComparisonInv]
  simp

/-- **The abelian germ model is Mathlib's sheaf pullback**, as an isomorphism. -/
def abelianSheafPullbackIso (F : Y.Sheaf AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F ≅
      abelianSheaf (ConcreteCategory.hom g) F.presheaf :=
  asIso (abelianSheafPullbackComparison g F)

end GermPullback

end

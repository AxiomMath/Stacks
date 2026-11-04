module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualityPlusIso
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparisonRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens

/-!
# `f^! ≅ f_new^!` and the change of compactification

For a separated morphism `g : X ⟶ Y` of schemes of finite type over a Noetherian base and two
compactifications `j₁`, `j₂` of `g`, the isomorphism `g^! ≅ g_new^!` of [Stacks, Tag 0AUE] at `j₂`
is the one at `j₁` after the isomorphism `g^!_{j₁} ≅ g^!_{j₂}` of [Stacks, Tag 0AA0], the
identification of `g^!K` being transported along the same isomorphism.

## Main results

* `Stacks.Duality.NormalizedOnOpens.upperShriekStdIsoFNewShriekOfIso_upperShriekPlusIso`: the
  isomorphism `g^! ≅ g_new^!` at `j₁` is the one at `j₂` precomposed with the isomorphism
  `g^!_{j₁} ≅ g^!_{j₂}`.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.NormalizedOnOpens

open Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

section PlusIso

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (g : X ⟶ Y)
  (j₁ j₂ : CompactificationOf (Over.mk g.left)) {K : Std Y.left} (hK : IsDualizing K)
  (hKb : DerivedCategoryB.IsBoundedBelow (dualizingQCoh hK).obj) {ω : Std X.left}

/-- `f^!K` at two compactifications, identified by [Stacks, Tag 0AA0] and read at the standard
model. -/
abbrev upperShriekDualizingPlusIso : upperShriekDualizing g j₁ hK ≅ upperShriekDualizing g j₂ hK :=
  (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison X.left).inverse).mapIso
    ((DominatingCompactification.upperShriekPlusIso g j₁ j₂).app ⟨dualizingQCoh hK, hKb⟩)

/-- If `s ≫ u₂ = u₁ ≫ G.map κ`, then `L = s ≫ u₂ ≫ G.map ε ≫ z` and
`R = u₁ ≫ G.map (κ ≫ ε) ≫ z` are equal. -/
theorem comp_comp_map_eq_comp_map_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒟 ⥤ 𝒞)
    {a0 a1 c : 𝒞} {e1 e2 e3 : 𝒟} (s : a0 ⟶ a1) (u₂ : a1 ⟶ G.obj e2) (u₁ : a0 ⟶ G.obj e1)
    (κ : e1 ⟶ e2) (ε : e2 ⟶ e3) (z : G.obj e3 ⟶ c) (B : s ≫ u₂ = u₁ ≫ G.map κ) {L R : a0 ⟶ c}
    (hL : L = s ≫ u₂ ≫ G.map ε ≫ z) (hR : R = u₁ ≫ G.map (κ ≫ ε) ≫ z) : L = R := by
  rw [hL, hR, reassoc_of% B, G.map_comp, Category.assoc]

/-- **`f^! ≅ f_new^!` does not depend on the compactification**: the isomorphism of
[Stacks, Tag 0AA0] from `j₁` to `j₂` carries the one at `j₂` and `e` to the one at `j₁` and the
identification `f^!_{j₁}K ≅ f^!_{j₂}K ≅ ω`. -/
theorem upperShriekStdIsoFNewShriekOfIso_upperShriekPlusIso (M : (plusCoh Y.left).FullSubcategory)
    (hM : DerivedCategoryB.IsBoundedBelow (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩).obj)
    (e : upperShriekDualizing g j₂ hK ≅ ω) :
    (comparison X.left).inverse.map
        ((DominatingCompactification.upperShriekPlusIso g j₁ j₂).hom.app
          ⟨toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩, hM⟩).hom.hom ≫
      (upperShriekStdIsoFNewShriekOfIso g j₂ hK e).hom.app M =
    (upperShriekStdIsoFNewShriekOfIso g j₁ hK
      (upperShriekDualizingPlusIso g j₁ j₂ hK hKb ≪≫ e)).hom.app M :=
  comp_comp_map_eq_comp_map_comp ((sheafHom X.left).obj ((pull g.left).op.obj
      (((sheafHom Y.left).flip.obj K).rightOp.obj ((plusCoh Y.left).ι.obj M)))) _ _ _ _ _ _
    (upperShriekDualityIso_upperShriekPlusIso g j₁ j₂ hK M hM hKb)
    (congrArg (_ ≫ ·) (upperShriekStdIsoFNewShriekOfIso_hom_app g j₂ hK e M))
    (upperShriekStdIsoFNewShriekOfIso_hom_app g j₁ hK
      (upperShriekDualizingPlusIso g j₁ j₂ hK hKb ≪≫ e) M)

end PlusIso

end Stacks.Duality.NormalizedOnOpens

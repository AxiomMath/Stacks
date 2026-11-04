module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# Restricting along an isomorphism of base objects

Let `m : W' ⟶ W` be a morphism of a big fppf site and let `j^{-1} = `
`CategoryTheory.OverShriek.relocalizeRestrict m` be restriction of presheaves along
`CategoryTheory.Over.map m`. When `m` is an **isomorphism**, restriction changes nothing that the
every-étale-chart condition of Stacks 03MJ sees, and it carries algebraic spaces over `W` to
algebraic spaces over `W'`.

## Main results

* `CategoryTheory.OverShriek.isIso_relocalizeRestrictMap`: the comparison
  `Λ_{m ≫ a}(j^{-1}F) ⟶ Λ_a F` of the two lower-shriek extensions is an isomorphism when `m` is.
* `CategoryTheory.OverShriek.relocalizeRestrictMap_naturality`: that comparison is natural in the
  presheaf.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeRestrict_iff`: the every-étale-chart
  condition of Stacks 03MJ is unchanged by restriction along an isomorphism.
* `AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict_iff`: restriction along an isomorphism
  preserves and reflects algebraicity.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {X A A' : C} (a : A ⟶ X) (m : A' ⟶ A)

/-- The morphism `Over.mk (m ≫ a) ⟶ Over.mk a` of the slice over `X` given by `m` is an
isomorphism when `m` is. -/
theorem isIso_overHomMk_comp [IsIso m] :
    IsIso (Over.homMk m rfl : Over.mk (m ≫ a) ⟶ Over.mk a) := by
  have _ : IsIso ((Over.forget X).map (Over.homMk m rfl : Over.mk (m ≫ a) ⟶ Over.mk a)) :=
    inferInstanceAs (IsIso m)
  exact isIso_of_reflects_iso _ (Over.forget X)

/-- **The comparison of the two lower-shriek extensions of a restriction is an isomorphism when
the restriction is taken along an isomorphism.** -/
theorem isIso_relocalizeRestrictMap [IsIso m] (F : (Over A)ᵒᵖ ⥤ Type v) :
    IsIso (relocalizeRestrictMap a m F) := by
  have _ := isIso_overHomMk_comp a m
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := MorphismProperty.isomorphisms ((Over X)ᵒᵖ ⥤ Type v))
    (isPullback_relocalizeRestrictMap a m F).flip
    (show IsIso (yoneda.map (Over.homMk m rfl : Over.mk (m ≫ a) ⟶ Over.mk a)) from
      inferInstance)

/-- **The comparison of the two lower-shriek extensions of a restriction is natural in the
presheaf.** -/
theorem relocalizeRestrictMap_naturality {F G : (Over A)ᵒᵖ ⥤ Type v} (k : F ⟶ G) :
    (relocalizePresheafFunctor (m ≫ a)).map ((relocalizeRestrict m).map k) ≫
        relocalizeRestrictMap a m G =
      relocalizeRestrictMap a m F ≫ (relocalizePresheafFunctor a).map k := by
  ext W x
  rfl

end CategoryTheory.OverShriek

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W W' : Scheme.{u}) (hW : B.Contains W) (hW' : B.Contains W')
  (m : B.obj hW' ⟶ B.obj hW)

/-- For `m` an isomorphism and `mm = m ≫ a`, the every-étale-chart condition of Stacks 03MJ holds
for the lower-shriek extension along `mm` of the restriction of `k` exactly when it holds for the
lower-shriek extension of `k` along `a`. -/
private theorem holdsOnEveryEtaleChart_relocalizeRestrictMap_aux {S : Scheme.{u}}
    (hS : B.Contains S) (a : B.obj hW ⟶ B.obj hS) [IsIso m]
    (P : MorphismProperty Scheme.{u}) {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : F ⟶ G)
    (mm : B.obj hW' ⟶ B.obj hS) (hmm : m ≫ a = mm) :
    Space.HoldsOnEveryEtaleChart B S hS P
        ((OverShriek.relocalizePresheafFunctor mm).map ((OverShriek.relocalizeRestrict m).map k)) ↔
      Space.HoldsOnEveryEtaleChart B S hS P ((OverShriek.relocalizePresheafFunctor a).map k) := by
  subst hmm
  have _ := OverShriek.isIso_relocalizeRestrictMap a m F
  have _ := OverShriek.isIso_relocalizeRestrictMap a m G
  refine Iff.trans (Space.holdsOnEveryEtaleChart_comp_iso_iff B S hS P
      ((OverShriek.relocalizePresheafFunctor (m ≫ a)).map
        ((OverShriek.relocalizeRestrict m).map k))
      (OverShriek.relocalizeRestrictMap a m G)).symm ?_
  rw [OverShriek.relocalizeRestrictMap_naturality]
  exact Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS P
    (OverShriek.relocalizeRestrictMap a m F) ((OverShriek.relocalizePresheafFunctor a).map k)

/-- **The every-étale-chart condition of Stacks 03MJ is unchanged by restriction along an
isomorphism of base objects.** For `m : W' ⟶ W` an isomorphism of the big fppf site and `k` a
morphism of presheaves on the big fppf site of `W`, the property `P` holds on every commuting
square of étale charts of the restriction `j^{-1}k` exactly when it holds on every such square
for `k`. -/
theorem Space.holdsOnEveryEtaleChart_relocalizeRestrict_iff [IsIso m]
    (P : MorphismProperty Scheme.{u}) {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : F ⟶ G) :
    Space.HoldsOnEveryEtaleChart B W' hW' P ((OverShriek.relocalizeRestrict m).map k) ↔
      Space.HoldsOnEveryEtaleChart B W hW P k := by
  exact (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B W' W hW' hW m P
    ((OverShriek.relocalizeRestrict m).map k)).symm.trans
    ((holdsOnEveryEtaleChart_relocalizeRestrictMap_aux B W W' hW hW' m hW (𝟙 (B.obj hW)) P k m
      (Category.comp_id m)).trans
    (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B W W hW hW (𝟙 (B.obj hW)) P k))

/-- **Restriction along an isomorphism of base objects preserves and reflects algebraicity.** For
`m : W' ⟶ W` an isomorphism of the big fppf site, a presheaf on the big fppf site of `W` is an
algebraic space over `W` exactly when its restriction along `CategoryTheory.Over.map m` is an
algebraic space over `W'`. -/
theorem isAlgebraicSpace_relocalizeRestrict_iff [IsIso m] (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsAlgebraicSpace B W' hW' ((OverShriek.relocalizeRestrict m).obj F) ↔
      IsAlgebraicSpace B W hW F := by
  have key : ∀ (mm : B.obj hW' ⟶ B.obj hW), m ≫ 𝟙 (B.obj hW) = mm →
      (IsAlgebraicSpace B W hW
          ((OverShriek.relocalizePresheafFunctor mm).obj
            ((OverShriek.relocalizeRestrict m).obj F)) ↔
        IsAlgebraicSpace B W hW
          ((OverShriek.relocalizePresheafFunctor (𝟙 (B.obj hW))).obj F)) := by
    rintro mm rfl
    have _ := OverShriek.isIso_relocalizeRestrictMap (𝟙 (B.obj hW)) m F
    exact ⟨isAlgebraicSpace_of_iso B W hW
        (asIso (OverShriek.relocalizeRestrictMap (𝟙 (B.obj hW)) m F)).symm,
      isAlgebraicSpace_of_iso B W hW (asIso (OverShriek.relocalizeRestrictMap (𝟙 (B.obj hW)) m F))⟩
  exact (isAlgebraicSpace_viewOver_iff B W' W hW' hW m
    ((OverShriek.relocalizeRestrict m).obj F)).symm.trans ((key m (Category.comp_id m)).trans
    (isAlgebraicSpace_viewOver_iff B W W hW hW (𝟙 (B.obj hW)) F))

end AlgebraicGeometry

end

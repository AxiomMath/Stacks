module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase

/-!
# Restriction to a smaller base is a base change over the base

Let `m : W' ⟶ W` be a morphism of a big fppf site and let `j^{-1} =`
`CategoryTheory.OverShriek.relocalizeRestrict m` be restriction of presheaves along
`CategoryTheory.Over.map m`. Let `k : X ⟶ Y` be a morphism of presheaves on the big fppf site of
`W` whose source and target are given over a presheaf `T` with subsingleton values by morphisms
`p : X ⟶ T` and `q : Y ⟶ T` with `k ≫ q = p`.

Then the restriction `j^{-1}k`, read over `W` again through the lower-shriek extension of
Stacks 03I5 part (2), *is* the base change `X ×_T h_{W'} ⟶ Y ×_T h_{W'}` of `k` over `T` along a
morphism `h_{W'} ⟶ T`: this is
`CategoryTheory.OverShriek.isPullback_relocalizeRestrictCounit` on each of the two corners,
together with the naturality of the counit. Since the every-étale-chart condition of Stacks 03MJ
does not see the lower-shriek extension
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`), a condition of that shape
holds for the restriction over `W'` exactly when it holds for the base change over `W`.

That is the step which turns a locus cut out on a base by a base-change condition into a locus
testing a condition *in the site of the base*: the condition at an object `W'` of the site of `W`
is read in the site of `W'`, while the locus is produced by a representability argument which
tests base changes along morphisms of presheaves on the site of `W`.

## Main results

* `CategoryTheory.OverShriek.relocalizeRestrictCounit_naturality`: the counit comparing the
  lower-shriek extension of a restriction with the original presheaf is natural.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeRestrict_iff_baseChangeOverBase`:
  **the every-étale-chart condition of Stacks 03MJ for a restriction is the condition for the
  base change over the base.**

## Implementation notes

The target presheaf `T` is an arbitrary presheaf with subsingleton values rather than the
representable presheaf of the terminal object of the site of `W`: that is all
`CategoryTheory.OverShriek.isPullback_relocalizeRestrictCounit` asks for, and it lets the
statement be used at whichever structural morphism a consumer has in hand. The morphism
`h_{W'} ⟶ T` is taken as data for the same reason; subsingleton-valuedness of `T` makes it
unique, so no compatibility has to be imposed on it.

Nothing here inverts the comparison of the two presentations of the base change by hand: the two
cartesian squares have the same cospan, so `CategoryTheory.IsPullback.isoIsPullback` produces the
comparison isomorphisms on both sides, and the single square identifying the two morphisms is
checked against the two projections of the canonical fibre product.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- **The counit comparing the lower-shriek extension of a restriction with the original presheaf
is natural in the presheaf.** Both composites send a section `(ψ, s)` of `Λ_f(j^{-1}X)` to the
restriction of `k s` along the comparison identifying the object it lives over with the
factorization `ψ` records. -/
theorem relocalizeRestrictCounit_naturality {X Y : (Over U)ᵒᵖ ⥤ Type v} (k : X ⟶ Y) :
    (relocalizePresheafFunctor f).map ((relocalizeRestrict f).map k) ≫
        relocalizeRestrictCounit f Y =
      relocalizeRestrictCounit f X ≫ k := by
  ext W x
  exact (k.naturality_apply (Over.homMk (𝟙 (unop W).left)
    (by rw [Category.id_comp]; exact x.2) : unop W ⟶ Over.mk (x.1.1 ≫ f)).op x.1.2).symm

end CategoryTheory.OverShriek

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W W' : Scheme.{u}) (hW : B.Contains W) (hW' : B.Contains W')
  (m : B.obj hW' ⟶ B.obj hW)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves of sets times out at the default budget
/-- Pullbacks of presheaves on the big fppf site over `W` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_EtaleChartRestrictBaseChange :
    HasPullbacks ((BigFppfOver B W hW)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_EtaleChartRestrictBaseChange
    {X Y Z : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The lower-shriek extension of the restriction of a morphism of presheaves along `m`, compared
with the base change of that morphism over a subsingleton-valued presheaf along the representable
presheaf of `m`: the comparison isomorphisms on the two corners carry the one morphism to the
other. -/
private theorem isoIsPullback_hom_comp_baseChangeOverBase
    {X Y T : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hT : ∀ Z, Subsingleton (T.obj Z)) (p : X ⟶ T) (q : Y ⟶ T) (hkq : k ≫ q = p)
    (τ : yoneda.obj (Over.mk m) ⟶ T) :
    ((OverShriek.isPullback_relocalizeRestrictCounit m X hT p τ).isoIsPullback _ _
          (IsPullback.of_hasPullback p τ)).hom ≫
        Space.baseChangeOverBase B W hW k p q hkq τ =
      (OverShriek.relocalizePresheafFunctor m).map ((OverShriek.relocalizeRestrict m).map k) ≫
        ((OverShriek.isPullback_relocalizeRestrictCounit m Y hT q τ).isoIsPullback _ _
          (IsPullback.of_hasPullback q τ)).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Space.baseChangeOverBase, pullback.lift_fst, Category.assoc,
      IsPullback.isoIsPullback_hom_fst, ← Category.assoc,
      IsPullback.isoIsPullback_hom_fst,
      OverShriek.relocalizeRestrictCounit_naturality m k]
  · rw [Category.assoc, Space.baseChangeOverBase, pullback.lift_snd, Category.assoc,
      IsPullback.isoIsPullback_hom_snd, IsPullback.isoIsPullback_hom_snd,
      relocalizeToYoneda_naturality B W' W hW' hW m ((OverShriek.relocalizeRestrict m).map k)]

/-- **The every-étale-chart condition of Stacks 03MJ for a restriction to a smaller base is the
condition for the base change over the base.** Let `k : X ⟶ Y` be a morphism of presheaves on the
big fppf site of `W` whose source and target are given over a presheaf `T` with subsingleton
values by `p` and `q` with `k ≫ q = p`, and let `m : W' ⟶ W` be an object of the site of `W`.
Then `P` holds on every commuting square of étale charts of the restriction `j^{-1}k` over `W'`
exactly when it holds on every such square for the base change `X ×_T h_{W'} ⟶ Y ×_T h_{W'}`
over `W`.

The restriction, read over `W` through its lower-shriek extension, *is* that base change
(`CategoryTheory.OverShriek.isPullback_relocalizeRestrictCounit`), and the extension is invisible
to the condition (`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`). -/
theorem Space.holdsOnEveryEtaleChart_relocalizeRestrict_iff_baseChangeOverBase
    (P : MorphismProperty Scheme.{u}) {X Y T : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hT : ∀ Z, Subsingleton (T.obj Z)) (p : X ⟶ T) (q : Y ⟶ T) (hkq : k ≫ q = p)
    (τ : yoneda.obj (Over.mk m) ⟶ T) :
    Space.HoldsOnEveryEtaleChart B W' hW' P ((OverShriek.relocalizeRestrict m).map k) ↔
      Space.HoldsOnEveryEtaleChart B W hW P
        (Space.baseChangeOverBase B W hW k p q hkq τ) := by
  have hbig := Space.holdsOnEveryEtaleChart_relocalizeMap_iff B W' W hW' hW m P
    ((OverShriek.relocalizeRestrict m).map k)
  refine hbig.symm.trans ?_
  refine Iff.trans ?_ (Space.holdsOnEveryEtaleChart_iso_comp_iff B W hW P
    ((OverShriek.isPullback_relocalizeRestrictCounit m X hT p τ).isoIsPullback _ _
      (IsPullback.of_hasPullback p τ)).hom (Space.baseChangeOverBase B W hW k p q hkq τ))
  rw [isoIsPullback_hom_comp_baseChangeOverBase B W W' hW hW' m k hT p q hkq τ]
  exact (Space.holdsOnEveryEtaleChart_comp_iso_iff B W hW P
    ((OverShriek.relocalizePresheafFunctor m).map ((OverShriek.relocalizeRestrict m).map k))
    ((OverShriek.isPullback_relocalizeRestrictCounit m Y hT q τ).isoIsPullback _ _
      (IsPullback.of_hasPullback q τ)).hom).symm

end AlgebraicGeometry

end

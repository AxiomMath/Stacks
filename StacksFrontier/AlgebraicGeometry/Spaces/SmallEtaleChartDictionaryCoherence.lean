module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueingDictionary
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus

/-!
# The chart-to-slice dictionary is compatible with the composition isomorphisms

Stacks 03LS describes a sheaf on the small étale site of an algebraic space `X` by a family of
sheaves on the small étale sites of the étale scheme charts of `X` with comparison isomorphisms
satisfying a cocycle condition, and Stacks 0GWK says the same with the slices `X_étale/U` in
place of the charts' small étale sites.
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure` identifies the two
indexings of restriction object by object; this file proves that the identification is
compatible with the composition isomorphisms on the two sides.

## Main results

* `AlgebraicGeometry.Space.chartLocalizationPostcompIso_comp`: the site-level coherence — the
  comparisons of Stacks 04M0 for two composable morphisms of charts compose to the comparison
  for the composite, read through `CategoryTheory.Over.mapComp`.
* `AlgebraicGeometry.Space.chartPostcompSheafIso_hom_eq`: the restriction-along-equal-functors
  half of the dictionary is the isomorphism of restriction functors induced by the comparison of
  Stacks 04M0, with no further transport.
* `AlgebraicGeometry.Space.chartPostcompSheafIso_comp`: that half is compatible with the
  composition isomorphisms on the two sides — the sheaf-level form of the site-level
  coherence.
* `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp`: **the first dictionary
  square of Stacks 03LS** — the chart-to-slice dictionary for a morphism of charts is
  compatible with the composition isomorphisms `chartInverseImageComp` and
  `CategoryTheory.GrothendieckTopology.overMapPullbackComp`.  This is what carries a chartwise
  glueing datum, cocycle condition included, to a slice-indexed one.
* `AlgebraicGeometry.Space.chartRestriction_overPullbackIso_comp`: **the second dictionary square
  of Stacks 03LS** — the same for the structure morphism of a chart, carrying
  `AlgebraicGeometry.Space.chartRestrictionComp` to
  `CategoryTheory.Sheaf.pushforwardOverMapIso`.  This is what identifies the canonical chartwise
  description of a sheaf with the canonical slice-indexed one.
* `AlgebraicGeometry.Space.chartRestrictionComp_inverseImageIso`: the bridge of Stacks 03LQ
  against Stacks 03G2, part (3), at the structure morphism of a chart, with the transport along
  `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` carried through.
* `CategoryTheory.comp_bridge_rearrange` and `CategoryTheory.comp_bridge_cancel`: the abstract
  rearrangements the two assemblies need.

## Implementation notes

Every isomorphism in the restriction-along-equal-functors half of the dictionary is restriction
along an isomorphism of functors of sites, so the calculus of
`StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus` reduces the sheaf-level
identity to the site-level one; the site-level one holds because every component of
`AlgebraicGeometry.Space.chartLocalizationPostcompIso` and of `CategoryTheory.Over.mapComp` is
the identity on underlying objects of the big fppf site.

Three measurements shape the proofs, and each was forced by a failure:

* the site-level coherence has to be stated a second and a third time, componentwise and in the
  opposite category, because its two sides have definitionally equal but syntactically different
  source and target functors, and then neither `CategoryTheory.Iso.trans_inv` nor
  `CategoryTheory.op_comp` rewrites inside it -- the implicit endpoints of the outer projection
  come from one side and those of the composite from the other, so the `rw` key does not match;
* for the same reason `CategoryTheory.Category.assoc` cannot reassociate the concrete composites
  of the dictionary: the same object occurs as `F.obj (G.obj T)` in one factor and as
  `(G ⋙ F).obj T` in the next, so the goal is not even type-correct at `implicit` transparency
  and `simp` declines it.  `CategoryTheory.comp_bridge_rearrange` does the rearrangement on
  abstract objects instead, where there is nothing to mismatch, and is applied with every
  morphism given positionally so that only definitional equality is checked;
* the composite of the two chartwise restriction functors may not be presented to the elaborator
  as `ρ pc_{chartMap (g ≫ f)}`: that defeq needs the strictness of the Stacks 03LP tower *and*
  `chartMap_comp` at once and exhausts the heartbeat limit.  Through
  `chartMap g ≫ chartMap f` -- which is what the bridge's `CategoryTheory.eqToHom` lands on, and
  what `AlgebraicGeometry.Space.eqToHom_smallEtalePostcomp_chartMap_congr` shows to be the
  identity -- it is one cheap step.

## Both dictionary squares of Stacks 03LS

The two squares the equivalence of Stacks 03LS needs are both here:
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp` for a *morphism* of charts and
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso_comp` for the *structure morphism* of a
chart.  The second one is the first with one genuinely new feature:
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace` is `CategoryTheory.Over.w`, a propositional
field, and not a definitional equality, so the transport the general bridge
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_comp'` carries is a real
`CategoryTheory.eqToHom` rather than the identity it is for a morphism of charts.  It is cancelled
against the component of `AlgebraicGeometry.Space.chartPostcompSheafIso`, whose underlying
morphism of the big fppf site is the identity, so that read in the small étale site of `X` it is
that same transport
(`AlgebraicGeometry.Space.eqToHom_comp_chartPostcompSheafIso`).

With both squares, `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueingEquivalence`
proves the equivalence of categories of Stacks 03LS,
`AlgebraicGeometry.Space.chartGlueingEquivalence`.

## References

* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

/-- The rearrangement that turns a naturality square, a bridge identity and a coherence
identity into one identity of five-fold composites.  Stated abstractly because the terms it is
applied to are large and spelled inconsistently — the same object occurs both as `F.obj (G.obj T)`
and as `(G ⋙ F).obj T` — so neither `rw` nor `simp` can reassociate the concrete composites,
whereas an explicit application checks only definitional equality. -/
theorem comp_bridge_rearrange {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ Bo P Q R : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) {c₁ : A₁ ⟶ Bo} {b₁ : Bo ⟶ A₃}
    (p : A₀ ⟶ P) (q : P ⟶ Q) (e : Q ⟶ Bo) (r : Bo ⟶ R) (w : R ⟶ A₄)
    (hnat : b ≫ c = c₁ ≫ b₁) (hbr : a ≫ c₁ = p ≫ q ≫ e) (hcps : b₁ ≫ d = r ≫ w)
    (r' : Q ⟶ R) (hr : e ≫ r = r') :
    (a ≫ b) ≫ c ≫ d = p ≫ (q ≫ r') ≫ w := by
  rw [← hr]
  simp only [Category.assoc]
  rw [← Category.assoc b, hnat]
  simp only [Category.assoc]
  rw [← Category.assoc a, hbr]
  simp only [Category.assoc]
  rw [hcps]

/-- Two restrictions along inverse morphisms of a presheaf compose to the identity.  Stated with
the two morphisms of sections given positionally, and equal to the restrictions only
propositionally, because the concrete terms it is applied to spell their common middle object two
different ways — one through the composite functor of sites and one through the two factors — so
`CategoryTheory.Functor.map_comp` has no key to match. -/
theorem presheaf_map_comp_eq_id {C : Type*} [Category C] {D : Type*} [Category D] (P : Cᵒᵖ ⥤ D)
    {x y : C} (m₁ : y ⟶ x) (m₂ : x ⟶ y)
    (g₁ : P.obj (Opposite.op x) ⟶ P.obj (Opposite.op y))
    (g₂ : P.obj (Opposite.op y) ⟶ P.obj (Opposite.op x))
    (hg₁ : g₁ = P.map m₁.op) (hg₂ : g₂ = P.map m₂.op) (h : m₂ ≫ m₁ = 𝟙 x) :
    g₁ ≫ g₂ = 𝟙 (P.obj (Opposite.op x)) := by
  rw [hg₁, hg₂, ← P.map_comp, ← op_comp, h, op_id, P.map_id]

/-- The rearrangement that turns a bridge identity and a cancellation into one identity of
threefold composites.  Stated abstractly for the same reason as
`CategoryTheory.comp_bridge_rearrange`. -/
theorem comp_bridge_cancel {C : Type*} [Category C] {A₀ A₁ A₂ A₃ P : C} (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₃) (p : A₀ ⟶ P) (q : P ⟶ A₃) (z : A₃ ⟶ A₂)
    (hbr : a ≫ b = p ≫ q ≫ z) (hz : z ≫ c = 𝟙 A₃) (hd : d = 𝟙 A₃) :
    a ≫ b ≫ c ≫ d = p ≫ q := by
  rw [hd, Category.comp_id, ← Category.assoc, hbr, Category.assoc, Category.assoc, hz,
    Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The site-level coherence -/

/-- **The comparisons of Stacks 04M0 are compatible with composition.**  For two composable
morphisms `g : W ⟶ V` and `f : V ⟶ U` of étale scheme charts of `X`, the comparison of
`AlgebraicGeometry.Space.chartLocalizationPostcompIso` for `f`, whiskered by postcomposition
along `g`, followed by the one for `g`, whiskered by `CategoryTheory.Over.map f`, is the
comparison for `g ≫ f` followed by `CategoryTheory.Over.mapComp`. -/
theorem chartLocalizationPostcompIso_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    Functor.isoWhiskerLeft (smallEtalePostcomp B S hS (chartMap B S hS X g)
          (isEtale_chartMap B S hS X g)) (chartLocalizationPostcompIso B S hS X f) ≪≫
        Functor.isoWhiskerRight (chartLocalizationPostcompIso B S hS X g) (Over.map f) =
      chartLocalizationPostcompIso B S hS X (g ≫ f) ≪≫
        Functor.isoWhiskerLeft (SmallEtale.chartLocalization B S hS X.1 W) (Over.mapComp g f) := by
  refine Iso.ext (NatTrans.ext (funext fun A => ?_))
  ext
  rfl

/-- `AlgebraicGeometry.Space.chartLocalizationPostcompIso_comp` in component form, with the
inverse isomorphisms composed as a cocycle condition does.  Stated separately because the two
sides of the isomorphism form have definitionally equal but syntactically different source and
target functors, so `CategoryTheory.Iso.trans_inv` does not rewrite inside it. -/
theorem chartLocalizationPostcompIso_comp_inv_app {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) (A : SmallEtale B S hS (chartSpace B S hS X W).1) :
    (Over.map f).map ((chartLocalizationPostcompIso B S hS X g).inv.app A) ≫
        (chartLocalizationPostcompIso B S hS X f).inv.app
          ((smallEtalePostcomp B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).obj A) =
      (Over.mapComp g f).inv.app ((SmallEtale.chartLocalization B S hS X.1 W).obj A) ≫
        (chartLocalizationPostcompIso B S hS X (g ≫ f)).inv.app A := by
  ext
  rfl

/-- `AlgebraicGeometry.Space.chartLocalizationPostcompIso_comp_inv_app` in the opposite
category, which is the form a presheaf consumes. -/
theorem chartLocalizationPostcompIso_comp_inv_app_op {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) (A : SmallEtale B S hS (chartSpace B S hS X W).1) :
    ((chartLocalizationPostcompIso B S hS X f).inv.app
          ((smallEtalePostcomp B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).obj A)).op ≫
        ((Over.map f).map ((chartLocalizationPostcompIso B S hS X g).inv.app A)).op =
      ((chartLocalizationPostcompIso B S hS X (g ≫ f)).inv.app A).op ≫
        ((Over.mapComp g f).inv.app
          ((SmallEtale.chartLocalization B S hS X.1 W).obj A)).op := by
  refine Quiver.Hom.unop_inj ?_
  ext
  rfl

/-! ### The coherence on sheaves -/

/-- **The restriction-along-equal-functors half of the dictionary is the isomorphism of
restriction functors induced by the comparison of Stacks 04M0.**  The second
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` that
`AlgebraicGeometry.Space.chartPostcompSheafIso` is built from is an identity isomorphism of
functors of sites, hence the identity. -/
theorem chartPostcompSheafIso_hom_eq {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hfc : (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U))
    (hfg' : (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)) :
    (chartPostcompSheafIso B S hS X f).hom =
      (@Functor.sheafPushforwardContinuousIso _ _ _ _ _ _
        (chartLocalizationPostcompIso B S hS X f) (Type (u + 1)) _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U) hfc hfg').hom := by
  have hu := isContinuous_chartLocalization_chartSpace B S hS X U
  have hv := isContinuous_chartLocalization_chartSpace B S hS X V
  have h : (chartPostcompSheafIso B S hS X f).hom =
      (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
          (chartLocalizationPostcompIso B S hS X f) (Type (u + 1)) _
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          ((SmallEtale.topology B S hS X.1).over U) _ hu hfg').hom ≫
        (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
          (Iso.refl (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)) (Type (u + 1)) _
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over V)
          ((SmallEtale.topology B S hS X.1).over U) hv _ hfg').inv := rfl
  have h1 : (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
        (chartLocalizationPostcompIso B S hS X f) (Type (u + 1)) _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        ((SmallEtale.topology B S hS X.1).over U) _ hu hfg').hom =
      (@Functor.sheafPushforwardContinuousIso _ _ _ _ _ _
        (chartLocalizationPostcompIso B S hS X f) (Type (u + 1)) _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U) hfc hfg').hom :=
    Functor.sheafPushforwardContinuousComp'_hom_eq (A := Type (u + 1))
      (J := SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (K := SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (L := (SmallEtale.topology B S hS X.1).over U) (instG := hu) (instFG := hfg')
      (instComp := hfc) (e := chartLocalizationPostcompIso B S hS X f)
  have h2 : (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
        (Iso.refl (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)) (Type (u + 1)) _
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over V)
        ((SmallEtale.topology B S hS X.1).over U) hv _ hfg').inv = 𝟙 _ :=
    Functor.sheafPushforwardContinuousComp'_refl_inv (A := Type (u + 1))
      (J := SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (K := (SmallEtale.topology B S hS X.1).over V)
      (L := (SmallEtale.topology B S hS X.1).over U)
      (F := SmallEtale.chartLocalization B S hS X.1 V) (G := Over.map f) (instF := hv)
      (instComp := hfg')
  rw [h, h1, h2]
  exact (Category.comp_id _).trans (by congr 1)

/-- Continuity of chartwise postcomposition followed by the comparison functor of
Stacks 04M0. -/
theorem isContinuous_smallEtalePostcomp_comp_chartLocalization {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) :
    (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    ((SmallEtale.topology B S hS X.1).over U)
    (smallEtalePostcomp_isContinuous B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f))
    (isContinuous_chartLocalization_chartSpace B S hS X U)

/-- Continuity of the comparison functor of Stacks 04M0 at a chart followed by the slice
functor along a morphism of charts. -/
theorem isContinuous_chartLocalization_comp_overMap {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    ((SmallEtale.topology B S hS X.1).over V)
    ((SmallEtale.topology B S hS X.1).over U)
    (isContinuous_chartLocalization_chartSpace B S hS X V) _

/-- The presheaf component of
`AlgebraicGeometry.Space.chartPostcompSheafIso`: restriction along the component of the
comparison of Stacks 04M0. -/
theorem chartPostcompSheafIso_hom_app_hom_app {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (T : Sheaf ((SmallEtale.topology B S hS X.1).over U) (Type (u + 1)))
    (A : (SmallEtale B S hS (chartSpace B S hS X V).1)ᵒᵖ) :
    ((chartPostcompSheafIso B S hS X f).hom.app T).hom.app A =
      T.obj.map ((chartLocalizationPostcompIso B S hS X f).inv.app (Opposite.unop A)).op := by
  rw [chartPostcompSheafIso_hom_eq B S hS X f
    (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X f)
    (isContinuous_chartLocalization_comp_overMap B S hS X f)]
  rfl

/-- The presheaf component of the inverse of the slice-pullback composition isomorphism. -/
theorem overMapPullbackComp_inv_app_hom_app {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) (T : Sheaf ((SmallEtale.topology B S hS X.1).over U) (Type (u + 1)))
    (A : (Over W)ᵒᵖ) :
    (((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app T).hom.app
        A =
      T.obj.map ((Over.mapComp g f).inv.app (Opposite.unop A)).op := by
  have instmc : (Over.map g ⋙ Over.map f).IsContinuous
      ((SmallEtale.topology B S hS X.1).over W) ((SmallEtale.topology B S hS X.1).over U) :=
    @Functor.isContinuous_comp _ _ _ _ _ _ _ _
      ((SmallEtale.topology B S hS X.1).over W)
      ((SmallEtale.topology B S hS X.1).over V)
      ((SmallEtale.topology B S hS X.1).over U) _ _
  have hQ : ((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).inv =
      (@Functor.sheafPushforwardContinuousIso _ _ _ _ _ _ (Over.mapComp g f) (Type (u + 1)) _
        ((SmallEtale.topology B S hS X.1).over W)
        ((SmallEtale.topology B S hS X.1).over U) _ instmc).hom :=
    Functor.sheafPushforwardContinuousComp'_inv_eq (A := Type (u + 1))
      (J := (SmallEtale.topology B S hS X.1).over W)
      (K := (SmallEtale.topology B S hS X.1).over V)
      (L := (SmallEtale.topology B S hS X.1).over U) (instComp := instmc)
      (e := (Over.mapComp g f).symm)
  rw [hQ]
  rfl

/-- **The restriction-along-equal-functors half of the dictionary is compatible with the
composition isomorphisms.**  This is the sheaf-level form of
`AlgebraicGeometry.Space.chartLocalizationPostcompIso_comp`: every isomorphism involved is
restriction along an isomorphism of functors of sites, so its component at a sheaf and an object
is that sheaf applied to the component of the site isomorphism, and the identity is the
site-level one read through the sheaf. -/
theorem chartPostcompSheafIso_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V)
    (T : Sheaf ((SmallEtale.topology B S hS X.1).over U) (Type (u + 1))) :
    ((smallEtalePostcomp B S hS (chartMap B S hS X g)
            (isEtale_chartMap B S hS X g)).sheafPushforwardContinuous (Type (u + 1))
              (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
              (SmallEtale.topology B S hS (chartSpace B S hS X V).1)).map
          ((chartPostcompSheafIso B S hS X f).hom.app T) ≫
        (chartPostcompSheafIso B S hS X g).hom.app
          (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj T) =
      (chartPostcompSheafIso B S hS X (g ≫ f)).hom.app T ≫
        (chartSliceSheafEquiv B S hS X W).functor.map
          (((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app
            T) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun A => ?_))
  have hlast : ((chartSliceSheafEquiv B S hS X W).functor.map
          (((SmallEtale.topology B S hS X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app
            T)).hom.app A =
      T.obj.map ((Over.mapComp g f).inv.app
        ((SmallEtale.chartLocalization B S hS X.1 W).obj (Opposite.unop A))).op :=
    overMapPullbackComp_inv_app_hom_app B S hS X f g T
      (Opposite.op ((SmallEtale.chartLocalization B S hS X.1 W).obj (Opposite.unop A)))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app,
    chartPostcompSheafIso_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op, hlast]
  exact (T.obj.map_comp _ _).symm.trans
    ((congrArg T.obj.map
      (chartLocalizationPostcompIso_comp_inv_app_op B S hS X f g (Opposite.unop A))).trans
      (T.obj.map_comp _ _))

/-- The transport that the chart-level bridge carries is the identity: the represented morphism
of a composite of chart morphisms is definitionally the composite of the represented
morphisms. -/
theorem eqToHom_smallEtalePostcomp_chartMap_congr {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    (eqToHom (smallEtalePostcomp_sheafPushforwardContinuous_congr B S hS
      (isEtale_chartMap B S hS X (g ≫ f)) (isEtale_chartMap_comp B S hS X f g)
      (chartMap_comp B S hS X f g).symm)) = 𝟙 _ :=
  eqToHom_refl _ _

/-- **The chart-to-slice dictionary is compatible with the composition isomorphisms.**

The two readings of the chartwise inverse image — along the structure of the charts and along
the slices of the small étale site of `X` — are carried into one another by the dictionary
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso` compatibly with the composition
comparisons `AlgebraicGeometry.Space.chartInverseImageComp` and
`CategoryTheory.GrothendieckTopology.overMapPullbackComp`.

This is the chart-level bridge of Stacks 03LQ against Stacks 03G2, part (3)
(`AlgebraicGeometry.Space.chartInverseImageComp_inverseImageIso`) composed with the coherence of
the restriction-along-equal-functors half (`AlgebraicGeometry.Space.chartPostcompSheafIso_comp`),
the two being joined by the naturality of the comparison of Stacks 03LQ. -/
theorem chartInverseImage_overMapPullbackIso_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V)
    (T : Sheaf ((SmallEtale.topology B S hS X.1).over U) (Type (u + 1))) :
    (chartInverseImage B S hS X g).map
          ((chartInverseImage_overMapPullbackIso B S hS X f).hom.app T) ≫
        (chartInverseImage_overMapPullbackIso B S hS X g).hom.app (((SmallEtale.topology B S hS
          X.1).overMapPullback (Type (u + 1)) f).obj T) =
      (chartInverseImageComp B S hS X f g).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj T)
        ≫
        (chartInverseImage_overMapPullbackIso B S hS X (g ≫ f)).hom.app T ≫
          ((chartSliceSheafEquiv B S hS X W).functor).map (((SmallEtale.topology B S hS
            X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app T) := by
  have hAf : (chartInverseImage B S hS X g).map
        ((chartInverseImage_overMapPullbackIso B S hS X f).hom.app T) =
      (chartInverseImage B S hS X g).map ((smallToposMorphism_inverseImageIso B S hS
          (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).hom.app
          ((chartSliceSheafEquiv B S hS X U).functor.obj T)) ≫
        (chartInverseImage B S hS X g).map
          ((chartPostcompSheafIso B S hS X f).hom.app T) :=
    (chartInverseImage B S hS X g).map_comp _ _
  have hAg : (chartInverseImage_overMapPullbackIso B S hS X g).hom.app (((SmallEtale.topology B S hS
    X.1).overMapPullback (Type (u + 1)) f).obj T) =
      (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X g)
      (isEtale_chartMap B S hS X g)).hom.app (((chartSliceSheafEquiv B S hS X V).functor).obj
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj T)) ≫
        (chartPostcompSheafIso B S hS X g).hom.app (((SmallEtale.topology B S hS
          X.1).overMapPullback (Type (u + 1)) f).obj T) := rfl
  have hAgf : (chartInverseImage_overMapPullbackIso B S hS X (g ≫ f)).hom.app T =
      (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X (g ≫ f))
      (isEtale_chartMap B S hS X (g ≫ f))).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj T)
        ≫
        (chartPostcompSheafIso B S hS X (g ≫ f)).hom.app T := rfl
  have hnat : (chartInverseImage B S hS X g).map ((chartPostcompSheafIso B S hS X f).hom.app T) ≫
        (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X g)
      (isEtale_chartMap B S hS X g)).hom.app (((chartSliceSheafEquiv B S hS X V).functor).obj
        (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj T)) =
      (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X g)
      (isEtale_chartMap B S hS X g)).hom.app (((smallEtalePostcomp B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)).obj ((chartSliceSheafEquiv B S hS X
          U).functor.obj T)) ≫
        ((smallEtalePostcomp B S hS (chartMap B S hS X g)
      (isEtale_chartMap B S hS X g)).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)).map ((chartPostcompSheafIso B S hS X
          f).hom.app T) :=
    (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X g)
      (isEtale_chartMap B S hS X g)).hom.naturality _
  have hbr : (chartInverseImage B S hS X g).map ((smallToposMorphism_inverseImageIso B S hS
    (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj T)) ≫
        (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X g)
      (isEtale_chartMap B S hS X g)).hom.app (((smallEtalePostcomp B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)).obj ((chartSliceSheafEquiv B S hS X
          U).functor.obj T)) =
      (chartInverseImageComp B S hS X f g).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj T)
        ≫
        ((smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X (g ≫ f))
      (isEtale_chartMap B S hS X (g ≫ f))).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj T)
        ≫ (eqToHom (smallEtalePostcomp_sheafPushforwardContinuous_congr B S hS
      (isEtale_chartMap B S hS X (g ≫ f)) (isEtale_chartMap_comp B S hS X f g)
      (chartMap_comp B S hS X f g).symm)).app ((chartSliceSheafEquiv B S hS X U).functor.obj T)) :=
    NatTrans.congr_app (chartInverseImageComp_inverseImageIso B S hS X f g)
      ((chartSliceSheafEquiv B S hS X U).functor.obj T)
  have heq : (eqToHom (smallEtalePostcomp_sheafPushforwardContinuous_congr B S hS
      (isEtale_chartMap B S hS X (g ≫ f)) (isEtale_chartMap_comp B S hS X f g)
      (chartMap_comp B S hS X f g).symm)).app ((chartSliceSheafEquiv B S hS X U).functor.obj T) = 𝟙
        _ :=
    NatTrans.congr_app (eqToHom_smallEtalePostcomp_chartMap_congr B S hS X f g)
      ((chartSliceSheafEquiv B S hS X U).functor.obj T)
  have hcps := chartPostcompSheafIso_comp B S hS X f g T
  rw [hAf, hAg, hAgf]
  exact comp_bridge_rearrange
    ((chartInverseImage B S hS X g).map ((smallToposMorphism_inverseImageIso B S hS (chartMap B S hS
      X f)
        (isEtale_chartMap B S hS X f)).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj T)))
    ((chartInverseImage B S hS X g).map ((chartPostcompSheafIso B S hS X f).hom.app T))
    ((smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X g)
        (isEtale_chartMap B S hS X g)).hom.app (((chartSliceSheafEquiv B S hS X V).functor).obj
          (((SmallEtale.topology B S hS X.1).overMapPullback (Type (u + 1)) f).obj T)))
    ((chartPostcompSheafIso B S hS X g).hom.app (((SmallEtale.topology B S hS X.1).overMapPullback
      (Type (u + 1)) f).obj T))
    ((chartInverseImageComp B S hS X f g).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj T))
    ((smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X (g ≫ f))
        (isEtale_chartMap B S hS X (g ≫ f))).hom.app ((chartSliceSheafEquiv B S hS X U).functor.obj
          T))
    ((eqToHom (smallEtalePostcomp_sheafPushforwardContinuous_congr B S hS
        (isEtale_chartMap B S hS X (g ≫ f)) (isEtale_chartMap_comp B S hS X f g)
        (chartMap_comp B S hS X f g).symm)).app ((chartSliceSheafEquiv B S hS X U).functor.obj T))
    ((chartPostcompSheafIso B S hS X (g ≫ f)).hom.app T)
    (((chartSliceSheafEquiv B S hS X W).functor).map (((SmallEtale.topology B S hS
      X.1).overMapPullbackComp (Type (u + 1)) g f).inv.app T))
    hnat hbr hcps
    ((chartPostcompSheafIso B S hS X (g ≫ f)).hom.app T)
    ((congrArg (fun z => z ≫ (chartPostcompSheafIso B S hS X (g ≫ f)).hom.app T) heq).trans
      (Category.id_comp _))

/-! ### The dictionary square for the structure morphism of a chart -/

/-- Postcomposition along two equal étale morphisms of algebraic spaces is the same functor of
small étale sites. -/
theorem smallEtalePostcomp_congr {A C : AlgebraicSpaces B S hS} {k k' : A ⟶ C}
    (hk : IsEtale B S hS k.hom) (hk' : IsEtale B S hS k'.hom) (e : k = k') :
    smallEtalePostcomp B S hS k hk = smallEtalePostcomp B S hS k' hk' := by
  subst e
  rfl

/-- The presheaf component of the transport of restriction of sheaves along an equality of
continuous functors of sites: it is the sheaf applied to the transport of objects. -/
theorem eqToHom_sheafPushforwardContinuous_app_hom_app {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] {G G' : C ⥤ D} (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] [G'.IsContinuous J K] (h : G = G')
    (M : Sheaf K (Type (u + 1))) (A : Cᵒᵖ) :
    ((eqToHom (sheafPushforwardContinuous_eq_of_functor_eq J K h)).app M).hom.app A =
      M.obj.map (eqToHom (Functor.congr_obj h.symm (Opposite.unop A))).op := by
  subst h
  rw [show eqToHom (sheafPushforwardContinuous_eq_of_functor_eq J K (rfl : G = G)) = 𝟙 _ from
    eqToHom_refl _ _]
  simp
  rfl

/-- The morphism of algebraic spaces represented by a morphism of charts, followed by the
structure morphism of the target chart, is étale: it *is* the structure morphism of the source
chart. -/
theorem isEtale_chartMap_comp_chartToSpace {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    IsEtale B S hS (chartMap B S hS X f ≫ chartToSpace B S hS X U).hom := by
  rw [chartMap_comp_chartToSpace]
  exact isEtale_chartToSpace B S hS X V

/-- `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_comp` with the composite of the
two étale morphisms named by a third morphism and an equality, and the comparisons transported
along that equality.  This is the shape the chart constructions present: the composite of a
morphism of charts with the structure morphism of the target chart is *equal* to the structure
morphism of the source chart, not literally it. -/
theorem smallToposMorphism_inverseImageIso_comp' {A C Y : AlgebraicSpaces B S hS} (k : A ⟶ C)
    (l : C ⟶ Y) (m : A ⟶ Y) (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom)
    (hm : IsEtale B S hS m.hom) (hkl : IsEtale B S hS (k ≫ l).hom) (e : k ≫ l = m) :
    Functor.whiskerRight (smallToposMorphism_inverseImageIso B S hS l hl).hom
        (smallToposMorphism B S hS k).inverseImage ≫
      Functor.whiskerLeft
        ((smallEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS C.1) (SmallEtale.topology B S hS Y.1))
        (smallToposMorphism_inverseImageIso B S hS k hk).hom =
    ((smallToposMorphism_comp_inverseImage B S hS k l).inv ≫
        eqToHom (congrArg (fun z : A ⟶ Y => (smallToposMorphism B S hS z).inverseImage) e)) ≫
      (smallToposMorphism_inverseImageIso B S hS m hm).hom ≫
        eqToHom (sheafPushforwardContinuous_eq_of_functor_eq
          (SmallEtale.topology B S hS A.1) (SmallEtale.topology B S hS Y.1)
          (smallEtalePostcomp_congr B S hS hm hkl e.symm)) := by
  subst e
  rw [show eqToHom (congrArg (fun z : A ⟶ Y => (smallToposMorphism B S hS z).inverseImage)
      (rfl : k ≫ l = k ≫ l)) = 𝟙 _ from eqToHom_refl _ _,
    show eqToHom (sheafPushforwardContinuous_eq_of_functor_eq
      (SmallEtale.topology B S hS A.1) (SmallEtale.topology B S hS Y.1)
      (smallEtalePostcomp_congr B S hS hm hkl (rfl : k ≫ l = k ≫ l).symm)) = 𝟙 _ from
      eqToHom_refl _ _,
    Category.comp_id, Category.comp_id]
  exact (Iso.eq_inv_comp _).mpr
    (smallToposMorphism_inverseImageIso_comp B S hS k l hk hl hm)

/-- **The bridge of Stacks 03LQ against Stacks 03G2, part (3), at the structure morphism of a
chart.**  The comparison of Stacks 03LQ for the structure morphism of a chart `U`, whiskered by
the chartwise inverse image along a morphism `f : V ⟶ U` of charts, followed by the comparison
for the represented morphism of `f`, is `AlgebraicGeometry.Space.chartRestrictionComp` followed by
the comparison for the structure morphism of `V` — the latter transported along
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`.

This is the companion of `AlgebraicGeometry.Space.chartInverseImageComp_inverseImageIso`; unlike
it, the transport is *not* the identity, because
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace` is `CategoryTheory.Over.w`, a propositional
field, and not a definitional equality. -/
theorem chartRestrictionComp_inverseImageIso {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    Functor.whiskerRight (smallToposMorphism_inverseImageIso B S hS
          (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)).hom
        (chartInverseImage B S hS X f) ≫
      Functor.whiskerLeft
        ((smallEtalePostcomp B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
            (SmallEtale.topology B S hS X.1))
        (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).hom =
    (chartRestrictionComp B S hS X f).hom ≫
      (smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).hom ≫
        eqToHom (sheafPushforwardContinuous_eq_of_functor_eq
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          (SmallEtale.topology B S hS X.1)
          (smallEtalePostcomp_congr B S hS (isEtale_chartToSpace B S hS X V)
            (isEtale_chartMap_comp_chartToSpace B S hS X f)
            (chartMap_comp_chartToSpace B S hS X f).symm)) := by
  have hcIC : (chartRestrictionComp B S hS X f).hom =
      (smallToposMorphism_comp_inverseImage B S hS (chartMap B S hS X f)
          (chartToSpace B S hS X U)).inv ≫
        eqToHom (congrArg (fun z : chartSpace B S hS X V ⟶ X =>
          (smallToposMorphism B S hS z).inverseImage)
          (chartMap_comp_chartToSpace B S hS X f)) := rfl
  rw [hcIC]
  exact smallToposMorphism_inverseImageIso_comp' B S hS (chartMap B S hS X f)
    (chartToSpace B S hS X U) (chartToSpace B S hS X V) (isEtale_chartMap B S hS X f)
    (isEtale_chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X V)
    (isEtale_chartMap_comp_chartToSpace B S hS X f) (chartMap_comp_chartToSpace B S hS X f)

/-- A morphism of the small étale site of an algebraic space between two *equal* étale charts
whose underlying morphism of the big fppf site is the transport is the transport: morphisms of the
small étale site are determined by their underlying morphisms. -/
theorem eq_eqToHom_of_left_eq_id {Y : AlgebraicSpaces B S hS} {A A' : SmallEtale B S hS Y.1}
    (α : A ⟶ A') (h : A = A')
    (hα : α.hom.left =
      eqToHom (congrArg (fun Z : SmallEtale B S hS Y.1 => Z.obj.left) h)) : α = eqToHom h := by
  subst h
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
  simpa using hα

/-- The comparison of Stacks 04M0 at two charts turns the slice projection of the larger chart
into the one of the smaller: the component of
`AlgebraicGeometry.Space.chartLocalizationPostcompIso` has the identity for its underlying
morphism of the big fppf site, so read in the small étale site of `X` it is the transport along
`AlgebraicGeometry.Space.chartMap_comp_chartToSpace`. -/
theorem chartLocalizationPostcompIso_inv_app_left_comp_eqToHom {V U : SmallEtale B S hS X.1}
    (f : V ⟶ U) (A : SmallEtale B S hS (chartSpace B S hS X V).1) :
    ((chartLocalizationPostcompIso B S hS X f).inv.app A).left ≫
        eqToHom (Functor.congr_obj (smallEtalePostcomp_congr B S hS
          (isEtale_chartToSpace B S hS X V)
          (isEtale_chartMap_comp_chartToSpace B S hS X f)
          (chartMap_comp_chartToSpace B S hS X f).symm).symm A) = 𝟙 _ :=
  have h1 : ((chartLocalizationPostcompIso B S hS X f).inv.app A).left =
      eqToHom (Functor.congr_obj (smallEtalePostcomp_congr B S hS
        (isEtale_chartToSpace B S hS X V)
        (isEtale_chartMap_comp_chartToSpace B S hS X f)
        (chartMap_comp_chartToSpace B S hS X f).symm) A) :=
    eq_eqToHom_of_left_eq_id B S hS _ _ (eqToHom_refl _ _).symm
  ((congrArg (fun z => z ≫ eqToHom (Functor.congr_obj (smallEtalePostcomp_congr B S hS
      (isEtale_chartToSpace B S hS X V)
      (isEtale_chartMap_comp_chartToSpace B S hS X f)
      (chartMap_comp_chartToSpace B S hS X f).symm).symm A)) h1).trans
    (eqToHom_trans _ _)).trans (eqToHom_refl _ _)

/-- **The transport of the bridge cancels against the restriction-along-equal-functors half of
the dictionary.**  The transport along `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` that
`AlgebraicGeometry.Space.chartRestrictionComp_inverseImageIso` carries is inverse to the
component of `AlgebraicGeometry.Space.chartPostcompSheafIso` at the restriction of a sheaf to the
slice. -/
theorem eqToHom_comp_chartPostcompSheafIso {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (eqToHom (sheafPushforwardContinuous_eq_of_functor_eq
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          (SmallEtale.topology B S hS X.1)
          (smallEtalePostcomp_congr B S hS (isEtale_chartToSpace B S hS X V)
            (isEtale_chartMap_comp_chartToSpace B S hS X f)
            (chartMap_comp_chartToSpace B S hS X f).symm))).app F ≫
        (chartPostcompSheafIso B S hS X f).hom.app (F.over U) = 𝟙 _ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun A => ?_))
  have ha := eqToHom_sheafPushforwardContinuous_app_hom_app
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1) (SmallEtale.topology B S hS X.1)
    (smallEtalePostcomp_congr B S hS (isEtale_chartToSpace B S hS X V)
      (isEtale_chartMap_comp_chartToSpace B S hS X f)
      (chartMap_comp_chartToSpace B S hS X f).symm) F A
  have hb := chartPostcompSheafIso_hom_app_hom_app B S hS X f (F.over U) A
  have hsite := chartLocalizationPostcompIso_inv_app_left_comp_eqToHom B S hS X f (Opposite.unop A)
  exact presheaf_map_comp_eq_id F.obj
    (eqToHom (Functor.congr_obj (smallEtalePostcomp_congr B S hS
      (isEtale_chartToSpace B S hS X V)
      (isEtale_chartMap_comp_chartToSpace B S hS X f)
      (chartMap_comp_chartToSpace B S hS X f).symm).symm (Opposite.unop A)))
    (((chartLocalizationPostcompIso B S hS X f).inv.app (Opposite.unop A)).left) _ _ ha hb hsite

/-- The dictionary for the structure morphism of a chart is the comparison of Stacks 03LQ with
nothing further: the `CategoryTheory.Functor.sheafPushforwardContinuousComp'` it is built from is
one of an identity isomorphism of functors of sites, hence the identity. -/
theorem chartRestriction_overPullbackIso_hom (U : SmallEtale B S hS X.1) :
    (chartRestriction_overPullbackIso B S hS X U).hom =
      (smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).hom := by
  have hu := isContinuous_chartLocalization_chartSpace B S hS X U
  have hfg : (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (SmallEtale.topology B S hS X.1) :=
    smallEtalePostcomp_isContinuous B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)
  have hinv := Functor.sheafPushforwardContinuousComp'_refl_inv (A := Type (u + 1))
    (J := SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (K := (SmallEtale.topology B S hS X.1).over U) (L := SmallEtale.topology B S hS X.1)
    (F := SmallEtale.chartLocalization B S hS X.1 U) (G := Over.forget U) (instF := hu)
    (instComp := hfg)
  exact (congrArg (fun z => (smallToposMorphism_inverseImageIso B S hS
      (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)).hom ≫ z) hinv).trans
    (Category.comp_id _)

/-- The slice-side comparison of the restrictions of a sheaf along a morphism of charts is the
identity: restriction to the slice at the target, further restricted along
`CategoryTheory.Over.map`, is restriction to the slice at the source, as the same functor of
sites. -/
theorem pushforwardOverMapIso_hom_eq_id {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (F.pushforwardOverMapIso f).hom = 𝟙 _ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl))

/-- **The chart-to-slice dictionary is compatible with the composition isomorphisms, at the
structure morphism of a chart.**

Restriction of a sheaf on the small étale site of `X` to a chart `U`, read as restriction to the
slice `X_étale/U` by `AlgebraicGeometry.Space.chartRestriction_overPullbackIso`, then restricted
along a morphism `f : V ⟶ U` of charts, agrees with restriction to the chart `V` read as
restriction to the slice `X_étale/V`: the dictionary carries
`AlgebraicGeometry.Space.chartRestrictionComp` to `CategoryTheory.Sheaf.pushforwardOverMapIso`.

This is the second of the dictionary squares Stacks 03LS owes, the companion of
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp`.  It is the bridge
`AlgebraicGeometry.Space.chartRestrictionComp_inverseImageIso` together with the cancellation
`AlgebraicGeometry.Space.eqToHom_comp_chartPostcompSheafIso` of the transport that bridge
carries. -/
theorem chartRestriction_overPullbackIso_comp {V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (chartInverseImage B S hS X f).map
          ((chartRestriction_overPullbackIso B S hS X U).hom.app F) ≫
        (chartInverseImage_overMapPullbackIso B S hS X f).hom.app (F.over U) ≫
          (chartSliceSheafEquiv B S hS X V).functor.map (F.pushforwardOverMapIso f).hom =
      (chartRestrictionComp B S hS X f).hom.app F ≫
        (chartRestriction_overPullbackIso B S hS X V).hom.app F := by
  have hηU : (chartInverseImage B S hS X f).map
        ((chartRestriction_overPullbackIso B S hS X U).hom.app F) =
      (chartInverseImage B S hS X f).map
        ((smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).hom.app F) :=
    congrArg (chartInverseImage B S hS X f).map
      (NatTrans.congr_app (chartRestriction_overPullbackIso_hom B S hS X U) F)
  have hηV : (chartRestriction_overPullbackIso B S hS X V).hom.app F =
      (smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).hom.app F :=
    NatTrans.congr_app (chartRestriction_overPullbackIso_hom B S hS X V) F
  have hpush : (chartSliceSheafEquiv B S hS X V).functor.map (F.pushforwardOverMapIso f).hom =
      𝟙 _ :=
    (congrArg (chartSliceSheafEquiv B S hS X V).functor.map
        (pushforwardOverMapIso_hom_eq_id B S hS X f F)).trans
      ((chartSliceSheafEquiv B S hS X V).functor.map_id _)
  have hd : (chartInverseImage_overMapPullbackIso B S hS X f).hom.app (F.over U) =
      (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).hom.app
            ((chartSliceSheafEquiv B S hS X U).functor.obj (F.over U)) ≫
        (chartPostcompSheafIso B S hS X f).hom.app (F.over U) := rfl
  have hbr : (chartInverseImage B S hS X f).map
          ((smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X U)
            (isEtale_chartToSpace B S hS X U)).hom.app F) ≫
        (smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).hom.app
            ((chartSliceSheafEquiv B S hS X U).functor.obj (F.over U)) =
      (chartRestrictionComp B S hS X f).hom.app F ≫
        (smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).hom.app F ≫
          (eqToHom (sheafPushforwardContinuous_eq_of_functor_eq
            (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
            (SmallEtale.topology B S hS X.1)
            (smallEtalePostcomp_congr B S hS (isEtale_chartToSpace B S hS X V)
              (isEtale_chartMap_comp_chartToSpace B S hS X f)
              (chartMap_comp_chartToSpace B S hS X f).symm))).app F :=
    NatTrans.congr_app (chartRestrictionComp_inverseImageIso B S hS X f) F
  rw [hηU, hηV, hd]
  exact comp_bridge_cancel
    ((chartInverseImage B S hS X f).map
      ((smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).hom.app F))
    ((smallToposMorphism_inverseImageIso B S hS (chartMap B S hS X f)
      (isEtale_chartMap B S hS X f)).hom.app
        ((chartSliceSheafEquiv B S hS X U).functor.obj (F.over U)))
    ((chartPostcompSheafIso B S hS X f).hom.app (F.over U))
    ((chartSliceSheafEquiv B S hS X V).functor.map (F.pushforwardOverMapIso f).hom)
    ((chartRestrictionComp B S hS X f).hom.app F)
    ((smallToposMorphism_inverseImageIso B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).hom.app F)
    ((eqToHom (sheafPushforwardContinuous_eq_of_functor_eq
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS X.1)
      (smallEtalePostcomp_congr B S hS (isEtale_chartToSpace B S hS X V)
        (isEtale_chartMap_comp_chartToSpace B S hS X f)
        (chartMap_comp_chartToSpace B S hS X f).symm))).app F)
    hbr (eqToHom_comp_chartPostcompSheafIso B S hS X f F) hpush

end AlgebraicGeometry.Space

end

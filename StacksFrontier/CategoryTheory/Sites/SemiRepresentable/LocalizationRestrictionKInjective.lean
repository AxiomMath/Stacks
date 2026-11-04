module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.KInjective
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact

/-!
# Stacks 0D88 for restriction along the localization functor

Let `(C, J)` be a site and `L = ⨿ i, L.obj i` a semi-representable object of `C`. Stacks 0D88 is
available in this library as
`CategoryTheory.SemiRepresentable.isKInjective_localizationInverseImage_mapHomologicalComplex`,
stated for `CategoryTheory.SemiRepresentable.localizationInverseImage`: the inverse image
`j^{-1} : Ab(C) ⥤ Ab(C/L)` presented as the family of the one-object inverse images
`CategoryTheory.GrothendieckTopology.overPullback`, reassembled by the canonical equivalence
`CategoryTheory.SemiRepresentable.formalCoproductSliceSheavesEquivalence`.

Every consumer of that statement which comes from the simplicial theory meets the same functor in
a different presentation: as restriction along the localization functor
`j_L = CategoryTheory.SemiRepresentable.componentOverForget`, that is as
`CategoryTheory.Functor.sheafPushforwardContinuous` of `j_L`. The two presentations agree on the
nose once the equivalence is inserted — restricting along `j_L` and then to the component indexed
by `i` is restriction along `Over.forget (L.obj i)`, by definition of `componentOverForget` as a
`CategoryTheory.Sigma.desc` — so the comparison below is the unit of the equivalence whiskered
with restriction, and the identification of the two composites is a `rfl`.

The second statement carries the result across an arbitrary *spelling* of the componentwise
localized topology. The simplicial-site situation of a simplicial semi-representable object
carries its component topologies as `topologyOfCoverings` of the slice coverings, which is only
propositionally equal to `componentwiseTopology` (that equality is
`CategoryTheory.SimplicialSemiRepresentable.componentTopology_eq`), and a topology occurs in the
*type* of a complex of sheaves. Taking the equality as a hypothesis and substituting it is what
makes the result usable there.

## Main definitions

* `CategoryTheory.SemiRepresentable.sheafPushforwardContinuousLocalizationInverseImageIso`:
  restriction along `j_L` is the localization inverse image.
* `CategoryTheory.SemiRepresentable.localizationPushforwardComplexIso`: the same on a complex of
  abelian sheaves.

## Main results

* `CategoryTheory.SemiRepresentable.isKInjective_sheafPushforwardContinuous_componentOverForget`:
  **Stacks 0D88 for restriction along `j_L`.**
* `CategoryTheory.SemiRepresentable`
  `.isKInjective_sheafPushforwardContinuous_componentOverForget_ofEq`: the same at any topology
  on `C/L` equal to the componentwise localized one.

## Implementation notes

No tag attribute is placed: Stacks 0D88 is already carried, for the inverse image of abelian
sheaves along the localization at a semi-representable object, by
`CategoryTheory.SemiRepresentable.isKInjective_localizationInverseImage_mapHomologicalComplex`,
and what is below is that statement read at a second presentation of the same functor.

The isomorphism of complexes is assembled from the components of the natural isomorphism by
`CategoryTheory.HomologicalComplex.Hom.isoOfComponents` rather than by
`CategoryTheory.NatIso.mapHomologicalComplex`, so that no additivity instance has to be found for
either functor beyond the ones the two `mapHomologicalComplex` applications already need.

## References

* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u' v'

namespace CategoryTheory.SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (L : FormalCoproduct.{u} C)

/-- **Restriction along the localization functor `j_L : C/L ⥤ C` is the localization inverse
image.** Restricting a sheaf along `j_L` and then to the component of `C/L` indexed by `i` is
restricting it along `Over.forget (L.obj i)`, because `j_L` is the `CategoryTheory.Sigma.desc` of
those forgetful functors; so restriction along `j_L` followed by the equivalence of
`CategoryTheory.SemiRepresentable.formalCoproductSliceSheavesEquivalence` is the family
`componentInverseImage` of the one-object inverse images, on the nose. The comparison is
therefore the unit of that equivalence. -/
def sheafPushforwardContinuousLocalizationInverseImageIso (A : Type u') [Category.{v'} A] :
    (componentOverForget L).sheafPushforwardContinuous A (componentwiseTopology J L) J ≅
      localizationInverseImage J L A :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (formalCoproductSliceSheavesEquivalence J L A).1.unitIso

/-- The comparison of `sheafPushforwardContinuousLocalizationInverseImageIso`, applied to every
term and every differential of a complex of abelian sheaves. -/
def localizationPushforwardComplexIso (I : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) :
    (localizationInverseImageMapHomologicalComplex J L).obj I ≅
      (((componentOverForget L).sheafPushforwardContinuous AddCommGrpCat.{u}
        (componentwiseTopology J L) J).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((sheafPushforwardContinuousLocalizationInverseImageIso J L
      AddCommGrpCat.{u}).app (I.X n)).symm)
    (fun i j _ => ((sheafPushforwardContinuousLocalizationInverseImageIso J L
      AddCommGrpCat.{u}).inv.naturality (I.d i j)).symm)

/-- **Stacks 0D88 for restriction along the localization functor.** Restriction along
`j_L : C/L ⥤ C` sends a K-injective complex of abelian sheaves on `(C, J)` to a K-injective
complex of abelian sheaves on `C/L`.

This is `isKInjective_localizationInverseImage_mapHomologicalComplex` carried across
`localizationPushforwardComplexIso`. -/
theorem isKInjective_sheafPushforwardContinuous_componentOverForget
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((componentOverForget L).sheafPushforwardContinuous AddCommGrpCat.{u}
        (componentwiseTopology J L) J).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := isKInjective_localizationInverseImage_mapHomologicalComplex J L I
  CochainComplex.isKInjective_of_iso (localizationPushforwardComplexIso J L I)

/-- **Stacks 0D88 for restriction along the localization functor, at any spelling of the
componentwise localized topology.** The topology of `C/L` occurs in the type of a complex of
sheaves on it, so a presentation of that topology which is only propositionally equal to
`componentwiseTopology` cannot be rewritten in place; the equality is taken as a hypothesis and
substituted instead. -/
theorem isKInjective_sheafPushforwardContinuous_componentOverForget_ofEq
    {T : GrothendieckTopology (ComponentOver L)}
    [(componentOverForget L).IsContinuous T J] (hT : T = componentwiseTopology J L)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((componentOverForget L).sheafPushforwardContinuous AddCommGrpCat.{u} T
        J).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  subst hT
  exact isKInjective_sheafPushforwardContinuous_componentOverForget J L I

end CategoryTheory.SemiRepresentable

end

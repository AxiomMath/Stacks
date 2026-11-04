module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotNumericalImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Models of subfunctors of the Quot functor

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a quasi-coherent
`𝒪_X`-module.  A quotient of `F_T` is recorded by a subobject, so the Quot presheaf of Stacks 09TR
takes values one universe above the schemes of the site, and an algebraic space structure on it
is a statement about a *model*: a presheaf of the universe of the site whose universe lift is the
Quot presheaf.  The same holds for every subfunctor `G` of the Quot presheaf, for instance the
fibre product `Quot^Q_{F/X/B} = Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` of a condition `Q` on
`Coh_{X/B}`.

Every such subfunctor has a model,
`AlgebraicGeometry.Space.QuotSituation.SubfunctorModel.canonical`.
This file shows that if the inclusion `G ⟶ Quot_{F/X/B}` is representable (for instance by closed
immersions), then every model of `G` maps to every model of `Quot_{F/X/B}` by a representable
transformation.  So by Stacks 02WY a model of `G` is an
algebraic space as soon as a model of `Quot_{F/X/B}` is.

## Main results

* `AlgebraicGeometry.Space.QuotSitePresheafModel.relative_mapFrom`: a property of morphisms of the
  site holding for the represented fibre products of a morphism into the Quot presheaf holds for
  its transport into a model.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isAlgebraicSpace_of_relative_ι`: a model of a
  subfunctor whose inclusion is representable is an algebraic space as soon as a model of the Quot
  presheaf is (Stacks 02WY).
* `Space.QuotSituation.isAlgebraicSpace_subfunctorModel_quotCondition_of_isFlatClosedCondition`:
  in particular for the fibre product of `Quot_{F/X/B}` with a flat closed substack of `Coh_{X/B}`.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS} (M : QuotSitePresheafModel D)

/-- A property of morphisms of schemes of the site which holds for the represented fibre products
of a morphism into the universe-lifted Quot presheaf also holds for its transport into a model:
the universe lift reflects the fibre products and is faithful. -/
theorem relative_mapFrom (P : MorphismProperty (BigFppfOver B S hS))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⋙ uliftFunctor.{u + 1, u} ⟶ D.quotSitePresheaf)
    (hp : P.relative uliftYoneda.{u + 1} p) :
    P.presheaf (M.mapFrom p) := by
  let L := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1, u}
  have hmap : L.map (M.mapFrom p) = p ≫ M.iso.inv := by
    ext T z
    cases z
    rfl
  have hp' : P.relative (yoneda ⋙ L) (L.map (M.mapFrom p)) := by
    rw [hmap]
    exact MorphismProperty.RespectsIso.postcomp _ M.iso.inv p hp
  constructor
  · intro a g
    obtain ⟨b, s, t, ht⟩ := hp'.1 (L.map g)
    have ht' : IsPullback (L.map (L.preimage t)) (L.map (yoneda.map s))
        (L.map (M.mapFrom p)) (L.map g) := by
      simpa using ht
    exact ⟨b, s, L.preimage t, ht'.of_map_of_faithful L⟩
  · intro a b g t s ht
    exact hp'.2 (L.map g) (L.map t) s (ht.map L)

/-- **A model of a subfunctor with representable inclusion is an algebraic space when a model of
the Quot presheaf is** (Stacks 02WY).  If the inclusion of a subfunctor `G` of the Quot presheaf
is representable by morphisms with some property `P`, and `F` is a presheaf of the universe of the
site whose universe lift is `G` (an `AlgebraicGeometry.Space.QuotSituation.SubfunctorModel`),
then `F` maps to the model `M` by a representable transformation,
so `F` is an algebraic space as soon as `M` is. -/
theorem isAlgebraicSpace_of_relative_ι {P : MorphismProperty (BigFppfOver B S hS)}
    {G : Subfunctor D.quotSitePresheaf} (hG : P.relative uliftYoneda.{u + 1} G.ι)
    (F : D.SubfunctorModel G) (hM : IsAlgebraicSpace B S hS M.presheaf) :
    IsAlgebraicSpace B S hS F.presheaf := by
  have hP : (⊤ : MorphismProperty (BigFppfOver B S hS)).relative uliftYoneda.{u + 1}
      (F.iso.hom ≫ G.ι) :=
    MorphismProperty.RespectsIso.precomp _ F.iso.hom G.ι ⟨hG.1, fun _ _ _ _ _ _ => trivial⟩
  exact isAlgebraicSpace_of_relativelyRepresentable B S hS (M.mapFrom (F.iso.hom ≫ G.ι))
    (M.relative_mapFrom ⊤ _ hP).rep hM

end QuotSitePresheafModel

namespace QuotSituation

variable (D : QuotSituation B S hS) {Q : CoherentObject D.toCoherentSituation → Prop}

/-- **The fibre product with a flat closed substack of `Coh_{X/B}` is an algebraic space when
`Quot_{F/X/B}` is.**  If a condition `Q` on the objects of `Coh_{X/B}`, inherited along its
morphisms, cuts out a flat closed substack, then every model of the subfunctor
`Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` of the Quot presheaf is an algebraic space as soon as
some model of the Quot presheaf is: its inclusion is representable by flat closed immersions. -/
theorem isAlgebraicSpace_subfunctorModel_quotCondition_of_isFlatClosedCondition
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A')
    (h : CoherentSituation.IsFlatClosedCondition D.toCoherentSituation Q)
    (M : QuotSitePresheafModel D) (hM : IsAlgebraicSpace B S hS M.presheaf)
    (F : D.SubfunctorModel (D.quotCondition Q hQ)) : IsAlgebraicSpace B S hS F.presheaf :=
  M.isAlgebraicSpace_of_relative_ι
    (D.relative_closedImmersion_flat_quotCondition_ι_of_isFlatClosedCondition hQ h) F hM

end QuotSituation

end AlgebraicGeometry.Space

end

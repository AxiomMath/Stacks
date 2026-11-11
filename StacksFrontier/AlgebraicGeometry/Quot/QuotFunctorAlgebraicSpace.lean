module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf

/-!
# Models of the Quot functor in the universe of the site (Stacks 09TU)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module, that is, the standing data
`AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR. Stacks 09TU asserts that, when `f` is in
addition separated, `Quot_{F/X/B}` is an algebraic space over `B`, and that its structure
morphism to `B` is locally of finite presentation when `F` is of finite presentation.

A quotient of `F_T` is recorded by its kernel, a subobject of `F_T`, so a section of
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf` over a scheme `T` of the site lives one
universe above the sections of an algebraic space. The conclusion of Stacks 09TU is therefore a
statement about an `AlgebraicGeometry.Space.QuotSitePresheafModel`, a presheaf of `Type u` whose
universe lift is the Quot presheaf — exactly as for the Hilbert functor of Stacks 0CZY, whose
models are `AlgebraicGeometry.Space.HilbertPresheafModel`. This file is about those models: it
produces one, over `B`, from a size bound on the sets of quotients, and it shows that the
conclusion does not depend on which model is produced.

## Main definitions

* `AlgebraicGeometry.Space.shrinkSitePresheaf` and
  `AlgebraicGeometry.Space.shrinkSitePresheafIso`: a presheaf on the schemes of the site with
  values one universe up, all of whose sets of sections are small, read as a presheaf in the
  universe of the site, together with the identification of its universe lift with it.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isoOfModel`: any two models of the Quot
  presheaf are isomorphic.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.exists_quotSitePresheafModel_of_small`: an auxiliary step
  towards Stacks 09TU — when the set of quotients over every scheme of the site is small, the
  Quot presheaf has a model in the universe of the site whose sections over each scheme are the
  quotients themselves and whose canonical morphism to `B` is the one of Stacks 09TR.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.whiskerRight_toBase`: the universe lift of the
  morphism to the base of a model is the canonical morphism to the base of the Quot presheaf, so
  a model is automatically a model *over* `B`.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isoOfModel_hom_comp_toBase`: the isomorphism
  between two models commutes with their morphisms to the base.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isoSource`: the chart condition of
  Stacks 03MJ transports along an isomorphism of the source, which is what carries local finite
  presentation of a structure morphism between two models.
* `AlgebraicGeometry.Space.QuotSitePresheafModel.isAlgebraicSpace_and_lfp_of_model`: the two
  clauses of the conclusion of Stacks 09TU hold for one model exactly when they hold for any
  other, so that conclusion is a statement about `F/X/B` and not about a choice of model.

## Where Stacks 09TU is proved

This file only prepares the statement. The smallness hypothesis of
`AlgebraicGeometry.Space.QuotSituation.exists_quotSitePresheafModel_of_small` is not part of
Stacks 09TU: it holds for every `F/X/B`, which is
`AlgebraicGeometry.Space.QuotSituation.exists_quotSitePresheafModel` in
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorModelSmall.lean`. Stacks 09TU itself, both of its
assertions for `f` of finite presentation and separated, is
`AlgebraicGeometry.Space.QuotSituation.isAlgebraicSpace_and_isLocallyOfFinitePresentation_quot`
in `StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorAlgebraicSpaceSeparated.lean`, through the
source's proof (Stacks 09TT, 04SZ, 0DP6, 09DS, 05UM, 09TP and 08K6).

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 09TP](https://stacks.math.columbia.edu/tag/09TP)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Shrinking a presheaf with small sets of sections -/

/-- A presheaf on the schemes of the big fppf site of `S` with values one universe above the
site, all of whose sets of sections are small, read as a presheaf in the universe of the site:
its sections over a scheme are a copy in `Type u` of the sections of the given presheaf, and
restriction is conjugated from it. -/
def shrinkSitePresheaf (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    [∀ T : (BigFppfOver B S hS)ᵒᵖ, Small.{u} (P.obj T)] :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (P.obj T)
  map {T T'} g := TypeCat.ofHom fun x =>
    equivShrink (P.obj T') (P.map g ((equivShrink (P.obj T)).symm x))
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro x
    change equivShrink (P.obj T) (P.map (𝟙 T) ((equivShrink (P.obj T)).symm x)) = x
    rw [Functor.map_id_apply, Equiv.apply_symm_apply]
  map_comp {T T' T''} g h := by
    apply ConcreteCategory.hom_ext
    intro x
    change equivShrink (P.obj T'') (P.map (g ≫ h) ((equivShrink (P.obj T)).symm x)) =
      equivShrink (P.obj T'') (P.map h ((equivShrink (P.obj T')).symm
        (equivShrink (P.obj T') (P.map g ((equivShrink (P.obj T)).symm x)))))
    rw [Equiv.symm_apply_apply, Functor.map_comp_apply]

/-- The universe lift of the shrinking of a presheaf with small sets of sections is that
presheaf: over every scheme of the site the two sets of sections are in bijection, compatibly
with restriction. -/
def shrinkSitePresheafIso (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    [∀ T : (BigFppfOver B S hS)ᵒᵖ, Small.{u} (P.obj T)] :
    shrinkSitePresheaf P ⋙ uliftFunctor.{u + 1, u} ≅ P :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Equiv.ulift.trans (equivShrink (P.obj T)).symm))
    fun {T T'} g => by
      apply ConcreteCategory.hom_ext
      intro x
      change (equivShrink (P.obj T')).symm
            (equivShrink (P.obj T') (P.map g ((equivShrink (P.obj T)).symm x.down))) =
          P.map g ((equivShrink (P.obj T)).symm x.down)
      rw [Equiv.symm_apply_apply]

/-! ### The chart condition transports along an isomorphism of the source -/

/-- **The chart condition of Stacks 03MJ transports along an isomorphism of the source.** If
`f : F ⟶ G` satisfies it and `f' : F' ⟶ G` is obtained from `f` along an isomorphism `F ≅ F'`,
then `f'` satisfies it, because an étale chart of `F'` composed with the inverse isomorphism is
an étale chart of `F`.

This is what carries local finite presentation of the morphism to the base from one model of a
presheaf to another. -/
theorem holdsOnEveryEtaleChart_of_isoSource (P : MorphismProperty Scheme.{u})
    {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F') {f : F ⟶ G} {f' : F' ⟶ G}
    (hcomp : e.hom ≫ f' = f) (h : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P f' := by
  intro U V a b g ha hb hsq
  refine h U V (a ≫ e.inv) b g (MorphismProperty.RespectsIso.postcomp _ e.inv a ha) hb ?_
  rw [hsq, ← hcomp]
  simp

/-! ### Models of the Quot presheaf -/

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS}

/-- **A model of the Quot presheaf is a model over the base.** The universe lift of its morphism
to the base is the canonical morphism to the base of Stacks 09TR, read through the identification
of the lift of the model with the Quot presheaf; this holds for every model, by the very
definition of `AlgebraicGeometry.Space.QuotSitePresheafModel.toBase`. -/
theorem whiskerRight_toBase (M : QuotSitePresheafModel D) :
    Functor.whiskerRight M.toBase uliftFunctor.{u + 1, u} =
      M.iso.hom ≫ D.quotSitePresheafToBase := by
  ext T z
  rfl

/-- **Any two models of the Quot presheaf are isomorphic.** Their universe lifts are both the
Quot presheaf, and a bijection of the lifts of two sets in `Type u` is a bijection of the sets
themselves. -/
def isoOfModel (M M' : QuotSitePresheafModel D) : M.presheaf ≅ M'.presheaf :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      (Equiv.ulift.symm.trans (((M.iso ≪≫ M'.iso.symm).app T).toEquiv.trans Equiv.ulift)))
    fun {T T'} g => by
      ext z
      exact congrArg ULift.down
        (types_congr_hom ((M.iso ≪≫ M'.iso.symm).hom.naturality g) (ULift.up z))

/-- **The isomorphism between two models commutes with their morphisms to the base**, so the two
models are isomorphic as presheaves over `B`. -/
theorem isoOfModel_hom_comp_toBase (M M' : QuotSitePresheafModel D) :
    (isoOfModel M M').hom ≫ M'.toBase = M.toBase := by
  ext T z
  exact congrArg (fun w => (D.quotSitePresheafToBase.app T w).down)
    (types_congr_hom (NatTrans.congr_app M'.iso.inv_hom_id T) (M.iso.hom.app T (ULift.up z)))

/-- **The conclusion of Stacks 09TU does not depend on the model it is asserted for.** If one
model of the Quot presheaf is an algebraic space whose morphism to the base is locally of finite
presentation, then so is every other: the two models are isomorphic over `B` by
`AlgebraicGeometry.Space.QuotSitePresheafModel.isoOfModel` and
`AlgebraicGeometry.Space.QuotSitePresheafModel.isoOfModel_hom_comp_toBase`, being an algebraic
space is invariant under isomorphism, and the chart condition of Stacks 03MJ transports along an
isomorphism of the source.

Neither clause is proved here for any model; what is proved is that each is a property of
`F/X/B` rather than of a choice of model. -/
theorem isAlgebraicSpace_and_lfp_of_model (M M' : QuotSitePresheafModel D)
    (halg : IsAlgebraicSpace B S hS M.presheaf)
    (hlfp : IsLocallyOfFinitePresentation B S hS M.toBase) :
    IsAlgebraicSpace B S hS M'.presheaf ∧
      IsLocallyOfFinitePresentation B S hS M'.toBase :=
  ⟨halg.of_iso (isoOfModel M M'),
    holdsOnEveryEtaleChart_of_isoSource _ (isoOfModel M M')
      (isoOfModel_hom_comp_toBase M M') hlfp⟩

end QuotSitePresheafModel

/-! ### A model of the Quot presheaf from a size bound -/

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **A model of the Quot presheaf from a size bound** (an auxiliary step towards Stacks 09TU).
Assume that over every scheme `T` of the big fppf site of `S` the set of pairs consisting of a
morphism `T ⟶ B` and a quotient of `F_T` which is quasi-coherent, of finite presentation, flat
over `T` and with support proper over `T` is small. Then the Quot presheaf of Stacks 09TR has a
model in the universe of the site: a presheaf of `Type u` whose sections over every scheme of the
site are exactly those pairs and whose canonical morphism to `B` is the one of Stacks 09TR.

This is what makes the two assertions of Stacks 09TU statable — an algebraic space takes values
in the universe of the site, whereas quotients are recorded by subobjects and so live one
universe up. The smallness hypothesis always holds, so a model always exists
(`AlgebraicGeometry.Space.QuotSituation.exists_quotSitePresheafModel`); Stacks 09TU itself is
`AlgebraicGeometry.Space.QuotSituation.isAlgebraicSpace_and_isLocallyOfFinitePresentation_quot`. -/
theorem exists_quotSitePresheafModel_of_small
    (hsmall : ∀ T : BigFppfOver B S hS, Small.{u} (QuotFamilyOver D T)) :
    ∃ M : QuotSitePresheafModel D,
      (∀ T : (BigFppfOver B S hS)ᵒᵖ, Nonempty (M.presheaf.obj T ≃ QuotFamilyOver D T.unop)) ∧
        Functor.whiskerRight M.toBase uliftFunctor.{u + 1, u} =
          M.iso.hom ≫ D.quotSitePresheafToBase := by
  have : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Small.{u} (D.quotSitePresheaf.obj T) :=
    fun T => hsmall T.unop
  exact ⟨⟨shrinkSitePresheaf D.quotSitePresheaf, shrinkSitePresheafIso D.quotSitePresheaf⟩,
    fun T => ⟨Equiv.ulift.symm.trans ((shrinkSitePresheafIso D.quotSitePresheaf).app T).toEquiv⟩,
    QuotSitePresheafModel.whiskerRight_toBase _⟩

end QuotSituation

end AlgebraicGeometry.Space

end

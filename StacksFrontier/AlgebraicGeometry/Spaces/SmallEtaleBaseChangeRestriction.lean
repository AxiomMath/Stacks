module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.MorphismLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of the small étale pushforward along an étale chart

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained
in a big fppf site `B`, and let `V` be an étale scheme chart of `Y`.  Stacks 04CF asserts the
identity

`f'_*(F|_U) = (f_*F)|_V`,

where `U = V ×_Y X` and `f' : U ⟶ V` is the base change of `f`.  This file supplies that
identity for the direct image of modules attached to the base-change functor
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4), together with the two
inputs it needs: continuity of the localized base-change functor and the structure map of the
morphism of small étale ringed sites.

The restriction `(-)|_V` is here the restriction `SheafOfModules.over` to the slice of the
small étale site of `Y` at the chart `V`, the same reading of Stacks' Equation 03LW used by
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart`, and `f'_*` is the pushforward
along the localized functor `CategoryTheory.Over.post` of Stacks 03CF, with the localized
structure map of Stacks 04J0, part (1).  With those readings the identity is an *equality* of
functors and not merely an isomorphism, because every functor in sight is a restriction along
a functor of sites.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingSheaf` is the structure sheaf of the small étale site
  of an algebraic space as a sheaf of (not necessarily commutative) rings, written over
  `AlgebraicGeometry.Space.SmallEtale.topology`.
* `AlgebraicGeometry.Space.smallBaseChangeProjection` is the cartesian projection
  `V ×_Y X ⟶ V` on underlying objects of the big fppf site, as a natural transformation.
* `AlgebraicGeometry.Space.smallBaseChangeSharp` is the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of
  the morphism of small étale ringed *sites* attached to a representable `f`: on an étale
  chart `V` of `Y` it is pullback of regular functions along that projection.  Its commutative
  form is `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat`.
* `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` is the resulting direct image of
  `𝒪_X`-modules, `SheafOfModules.pushforward` of that structure map.  Unlike
  `AlgebraicGeometry.Space.modulePushforward` its module universe is free.

## Main results

* `AlgebraicGeometry.Space.ringedSite_ringSheaf_eq` and
  `AlgebraicGeometry.Space.modules_eq_sheafOfModules`: the sheaf of rings and the category of
  modules of this file are the ones of
  `StacksFrontier.AlgebraicGeometry.Spaces.RingedSite`, on the nose.
* `AlgebraicGeometry.Space.preservesPullbacks_comparisonFunctor` and
  `AlgebraicGeometry.Space.preservesPullbacks_smallBaseChange`: the comparison functor of
  Stacks 03G1 and small-chart base change preserve fibre products.
* `AlgebraicGeometry.Space.isContinuous_overPost_smallBaseChange`: the localization of
  small-chart base change at an étale chart is continuous.  This is the input that the proof
  of Stacks 03CF asserts without argument.
* `AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward`: for a representable
  morphism the direct image of sheaves of sets on the small étale sites
  (`AlgebraicGeometry.Space.smallEtaleDirectImage`) is restriction along small-chart base
  change.  So for a representable morphism that direct image is not an abstract conjugate of
  the spaces-étale one.
* `AlgebraicGeometry.Space.overFunctor_comp_smallBaseChangeModulePushforward` is the identity
  of Stacks 04CF in the above reading.

## Implementation notes

The sheaf of rings is written over `AlgebraicGeometry.Space.SmallEtale.topology` rather than
as `AlgebraicGeometry.RingedSite.ringSheaf` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the same sheaf
(`AlgebraicGeometry.Space.ringedSite_ringSheaf_eq`), because the second form phrases the site
as the projection `.C` of a structure instance: instance search does not unfold that
projection, so a continuity hypothesis about a functor between the small étale sites does not
apply to the sheaves of modules indexed by it.  The two forms are interchangeable by `rfl`,
and `AlgebraicGeometry.Space.modules_eq_sheafOfModules` records that for the categories of
modules.

The continuity of `CategoryTheory.Over.post` is obtained from
`CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks`, so the work is to show
that `AlgebraicGeometry.Space.smallBaseChange` preserves fibre products.  That is done through
the comparison square of Stacks 03G2, part (4): the comparison functor of Stacks 03G1 is fully
faithful, hence reflects limits, and it preserves fibre products because its composite with
the inclusion of the slice over the space and the inclusion of the algebraic spaces into
presheaves is `AlgebraicGeometry.Space.SmallEtale.toOver` followed by `yoneda`, both of which
preserve fibre products.  Spaces-étale base change already preserves them
(`AlgebraicGeometry.Space.preservesPullbacks_spacesBaseChange`).

The structure map is not built by hand: the cartesian projections assemble into a natural
transformation `smallBaseChange ⋙ toOver ⟶ toOver` whose naturality *is*
`AlgebraicGeometry.Space.smallBaseChange_map_snd`, and the structure map is the opposite of
that transformation whiskered with global regular functions, since the structure presheaf of
the small étale site is global regular functions on the underlying scheme of a chart.  No
separate naturality argument is therefore needed.

This file does **not** identify `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`
with `AlgebraicGeometry.Space.modulePushforward`, the realization of Stacks 03LU, and so it
does not carry the tag of 04CF.  Two comparisons are missing for that.  First,
`AlgebraicGeometry.Space.modulePushforward` is built from
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor`, which transports the ring and module
operations across a finite-product-preserving functor of sheaves of sets, and the identity on
sections is only propositionally a ring homomorphism from those transported operations to the
honest ones; so even for a representable morphism
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf` of the direct image is not the direct image
of the sheaf of rings definitionally.  Second, the structure map
`AlgebraicGeometry.Space.structureSharp` is built through the right Kan extension of
Stacks 03G1 and is not identified with `AlgebraicGeometry.Space.smallBaseChangeSharp` here.
`AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward` is the sheaf-of-sets half
of the first comparison.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe m u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure sheaf of rings over the small étale topology -/

/-- The structure sheaf of the small étale site of an algebraic space as a sheaf of (not
necessarily commutative) rings, the sheaf of rings in which its sheaves of modules are
indexed, written over `AlgebraicGeometry.Space.SmallEtale.topology`.

This is `AlgebraicGeometry.RingedSite.ringSheaf` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, by `rfl`; see the implementation notes for why
the topology is spelled out. -/
noncomputable abbrev smallEtaleRingSheaf (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : Sheaf (SmallEtale.topology B S hS F) RingCat.{u} :=
  (sheafCompose (SmallEtale.topology B S hS F) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (structureSheaf B S hS F hF)

/-- The sheaf of rings of this file is the one of the small étale ringed site. -/
theorem ringedSite_ringSheaf_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) =
      smallEtaleRingSheaf B S hS F hF :=
  rfl

/-- The `𝒪_F`-modules of `AlgebraicGeometry.Space.Modules` are the sheaves of modules over
`AlgebraicGeometry.Space.smallEtaleRingSheaf`. -/
theorem modules_eq_sheafOfModules (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    Modules.{u, m} B S hS F hF = SheafOfModules.{m} (smallEtaleRingSheaf B S hS F hF) :=
  rfl

/-! ### Fibre products -/

/-- The comparison functor of Stacks 03G1 preserves fibre products.

Fibre products of the spaces-étale site are created by its inclusion into the slice over the
space, and that inclusion, like the inclusion of the algebraic spaces into presheaves,
reflects limits; after composing with both, the comparison functor becomes
`AlgebraicGeometry.Space.SmallEtale.toOver` followed by `yoneda`. -/
theorem preservesPullbacks_comparisonFunctor (X : AlgebraicSpaces B S hS) :
    PreservesLimitsOfShape WalkingCospan (comparisonFunctor B S hS X) := by
  have h₀ : PreservesLimitsOfShape WalkingCospan
      ((SmallEtale.inclusion B S hS X.1 ⋙ chartFunctor B S hS X) ⋙
        (Over.forget X ⋙ ObjectProperty.ι
          (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))) := by
    rw [show (SmallEtale.inclusion B S hS X.1 ⋙ chartFunctor B S hS X) ⋙
        (Over.forget X ⋙ ObjectProperty.ι
          (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) =
        SmallEtale.toOver B S hS X.1 ⋙ yoneda from rfl]
    infer_instance
  have h₁ : PreservesLimitsOfShape WalkingCospan
      (SmallEtale.inclusion B S hS X.1 ⋙ chartFunctor B S hS X) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget X ⋙ ObjectProperty.ι _)
  have h₂ : PreservesLimitsOfShape WalkingCospan
      (comparisonFunctor B S hS X ⋙ SpacesEtale.inclusion B S hS X) :=
    preservesLimitsOfShape_of_natIso (J := WalkingCospan)
      (ObjectProperty.liftCompιIso (IsEtaleOver B S hS X)
        (SmallEtale.inclusion B S hS X.1 ⋙ chartFunctor B S hS X)
        (fun U => isEtale_of_presheaf_etale B S hS U.2)).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (SpacesEtale.inclusion B S hS X)

variable {X Y : AlgebraicSpaces B S hS}

/-- Small-chart base change along a representable morphism preserves fibre products: it does
so after composition with the comparison functor of Stacks 03G1, by the comparison square of
Stacks 03G2, part (4) and preservation by spaces-étale base change, and the comparison functor
is fully faithful, hence reflects limits. -/
theorem preservesPullbacks_smallBaseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    PreservesLimitsOfShape WalkingCospan (smallBaseChange B S hS f hf) := by
  have hY := preservesPullbacks_comparisonFunctor B S hS Y
  have hX := preservesPullbacks_comparisonFunctor B S hS X
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have h : PreservesLimitsOfShape WalkingCospan
      (smallBaseChange B S hS f hf ⋙ comparisonFunctor B S hS X) :=
    preservesLimitsOfShape_of_natIso (J := WalkingCospan)
      (smallBaseChange_comparison B S hS f hf).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (comparisonFunctor B S hS X)

/-- **Stacks 03CF, the continuity of `u'`, for small-chart base change.** The localization
`Y_étale/V ⥤ X_étale/(V ×_Y X)` of small-chart base change at an étale chart `V` of `Y` is
continuous for the localized small étale topologies.

This is the input that the proof of Stacks 03CF asserts without argument; here it follows from
`AlgebraicGeometry.Space.preservesPullbacks_smallBaseChange` and the fact that the small étale
site has fibre products. -/
theorem isContinuous_overPost_smallBaseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (Over.post (X := V) (smallBaseChange B S hS f hf)).IsContinuous
      ((SmallEtale.topology B S hS Y.1).over V)
      ((SmallEtale.topology B S hS X.1).over ((smallBaseChange B S hS f hf).obj V)) :=
  have := preservesPullbacks_smallBaseChange B S hS f hf
  Functor.isContinuous_overPost_of_preservesPullbacks _ _ _ V

/-! ### The structure map of small-chart base change -/

/-- The cartesian projection `V ×_Y X ⟶ V` of Stacks 03G2, part (4), on the objects of the big
fppf site underlying the charts, as a natural transformation.  Its naturality is
`AlgebraicGeometry.Space.smallBaseChange_map_snd`. -/
noncomputable def smallBaseChangeProjection (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallBaseChange B S hS f hf ⋙ SmallEtale.toOver B S hS X.1 ⟶
      SmallEtale.toOver B S hS Y.1 where
  app V := hf.snd V.1.hom
  naturality _ _ k := smallBaseChange_map_snd B S hS f hf k

/-- The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of the morphism of small étale ringed *sites*
attached to a representable morphism of algebraic spaces, as a morphism of sheaves of
*commutative* rings: on an étale chart `V` of `Y` it is pullback of regular functions along the
cartesian projection `V ×_Y X ⟶ V`.

It is the opposite of `AlgebraicGeometry.Space.smallBaseChangeProjection` whiskered with global
regular functions, because the structure presheaf of the small étale site is global regular
functions on the underlying scheme of a chart. -/
noncomputable def smallBaseChangeSharpCommRingCat (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    structureSheaf B S hS Y.1 Y.2 ⟶
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (structureSheaf B S hS X.1 X.2) where
  hom := Functor.whiskerRight (NatTrans.op (smallBaseChangeProjection B S hS f hf))
    ((BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ)

/-- The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of small-chart base change as a morphism of sheaves
of (not necessarily commutative) rings, the form in which sheaves of modules consume it. -/
noncomputable def smallBaseChangeSharp (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallEtaleRingSheaf B S hS Y.1 Y.2 ⟶
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (smallEtaleRingSheaf B S hS X.1 X.2) :=
  (sheafCompose (SmallEtale.topology B S hS Y.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (smallBaseChangeSharpCommRingCat B S hS f hf)

/-- The direct image of `𝒪_X`-modules along a representable morphism of algebraic spaces, taken
along small-chart base change and the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp`.

Unlike `AlgebraicGeometry.Space.modulePushforward`, which factors through the inverse image of
an abstract finite-product-preserving functor of sheaves of sets, this is restriction of
scalars along a restriction of sites, so its module universe is free. -/
noncomputable def smallBaseChangeModulePushforward (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2) ⥤
      SheafOfModules.{m} (smallEtaleRingSheaf B S hS Y.1 Y.2) :=
  SheafOfModules.pushforward (smallBaseChangeSharp B S hS f hf)

/-! ### The direct image of sheaves of sets along a representable morphism -/

/-- For a *representable* morphism of algebraic spaces the direct image of sheaves of sets on
the small étale sites is restriction along small-chart base change.

`AlgebraicGeometry.Space.smallEtaleDirectImage` is defined by conjugating the spaces-étale
direct image with the comparison equivalences of Stacks 03G1, and so is not visibly a
restriction; this identifies it with one as soon as `f` is representable, using the
direct-image comparison of the small and spaces-étale base-change square. -/
@[sga "4½ Arcata 2.3.3" "more general"]
noncomputable def smallEtaleDirectImageIsoSheafPushforward (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallEtaleDirectImage B S hS f ≅
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  Functor.isoWhiskerLeft (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse
      (smallBaseChange_pushforward_comparisonTypeU B S hS f hf).symm ≪≫
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.invFunIdAssoc _

/-! ### Stacks 04CF -/

/-- **Stacks 04CF** for `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`: for a
representable morphism `f : X ⟶ Y` of algebraic spaces and an étale chart `V` of `Y`, the
restriction to `V` of the direct image of an `𝒪_X`-module is the direct image, along the base
change of `f` to `V`, of the restriction of the module to `U = V ×_Y X`:

`f'_*(F|_U) = (f_*F)|_V`.

The restrictions are restriction to the slices of the small étale sites, which is Stacks'
Equation 03LW, and `f'_*` is the pushforward along the localized base-change functor of
Stacks 03CF with the localized structure map of Stacks 04J0, part (1).  Everything in sight
being a restriction along a functor of sites, this is an equality of functors.

This is Stacks 04J0, part (3) applied to small-chart base change; the content of the present
statement is that its hypotheses hold there, namely
`AlgebraicGeometry.Space.isContinuous_overPost_smallBaseChange` and the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp`. -/
theorem overFunctor_comp_smallBaseChangeModulePushforward (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    letI := isContinuous_overPost_smallBaseChange B S hS f hf V
    (SheafOfModules.overFunctor (smallEtaleRingSheaf B S hS X.1 X.2)
          ((smallBaseChange B S hS f hf).obj V) :
        SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2) ⥤ _) ⋙
        SheafOfModules.pushforward (RingedSite.MorphismLocalization.localizedStructureMap
          (smallBaseChange B S hS f hf) (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1) V (smallEtaleRingSheaf B S hS X.1 X.2)
          (smallEtaleRingSheaf B S hS Y.1 Y.2) (smallBaseChangeSharp B S hS f hf)) =
      smallBaseChangeModulePushforward B S hS f hf ⋙
        SheafOfModules.overFunctor (smallEtaleRingSheaf B S hS Y.1 Y.2) V :=
  let := isContinuous_overPost_smallBaseChange B S hS f hf V
  RingedSite.MorphismLocalization.pushforward_overPullback_comm_modules
    (smallBaseChange B S hS f hf)
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) V
    (smallEtaleRingSheaf B S hS X.1 X.2) (smallEtaleRingSheaf B S hS Y.1 Y.2)
    (smallBaseChangeSharp B S hS f hf)

end AlgebraicGeometry.Space

end

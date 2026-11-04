module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of the direct image of modules to an étale chart, for an arbitrary morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `V` be an étale scheme chart of `Y`.  Stacks 04CF asserts the identity

`f'_*(F|_U) = (f_*F)|_V`,

where `U = V ×_Y X` and `f' : U ⟶ V` is the base change of `f`.  This file supplies that
identity for `AlgebraicGeometry.Space.modulePushforward`, the direct image of modules of
Stacks 03LU, with **no representability hypothesis on `f`** — which is the form in which the
proof of Stacks 03M9 invokes it.

`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean`) carries the same
equation for a *representable* `f`, as an equality of functors.  That form cannot be extended to
an arbitrary `f`: it is phrased through `AlgebraicGeometry.Space.smallBaseChange`, base change on
étale *scheme* charts, which exists only when `f` is representable.  For an arbitrary `f` the
fibre product `U = V ×_Y X` is an algebraic space and not an étale scheme chart of `X`, so it is
not an object of the small étale site of `X` and the restriction `F|_U` cannot be taken there.
Here `U` is therefore `AlgebraicGeometry.Space.chartBaseChange`, the base change of the chart on
the *spaces-étale* site of Stacks 03G0, and `F|_U` is restriction to the slice of the
spaces-étale site of `X` at `U` — the same reading of Stacks' Equation 03LW as in the
representable file, one site up.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeRestriction` is the restriction `F ↦ F|_U` of sheaves
  of sets, and `AlgebraicGeometry.Space.chartLocalizedDirectImage` is the localized direct image
  `f'_*` of sheaves of sets, both at the universe of the structure rings.
* `AlgebraicGeometry.Space.chartBaseChangeRingSheaf` is the restriction `𝒪_X|_U` of the
  structure sheaf, and `AlgebraicGeometry.Space.moduleChartBaseChangeRestriction` the
  restriction `F ↦ F|_U` of modules.
* `AlgebraicGeometry.Space.overStructureSharp` is the restriction of the structure map `f^♯` of
  Stacks 03G8 to the slice at `V`, `AlgebraicGeometry.Space.chartLocalizedStructureSharp` is the
  structure map `(f')^♯ : 𝒪_V ⟶ f'_*(𝒪_X|_U)` of the base-changed morphism, and
  `AlgebraicGeometry.Space.chartLocalizedModulePushforward` is the resulting direct image
  `f'_*` of modules, in the shape of Stacks 03D6, part (1).

## Main results

* `AlgebraicGeometry.Space.chartRestrictionDirectImageIso` is Stacks 04CF for sheaves of sets:
  the restriction to `V` of the direct image of a sheaf of sets is the localized direct image of
  the restriction to `U`.
* `AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso` is Stacks 04CF for
  `AlgebraicGeometry.Space.modulePushforward` and an arbitrary morphism of algebraic spaces.

## Implementation notes

The identity is proved directly for `AlgebraicGeometry.Space.modulePushforward` rather than by
transporting the representable form, for the reason recorded above: the representable form
quantifies over a functor that does not exist for a general `f`.

Three of the four steps are definitional identities, and are used as such.  Writing `Λ_V` for
restriction of sheaves of sets to the slice at `V` and `Φ_f` for
`AlgebraicGeometry.Space.smallEtaleDirectImage`,

* restriction of scalars commutes with restriction to a slice, because both only reindex
  sections;
* `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` and
  `Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` commute with restriction to a slice, the
  localized transporting functor being `Φ_f ⋙ Λ_V`, because the sections of a restricted sheaf
  over an object of the slice are the sections of the sheaf over its underlying object, on the
  nose;
* and restriction of scalars along a composite is the composite of the restrictions.

Together these make `AlgebraicGeometry.Space.modulePushforward_comp_overFunctor_eq` a `rfl`,
and the mathematical content is confined to the remaining step, the comparison
`Φ_f ⋙ Λ_V ≅ (F ↦ F|_U) ⋙ f'_*` of transporting functors.  That comparison is two instances of
the Stacks 03CF localization comparison
`AlgebraicGeometry.RingedSite.MorphismLocalization.localizationComparisonIso`: one for the
comparison functor of Stacks 03G1 at the chart `V`, one for spaces-étale base change at the
corresponding object of the spaces-étale site.  Each needs the continuity of `Over.post` of the
functor in question, which is `Functor.isContinuous_overPost_of_preservesPullbacks` applied to
`AlgebraicGeometry.Space.preservesPullbacks_comparisonFunctor` and to
`AlgebraicGeometry.Space.preservesPullbacks_spacesBaseChange`.

The comparison of the transporting functors is then carried to modules by
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso`, and the composite transporting
functor is split into its two factors by
`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso`.  Both of those transports read the scalars
through a comparison of the transported sheaves of rings, so the two sides of the final
isomorphism are modules over *a priori* different, canonically isomorphic, sheaves of rings; the
composite of the two ring comparisons with `(f)^♯` restricted to the slice is exactly the
structure map `AlgebraicGeometry.Space.chartLocalizedStructureSharp` of `f'`, and
`AlgebraicGeometry.Space.chartLocalizedStructureSharp_comp_comparison` is the one equation
needed to make the two transports meet.

Unlike the representable form this is an isomorphism and not an equality of functors:
`AlgebraicGeometry.Space.smallEtaleDirectImage` is conjugated by the comparison equivalence of
Stacks 03G1, whose quasi-inverse is a chosen one, so the two sides are not restrictions along
one functor of sites.

The module universe is the universe `u` of the structure rings, not a free one, for the reason
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean`: the direct image of modules
applies the direct image of sheaves of *sets* to the sheaf underlying the module, and on the
small étale site of an algebraic space that direct image is available only at `Type u`.

Every intermediate isomorphism is a *named* declaration whose type is written out, and the
composites are kept un-reassociated: `AlgebraicGeometry.Space.modulePushforwardOverIsoLeft`,
`...Middle` and `...Right` meet at syntactically identical functors, and the two reassociations
and the two collapses of iterated restriction of scalars are done explicitly, by
`CategoryTheory.Functor.associator` and by `SheafOfModules.restrictScalars_comp`.  That is not
cosmetic.  Composing these isomorphisms with the reassociation left to the unifier asks it to
solve `?F ⋙ ?G ≟ (P ⋙ A) ⋙ B` with `?F`, `?G` unknown; the first-order match fails, and the
fallback unfolds the transporting functors, hence
`AlgebraicGeometry.Space.smallEtaleDirectImage` and the comparison equivalence of Stacks 03G1,
whose quasi-inverse is a `CategoryTheory.Functor.objPreimage`, i.e. a `Classical.choose` — and
that reduction does not terminate.  With the intermediate types written out no metavariable
reaches that position and no reduction happens at all; **no raised heartbeat budget is needed**,
and no `set_option` appears in this file.  For the same reason
`AlgebraicGeometry.Space.chartLocalizedStructureSharp_comp_comparison` is proved in term mode:
`rw` and `simp` fail to fire `CategoryTheory.Category.assoc` on its goal, whose implicit
arguments are the transported sheaves of rings.

`SheafOfModules.restrictScalars_comp` is stated outside the namespace
`AlgebraicGeometry.Space`: it is a general fact about restriction of scalars for sheaves of
modules over a site and belongs with that notion.

What this file does *not* supply is the identification of the slice of the spaces-étale site of
`X` at `U` with the small étale site of the algebraic space `U` itself.  Until that is available
the right-hand side is `f'_*` read on that slice, and not
`AlgebraicGeometry.Space.modulePushforward` of a morphism `U ⟶ V` of algebraic spaces.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe v w u

/-- Restriction of scalars along a composite of morphisms of sheaves of rings is the composite of
the restrictions, in the opposite order. -/
theorem SheafOfModules.restrictScalars_comp {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R R' R'' : Sheaf J RingCat.{w}} (a : R ⟶ R') (b : R' ⟶ R'') :
    SheafOfModules.restrictScalars.{v} b ⋙ SheafOfModules.restrictScalars.{v} a =
      SheafOfModules.restrictScalars.{v} (a ≫ b) :=
  rfl

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Continuity of the two localized functors -/

/-- **Stacks 03CF, the continuity of `u'`, for the comparison functor of Stacks 03G1.** The
localization of the comparison functor at an étale scheme chart `V` of an algebraic space is
continuous for the localized topologies.

The comparison functor preserves fibre products
(`AlgebraicGeometry.Space.preservesPullbacks_comparisonFunctor`) and the small étale site has
them, so this is `CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks`. -/
instance isContinuous_overPost_comparisonFunctor (Z : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Z.1) :
    (Over.post (X := V) (comparisonFunctor B S hS Z)).IsContinuous
      ((SmallEtale.topology B S hS Z.1).over V)
      ((SpacesEtale.topology B S hS Z).over ((comparisonFunctor B S hS Z).obj V)) :=
  haveI := preservesPullbacks_comparisonFunctor B S hS Z
  Functor.isContinuous_overPost_of_preservesPullbacks _ _ _ V

/-- **Stacks 03CF, the continuity of `u'`, for spaces-étale base change.** The localization
`Y_{spaces,étale}/W ⥤ X_{spaces,étale}/(W ×_Y X)` of spaces-étale base change along an arbitrary
morphism of algebraic spaces is continuous for the localized topologies.

Spaces-étale base change preserves fibre products
(`AlgebraicGeometry.Space.preservesPullbacks_spacesBaseChange`) and the spaces-étale site has
them, so this is `CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks`.  No
representability of `f` is used. -/
instance isContinuous_overPost_spacesBaseChange (f : X ⟶ Y) (W : SpacesEtale B S hS Y) :
    (Over.post (X := W) (spacesBaseChange B S hS f).functor).IsContinuous
      ((SpacesEtale.topology B S hS Y).over W)
      ((SpacesEtale.topology B S hS X).over ((spacesBaseChange B S hS f).functor.obj W)) :=
  Functor.isContinuous_overPost_of_preservesPullbacks _ _ _ W

/-! ### Sheaves of sets -/

/-- The restriction `F ↦ F|_U` of sheaves of sets on the small étale site of `X` to the slice of
the *spaces-étale* site of `X` at `U = V ×_Y X`, at the universe of the structure rings.

This is Stacks' Equation 03LW for the étale morphism `U ⟶ X` of algebraic spaces: pass from the
small étale topos of `X` to its spaces-étale topos by the comparison equivalence of Stacks 03G1
and restrict to the slice at `U`.  For a general `f` the object `U` is an algebraic space and not
an étale scheme chart of `X`, so the slice of the *small* étale site is not available. -/
noncomputable def chartBaseChangeRestriction (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤
      Sheaf ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V)) (Type u) :=
  (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse ⋙
    (SpacesEtale.topology B S hS X).overPullback (Type u) (chartBaseChange B S hS f V)

/-- The restriction to `U` preserves finite products: it is the composite of the quasi-inverse of
an equivalence with a restriction along a functor of sites. -/
instance preservesFiniteProducts_chartBaseChangeRestriction (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    PreservesFiniteProducts (chartBaseChangeRestriction B S hS f V) := by
  unfold chartBaseChangeRestriction
  infer_instance

/-- The localized direct image `f'_*` of sheaves of sets along the base change
`f' : U ⟶ V` of `f`, at the universe of the structure rings, read as a functor to sheaves on the
slice of the *small* étale site of `Y` at the chart `V`.

It is the direct image along the localization of spaces-étale base change — the morphism of
sites `f'` of Stacks 03CF — followed by the localization of the comparison functor of
Stacks 03G1 at `V`, which identifies the slice `Y_{spaces,étale}/W` with the slice
`Y_étale/V`.  The second factor is half of an equivalence of sites and carries no geometry;
it is present because the left-hand side of Stacks 04CF is a sheaf on `Y_étale/V`. -/
noncomputable def chartLocalizedDirectImage (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Sheaf ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V)) (Type u) ⥤
      Sheaf ((SmallEtale.topology B S hS Y.1).over V) (Type u) :=
  (Over.post (X := (comparisonFunctor B S hS Y).obj V)
      (spacesBaseChange B S hS f).functor).sheafPushforwardContinuous (Type u)
      ((SpacesEtale.topology B S hS Y).over ((comparisonFunctor B S hS Y).obj V))
      ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V)) ⋙
    (Over.post (X := V) (comparisonFunctor B S hS Y)).sheafPushforwardContinuous (Type u)
      ((SmallEtale.topology B S hS Y.1).over V)
      ((SpacesEtale.topology B S hS Y).over ((comparisonFunctor B S hS Y).obj V))

/-- The localized direct image preserves finite products: both of its factors are restrictions
along functors of sites. -/
instance preservesFiniteProducts_chartLocalizedDirectImage (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    PreservesFiniteProducts (chartLocalizedDirectImage B S hS f V) := by
  unfold chartLocalizedDirectImage
  infer_instance

/-- **Stacks 04CF for sheaves of sets, for an arbitrary morphism of algebraic spaces.** The
restriction to an étale scheme chart `V` of `Y` of the direct image of a sheaf of sets on the
small étale site of `X` is the localized direct image of the restriction to `U = V ×_Y X`.

The two factors are the Stacks 03CF localization comparison for the comparison functor of
Stacks 03G1 at `V` and for spaces-étale base change at the corresponding spaces-étale object;
the quasi-inverse of the comparison equivalence is carried along unchanged. -/
noncomputable def chartRestrictionDirectImageIso (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    smallEtaleDirectImage B S hS f ⋙
        (SmallEtale.topology B S hS Y.1).overPullback (Type u) V ≅
      chartBaseChangeRestriction B S hS f V ⋙ chartLocalizedDirectImage B S hS f V :=
  Functor.isoWhiskerLeft
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
      (RingedSite.MorphismLocalization.localizationComparisonIso (comparisonFunctor B S hS Y)
        (SpacesEtale.topology B S hS Y) (SmallEtale.topology B S hS Y.1) V (Type u)).symm ≪≫
    Functor.isoWhiskerLeft (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse
      (Functor.isoWhiskerRight
        (RingedSite.MorphismLocalization.localizationComparisonIso
          (spacesBaseChange B S hS f).functor
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
          ((comparisonFunctor B S hS Y).obj V) (Type u)).symm
        ((Over.post (X := V) (comparisonFunctor B S hS Y)).sheafPushforwardContinuous (Type u)
          ((SmallEtale.topology B S hS Y.1).over V)
          ((SpacesEtale.topology B S hS Y).over ((comparisonFunctor B S hS Y).obj V))))

/-! ### Modules -/

/-- The restriction `𝒪_X|_U` of the structure sheaf of `X` to the slice of the spaces-étale site
at `U = V ×_Y X`, as a sheaf of rings: the structure sheaf of `U` in the reading of this file,
and the sheaf of rings over which `F|_U` is a module. -/
noncomputable def chartBaseChangeRingSheaf (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Sheaf ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V)) RingCat.{u} :=
  pullbackRingSheaf.{u, u, u + 1, u + 1, u, u + 1}
    ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V))
    (chartBaseChangeRestriction B S hS f V) (structureRingSheaf B S hS X)

/-- The restriction `F ↦ F|_U` of `𝒪_X`-modules to `U = V ×_Y X`, as `𝒪_X|_U`-modules. -/
noncomputable def moduleChartBaseChangeRestriction (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (chartBaseChangeRingSheaf B S hS f V) :=
  pullbackModuleFunctor ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V))
    (chartBaseChangeRestriction B S hS f V) (structureRingSheaf B S hS X)

/-- **Stacks 03D1** for the localized direct image: the direct image of `𝒪_X|_U`-modules along
`f' : U ⟶ V`, taken over the direct-image sheaf of rings `f'_*(𝒪_X|_U)`. -/
noncomputable def chartLocalizedModuleDirectImage (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    SheafOfModules.{u} (chartBaseChangeRingSheaf B S hS f V) ⥤
      SheafOfModules.{u} (pullbackRingSheaf.{u, u, u, u + 1, u + 1, u + 1}
        ((SmallEtale.topology B S hS Y.1).over V)
        (chartLocalizedDirectImage B S hS f V) (chartBaseChangeRingSheaf B S hS f V)) :=
  pullbackModuleFunctor ((SmallEtale.topology B S hS Y.1).over V)
    (chartLocalizedDirectImage B S hS f V) (chartBaseChangeRingSheaf B S hS f V)

/-- The comparison of the sheaves of rings transported along `Φ_f ⋙ Λ_V` and along
`(F ↦ F|_U) ⋙ f'_*`, induced by `AlgebraicGeometry.Space.chartRestrictionDirectImageIso`.  It is
the identity on underlying sheaves of sets. -/
noncomputable def chartRestrictionRingMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        ((SmallEtale.topology B S hS Y.1).over V)
        (smallEtaleDirectImage B S hS f ⋙
          (SmallEtale.topology B S hS Y.1).overPullback (Type u) V)
        (structureRingSheaf B S hS X) ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        ((SmallEtale.topology B S hS Y.1).over V)
        (chartBaseChangeRestriction B S hS f V ⋙ chartLocalizedDirectImage B S hS f V)
        (structureRingSheaf B S hS X) :=
  pullbackRingSheafMapOfNatTrans ((SmallEtale.topology B S hS Y.1).over V)
    (structureRingSheaf B S hS X) (chartRestrictionDirectImageIso B S hS f V).hom

/-- The comparison of the iterated transport `f'_*(𝒪_X|_U)` of the structure sheaf of `X` with
its transport along the composite functor `(F ↦ F|_U) ⋙ f'_*` in one step.  It, too, is the
identity on underlying sheaves of sets. -/
noncomputable def chartBaseChangeRingComparison (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    pullbackRingSheaf.{u, u, u, u + 1, u + 1, u + 1}
        ((SmallEtale.topology B S hS Y.1).over V)
        (chartLocalizedDirectImage B S hS f V) (chartBaseChangeRingSheaf B S hS f V) ≅
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        ((SmallEtale.topology B S hS Y.1).over V)
        (chartBaseChangeRestriction B S hS f V ⋙ chartLocalizedDirectImage B S hS f V)
        (structureRingSheaf B S hS X) :=
  pullbackRingSheafCompIso ((SmallEtale.topology B S hS Y.1).over V)
    ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V))
    (chartLocalizedDirectImage B S hS f V) (chartBaseChangeRestriction B S hS f V)
    (structureRingSheaf B S hS X)

/-- The restriction of the structure map `f^♯` of Stacks 03G8 to the slice of the small étale
site of `Y` at the chart `V`. -/
noncomputable def overStructureSharp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (structureRingSheaf B S hS Y).over V ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        ((SmallEtale.topology B S hS Y.1).over V)
        (smallEtaleDirectImage B S hS f ⋙
          (SmallEtale.topology B S hS Y.1).overPullback (Type u) V)
        (structureRingSheaf B S hS X) :=
  ((SmallEtale.topology B S hS Y.1).overPullback RingCat.{u} V).map (structureSharp B S hS f)

/-- The structure map `(f')^♯ : 𝒪_V ⟶ f'_*(𝒪_X|_U)` of the base change `f' : U ⟶ V` of `f`: the
structure map `f^♯` of Stacks 03G8 restricted to the slice at `V`, read through the two ring
comparisons of this file.

This is the localized structure map of Stacks 04J0, part (1) for the present reading of `f'`. -/
noncomputable def chartLocalizedStructureSharp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (structureRingSheaf B S hS Y).over V ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u + 1, u + 1}
        ((SmallEtale.topology B S hS Y.1).over V)
        (chartLocalizedDirectImage B S hS f V) (chartBaseChangeRingSheaf B S hS f V) :=
  (overStructureSharp B S hS f V ≫ chartRestrictionRingMap B S hS f V) ≫
    (chartBaseChangeRingComparison B S hS f V).inv

/-- The defining property of the localized structure map: composed with the comparison of the
transported sheaves of rings it is the restriction of `f^♯` to the slice at `V`, read through the
comparison of transporting functors. -/
theorem chartLocalizedStructureSharp_comp_comparison (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    chartLocalizedStructureSharp B S hS f V ≫ (chartBaseChangeRingComparison B S hS f V).hom =
      overStructureSharp B S hS f V ≫ chartRestrictionRingMap B S hS f V :=
  (Category.assoc _ _ _).trans
    ((congrArg
        (fun φ ↦ (overStructureSharp B S hS f V ≫ chartRestrictionRingMap B S hS f V) ≫ φ)
        (chartBaseChangeRingComparison B S hS f V).inv_hom_id).trans (Category.comp_id _))

/-- **Stacks 03D6, part (1)** for the localized direct image, and the right-hand side of
Stacks 04CF: the direct image `f'_*` of `𝒪_X|_U`-modules along the base change `f' : U ⟶ V` of
`f`, read as `𝒪_V`-modules by restriction of scalars along `(f')^♯`. -/
noncomputable def chartLocalizedModulePushforward (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    SheafOfModules.{u} (chartBaseChangeRingSheaf B S hS f V) ⥤
      SheafOfModules.{u} ((structureRingSheaf B S hS Y).over V) :=
  chartLocalizedModuleDirectImage B S hS f V ⋙
    SheafOfModules.restrictScalars (chartLocalizedStructureSharp B S hS f V)

/-- Restriction of the direct image of modules to the slice at `V` is the transport of modules
along the localized transporting functor `Φ_f ⋙ Λ_V`, with the restriction of `f^♯` as its
structure map.

This holds by `rfl`: restriction to a slice only reindexes sections, so it commutes both with the
transport of modules along a finite-product-preserving functor of sheaves of sets and with
restriction of scalars. -/
theorem modulePushforward_comp_overFunctor_eq (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    modulePushforward B S hS f ⋙
          SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS Y) V =
      pullbackModuleFunctor ((SmallEtale.topology B S hS Y.1).over V)
          (smallEtaleDirectImage B S hS f ⋙
            (SmallEtale.topology B S hS Y.1).overPullback (Type u) V)
          (structureRingSheaf B S hS X) ⋙
        SheafOfModules.restrictScalars (overStructureSharp B S hS f V) :=
  rfl

/-- The right-hand side of Stacks 04CF with its two factors merged into the transport of modules
along the composite functor, in the shape in which the composition law for that transport
delivers it. -/
theorem chartLocalizedModulePushforward_eq (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    moduleChartBaseChangeRestriction B S hS f V ⋙ chartLocalizedModulePushforward B S hS f V =
      (moduleChartBaseChangeRestriction B S hS f V ⋙
          chartLocalizedModuleDirectImage B S hS f V) ⋙
        SheafOfModules.restrictScalars (chartLocalizedStructureSharp B S hS f V) :=
  rfl

/-- The left-hand side of Stacks 04CF, carried onto the transport of modules along the composite
functor `(F ↦ F|_U) ⋙ f'_*` by the comparison of transporting functors. -/
noncomputable def modulePushforwardOverIsoLeft (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    modulePushforward B S hS f ⋙
        SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS Y) V ≅
      (pullbackModuleFunctor ((SmallEtale.topology B S hS Y.1).over V)
            (chartBaseChangeRestriction B S hS f V ⋙ chartLocalizedDirectImage B S hS f V)
            (structureRingSheaf B S hS X) ⋙
          SheafOfModules.restrictScalars (chartRestrictionRingMap B S hS f V)) ⋙
        SheafOfModules.restrictScalars (overStructureSharp B S hS f V) :=
  eqToIso (modulePushforward_comp_overFunctor_eq B S hS f V) ≪≫
    Functor.isoWhiskerRight
      (pullbackModuleFunctorIsoOfNatIso ((SmallEtale.topology B S hS Y.1).over V)
        (structureRingSheaf B S hS X) (chartRestrictionDirectImageIso B S hS f V)
        (chartRestrictionRingMap B S hS f V)
        (ringSheafMap_pullbackRingSheafMapOfNatTrans ((SmallEtale.topology B S hS Y.1).over V)
          (structureRingSheaf B S hS X) (chartRestrictionDirectImageIso B S hS f V).hom))
      (SheafOfModules.restrictScalars (overStructureSharp B S hS f V))

/-- The right-hand side of Stacks 04CF, carried onto the transport of modules along the same
composite functor by the composition law for that transport. -/
noncomputable def modulePushforwardOverIsoRight (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (moduleChartBaseChangeRestriction B S hS f V ⋙
          chartLocalizedModuleDirectImage B S hS f V) ⋙
        SheafOfModules.restrictScalars (chartLocalizedStructureSharp B S hS f V) ≅
      (pullbackModuleFunctor ((SmallEtale.topology B S hS Y.1).over V)
            (chartBaseChangeRestriction B S hS f V ⋙ chartLocalizedDirectImage B S hS f V)
            (structureRingSheaf B S hS X) ⋙
          SheafOfModules.restrictScalars (chartBaseChangeRingComparison B S hS f V).hom) ⋙
        SheafOfModules.restrictScalars (chartLocalizedStructureSharp B S hS f V) :=
  Functor.isoWhiskerRight
    (pullbackModuleCompIso ((SmallEtale.topology B S hS Y.1).over V)
      ((SpacesEtale.topology B S hS X).over (chartBaseChange B S hS f V))
      (chartLocalizedDirectImage B S hS f V) (chartBaseChangeRestriction B S hS f V)
      (structureRingSheaf B S hS X))
    (SheafOfModules.restrictScalars (chartLocalizedStructureSharp B S hS f V))

/-- The two transports of modules along the composite functor agree: their scalars differ by the
two ring comparisons of this file, and composing them with the restriction of `f^♯` gives the
localized structure map `(f')^♯`, which is
`AlgebraicGeometry.Space.chartLocalizedStructureSharp_comp_comparison`. -/
noncomputable def modulePushforwardOverIsoMiddle (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (pullbackModuleFunctor ((SmallEtale.topology B S hS Y.1).over V)
            (chartBaseChangeRestriction B S hS f V ⋙ chartLocalizedDirectImage B S hS f V)
            (structureRingSheaf B S hS X) ⋙
          SheafOfModules.restrictScalars (chartRestrictionRingMap B S hS f V)) ⋙
        SheafOfModules.restrictScalars (overStructureSharp B S hS f V) ≅
      (pullbackModuleFunctor ((SmallEtale.topology B S hS Y.1).over V)
            (chartBaseChangeRestriction B S hS f V ⋙ chartLocalizedDirectImage B S hS f V)
            (structureRingSheaf B S hS X) ⋙
          SheafOfModules.restrictScalars (chartBaseChangeRingComparison B S hS f V).hom) ⋙
        SheafOfModules.restrictScalars (chartLocalizedStructureSharp B S hS f V) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (SheafOfModules.restrictScalars_comp
      (overStructureSharp B S hS f V) (chartRestrictionRingMap B S hS f V))) ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (congrArg SheafOfModules.restrictScalars.{u}
      (chartLocalizedStructureSharp_comp_comparison B S hS f V))).symm ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (SheafOfModules.restrictScalars_comp
      (chartLocalizedStructureSharp B S hS f V)
      (chartBaseChangeRingComparison B S hS f V).hom)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **Stacks 04CF, for an arbitrary morphism of algebraic spaces.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` and let `V` be an étale scheme chart of `Y`.  Write
`U = V ×_Y X` for the base change of the chart, an étale algebraic space over `X`, and
`f' : U ⟶ V` for the base change of `f`.  Then for every `𝒪_X`-module `F`

`f'_*(F|_U) = (f_*F)|_V`.

The restriction `(-)|_V` is restriction to the slice of the small étale site of `Y` at `V`, the
restriction `(-)|_U` is restriction to the slice of the *spaces-étale* site of `X` at `U` — both
readings of Stacks' Equation 03LW — and `f'_*` is the direct image along the localized
base-change functor of Stacks 03CF with the localized structure map
`AlgebraicGeometry.Space.chartLocalizedStructureSharp` of Stacks 04J0, part (1).

No representability hypothesis is made on `f`; this is the form in which the proof of
Stacks 03M9 invokes the identity.  It is an isomorphism rather than an equality of functors
because `AlgebraicGeometry.Space.smallEtaleDirectImage` is conjugated by the comparison
equivalence of Stacks 03G1; for a representable `f` an equality is available in the reading of
`AlgebraicGeometry.Space.overFunctor_comp_smallBaseChangeModulePushforward`. -/
@[stacks 04CF "for an arbitrary morphism of algebraic spaces, with the restriction to the
  base-changed chart taken on the slice of the spaces-étale site"]
noncomputable def modulePushforward_comp_overFunctorIso (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    modulePushforward B S hS f ⋙
        SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS Y) V ≅
      moduleChartBaseChangeRestriction B S hS f V ⋙
        chartLocalizedModulePushforward B S hS f V :=
  modulePushforwardOverIsoLeft B S hS f V ≪≫ modulePushforwardOverIsoMiddle B S hS f V ≪≫
    (modulePushforwardOverIsoRight B S hS f V).symm ≪≫
    eqToIso (chartLocalizedModulePushforward_eq B S hS f V).symm

end AlgebraicGeometry.Space

end

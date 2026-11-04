module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardTopoi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionLocalToGlobal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCompletionTopos

/-!
# Derived completion across the dense-subsite replacement

The reduction of [Stacks, Tag 0A0G] from a morphism of ringed topoi to a morphism of ringed sites
goes through the square of [Stacks, Tag 03CR], exactly as `PushforwardTopoi.lean`'s proof of
[Stacks, Tag 099J] does. Three of the square's four arrows are handled by the ringed-sites case
of the tag; this file handles the two that are *equivalences* — the dense-subsite replacements
`g : X ⟶ X'` and `e : Y ⟶ Y'`.

## The observation this file rests on

The inverse of the replacement equivalence **is itself a morphism of ringed sites**:
`AlgebraicGeometry.RingedToposHom.denseRestrictSite` of `PushforwardTopoi.lean` presents
`X' ⟶ X` by the dense-subsite inclusion `v : 𝒞 ⥤ 𝒞'`. So nothing has to be transported across an
equivalence by hand: the ringed-sites case of [Stacks, Tag 0A0G],
`RingedSite.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType`,
applies to it directly, at its own data — a sheaf of ideals `ℐ ⊂ 𝒪_X` of finite type and the
ideal sheaf `ℐ'' = v^{-1}ℐ · 𝒪_{X'}` that Section 52.7 builds out of it.

What then remains for the equivalence is to turn that statement about the restriction `Rr_*` into
one about `D(g_*)`, and that is
`nonempty_iso_mapDerivedCategory_derivedCompletion_denseReplacement` below: `D(g_*)` is an
equivalence with `Rr_*` as a quasi-inverse, by
`AlgebraicGeometry.RingedToposHom.derivedPushforwardDenseRestrictMapIso` together with the round
trip of `PushforwardTopoi.lean`, so an identification of `Rr_*(E^∧)` with `(Rr_*E)^∧` at every `E`
yields one of `D(g_*)(K^∧)` with `(D(g_*)K)^∧` at every `K`.

## Only existence is needed

Each statement below is an isomorphism of objects, and the last two are stated as `Nonempty`.
That is deliberate and costs nothing downstream:
`AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_of_nonempty_iso`
turns a merely existential, non-canonical, non-natural display, quantified over all objects, into
invertibility of the *canonical* comparison map at every object. So no coherence between the
isomorphisms assembled here and the canonical map has to be proved.

## The instances

Three instances are restated in the shape the replacement sites present — the finite type of the
ideal, [Stacks, Tag 099F]'s reflector along it, and the additivity of the direct image along `g`.
All three are the same discrimination-tree gap that `PushforwardTopoi.lean` documents for the
additivity of the direct image, and that `PushforwardCompletionTopos.lean` documents for the
reflector: `AlgebraicGeometry.RingedTopos.toRingedSite` and `denseReplacement` are reducible
abbreviations for structure literals, whose fields reduce away under the reducible transparency of
the discrimination tree. In each case the explicit term elaborates and only the search fails.

*The derived category must be the standard one, at high priority.* `HasDerivedCategory.standard`
is declared a local instance at priority `100000`, as in
`PushforwardCommutesCompletionToposCriterion.lean`, and not at the default priority that
`PushforwardTopoi.lean` uses. This is not cosmetic: the derived-completion development
(`AlgebraicGeometry.RingedSite.derivedCompletion`) and the topos-level derived direct image
(`Stacks.Cohomology.DerivedPushforward.derivedPushforward`, and with it
`CategoryTheory.Functor.mapDerivedCategory` and the round-trip isomorphisms) otherwise resolve
`CategoryTheory.HasDerivedCategory` to instances with *different morphism universes*, and a
statement mixing them does not typecheck. That is the concrete reason `PushforwardTopoi.lean`,
which proves [Stacks, Tag 099J] at the default priority, contains no occurrence of
`derivedCompletion` at all: at that priority it could not have.

## Main results

* `RingedToposHom.isIso_derivedCompletionPushforwardComparison_denseRestrict`:
  the ringed-sites case of [Stacks, Tag 0A0G] at the dense-subsite restriction.
* `RingedToposHom.nonempty_iso_derivedPushforward_derivedCompletion_denseRestrict`:
  the display `Rr_*(E^∧) ≅ (Rr_*E)^∧` for the restriction, at every object.
* `RingedToposHom.nonempty_iso_mapDerivedCategory_derivedCompletion_denseReplacement`:
  the display `D(g_*)(K^∧) ≅ (D(g_*)K)^∧` for the replacement equivalence, at every object.

## No attribute

Nothing here carries `@[stacks 0A0G]`. These are statements about the two *equivalences* of the
[Stacks, Tag 03CR] square, not about an arbitrary morphism of ringed topoi; the tag's
registrations stay where they are.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance 100000] HasDerivedCategory.standard

variable (X : RingedTopos.{u, u, u}) {C' : Type u} [SmallCategory C']
  (J' : GrothendieckTopology C') (v : X.C ⥤ C') [v.IsDenseSubsite X.J J']
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))
  [I.toSheafOfModules.IsFiniteType]
  [∀ U : C', HasWeakSheafify (J'.over U) AddCommGrpCat.{u}]
  [∀ U : C', (J'.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasWeakSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Additivity of the direct image along the replacement equivalence.** This is
`AlgebraicGeometry.RingedToposHom.pushforwardModules_additive`, which is already a global
instance; it is restated keyed on `denseReplacementHom` because instance search does not find it
at that morphism. Its target `denseReplacement X J' v` is a reducible abbreviation for a structure
literal, whose fields reduce away under the reducible transparency of the discrimination tree —
the same gap `PushforwardTopoi.lean` documents and keys around for its own uses. The explicit
term elaborates; only the search fails. It is needed here to form `D(g_*)`, which is
`CategoryTheory.Functor.mapDerivedCategory` and so requires its functor to be additive. -/
local instance additive_pushforwardModules_denseReplacementHom :
    (pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v)).Additive :=
  pushforwardModules_additive.{u, u, u, u, u, u} (denseReplacementHom X J' v)

/-- **`D(g_*)`**, the equivalence of derived categories induced by the dense-subsite replacement
`g : X ⟶ X'`. It is `CategoryTheory.Functor.mapDerivedCategory` of the direct image of sheaves of
modules along `g`, which is an equivalence by `PushforwardTopoi.lean`; this is the functor the
[Stacks, Tag 03CR] reduction applies to a complex on `X` before pushing it along the square's
middle arrow. -/
abbrev denseReplacementMapDerived :=
  (pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v)).mapDerivedCategory

/-- **The ideal sheaf `v^{-1}ℐ · 𝒪_{X'}` on the dense-subsite replacement**, built out of
`ℐ ⊂ 𝒪_X` by Section 52.7 along the restriction morphism of ringed sites
`AlgebraicGeometry.RingedToposHom.denseRestrictSite`.

This is the sheaf of ideals of `𝒪_{X'}` that the ringed-sites case of [Stacks, Tag 0A0G] pairs
with `ℐ` at that morphism, and therefore the one along which the completions on `X'` below are
taken. -/
abbrev denseReplacementIdeal : SheafOfModules.Submodule
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseReplacement X J' v).toRingedSite.O)) :=
  RingedSite.inverseImageIdealSheaf.{u} (denseRestrictSite X J' v) I

/-- `v^{-1}ℐ · 𝒪_{X'}` is of finite type, because `ℐ` is. This is
`AlgebraicGeometry.RingedSite.isFiniteType_inverseImageIdealSheaf`, restated at the replacement
site, whose presentation as a structure literal keeps instance search from finding it. -/
instance isFiniteType_denseReplacementIdeal :
    (denseReplacementIdeal X J' v I).toSheafOfModules.IsFiniteType :=
  RingedSite.isFiniteType_inverseImageIdealSheaf.{u}
    (denseRestrictSite X J' v) I inferInstance

/-- [Stacks, Tag 099F] at the replacement site and `v^{-1}ℐ · 𝒪_{X'}`: the inclusion of the
derived-complete objects has a left adjoint, so the derived completion functor along that ideal
exists. Restated for the same reason as `isFiniteType_denseReplacementIdeal`. -/
instance isRightAdjoint_ι_isDerivedComplete_denseReplacementIdeal :
    (ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u}
      (denseReplacement X J' v).toRingedSite (denseReplacementIdeal X J' v I))).IsRightAdjoint :=
  RingedSite.isRightAdjoint_ι_isDerivedComplete.{u}
    (denseReplacement X J' v).toRingedSite (denseReplacementIdeal X J' v I)

/-- **The ringed-sites case of [Stacks, Tag 0A0G] at the dense-subsite restriction `X' ⟶ X`.**
The canonical comparison map `(Rr_*E)^∧ ⟶ Rr_*(E^∧)` is invertible at every `E`, the completion
on `X` being taken along `ℐ` and the one on `X'` along `v^{-1}ℐ · 𝒪_{X'}`.

This is a direct instance of
`RingedSite.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType`:
the inverse of the replacement equivalence is a morphism of ringed *sites*, so the ringed-sites
case applies to it with nothing to transport. -/
theorem isIso_derivedCompletionPushforwardComparison_denseRestrict
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseReplacement X J' v).toRingedSite.O))) :
    IsIso ((RingedSite.derivedCompletionPushforwardComparison.{u}
      (denseRestrictSite X J' v) I (denseReplacementIdeal X J' v I)
      (RingedSite.pushforwardIdealCompatible_inverseImageIdealSheaf.{u}
        (denseRestrictSite X J' v) I)).app E) :=
  RingedSite.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType.{u}
    (denseRestrictSite X J' v) I E

/-- **The display of [Stacks, Tag 0A0G] at the dense-subsite restriction**, as an isomorphism of
objects: `Rr_*(E^∧) ≅ (Rr_*E)^∧` for every `E`. This is
`isIso_derivedCompletionPushforwardComparison_denseRestrict` read as an isomorphism and
inverted. -/
theorem nonempty_iso_derivedPushforward_derivedCompletion_denseRestrict
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseReplacement X J' v).toRingedSite.O))) :
    Nonempty ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
          (denseRestrictSite X J' v).toRingedToposSiteHom).obj
        ((RingedSite.derivedCompletion (denseReplacement X J' v).toRingedSite
          (denseReplacementIdeal X J' v I)).obj E) ≅
      (RingedSite.derivedCompletion X.toRingedSite I).obj
        ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
          (denseRestrictSite X J' v).toRingedToposSiteHom).obj E)) :=
  have := isIso_derivedCompletionPushforwardComparison_denseRestrict X J' v I E
  ⟨(asIso ((RingedSite.derivedCompletionPushforwardComparison.{u}
    (denseRestrictSite X J' v) I _ (RingedSite.pushforwardIdealCompatible_inverseImageIdealSheaf.{u}
      _ _)).app E)).symm⟩

/-- **The display of [Stacks, Tag 0A0G] across the dense-subsite replacement equivalence**:
`D(g_*)(K^∧) ≅ (D(g_*)K)^∧` for every `K`, the completion on `X` taken along `ℐ` and the one on
`X'` along `v^{-1}ℐ · 𝒪_{X'}`.

This is the statement the [Stacks, Tag 03CR] reduction needs about the square's left-hand arrow,
and it is deduced from the statement about the *restriction* rather than proved again. Write `A`
for `(D(g_*)K)^∧`. Since `D(g_*)` is an equivalence, `A ≅ D(g_*)B` for some `B`, and
`Rr_*(D(g_*)B) ≅ B` by
`AlgebraicGeometry.RingedToposHom.derivedPushforwardDenseRestrictMapIso`; so `Rr_*A ≅ B` and
hence `D(g_*)(Rr_*A) ≅ A`. On the other hand
`nonempty_iso_derivedPushforward_derivedCompletion_denseRestrict` at `D(g_*)K` gives
`Rr_*A ≅ (Rr_*(D(g_*)K))^∧ ≅ K^∧`, again by that same identification. Applying `D(g_*)` to the
second chain and comparing with the first yields the display.

Only existence is asserted, and only existence is needed: see "Only existence is needed" in the
module documentation. -/
theorem nonempty_iso_mapDerivedCategory_derivedCompletion_denseReplacement
    (K : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))) :
    Nonempty ((denseReplacementMapDerived X J' v).obj
        ((RingedSite.derivedCompletion X.toRingedSite I).obj K) ≅
      (RingedSite.derivedCompletion (denseReplacement X J' v).toRingedSite
          (denseReplacementIdeal X J' v I)).obj
        ((denseReplacementMapDerived X J' v).obj K)) := by
  -- `R(g⁻¹)_* ⋙ D(g_*) ≅ 𝟭`, the round trip of `PushforwardTopoi.lean`
  have i := (Stacks.Cohomology.DerivedPushforward.derivedPushforwardCompEquivIso
      (denseReplacementInv X J' v) (denseReplacementHom X J' v)).symm ≪≫
    derivedPushforwardRoundTripIso X J' v
  -- the display at `D(g_*)K`, with `Rr_*(D(g_*)K) ≅ K`
  obtain ⟨d⟩ := nonempty_iso_derivedPushforward_derivedCompletion_denseRestrict X J' v I
    ((denseReplacementMapDerived X J' v).obj K)
  refine ⟨(denseReplacementMapDerived X J' v).mapIso
    ((d ≪≫ (RingedSite.derivedCompletion X.toRingedSite I).mapIso
      (derivedPushforwardDenseRestrictMapIso X J' v K)).symm ≪≫
      ((derivedPushforwardDenseReplacementInvIso X J' v).app _).symm) ≪≫ i.app _⟩

end AlgebraicGeometry.RingedToposHom

end

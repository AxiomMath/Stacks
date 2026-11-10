module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffineQuasiCoherent
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel

/-!
# The twisted inverse image of a closed immersion of `FTS S`, at the locally small model

`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImage.lean` proves
[Stacks, Tag 0AA2] at `CategoryTheory.HasDerivedCategory.standard`, where the morphisms of
`D(𝒪_X)` live in `Type (u + 1)`. `HasDerivedCategory` carries the localized category as *data*,
so that statement says nothing about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model at which `D(𝒪_X)` has
the direct sums Brown representability ([Stacks, Tag 0A8G]) asks for and therefore the only one
at which the existence of `i^!` ([Stacks, Tag 0A9E]) is available. This file restates the tag
there.

The restatement is not an attribute deletion: `R ℰom(𝒪_Z, -)` itself is pinned. The abbreviation
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupport`
resolves its `HasDerivedCategory` instance at declaration time, so the functor the standard-model
statement is about is a different functor from the one below, and the predicate asserting that a
right adjoint agrees with it is a different predicate. Both are rebuilt here.

## Main definitions

* `Stacks.Duality.LocallySmall.derivedSheafHomExactSupport` — the right derived functor
  `R ℰom(𝒪_Z, -) : D(𝒪_W) ⥤ D(𝒪_Z)` of sheaf Hom with exact support along a closed immersion,
  at the locally small derived categories.
* `Stacks.Duality.LocallySmall.IsDerivedSheafHomRightAdjoint` — the conclusion of
  [Stacks, Tag 0A9X] for one closed immersion and one candidate right adjoint, at those
  categories.
* `Stacks.Duality.LocallySmall.Tag0A9XHypothesis` — that conclusion quantified over all closed
  immersions, which is what the restatement below consumes.

## Main results

* `Stacks.Duality.LocallySmall.derivedModulePushforwardSheafHomExactSupportAdjunction` —
  **[Stacks, Tag 0A76] at the locally small derived categories**: `Ri_* ⊣ R ℰom(𝒪_Z, -)`.
* `Stacks.Duality.LocallySmall.isBoundedBelow_derivedSheafHomExactSupport_obj` —
  `R ℰom(𝒪_Z, -)` is left t-exact there.
* `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts` — **[Stacks, Tag 0AA2] at
  the locally small derived categories**, in the reduction form that carries the conclusion of
  [Stacks, Tag 0A9X] as a hypothesis. **That hypothesis is no longer hypothetical**: it is
  `Stacks.Duality.LocallySmall.tag0A9XHypothesis` of
  `StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHomLocallySmall.lean`,
  and the tag with it discharged is
  `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion` there.
* `Stacks.Duality.LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine` — the
  same **with `i^!` produced rather than taken as a parameter**, for an affine source. This is
  the composition with [Stacks, Tag 0A9E] that the standard model cannot express at all, and it
  is what the transport was for; its unconditional form, with `h0A9X` discharged, is
`Stacks.Duality.LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional`
  in that same file.

## Implementation notes

**What is proved here, and where the rest is.** The content of [Stacks, Tag 0AA2] is the
*restatement* step: in Situation 48.16.1 the hypotheses [Stacks, Tag 0A9X] asks of a closed
immersion — quasi-compactness and quasi-separatedness of the target, and pseudo-coherence of the
immersion — are automatic. That step is model-free, and it is what
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts` proves, taking the conclusion
of [Stacks, Tag 0A9X] at this model as the explicit hypothesis `h0A9X` — exactly as the reduction
form `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts` does at the standard model. The two
forms are kept apart because the reduction is the restatement step on its own, independent of how
[Stacks, Tag 0A9X] is proved.

**`h0A9X` is no longer hypothetical.** The predicate
`Stacks.Duality.LocallySmall.Tag0A9XHypothesis` is *proved*, as
`Stacks.Duality.LocallySmall.tag0A9XHypothesis` in the sibling file
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHomLocallySmall.lean`, and
the two statements below with it discharged are
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion` and
`Stacks.Duality.LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional`
there. The discharge at the standard model, `Stacks.Duality.tag0A9XHypothesis`, still says
nothing here: it is about the standard-model predicate.

**How [Stacks, Tag 0A9X] crossed, and what was not re-pinned.** Its one non-formal input is
part (1) of [Stacks, Tag 0A78],
`AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus`, whose proof
rests on part (1) of [Stacks, Tag 0A6H]
(`AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent`) and so on
[Stacks, Tag 06Z0] in the packaging
`AlgebraicGeometry.StandardModel.exists_isBoundedBelow_iso_mapDerivedCategory`. That spine is a
dozen or more files, two of them near a thousand lines, and one of them
(`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportQuasicoherent.lean`) would
have to be split, part (1) from part (2), because its part (2) genuinely uses the standard model.
**None of it was re-pinned.** Instead part (1) of [Stacks, Tag 0A78] is restated with no derived
category in it at all — for `s : K ⟶ J` a K-injective resolution, the complex `ℰom(𝒪_Z, J)` has
quasi-coherent cohomology vanishing in low degrees — proved in that form from the standard-model
statement, and read back at an arbitrary model; the file is
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportQuasicoherentAnyModel.lean`
(this library). A statement about complexes and quasi-isomorphisms only is model-agnostic and
crosses for free;
this is the route part (2) of [Stacks, Tag 08D5] was transported by in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBoundAnyModel.lean`. The
mathematics of [Stacks, Tag 06Z0] at this model is in the tree independently, as
`AlgebraicGeometry.derivedTilde_isEquivalence` and
`AlgebraicGeometry.derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel`.

**No `attribute [local instance] HasDerivedCategory.standard`.** That attribute is what the file
exists to remove. The derived categories here are the global instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and
`SheafOfModules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which agree by `rfl` on the two
interchangeable spellings `AlgebraicGeometry.Scheme.Modules W` and
`SheafOfModules (structureSheafRing W.toRingedSpace)` of the category of
`𝒪_W`-modules; that is what lets the quasi-coherent subcategory, which is stated in the first
spelling, and sheaf Hom with exact support, which is stated in the second, meet in one statement
with no `attribute [local instance 10000]` to force them together. A free
`[HasDerivedCategory.{w} _]` binder would *not* do: a binder is found for the spelling it is
written in and not for the other, so the two halves of
`Stacks.Duality.LocallySmall.IsDerivedSheafHomRightAdjoint` would be taken at different models.

**`AlgebraicGeometry.Scheme.Modules.pushforward` and
`RingedSpaceModuleAdjunction.modulePushforward`** are the same functor in the two spellings, and
the quasi-coherence of the cohomology of `Ri_*` is read off the model-free
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom`,
which being stated at a free model is available at this one — this is the idiom of
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_affine`.

## References

* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality.LocallySmall

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-! ### `R ℰom(𝒪_Z, -)` at the locally small derived categories -/

/-- Sheaf Hom with exact support has a pointwise total right derived functor at the locally small
derived categories: sheaves of modules form a Grothendieck abelian category, so every complex of
them admits a quasi-isomorphism into a K-injective complex, and that criterion
([Stacks, Tag 070K]) is model-free. -/
instance hasPointwiseRightDerivedFunctor_sheafHomExactSupport :
    ((closedQuotient i).sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (structureSheafRing (closedQuotient i).X)) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- **`R ℰom(𝒪_Z, -) : D(𝒪_W) ⥤ D(𝒪_Z)` at the locally small derived categories.** This is
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupport`
with the model left to the global locally small instances rather than resolved at
`CategoryTheory.HasDerivedCategory.standard`; being the same total right derived functor at a
different model, it is a different functor. -/
abbrev derivedSheafHomExactSupport :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (closedQuotient i).X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing (closedQuotient i).Z)) :=
  ((closedQuotient i).sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing (closedQuotient i).X)) (ComplexShape.up ℤ))

/-- The canonical map from sheaf Hom with exact support to its right derived functor, at the
locally small derived categories. -/
abbrev derivedSheafHomExactSupportComparison :
    (closedQuotient i).sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSheafHomExactSupport i :=
  ((closedQuotient i).sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing (closedQuotient i).X)) (ComplexShape.up ℤ))

/-- **Stacks Project, Tag 0A76, at the locally small derived categories.** Derived pushforward
along a closed immersion of schemes, read as a closed quotient morphism of ringed spaces, is left
adjoint to the right derived functor of sheaf Hom with exact support: `Ri_* ⊣ R ℰom(𝒪_Z, -)`.

The abstract input `Stacks.DerivedFunctor.derivedAdjunction` is stated at a free
`[HasDerivedCategory.{w} _]` binder, so the only thing the standard model was supplying is the
model itself. -/
@[stacks 0A76 "at the locally small derived categories, the model at which the direct-sum and \
  Brown-representability statements about D(O_X) have content; the standard-model form is \
  RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.\
  derivedModulePushforwardSheafHomExactSupportAdjunction, \
  which is about a different pair of categories"]
def derivedModulePushforwardSheafHomExactSupportAdjunction :
    (modulePushforward (closedQuotient i).i).mapDerivedCategory ⊣ derivedSheafHomExactSupport i :=
  Stacks.DerivedFunctor.derivedAdjunction
    (closedQuotient i).modulePushforwardSheafHomExactSupportAdjunction
    (derivedSheafHomExactSupport i) (derivedSheafHomExactSupportComparison i)
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- **Boundedness below is preserved by `R ℰom(𝒪_Z, -)` at the locally small derived
categories.** The right derived functor of sheaf Hom with exact support is left t-exact: a
bounded-below injective resolution is K-injective and therefore computes the derived functor
degreewise, and an additive functor preserves zero objects. The input
`Stacks.DerivedFunctor.isGE_totalRightDerived_obj` is model-free. -/
theorem isBoundedBelow_derivedSheafHomExactSupport_obj
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing (closedQuotient i).X)))
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow ((derivedSheafHomExactSupport i).obj K) := by
  obtain ⟨n, hn⟩ := hK
  have hGE : K.IsGE n := (DerivedCategory.isGE_iff K n).2 hn
  have h := Stacks.DerivedFunctor.isGE_totalRightDerived_obj
    (closedQuotient i).sheafHomExactSupport K n
  exact ⟨n, (DerivedCategory.isGE_iff _ n).1 h⟩

/-! ### The conclusion of Tag 0A9X at the locally small derived categories -/

/-- The bounded-below objects of `D_QCoh(𝒪_Z)` at the locally small derived category, as a
property of its objects. -/
abbrev isBoundedBelowQuasiCoherent (V : Scheme.{u}) :
    ObjectProperty (quasiCoherentDerivedCategory V) :=
  fun K => DerivedCategoryB.IsBoundedBelow K.obj

/-- **The conclusion of [Stacks, Tag 0A9X] for one closed immersion `i : Z ⟶ W` and one candidate
right adjoint `a` of `Ri_*`, at the locally small derived categories:** on the bounded-below part
of `D_QCoh(𝒪_W)` the functor `a` agrees with the right derived functor of sheaf Hom with exact
support of [Stacks, Tag 0A76], that is, with `R𝓗om_{𝒪_W}(𝒪_Z, -)`.

This is `Stacks.Duality.IsDerivedSheafHomRightAdjoint` at a different model, hence a different
predicate: both the quasi-coherent derived categories and the functor it compares `a` to are
taken at `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
def IsDerivedSheafHomRightAdjoint
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z) : Prop :=
  Nonempty
    ((ObjectProperty.ι (isBoundedBelowQuasiCoherent W) ⋙ a ⋙
        (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
          (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι) ≅
      (ObjectProperty.ι (isBoundedBelowQuasiCoherent W) ⋙
        (DerivedCategoryB.derivedCategoryB (A := W.Modules)
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι ⋙
        derivedSheafHomExactSupport i))

/-! ### The restriction of `Ri_*` to `D_QCoh` for an affine morphism -/

/-- **Derived direct image along an affine morphism of schemes preserves quasi-coherent
cohomology, at the locally small derived categories.** This is part (1) of [Stacks, Tag 08D5] for
an affine morphism; it is what makes `Ri_*` restrict to `D_QCoh` with no hypothesis supplied, for
`i` a closed immersion.

It is the model-free
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom`,
which being stated at an arbitrary chosen model of the two derived categories is available
here. -/
theorem isQuasicoherent_homology_derivedPushforward_of_isAffineHom {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsAffineHom i] (K : quasiCoherentDerivedCategory Z) (n : ℤ) :
    ((DerivedCategory.homologyFunctor W.Modules n).obj
      ((derivedPushforward i).obj K.obj)).IsQuasicoherent :=
  AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom
    i K.obj K.2 n

/-- **The restriction of `Ri_*` to `D_QCoh` for an affine morphism of schemes**, at the locally
small derived categories and with no quasi-coherence hypothesis supplied: it is discharged by
`Stacks.Duality.LocallySmall.isQuasicoherent_homology_derivedPushforward_of_isAffineHom`. A closed
immersion is affine, so this is the functor `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` whose right
adjoint is `i^!`. -/
abbrev affineHomQuasiCoherentDerivedPushforward {Z W : Scheme.{u}} (i : Z ⟶ W) [IsAffineHom i] :
    quasiCoherentDerivedCategory Z ⥤ quasiCoherentDerivedCategory W :=
  quasiCoherentDerivedPushforward i (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i)

/-! ### Tag 0AA2 at the locally small derived categories -/

/-- The statement of [Stacks, Tag 0A9X] at the locally small derived categories, as a hypothesis:
for a pseudo-coherent closed immersion into a quasi-compact and quasi-separated scheme, any right
adjoint of the derived direct image on complexes with quasi-coherent cohomology is derived sheaf
Hom out of the structure sheaf of the closed subscheme, on bounded-below complexes.

The right adjoint appears as an explicit parameter `a` together with the adjunction that
characterises it, so no existence statement is used and nothing is chosen. The derived direct
image it is adjoint to is the canonical
`Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward`, a closed immersion being
affine; no quasi-coherence hypothesis is quantified over. -/
def Tag0A9XHypothesis : Prop :=
  ∀ {Z W : Scheme.{u}} (j : Z ⟶ W) [IsClosedImmersion j],
    CompactSpace W → QuasiSeparatedSpace W → PseudoCoherent j →
    ∀ (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z),
      (affineHomQuasiCoherentDerivedPushforward j ⊣ a) → IsDerivedSheafHomRightAdjoint j a

/-- **Stacks Project, Tag 0AA2 (Lemma 48.17.4), at the locally small derived categories.** In
Situation 48.16.1, let `i : X ⟶ Y` be a morphism of `FTS S` whose underlying morphism of schemes
is a closed immersion, and let `a` be a right adjoint of
`Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then `a`, which is `i^!`, is derived sheaf Hom out of `𝒪_X`:
`i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)` on bounded-below complexes with quasi-coherent cohomology.

This is the transport of `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts` off
`CategoryTheory.HasDerivedCategory.standard`. It is at this model and not that one that `i^!`
exists: the existence statement is [Stacks, Tag 0A9E], whose proof runs Brown representability
([Stacks, Tag 0A8G]) and so needs coproducts of `D(𝒪_X)` indexed by the morphism universe, which
at the standard model is `u + 1` and are not there — the composition of that tag with the
standard-model form of this one is a universe-level type error, not a missing lemma. At the
locally small model the coproducts are
`AlgebraicGeometry.Scheme.Modules.hasColimitsOfShape_discrete_derivedCategory`, and
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isAffine`
is [Stacks, Tag 0A9E] for an affine scheme here.

The source proves the tag by saying that it is a restatement of [Stacks, Tag 0A9X]; the
restatement is exactly the discharge of that tag's hypotheses in Situation 48.16.1 — by
`AlgebraicGeometry.FTS.compactSpace`,
`AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace` and
`AlgebraicGeometry.FTS.pseudoCoherent_left_of_isClosedImmersion` — and that is what is proved
here. This is the reduction form, which takes the conclusion of [Stacks, Tag 0A9X] at this model
as the hypothesis `h0A9X`. **That hypothesis is no longer hypothetical**: it is
`Stacks.Duality.LocallySmall.tag0A9XHypothesis` of
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHomLocallySmall.lean`, and
the tag with it discharged is
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion` there. The
reduction is kept because it is the restatement step on its own, independent of how
[Stacks, Tag 0A9X] is proved. The preservation of quasi-coherent cohomology by `Ri_*`, which the
restriction of `Ri_*` to `D_QCoh` needs, is *not* a hypothesis either — it is part (1) of
[Stacks, Tag 08D5] for an affine morphism, a closed immersion being affine.

This declaration is not registered as [Stacks, Tag 0AA2]: the full statement, with `i^!`
produced for every object of `FTS S` and no affineness or quasi-affineness hypothesis, is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`. -/
theorem isDerivedSheafHomRightAdjoint_of_fts (h0A9X : Tag0A9XHypothesis.{u})
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (i : X ⟶ Y)
    [IsClosedImmersion i.left]
    (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
    (adj : affineHomQuasiCoherentDerivedPushforward i.left ⊣ a) :
    IsDerivedSheafHomRightAdjoint i.left a :=
  h0A9X i.left inferInstance inferInstance
    (FTS.pseudoCoherent_left_of_isClosedImmersion i) a adj

/-! ### `i^!` is no longer a parameter when the source is affine -/

/-- **The restriction of `Ri_*` to `D_QCoh` that [Stacks, Tag 0A9E] produces a right adjoint of
is the one [Stacks, Tag 0AA2] is about.** For a morphism of schemes that is affine as well as
quasi-compact and quasi-separated, with quasi-compact target,
`Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward` and
`Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward` are the same functor: both
are `Stacks.Duality.quasiCoherentDerivedPushforward` at a proof of the same `Prop`, and the two
proofs — part (1) of [Stacks, Tag 08D5] for an affine morphism and for a quasi-compact
quasi-separated one — are equal by proof irrelevance.

At `CategoryTheory.HasDerivedCategory.standard` there is nothing to say: the two functors are
between different categories there, [Stacks, Tag 0A9E] not being available at that model at
all. -/
theorem affineHomQuasiCoherentDerivedPushforward_eq_qcqsRestrictedDerivedPushforward
    {Z W : Scheme.{u}} (j : Z ⟶ W) [IsAffineHom j] [QuasiCompact j] [QuasiSeparated j]
    [CompactSpace W] :
    affineHomQuasiCoherentDerivedPushforward j =
      Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward j :=
  rfl

/-- **Stacks Project, Tag 0AA2 (Lemma 48.17.4) with `i^!` produced rather than assumed, for an
affine source.** In Situation 48.16.1, let `i : X ⟶ Y` be a morphism of `FTS S` whose underlying
morphism of schemes is a closed immersion, and let `X` be affine. Then `Ri_*` *has* a right
adjoint, and that right adjoint — `i^!` — is derived sheaf Hom out of `𝒪_X`:
`i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)` on bounded-below complexes with quasi-coherent cohomology.

**This is the statement the transport was for.** Every other form of the tag in this tree takes
`i^!` as an explicit parameter `a` together with its adjunction, because the existence statement
[Stacks, Tag 0A9E] is proved by Brown representability ([Stacks, Tag 0A8G]) and so needs
coproducts of `D(𝒪_X)` indexed by the morphism universe, which at
`CategoryTheory.HasDerivedCategory.standard` is `u + 1` and are not there; the two statements are
then about different categories and do not compose at all. At the locally small model they do:
`Stacks.Duality.AffineGeneration.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isAffine` is
[Stacks, Tag 0A9E] with no hypothesis for an affine source, its functor is the one above by
`affineHomQuasiCoherentDerivedPushforward_eq_qcqsRestrictedDerivedPushforward`,
and the conclusion follows from
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts`.

`h0A9X` is **no longer hypothetical**: it is
`Stacks.Duality.LocallySmall.tag0A9XHypothesis` of
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHomLocallySmall.lean`, and
this statement with it discharged is
`Stacks.Duality.LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional`
there. What remains is the affineness of `X`, the hypothesis under which [Stacks, Tag 09IS] — the
compact generation of `D_QCoh(𝒪_X)`, which Brown representability consumes — is proved; it is not
needed by the restatement itself, and [Stacks, Tag 09IS] for an arbitrary object of `FTS S` is
open.

This declaration is not registered as [Stacks, Tag 0AA2]: the full statement, with `i^!`
produced for every object of `FTS S` and no affineness or quasi-affineness hypothesis, is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`. -/
theorem exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine
    (h0A9X : Tag0A9XHypothesis.{u})
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (i : X ⟶ Y)
    [IsClosedImmersion i.left] [IsAffine X.left] :
    ∃ (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left),
      Nonempty (affineHomQuasiCoherentDerivedPushforward i.left ⊣ a) ∧
      IsDerivedSheafHomRightAdjoint i.left a := by
  obtain ⟨a, ⟨adj⟩⟩ :=
    Stacks.Duality.AffineGeneration.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isAffine
      (f := i.left)
  exact ⟨a, ⟨adj⟩, isDerivedSheafHomRightAdjoint_of_fts h0A9X i a adj⟩

end Stacks.Duality.LocallySmall

end

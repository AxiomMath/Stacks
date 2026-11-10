module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffineQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestriction
public import StacksFrontier.CategoryTheory.Triangulated.CompactGenerationAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# `D_QCoh(𝒪_X)` is compactly generated for a quasi-affine scheme

Compact generation of `D_QCoh` passes from a scheme to any of its quasi-compact open subschemes.
Let `j : U ⟶ X` be a quasi-compact open immersion with `X` quasi-compact. Then

* `j^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_U)` is left adjoint to `Rj_* : D_QCoh(𝒪_U) ⥤ D_QCoh(𝒪_X)`,
  which is `Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrictAdjunction`;
* `Rj_*` commutes with direct sums indexed by `Type u` ([Stacks, Tag 08DZ]);
* `Rj_*` is fully faithful, because `j` is an open immersion, so an object of `D_QCoh(𝒪_U)`
  killed by `Rj_*` is zero.

Those are exactly the hypotheses of
`CategoryTheory.Pretriangulated.isCompactlyGenerated_of_reflects_isZero`, so the image under `j^*`
of a compact generator of `D_QCoh(𝒪_X)` is a compact generator of `D_QCoh(𝒪_U)`.

Applied to the quasi-compact open immersion `X ⟶ Spec Γ(X, ⊤)` of a quasi-affine scheme, with the
affine case of [Stacks, Tag 09IS] on the right, this gives **[Stacks, Tag 09IS] for every
quasi-affine scheme** — a strictly larger class than the affine schemes: the punctured affine
plane is quasi-affine and not affine
(`Stacks.Examples.PinchedPlane.puncturedPlane_isQuasiAffine`).

## Main results

The first two items are in the namespace `Stacks.Duality.OpenImmersion`; the remaining names are
relative to the namespace `Stacks.Duality`.

* `isZero_of_isZero_quasiCoherentDerivedPushforward` — an object of `D_QCoh(𝒪_U)` whose derived
  pushforward along an open immersion vanishes is zero.
* `isCompactlyGenerated_quasiCoherentDerivedCategory_of_isOpenImmersion` and
  `exists_isCompactObject_isWeakTriangulatedGenerator_of_isOpenImmersion` — **compact generation
  of `D_QCoh` passes to a quasi-compact open subscheme**, in the family form of
  [Stacks, Tag 09SQ] and in the single-generator form.
* `QuasiAffineGeneration.exists_isCompactObject_isWeakTriangulatedGenerator_of_isQuasiAffine` —
  **[Stacks, Tag 09IS] for a quasi-affine scheme**: `D_QCoh(𝒪_X)` has a single compact generator.
* `QuasiAffineGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory_of_isQuasiAffine` and
  `…_derivedQuasiCoherent_of_isQuasiAffine` — the same in the
  `CategoryTheory.Pretriangulated.IsCompactlyGenerated` form, at the two spellings of the category
  of `𝒪_X`-modules.
* `QuasiAffineGeneration.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isQuasiAffine` and
  its exact companion — the conclusion of [Stacks, Tag 0A9E] for a quasi-compact quasi-separated
  morphism out of a quasi-affine scheme into a quasi-compact scheme.
* `QuasiAffineGeneration.isLeftAdjoint_derivedQuasiCoherentι_of_isQuasiAffine` and its exact
  companion — **[Stacks, Tag 0CR0] with no hypothesis** for a quasi-affine scheme.
* `LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isQuasiAffine` —
  **[Stacks, Tag 0AA2]** with the affineness of the source weakened to quasi-affineness.

## Implementation notes

**What this does and does not reach.** [Stacks, Tag 09IS] asserts the existence of a single
perfect generator of `D_QCoh(𝒪_X)` for every quasi-compact quasi-separated `X`. The source proves
it by the induction principle [Stacks, Tag 08DR] over the quasi-compact opens of `X`, and that
induction *builds up* from an affine open to larger opens; the transfer carried out here goes the
other way, *down* from a scheme to a quasi-compact open of it, so starting from the affine case it
reaches exactly the schemes admitting a quasi-compact open immersion into an affine scheme, i.e.
the quasi-affine ones ([Stacks, Tag 01P6]). The step of the source's induction is carried out
in `StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean`; the
caveat recorded on the affine case in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/AffineQuasiCoherent.lean` continues to
name what is missing — [Stacks, Tag 09IQ] at a quasi-compact quasi-separated scheme and the
implication *perfect ⇒ compact* of [Stacks, Tag 09M1], the latter resting on the Hom formula of
[Stacks, Tag 08DQ], of which the library has only closure properties of a dévissage with no base
case.

Nothing here needs either of those two: the affine base case produces a generator already
exhibited as *compact*, and compactness, not perfectness, is what travels along `j^*`. So the
generator produced below is likewise compact rather than perfect.

**The transfer is cheap and the direction matters.** Both halves are formal. Compactness of
`j^* P` is the adjunction bijection together with the commutation of `Rj_*` with direct sums;
generation is the adjunction bijection together with full faithfulness of `Rj_*`. Neither uses
that `j^*` is fully faithful — it is not — and neither uses a triangulated structure. They are
`CategoryTheory.isCompactObject_map_of_adjunction` and
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_reflects_isZero` of
`StacksFrontier/CategoryTheory/Triangulated/CompactGenerationAdjunction.lean`.

**The model.** Everything is at the locally small derived category of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, supplied by instance search, as in the
affine file: [Stacks, Tag 0A8G] asks for direct sums indexed by the *morphism* universe, and only
at this model is that universe `u`. No `attribute [local instance] HasDerivedCategory.standard`
appears, and none may: the three inputs —
`Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrictAdjunction`,
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit` and
`DerivedPushforward.LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward`
— are available here precisely because the first two are stated at a free `HasDerivedCategory`
binder and the third at the locally small model.

**What [Stacks, Tag 0AA2] still needs.** The implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/AffineQuasiCoherent.lean` record that
closing [Stacks, Tag 0AA2] needs two things: the transport of
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImage.lean` off
`CategoryTheory.HasDerivedCategory.standard`, *and* [Stacks, Tag 09IS] for the source of the
closed immersion, an arbitrary object of `FTS S`. The first of those is now available —
`Stacks.Duality.LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional`
of `StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHomLocallySmall.lean` —
so the affineness of `X.left` there is the *only* thing left, and it is there only to make
[Stacks, Tag 09IS] available. The theorem at the end of this file weakens it to
quasi-affineness; removing it outright still waits on the tag at a quasi-compact quasi-separated
scheme.

**`j` is quasi-separated for free.** An open immersion is a monomorphism, hence a quasi-separated
morphism, so only `QuasiCompact j` is an instance argument; for `j` the inclusion of a
quasi-compact open of a quasi-separated scheme it is automatic, and for `X.toSpecΓ` out of a
quasi-affine scheme it is Mathlib's instance for a quasi-compact source.

## References

* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality.OpenImmersion

/-! ### Restriction along an open immersion, on the quasi-coherent derived categories -/

section Restrict

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Restriction along an open immersion preserves quasi-coherent cohomology**, in the form of
the hypothesis `hres` of `Stacks.Duality.OpenImmersion.quasiCoherentDerivedRestrict`. This is
`Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict` read on an object of
`D_QCoh(𝒪_X)`. -/
theorem isQuasicoherent_homology_derivedRestrict
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor U.Modules i).obj
      ((derivedRestrict j).obj K.obj)).IsQuasicoherent :=
  derivedCategoryB_derivedRestrict j K.obj K.2 i

/-- **`j^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_U)`** along an open immersion, with the preservation of
quasi-coherence discharged by
`Stacks.Duality.OpenImmersion.isQuasicoherent_homology_derivedRestrict`. -/
abbrev restrictedDerivedRestrict :
    Stacks.Duality.quasiCoherentDerivedCategory X ⥤
      Stacks.Duality.quasiCoherentDerivedCategory U :=
  quasiCoherentDerivedRestrict j (isQuasicoherent_homology_derivedRestrict j)

/-- `j^*` restricted to the quasi-coherent derived categories is compatible with the inclusions:
`(restricted j^*) ⋙ ι ≅ ι ⋙ j^*`, by definition of the restriction. -/
abbrev restrictedDerivedRestrictCompιIso :
    restrictedDerivedRestrict j ⋙ (DerivedCategoryB.derivedCategoryB (A := U.Modules)
        (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι ≅
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ derivedRestrict j :=
  (DerivedCategoryB.derivedCategoryB (A := U.Modules)
    (SheafOfModules.isQuasicoherent U.ringCatSheaf)).liftCompιIso _
      (isQuasicoherent_homology_derivedRestrict j)

/-- The restriction of `j^*` to the quasi-coherent derived categories commutes with the shift,
because its composite with the fully faithful inclusion does. -/
instance commShift_restrictedDerivedRestrict :
    (restrictedDerivedRestrict j).CommShift ℤ :=
  Functor.CommShift.ofComp (restrictedDerivedRestrictCompιIso j) ℤ

/-- The restriction of `j^*` to the quasi-coherent derived categories is additive, because its
composite with the faithful additive inclusion is. -/
instance additive_restrictedDerivedRestrict : (restrictedDerivedRestrict j).Additive :=
  haveI : (restrictedDerivedRestrict j ⋙ (DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι).Additive :=
    Functor.additive_of_iso (restrictedDerivedRestrictCompιIso j).symm
  Functor.additive_of_comp_faithful (restrictedDerivedRestrict j)
    (DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι

end Restrict

/-! ### `Rj_*` reflects the zero object -/

section Reflect

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((Stacks.Duality.derivedPushforward j).obj K.obj)).IsQuasicoherent)

/-- **An object of `D_QCoh(𝒪_U)` killed by `Rj_*` is zero**, for `j : U ⟶ X` an open immersion.
The inclusion of `D_QCoh` is additive, so the vanishing may be read in `D(𝒪_X)`; `j^*` is additive
too, so `j^* Rj_* E` vanishes; and the counit `j^* Rj_* E ⟶ E` is invertible because `j` is an
open immersion ([Stacks, Tag 08DF]),
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_counit`. The inclusion is
faithful, so the vanishing descends to `D_QCoh(𝒪_U)`.

This is full faithfulness of `Rj_*` in the only form the generation argument consumes. -/
theorem isZero_of_isZero_quasiCoherentDerivedPushforward
    (E : Stacks.Duality.quasiCoherentDerivedCategory U)
    (h : IsZero ((Stacks.Duality.quasiCoherentDerivedPushforward j hpush).obj E)) : IsZero E := by
  have h₁ : IsZero ((Stacks.Duality.derivedPushforward j).obj E.obj) :=
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map_isZero h
  have h₂ : IsZero E.obj :=
    ((derivedRestrict j).map_isZero h₁).of_iso
      (asIso ((derivedRestrictPushforwardAdjunction j).counit.app E.obj)).symm
  rw [IsZero.iff_id_eq_zero]
  refine (DerivedCategoryB.derivedCategoryB (A := U.Modules)
    (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι.map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 h₂

end Reflect

/-! ### Compact generation passes to a quasi-compact open subscheme -/

section Transfer

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [AlgebraicGeometry.QuasiCompact j] [CompactSpace X]

/-- The adjunction `j^* ⊣ Rj_*` on the quasi-coherent derived categories of a quasi-compact open
immersion into a quasi-compact scheme, with both preservation hypotheses discharged: the one for
`Rj_*` by part (1) of [Stacks, Tag 08D5] and the one for `j^*` by exactness of restriction. -/
abbrev restrictedDerivedRestrictAdjunction :
    restrictedDerivedRestrict j ⊣ Stacks.Duality.quasiCoherentDerivedPushforward j
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j) :=
  quasiCoherentDerivedRestrictAdjunction j (isQuasicoherent_homology_derivedRestrict j)
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)

/-- **`Rj_*` commutes with direct sums indexed by `Type u`** on the quasi-coherent derived
categories of a quasi-compact open immersion into a quasi-compact scheme: [Stacks, Tag 08DZ] at
the locally small model. -/
theorem preservesColimitsOfShape_discrete_restrictedDerivedPushforward (α : Type u) :
    PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward j
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)) :=
  DerivedPushforward.LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward
    j _ α

/-- Local instance form of the commutation of `Rj_*` with direct sums. -/
private instance instPreservesColimitsOfShapeDiscreteRestrictedDerivedPushforward
    (α : Type u) :
    PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward j
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)) :=
  preservesColimitsOfShape_discrete_restrictedDerivedPushforward j α

include j in
/-- **Compact generation of `D_QCoh` passes to a quasi-compact open subscheme.** Let
`j : U ⟶ X` be a quasi-compact open immersion with `X` quasi-compact. If `D_QCoh(𝒪_X)` is
compactly generated then so is `D_QCoh(𝒪_U)`: the restrictions `j^*(E i)` of a compact generating
family form one.

This is `CategoryTheory.Pretriangulated.isCompactlyGenerated_of_reflects_isZero` for the
adjunction `j^* ⊣ Rj_*`, whose two inputs are [Stacks, Tag 08DZ] at the locally small model and
the full faithfulness of `Rj_*` along an open immersion. -/
theorem isCompactlyGenerated_quasiCoherentDerivedCategory_of_isOpenImmersion
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory U) :=
  isCompactlyGenerated_of_reflects_isZero (restrictedDerivedRestrictAdjunction j)
    (isZero_of_isZero_quasiCoherentDerivedPushforward j _) hX

include j in
/-- **A single compact generator of `D_QCoh` restricts to one on a quasi-compact open
subscheme.** The single-generator form of
`isCompactlyGenerated_quasiCoherentDerivedCategory_of_isOpenImmersion`, which is the shape
[Stacks, Tag 09IS] states. -/
theorem exists_isCompactObject_isWeakTriangulatedGenerator_of_isOpenImmersion
    (hX : ∃ P : Stacks.Duality.quasiCoherentDerivedCategory X,
      IsCompactObject.{u} P ∧ (ObjectProperty.singleton P).IsWeakTriangulatedGenerator) :
    ∃ P : Stacks.Duality.quasiCoherentDerivedCategory U,
      IsCompactObject.{u} P ∧ (ObjectProperty.singleton P).IsWeakTriangulatedGenerator := by
  obtain ⟨P, hc, hg⟩ := hX
  have : (Stacks.Duality.quasiCoherentDerivedPushforward j
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)).Additive :=
    (restrictedDerivedRestrictAdjunction j).right_adjoint_additive
  exact ⟨(restrictedDerivedRestrict j).obj P,
    isCompactObject_map_of_adjunction (restrictedDerivedRestrictAdjunction j) hc,
    ObjectProperty.isWeakTriangulatedGenerator_singleton_map_of_reflects_isZero
      (restrictedDerivedRestrictAdjunction j)
      (isZero_of_isZero_quasiCoherentDerivedPushforward j _) hg⟩

end Transfer

end Stacks.Duality.OpenImmersion

/-! ### Tag 09IS for a quasi-affine scheme -/

namespace Stacks.Duality.QuasiAffineGeneration

/-- **[Stacks, Tag 09IS] for a quasi-affine scheme.** `D_QCoh(𝒪_X)` is generated by a single
compact object.

A quasi-affine scheme is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an open immersion
([Stacks, Tag 01P6], Mathlib's `AlgebraicGeometry.Scheme.IsQuasiAffine`), so this is the affine
case `AffineGeneration.exists_isCompactObject_isWeakTriangulatedGenerator_of_isAffine`
restricted along that immersion by
`OpenImmersion.exists_isCompactObject_isWeakTriangulatedGenerator_of_isOpenImmersion`.
The generator is therefore the restriction to `X` of the structure sheaf of `Spec Γ(X, ⊤)` in
degree zero, which is `𝒪_X` in degree zero — the source's own generator. -/
@[stacks 09IS "FOR A QUASI-AFFINE SCHEME, and with the generator exhibited as a COMPACT rather \
  than a perfect object. This weakens the affine hypothesis of \
  Stacks.Duality.AffineGeneration.exists_isCompactObject_isWeakTriangulatedGenerator_of_isAffine \
  but does NOT reach the tag's quasi-compact quasi-separated statement. The route is the reverse \
  of the source's: compact generation passes DOWN from a scheme to a quasi-compact open of it, by \
  Stacks.Duality.OpenImmersion.\
  isCompactlyGenerated_quasiCoherentDerivedCategory_of_isOpenImmersion, \
  so from the affine case it reaches exactly the schemes with a quasi-compact open immersion into \
  an affine scheme, the quasi-affine ones. The source's own induction over the quasi-compact \
  opens, Tag 08DR, goes the other way and still needs Tag 09IQ at a quasi-compact \
  quasi-separated scheme and the implication perfect implies compact of Tag 09M1, neither of \
  which is in the library; see the implementation notes of \
  StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/AffineQuasiCoherent.lean. Nothing \
  here needs either: the generator is compact by construction and compactness is what the \
  consumers of the tag ask for"]
theorem exists_isCompactObject_isWeakTriangulatedGenerator_of_isQuasiAffine (X : Scheme.{u})
    [X.IsQuasiAffine] :
    ∃ P : Stacks.Duality.quasiCoherentDerivedCategory X,
      IsCompactObject.{u} P ∧ (ObjectProperty.singleton P).IsWeakTriangulatedGenerator :=
  Stacks.Duality.OpenImmersion.exists_isCompactObject_isWeakTriangulatedGenerator_of_isOpenImmersion
    X.toSpecΓ
    (Stacks.Duality.AffineGeneration.exists_isCompactObject_isWeakTriangulatedGenerator_of_isAffine
      (Spec Γ(X, ⊤)))

/-- **[Stacks, Tag 09IS] for a quasi-affine scheme, in the form [Stacks, Tag 09SQ] defines and
Brown representability consumes**, at the spelling of `D_QCoh(𝒪_X)` over
`AlgebraicGeometry.Scheme.Modules X` — the one the statement of [Stacks, Tag 0A9E] uses. -/
@[stacks 09IS "FOR A QUASI-AFFINE SCHEME, in the IsCompactlyGenerated form of Tag 09SQ at the \
  Scheme.Modules spelling of the category, which is the one Tag 0A9E's statement uses; see \
  Stacks.Duality.QuasiAffineGeneration.\
  exists_isCompactObject_isWeakTriangulatedGenerator_of_isQuasiAffine \
  for the full caveat"]
theorem isCompactlyGenerated_quasiCoherentDerivedCategory_of_isQuasiAffine (X : Scheme.{u})
    [X.IsQuasiAffine] :
    IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X) :=
  Stacks.Duality.OpenImmersion.isCompactlyGenerated_quasiCoherentDerivedCategory_of_isOpenImmersion
    X.toSpecΓ
    (Stacks.Duality.AffineGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory_of_isAffine
      (Spec Γ(X, ⊤)))

/-- **[Stacks, Tag 09IS] for a quasi-affine scheme**, at the spelling of `D_QCoh(𝒪_X)` over
`AlgebraicGeometry.SheafOfModules X.ringCatSheaf` — the one the hypothesis of [Stacks, Tag 0CR0]
uses. The two spellings are the same type with separately declared `HasDerivedCategory`
instances. -/
@[stacks 09IS "FOR A QUASI-AFFINE SCHEME, in the IsCompactlyGenerated form of Tag 09SQ at the \
  SheafOfModules spelling of the category, which is the one Tag 0CR0's hypothesis uses; see \
  Stacks.Duality.QuasiAffineGeneration.\
  exists_isCompactObject_isWeakTriangulatedGenerator_of_isQuasiAffine \
  for the full caveat"]
theorem isCompactlyGenerated_derivedQuasiCoherent_of_isQuasiAffine (X : Scheme.{u})
    [X.IsQuasiAffine] :
    IsCompactlyGenerated.{u}
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory :=
  isCompactlyGenerated_quasiCoherentDerivedCategory_of_isQuasiAffine X

/-! ### The consequences: Tags 0A9E, 0CR0 and 0AA2 with the hypothesis weakened -/

section Consequences

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f] [CompactSpace Y] [X.IsQuasiAffine]

/-- **`Rf_*` has a right adjoint for a morphism out of a quasi-affine scheme.** Let
`f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes with `X` quasi-affine and `Y`
quasi-compact. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint — the twisted inverse
image `f^×`.

This special case is not registered as [Stacks, Tag 0A9E]; the tag, for a morphism of
quasi-compact quasi-separated schemes, is
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`. -/
theorem isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isQuasiAffine :
    (Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward f).IsLeftAdjoint :=
  open DerivedPushforward in
  isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated
    f (isCompactlyGenerated_quasiCoherentDerivedCategory_of_isQuasiAffine X)

/-- **`Rf_*` has an exact right adjoint for a morphism out of a quasi-affine scheme.** -/
theorem exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward_of_isQuasiAffine :
    ∃ (a : _) (adj : Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward f ⊣ a)
      (_ : a.CommShift ℤ), adj.IsTriangulated :=
  open DerivedPushforward in
  exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated
    f (isCompactlyGenerated_quasiCoherentDerivedCategory_of_isQuasiAffine X)

end Consequences

/-- **[Stacks, Tag 0CR0] with no hypothesis, for a quasi-affine scheme.** The inclusion
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint, the coherator `DQ_X`.

This declaration is not registered as [Stacks, Tag 0CR0]: the tag for every quasi-compact
quasi-separated scheme, with no compact-generation hypothesis, is
`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι` in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCoherator.lean`. -/
theorem isLeftAdjoint_derivedQuasiCoherentι_of_isQuasiAffine (X : Scheme.{u})
    [X.IsQuasiAffine] :
    (Stacks.Duality.derivedQuasiCoherent.{u, u} X).ι.IsLeftAdjoint :=
  Stacks.Duality.Coherator.isLeftAdjoint_derivedQuasiCoherentι X
    (isCompactlyGenerated_derivedQuasiCoherent_of_isQuasiAffine X)

/-- **[Stacks, Tag 0CR0] with the coherator exhibited as exact, with no hypothesis, for a
quasi-affine scheme.**

This declaration is not registered as [Stacks, Tag 0CR0]: the tag for every quasi-compact
quasi-separated scheme, with no compact-generation hypothesis, is
`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι` in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCoherator.lean`. -/
theorem exists_isTriangulated_rightAdjoint_derivedQuasiCoherentι_of_isQuasiAffine (X : Scheme.{u})
    [X.IsQuasiAffine] :
    ∃ (DQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
        (Stacks.Duality.derivedQuasiCoherent.{u, u} X).FullSubcategory)
      (adj : (Stacks.Duality.derivedQuasiCoherent.{u, u} X).ι ⊣ DQ) (_ : DQ.CommShift ℤ),
      adj.IsTriangulated :=
  Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_derivedQuasiCoherentι X
    (isCompactlyGenerated_derivedQuasiCoherent_of_isQuasiAffine X)

end Stacks.Duality.QuasiAffineGeneration

/-! ### Tag 0AA2 for a quasi-affine source -/

namespace Stacks.Duality.LocallySmall

/-- **[Stacks, Tag 0AA2] at the locally small derived categories, for a closed immersion whose
source is quasi-affine.** Let `S` be a Noetherian scheme, let `X`, `Y` be objects of `FTS S` and
let `i : X ⟶ Y` be a morphism whose underlying morphism of schemes is a closed immersion with `X`
quasi-affine. Then `Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint, and that right adjoint
— `i^!` — is derived sheaf Hom out of `𝒪_X`.

This is
`Stacks.Duality.LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional`
with its affineness hypothesis weakened: that hypothesis is there only because
[Stacks, Tag 09IS] — the compact generation of `D_QCoh(𝒪_X)`, which Brown representability
consumes — is available for affine schemes, and also for quasi-affine ones. The
restatement itself uses neither. [Stacks, Tag 09IS] for an arbitrary object of `FTS S` remains
open, so the hypothesis is weakened and not removed.

This declaration is not registered as [Stacks, Tag 0AA2]: the full statement, with `i^!`
produced for every object of `FTS S` and no affineness or quasi-affineness hypothesis, is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`. -/
theorem exists_isDerivedSheafHomRightAdjoint_of_fts_of_isQuasiAffine
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (i : X ⟶ Y)
    [IsClosedImmersion i.left] [X.left.IsQuasiAffine] :
    ∃ (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left),
      Nonempty (affineHomQuasiCoherentDerivedPushforward i.left ⊣ a) ∧
      IsDerivedSheafHomRightAdjoint i.left a := by
  obtain ⟨a, ⟨adj⟩⟩ :=
    QuasiAffineGeneration.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isQuasiAffine
      (f := i.left)
  exact ⟨a, ⟨adj⟩, isDerivedSheafHomRightAdjoint_of_fts tag0A9XHypothesis.{u} i a adj⟩

end Stacks.Duality.LocallySmall

end

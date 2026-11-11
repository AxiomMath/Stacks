module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# From a separated universally injective morphism to an affine scheme

Let `X` be a quasi-compact algebraic space over `S` and let `p : X ⟶ Spec A` be a morphism to
an affine object of the site.  The last two paragraphs of the proof of Stacks 07V6 run as
follows: `p` is separated and of finite type, it is universally injective, hence locally
quasi-finite by Stacks 06RW, hence representable by Stacks 0418, so `X` is a scheme; and that
scheme is affine by Serre's criterion, Stacks 01XF.  This file formalizes exactly that passage,
for an arbitrary target affine object of the site, with the three assertions about `X` that the
source's earlier paragraphs supply left as hypotheses.

## Main results

* `AlgebraicGeometry.Space.discreteTopology_points_pullback_of_universallyInjective`: the fibre
  of a universally injective morphism over a field-valued point of its target has discrete
  point space — indeed at most one point.
* `AlgebraicGeometry.Space.isRepresentable_of_isSeparated_of_universallyInjective`: a
  universally injective morphism locally of finite type is locally quasi-finite,
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_universallyInjective` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyVanishingAffineness.lean`), the step the source
  performs with Stacks 07V4 and Stacks 06RW; such a
  morphism with separated source over a representable target has representable source, so `X`
  is a scheme.
* `AlgebraicGeometry.Space.isAffineSpace_of_isSeparated_of_universallyInjective`: and that
  scheme is affine.
* `…CohomologyVanishingSituation.isAffineSpace_of_isSeparated_of_universallyInjective`: the
  same conclusion for the canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)` of Situation 07UY, which is
  the assertion of Stacks 07V6 for a situation whose base is terminal, with the four inputs of
  the source's proof that this development does not have carried as named hypotheses.
* `AlgebraicGeometry.Space.isSeparated_to_affine_of_isAffine_isIntegralHom_isSurjective`: the
  separatedness hypothesis `hsep` above, discharged outright for an algebraic space admitting a
  surjective integral morphism from an *affine* object of the site.  This is the shape in which
  the separatedness step is available to Stacks 07VP, whose hypotheses hand over such a cover.

## Implementation notes

*Why Stacks 07V6 is not registered.*  The declarations here are the tail of the source's proof
and not the tag.  Four assertions about `X` are hypotheses below, and none of them is available
in this development for a general situation as in Stacks 07UY:

* `hsep`, separatedness of `p`, is the assertion of Stacks 07V5, proved as
  `…CohomologyVanishingSituation.isSeparated_toSpecGlobalFunctions` in
  `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyVanishingSeparatedMorphism.lean` for a
  situation at the module universe of the structure sheaf; the declaration below keeps a
  general module universe.
* `hinj`, universal injectivity of `p`, is the assertion of Stacks 07V4.  The two declarations
  carrying that tag are in
  `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyVanishingClosedPoints.lean`: one proves the
  separation of two distinct *closed* points of `|X|` only, and the other proves universal
  injectivity from two hypotheses about every field-valued point of `X` which are not
  consequences of Situation 07UY.  Neither discharges this one.
* `hft`, that `p` is locally of finite type, is the conclusion of the source's third paragraph:
  `Γ(X, 𝒪_X)[x_1, …, x_n] → B` is surjective for an affine étale chart `U = Spec B` of `X`.
  That paragraph is not formalized anywhere in this development.  Its first ingredient is
  available: the identification `φ^*φ_*𝒪_U = t_*𝒪_R` for the étale chart `φ : U ⟶ X` and its
  kernel pair `R` is the degree-zero clause of part (1) of Stacks 073K, which is proved
  unconditionally as `AlgebraicGeometry.Space.flatBaseChangeZero`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFlatBaseChangeQuasicoherent.lean`).  What is
  absent is the rest: the generators of `C` over `t : B → C` coming from the surjection
  `B ⊗_A B → C` which separatedness of `p` provides, the surjection
  `𝒪_X[z_1, …, z_n] → φ_*𝒪_U` they define, the vanishing hypothesis of the situation applied
  to its kernel, and the passage from finite type of `B` over `A` to finite type of `p`.
* `h07V0` is clause (1) of Stacks 07V0 in the Zariski-cohomology shape that Stacks 01XF
  consumes, the predicate
  `AlgebraicGeometry.Space.SchemeAffineOverFirstZariskiCohomologyVanishing` already used by the
  proof of Stacks 07V5.  The étale-cohomology clause (1) *is* proved, as
  `…CohomologyVanishingSituation.isZero_firstCohomology_of_isAffineHom`, and the comparison of
  the two cohomologies in degree one — Stacks 03DW — is not: the only carrier of that tag,
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModuleCohomologyDegreeZero.lean`, is
  clause-qualified to degree zero.

Only `hft` is a step of the proof of Stacks 07V6 itself; the other three are assertions of
named neighbouring tags.  Quasi-separatedness of `X` is not used below, and quasi-compactness
is used only to make the representing scheme quasi-compact for Serre's criterion.

*The fibre step.*  Stacks 06RW asks for discreteness of the point space of the fibre of `p`
over every field-valued point of the target.  Universal injectivity gives more: the fibre has
at most one point, because its point space injects into that of the spectrum of the field,
which is a singleton by `AlgebraicGeometry.Space.subsingleton_points_yoneda_siteObject`.  The
orientation of the fibre product is the one Stacks 06RW uses, `pullback g p` for
`g : Spec k ⟶ Spec A`, which is also the orientation in which
`AlgebraicGeometry.Space.UniversallyInjective` is stated, so no comparison of the two fibre
products is needed.

*From representability to affineness.*  Stacks 0418 gives relative representability of `p`
along the Yoneda embedding; the target being representable, `X` is representable, which is
`CategoryTheory.Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable`.
The representing object `X.reprX` is an object of the site, its presheaf is quasi-compact
because `X` is, hence its scheme is a compact space by
`AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj`, and `X.reprW` is an
isomorphism, hence an affine morphism by
`AlgebraicGeometry.Space.isAffineHom_of_isIso`, so `h07V0` applies to it and Stacks 01XF makes
the scheme affine.  The source's "`X` is affine, hence equal to `Spec(A)`" is the affineness
assertion only; the identification of `X` with `Spec A` is not stated here, and `p` is not
shown to be an isomorphism.

## References

* [Stacks Project, Tag 07V6](https://stacks.math.columbia.edu/tag/07V6)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 07V5](https://stacks.math.columbia.edu/tag/07V5)
* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 06RW](https://stacks.math.columbia.edu/tag/06RW)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_CohomologyVanishingAffineScheme :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_CohomologyVanishingAffineScheme
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Separatedness over an affine object from an affine integral cover -/

/-- **An algebraic space admitting a surjective integral morphism from an affine object of the
site is separated over every affine object of the site.**

This is `AlgebraicGeometry.Space.isSeparated_to_affine_of_existsIntegralSurjectiveSchemeCover`
with the cover handed over as data and assumed affine, and it carries no hypothesis at all.
Both of that statement's carried hypotheses, and its quasi-compactness assumption, are consumed
there for the single purpose of making the cover affine: clause (1) of Stacks 07V0 feeds Serre's
criterion Stacks 01XF, and quasi-compactness of `X` is what makes the cover quasi-compact so
that the criterion applies.  With the cover affine from the start none of the three is needed,
so in particular no cohomology-vanishing hypothesis of any kind enters, and Stacks 09YB
(`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_and_refining`) is not appealed
to.

This is the shape in which the separatedness step of the proof of Stacks 07V6 is available to
Stacks 07VP, whose hypotheses hand over exactly such a cover: a surjection onto `X` from an
affine scheme which is finite, hence integral by Stacks 0414,
`AlgebraicGeometry.Space.IsFinite.isIntegralHom`.  It is *not* Stacks 07V5, whose hypotheses are
those of Situation 07UY alone and supply no cover. -/
theorem isSeparated_to_affine_of_isAffine_isIntegralHom_isSurjective
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (W : BigFppfOver B S hS) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (g : yoneda.obj W ⟶ X) (hgsurj : IsSurjective B S hS g)
    (hgint : IsIntegralHom B S hS g)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : X ⟶ yoneda.obj V) :
    IsSeparated B S hS p := by
  have hWsp : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  obtain ⟨hgaff, hgclosed⟩ :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hWsp hX g).1 hgint
  have hcomp : IsSeparated B S hS (g ≫ p) := by
    have hsep := isSeparated_yoneda_map_of_isAffine B S hS (yoneda.preimage (g ≫ p)) hW hV
    rwa [yoneda.map_preimage] at hsep
  exact isSeparated_of_isSurjective_of_universallyClosed B S hS hWsp hX
    (isAlgebraicSpace_yoneda B S hS V) g p hgsurj hgclosed hcomp

/-! ### Fibres of a universally injective morphism -/

/-- **The fibre of a universally injective morphism over a field-valued point of its target
has at most one point.**  The point space of the fibre injects into the point space of the
spectrum of the field, which is a singleton. -/
theorem subsingleton_points_pullback_of_universallyInjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : UniversallyInjective B S hS f) (p : FieldValuedPoint B S hS Y) :
    Subsingleton (points B S hS (pullback (yonedaEquiv.symm p.value) f)) := by
  have hsub : Subsingleton (points B S hS (yoneda.obj p.siteObject)) :=
    subsingleton_points_yoneda_siteObject B S hS p
  exact ⟨fun a b => hf (yoneda.obj p.siteObject)
    (isAlgebraicSpace_yoneda B S hS p.siteObject) (yonedaEquiv.symm p.value)
    (hsub.elim _ _)⟩

/-- **The fibre of a universally injective morphism over a field-valued point of its target
has discrete point space.**  This is the hypothesis condition (2) of Stacks 06RW asks for. -/
theorem discreteTopology_points_pullback_of_universallyInjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : UniversallyInjective B S hS f) (p : FieldValuedPoint B S hS Y) :
    DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f)) :=
  have := subsingleton_points_pullback_of_universallyInjective B S hS f hf p
  Subsingleton.discreteTopology

/-! ### Local quasi-finiteness, representability and affineness -/

/-- **An algebraic space separated, universally injective and locally of finite type over an
affine object of the site is a scheme.**  The morphism is locally quasi-finite, hence
representable by Stacks 0418, and the target is representable, so the source is too. -/
theorem isRepresentable_of_isSeparated_of_universallyInjective
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : BigFppfOver B S hS) (p : X ⟶ yoneda.obj V)
    (hsep : IsSeparated B S hS p)
    (hft : IsLocallyOfFiniteType B S hS p)
    (hinj : UniversallyInjective B S hS p) :
    X.IsRepresentable :=
  Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable p
    (relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS p hX
      (isAlgebraicSpace_yoneda B S hS V)
      (isLocallyQuasiFinite_of_universallyInjective B S hS hX
        (isAlgebraicSpace_yoneda B S hS V) p hft hinj) hsep)

/-- **The last two paragraphs of the proof of Stacks 07V6.**  A quasi-compact algebraic space
`X` which is separated, universally injective and locally of finite type over an affine object
of the site, and over which the first Zariski cohomology of every quasi-coherent sheaf of
ideals on a scheme affine over `X` vanishes, is an affine algebraic space.

`X` is a scheme by Stacks 0418, that scheme is quasi-compact because `X` is, and the
cohomology hypothesis applied to the isomorphism `X.reprW` — an affine morphism, being an
isomorphism — feeds Serre's criterion, Stacks 01XF.

Stacks 07V6 is *not* registered on this declaration: all four hypotheses are assertions which
Situation 07UY is supposed to supply and this development cannot.  See this file's
implementation notes for each. -/
theorem isAffineSpace_of_isSeparated_of_universallyInjective
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (V : BigFppfOver B S hS) (p : X ⟶ yoneda.obj V)
    (hsep : IsSeparated B S hS p)
    (hft : IsLocallyOfFiniteType B S hS p)
    (hinj : UniversallyInjective B S hS p)
    (h07V0 : SchemeAffineOverFirstZariskiCohomologyVanishing B S hS X) :
    IsAffineSpace B S hS X := by
  have hrep : X.IsRepresentable :=
    isRepresentable_of_isSeparated_of_universallyInjective B S hS hX V p hsep hft hinj
  have hWqc : IsQuasiCompactSpace B S hS (yoneda.obj X.reprX) :=
    IsQuasiCompactSpace.of_iso B S hS hXqc X.reprW.symm
  have hWcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj X.reprX) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hWqc
  have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj X.reprX) :=
    Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal _
      (h07V0 X.reprX X.reprW.hom (isAffineHom_of_isIso X.reprW.hom))
  exact (isAffineSpace_yoneda B S hS X.reprX hWaff).of_iso X.reprW

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m}) (hterminal : IsTerminal T.base)
    (V : BigFppfOver T.site T.base T.containsBase)
    [IsAffine ((BigFppfOver.toScheme T.site T.base T.containsBase).obj V)]
    (e : Γ((BigFppfOver.toScheme T.site T.base T.containsBase).obj V, ⊤) ≃+*
      _root_.AlgebraicGeometry.Space.globalFunctions T.site T.base T.containsBase T.space.1)

/-- **The assertion of Stacks 07V6 for a situation as in Stacks 07UY whose base is terminal**,
with the four inputs of the source's proof that this development does not have carried as named
hypotheses: separatedness of the canonical morphism `p : X ⟶ Spec Γ(X, 𝒪_X)` (Stacks 07V5),
its universal injectivity (Stacks 07V4), that it is locally of finite type (the third paragraph
of the source's proof, through Stacks 073K), and clause (1) of Stacks 07V0 in Zariski
cohomology.  `Spec Γ(X, 𝒪_X)` is presented by an affine object `V` of the site through a ring
isomorphism `Γ(V, 𝒪_V) ≅ Γ(X, 𝒪_X)`.

The tag is not registered: see the implementation notes of this file for why none of the four
hypotheses can be discharged here. -/
theorem isAffineSpace_of_isSeparated_of_universallyInjective
    (hsep : IsSeparated T.site T.base T.containsBase
      (toSpecGlobalFunctions T hterminal V e).hom)
    (hft : IsLocallyOfFiniteType T.site T.base T.containsBase
      (toSpecGlobalFunctions T hterminal V e).hom)
    (hinj : _root_.AlgebraicGeometry.Space.UniversallyInjective T.site T.base T.containsBase
      (toSpecGlobalFunctions T hterminal V e).hom)
    (h07V0 : SchemeAffineOverFirstZariskiCohomologyVanishing T.site T.base T.containsBase
      T.space.1) :
    IsAffineSpace T.site T.base T.containsBase T.space.1 :=
  _root_.AlgebraicGeometry.Space.isAffineSpace_of_isSeparated_of_universallyInjective
    T.site T.base T.containsBase T.space.2 T.quasiCompact V _ hsep hft hinj h07V0

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end

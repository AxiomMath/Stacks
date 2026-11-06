module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentEtaleLocal

/-!
# Descending étale sheaves along a representable cover of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is representable by
schemes and which is surjective and integral, or surjective and proper, or surjective and flat
and locally of finite presentation. Then étale sheaves on `Y` are descent data for the covering
`{X ⟶ Y}`. This is **Stacks 0GFU**.

The source argument is run here. Each of the three conditions is a property of representable
morphisms in the sense of Stacks 02WE, hence is stable under arbitrary base change for free, so
Stacks 0GFT lets one test effective descent along an étale covering of `Y`. The definition of an
algebraic space (Stacks 025Y) supplies a one-member étale covering `{a : U ⟶ Y}` by a *scheme*,
and the two base changes of `f` that Stacks 0GFT asks about — along `a`, and along the structure
morphism of `U ×_Y U` — then have representable target: `U` is a scheme by construction, and
`U ×_Y U` is a scheme because `a` is representable, the diagonal of `Y` being so. That is the
reduction of the source to the case of a scheme target, and it is what this file proves.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtaleDescentOverRepresentable` is effective descent restricted
  to the morphisms whose *target is representable*, that is, the case of a scheme base. It is
  what the three statements below are granted, and it is strictly weaker than any of them: the
  target of the morphism in each conclusion is an arbitrary algebraic space.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_descentOverRepresentable` is
  the étale-local reduction, for an arbitrary property of morphisms of presheaves stable under
  base change;
* `AlgebraicGeometry.Space.isRepresentable_pullback_of_yoneda` is the representability of the
  overlap of two scheme-valued points of an algebraic space;
* `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_surjective_integral`,
  `…_of_surjective_proper` and `…_of_surjective_flat_locallyOfFinitePresentation` are the three
  cases of Stacks 0GFU.

## Implementation notes

The statements are for `AlgebraicGeometry.Space.spacesEtalePseudofunctor`, the pseudofunctor of
spaces-étale inverse images, exactly as Stacks 0GFS and Stacks 0GFT are in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleGlobalDescent` and
`…SpacesEtaleDescentEtaleLocal`; the source states all three for the small étale topoi, which
are the same topoi by Stacks 03G1.

The case over a scheme base is not available in this library and is carried as an explicit
hypothesis: the source deduces it from Étale Cohomology, Lemmas 0GEZ, 0GF0 and 0GF2, none of
which this library has, and those in turn rest on the dévissage of Stacks 0GF1 and, for the
integral case, on the base-change theorem of Stacks 0EYP. Each of the three statements below
carries the hypothesis for its own property only, so that no case borrows the conclusion of
another.

The three conditions are *alternatives*, not simultaneous assumptions, so each case is a
separate statement. Each is phrased with its conjuncts as separate hypotheses, which is how the
library states a property of a representable morphism, and they are combined internally into
the single conjunct property the reduction runs on.

## References

* [Stacks Project, Tag 0GFU](https://stacks.math.columbia.edu/tag/0GFU)
* [Stacks Project, Tag 0GFT](https://stacks.math.columbia.edu/tag/0GFT)
* [Stacks Project, Tag 02WE](https://stacks.math.columbia.edu/tag/02WE)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_SpacesEtaleDescentRepresentableCover :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_SpacesEtaleDescentRepresentableCover
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Representability of the overlap of two scheme-valued points -/

/-- The fibre product of two morphisms from representable presheaves into an algebraic space
over `S` is representable: such a morphism is representable because the diagonal of an algebraic
space is, and the fibre product of a representable morphism with a representable presheaf is
represented by an object of the site. -/
theorem isRepresentable_pullback_of_yoneda {Y : AlgebraicSpaces B S hS}
    {T T' : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Y.1) (b : yoneda.obj T' ⟶ Y.1) :
    (pullback a b).IsRepresentable := by
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable a :=
    Functor.relativelyRepresentable.diag_iff.1 Y.property.diagonal_representable a
  exact Functor.IsRepresentable.mk' (hrep.isPullback' b).isoPullback

/-! ### The case of a representable target, and the reduction to it -/

/-- **Effective descent of spaces-étale sheaves along the morphisms with property `Q` whose
target is representable.** This is the case of Stacks 0GFU in which the base is a scheme, the
case the source settles by citing Étale Cohomology, Lemmas 0GEZ, 0GF0 and 0GF2.

It is a strictly weaker assertion than any of the three statements of Stacks 0GFU below, whose
conclusions are about a morphism whose target is an arbitrary algebraic space; passing from this
to those is exactly the étale-local reduction the source performs, and is
`AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_descentOverRepresentable`. -/
abbrev SpacesEtaleDescentOverRepresentable
    (Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) : Prop :=
  ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y'), Y'.1.IsRepresentable → Q f'.hom →
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f')).IsEquivalence

/-- **The étale-local reduction of Stacks 0GFU to a scheme base.** Let `Q` be a property of
morphisms of presheaves on the big fppf site of `S` which is stable under base change, and
suppose that descent of spaces-étale sheaves is effective along every morphism with `Q` whose
target is representable. Then it is effective along every morphism with `Q`.

The scheme atlas of the target provided by Stacks 025Y is a one-member étale covering of it, so
Stacks 0GFT reduces the claim to the two base changes of `f` it names; their targets are the
atlas itself, which is representable, and the fibre product of the atlas with itself over the
target, which is representable by
`AlgebraicGeometry.Space.isRepresentable_pullback_of_yoneda`. -/
theorem isEquivalence_toDescentData_singleton_of_descentOverRepresentable
    (Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [Q.IsStableUnderBaseChange]
    (hQ : SpacesEtaleDescentOverRepresentable B S hS Q)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : Q f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  obtain ⟨T, a, hsurj, hetale⟩ := Y.property.exists_atlas
  have hg : IsEtaleCovering B S hS
      (fun _ : PUnit.{u + 1} => (yoneda.obj T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (fun _ => a) :=
    isEtaleCovering_atlas.{u, u} B S hS Y.property hsurj hetale
  refine isEquivalence_toDescentData_singleton_of_isEtaleCovering B S hS f
    (fun _ : PUnit.{u + 1} => (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
      AlgebraicSpaces B S hS))
    (fun _ => ObjectProperty.homMk a) hg (fun _ => ?_) (fun _ _ => ?_)
  · exact hQ _ inferInstance (Q.pullback_snd f.hom a hf)
  · exact hQ _ (isRepresentable_pullback_of_yoneda B S hS a a)
      (Q.pullback_snd f.hom _ hf)

/-! ### The three cases of Stacks 0GFU -/

section Cases

variable {X Y : AlgebraicSpaces B S hS}

/-- A representable morphism of presheaves on the big fppf site of `S` all of whose represented
base changes have `P` and all of whose represented base changes have `P'` has the conjunction of
the two properties after every represented base change. -/
private theorem presheaf_inf_of {P P' : MorphismProperty Scheme.{u}}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (h : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f)
    (h' : (MorphismProperty.inverseImage P' (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (P ⊓ P') (BigFppfOver.toScheme B S hS)).presheaf f :=
  ⟨h.rep, fun _ _ g fst snd BC => ⟨h.property g fst snd BC, h'.property g fst snd BC⟩⟩

/-- The reduction of `isEquivalence_toDescentData_singleton_of_descentOverRepresentable` for the
presheaf version of a property `P` of schemes, which is stable under base change for free. -/
private theorem isEquivalence_toDescentData_singleton_of_inverseImage
    {P : MorphismProperty Scheme.{u}}
    (hsch : SpacesEtaleDescentOverRepresentable B S hS
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf)
    (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  have := MorphismProperty.relative_isStableUnderBaseChange
    (F := yoneda (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
  exact isEquivalence_toDescentData_singleton_of_descentOverRepresentable B S hS _ hsch f hf

/-- **Stacks 0GFU, the surjective integral case.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is representable by schemes, surjective and integral. Then spaces-étale
sheaves on `Y` are equivalent, via the canonical descent datum, to descent data for the covering
`{X ⟶ Y}`, granted the same assertion for a morphism with representable target. -/
@[stacks 0GFU "the surjective integral case, for the pseudofunctor of spaces-étale inverse \
images, granted the case of a representable target as the hypothesis `hsch`.  Proved here: the \
étale-local reduction of the source, that is, that the conclusion for an arbitrary algebraic \
space `Y` follows from the case in which the target is a scheme -- a scheme atlas of `Y` is a \
one-member étale covering (Tag 025Y), the two base changes of `f` named by Tag 0GFT have \
representable target, and the representable surjective integral morphisms are stable under base \
change (Tag 02WE).  NOT proved, and carried by `hsch`: the case of a scheme target, which the \
source deduces from Etale Cohomology Tag 0GEZ; that lemma is not in this library and rests in \
turn on the devissage of Tag 0GF1 and on the base-change theorem of Tag 0EYP.  The other two \
cases of the source statement are separate declarations with their own hypothesis."]
theorem isEquivalence_toDescentData_singleton_of_surjective_integral
    (hsch : SpacesEtaleDescentOverRepresentable B S hS
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} ⊓ @AlgebraicGeometry.IsIntegralHom.{u})
        (BigFppfOver.toScheme B S hS)).presheaf)
    (f : X ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (hint : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsIntegralHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  exact isEquivalence_toDescentData_singleton_of_inverseImage B S hS hsch f
    (presheaf_inf_of B S hS hsurj hint)

/-- **Stacks 0GFU, the surjective proper case.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is representable by schemes, surjective and proper. Then spaces-étale
sheaves on `Y` are equivalent, via the canonical descent datum, to descent data for the covering
`{X ⟶ Y}`, granted the same assertion for a morphism with representable target. -/
@[stacks 0GFU "the surjective proper case, for the pseudofunctor of spaces-étale inverse \
images, granted the case of a representable target as the hypothesis `hsch`.  Proved here: the \
étale-local reduction of the source, that is, that the conclusion for an arbitrary algebraic \
space `Y` follows from the case in which the target is a scheme -- a scheme atlas of `Y` is a \
one-member étale covering (Tag 025Y), the two base changes of `f` named by Tag 0GFT have \
representable target, and the representable surjective proper morphisms are stable under base \
change (Tag 02WE).  NOT proved, and carried by `hsch`: the case of a scheme target, which the \
source deduces from Etale Cohomology Tag 0GF0; that lemma is not in this library and rests in \
turn on the devissage of Tag 0GF1 and on the proper base-change theorem of Tag 0A3U.  The other \
two cases of the source statement are separate declarations with their own hypothesis."]
theorem isEquivalence_toDescentData_singleton_of_surjective_proper
    (hsch : SpacesEtaleDescentOverRepresentable B S hS
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} ⊓ @AlgebraicGeometry.IsProper.{u})
        (BigFppfOver.toScheme B S hS)).presheaf)
    (f : X ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (hproper : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsProper.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  exact isEquivalence_toDescentData_singleton_of_inverseImage B S hS hsch f
    (presheaf_inf_of B S hS hsurj hproper)

/-- **Stacks 0GFU, the surjective flat locally finitely presented case.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` which is representable by schemes, surjective, flat and
locally of finite presentation. Then spaces-étale sheaves on `Y` are equivalent, via the
canonical descent datum, to descent data for the covering `{X ⟶ Y}`, granted the same assertion
for a morphism with representable target. -/
@[stacks 0GFU "the surjective flat locally-of-finite-presentation case, for the pseudofunctor \
of spaces-étale inverse images, granted the case of a representable target as the hypothesis \
`hsch`.  Proved here: the étale-local reduction of the source, that is, that the conclusion for \
an arbitrary algebraic space `Y` follows from the case in which the target is a scheme -- a \
scheme atlas of `Y` is a one-member étale covering (Tag 025Y), the two base changes of `f` \
named by Tag 0GFT have representable target, and the representable surjective flat morphisms \
locally of finite presentation are stable under base change (Tag 02WE).  NOT proved, and \
carried by `hsch`: the case of a scheme target, which the source deduces from Etale Cohomology \
Tag 0GF2; that lemma is not in this library and rests in turn on the devissage of Tag 0GF1 and \
on the finite domination of an fppf covering of Tag 0CP0.  The other two cases of the source \
statement are separate declarations with their own hypothesis."]
theorem isEquivalence_toDescentData_singleton_of_surjective_flat_locallyOfFinitePresentation
    (hsch : SpacesEtaleDescentOverRepresentable B S hS
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} ⊓ @AlgebraicGeometry.Flat.{u} ⊓
          @AlgebraicGeometry.LocallyOfFinitePresentation.{u})
        (BigFppfOver.toScheme B S hS)).presheaf)
    (f : X ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (hflat : (MorphismProperty.inverseImage (@AlgebraicGeometry.Flat.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (hlfp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  exact isEquivalence_toDescentData_singleton_of_inverseImage B S hS hsch f
    (presheaf_inf_of B S hS (presheaf_inf_of B S hS hsurj hflat) hlfp)

end Cases

end AlgebraicGeometry.Space

end

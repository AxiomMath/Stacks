module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms

/-!
# Stacks 0ARS for the quasi-separatedness axiom of Stacks 0ARN

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0ARN, part (2)** declares `f` *quasi-separated*
when its relative diagonal is quasi-compact, quasi-compactness of a morphism of formal
algebraic spaces being **Stacks 0AJC**; this is
`AlgebraicGeometry.FormalSpace.HasQuasiCompactDiagonal`. **Stacks 0ARS** gives five equivalent
conditions for either separation axiom of Stacks 0ARN. This file proves them for the
quasi-separatedness axiom; the separatedness axiom is treated in
`StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism`, whose machinery — uniform in a
Zariski-local property `P` of morphisms of schemes — is reused here.

The step that makes that reuse possible is a comparison, which this file proves first: for a
morphism whose relative diagonal is representable, quasi-compactness of the relative diagonal
in the sense of Stacks 0AJC is the same as the relative diagonal condition
`AlgebraicGeometry.FormalSpace.HasRelativeDiagonal` for quasi-compactness of morphisms of
schemes, and the same as `AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism`, the a priori
stronger condition that the morphism of presheaves underlying the relative diagonal be
quasi-compact in the sense of **Stacks 03HE**.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_isQuasiCompactULift`: **Stacks 0AM2** in
  the form needed here, for a morphism representable by algebraic spaces the fibre product
  condition of Stacks 0AJC is quasi-compactness of the underlying morphism of presheaves in the
  sense of Stacks 03HE.
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_relative_quasiCompact`: for a morphism
  representable by objects of the site, the fibre product condition of Stacks 0AJC is the
  condition that every represented base change be a quasi-compact morphism of schemes.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_isQuasiSeparatedMorphism` and its
  `…_of_relativelyRepresentable_diag` and `…_of_isFormalAlgebraicSpace` variants: the two
  readings of the quasi-separatedness axiom agree, with the last showing that under the
  hypotheses of Stacks 0ARN itself they never differ.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact`:
  the quasi-separatedness axiom as a relative diagonal condition.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_forall_baseChange`:
  **Stacks 0ARS, clauses (1) and (2)** for the quasi-separatedness axiom.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_forall_affine_baseChange`:
  **Stacks 0ARS, clauses (1) and (3)** for the quasi-separatedness axiom.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_isQuasiSeparated`:
  **Stacks 0ARS, clauses (3) and (4)** for the quasi-separatedness axiom, the absolute notion
  being clause (1) of **Stacks 0AJ7** as recorded in
  `AlgebraicGeometry.FormalSpace.IsQuasiSeparated`.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_of_locallySurjective`,
  `AlgebraicGeometry.FormalSpace.exists_atlas_hasQuasiCompactDiagonal_pullback_snd` and
  `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_of_atlas`: **Stacks 0ARS, clause (5)**
  for the quasi-separatedness axiom — the descent step along one locally surjective morphism
  onto the relative self-product, and the two directions of the covering form of
  Definition 0AIM.
* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_tfae` and
  `AlgebraicGeometry.FormalSpace.isSeparatedMorphism_tfae`: all five conditions of
  **Stacks 0ARS** are equivalent, for each of the two separation axioms of Stacks 0ARN, for a
  morphism of formal algebraic spaces; `AlgebraicGeometry.FormalSpace.separationAxiom_tfae`
  states both together and carries the registration of the whole tag.
* Each of the four clause statements has a `…_of_isFormalAlgebraicSpace` form in which the
  representability hypothesis is discharged, so that nothing is assumed beyond what the source
  assumes.

## What is assumed

Nothing beyond the source. The comparison needs representability of the relative diagonal, and
so do the clause statements, since — unlike the spelling of the separatedness axiom in this
library — the quasi-separatedness axiom does not contain it. That is a genuine hypothesis for
an arbitrary morphism of fppf sheaves, and it appears in the binders of the general forms and
is named in their notes. It is *not* an extra assumption over the source: Stacks 0ARS
hypothesises that `X` and `Y` be formal algebraic spaces, and for a source which is a formal
algebraic space the relative diagonal is representable by objects of the site by **Stacks 0AN2**
together with the representability assertion of **Stacks 0AIP**. Each statement is therefore
given twice over, once with the representability hypothesis carried and once in the source's
own form with it discharged.

## Implementation notes

The comparison of Stacks 0AJC with Stacks 03HE rests on two inputs, both proved in this
library: the agreement of the two notions of a quasi-compact *space* on an algebraic space,
`AlgebraicGeometry.FormalSpace.quasiCompactSpaceAgreesOnAlgebraicSpaces`, and the equivalence
of conditions (2) and (3) of **Stacks 0AJB**,
`AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_isQuasiCompactOnSchemeBaseChanges`. Both
reach this file through
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismComparison`, which also supplies
Stacks 0AM2 itself and the assembly lemma
`AlgebraicGeometry.FormalSpace.isQuasiCompactULift_of_forall_compact`.

The comparison with the relative diagonal condition goes through the Zariski-locality of
quasi-compactness of morphisms of schemes: a represented base change over an arbitrary object
of the site is tested over the affine opens of that object, which again belong to the site, and
an affine object represents a quasi-compact algebraic space, against which Stacks 03HE may be
tested directly. In the other direction a represented base change over a quasi-compact object
has quasi-compact underlying scheme, hence is a quasi-compact algebraic space.

Clauses (1), (2), (3) and (5) are then the specializations to
`P = AlgebraicGeometry.QuasiCompact` of the statements of Stacks 0ARS proved uniformly in `P`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism`, transported across the
comparison. Clause (4) is not of that uniform shape — it names the absolute notion of
Stacks 0AJ7, which is given separately for each axiom — so it is proved here, as the
separatedness case is proved there, from the comparison of the two descriptions
`U ×_X V = X ×_{Δ, X ×_Z X} (U ×_Z V)` of a fibre product of two affine scheme-valued points.
The scheme-level inputs for it are that a quasi-compact morphism into a quasi-compact scheme
has quasi-compact source, and conversely that a morphism from a quasi-compact scheme to an
affine one is quasi-compact.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AM2](https://stacks.math.columbia.edu/tag/0AM2)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 0ARP](https://stacks.math.columbia.edu/tag/0ARP)
* [Stacks Project, Tag 0ARS](https://stacks.math.columbia.edu/tag/0ARS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves is quasi-compact in the sense of Stacks 03HE as soon as its base
changes along maps from compact represented objects are quasi-compact spaces. -/
private theorem isQuasiCompactULift_of_forall_compactSpace
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (p : F ⟶ G)
    (h : ∀ (V : BigFppfOver B S hS), CompactSpace ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ η : (uliftYoneda.{u + 1}).obj V ⟶ G,
        Space.IsQuasiCompactSpaceULift.{u + 1} B S hS (pullback η p)) :
    Space.IsQuasiCompactULift.{u + 1} B S hS p := by
  intro Z _ hZqc g
  obtain ⟨V, c, hVc, hcSurj, hcEtale⟩ := hZqc
  have hcE := (Space.isEtaleULift_iff_relative_etale B S hS c).mp hcEtale
  let k : pullback (c ≫ g) p ⟶ pullback g p :=
    pullback.lift (pullback.fst (c ≫ g) p ≫ c) (pullback.snd (c ≫ g) p)
      (by rw [Category.assoc, pullback.condition])
  have hbig : IsPullback (pullback.fst (c ≫ g) p) (k ≫ pullback.snd g p) (c ≫ g) p := by
    simpa only [k, pullback.lift_snd] using IsPullback.of_hasPullback (c ≫ g) p
  have hsquare : IsPullback k (pullback.fst (c ≫ g) p) (pullback.fst g p) c :=
    (hbig.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback g p)).flip
  obtain ⟨W, γ, hWc, hγSurj, hγEtale⟩ := h V hVc (c ≫ g)
  exact ⟨W, γ ≫ k, hWc,
    Space.relative_comp B S hS hγSurj (Space.relative_of_isPullback B S hS hsquare hcSurj),
    (Space.isEtaleULift_iff_relative_etale B S hS (γ ≫ k)).mpr
      (Space.relative_comp B S hS
        ((Space.isEtaleULift_iff_relative_etale B S hS γ).mp hγEtale)
        (Space.relative_of_isPullback B S hS hsquare hcE))⟩

/-! ### Quasi-compactness of Stacks 0AJC against quasi-compactness of Stacks 03HE -/

/-- For a morphism of fppf sheaves on the big fppf site of `S` representable by algebraic
spaces, the fibre product condition of **Stacks 0AJC** and quasi-compactness of the underlying
morphism of presheaves in the sense of **Stacks 03HE** agree. -/
theorem isQuasiCompact_iff_isQuasiCompactULift {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsQuasiCompact B S hS f ↔ Space.IsQuasiCompactULift.{u + 1} B S hS f.hom := by
  constructor
  · intro hqc
    refine isQuasiCompactULift_of_forall_compactSpace B S hS _ (fun V hV η => ?_)
    exact (isQuasiCompactSpace_iff_isQuasiCompactSpaceULift' B S hS hf
      (IsPullback.of_hasPullback (⟨η⟩ : yonedaSheaf B S hS V ⟶ Y) f)).mp
      (IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges B S hS hqc V hV _ _ _ _
        (IsPullback.of_hasPullback _ f))
  · intro h T hT g W p q sq
    refine (isQuasiCompactSpace_iff_isQuasiCompactSpaceULift' B S hS hf sq).mpr ?_
    exact h _ (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)
      (Space.isQuasiCompactSpaceULift_uliftYoneda.{u + 1} B S hS T
        (@Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj T) hT)) g.hom

/-! ### Quasi-compactness of Stacks 0AJC as a represented condition -/

/-- A presheaf represented by an object of the site which is a quasi-compact algebraic space
over `S` has quasi-compact underlying scheme: in the value universe `Type u` this is
`AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj`, and quasi-compactness
of an algebraic space is unchanged by the universe lift. -/
theorem compactSpace_of_isQuasiCompactSpaceULift_uliftYoneda (V : BigFppfOver B S hS)
    (h : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj V)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj V) :=
  Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    ((Space.isQuasiCompactSpaceULift_comp_uliftFunctor_iff.{u + 1} B S hS
      (yoneda.obj V)).mp h)

/-- For a morphism of fppf sheaves on the big fppf site of `S` representable by objects of the
site, the fibre product condition of **Stacks 0AJC** is the same as asking that every
represented base change of the morphism be a quasi-compact morphism of schemes.

From Stacks 0AJC to the represented condition: quasi-compactness of a morphism of schemes is
Zariski local on the target, so by
`AlgebraicGeometry.FormalSpace.relative_of_affine_test` it is enough to test a represented
base change over an *affine* object of the site, and such an object represents a quasi-compact
algebraic space, against which Stacks 03HE may be tested directly. In the other direction a
represented base change over a quasi-compact object of the site has quasi-compact underlying
scheme, hence is a quasi-compact algebraic space, and
`AlgebraicGeometry.FormalSpace.isQuasiCompactULift_of_forall_compact` assembles those into
Stacks 03HE. -/
theorem isQuasiCompact_iff_relative_quasiCompact {X Y : FppfSheaf B S hS} (a : X ⟶ Y)
    (ha : (fppfYoneda B S hS).relativelyRepresentable a) :
    IsQuasiCompact B S hS a ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS) a := by
  have _ := AlgebraicGeometry.isZariskiLocalAtTarget_quasiCompact'.{u}
  let L := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let e := fppfYonedaCompSheafToPresheaf' B S hS
  rw [isQuasiCompact_iff_isQuasiCompactULift B S hS a
    (isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable B S hS a ha)]
  constructor
  · intro h
    refine relative_of_affine_test' B S hS
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) a ha ?_
    intro U V g p q hU sq
    refine AlgebraicGeometry.quasiCompact_of_compactSpace_of_isAffine _ hU ?_
    refine compactSpace_of_isQuasiCompactSpaceULift_uliftYoneda B S hS V ?_
    refine Space.isQuasiCompactSpaceULift_of_iso B S hS (e.app V) ?_
    refine Space.isQuasiCompactSpaceULift_of_iso B S hS ((sq.map L).flip.isoPullback).symm ?_
    exact h _
      (Space.isAlgebraicSpaceULift_of_iso B S hS (e.app U).symm
        (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U))
      (Space.isQuasiCompactSpaceULift_of_iso B S hS (e.app U).symm
        (Space.isQuasiCompactSpaceULift_uliftYoneda.{u + 1} B S hS U
          (@Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj U) hU)))
      g.hom
  · intro h
    have h' := (relative_fppfYoneda_iff_uliftYoneda' B S hS _ a).mp h
    refine isQuasiCompactULift_of_forall_compactSpace B S hS _ (fun V hV η => ?_)
    have hqc : AlgebraicGeometry.QuasiCompact
        ((BigFppfOver.toScheme B S hS).map (h'.rep.snd η)) := h'.property_snd η
    have hc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (h'.rep.pullback η)) :=
      AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
        ((BigFppfOver.toScheme B S hS).map (h'.rep.snd η))
    exact Space.isQuasiCompactSpaceULift_of_iso B S hS ((h'.rep.isPullback η).flip.isoPullback)
      (Space.isQuasiCompactSpaceULift_uliftYoneda.{u + 1} B S hS _ hc)

/-! ### The two readings of the quasi-separatedness axiom of Stacks 0ARN -/

/-- **The two readings of the quasi-separatedness axiom of Stacks 0ARN, part (2), agree.** For
a morphism of fppf sheaves on the big fppf site of `S` whose relative diagonal is representable
by algebraic spaces over `S`, the condition
`AlgebraicGeometry.FormalSpace.HasQuasiCompactDiagonal` of Stacks 0ARN, part (2) — that the
relative diagonal be quasi-compact in the sense of Stacks 0AJC — and the condition
`AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism` — that the morphism of presheaves
underlying the relative diagonal be quasi-compact in the sense of Stacks 03HE — are the same
condition. This is **Stacks 0AM2** applied to the relative diagonal. -/
theorem hasQuasiCompactDiagonal_iff_isQuasiSeparatedMorphism {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.diagonal f).hom) :
    HasQuasiCompactDiagonal B S hS f ↔ IsQuasiSeparatedMorphism B S hS f :=
  isQuasiCompact_iff_isQuasiCompactULift B S hS (pullback.diagonal f) hf

/-- The agreement of the two readings of the quasi-separatedness axiom of Stacks 0ARN,
part (2), for a morphism whose source has relatively representable absolute diagonal: the
relative diagonal is then representable by objects of the site by **Stacks 0AN2**, hence by
algebraic spaces over `S`. -/
theorem hasQuasiCompactDiagonal_iff_isQuasiSeparatedMorphism_of_relativelyRepresentable_diag
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : (fppfYoneda B S hS).relativelyRepresentable (diag X)) :
    HasQuasiCompactDiagonal B S hS f ↔ IsQuasiSeparatedMorphism B S hS f :=
  hasQuasiCompactDiagonal_iff_isQuasiSeparatedMorphism B S hS f
    (isRepresentableByAlgebraicSpacesULift_hom_of_relativelyRepresentable B S hS _
      (relativelyRepresentable_pullback_diagonal B S hS f hX))

/-- The agreement of the two readings of the quasi-separatedness axiom of Stacks 0ARN,
part (2), for a morphism whose source is a formal algebraic space over `S`: the absolute
diagonal of the source is then representable by objects of the site by **Stacks 0AIP**. Under
the hypothesis of Stacks 0ARN itself the two readings therefore never differ. -/
theorem hasQuasiCompactDiagonal_iff_isQuasiSeparatedMorphism_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasQuasiCompactDiagonal B S hS f ↔ IsQuasiSeparatedMorphism B S hS f :=
  hasQuasiCompactDiagonal_iff_isQuasiSeparatedMorphism_of_relativelyRepresentable_diag B S hS f
    (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)

/-- The quasi-separatedness axiom of Stacks 0ARN, part (2), is the relative diagonal condition
of `AlgebraicGeometry.FormalSpace.HasRelativeDiagonal` for quasi-compactness of morphisms of
schemes, as soon as the relative diagonal is representable by objects of the site. This is what
makes the statements of Stacks 0ARS proved uniformly in a Zariski-local property of morphisms
of schemes in `StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism` available for the
quasi-separatedness axiom. -/
theorem hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f)) :
    HasQuasiCompactDiagonal B S hS f ↔
      HasRelativeDiagonal B S hS (@AlgebraicGeometry.QuasiCompact.{u}) f :=
  isQuasiCompact_iff_relative_quasiCompact B S hS (pullback.diagonal f) hf

/-- The relative diagonal of a base change of `f` is representable by objects of the site as
soon as the relative diagonal of `f` is, being a base change of it. -/
theorem relativelyRepresentable_pullback_diagonal_pullbackSnd {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f))
    {Y' : FppfSheaf B S hS} (g : Y' ⟶ Y) :
    (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal (pullback.snd f g)) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange (fppfYoneda B S hS)).of_isPullback
    (diagonal_isPullback_diagonal' f g) hf

/-! ### Stacks 0ARS, clauses (1) and (2), for quasi-separatedness -/

/-- **Stacks 0ARS, clauses (1) and (2) for the quasi-separatedness axiom of Stacks 0ARN.** A
morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose relative diagonal is
representable by objects of the site is quasi-separated exactly when its base change to every
scheme over the target is quasi-separated.

The hypothesis `hf` is carried: unlike the separatedness axiom, whose spelling in this library
contains representability of the relative diagonal, the quasi-separatedness axiom does not, and
the comparison with the relative diagonal condition of
`AlgebraicGeometry.FormalSpace.HasRelativeDiagonal` needs it. It is discharged for a source
which is a formal algebraic space — the hypothesis of Stacks 0ARS itself — in
`…hasQuasiCompactDiagonal_iff_forall_baseChange_of_isFormalAlgebraicSpace`
below. -/
@[stacks 0ARS "clauses (1) and (2) for the quasi-separated axiom of Stacks 0ARN: a morphism of \
formal algebraic spaces with relatively representable relative diagonal is quasi-separated if \
and only if its base change to every scheme over the target is quasi-separated; the \
representability hypothesis is discharged for a source which is a formal algebraic space in \
`…hasQuasiCompactDiagonal_iff_forall_baseChange_of_isFormalAlgebraicSpace`"]
theorem hasQuasiCompactDiagonal_iff_forall_baseChange {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f)) :
    HasQuasiCompactDiagonal B S hS f ↔
      ∀ (U : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj U ⟶ Y),
        HasQuasiCompactDiagonal B S hS (pullback.snd f g) := by
  have _ := MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
  refine (hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS f hf).trans
    ((hasRelativeDiagonal_iff_forall_baseChange B S hS
      (@AlgebraicGeometry.QuasiCompact.{u}) f).trans ?_)
  exact forall_congr' fun U ↦ forall_congr' fun g ↦
    (hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS
      (pullback.snd f g)
      (relativelyRepresentable_pullback_diagonal_pullbackSnd B S hS f hf g)).symm

/-- **Stacks 0ARS, clauses (1) and (2) for the quasi-separatedness axiom of Stacks 0ARN**, in
the source's own form: a morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose
source is a formal algebraic space is quasi-separated exactly when its base change to every
scheme over the target is quasi-separated. The representability hypothesis of
`AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_forall_baseChange` is discharged
here: the relative diagonal of `f` is a base change of the absolute diagonal of `X`, which is
representable by objects of the site by **Stacks 0AIP**. -/
@[stacks 0ARS "clauses (1) and (2) for the quasi-separated axiom of Stacks 0ARN, in the \
source's form with no extra hypothesis: a morphism of formal algebraic spaces is \
quasi-separated if and only if its base change to every scheme over the target is \
quasi-separated"]
theorem hasQuasiCompactDiagonal_iff_forall_baseChange_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasQuasiCompactDiagonal B S hS f ↔
      ∀ (U : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj U ⟶ Y),
        HasQuasiCompactDiagonal B S hS (pullback.snd f g) :=
  hasQuasiCompactDiagonal_iff_forall_baseChange B S hS f
    (relativelyRepresentable_pullback_diagonal B S hS f
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX))

/-! ### Stacks 0ARS, clauses (1) and (3), for quasi-separatedness -/

/-- **Stacks 0ARS, clauses (1) and (3) for the quasi-separatedness axiom of Stacks 0ARN.** A
morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose relative diagonal is
representable by objects of the site is quasi-separated exactly when its base change to every
*affine* scheme over the target is quasi-separated. Quasi-compactness of morphisms of schemes
is Zariski local on the target, which is what lets the test objects be restricted to the affine
ones.

As in clauses (1) and (2), the hypothesis `hf` is carried, and is discharged for a source which
is a formal algebraic space in
`…hasQuasiCompactDiagonal_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace`
below. -/
@[stacks 0ARS "clauses (1) and (3) for the quasi-separated axiom of Stacks 0ARN: a morphism of \
formal algebraic spaces with relatively representable relative diagonal is quasi-separated if \
and only if its base change to every affine scheme over the target is quasi-separated; the \
representability hypothesis is discharged for a source which is a formal algebraic space in \
`…hasQuasiCompactDiagonal_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace`"]
theorem hasQuasiCompactDiagonal_iff_forall_affine_baseChange {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f)) :
    HasQuasiCompactDiagonal B S hS f ↔
      ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ (g : (fppfYoneda B S hS).obj U ⟶ Y),
          HasQuasiCompactDiagonal B S hS (pullback.snd f g) := by
  have _ := AlgebraicGeometry.isZariskiLocalAtTarget_quasiCompact'.{u}
  refine (hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS f hf).trans
    (((hasRelativeDiagonal_iff_forall_affine_baseChange B S hS
      (@AlgebraicGeometry.QuasiCompact.{u}) f).trans (and_iff_right hf)).trans ?_)
  exact forall_congr' fun U ↦ forall_congr' fun _ ↦ forall_congr' fun g ↦
    (hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS (pullback.snd f g)
      (relativelyRepresentable_pullback_diagonal_pullbackSnd B S hS f hf g)).symm

/-- **Stacks 0ARS, clauses (1) and (3) for the quasi-separatedness axiom of Stacks 0ARN**, in
the source's own form: a morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose
source is a formal algebraic space is quasi-separated exactly when its base change to every
affine scheme over the target is quasi-separated. The representability hypothesis of
`AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_forall_affine_baseChange` is
discharged by **Stacks 0AIP** and **Stacks 0AN2** as before. -/
@[stacks 0ARS "clauses (1) and (3) for the quasi-separated axiom of Stacks 0ARN, in the \
source's form with no extra hypothesis: a morphism of formal algebraic spaces is \
quasi-separated if and only if its base change to every affine scheme over the target is \
quasi-separated"]
theorem hasQuasiCompactDiagonal_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasQuasiCompactDiagonal B S hS f ↔
      ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ (g : (fppfYoneda B S hS).obj U ⟶ Y),
          HasQuasiCompactDiagonal B S hS (pullback.snd f g) :=
  hasQuasiCompactDiagonal_iff_forall_affine_baseChange B S hS f
    (relativelyRepresentable_pullback_diagonal B S hS f
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX))

/-! ### Stacks 0ARS, clauses (3) and (4), for quasi-separatedness -/

/-- **Stacks 0ARS, clauses (3) and (4) for the quasi-separatedness axiom of Stacks 0ARN.** A
morphism `f : X ⟶ Z` of fppf sheaves on the big fppf site of `S` whose target is represented by
an affine scheme of the site and whose relative diagonal is representable by objects of the
site is quasi-separated exactly when the source `X` is quasi-separated as a single sheaf, in the
sense of clause (1) of Stacks 0AJ7 — that is, clause (3) of Stacks 0AJ5: the fibre product over
`X` of any two affine scheme-valued points of `X` has quasi-compact underlying scheme.

Both directions are the argument of the source read through the comparison of the two fibre
product descriptions
`U ×_X V = X ×_{Δ, X ×_Z X} (U ×_Z V)`, which is
`AlgebraicGeometry.FormalSpace.pair_diagonal_square` in one direction and
`AlgebraicGeometry.FormalSpace.diagonal_test_pair_square` in the other. The scheme-level inputs
are that a quasi-compact morphism into a quasi-compact scheme has quasi-compact source, and
conversely that a morphism from a quasi-compact scheme to an affine one is quasi-compact. -/
@[stacks 0ARS "clauses (3) and (4) for the quasi-separated axiom of Stacks 0ARN: a morphism of \
formal algebraic spaces to an affine scheme with relatively representable relative diagonal is \
quasi-separated if and only if its source is a quasi-separated formal algebraic space; the \
representability hypothesis is discharged for a source which is a formal algebraic space in \
`…hasQuasiCompactDiagonal_iff_isQuasiSeparated_of_isFormalAlgebraicSpace`"]
theorem hasQuasiCompactDiagonal_iff_isQuasiSeparated {X : FppfSheaf B S hS}
    {Z : BigFppfOver B S hS} (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (f : X ⟶ (fppfYoneda B S hS).obj Z)
    (hf : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f)) :
    HasQuasiCompactDiagonal B S hS f ↔ IsQuasiSeparated B S hS X := by
  have _ := AlgebraicGeometry.isZariskiLocalAtTarget_quasiCompact'.{u}
  let T := BigFppfOver.toScheme B S hS
  let F := fppfYoneda B S hS
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let _ : F.Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  let _ : PreservesLimitsOfShape WalkingCospan F := fppfYoneda_preservesPullbacks' B S hS
  let _ := hZ
  rw [hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS f hf]
  constructor
  · intro hrel U V P a b p q hU hV sq
    obtain ⟨l, -, -, sp⟩ := pair_diagonal_square' F f a b (F.preimage (a ≫ f))
      (F.preimage (b ≫ f)) (F.map_preimage _) (F.map_preimage _) p q sq
    have hsq := (IsPullback.of_hasPullback (F.preimage (a ≫ f)) (F.preimage (b ≫ f))).map T
    let _ := hU
    let _ := hV
    have _ : CompactSpace (T.obj (pullback (F.preimage (a ≫ f)) (F.preimage (b ≫ f)))) :=
      @Scheme.compactSpace_of_isAffine _ (IsAffine.of_isPullback hsq)
    have _ : AlgebraicGeometry.QuasiCompact (T.map l) := hrel.property _ _ _ sp
    exact AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (T.map l)
  · intro h
    refine relative_of_affine_test' B S hS (@AlgebraicGeometry.QuasiCompact.{u})
      (pullback.diagonal f) hf ?_
    intro U V γ t q hU hs
    obtain ⟨W, p, r, a₀, l, e, -, -, -, -, sq, sp⟩ :=
      diagonal_test_pair_square' F f hf γ t q hs
    have hW : CompactSpace (T.obj W) := h U U W _ _ p r hU hU sq
    let _ := hU
    have _ : IsAffine (T.obj (pullback a₀ a₀)) :=
      IsAffine.of_isPullback ((IsPullback.of_hasPullback a₀ a₀).map T)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.QuasiCompact.{u}) (sp.map T)
      (AlgebraicGeometry.quasiCompact_of_compactSpace_of_isAffine (T.map l) inferInstance hW)

/-- **Stacks 0ARS, clauses (3) and (4) for the quasi-separatedness axiom of Stacks 0ARN**, in
the source's own form: a morphism from a formal algebraic space to a sheaf represented by an
affine scheme of the site is quasi-separated exactly when its source is a quasi-separated
formal algebraic space, quasi-separatedness of a single sheaf being read as clause (1) of
Stacks 0AJ7. The representability hypothesis of
`AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_isQuasiSeparated` is discharged by
**Stacks 0AIP** and **Stacks 0AN2**. -/
@[stacks 0ARS "clauses (3) and (4) for the quasi-separated axiom of Stacks 0ARN, in the \
source's form with no extra hypothesis: a morphism from a formal algebraic space to an affine \
scheme is quasi-separated if and only if its source is a quasi-separated formal algebraic \
space"]
theorem hasQuasiCompactDiagonal_iff_isQuasiSeparated_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (f : X ⟶ (fppfYoneda B S hS).obj Z) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasQuasiCompactDiagonal B S hS f ↔ IsQuasiSeparated B S hS X :=
  hasQuasiCompactDiagonal_iff_isQuasiSeparated B S hS hZ f
    (relativelyRepresentable_pullback_diagonal B S hS f
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX))

/-! ### Stacks 0ARS, clause (5), for quasi-separatedness -/

/-- **Stacks 0ARS, the descent step of clause (5) for the quasi-separatedness axiom of
Stacks 0ARN.** Quasi-separatedness of a morphism of fppf sheaves whose relative diagonal is
relatively representable descends along a locally surjective morphism onto the relative
self-product. Quasi-compactness of morphisms of schemes is fppf local on the target by
**Stacks 02WH**, which is what the descent step consumes. -/
@[stacks 0ARS "the descent step of clause (5) for the quasi-separated axiom of Stacks 0ARN: \
quasi-separatedness descends along a single locally surjective morphism onto the relative \
self-product, which is the atlas clause with the covering of Definition 0AIM replaced by one \
locally surjective morphism, and is not the atlas form itself"]
theorem hasQuasiCompactDiagonal_of_locallySurjective {X Y W : FppfSheaf B S hS} (f : X ⟶ Y)
    (b : W ⟶ pullback f f) (hb : Sheaf.IsLocallySurjective b)
    (hrep : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f))
    (hbase : (MorphismProperty.inverseImage (@AlgebraicGeometry.QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.snd (pullback.diagonal f) b)) :
    HasQuasiCompactDiagonal B S hS f := by
  have _ : MorphismProperty.IsLocalAtTarget (@AlgebraicGeometry.QuasiCompact.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact (hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS f hrep).mpr
    (hasRelativeDiagonal_of_locallySurjective B S hS _ f b hb hrep hbase)

/-- **Stacks 0ARS, clause (1) implies clause (5) for the quasi-separatedness axiom of
Stacks 0ARN, in the covering form.** If `Y` is a formal algebraic space and `f : X ⟶ Y` is
quasi-separated then there is a covering `{Y_j ⟶ Y}` as in Definition 0AIM along which every
base change of `f` is quasi-separated. The covering is the atlas of `Y` furnished by
Definition 0AIM; the base changes inherit the condition by **Stacks 0ARP**. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, necessity for the \
quasi-separated axiom of Stacks 0ARN: a quasi-separated morphism of formal algebraic spaces \
has quasi-separated base change to every member of some covering of the target as in \
Definition 0AIM"]
theorem exists_atlas_hasQuasiCompactDiagonal_pullback_snd {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hf : HasQuasiCompactDiagonal B S hS f) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y),
      (∀ j, IsAffineFormalAlgebraicSpace B S hS (Yj j)) ∧
      (∀ j, ∃ hgj : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g j).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g j).hom hgj) ∧
      Sheaf.IsLocallySurjective (Sigma.desc g) ∧
      ∀ j, HasQuasiCompactDiagonal B S hS (pullback.snd f (g j)) := by
  obtain ⟨-, I, Yj, g, haffine, hetale, hsurj⟩ := hY
  exact ⟨I, Yj, g, haffine, hetale, hsurj, fun j ↦ HasQuasiCompactDiagonal.of_isPullback B S hS
    (IsPullback.of_hasPullback f (g j)) hf⟩

/-- **Stacks 0ARS, clause (5) implies clause (1) for the quasi-separatedness axiom of
Stacks 0ARN, in the covering form of Definition 0AIM.** Let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S` whose relative diagonal is representable by objects of the
site. If there is a family `{Y_j ⟶ Y}` whose induced morphism from the coproduct is a surjection
of sheaves — the covering condition of Definition 0AIM — such that every base change
`Y_j ×_Y X ⟶ Y_j` of `f` is quasi-separated, then `f` is quasi-separated.

The hypothesis `hrep` is carried, and is discharged for a source which is a formal algebraic
space in
`AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_of_atlas_of_isFormalAlgebraicSpace`
below. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, sufficiency for the \
quasi-separated axiom of Stacks 0ARN: a morphism of formal algebraic spaces with relatively \
representable relative diagonal is quasi-separated as soon as its base change to every member \
of a covering of the target as in Definition 0AIM is quasi-separated; the representability \
hypothesis is discharged for a source which is a formal algebraic space in \
`…hasQuasiCompactDiagonal_of_atlas_of_isFormalAlgebraicSpace`"]
theorem hasQuasiCompactDiagonal_of_atlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc g))
    (hrep : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f))
    (hqs : ∀ j, HasQuasiCompactDiagonal B S hS (pullback.snd f (g j))) :
    HasQuasiCompactDiagonal B S hS f := by
  have _ : MorphismProperty.IsLocalAtTarget (@AlgebraicGeometry.QuasiCompact.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  refine (hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS f hrep).mpr
    (hasRelativeDiagonal_of_atlas B S hS _ f I Yj g hsurj hrep (fun j ↦ ?_))
  exact (hasQuasiCompactDiagonal_iff_hasRelativeDiagonal_quasiCompact B S hS
    (pullback.snd f (g j))
    (relativelyRepresentable_pullback_diagonal_pullbackSnd B S hS f hrep (g j))).mp (hqs j)

/-- **Stacks 0ARS, clause (5) implies clause (1) for the quasi-separatedness axiom of
Stacks 0ARN**, in the covering form of Definition 0AIM and in the source's own form: a morphism
`f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose source is a formal algebraic space
is quasi-separated as soon as its base change to every member of some covering of the target as
in Definition 0AIM is. The representability hypothesis of
`AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_of_atlas` is discharged by
**Stacks 0AIP** and **Stacks 0AN2**. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, sufficiency for the \
quasi-separated axiom of Stacks 0ARN, in the source's form with no extra hypothesis: a \
morphism of formal algebraic spaces is quasi-separated as soon as its base change to every \
member of a covering of the target as in Definition 0AIM is quasi-separated"]
theorem hasQuasiCompactDiagonal_of_atlas_of_isFormalAlgebraicSpace {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc g))
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hqs : ∀ j, HasQuasiCompactDiagonal B S hS (pullback.snd f (g j))) :
    HasQuasiCompactDiagonal B S hS f :=
  hasQuasiCompactDiagonal_of_atlas B S hS f I Yj g hsurj
    (relativelyRepresentable_pullback_diagonal B S hS f
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)) hqs

/-! ### Stacks 0ARS in full -/

/-- **Stacks 0ARS for the quasi-separatedness axiom of Stacks 0ARN**: for a morphism
`f : X ⟶ Y` of formal algebraic spaces over `S` the following are equivalent:
1. `f` is quasi-separated;
2. for every scheme `Z` of the site and every `Z ⟶ Y` the base change `Z ×_Y X ⟶ Z` is
  quasi-separated;
3. for every affine scheme `Z` of the site and every `Z ⟶ Y` the base change `Z ×_Y X ⟶ Z` is
  quasi-separated;
4. for every affine scheme `Z` of the site and every `Z ⟶ Y` the formal algebraic space
  `Z ×_Y X` is quasi-separated in the sense of Stacks 0AJ7;
5. there is a covering `{Y_j ⟶ Y}` as in Definition 0AIM — affine formal algebraic spaces,
  étale morphisms representable by algebraic spaces, jointly surjective — such that every base
  change `Y_j ×_Y X ⟶ Y_j` is quasi-separated. -/
theorem hasQuasiCompactDiagonal_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    List.TFAE
      [HasQuasiCompactDiagonal B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj Z ⟶ Y),
          HasQuasiCompactDiagonal B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y),
            HasQuasiCompactDiagonal B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y), IsQuasiSeparated B S hS (pullback f g),
        ∃ (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y),
          (∀ j, IsAffineFormalAlgebraicSpace B S hS (Yj j)) ∧
          (∀ j, ∃ hgj : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g j).hom,
            Space.HasPropertyULift.{u + 1} B S hS
              (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g j).hom hgj) ∧
          Sheaf.IsLocallySurjective (Sigma.desc g) ∧
          ∀ j, HasQuasiCompactDiagonal B S hS (pullback.snd f (g j))] := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hrep := relativelyRepresentable_pullback_diagonal B S hS f
    (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)
  tfae_have 1 ↔ 2 := hasQuasiCompactDiagonal_iff_forall_baseChange B S hS f hrep
  tfae_have 1 ↔ 3 := hasQuasiCompactDiagonal_iff_forall_affine_baseChange B S hS f hrep
  tfae_have 3 ↔ 4 := forall_congr' fun _ ↦ forall_congr' fun hZ ↦ forall_congr' fun g ↦
    hasQuasiCompactDiagonal_iff_isQuasiSeparated B S hS hZ (pullback.snd f g)
      (relativelyRepresentable_pullback_diagonal_pullbackSnd B S hS f hrep g)
  tfae_have 1 → 5 := exists_atlas_hasQuasiCompactDiagonal_pullback_snd B S hS f hY
  tfae_have 5 → 1 := fun ⟨I, Yj, g, _, _, hsurj, h⟩ ↦
    hasQuasiCompactDiagonal_of_atlas B S hS f I Yj g hsurj hrep h
  tfae_finish

/-- **Stacks 0ARS for the separatedness axiom of Stacks 0ARN**: for a morphism `f : X ⟶ Y` of
formal algebraic spaces over `S` the following are equivalent:
1. `f` is separated;
2. for every scheme `Z` of the site and every `Z ⟶ Y` the base change `Z ×_Y X ⟶ Z` is
  separated;
3. for every affine scheme `Z` of the site and every `Z ⟶ Y` the base change `Z ×_Y X ⟶ Z` is
  separated;
4. for every affine scheme `Z` of the site and every `Z ⟶ Y` the formal algebraic space
  `Z ×_Y X` is separated in the sense of Stacks 0AJ7;
5. there is a covering `{Y_j ⟶ Y}` as in Definition 0AIM such that every base change
  `Y_j ×_Y X ⟶ Y_j` is separated. -/
theorem isSeparatedMorphism_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    List.TFAE
      [IsSeparatedMorphism B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj Z ⟶ Y),
          IsSeparatedMorphism B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y),
            IsSeparatedMorphism B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y), IsSeparated B S hS (pullback f g),
        ∃ (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y),
          (∀ j, IsAffineFormalAlgebraicSpace B S hS (Yj j)) ∧
          (∀ j, ∃ hgj : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g j).hom,
            Space.HasPropertyULift.{u + 1} B S hS
              (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g j).hom hgj) ∧
          Sheaf.IsLocallySurjective (Sigma.desc g) ∧
          ∀ j, IsSeparatedMorphism B S hS (pullback.snd f (g j))] := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hrep := relativelyRepresentable_pullback_diagonal B S hS f
    (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)
  tfae_have 1 ↔ 2 := isSeparatedMorphism_iff_forall_baseChange B S hS f
  tfae_have 1 ↔ 3 :=
    isSeparatedMorphism_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace B S hS f hX
  tfae_have 3 ↔ 4 := forall_congr' fun _ ↦ forall_congr' fun hZ ↦ forall_congr' fun g ↦
    (isSeparatedMorphism_iff_isSeparated B S hS hZ (pullback.snd f g)).trans
      (and_iff_right (relativelyRepresentable_pullback_diagonal_pullbackSnd B S hS f hrep g))
  tfae_have 1 → 5 := exists_atlas_isSeparatedMorphism_pullback_snd B S hS f hY
  tfae_have 5 → 1 := fun ⟨I, Yj, g, _, _, hsurj, h⟩ ↦
    isSeparatedMorphism_of_atlas B S hS f I Yj g hsurj h
  tfae_finish

/-- **Stacks 0ARS.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S`. For
each of the two separation axioms `P` of Stacks 0ARN — quasi-separated (the relative diagonal
quasi-compact) and separated (the relative diagonal a closed immersion) — the following are
equivalent: (1) `f` is `P`; (2) every base change `Z ×_Y X ⟶ Z` along a scheme `Z ⟶ Y` is `P`;
(3) every such base change with `Z` affine is `P`; (4) for every affine scheme `Z ⟶ Y` the
formal algebraic space `Z ×_Y X` is `P` in the sense of Stacks 0AJ7; (5) there is a covering
`{Y_j ⟶ Y}` as in Definition 0AIM with every base change `Y_j ×_Y X ⟶ Y_j` being `P`.

The first conjunct is `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_tfae`, the second
`AlgebraicGeometry.FormalSpace.isSeparatedMorphism_tfae`. -/
@[stacks 0ARS "in full: the five conditions are equivalent for each of the two separation \
axioms of Definition 0ARN, quasi-separated and separated, for any morphism of formal \
algebraic spaces"]
theorem separationAxiom_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    List.TFAE
      [HasQuasiCompactDiagonal B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj Z ⟶ Y),
          HasQuasiCompactDiagonal B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y),
            HasQuasiCompactDiagonal B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y), IsQuasiSeparated B S hS (pullback f g),
        ∃ (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y),
          (∀ j, IsAffineFormalAlgebraicSpace B S hS (Yj j)) ∧
          (∀ j, ∃ hgj : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g j).hom,
            Space.HasPropertyULift.{u + 1} B S hS
              (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g j).hom hgj) ∧
          Sheaf.IsLocallySurjective (Sigma.desc g) ∧
          ∀ j, HasQuasiCompactDiagonal B S hS (pullback.snd f (g j))] ∧
    List.TFAE
      [IsSeparatedMorphism B S hS f,
        ∀ (Z : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj Z ⟶ Y),
          IsSeparatedMorphism B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y),
            IsSeparatedMorphism B S hS (pullback.snd f g),
        ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : (fppfYoneda B S hS).obj Z ⟶ Y), IsSeparated B S hS (pullback f g),
        ∃ (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y),
          (∀ j, IsAffineFormalAlgebraicSpace B S hS (Yj j)) ∧
          (∀ j, ∃ hgj : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g j).hom,
            Space.HasPropertyULift.{u + 1} B S hS
              (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g j).hom hgj) ∧
          Sheaf.IsLocallySurjective (Sigma.desc g) ∧
          ∀ j, IsSeparatedMorphism B S hS (pullback.snd f (g j))] :=
  ⟨hasQuasiCompactDiagonal_tfae B S hS f hX hY, isSeparatedMorphism_tfae B S hS f hX hY⟩

end AlgebraicGeometry.FormalSpace

end

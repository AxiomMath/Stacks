module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Refinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.CoveringsParts0DBI
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.Permanence
public import StacksCore.Tactic.StacksAttribute

/-!
# Permanence properties and examples of h coverings

An h covering of a scheme is a family of morphisms which are locally of finite presentation
and which is a ph covering, `AlgebraicGeometry.IsHCovering`.  This file records the
elementary examples — an isomorphism and a proper surjection of finite presentation — the
comparison with ph coverings over a locally Noetherian base, and the stability of h coverings
under composition of families and under base change.

## Main results

* `AlgebraicGeometry.IsPHCovering.reindex` and `AlgebraicGeometry.IsHCovering.reindex`:
  reindexing along an equivalence of index types preserves both conditions.
* `AlgebraicGeometry.isHCovering_of_isIso`: an isomorphism is an h covering.
* `AlgebraicGeometry.surjective_proper_isHCovering`: a proper surjection of finite
  presentation is an h covering by itself.
* `AlgebraicGeometry.isHCovering_iff_isPHCovering`: over a locally Noetherian scheme the h
  coverings are exactly the ph coverings.
* `AlgebraicGeometry.isHCovering_pullback_of_forall_exists_isAffineOpen` and
  `AlgebraicGeometry.isHCovering_pullback_of_isAffine`: h coverings are stable under base
  change along a morphism each of whose affine opens maps into an affine open of the target,
  in particular along any morphism to an affine scheme.
* `AlgebraicGeometry.isHCovering_bind` and `AlgebraicGeometry.isHCovering_pullback`: h
  coverings are stable under composition of families and under base change.

## Implementation notes

The family of all composites of a family over the members of another family is
`CategoryTheory.PreZeroHypercover.bind`.  The singleton family of an isomorphism is allowed
an arbitrary one-element index type, since consumers inside a site meet it with the index
type that site's covering families use.

Composition and base change are deduced from the corresponding statements for ph coverings,
`AlgebraicGeometry.isPHCovering_bind` and `AlgebraicGeometry.isPHCovering_pullback`, which
are Stacks 0DBI parts (2) and (3) in full generality.  Those rest on the general refinement
statement of Stacks 0DBF part (2),
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind`, which this development proves
outright from its own Chow's lemma, Stacks 0202.  The other half of an h covering asks for
nothing beyond the `CategoryTheory.MorphismProperty` instances of local finite presentation,
which is closed under composition and stable under base change.  Both statements are
therefore unconditional.

The route through V coverings, `AlgebraicGeometry.IsVCovering.comp` and
`AlgebraicGeometry.isVCovering_pullback`, is not taken for them. It passes through the
comparison of ph and V coverings for families which are locally of finite presentation, which
is Stacks 0ETR and rests on `AlgebraicGeometry.StandardVCoveringHasPHRefinement` and so on the
Raynaud–Gruson flattening theorem, far further down the import graph than this file. The
comparison is therefore stated here granted that predicate, as
`AlgebraicGeometry.isHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement`. The
predicate is discharged, and the comparison stated outright as
`AlgebraicGeometry.isHCovering_iff_isVCovering`, in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`, which imports this
file and so cannot be imported by it.

The confined base change statements `AlgebraicGeometry.isHCovering_pullback_of_isAffine` and
`AlgebraicGeometry.isHCovering_pullback_of_forall_exists_isAffineOpen` are kept, now as
special cases that need neither Stacks 0DBF part (2) nor Chow's lemma: there each affine open
of the source factors through an affine open of the base, so the standard ph covering living
over the latter can be base changed directly and no composite of two standard ph coverings
has to be collapsed.

## References

* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0ETS](https://stacks.math.columbia.edu/tag/0ETS)
* [Stacks Project, Tag 0ETW](https://stacks.math.columbia.edu/tag/0ETW)
* [Stacks Project, Tag 0ETY](https://stacks.math.columbia.edu/tag/0ETY)
* [Stacks Project, Tag 0H45](https://stacks.math.columbia.edu/tag/0H45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- Reindexing a ph covering along an equivalence of index types gives a ph covering. -/
public theorem IsPHCovering.reindex {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (h : IsPHCovering X f) {ι : Type w} (e : ι ≃ I) :
    IsPHCovering (fun j ↦ X (e j)) (fun j ↦ f (e j)) := by
  refine ⟨fun j ↦ ((isPHCovering_iff X f).1 h).1 (e j), fun U hU ↦ ?_⟩
  obtain ⟨𝒰, h𝒰, ⟨φ⟩⟩ := ((isPHCovering_iff X f).1 h).2 U hU
  exact ⟨𝒰, h𝒰, ⟨φ.comp ((PreZeroHypercover.Hom.toReindex
    ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T) e).pullback₂ U.ι)⟩⟩

/-- Reindexing an h covering along an equivalence of index types gives an h covering. -/
public theorem IsHCovering.reindex {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (h : IsHCovering X f) {ι : Type w} (e : ι ≃ I) :
    IsHCovering (fun j ↦ X (e j)) (fun j ↦ f (e j)) :=
  ⟨fun j ↦ h.1 (e j), h.2.reindex e⟩

/-- **Stacks 0ETY, part (1).** An isomorphism of schemes, regarded as a family indexed by a
type with exactly one element, is an h covering. -/
@[stacks 0ETY "part (1)"]
public theorem isHCovering_of_isIso {T' T : Scheme.{u}} {I : Type v} [Unique I] (f : T' ⟶ T)
    [IsIso f] : IsHCovering (fun _ : I ↦ T') (fun _ ↦ f) :=
  ⟨fun _ ↦ inferInstance, (isPHCovering_of_isIso f).reindex (Equiv.ofUnique I Unit)⟩

/-- **Stacks 0ETW.** A surjective proper morphism of schemes of finite presentation is an h
covering by itself. -/
@[stacks 0ETW]
public theorem surjective_proper_isHCovering {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Surjective f] [IsProper f] (hf : FinitePresentation f) :
    IsHCovering (fun _ : Unit ↦ Y) (fun _ ↦ f) :=
  ⟨fun _ ↦ hf.locallyOfFinitePresentation, surjective_proper_isPHCovering f⟩

/-- **Stacks 0H45.** Over a locally Noetherian scheme a family of morphisms is an h covering
if and only if it is a ph covering, because there local finite presentation and local finite
type agree. -/
@[stacks 0H45]
public theorem isHCovering_iff_isPHCovering {T : Scheme.{u}} [IsLocallyNoetherian T]
    {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    IsHCovering X f ↔ IsPHCovering X f :=
  ⟨And.right, fun h ↦ ⟨fun i ↦ LocallyOfFinitePresentation.iff_locallyOfFiniteType.2
    (((isPHCovering_iff X f).1 h).1 i), h⟩⟩

/-- A family is an h covering once its base change is a ph covering, since local finite
presentation is stable under base change. -/
private theorem isHCovering_pullback_of_isPHCovering {T T' : Scheme.{u}} {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsHCovering X f) (g : T' ⟶ T)
    (h : IsPHCovering (fun i ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g)) :
    IsHCovering (fun i ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g) :=
  ⟨fun i ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (f i) g) (hf.1 i), h⟩

/-- **The confined case of Stacks 0ETY part (3).** Let `{X i ⟶ T}` be an h covering and let
`g : T' ⟶ T` be a morphism with the property that every affine open of `T'` is mapped by `g`
into some affine open of `T`. Then the base change `{X i ×_T T' ⟶ T'}` is an h covering.

Local finite presentation is stable under base change, and the ph-covering condition is
`AlgebraicGeometry.isPHCovering_pullback_of_forall_exists_isAffineOpen`. No Stacks attribute
is attached, since part (3) assumes nothing about `g`. -/
public theorem isHCovering_pullback_of_forall_exists_isAffineOpen {T T' : Scheme.{u}}
    {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsHCovering X f) (g : T' ⟶ T)
    (hg : ∀ U' : T'.Opens, IsAffineOpen U' →
      ∃ U : T.Opens, IsAffineOpen U ∧ Set.range (U'.ι ≫ g).base ⊆ (U : Set T)) :
    IsHCovering (fun i ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g) :=
  isHCovering_pullback_of_isPHCovering hf g
    (isPHCovering_pullback_of_forall_exists_isAffineOpen hf.2 g hg)

/-- **Stacks 0ETY part (3) over an affine base.** The base change of an h covering of an
affine scheme along an arbitrary morphism of schemes is an h covering.

Every affine open of the source maps into the affine open `⊤` of the target, so this is the
case `U = ⊤` of `AlgebraicGeometry.isHCovering_pullback_of_forall_exists_isAffineOpen`. It is
not tagged, since Stacks 0ETY part (3) makes no affineness assumption on the base. -/
public theorem isHCovering_pullback_of_isAffine {T T' : Scheme.{u}} [IsAffine T] {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsHCovering X f) (g : T' ⟶ T) :
    IsHCovering (fun i ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g) :=
  isHCovering_pullback_of_isPHCovering hf g (isPHCovering_pullback_of_isAffine hf.2 g)

/-- Granted `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, an h covering is the same
thing as a family of morphisms locally of finite presentation which is a V covering. This is
the form of Stacks 0ETS in which the source states the definition.

That predicate is a theorem of this development, so the statement holds outright; see
`AlgebraicGeometry.isHCovering_iff_isVCovering` in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`, which is where the
predicate can first be named. -/
public theorem isHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement
    (H : StandardVCoveringHasPHRefinement.{u})
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    IsHCovering X f ↔ (∀ i, LocallyOfFinitePresentation (f i)) ∧ IsVCovering X f :=
  and_congr_right (isPHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement H X f)

/-- **Stacks 0ETY part (2).** Composing an h covering with an h covering of each of its
members gives an h covering.

Local finite presentation is closed under composition, and the ph-covering condition is
`AlgebraicGeometry.isPHCovering_bind`, which is Stacks 0DBI part (2). -/
@[stacks 0ETY "part (2)"]
public theorem isHCovering_bind {T : Scheme.{u}}
    (E : PreZeroHypercover.{v} T) (hE : IsHCovering E.X E.f)
    (F : ∀ i, PreZeroHypercover.{w} (E.X i))
    (hF : ∀ i, IsHCovering (F i).X (F i).f) :
    IsHCovering (E.bind F).X (E.bind F).f := by
  refine ⟨?_, isPHCovering_bind E hE.2 F fun i ↦ (hF i).2⟩
  rintro ⟨i, j⟩
  have := hE.1 i
  have := (hF i).1 j
  exact locallyOfFinitePresentation_comp ((F i).f j) (E.f i)

/-- **Stacks 0ETY part (3).** The base change of an h covering along an arbitrary morphism of
schemes is an h covering.

Local finite presentation is stable under base change, and the ph-covering condition is
`AlgebraicGeometry.isPHCovering_pullback`, which is Stacks 0DBI part (3). -/
@[stacks 0ETY "part (3)"]
public theorem isHCovering_pullback {T T' : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (hf : IsHCovering X f) (g : T' ⟶ T) :
    IsHCovering (fun i ↦ pullback (f i) g) (fun i ↦ pullback.snd (f i) g) :=
  isHCovering_pullback_of_isPHCovering hf g (isPHCovering_pullback hf.2 g)

end AlgebraicGeometry

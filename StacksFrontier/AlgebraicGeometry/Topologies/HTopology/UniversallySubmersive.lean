module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Submersive
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhCoveringRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.VCoveringSubmersive
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfVComparison

/-!
# h coverings and universally submersive morphisms

Over a Noetherian scheme `X` a finite family `{X i ⟶ X}` of finite type morphisms is an h
covering exactly when the morphism `∐ X i ⟶ X` from the disjoint union of its sources is
universally submersive. This is the point of contact between the h topology as it is defined
here — families locally of finite presentation which are ph coverings — and Voevodsky's
original definition by joint universal submersiveness.

## Main definitions

* `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement` is the geometric input the implication
  from universal submersiveness to the h covering condition needs and this file does not prove:
  that such a family is refined by a ph covering.

## Main results

* `AlgebraicGeometry.universallySubmersive_sigmaDesc_of_isHCovering`: the disjoint-union morphism
  of an h covering is universally submersive. This needs no finiteness or Noetherian hypothesis.
* `AlgebraicGeometry.exists_mem_range_of_surjective_sigmaDesc`: a family whose disjoint-union
  morphism is surjective is jointly surjective.
* `AlgebraicGeometry.isHCovering_of_universallySubmersive_of_flat`: the converse implication for a
  family of *flat* morphisms, granted `AlgebraicGeometry.FppfHasFiniteDomination`.
* `AlgebraicGeometry.isHCovering_of_universallySubmersive` and
  `AlgebraicGeometry.universallySubmersive_sigmaDesc_iff_isHCovering`: the converse implication,
  and the equivalence, granted `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement`.

## Implementation notes

The forward implication composes three statements of the library: an h covering is a ph covering by
definition, a ph covering is a V covering
(`AlgebraicGeometry.isVCovering_of_isPHCovering`), and the disjoint-union morphism of a V
covering is universally submersive (`AlgebraicGeometry.isVCovering_universallySubmersive`).
Nothing in that chain uses the base, the index type or the members beyond smallness of the
index type, so it is recorded in that generality.

The converse is where all the content of the source lies, and this file does not prove it.
The Stacks argument chooses a generic flatness stratification of the base (Stacks 0H3Z), takes
scheme-theoretic closures of its strata (Stacks 01R8) to reduce to a reduced base with a dense
open over which the family is flat, flattens the family by an admissible blowup of that base
(Stacks 0815) which may be taken to have scheme-theoretically dense centre (Stacks 080Y), and
then lifts points of the blowup along discrete valuation rings (Stacks 0CM2) to recognize the
flattened family as an fppf covering. The flattening step is no longer an obstruction: the
flatness assertion of Stacks 0815 is proved, as
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup` in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/GenericFibreFreeBlowup0811.lean`. What is not
carried out here is the rest of that argument, which also has to pass from the finite type
morphisms over a Noetherian base that the predicate below quantifies over to the finitely
presented data the flattening theorem consumes. What the whole argument produces is a ph covering
refining the given family, and that is exactly what
`AlgebraicGeometry.UniversallySubmersiveHasPHRefinement` asserts; the step from such a
refinement to the h covering condition is proved here, from Stacks 0ET9 and Stacks 0H45.

The endgame of the Stacks argument *is* proved here, in
`AlgebraicGeometry.isHCovering_of_universallySubmersive_of_flat`: once the members of the family
are flat, universal submersiveness contributes only joint surjectivity, so the family is an fppf
covering and Stacks 0DBT applies. The weak form of Stacks 0CP0 isolated as
`AlgebraicGeometry.FppfHasFiniteDomination` is what that last appeal still costs.

Smallness of the index type relative to the universe of the schemes is carried as an instance
argument next to its finiteness: it follows from finiteness, but Mathlib has no instance to that
effect, and it is needed to form the coproduct `∐ X i` at all.

## References

* [Stacks Project, Tag 040H](https://stacks.math.columbia.edu/tag/040H)
* [Stacks Project, Tag 0ET9](https://stacks.math.columbia.edu/tag/0ET9)
* [Stacks Project, Tag 0ETP](https://stacks.math.columbia.edu/tag/0ETP)
* [Stacks Project, Tag 0ETS](https://stacks.math.columbia.edu/tag/0ETS)
* [Stacks Project, Tag 0ETT](https://stacks.math.columbia.edu/tag/0ETT)
* [Stacks Project, Tag 0H45](https://stacks.math.columbia.edu/tag/0H45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- Every point of a coproduct of schemes lies in the image of one of the canonical morphisms
from its summands. -/
private theorem exists_sigmaι_base_eq {I : Type v} [Small.{u} I] (Y : I → Scheme.{u})
    (p : (∐ Y : Scheme.{u})) : ∃ (i : I) (y : Y i), (Sigma.ι Y i).base y = p :=
  (sigmaOpenCover Y).exists_eq p

/-- A family of morphisms of schemes whose disjoint-union morphism is surjective is jointly
surjective: a preimage of a point of the target lies in the image of one of the canonical
morphisms from the sources into the coproduct. -/
theorem exists_mem_range_of_surjective_sigmaDesc {X : Scheme.{u}} {I : Type v} [Small.{u} I]
    {Y : I → Scheme.{u}} {f : ∀ i, Y i ⟶ X} (h : Function.Surjective (Sigma.desc f).base)
    (x : X) : ∃ i, x ∈ Set.range (f i).base := by
  obtain ⟨p, hp⟩ := h x
  obtain ⟨i, y, hy⟩ := exists_sigmaι_base_eq Y p
  exact ⟨i, y, by rw [← hp, ← hy, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩

/-- **Stacks 0ETT, (2) implies (1).** The morphism from the disjoint union of the sources of an
h covering to its target is universally submersive.

An h covering is a ph covering, hence a V covering, and the disjoint-union morphism of a V
covering is universally submersive. No Noetherian or finiteness hypothesis is involved. -/
@[stacks 0ETT "(2) implies (1)"]
theorem universallySubmersive_sigmaDesc_of_isHCovering {X : Scheme.{u}} {I : Type v}
    [Small.{u} I] {Y : I → Scheme.{u}} {f : ∀ i, Y i ⟶ X} (hf : IsHCovering Y f) :
    UniversallySubmersive (Sigma.desc f) :=
  isVCovering_universallySubmersive Y f (isVCovering_of_isPHCovering Y f hf.2)

/-- **The flat case of Stacks 0ETT, (1) implies (2)**, granted
`AlgebraicGeometry.FppfHasFiniteDomination`: a finite family of flat morphisms of finite type to
a Noetherian scheme whose disjoint-union morphism is universally submersive is an h covering.

This is the last step of the Stacks argument, reached there after a flattening blowup. Universal
submersiveness enters only through surjectivity of the disjoint-union morphism, so the family is
jointly surjective, flat and locally of finite presentation, that is an fppf covering, and
Stacks 0DBT identifies it as a ph covering. -/
theorem isHCovering_of_universallySubmersive_of_flat (H : FppfHasFiniteDomination.{u, v})
    {X : Scheme.{u}} [IsNoetherian X] {I : Type v} [Finite I] [Small.{u} I]
    {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (f i)]
    [∀ i, QuasiCompact (f i)] [∀ i, Flat (f i)]
    (hsub : UniversallySubmersive (Sigma.desc f)) : IsHCovering Y f := by
  have hfp : ∀ i, LocallyOfFinitePresentation (f i) := fun i ↦
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  refine ⟨hfp, isPHCovering_of_mem_fppfPrecoverage H Y f ?_⟩
  refine (Scheme.ofArrows_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr ⟨?_, fun i ↦ ⟨inferInstance, hfp i⟩⟩
  exact exists_mem_range_of_surjective_sigmaDesc
    ((submersive_iff _).1 (submersive_of_universallySubmersive hsub)).surjective

/-- The geometric input of Stacks 0ETT which this development does not have: a finite family of
morphisms of finite type to a Noetherian scheme whose disjoint-union morphism is universally
submersive is refined by a ph covering.

The Stacks proof constructs such a refinement from a generic flatness stratification of the base
and a flattening blowup; see the implementation notes of this file for what of that this
development carries out. The predicate is stated in the shape of the second clause of
`AlgebraicGeometry.isPHCovering_tfae`, so that it combines with that equivalence directly, and is
a `Prop` so that it can be carried as an explicit hypothesis, in the style of
`AlgebraicGeometry.FinitePresentationHasFlatteningBlowup` and
`AlgebraicGeometry.StandardVCoveringHasPHRefinement`, both of which are now theorems. -/
def UniversallySubmersiveHasPHRefinement : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X] (I : Type v) [Finite I] [Small.{u} I]
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X), (∀ i, LocallyOfFiniteType (f i)) →
    (∀ i, QuasiCompact (f i)) → UniversallySubmersive (Sigma.desc f) →
    ∃ (K : Type v) (Z : K → Scheme.{u}) (g : ∀ k, Z k ⟶ X), IsPHCovering Z g ∧
      Nonempty (({ I₀ := K, X := Z, f := g } : PreZeroHypercover.{v} X).Hom
        ({ I₀ := I, X := Y, f := f } : PreZeroHypercover.{v} X))

/-- **Stacks 0ETT, (1) implies (2)**, granted
`AlgebraicGeometry.UniversallySubmersiveHasPHRefinement`: a finite family of morphisms of finite
type to a Noetherian scheme whose disjoint-union morphism is universally submersive is an h
covering.

The hypothesis supplies a ph covering refining the family; a family of morphisms locally of
finite type refined by a ph covering is a ph covering (Stacks 0ET9), and over a locally
Noetherian base the ph coverings are exactly the h coverings (Stacks 0H45). -/
@[stacks 0ETT "(1) implies (2)"]
theorem isHCovering_of_universallySubmersive (H : UniversallySubmersiveHasPHRefinement.{u, v})
    {X : Scheme.{u}} [IsNoetherian X] {I : Type v} [Finite I] [Small.{u} I]
    {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (f i)]
    [∀ i, QuasiCompact (f i)] (hsub : UniversallySubmersive (Sigma.desc f)) :
    IsHCovering Y f :=
  (isHCovering_iff_isPHCovering Y f).2
    (((isPHCovering_tfae Y f fun i ↦ inferInstance).out 2 1).1
      (H X I Y f (fun i ↦ inferInstance) (fun i ↦ inferInstance) hsub))

/-- **Stacks 0ETT**, granted `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement`: for a
finite family `{X i ⟶ X}` of morphisms of finite type to a Noetherian scheme `X`, the morphism
`∐ X i ⟶ X` is universally submersive if and only if the family is an h covering.

The implication from the h covering condition is unconditional; the hypothesis is used only for
the converse. -/
@[stacks 0ETT]
theorem universallySubmersive_sigmaDesc_iff_isHCovering
    (H : UniversallySubmersiveHasPHRefinement.{u, v}) {X : Scheme.{u}} [IsNoetherian X]
    {I : Type v} [Finite I] [Small.{u} I] {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFiniteType (f i)] [∀ i, QuasiCompact (f i)] :
    UniversallySubmersive (Sigma.desc f) ↔ IsHCovering Y f :=
  ⟨isHCovering_of_universallySubmersive H f, universallySubmersive_sigmaDesc_of_isHCovering⟩

end AlgebraicGeometry

end

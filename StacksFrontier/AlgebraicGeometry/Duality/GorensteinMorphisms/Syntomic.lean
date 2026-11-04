module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Fibres
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties

/-!
# A syntomic morphism is Gorenstein

A syntomic morphism of schemes is a Gorenstein morphism, and equivalently so is a flat local
complete intersection morphism.

A syntomic morphism is flat, and each of its fibres is a local complete intersection over the
residue field of its base point, syntomicity being stable under base change. The spectrum of a
field is a regular, hence Gorenstein, scheme, so a local complete intersection morphism over it
has Gorenstein source: every fibre is a Gorenstein scheme. A flat morphism with Gorenstein
fibres is a Gorenstein morphism.

## Main results

* `AlgebraicGeometry.isGorenstein_Spec_residueField`: the spectrum of a residue field of a
  scheme is a Gorenstein scheme.
* `AlgebraicGeometry.isLocallyNoetherian_fiber_of_syntomic`: the fibres of a syntomic morphism
  are locally Noetherian.
* `AlgebraicGeometry.isGorenstein_fiber_of_syntomic`: the fibres of a syntomic morphism are
  Gorenstein schemes.
* `AlgebraicGeometry.isGorenstein_of_syntomic` — **Stacks 0C15**, first formulation.
* `AlgebraicGeometry.isGorenstein_of_flat_of_isLocalCompleteIntersectionMorphism` —
  **Stacks 0C15**, second formulation.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.IsGorenstein` takes a proof that every fibre is locally
Noetherian as an argument, since the Gorenstein property of the local ring of a fibre needs a
Noetherian structure on that local ring. For a syntomic morphism that proof is not a hypothesis:
a syntomic morphism is locally of finite presentation by Stacks 01UL, so each fibre is locally
of finite type over a field and therefore locally Noetherian. Both statements below accordingly
supply it from `AlgebraicGeometry.isLocallyNoetherian_fiber_of_syntomic` and carry no hypothesis
beyond the one in the source; `IsLocallyNoetherian` being a proposition, this is the same
statement as for any other such proof.

Gorensteinness of the fibres is Stacks 0BVA applied to the structure morphism
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` of the fibre, which is a base change of
the morphism and hence syntomic, so a local complete intersection morphism by Stacks 069K. Its
target `Spec κ(s)` is covered by a single affine open whose sections are the field `κ(s)`, so it
is regular and therefore Gorenstein by Stacks 0DWG. Passing from Gorenstein fibres to a
Gorenstein morphism is Stacks 0C05.

The fibrewise criterion for syntomicity, Stacks 01UF, enters only in the direction used here,
that a fibre of a syntomic morphism is a local complete intersection over the residue field;
that direction is the base-change stability of syntomic morphisms rather than the implication
formalized as `AlgebraicGeometry.syntomic_of_lci_fibers`.

## References

* [Stacks Project, Tag 0C15](https://stacks.math.columbia.edu/tag/0C15)
* [Stacks Project, Tag 01UF](https://stacks.math.columbia.edu/tag/01UF)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 0BVA](https://stacks.math.columbia.edu/tag/0BVA)
* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
* [Stacks Project, Tag 0DWG](https://stacks.math.columbia.edu/tag/0DWG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The spectrum of a residue field of a scheme is a Gorenstein scheme: it is covered by the
single affine open `⊤`, whose ring of sections is a field and hence a regular ring, so the
scheme is regular and Stacks 0DWG applies. -/
public theorem isGorenstein_Spec_residueField (S : Scheme.{u}) (s : S) :
    IsGorenstein (Spec (S.residueField s)) := by
  refine isGorenstein_of_isRegular _ fun _ => ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
  exact IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (S.residueField s)).symm.commRingCatIsoToRingEquiv

/-- Every fibre of a syntomic morphism is locally Noetherian: a syntomic morphism is locally of
finite presentation, so the fibre is locally of finite type over the residue field of its base
point. -/
public theorem isLocallyNoetherian_fiber_of_syntomic {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Syntomic f) (s : S) : IsLocallyNoetherian (f.fiber s) := by
  let : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)

/-- Every fibre of a syntomic morphism is a Gorenstein scheme: the fibre is syntomic over the
residue field of its base point, hence a local complete intersection morphism over a Gorenstein
scheme. -/
public theorem isGorenstein_fiber_of_syntomic {X S : Scheme.{u}} {f : X ⟶ S} (hf : Syntomic f)
    (s : S) : IsGorenstein (f.fiber s) := by
  have hfs : Syntomic (f.fiberToSpecResidueField s) :=
    syntomic_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) hf
  exact isGorenstein_of_isLocalCompleteIntersectionMorphism (f.fiberToSpecResidueField s)
    ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism _).mp hfs).2
    (isGorenstein_Spec_residueField S s)

/-- **Stacks 0C15.** A syntomic morphism of schemes is a Gorenstein morphism. -/
@[stacks 0C15 "a syntomic morphism is Gorenstein"]
public theorem isGorenstein_of_syntomic {X S : Scheme.{u}} (f : X ⟶ S) (hf : Syntomic f) :
    f.IsGorenstein (isLocallyNoetherian_fiber_of_syntomic hf) := by
  let : Flat f := flat hf
  exact Scheme.Hom.isGorensteinAt_of_flat_of_isGorenstein_fiber f
    (isLocallyNoetherian_fiber_of_syntomic hf) (isGorenstein_fiber_of_syntomic hf)

/-- **Stacks 0C15.** A flat local complete intersection morphism of schemes is a Gorenstein
morphism; this is the second formulation of the lemma, equivalent to the first by Stacks
069K. -/
@[stacks 0C15 "a flat local complete intersection morphism is Gorenstein"]
public theorem isGorenstein_of_flat_of_isLocalCompleteIntersectionMorphism {X S : Scheme.{u}}
    (f : X ⟶ S) (hflat : Flat f) (hlci : IsLocalCompleteIntersectionMorphism f) :
    f.IsGorenstein (isLocallyNoetherian_fiber_of_syntomic
      (syntomic_of_flat_of_isLocalCompleteIntersectionMorphism hflat hlci)) :=
  isGorenstein_of_syntomic f (syntomic_of_flat_of_isLocalCompleteIntersectionMorphism hflat hlci)

end AlgebraicGeometry

end

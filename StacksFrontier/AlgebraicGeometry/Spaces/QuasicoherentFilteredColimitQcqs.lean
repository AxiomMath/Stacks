module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationColimitAffineOverNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation

/-!
# Quasi-coherent modules on a quasi-compact quasi-separated algebraic space

**Stacks 07V9** asserts that on a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S` every quasi-coherent `𝒪_X`-module is a filtered colimit of `𝒪_X`-modules of finite
presentation.

The source's proof is short.  View `X` over `Spec ℤ`, write it as `X = lim X_i` with absolute
Noetherian approximation (Stacks 07SU); the stages are of finite type over `Spec ℤ`, hence
Noetherian (Stacks 04ZL); each projection `X ⟶ X_i` is affine (Stacks 07SF, part (1)); and
Stacks 07UW, quasi-coherent modules on a space affine over a Noetherian space, finishes.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_noetherianApproximation_π` — the projection from a
  Noetherian approximation to any one of its stages is affine, which is Stacks 07SF, part (1),
  read on the approximation's own limiting cone.
* **Stacks 07V9** itself is proved, without carried inputs, as
  `AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentation` (and its on-site form
  `AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentationOnSite`) in
  `StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationGeneration/Main.lean`.

## Implementation notes

### The carried inputs, and why each is general

Seven hypotheses are carried.  Every one of them is stated about *arbitrary* algebraic spaces,
morphisms and modules of its own; none mentions `X`, `hX` or `F`, and none has this theorem's
conclusion as its consequent.  This is the discipline of `hscheme` of
`AlgebraicGeometry.Space.exists_isAffine_etale_charts_projective_sections` and of `hEKP` of
`Stacks.Algebraization.completionFullyFaithful_of_isAdicComplete_of_annihilated`.

* `h07SU` is **Stacks 07SU**, absolute Noetherian approximation for algebraic spaces, in the
  interface `AlgebraicGeometry.Space.NoetherianApproximation` of
  `StacksFrontier/AlgebraicGeometry/Spaces/NoetherianApproximation.lean`: a directed set, an
  inverse system of algebraic spaces over it with affine transition morphisms whose stages are
  quasi-separated and of finite type over `Spec ℤ`, and a limiting cone with the given space as
  vertex.  That tag is not proved in this development.
* `h04ZL` is **Stacks 04ZL** in the form in which the source quotes it here, across the
  base-crossing the source performs with Stacks 03I5 and Stacks 03BS: an algebraic space which
  is quasi-separated and of finite type over `Spec ℤ` is Noetherian.  Stacks 04ZL itself is
  proved, as `AlgebraicGeometry.Space.isNoetherian_of_isFinitePresentation`, but it concludes
  Noetherianity of the *source of a morphism of finite presentation with Noetherian target*, and
  the plumbing that turns "of finite type over `Spec ℤ`" — which is a property of
  `AlgebraicGeometry.Space.viewOverIntegers`, a presheaf over a different base — into such a
  morphism over `S` with `Spec ℤ` as target is absent from this library, as is the Noetherianity of
  `Spec ℤ` as an algebraic space.  So the composite is carried, quantified over its own space.
* `hNoeth`, `hpush`, `hpull`, `hepi` and `hqcqs` are the five general cited inputs of
  Stacks 07UW, `AlgebraicGeometry.Space.isFilteredColimit_isFinitePresentation_of_isAffineHom`,
  re-carried verbatim so that this theorem applies that one; see its module documentation for
  what each stands in for (Stacks 07UV with 07UB, 08AI, 03LU with 05VR, 03LX, and the
  quasi-compactness and quasi-separatedness of a space affine over a Noetherian one).

### The cardinality conditions, and why they strengthen `h07SU`

Stacks 07SF, part (1) is proved as `AlgebraicGeometry.Space.isAffineHom_limitπ`, and it carries
two side conditions which the bare statement of Stacks 07SU does not supply: the index category
of the system must have fewer objects, and fewer morphisms in each Hom-set, than the cofinality
of the site's size cutoff `B.cutoff`.  They are what makes the limit exist in the site and be
recognizable there, and they are the same conditions Stacks 07SF and Stacks 0828
carry throughout this development.  `h07SU` therefore asks for an approximation *whose index set
satisfies them*, which is strictly stronger than the cited Stacks 07SU; this is disclosed in the
tag's attribute description.  The conditions are stated on the directed set `A.I` itself; the
index category of the inverse system is `(A.I)ᵒᵖ`, on which they are the same two cardinals.

### The universe of the index category

The conclusion's index category is the one the proof of Stacks 07UW constructs, a category of
triples whose objects live in `Type (u + 1)` with Hom-types in `Type u`.  No smallness of it is
claimed, and the tag claims none.  In particular this is not the `Type u`-with-`SmallCategory`
spelling of the hypothesis `h07V9` of
`AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone`, which asks for more
than the tag asserts.

## References

* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07UW](https://stacks.math.columbia.edu/tag/07UW)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 07SF, part (1)** read on a Noetherian approximation: if the directed set indexing
an approximation `A` of `X` is small enough for the site — fewer objects, and fewer morphisms in
each Hom-set, than the cofinality of the size cutoff `B.cutoff` — then every projection
`A.π.app j : X ⟶ A.diagram.obj j` is affine.

`AlgebraicGeometry.Space.isAffineHom_limitπ` gives this for the projections of the canonical
limit cone of `A.diagram`; the approximation's own cone is carried onto that one by the
canonical isomorphism of limit cone points, and affineness is stable under composition with an
isomorphism. -/
theorem isAffineHom_noetherianApproximation_π
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : NoetherianApproximation B S hS hZ X)
    (hsize : letI := A.preorder; #A.I < B.cutoff.ord.cof)
    (hhom : letI := A.preorder; ∀ i j : A.I, #(i ⟶ j) < B.cutoff.ord.cof)
    (j : letI := A.preorder; (A.I)ᵒᵖ) :
    letI := A.preorder
    IsAffineHom B S hS (A.π.app j) := by
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  let : IsCofiltered (A.I)ᵒᵖ := A.isCofiltered_op
  have hsizeop : #((A.I)ᵒᵖ) < B.cutoff.ord.cof := by
    rwa [← Cardinal.mk_congr (Opposite.equivToOpposite (α := A.I))]
  have hhomop : ∀ i i' : (A.I)ᵒᵖ, #(i ⟶ i') < B.cutoff.ord.cof := by
    intro i i'
    have e : (i ⟶ i') ≃ (i'.unop ⟶ i.unop) :=
      (Opposite.equivToOpposite (α := (i'.unop ⟶ i.unop))).symm
    rw [Cardinal.mk_congr e]
    exact hhom _ _
  have hlim : IsAffineHom B S hS (limit.π A.diagram j) :=
    isAffineHom_limitπ B S hS A.diagram hsizeop hhomop
      (fun g => A.isAffineHom_map g) j
  have heq : A.π.app j =
      (A.isLimit.conePointUniqueUpToIso (limit.isLimit A.diagram)).hom ≫
        limit.π A.diagram j :=
    (IsLimit.conePointUniqueUpToIso_hom_comp A.isLimit (limit.isLimit A.diagram) j).symm
  rw [heq]
  exact isAffineHom_iso_comp _ hlim

end AlgebraicGeometry.Space

end

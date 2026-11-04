module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.CompatibleOpens

/-!
# The stages of a quasi-compact open realized as an inverse limit

Let `D` be a cofiltered diagram of schemes with affine transition morphisms, let `c` be a cone
over it, and let `V j ≤ D.obj j` be a transition-compatible family of quasi-compact opens cutting
the open `U` out of the vertex, with the restricted cone limiting.  This file transports the
three facts Mathlib proves about affine-transition limits — the transition morphisms of the
subdiagram are affine, the sections of `U` are the colimit of the sections of the `V j`, and some
stage is quasi-affine as soon as `U` is — from the ambient diagram to the subdiagram of opens.

These are the geometric inputs of step (ii) of the one-affine-open step of Tag 07RN.  There `U`
is the overlap of the affine open being added with the part of the scheme already approximated,
and the `V j` are its models at the finite stages; the colimit of sections is the ring `R` that
`Stacks.FibreProduct.isColimitCocone` takes as its base, and quasi-affineness of a
stage is what makes the open immersion of that stage into the spectrum of its sections exist.

## Main results

* `AlgebraicGeometry.isAffineHom_compatibleOpensDiagram_map`: the transition morphisms of
  `AlgebraicGeometry.compatibleOpensDiagram` are affine.  The square cut out by an open immersion
  is cartesian, by `AlgebraicGeometry.IsOpenImmersion.isPullback`, and affine morphisms are
  stable under base change.  This is the instance which makes *every* result of Mathlib's
  `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` available for the subdiagram; without
  it none of them applies, since all of them assume affine transitions.

* `AlgebraicGeometry.compactSpace_compatibleOpensDiagram_obj` and
  `AlgebraicGeometry.quasiSeparatedSpace_compatibleOpensDiagram_obj` are the other two standing
  hypotheses of that file, for the subdiagram.  They are lemmas and not instances, because
  quasi-compactness of the opens is a hypothesis rather than something to be synthesized; a
  consumer introduces them locally.

* `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone_compatibleOpens` is Tag 01Z0 for the
  subdiagram: the sections of `U` are the filtered colimit of the sections of the `V j`.

* `AlgebraicGeometry.Scheme.exists_forall_isQuasiAffine_compatibleOpens` is Tag 01Z5 for the
  subdiagram, in the form the one-affine-open induction needs: *some* stage is quasi-affine, and
  then so is every stage above it, since the transition morphisms are affine and
  `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom` propagates quasi-affineness backwards
  along an affine morphism.

## Implementation notes

The index universes are tied to the scheme universe, as they must be: Mathlib's file on
affine-transition limits declares three index universes and uses only one, and freeing the index
universe of the results used here breaks the synthesis of the colimits of `CommRingCat` that
`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone` rests on.  See the restriction recorded for
the restated Tag 06AC, in the namespace
`Stacks.AlgebraicGeometry.LimitFiniteLocallyFree`; two results used here are restated for
exactly this.

Transparency gotchas:

* `AlgebraicGeometry.compatibleOpensDiagram` is reducible, and the affineness instance below
  depends on that: the cartesian square is recognized only because the transition morphism
  unfolds to a `AlgebraicGeometry.Scheme.Hom.resLE` application.

* The cartesian square has to be handed to `CategoryTheory.MorphismProperty.of_isPullback` in
  *flipped* form.  The unflipped square has the restriction as its first leg and the inclusion
  of the open as its second, and base change produces the property of the second leg; flipping
  is what makes the conclusion about the restriction instead of about the inclusion.

* In `AlgebraicGeometry.Scheme.exists_forall_isQuasiAffine_compatibleOpens` the propagation to
  later stages is stated with an explicit morphism `j ⟶ j₀` rather than an inequality of indices,
  since the diagram is indexed by a bare category here.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01Z5](https://stacks.math.columbia.edu/tag/01Z5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {J : Type u} [Category.{u} J] {D : J ⥤ Scheme.{u}} {c : Cone D}
  (V : ∀ j, (D.obj j).Opens) (hV : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V k = V j)

/-- **The transition morphisms of a compatible family of opens are affine.**  The square cut out
by the open immersion `(V k).ι` is cartesian and affine morphisms are stable under base change.
This instance is what makes Mathlib's results on affine-transition limits applicable to the
subdiagram cut out by a compatible family of opens. -/
instance isAffineHom_compatibleOpensDiagram_map
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : J} (f : j ⟶ k) :
    IsAffineHom ((compatibleOpensDiagram D V hV).map f) :=
  MorphismProperty.of_isPullback
    (IsOpenImmersion.isPullback _ _ _ _
      (Scheme.Hom.resLE_comp_ι (D.map f) (hV f).ge).symm (by simpa using hV f)).flip
    inferInstance

/-- The stages of a compatible family of quasi-compact opens are quasi-compact. -/
lemma compactSpace_compatibleOpensDiagram_obj
    (hVc : ∀ j, IsCompact (V j : Set (D.obj j))) (j : J) :
    CompactSpace ((compatibleOpensDiagram D V hV).obj j) :=
  isCompact_iff_compactSpace.mp (hVc j)

/-- The stages of a compatible family of opens of quasi-separated schemes are
quasi-separated. -/
lemma quasiSeparatedSpace_compatibleOpensDiagram_obj
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j)) (j : J) :
    QuasiSeparatedSpace ((compatibleOpensDiagram D V hV).obj j) :=
  have := hqs j
  quasiSeparatedSpace_of_quasiSeparated (V j).ι

variable (U : c.pt.Opens) (hU : ∀ j, c.π.app j ⁻¹ᵁ V j = U)

/-- **The sections of a quasi-compact open realized as an inverse limit are the colimit of the
sections of its models.**  This is Mathlib's `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`,
Tag 01Z0, applied to the subdiagram cut out by a compatible family of quasi-compact opens. -/
lemma nonempty_isColimit_Γ_mapCocone_compatibleOpens [IsCofiltered J]
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    (hc : IsLimit (compatibleOpensCone D c V hV U hU))
    (hVc : ∀ j, IsCompact (V j : Set (D.obj j)))
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j)) :
    Nonempty (IsColimit (Scheme.Γ.mapCocone (compatibleOpensCone D c V hV U hU).op)) :=
  have := compactSpace_compatibleOpensDiagram_obj V hV hVc
  have := quasiSeparatedSpace_compatibleOpensDiagram_obj V hV hqs
  nonempty_isColimit_Γ_mapCocone _ _ hc

/-- **Every sufficiently late stage of a quasi-affine inverse limit is quasi-affine.**  Mathlib's
`AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit`, Tag 01Z5, gives one quasi-affine
stage of the subdiagram cut out by a compatible family of quasi-compact opens; the transition
morphisms of that subdiagram are affine, so quasi-affineness propagates to every stage above
it. -/
lemma Scheme.exists_forall_isQuasiAffine_compatibleOpens [IsCofiltered J]
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    (hc : IsLimit (compatibleOpensCone D c V hV U hU))
    (hVc : ∀ j, IsCompact (V j : Set (D.obj j)))
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j))
    [Scheme.IsQuasiAffine (U : Scheme.{u})] :
    ∃ j₀ : J, ∀ (j : J) (_ : j ⟶ j₀),
      Scheme.IsQuasiAffine ((compatibleOpensDiagram D V hV).obj j) := by
  have := compactSpace_compatibleOpensDiagram_obj V hV hVc
  have := quasiSeparatedSpace_compatibleOpensDiagram_obj V hV hqs
  obtain ⟨j₀, hj₀⟩ := Scheme.exists_isQuasiAffine_of_isLimit _ _ hc
  exact ⟨j₀, fun j f ↦ Scheme.IsQuasiAffine.of_isAffineHom ((compatibleOpensDiagram D V hV).map f)⟩

end AlgebraicGeometry

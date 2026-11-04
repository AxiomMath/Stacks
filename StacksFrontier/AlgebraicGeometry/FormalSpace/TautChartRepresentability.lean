module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFormalSpectrumRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability

/-!
# Taut chart maps and representability by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. This file compares tautness of the chart
maps of a morphism of formal algebraic spaces over `S` with representability by algebraic
spaces: on charts through **Stacks 0AN5**, and from a morphism to its charts through
**Stacks 0AN4** and **Stacks 0AQ0**. These are the comparisons the proof of **Stacks 0ANK**
makes between its conditions (1) to (3) and its condition (4).

## Main results

* `hasTautOnAffineChartMap_of_isRepresentableByAlgebraicSpacesULift`:
  **Stacks 0AN5**, the implication from its condition (1) to its condition (3), with no
  indexing hypothesis on either space.
* `isRepresentableByAlgebraicSpacesULift_iff_hasTautOnAffineChartMap`:
  **Stacks 0AN5**, the equivalence of its conditions (1) and (3), read on countably indexed
  affine formal algebraic spaces.
* `isTautOnEveryAffineEtaleDiagram_of_isRepresentableByAlgebraicSpaces`:
  the implication from condition (4) to condition (1) of **Stacks 0ANK**, asking only that the
  target be a formal algebraic space.

## Implementation notes

The equivalence of conditions (1) and (3) of Stacks 0AN5 is read on countably indexed affine
formal algebraic spaces: a countably indexed affine formal algebraic space is a formal spectrum
(Stacks 0AIK) and a map of formal spectra comes from a continuous homomorphism (Stacks 0AN0), so
the two registered implications of Stacks 0AN5 transport along a presentation. Restricting to
countably indexed charts is what keeps the reading faithful, since an affine formal algebraic
space which is not a formal spectrum has no presentation at all and the condition on its chart
maps is then vacuous. Only the implication from condition (3) to condition (1) has to produce a
presentation, so the other one is stated with no indexing hypothesis at all. The set-theoretic
hypotheses of the two implications come free at that class of rings: a countable fundamental
system of neighbourhoods of `0` bounds the coproduct of all the quotient spectra, which is
`AlgebraicGeometry.FormalSpace.QuotientSystem.hasLargeSite_of_isCountablyGenerated`.

Stacks 0AQ0, the hypothesis `h0AQ0` of `isRepresentableOnEverySquare_of_isRepresentable`, is
discharged by `isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace`.

## References

* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANK](https://stacks.math.columbia.edu/tag/0ANK)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Representability by algebraic spaces transports along isomorphisms of fppf sheaves. -/
private theorem isRepresentableByAlgebraicSpacesULift_of_iso_sheaf
    {U V U' V' : FppfSheaf B S hS} {t : U ⟶ V} {t' : U' ⟶ V'} (eU : U ≅ U') (eV : V ≅ V')
    (hc : t ≫ eV.hom = eU.hom ≫ t')
    (ht : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t'.hom :=
  Space.isRepresentableByAlgebraicSpacesULift_of_iso B S hS
    ((sheafToPresheaf _ _).mapIso eU) ((sheafToPresheaf _ _).mapIso eV)
    (congrArg (fun z : U ⟶ V' ↦ z.hom) hc) ht

/-- **Stacks 0AN5**, the implication from its condition (1) to its condition (3), with no
indexing hypothesis on either space: if `t : U ⟶ V` is representable by algebraic spaces, then
every continuous homomorphism of countably indexed weakly admissible topological rings
presenting it is taut.

Nothing has to be known about `U` and `V` for this direction, because
`AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` quantifies over the presentations:
a presentation of `t` by rings of the class is handed to the implication, rather than produced
from a hypothesis on the spaces, and it puts `t` in the image of `formalSpectrumMap`, where
Stacks 0AN5 applies. Membership in the class supplies the two set-theoretic hypotheses of that
implication through
`AlgebraicGeometry.FormalSpace.QuotientSystem.hasLargeSite_of_isCountablyGenerated`. -/
theorem hasTautOnAffineChartMap_of_isRepresentableByAlgebraicSpacesULift
    {U V : FppfSheaf B S hS} (t : U ⟶ V)
    (ht : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TautChartProperty t := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  refine isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap B S hS hA hCR.1 _ _
    (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS D hA hCA.2)
    (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS E hCR.1 hCR.2) g ?_
  refine isRepresentableByAlgebraicSpacesULift_of_iso_sheaf B S hS eU eV ?_ ht
  rw [hg]; simp

/-- **Stacks 0AN5**, the implication from its condition (3) to its condition (1) on countably
indexed affine formal algebraic spaces: if every continuous homomorphism of countably indexed
weakly admissible topological rings presenting `t : U ⟶ V` is taut, then `t` is representable
by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpacesULift_of_hasTautOnAffineChartMap
    {U V : FppfSheaf B S hS} (t : U ⟶ V) (hU : IsCountablyIndexed B S hS U)
    (hV : IsCountablyIndexed B S hS V)
    (hP : HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TautChartProperty t) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom := by
  obtain ⟨R, hCR, hTR, hRR, hLR, E, hR, hRc, ⟨eU⟩⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hU
  obtain ⟨A, hCA, hTA, hRA, hLA, D, hA, hAc, ⟨eV⟩⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hV
  obtain ⟨g, hg, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hA hR (eU.inv ≫ t ≫ eV.hom)
  have htaut : RingHom.IsTaut g.toRingHom :=
    hP A R ⟨hA, hAc⟩ ⟨hR, hRc⟩ hA D E eU eV g (by rw [hg]; simp)
  refine isRepresentableByAlgebraicSpacesULift_of_iso_sheaf B S hS eU.symm eV.symm ?_
    (isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hA hR _ _
      (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS E hR hRc) g htaut)
  rw [hg]; simp

/-- **Stacks 0AN5**, the equivalence of its conditions (1) and (3) read on countably indexed
affine formal algebraic spaces: a morphism `t : U ⟶ V` of countably indexed formal algebraic
spaces over `S` is representable by algebraic spaces exactly when every continuous
homomorphism of countably indexed weakly admissible topological rings presenting it is taut.

Both spaces are formal spectra of rings of the class by Stacks 0AIK, and a morphism of formal
spectra is the formal spectrum of a unique continuous homomorphism by Stacks 0AN0, so each
condition transports along a presentation to the other. The set-theoretic hypotheses of the
two implications of Stacks 0AN5 are discharged by
`QuotientSystem.hasLargeSite_of_isCountablyGenerated`: a countable fundamental system of
neighbourhoods of `0` bounds the size of the coproduct of all the quotient spectra, and that is
exactly what membership in the class asserts of the presenting rings. -/
theorem isRepresentableByAlgebraicSpacesULift_iff_hasTautOnAffineChartMap
    {U V : FppfSheaf B S hS} (t : U ⟶ V) (hU : IsCountablyIndexed B S hS U)
    (hV : IsCountablyIndexed B S hS V) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
        TautChartProperty t :=
  ⟨hasTautOnAffineChartMap_of_isRepresentableByAlgebraicSpacesULift B S hS t,
    isRepresentableByAlgebraicSpacesULift_of_hasTautOnAffineChartMap B S hS t hU hV⟩

/-- **Stacks 0ANK, condition (4) implies condition (1)**, with no indexing hypothesis on either
space: a morphism `f : X ⟶ Y` of formal algebraic spaces over `S` which is representable by
algebraic spaces has every one of its affine étale chart squares given by a taut continuous
homomorphism of countably indexed weakly admissible topological rings.

The chart map `t : U ⟶ V` of such a square is representable by algebraic spaces by the
implication (1) ⟹ (3) of Stacks 0AN4, whose input Stacks 0AQ0 is
`isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace`, and tautness of the
homomorphisms presenting it is then the implication (1) ⟹ (3) of Stacks 0AN5,
`hasTautOnAffineChartMap_of_isRepresentableByAlgebraicSpacesULift`. Neither step needs the
charts to be countably indexed — that is only needed in the converse direction, where a
presentation has to be produced rather than received — so `X` and `Y` need only be formal
algebraic spaces. Indeed `X` itself is unconstrained. -/
theorem isTautOnEveryAffineEtaleDiagram_of_isRepresentableByAlgebraicSpaces
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsTautOnEveryAffineEtaleDiagram B S hS f := by
  intro U V a b t hU hV ha hb hsq
  refine hasTautOnAffineChartMap_of_isRepresentableByAlgebraicSpacesULift B S hS t ?_
  exact isRepresentableOnEverySquare_of_isRepresentable B S hS f hY
    (fun s r _ hA' _ hsr ↦ isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace
      B S hS s r hA' hsr) hf U V a b t
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha.1 hb.1 hsq

end AlgebraicGeometry.FormalSpace

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionNotSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallySeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.Examples.Spaces.AffineOverSpaceNoImmersion

/-!
# The involution quotient of the affine line is not locally separated

Stacks 02Z1 asserts of the algebraic space `X = 𝐀¹_k/R`, where `R = Δ ⨿ Γ°` is the relation
scheme of `AlgebraicGeometry.AffineLineInvolution.relationScheme` (the diagonal together with
the graph of negation on the punctured line), that it is quasi-separated but *not* locally
separated — and in particular that the pre-relation `j : R ⟶ U ×_k U` is not an immersion.

This file proves the two remaining assertions.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.not_isImmersion_involutionRelation`: **Stacks
  02Z1**, the pre-relation `j` is not an immersion.
* `AlgebraicGeometry.AffineLineInvolution.not_isAbsolutelyLocallySeparated_involutionQuotient`:
  **Stacks 02Z1**, the quotient is not locally separated.

## Implementation notes

The non-immersion statement is proved exactly as
`AlgebraicGeometry.AffineLineInvolution.not_isClosedImmersion_involutionRelation` disclaims it
would be: by a specialization argument on the restriction of `j` to the two summands of `R`.
On the diagonal summand `j` restricts to the diagonal of `U = 𝐀¹_k`; on the graph summand it
restricts, by `AlgebraicGeometry.AffineLineInvolution.inr_comp_involutionRelation`, to the
inclusion of the puncture followed by the graph of negation. If `j` were an immersion it would
be an embedding, so it would reflect specializations; but the generic point `η` of the
punctured line specializes to every point in particular to the zero section `z`, which
negation fixes, so downstairs the two images specialize into one another while upstairs,
by `not_specializes_relationScheme`, no point of the graph summand specializes to a point of
the diagonal summand. This contradiction is the content of
`not_isImmersion_involutionRelation`.

Passing to the quotient uses the contrapositive of the general criterion
`AlgebraicGeometry.Space.isImmersion_of_represented_kernelPair`, recorded here as
`AlgebraicGeometry.Space.not_isLocallySeparatedOver_of_not_isImmersion_kernelPair`: on a
locally separated presheaf a represented kernel pair of a chart is an immersion into the
product of the chart with itself, so a non-immersion refutes local separatedness. The chart
`𝔸¹_k ⟶ X` of `AlgebraicGeometry.AffineLineInvolution.involutionQuotient` represents the
kernel pair `(chartTarget, chartSource)` of the relation by
`AlgebraicGeometry.Space.quotientMap_isPullback` (Stacks 02WV), and this kernel pair is
identified with `(involutionRelation k).left` by
`Stacks.Examples.AffineOverAlgebraicSpace.relation_eq_involutionRelation`. The absolute
statement then follows from the contrapositive of
`AlgebraicGeometry.Space.isLocallySeparatedOver_of_isAbsolutelyLocallySeparated` (Stacks 04ZI,
part 2), fed by the algebraicity of the quotient,
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient`.

## References

* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 04ZI](https://stacks.math.columbia.edu/tag/04ZI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open Stacks.Examples.AffineOverAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

/-- On the first summand of the relation scheme the pre-relation of Stacks 02Z1 is the
diagonal of the affine line. -/
theorem inl_comp_involutionRelation :
    (coprod.inl : affineLine k ⟶ relationScheme k) ≫ involutionRelation k
      = Limits.diag (affineLine k) := by
  refine prod.hom_ext ?_ ?_ <;>
    simp [involutionRelation, Limits.diag, coprod.inl_desc]

/-- **Stacks 02Z1.** The pre-relation `j : R ⟶ U ×_k U` of the involution quotient is not an
immersion.

On the graph summand `j` restricts to the inclusion of the puncture followed by the graph of
negation; on the diagonal summand it restricts to the diagonal. The generic point of the
punctured line specializes to the zero section, which negation fixes, so an immersion would
force a specialization between the images of the two summands that
`not_specializes_relationScheme` rules out upstairs. -/
@[stacks 02Z1 "the relation j is not an immersion"]
theorem not_isImmersion_involutionRelation :
    ¬ AlgebraicGeometry.IsImmersion ((involutionRelation k).left) := by
  intro him
  have hΔ := inl_comp_involutionRelation k
  have hΓ := inr_comp_involutionRelation k
  obtain ⟨η, hηmem, hηspec⟩ := exists_genericPoint_affineLine k
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of k)))
  set z : (affineLine k).left := originSection k x₀ with hz
  set ηV : (puncturedAffineLine k).left := ⟨η, hηmem⟩ with hηV
  have horig_w : originSection k ≫ (affineLine k).hom = 𝟙 (Spec (.of k)) := by
    simp [originSection]
  set chartOrigin : (Over.mk (𝟙 (Spec (.of k))) : Over (Spec (.of k))) ⟶ affineLine k :=
    Over.homMk (originSection k) horig_w with hchartOrigin
  have hchartOriginLeft : chartOrigin.left = originSection k := rfl
  have horigin : chartOrigin ≫ negGraph k = chartOrigin ≫ Limits.diag (affineLine k) := by
    refine prod.hom_ext ?_ ?_
    · simp [negGraph, Limits.diag]
    · simp only [negGraph, Limits.diag, Category.assoc, prod.lift_snd, Category.comp_id]
      exact Over.OverMorphism.ext <| by
        rw [Over.comp_left, hchartOriginLeft]; exact originSection_comp_affineLineNeg k
  have hcomp : ∀ {X Y Z : Over (Spec (.of k))} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.left),
      (f ≫ g).left x = g.left (f.left x) := fun _ _ _ => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  have hGamma : (involutionRelation k).left
      (((coprod.inr : puncturedAffineLine k ⟶ relationScheme k).left) ηV) =
      ((negGraph k).left) η := by
    rw [← hcomp, hΓ, hcomp, puncturedAffineLineInclusion_left, hηV, Scheme.Opens.ι_apply]
  have hDelta : (involutionRelation k).left
      (((coprod.inl : affineLine k ⟶ relationScheme k).left) z) =
      ((negGraph k).left) z := by
    have hz' : z = chartOrigin.left x₀ := by rw [hchartOriginLeft]
    rw [hz', ← hcomp, ← hcomp chartOrigin, hΔ, ← hcomp, ← horigin, hcomp]
  have hTargetSpec : (involutionRelation k).left
      (((coprod.inr : puncturedAffineLine k ⟶ relationScheme k).left) ηV) ⤳
      (involutionRelation k).left
      (((coprod.inl : affineLine k ⟶ relationScheme k).left) z) := by
    rw [hGamma, hDelta]
    exact (hηspec z).map ((negGraph k).left).continuous
  have hDomainSpec : ((coprod.inr : puncturedAffineLine k ⟶ relationScheme k).left) ηV ⤳
      ((coprod.inl : affineLine k ⟶ relationScheme k).left) z :=
    ((involutionRelation k).left).isEmbedding.isInducing.specializes_iff.mp hTargetSpec
  exact not_specializes_relationScheme k ηV z hDomainSpec

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- The chart `𝔸¹_k ⟶ X` of the involution quotient is not locally separated over `Spec k`:
its represented kernel pair, identified with the relation `j` by
`Stacks.Examples.AffineOverAlgebraicSpace.relation_eq_involutionRelation`, is not an
immersion. -/
theorem not_isLocallySeparatedOver_quotientSpace [NeZero (2 : k)] :
    ¬ Space.IsLocallySeparatedOver B (Spec (.of k)) hS (quotientSpace k B hS) := by
  have := isEtaleEquivalenceRelation_relation k B hS
  refine Space.not_isLocallySeparatedOver_of_not_isImmersion_kernelPair B (Spec (.of k)) hS
    (quotientSpaceMap k B hS) (chartTarget k B hS) (chartSource k B hS)
    (Space.quotientMap_isPullback B (Spec (.of k)) hS (chartSource k B hS) (chartTarget k B hS))
    ?_
  change ¬ AlgebraicGeometry.IsImmersion
    (Space.relation B (Spec (.of k)) hS (chartSource k B hS) (chartTarget k B hS)).left
  rw [relation_eq_involutionRelation]
  exact not_isImmersion_involutionRelation k

/-- **Stacks 02Z1, not locally separated.** Away from characteristic two, the quotient of the
affine line by the punctured graph of negation is not a locally separated algebraic space.

The contrapositive of
`AlgebraicGeometry.Space.isLocallySeparatedOver_of_isAbsolutelyLocallySeparated` (Stacks 04ZI,
part 2) reduces this to the relative statement `not_isLocallySeparatedOver_quotientSpace`, using
the algebraicity of the quotient supplied by
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient`. -/
@[stacks 02Z1 "not_locally_separated"]
theorem not_isAbsolutelyLocallySeparated_involutionQuotient (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    ¬ Space.IsAbsolutelyLocallySeparated B (Spec (.of k)) hS hZ
      (involutionQuotient k B hS).obj := by
  have : NeZero (2 : k) := ⟨hchar⟩
  rw [← quotientSpace_eq k B hS]
  intro h
  exact not_isLocallySeparatedOver_quotientSpace k B hS
    (Space.isLocallySeparatedOver_of_isAbsolutelyLocallySeparated B (Spec (.of k)) hS hZ
      (by rw [quotientSpace_eq]; exact isAlgebraicSpace_involutionQuotient k hchar B hS) h)

end AlgebraicGeometry.AffineLineInvolution

end

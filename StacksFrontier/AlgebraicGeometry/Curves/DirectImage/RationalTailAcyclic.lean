module

public import StacksFrontier.AlgebraicGeometry.Curves.DirectImage.RationalTailHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison

/-!
# The structure sheaf of a curve is acyclic for the contraction of a rational tail

Let `k` be a field, let `X` be a scheme proper over `k` of dimension one with at worst nodal
singularities and only constant global functions, let `C ⊆ X` be a rational tail
([Stacks, Tag 0E3H]) and let `c : X ⟶ X'` be a contraction of `C` onto the scheme-theoretic
closure `X'` of its complement. Then

`R ⁿ c_* 𝒪_X = 0` for every `n > 0`,

that is, `𝒪_X` is acyclic for `c_*`.

[Stacks, Tag 0E3H] only asserts the degree-one case, which is
`Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf`. The vanishing in
every positive degree is what the comparison of the cohomology of `X` with the cohomology of
`X'` needs: the collapse isomorphism `Stacks.AcyclicCollapse.objIso` asks for the vanishing of
`R ⁿ c_*` of its object in *every* positive degree, and it is the only form of that collapse
applicable to a direct image, the sharper degree-by-degree form
`Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app` asking for
`Functor.PreservesInjectiveObjects` of the direct-image functor, which is false (see the
implementation notes of `StacksFrontier/AlgebraicGeometry/ClosedImmersionCohomology/Basic.lean`).

## The argument

It is the argument of the degree-one case, run in every degree. The union sequence
`0 ⟶ 𝒪_X ⟶ 𝒪_C ⊞ 𝒪_{X'} ⟶ 𝒪_{C ∩ X'} ⟶ 0` of [Stacks, Tag 0C4J] has all three of its outer
and middle terms handled in every positive degree:

* `R ⁿ c_* 𝒪_C = 0`, because `c` carries `C` to a point and `H ⁿ(C, 𝒪_C) = 0` for `n > 0`: in
  degree one that is the genus-zero clause of the rational tail, and in degrees two and above it
  is Grothendieck vanishing, `C` being proper over `k` of dimension at most one.
* `R ⁿ c_* 𝒪_{X'} = 0`, already proved in every positive degree.
* `R ⁿ c_* 𝒪_{C ∩ X'} = 0`, because the intersection is carried into `X'` by a closed immersion,
  so both legs of `C ∩ X' ⟶ X ⟶ X'` are affine. This is the same mechanism as for `𝒪_{X'}` and
  needs no cohomological input; in particular the surjectivity used in degree one is not needed
  again in the higher degrees, where the term the connecting map lands in already vanishes.

## Main results

* `Stacks.Curves.isZero_Hgroup_unit_rationalTail`: `H ⁿ(C, 𝒪_C) = 0` for every `n > 0`, for a
  rational tail of a proper one-dimensional curve.
* `Stacks.Curves.isZero_rightDerived_pushforward_structureSheaf_rationalTail`,
  `Stacks.Curves.isZero_rightDerived_pushforward_structureSheaf_intersection` and
  `Stacks.Curves.isZero_rightDerived_pushforward_biprod_structureSheaves`: the three terms of
  the union sequence, in every positive degree.
* `Stacks.Curves.isZero_rightDerived_pushforward_ambientStructureSheaf`: **`R ⁿ c_* 𝒪_X = 0` for
  every `n > 0`**, at the standing hypotheses of [Stacks, Tag 0E3H].
* `Stacks.Curves.rightAcyclic_pushforward_ambientStructureSheaf`: the same, packaged as
  acyclicity of `𝒪_X` for `c_*`.

## Implementation notes

The dimension hypothesis `topologicalKrullDim X = 1` is used here for two things: the Grothendieck
vanishing on `C`, through the bound `dim C ≤ dim X` along the closed immersion `C ⟶ X`; and, as in
the degree-one case, the identification of the scheme-theoretic union of `C` and `X'` with `X`.

No `@[stacks 0E3H]` attribute is placed here, and the reason is a covering-set judgement rather
than the audit scanner: the tag's direct-image clause is the degree-one statement, and *that* is
registered, as `@[stacks 0E3H "higher_direct_image_vanishing"]` on
`Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf` in
`Curves/DirectImage/RationalTailHigherDirectImage.lean`. What this file proves is the
unbounded-degree strengthening, which the source does not assert; labelling it too would claim
one clause twice, at a shape the source does not have.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}

/-- **A rational tail of a proper one-dimensional curve has `H ⁿ(C, 𝒪_C) = 0` for every
`n > 0`.** In degree one this is the genus-zero clause of the rational tail, through
`Stacks.Curves.isZero_Hgroup_unit_one_rationalTail`. In the higher degrees it is Grothendieck
vanishing, [Stacks, Tag 02UZ]: the tail is a closed subscheme of `X`, hence proper over `k` and
of dimension at most that of `X`, which is one. -/
public theorem isZero_Hgroup_unit_rationalTail (hdim : topologicalKrullDim X = 1)
    (hC : IsRationalTail k X C) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (Hgroup C.subscheme.ringCatSheaf ⊤ n
      (SheafOfModules.unit C.subscheme.ringCatSheaf)) := by
  match n, hn with
  | 1, _ => exact isZero_Hgroup_unit_one_rationalTail hC
  | (m + 2), _ =>
    refine (isZero_cohomologyOverField_iff_isZero_hgroup k
      (C.subschemeι ≫ (X ↘ Spec (.of k))) _ (m + 2)).1 ?_
    refine isZero_cohomologyOverField_of_topologicalKrullDim_le k
      (C.subschemeι ≫ (X ↘ Spec (.of k))) _ (d := 1) ?_ (by omega)
    have hle := C.subschemeι.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    rw [hdim] at hle
    exact_mod_cast hle

/-- **`R ⁿ c_* 𝒪_C = 0` in every positive degree, for a contraction `c` of a rational tail
`C`.** This is `Stacks.Curves.isZero_rightDerived_one_pushforward_structureSheaf_rationalTail`
in every degree: the contraction carries all of `C` to the attaching point, so the higher direct
image is the cohomology of `C`, and that vanishes above degree zero by
`Stacks.Curves.isZero_Hgroup_unit_rationalTail`. -/
public theorem isZero_rightDerived_pushforward_structureSheaf_rationalTail
    (hdim : topologicalKrullDim X = 1)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      ((Scheme.Modules.pushforward C.subschemeι).obj
        (SheafOfModules.unit C.subscheme.ringCatSheaf))) :=
  Stacks.PointImageHigherDirectImage.isZero_rightDerived_pushforward_pushforward_of_const
    C.subschemeι c (SheafOfModules.unit C.subscheme.ringCatSheaf)
    (base_const_of_isContractionOfRationalTail hc) n hn
    (isZero_Hgroup_unit_rationalTail hdim hC n hn)

/-- **`R ⁿ c_* 𝒪_{C ∩ X'} = 0` in every positive degree, for a contraction `c` of a rational
tail.** The scheme-theoretic intersection of the tail with the closure of its complement is a
closed subscheme of that closure, so the contraction carries it there by a closed immersion
(`Stacks.Curves.isClosedImmersion_intersectionWithComplementaryCurveι_comp`); both legs of
`C ∩ X' ⟶ X ⟶ X'` are then affine and the collapse of
`Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp` applies with
[Stacks, Tag 01XC] at each. No cohomological input is needed. -/
public theorem isZero_rightDerived_pushforward_structureSheaf_intersection
    {c : X ⟶ complementaryCurve C}
    (hc : complementaryCurveι C ≫ c = 𝟙 (complementaryCurve C)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf
        (intersectionWithComplementaryCurveIdeal C))) := by
  have := isClosedImmersion_intersectionWithComplementaryCurveι_comp hc
  exact Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp
    (intersectionWithComplementaryCurveIdeal C).subschemeι c
    (SheafOfModules.unit (intersectionWithComplementaryCurveIdeal C).subscheme.ringCatSheaf) n hn

/-- **`R ⁿ c_* 𝒪_{X'} = 0` in every positive degree, for a contraction `c` of a rational
tail.** This is
`Stacks.Curves.isZero_rightDerived_one_pushforward_structureSheaf_complementaryCurve` in every
degree, by the same argument: the contraction restricts to the identity on `X'`, so both legs of
`X' ⟶ X ⟶ X'` are affine. -/
public theorem isZero_rightDerived_pushforward_structureSheaf_complementaryCurve
    {c : X ⟶ complementaryCurve C}
    (hc : complementaryCurveι C ≫ c = 𝟙 (complementaryCurve C)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf (complementaryCurveIdeal C))) := by
  have : IsAffineHom (complementaryCurveι C ≫ c) := by rw [hc]; infer_instance
  exact Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp
    (complementaryCurveι C) c (SheafOfModules.unit (complementaryCurve C).ringCatSheaf) n hn

/-- **`R ⁿ c_*(𝒪_C ⊞ 𝒪_{X'}) = 0` in every positive degree, for a contraction `c` of a rational
tail.** The biproduct is split, so the vanishing transfers from the two summands by
`Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂`, exactly as in degree one. -/
public theorem isZero_rightDerived_pushforward_biprod_structureSheaves
    (hdim : topologicalKrullDim X = 1)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf C ⊞
        Scheme.IdealSheafData.closedSubschemeStructureSheaf (complementaryCurveIdeal C))) :=
  Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf C)
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf
        (complementaryCurveIdeal C))).shortExact
    (Scheme.Modules.pushforward c) n
    (isZero_rightDerived_pushforward_structureSheaf_rationalTail hdim hc n hn)
    (isZero_rightDerived_pushforward_structureSheaf_complementaryCurve hc.1 n hn)

/-- **`R ⁿ c_* 𝒪_{C ∪ X'} = 0` in every positive degree, for a contraction `c` of a rational
tail.** This is the union sequence of [Stacks, Tag 0C4J] read in degree `n`, at the pair
`(C, complementaryCurveIdeal C)`, whose scheme-theoretic union is cut out by
`C ⊓ complementaryCurveIdeal C`; identifying that union with `X` is done in
`Stacks.Curves.isZero_rightDerived_pushforward_ambientStructureSheaf` and needs the dimension and
nodality hypotheses, which the vanishing itself does not.

In degree one the surjectivity
`Stacks.Curves.epi_rightDerived_zero_pushforward_map_biprodToIntersection` is what makes the
connecting map vanish, as in the degree-one case; from degree two on the term the connecting map
leaves — `R ⁿ c_* 𝒪_{C ∩ X'}` with `n > 0` — is itself zero, so every map out of it is an
epimorphism and no surjectivity has to be produced. -/
public theorem isZero_rightDerived_pushforward_schemeTheoreticUnion
    (hdim : topologicalKrullDim X = 1)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf
        (C ⊓ complementaryCurveIdeal C))) := by
  obtain ⟨hz, hSE⟩ :=
    Scheme.IdealSheafData.unionIntersection_shortExact C (complementaryCurveIdeal C)
  match n, hn with
  | (m + 1), _ =>
    refine Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_epi hSE
      (Scheme.Modules.pushforward c) m ?_
      (isZero_rightDerived_pushforward_biprod_structureSheaves hdim hc (m + 1) m.succ_pos)
    match m with
    | 0 => exact epi_rightDerived_zero_pushforward_map_biprodToIntersection hc.1
    | (p + 1) =>
      exact ⟨fun g h _ =>
        (isZero_rightDerived_pushforward_structureSheaf_intersection hc.1 (p + 1)
          p.succ_pos).eq_of_src g h⟩

/-- **`R ⁿ c_* 𝒪_X = 0` in every positive degree, for a contraction `c` of a rational tail on a
nodal curve**: the structure sheaf of `X` is acyclic for the direct image along the contraction.

This is the unbounded-degree form of the direct-image clause of [Stacks, Tag 0E3H], at that
tag's standing hypotheses. As in the degree-one case
`Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf`, the nodality and
global-sections hypotheses enter only through
`Stacks.Curves.tail_inf_complementaryCurveIdeal_eq_bot`, which says that the tail and the
closure of its complement cover `X` scheme-theoretically. -/
public theorem isZero_rightDerived_pushforward_ambientStructureSheaf
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (Scheme.IdealSheafData.ambientStructureSheaf X)) :=
  (isZero_rightDerived_pushforward_schemeTheoreticUnion hdim hc n hn).of_iso
    (((Scheme.Modules.pushforward c).rightDerived n).mapIso
      ((Scheme.IdealSheafData.closedSubschemeStructureSheafBotIso X).symm ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.closedSubschemeStructureSheaf
          (tail_inf_complementaryCurveIdeal_eq_bot k X hdim hnodal C hC).symm)))

/-- **The structure sheaf of `X` is acyclic for the direct image along a contraction of a
rational tail.** This is
`Stacks.Curves.isZero_rightDerived_pushforward_ambientStructureSheaf` in the shape the collapse
isomorphism `Stacks.AcyclicCollapse.objIso` consumes. -/
public theorem rightAcyclic_pushforward_ambientStructureSheaf
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
  isZero_rightDerived_pushforward_ambientStructureSheaf hdim hnodal hc n hn

end Stacks.Curves

end

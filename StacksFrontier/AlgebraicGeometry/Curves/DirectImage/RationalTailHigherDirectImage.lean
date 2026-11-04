module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.SchemeTheoreticUnion
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Contraction
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusZeroVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.PointImageHigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionExactSequence

/-!
# The first higher direct image of the structure sheaf of a contracted rational tail vanishes

Let `k` be a field, let `X` be a scheme proper over `k`, let `C ⊆ X` be a rational tail
([Stacks, Tag 0E3H]) and let `c : X ⟶ X'` be a contraction of `C` onto the scheme-theoretic
closure `X'` of its complement. Then

`R ¹ c_* 𝒪_X = 0`,

which is the direct-image vanishing asserted by [Stacks, Tag 0E3H].

It is obtained from the union sequence `0 ⟶ 𝒪_X ⟶ 𝒪_C ⊞ 𝒪_{X'} ⟶ 𝒪_{C ∩ X'} ⟶ 0` of
[Stacks, Tag 0C4J], through the long exact sequence of higher direct images: the middle term has
`R ¹ c_*(𝒪_C ⊞ 𝒪_{X'}) = 0`, and `c_*` carries the last arrow to a surjection. The two summands
of the middle term are separate statements. For the tail,

`R ¹ c_* 𝒪_C = 0`

is the two inputs this file imports, in sequence:

* the contraction carries all of `C` to the attaching point — that is the second clause of
  `AlgebraicGeometry.IsContractionOfRationalTail`, which factors `C ⟶ X ⟶ X'` through the
  spectrum of the residue field at the attaching point, a one-point scheme — so
  `Stacks.PointImageHigherDirectImage.isZero_rightDerived_pushforward_pushforward_of_const`
  reduces the higher direct image to the cohomology `H ¹(C, 𝒪_C)`;
* and `H ¹(C, 𝒪_C) = 0`, which is
  `AlgebraicGeometry.isZero_Hgroup_unit_one_of_genus_eq_zero` applied to the genus-zero clause of
  the rational tail, properness of `C` over `k` coming from the closed immersion `C ⟶ X`.

For the closure of the complement the contraction restricts to the identity, and the surjectivity
of `c_*(𝒪_C ⊞ 𝒪_{X'}) ⟶ c_* 𝒪_{C ∩ X'}` comes from the same source: the intersection is a closed
subscheme of `X'`, so functions on `X'` already restrict onto it.

## Main results

* `Stacks.Curves.isZero_Hgroup_unit_one_rationalTail`: `H ¹(C, 𝒪_C) = 0` for a rational tail of a
  scheme proper over the ground field.
* `Stacks.Curves.isZero_rightDerived_one_pushforward_structureSheaf_rationalTail`:
  `R ¹ c_* 𝒪_C = 0` for a contraction `c` of the rational tail.
* `Stacks.Curves.epi_rightDerived_zero_pushforward_map_biprodToIntersection`: `R ⁰ c_*` carries
  the difference-of-restrictions map of [Stacks, Tag 0C4J] to an epimorphism.
* `Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf`:
  `R ¹ c_* 𝒪_X = 0`, at the standing hypotheses of [Stacks, Tag 0E3H].

## Implementation notes

The statement is about an arbitrary contraction `c`, characterised by
`AlgebraicGeometry.IsContractionOfRationalTail`, rather than about
`Stacks.Curves.canonicalContraction`; only the restriction of `c` to `C` is used, and not even
its value, just the fact that the restriction factors through a one-point scheme. Specialising to
the canonical contraction is `isContractionOfRationalTail_canonicalContraction`.

Properness of `X` over `k` is an instance hypothesis. It is one of the standing hypotheses of
[Stacks, Tag 0E3H], and it is what the finiteness input [Stacks, Tag 02O6] of
`AlgebraicGeometry.isZero_Hgroup_unit_one_of_genus_eq_zero` needs: without it `genus f = 0` says
only that a possibly infinite-dimensional space has `Module.finrank` zero.

`Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf` carries a *scoped*
`@[stacks 0E3H "higher_direct_image_vanishing"]`. An earlier note withheld the attribute on two
grounds, neither of which survives. The first was that the audit scanner keys on the bare
four-character tag while this is one clause of a covering set with a dozen declarations in it;
that is exactly the situation the scoped sub-label convention of
`Curves/CanonicalContraction/Existence.lean` addresses, and it is why the other registrations in
this covering set are scoped. The second was that the genus equality the tag ultimately asserts
is downstream of the vanishing proved here and is not claimed — true, and irrelevant: a scoped
label claims its clause and not the tag, and the genus equality is registered where it is
proved, in `Curves/DirectImage/RationalTailCohomologyIso.lean`. `R ¹ c_* 𝒪_X = 0` is an
assertion the source makes outright, at its own standing hypotheses.

The unbounded-degree form in `Curves/DirectImage/RationalTailAcyclic.lean` is deliberately *not*
registered: it is a strengthening of this clause rather than the clause, and the covering set
wants the declaration that states the source's assertion.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

section Epi

variable {X : Scheme.{u}} {C : X.IdealSheafData}

/-- **A contraction carries the scheme-theoretic intersection of the tail with the closure of
its complement into the complementary curve by a closed immersion.** The intersection is a
closed subscheme of that closure, so its immersion into the ambient scheme factors through
`complementaryCurveι C`, and the contraction undoes that factor. -/
theorem isClosedImmersion_intersectionWithComplementaryCurveι_comp
    {c : X ⟶ complementaryCurve C}
    (hc : complementaryCurveι C ≫ c = 𝟙 (complementaryCurve C)) :
    IsClosedImmersion ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ c) := by
  have hle : complementaryCurveIdeal C ≤ intersectionWithComplementaryCurveIdeal C := le_sup_right
  have hι : (intersectionWithComplementaryCurveIdeal C).subschemeι ≫ c =
      Scheme.IdealSheafData.inclusion hle := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι hle, Category.assoc, hc, Category.comp_id]
  rw [hι]
  exact Scheme.IdealSheafData.isClosedImmersion_inclusion _

/-- **A contraction carries the difference-of-restrictions map of [Stacks, Tag 0C4J] to an
epimorphism.** The map `𝒪_C ⊞ 𝒪_{X'} ⟶ 𝒪_{C ∩ X'}` is already surjective on the first summand
alone, by functions restricted from the ambient curve, and the direct image of that witness is
still a witness because the intersection is carried into `X'` by a closed immersion. -/
theorem epi_pushforward_map_biprodToIntersection {c : X ⟶ complementaryCurve C}
    (hc : complementaryCurveι C ≫ c = 𝟙 (complementaryCurve C)) :
    Epi ((Scheme.Modules.pushforward c).map
      (Scheme.IdealSheafData.biprodToIntersection C (complementaryCurveIdeal C))) :=
  have := isClosedImmersion_intersectionWithComplementaryCurveι_comp hc
  Scheme.IdealSheafData.epi_pushforward_map_biprodToIntersection C (complementaryCurveIdeal C) c

/-- **A contraction carries the difference-of-restrictions map of [Stacks, Tag 0C4J] to an
epimorphism in degree zero of the derived functor.** This is the shape in which the long exact
sequence of higher direct images consumes it. The zeroth right derived functor of a direct image
is the direct image itself, the latter being left exact, and the comparison is natural, so this
is `Stacks.Curves.epi_pushforward_map_biprodToIntersection` conjugated by an isomorphism. -/
theorem epi_rightDerived_zero_pushforward_map_biprodToIntersection
    {c : X ⟶ complementaryCurve C}
    (hc : complementaryCurveι C ≫ c = 𝟙 (complementaryCurve C)) :
    Epi (((Scheme.Modules.pushforward c).rightDerived 0).map
      (Scheme.IdealSheafData.biprodToIntersection C (complementaryCurveIdeal C))) := by
  have := epi_pushforward_map_biprodToIntersection hc
  rw [← NatIso.naturality_2
    (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso c)
    (Scheme.IdealSheafData.biprodToIntersection C (complementaryCurveIdeal C))]
  infer_instance

end Epi

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}

/-- **A rational tail of a scheme proper over `k` has `H ¹(C, 𝒪_C) = 0`.** The tail has genus
zero by definition, and it is proper over `k` because it is a closed subscheme of `X`; so
`AlgebraicGeometry.isZero_Hgroup_unit_one_of_genus_eq_zero` applies. -/
public theorem isZero_Hgroup_unit_one_rationalTail (hC : IsRationalTail k X C) :
    Limits.IsZero (Hgroup C.subscheme.ringCatSheaf ⊤ 1
      (SheafOfModules.unit C.subscheme.ringCatSheaf)) :=
  isZero_Hgroup_unit_one_of_genus_eq_zero k (C.subschemeι ≫ (X ↘ Spec (.of k)))
    hC.genus_eq_zero

omit [IsProper (X ↘ Spec (.of k))] in
/-- **A contraction of a rational tail has constant underlying map on the tail.** The second
clause of `AlgebraicGeometry.IsContractionOfRationalTail` factors `C ⟶ X ⟶ X'` through the
spectrum of the residue field at the attaching point, whose underlying space is a single
point. -/
public theorem base_const_of_isContractionOfRationalTail {hC : IsRationalTail k X C}
    {c : X ⟶ complementaryCurve C} (hc : IsContractionOfRationalTail hC c)
    (u v : C.subscheme) :
    (C.subschemeι ≫ c).base u = (C.subschemeι ≫ c).base v := by
  obtain ⟨-, p, -, hp⟩ := hc
  rw [hp]
  show p.base ((canonicalMapToAttachingPoint hC).base u) =
    p.base ((canonicalMapToAttachingPoint hC).base v)
  congr 1
  exact Subsingleton.elim _ _

/-- **`R ¹ c_* 𝒪_C = 0` for a contraction `c` of a rational tail `C`.**

Here `𝒪_C` is the pushforward of the structure sheaf of `C` along the closed immersion
`C ⟶ X`, which is the shape in which it appears in the union sequence of [Stacks, Tag 0C4J];
so the statement is the vanishing of the first higher direct image along `c` of that
`𝒪_X`-module. It is the tail summand of the reduction of the `R ¹ c_* 𝒪_X = 0` clause of
[Stacks, Tag 0E3H] through that sequence. -/
public theorem isZero_rightDerived_one_pushforward_structureSheaf_rationalTail
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      ((Scheme.Modules.pushforward C.subschemeι).obj
        (SheafOfModules.unit C.subscheme.ringCatSheaf))) :=
  Stacks.PointImageHigherDirectImage.isZero_rightDerived_pushforward_pushforward_of_const
    C.subschemeι c (SheafOfModules.unit C.subscheme.ringCatSheaf)
    (base_const_of_isContractionOfRationalTail hc) 1 Nat.one_pos
    (isZero_Hgroup_unit_one_rationalTail hC)

omit [IsProper (X ↘ Spec (.of k))] in
/-- **`R ¹ c_* 𝒪_{X'} = 0` for a contraction `c` of a rational tail**, where `X'` is the
scheme-theoretic closure of the complement of the tail and `𝒪_{X'}` is its structure sheaf
pushed forward to `X`.

Here the contraction restricts to the *identity* on `X'`, so the composite `X' ⟶ X ⟶ X'` is
affine for a trivial reason, and the collapse of
`Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp` applies with
[Stacks, Tag 01XC] at both legs. No cohomological input about `X'` is needed. -/
public theorem isZero_rightDerived_one_pushforward_structureSheaf_complementaryCurve
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf (complementaryCurveIdeal C))) := by
  have : IsAffineHom (complementaryCurveι C ≫ c) := by
    rw [hc.1]; infer_instance
  exact Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp
    (complementaryCurveι C) c (SheafOfModules.unit (complementaryCurve C).ringCatSheaf)
    1 Nat.one_pos

/-- **`R ¹ c_*(𝒪_C ⊞ 𝒪_{X'}) = 0` for a contraction `c` of a rational tail.**

This is the middle term of the union sequence of [Stacks, Tag 0C4J] at the pair
`(C, complementaryCurveIdeal C)`, whose outer terms are the structure sheaf of `X` — the
scheme-theoretic union of the tail and the closure of its complement — and the structure sheaf
of the attaching point. So this is exactly the hypothesis `h₂` that
`Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁` asks of that sequence at
`n = 0` in order to conclude `R ¹ c_* 𝒪_X = 0`.

The biproduct is handled by the split short exact sequence `0 ⟶ 𝒪_C ⟶ 𝒪_C ⊞ 𝒪_{X'} ⟶ 𝒪_{X'} ⟶ 0`
of `CategoryTheory.ShortComplex.Splitting.ofHasBinaryBiproduct`, to which the long exact
sequence's own `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂` applies: no
additivity of the derived functor on biproducts has to be arranged separately. -/
public theorem isZero_rightDerived_one_pushforward_biprod_structureSheaves
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf C ⊞
        Scheme.IdealSheafData.closedSubschemeStructureSheaf (complementaryCurveIdeal C))) :=
  Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf C)
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf
        (complementaryCurveIdeal C))).shortExact
    (Scheme.Modules.pushforward c) 1
    (isZero_rightDerived_one_pushforward_structureSheaf_rationalTail hc)
    (isZero_rightDerived_one_pushforward_structureSheaf_complementaryCurve hc)

/-- **`R ¹ c_* 𝒪_{C ∪ X'} = 0` for a contraction `c` of a rational tail.**

This is the reduction of the `R ¹ c_* 𝒪_X = 0` clause of [Stacks, Tag 0E3H] through the union
sequence of [Stacks, Tag 0C4J], carried out: the sequence is applied at the pair
`(C, complementaryCurveIdeal C)`, whose scheme-theoretic union is cut out by
`C ⊓ complementaryCurveIdeal C`. Identifying that union with `X` needs the dimension and
nodality hypotheses of the tag and is done in
`Stacks.Curves.isZero_rightDerived_one_pushforward_ambientStructureSheaf`; the vanishing itself
needs neither and is proved here at the union.

The surjectivity input cannot be replaced by
`Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁`, whose hypothesis at `n = 0`
would be `c_* 𝒪_{C ∩ X'} = 0`: the intersection is the attaching point, whose structure sheaf
pushes forward to the residue field there and is not zero. The variant that takes surjectivity
instead is `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_epi`, and the
surjectivity it asks for is
`Stacks.Curves.epi_rightDerived_zero_pushforward_map_biprodToIntersection`. -/
public theorem isZero_rightDerived_one_pushforward_schemeTheoreticUnion
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf
        (C ⊓ complementaryCurveIdeal C))) := by
  obtain ⟨hz, hSE⟩ :=
    Scheme.IdealSheafData.unionIntersection_shortExact C (complementaryCurveIdeal C)
  exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_epi hSE
    (Scheme.Modules.pushforward c) 0
    (epi_rightDerived_zero_pushforward_map_biprodToIntersection hc.1)
    (isZero_rightDerived_one_pushforward_biprod_structureSheaves hc)

/-- **`R ¹ c_* 𝒪_X = 0` for a contraction `c` of a rational tail on a nodal curve.**

This is the direct-image vanishing clause of [Stacks, Tag 0E3H], at that tag's standing
hypotheses: `X` is proper and one-dimensional over `k` with only constant global functions and
at worst nodal singularities. Those hypotheses enter only through
`Stacks.Curves.tail_inf_complementaryCurveIdeal_eq_bot`, which says that the tail and the
closure of its complement cover `X` scheme-theoretically, so that the union term of
`Stacks.Curves.isZero_rightDerived_one_pushforward_schemeTheoreticUnion` is the structure sheaf
of `X` itself.

The genus equality that [Stacks, Tag 0E3H] ultimately asserts is downstream of this and is not
claimed here; the scoped sub-label registers the direct-image clause alone. -/
@[stacks 0E3H "higher_direct_image_vanishing"]
public theorem isZero_rightDerived_one_pushforward_ambientStructureSheaf
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) :
    Limits.IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (Scheme.IdealSheafData.ambientStructureSheaf X)) :=
  (isZero_rightDerived_one_pushforward_schemeTheoreticUnion hc).of_iso
    (((Scheme.Modules.pushforward c).rightDerived 1).mapIso
      ((Scheme.IdealSheafData.closedSubschemeStructureSheafBotIso X).symm ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.closedSubschemeStructureSheaf
          (tail_inf_complementaryCurveIdeal_eq_bot k X hdim hnodal C hC).symm)))

end Stacks.Curves

end

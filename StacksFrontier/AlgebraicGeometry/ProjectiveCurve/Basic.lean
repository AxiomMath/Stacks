module

public import StacksFrontier.AlgebraicGeometry.AffineSpaceImmersion.Projective
public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Witness
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.MapBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective line over a field is a curve

Every statement of [Stacks, Tag 0A27] and of its proof steps is quantified over curves over a
field, and the right-hand alternative of the tag asserts H-projectivity. So the tag says nothing
about anything projective unless some H-projective curve exists, and before this file none did:
the only inhabitant of `AlgebraicGeometry.IsCurve` in the repository was the affine line
(`AlgebraicGeometry.isCurve_specPolynomial`), which is affine and provably *not* H-projective
(`AlgebraicGeometry.not_exists_isClosedImmersion_projectiveSpaceOver_specPolynomial`).

This file supplies the missing object. The projective line over a field is a curve, so the
hypothesis bundle of `AlgebraicGeometry.isAffine_or_exists_isClosedImmersion_of_compactification`
— the assembly of [Stacks, Tag 0A27] — has a model, and the assembly fires on it and returns the
projective alternative.

The route is the standard affine cover. `AlgebraicGeometry.ProjectiveSpace.fromAffineSpace`
exhibits `𝔸ᴺ_S` as the `i`-th standard chart of `ℙᴺ_S` for each homogeneous coordinate `i`, and
Mathlib knows that affine space over an integral base is integral. Reducedness of `ℙᴺ_S` is then
immediate from the cover. Irreducibility is not, because a cover by irreducible opens need not
be irreducible; what is proved here is that for `N = 1` the two charts must meet, since
otherwise each of them would be closed and the affine line would be proper over the field — and
a proper curve is not affine. Once `ℙ¹_k` is irreducible, its dimension is that of a nonempty
open ([Stacks, Tag 0A21]), i.e. that of `𝔸¹_k`, which is one.

## Main results

* `AlgebraicGeometry.ProjectiveSpace.opensRange_fromAffineSpace` and
  `AlgebraicGeometry.ProjectiveSpace.iSup_opensRange_fromAffineSpace`: the image of the `i`-th
  chart immersion is the preimage of `D₊(Tᵢ)`, and the `N + 1` charts cover `ℙᴺ_S`.
* `AlgebraicGeometry.ProjectiveSpace.exists_mem_range_fromAffineSpace` and
  `AlgebraicGeometry.ProjectiveSpace.affineSpaceCover`: that cover pointwise, and as an
  `AlgebraicGeometry.Scheme.OpenCover`.
* `AlgebraicGeometry.isReduced_projectiveSpace`: `ℙᴺ_S` is reduced when `S` is, for every `N`.
* `AlgebraicGeometry.topologicalKrullDim_affineSpace` and
  `AlgebraicGeometry.isCurve_affineSpace`: **affine space on one coordinate over a field has
  dimension one and is a curve**, from Mathlib's instances for
  `AlgebraicGeometry.AffineSpace`.
* `AlgebraicGeometry.not_isProper_affineSpace`: the affine line is not proper over its ground
  field.
* `AlgebraicGeometry.irreducibleSpace_of_union_of_isPreirreducible`: a space covered by two
  meeting preirreducible opens is irreducible.
* `AlgebraicGeometry.isPreirreducible_range_fromAffineSpace`,
  `AlgebraicGeometry.union_range_fromAffineSpace_one` and
  `AlgebraicGeometry.inter_range_fromAffineSpace_nonempty`: the two standard charts of `ℙ¹_k` are
  preirreducible, cover it, and meet.
* `AlgebraicGeometry.irreducibleSpace_projectiveSpace_one` and
  `AlgebraicGeometry.isIntegral_projectiveSpace_one`: `ℙ¹_k` is irreducible, hence integral.
* `AlgebraicGeometry.topologicalKrullDim_projectiveSpace_one`: `dim ℙ¹_k = 1`.
* `AlgebraicGeometry.isCurve_projectiveSpaceOver_one`: **the projective line over a field is a
  curve.** It is the only inhabitant of `AlgebraicGeometry.IsCurve` in this repository on a
  scheme that is not affine, and so the first one that can be H-projective.
* `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_projectiveLine`:
  **the assembly of [Stacks, Tag 0A27] fires on `ℙ¹_k`** and returns the projective alternative,
  so its hypothesis set is satisfiable on an object which is not affine.
* `AlgebraicGeometry.isAffineOpen_opensRange_fromAffineSpace`: each standard chart of `ℙᴺ_{Spec R}`
  is an affine open.
* `AlgebraicGeometry.isAffine_or_exists_isClosedImmersion_affineSpace_of_compl_eq_singleton`: the
  model of the assembly with **nonempty** complement — `𝔸¹_k` inside `ℙ¹_k` — conditional on the
  one input this repository does not have, that the complement of the affine chart of `ℙ¹_k` is a
  single point.

## Implementation notes

**Both spellings of relative projective space occur, and the final statement is at the tagged
one.** `AlgebraicGeometry.ProjectiveSpace.fromAffineSpace` lands in
`AlgebraicGeometry.ProjectiveSpace`, while [Stacks, Tag 0A27]'s assembly and the H-projectivity
existential are stated at `AlgebraicGeometry.projectiveSpaceOver`. The two schemes and their
structure morphisms are equal by `rfl` (`AlgebraicGeometry.projectiveSpaceOver_eq_projectiveSpace`
and `AlgebraicGeometry.projectiveSpaceOver_over_eq`), but `AlgebraicGeometry.ProjectiveSpace` is a
`def` and `AlgebraicGeometry.projectiveSpaceOver` a reducible `abbrev`, so instance search does
not cross between them on its own. Everything intermediate is therefore stated at
`AlgebraicGeometry.ProjectiveSpace`, and the curve statement is given once at the
`projectiveSpaceOver` spelling with its type declared, which is what the assembly consumes.

**Only `N = 1` is covered for irreducibility, and the reason is not laziness.** With three or
more homogeneous coordinates, two charts being disjoint does not make either of them closed, so
the argument below has no analogue; the charts of `ℙᴺ_k` do of course all meet, but exhibiting a
point of `D₊(Tᵢ Tⱼ)` needs the homogeneous prime spectrum of the integral model and is not done
here. Reducedness, by contrast, is proved for every `N` and every base.

**No `@[stacks]` attribute is attached to anything here.** [Stacks, Tag 0A23] is the *definition*
of a curve and is carried by `AlgebraicGeometry.IsCurve`; exhibiting an inhabitant of a
definition does not realize the definition's tag. [Stacks, Tag 01NG] is carried by
`Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top` and
`Stacks.ProjectiveChart.basicOpen_X_iso_affineSpace`, and the cover below is that tag transported
along a base change rather than the tag itself.

## References

* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

/-- **The image of the `i`-th chart immersion of `ℙᴺ_S` is the preimage of `D₊(Tᵢ)`.** The chart
square is cartesian and both of its vertical maps are open immersions. -/
public theorem opensRange_fromAffineSpace (N : ℕ) (i : Fin (N + 1)) (S : Scheme.{u}) :
    (fromAffineSpace.{u} N i S).opensRange =
      toProjectiveSpaceZ N S ⁻¹ᵁ standardChart.{u} N i := by
  rw [← opensRange_fromAffineSpaceZ N i]
  exact IsOpenImmersion.opensRange_eq_preimage_opensRange
    (isPullback_fromAffineSpace N i S).flip

/-- **The `N + 1` standard charts cover `ℙᴺ_S`.** This is [Stacks, Tag 01NG] for the integral
model (`Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top`), pulled back along `ℙᴺ_S ⟶ ℙᴺ_ℤ`. -/
public theorem iSup_opensRange_fromAffineSpace (N : ℕ) (S : Scheme.{u}) :
    (⨆ i : Fin (N + 1), (fromAffineSpace.{u} N i S).opensRange) = ⊤ := by
  simp only [opensRange_fromAffineSpace]
  exact Scheme.Hom.iSup_preimage_eq_top _
    (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) N)

/-- Every point of `ℙᴺ_S` lies in one of the `N + 1` standard charts. -/
public theorem exists_mem_range_fromAffineSpace (N : ℕ) (S : Scheme.{u})
    (x : ProjectiveSpace N S) :
    ∃ i : Fin (N + 1), x ∈ Set.range ((fromAffineSpace.{u} N i S).base) := by
  have hx : x ∈ (⨆ i : Fin (N + 1), (fromAffineSpace.{u} N i S).opensRange) := by
    rw [iSup_opensRange_fromAffineSpace N S]; trivial
  exact Opens.mem_iSup.mp hx

/-- **The standard affine cover of `ℙᴺ_S`**: the `N + 1` chart immersions of affine `N`-space,
which are open immersions and jointly surjective. -/
public noncomputable def affineSpaceCover (N : ℕ) (S : Scheme.{u}) :
    (ProjectiveSpace N S).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (N + 1)) (fun _ => AffineSpace (ULift.{u} (Fin N)) S)
    (fun i => fromAffineSpace.{u} N i S) (fun x => by
      obtain ⟨i, y, hy⟩ := exists_mem_range_fromAffineSpace N S x
      exact ⟨i, y, hy⟩)

end ProjectiveSpace

/-- **Relative projective space over a reduced base is reduced.** It is covered by copies of
relative affine space, which Mathlib knows to be reduced. -/
public instance isReduced_projectiveSpace (N : ℕ) (S : Scheme.{u}) [IsReduced S] :
    IsReduced (ProjectiveSpace N S) := by
  have : ∀ i : (ProjectiveSpace.affineSpaceCover N S).I₀,
      IsReduced ((ProjectiveSpace.affineSpaceCover N S).X i) :=
    fun _ => inferInstanceAs (IsReduced (AffineSpace (ULift.{u} (Fin N)) S))
  exact IsReduced.of_openCover _ (ProjectiveSpace.affineSpaceCover N S)

/-! ### Affine space on one coordinate over a field is a curve -/

/-- **Affine space on a one-element set of coordinates over a field has dimension one.** It is
the spectrum of a polynomial ring in one variable over the field
(`AlgebraicGeometry.AffineSpace.SpecIso`), and `dim k[T] = dim k + 1 = 1`. -/
public theorem topologicalKrullDim_affineSpace (k : Type u) [Field k] (ι : Type u) [Unique ι] :
    topologicalKrullDim (AffineSpace ι (Spec (.of k))) = 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (AffineSpace.SpecIso ι (.of k))).isHomeomorph,
    show topologicalKrullDim ↥(Spec (.of (MvPolynomial ι k)))
        = topologicalKrullDim (PrimeSpectrum (MvPolynomial ι k)) from rfl,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv (MvPolynomial.uniqueAlgEquiv k ι).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- **Affine space on a one-element set of coordinates over a field is a curve.** Integrality,
separatedness, finite type and quasi-compactness of the structure morphism are all Mathlib
instances for `AlgebraicGeometry.AffineSpace`; the dimension is
`AlgebraicGeometry.topologicalKrullDim_affineSpace`.

This is the affine line again, but presented as `𝔸¹_k` rather than as
`Spec k[T]`, which is the presentation the standard charts of `ℙᴺ_k` carry. -/
public theorem isCurve_affineSpace (k : Type u) [Field k] (ι : Type u) [Unique ι] :
    IsCurve k (AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)) :=
  { topologicalKrullDim_eq_one := topologicalKrullDim_affineSpace k ι }

/-- **Affine space on a one-element set of coordinates over a field is not proper over that
field.** It is a curve by `AlgebraicGeometry.isCurve_affineSpace` and it is affine, and a proper
curve is not affine (`AlgebraicGeometry.not_isAffine_of_isCurve`). -/
public theorem not_isProper_affineSpace (k : Type u) [Field k] (ι : Type u) [Unique ι] :
    ¬ IsProper (AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)) := by
  intro hproper
  have := hproper
  have := isCurve_affineSpace k ι
  exact not_isAffine_of_isCurve k (AffineSpace ι (Spec (.of k)) ↘ Spec (.of k)) inferInstance

/-! ### The projective line over a field is an integral curve -/

/-- **A space covered by two meeting preirreducible opens is irreducible.** A nonempty open
either meets the first of them, or meets the second — and then meets the first inside the second,
which is preirreducible. So the first open is dense and the space is its closure.

Stated for two opens rather than for a family because that is the shape the two standard charts
of `ℙ¹_k` have; for a larger family the hypothesis would have to say which pairs meet. -/
public theorem irreducibleSpace_of_union_of_isPreirreducible {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUo : IsOpen U) (hcover : U ∪ V = Set.univ)
    (hU : IsPreirreducible U) (hV : IsPreirreducible V) (hmeet : (U ∩ V).Nonempty) :
    IrreducibleSpace X := by
  obtain ⟨p, hpU, hpV⟩ := hmeet
  have hdense : Dense U := by
    refine dense_iff_inter_open.mpr fun W hWo hWne => ?_
    obtain ⟨x, hxW⟩ := hWne
    rcases (Set.eq_univ_iff_forall.mp hcover x) with hxU | hxV
    · exact ⟨x, hxW, hxU⟩
    · obtain ⟨y, hyV, hyW, hyU⟩ := hV W U hWo hUo ⟨x, hxV, hxW⟩ ⟨p, hpV, hpU⟩
      exact ⟨y, hyW, hyU⟩
  have : PreirreducibleSpace X :=
    (preirreducibleSpace_iff X).mpr (hdense.closure_eq ▸ hU.closure)
  exact ⟨⟨p⟩⟩

/-- Each standard chart of `ℙᴺ_S` is preirreducible as soon as `𝔸ᴺ_S` is irreducible: it is the
image of `𝔸ᴺ_S` under a continuous map. -/
public theorem isPreirreducible_range_fromAffineSpace (N : ℕ) (S : Scheme.{u})
    [IrreducibleSpace (AffineSpace (ULift.{u} (Fin N)) S)] (i : Fin (N + 1)) :
    IsPreirreducible (Set.range ((ProjectiveSpace.fromAffineSpace.{u} N i S).base)) := by
  have h := ((preirreducibleSpace_iff (AffineSpace (ULift.{u} (Fin N)) S)).mp inferInstance).image
    ((ProjectiveSpace.fromAffineSpace.{u} N i S).base) (by fun_prop)
  rwa [Set.image_univ] at h

/-- The two standard charts of `ℙ¹_S` cover it. -/
public theorem union_range_fromAffineSpace_one (S : Scheme.{u}) :
    Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 0 S).base) ∪
        Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 1 S).base) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  obtain ⟨i, hi⟩ := ProjectiveSpace.exists_mem_range_fromAffineSpace 1 S x
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

/-- **The two standard charts of `ℙ¹_k` meet.** If they did not, each would be the complement of
the other, hence closed; the chart immersion would then be a closed immersion and the affine line
would be proper over `k`, contradicting `AlgebraicGeometry.not_isProper_affineSpace`.

This is the one place where `N = 1` is used: with more coordinates, two disjoint charts do not
exhaust the space and neither of them becomes closed. -/
public theorem inter_range_fromAffineSpace_nonempty (k : Type u) [Field k] :
    (Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).base) ∩
      Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 1 (Spec (.of k))).base)).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hcompl : Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).base)
      = (Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 1 (Spec (.of k))).base))ᶜ := by
    refine Set.ext fun x => ⟨fun hx hx1 => ?_, fun hx => ?_⟩
    · exact (Set.eq_empty_iff_forall_notMem.mp hempty x) ⟨hx, hx1⟩
    · exact ((Set.eq_univ_iff_forall.mp
        (union_range_fromAffineSpace_one (Spec (.of k)))) x).resolve_right hx
  have hclosed : IsClosed
      (Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).base)) := by
    rw [hcompl]
    exact (ProjectiveSpace.fromAffineSpace.{u} 1 1 (Spec (.of k))).opensRange.isOpen.isClosed_compl
  have : IsClosedImmersion (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))) :=
    IsClosedImmersion.of_isPreimmersion _ hclosed
  have hproper : IsProper (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)) := by
    rw [← ProjectiveSpace.fromAffineSpace_over 1 0 (Spec (.of k))]
    infer_instance
  exact not_isProper_affineSpace k (ULift.{u} (Fin 1)) hproper

/-- **The projective line over a field is irreducible.** Its two standard charts are
preirreducible, they cover it, and they meet. -/
public instance irreducibleSpace_projectiveSpace_one (k : Type u) [Field k] :
    IrreducibleSpace (ProjectiveSpace 1 (Spec (.of k))) :=
  irreducibleSpace_of_union_of_isPreirreducible
    (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).opensRange.isOpen
    (union_range_fromAffineSpace_one (Spec (.of k)))
    (isPreirreducible_range_fromAffineSpace 1 (Spec (.of k)) 0)
    (isPreirreducible_range_fromAffineSpace 1 (Spec (.of k)) 1)
    (inter_range_fromAffineSpace_nonempty k)

/-- **The projective line over a field is integral**: it is irreducible and reduced. -/
public instance isIntegral_projectiveSpace_one (k : Type u) [Field k] :
    IsIntegral (ProjectiveSpace 1 (Spec (.of k))) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- Affine `N`-space is isomorphic, as a scheme, to the image of its `i`-th chart immersion. -/
private noncomputable def affineSpaceIsoOpensRange (N : ℕ) (i : Fin (N + 1)) (S : Scheme.{u}) :
    AffineSpace (ULift.{u} (Fin N)) S ≅
      (ProjectiveSpace.fromAffineSpace.{u} N i S).opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq (ProjectiveSpace.fromAffineSpace.{u} N i S)
    (ProjectiveSpace.fromAffineSpace.{u} N i S).opensRange.ι (by simp)

/-- **The projective line over a field has dimension one.** It is irreducible and locally of
finite type over the field, so its dimension is that of any nonempty open ([Stacks, Tag 0A21]);
the first standard chart is such an open and is `𝔸¹_k`, of dimension one. -/
public theorem topologicalKrullDim_projectiveSpace_one (k : Type u) [Field k] :
    topologicalKrullDim (ProjectiveSpace 1 (Spec (.of k))) = 1 := by
  have hdim := topologicalKrullDim_eq_of_isOpen k (ProjectiveSpace 1 (Spec (.of k)))
    (ProjectiveSpace 1 (Spec (.of k)) ↘ Spec (.of k))
    (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).opensRange
    (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).opensRange.isOpen
    (by
      obtain ⟨x, hx, -⟩ := inter_range_fromAffineSpace_nonempty k
      exact ⟨x, hx⟩)
  refine hdim.trans ?_
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso
      (affineSpaceIsoOpensRange 1 0 (Spec (.of k)))).isHomeomorph).symm.trans
    (topologicalKrullDim_affineSpace k (ULift.{u} (Fin 1)))

/-- **The projective line over a field is a curve** ([Stacks, Tag 0A23]). It is integral, its
structure morphism is separated, locally of finite type and quasi-compact because it is proper
(`AlgebraicGeometry.projectiveSpaceOver_isProper`), and its dimension is one.

In this library exactly four declarations conclude `AlgebraicGeometry.IsCurve`. One is a producer
whose input nothing exhibits
(`Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp`), two are the affine
line in its two presentations, and this is the only one on a scheme that is not affine — so it is
the first object on which the projective alternative of [Stacks, Tag 0A27] can hold. The statement
is given at the `AlgebraicGeometry.projectiveSpaceOver` spelling, which is the one the tag's
assembly and the H-projectivity existential use. -/
@[ega "I 5.5.11", ega "II 7.4.14" "partial"]
public theorem isCurve_projectiveSpaceOver_one (k : Type u) [Field k] :
    IsCurve k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) := by
  have hint : IsIntegral (projectiveSpaceOver 1 (Spec (.of k))) :=
    isIntegral_projectiveSpace_one k
  have hproper : IsProper (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  have hqc : QuasiCompact (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  have hvar : IsVariety k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) := IsVariety.mk
  exact (isCurve_iff k _).mpr ⟨hvar, topologicalKrullDim_projectiveSpace_one k⟩

/-- **The assembly of [Stacks, Tag 0A27] fires on the projective line, and returns the projective
alternative.** Take both the curve and its compactification to be `ℙ¹_k` and the open immersion
to be the identity: the compactification hypothesis — H-projectivity of the target — is the
identity closed immersion (`exists_isClosedImmersion_projectiveSpaceOver_self`), and the inner
claim is vacuous because the identity is surjective. The conclusion cannot be the affine
alternative, since a proper curve is not affine.

So the hypothesis bundle of
`AlgebraicGeometry.isAffine_or_exists_isClosedImmersion_of_compactification` is jointly
satisfiable, on an object which is a curve and is **not** affine — the complementary witness to
`AlgebraicGeometry.isCurve_specPolynomial`, where the same bundle's conclusion is the affine
alternative. -/
public theorem exists_isClosedImmersion_projectiveSpaceOver_projectiveLine (k : Type u)
    [Field k] :
    ∃ (n : ℕ) (i : projectiveSpaceOver 1 (Spec (.of k)) ⟶
          projectiveSpaceOver n (Spec (.of k))),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        = (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) := by
  have hcurve := isCurve_projectiveSpaceOver_one k
  refine (isAffine_or_exists_isClosedImmersion_of_compactification k
    (f := projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    (g := projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) (𝟙 _) (Category.id_comp _)
    (exists_isClosedImmersion_projectiveSpaceOver_self 1 (Spec (.of k)))
    (fun y hy => absurd ⟨y, rfl⟩ hy)).resolve_left ?_
  exact not_isAffine_of_isCurve k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))

/-- **Each standard chart of `ℙᴺ_{Spec R}` is an affine open**: it is isomorphic, as an open
subscheme, to affine `N`-space over `Spec R`, which is affine. -/
public theorem isAffineOpen_opensRange_fromAffineSpace (N : ℕ) (i : Fin (N + 1))
    (R : CommRingCat.{u}) :
    IsAffineOpen (ProjectiveSpace.fromAffineSpace.{u} N i (Spec R)).opensRange := by
  exact IsAffine.of_isIso (affineSpaceIsoOpensRange N i (Spec R)).inv

/-- **The non-degenerate model of the assembly of [Stacks, Tag 0A27], with its one missing input
left in the statement.** The affine line is an open subscheme of the projective line, both are
curves over `k`, and the projective line is H-projective over `k`; so the assembly applies to the
open immersion `𝔸¹_k ⟶ ℙ¹_k`, whose complement is *not* empty, and the branch it then takes is
the one the source performs with [Stacks, Tag 09N9]. The inner claim is discharged from the
hypothesis `hy`.

`hy` — that the complement of the affine chart of `ℙ¹_k` is a single point — is the one input
not proved in this repository. It is left as a hypothesis rather than bundled away, so that the
reach of this model is legible: with it, the assembly has a model whose complement is nonempty,
and `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver_projectiveLine` is the model
with empty complement. Identifying that complement needs the closed subscheme `V₊(T₀)` of the
integral model of the projective line, which this repository does not describe. -/
public theorem isAffine_or_exists_isClosedImmersion_affineSpace_of_compl_eq_singleton
    (k : Type u) [Field k] (y : ProjectiveSpace 1 (Spec (.of k)))
    (hy : (Set.range ((ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).base))ᶜ
      = ({y} : Set (ProjectiveSpace 1 (Spec (.of k))))) :
    IsAffine (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))) ∨
      ∃ (n : ℕ) (i : AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ⟶
            projectiveSpaceOver n (Spec (.of k))),
        IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
          = (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k)) := by
  have := isCurve_affineSpace k (ULift.{u} (Fin 1))
  have := isCurve_projectiveSpaceOver_one k
  have hoi : @IsOpenImmersion (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)))
      (projectiveSpaceOver 1 (Spec (.of k)))
      (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))) :=
    ProjectiveSpace.isOpenImmersion_fromAffineSpace 1 0 (Spec (.of k))
  refine isAffine_or_exists_isClosedImmersion_of_compactification k
    (f := AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k)) ↘ Spec (.of k))
    (g := projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    (ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k)))
    (ProjectiveSpace.fromAffineSpace_over 1 0 (Spec (.of k)))
    (exists_isClosedImmersion_projectiveSpaceOver_self 1 (Spec (.of k))) ?_
  intro z hz
  have hzy := Set.mem_singleton_iff.mp (hy.subset hz)
  refine ⟨(ProjectiveSpace.fromAffineSpace.{u} 1 0 (Spec (.of k))).opensRange,
    Set.ext fun w => ?_, isAffineOpen_opensRange_fromAffineSpace 1 0 (.of k)⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  refine ⟨fun hw hwz => hz (hwz ▸ hw), fun hwz => ?_⟩
  by_contra hw
  exact hwz ((Set.mem_singleton_iff.mp (hy.subset hw)).trans hzy.symm)

end AlgebraicGeometry

end

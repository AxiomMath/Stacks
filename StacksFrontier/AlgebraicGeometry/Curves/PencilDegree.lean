module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.CurveUnitDegree.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesMorphism
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# The morphism to the projective line attached to a pencil

[Stacks, Tag 0CCR] says that for a `𝔤¹_d` — a linear series `(ℒ, V)` of degree `d` and dimension
one on a nonsingular proper curve `X` over a field `k` — the morphism `φ : X ⟶ 𝐏¹_k` of
[Stacks, Tag 0CCP] either

1. is nonconstant and has degree `≤ d`, or
2. factors through a closed point of `𝐏¹_k`, and in that case `H⁰(X, 𝒪_X) ≠ k`.

Both alternatives are formalized, the second one *with* its conclusion, and the tag is stated
whole and under exactly the source's hypotheses on one declaration,
`Stacks.LinearSeriesMorphism.degreeOver_le_or_constant_of_isRegular`, which carries
`@[stacks 0CCR]`.

## The shape of the statement

[Stacks, Tag 0CCP] is the theorem
`LinearSeriesMorphism.exists_hom_over_and_hom_pullback_twistingSheafAtUniverse_of_isRegular`,
which asserts the **existence** of a basis `b` of `V`, of `φ`, and of the comparison
`α : φ ^* 𝒪(1) ⟶ ℒ` carrying the pulled-back coordinates `φ ^* T₀, φ ^* T₁` to the sections
underlying `b`. It does not produce `φ` as data, so there is no term `φ (ℒ, V)` to name. The
source's definite article is therefore rendered by the *property* that characterizes `φ` rather
than by a choice of it, and the tagged theorem is the conjunction of

1. **existence** — there is a triple `(b, φ, α)` of that shape, i.e. Tag 0CCP's data for
   `(ℒ, V)`; and
2. **universality** — *every* triple of that shape satisfies the alternative.

The second component is what makes the statement be about `φ` rather than about some morphism
that happens to behave well: it speaks of every morphism Tag 0CCP's property characterizes, so
it is independent of any choice, and it is strictly stronger than the assertion that *some*
morphism to `𝐏¹_k` over `k` satisfies the alternative. It is proved by
`Stacks.LinearSeriesMorphism.degreeOver_le_or_constant`, the disjunction for a single triple
handed to it, whose arguments the tagged theorem universally quantifies.

## Main definitions

* `Stacks.LinearSeriesMorphism.pullbackProjectiveSpaceTwistingSheafIso`: the two pullback
  spellings of `p ^* 𝒪(1)` agree.

## Main results

* `Stacks.LinearSeriesMorphism.nonempty_pullback_twistingSheafAtUniverse_iso_unit` and
  `Stacks.LinearSeriesMorphism.nonempty_pullback_projectiveSpaceTwistingSheaf_iso_unit`: **the
  source's "the pullback of an invertible module by a constant morphism is trivial"**, at the
  module the tag applies it to.
* `Stacks.LinearSeriesMorphism.invertibleCurveDegree_projectiveSpaceTwistingSheaf_one_pos` and
  `Stacks.LinearSeriesMorphism.one_le_curveDegree_projectiveSpaceTwistingSheaf_one`:
  **`deg 𝒪_{𝐏¹_k}(1) > 0`**, in the two degree spellings.
* `Stacks.LinearSeriesMorphism.isClosed_singleton_of_constant`: the image of a constant morphism
  out of a proper scheme is a closed point.
* `Stacks.LinearSeriesMorphism.one_lt_rank_cohomologyOverField_unit_of_iso_unit`: **the conclusion
  of alternative (2)**, `H⁰(X, 𝒪_X) ≠ k`, from a trivialization of `φ ^* 𝒪(1)`.
* `Stacks.LinearSeriesMorphism.degreeOver_le_or_constant`: the disjunction for a *given* triple
  `(b, p, α)` of the shape [Stacks, Tag 0CCP] produces, on every proper curve carrying such
  data. Universally quantified over its arguments this is the universality component of the tag.
* `Stacks.LinearSeriesMorphism.degreeOver_le_or_constant_of_isRegular`:
  **[Stacks, Tag 0CCR]**, stated whole and under exactly the source's hypotheses.

## Implementation notes

**`H⁰(X, 𝒪_X) ≠ k` is `1 < Module.rank k H⁰(X, 𝒪_X)`.** The structure morphism makes `k` act on
`H⁰(X, 𝒪_X)` with `1` as a generator of the image, so the two statements agree; the rank form is
used rather than `Module.finrank ≠ 1` because `Module.finrank` is zero on an infinite-dimensional
space, which would make a `finrank` statement false exactly where it should be strongest.
`Cardinal`-valued rank needs no finiteness input at all.

**How the conclusion of alternative (2) is proved.** `Γ(ℱ, ⊤)` carries no `Module k` instance —
see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Curves/LinearSeriesMorphism.lean` — so the two sections underlying
a basis of `V` cannot be said to be linearly independent, and the source's "there are two linearly
independent sections of `𝒪_X`" is not directly available. What replaces it is
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap`: the bijection
`H⁰(X, ℱ) ≃ Γ(ℱ, ⊤)` intertwines `α.app ⊤` with the `k`-linear map
`AlgebraicGeometry.cohomologyOverFieldMap k f α 0`. Pulling the basis of `V` back along that
bijection therefore exhibits two classes in `H⁰(X, φ ^* 𝒪(1))` whose images under a `k`-linear map
are linearly independent, hence are themselves linearly independent; so
`2 ≤ Module.rank k H⁰(X, φ ^* 𝒪(1))`, and the trivialization moves that to `𝒪_X`. The linear
structure is never transported onto `Γ`.

**Alternative (1) is the source's computation.** For nonconstant `p`, [Stacks, Tag 0AYZ] —
`AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul` — gives
`deg(p ^* 𝒪(1)) = deg(X/𝐏¹_k)·deg(𝒪(1))`, and part (5) of [Stacks, Tag 0B40]
(`AlgebraicGeometry.invertibleCurveDegree_le_of_hom_ne_zero`) applied to the nonzero `α` gives
`deg(p ^* 𝒪(1)) ≤ deg(ℒ) = d`. That `𝐏¹_k` is a proper curve over `k`, which Tag 0AYZ needs of the
target, is `AlgebraicGeometry.isCurve_projectiveSpaceOver_one`, made a local instance below.

**Only positivity of `deg 𝒪_{𝐏¹_k}(1)` is used, and it is proved rather than assumed.** The
source computes `deg 𝒪_{𝐏¹_k}(1) = 1` and then reads `deg(X/𝐏¹_k)·deg(𝒪(1)) ≤ d` as
`deg(X/𝐏¹_k) ≤ d`; since `deg(X/𝐏¹_k)` is a natural number, `deg 𝒪_{𝐏¹_k}(1) ≥ 1` already gives
that, with the same conclusion. The exact value `1` would need `χ(𝐏¹_k, 𝒪(1)) = 2`, i.e. the
transport of [Stacks, Tag 01XU] (`Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology`) through
the comparison of `Proj k[T₀, T₁]` with `𝐏¹_{Spec k}`, and is not done here;
`Stacks.LinearSeriesMorphism.invertibleCurveDegree_projectiveSpaceTwistingSheaf_one_pos` is the
positivity, and it is the first invertible module of nonzero degree exhibited in this
development.

**"Factors through a closed point" is rendered set-theoretically**, as constancy of `p` together
with closedness of its image point. For the reduced `X` at hand the two are equivalent, but the
equivalence needs [Stacks, Tag 0356] — a morphism from a reduced scheme factors through the
reduced induced structure on a closed subscheme containing its image — together with the
identification of that structure on a closed point with `Spec` of its residue field, and the
repository has neither in a usable form. Closedness of the image point *is* proved, from
properness of `p`.

**The closed point need not be rational, and nothing here assumes it is.** The tag said "is
constant" until Tongmu He's comment #5100 of 12 May 2020 observed that over a `k` which is not
algebraically closed two sections that are linearly independent over `k` need not be
algebraically independent, so the morphism they define can factor through a closed point whose
residue field is a nontrivial extension of `k`; the tag was corrected to "factors through a
closed point". Alternative (2) below is `∃ y, IsClosed {y} ∧ ∀ x, p.base x = y`: it asserts of
the image point only that it is a closed point of `𝐏¹_k`, and says nothing about its residue
field, so a non-rational closed point satisfies it exactly as a rational one does. No hypothesis
anywhere in this file asks `k` to be algebraically closed or the point to be `k`-rational.

**Two pullback spellings of `𝒪(1)` occur and are identified.** Tag 0CCP's `α` has source
`(p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) ^* 𝒪(1)`, the pullback along the
morphism to the integral model `𝐏¹_ℤ`, while Tag 0AYZ speaks of `p ^* ℰ` for a module `ℰ` on
`𝐏¹_k`. The two agree at `ℰ = Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 1
(Spec (.of k))` by `AlgebraicGeometry.Scheme.Modules.pullbackComp`, which is what
`Stacks.LinearSeriesMorphism.pullbackProjectiveSpaceTwistingSheafIso` is.

## References

* [Stacks Project, Tag 0CCR](https://stacks.math.columbia.edu/tag/0CCR)
* [Stacks Project, Tag 0CCP](https://stacks.math.columbia.edu/tag/0CCP)
* [Stacks Project, Tag 0CCN](https://stacks.math.columbia.edu/tag/0CCN)
* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections Stacks.TwistPullbackPinned
open Stacks.AlgebraicGeometry.BirationalCurveFinite (isProper_of_comp_eq)

universe u

namespace Stacks.LinearSeriesMorphism

attribute [local instance] AlgebraicGeometry.isCurve_projectiveSpaceOver_one
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The pullback of `𝒪(1)` along a morphism with constant image is trivial -/

/-- Every point of `𝐏ⁿ_S` lies in one of the standard charts. -/
private theorem exists_mem_standardChart (n : ℕ) (S : Scheme.{u}) (y : projectiveSpaceOver n S) :
    ∃ i : Fin (n + 1), y ∈ projectiveSpaceOver.standardChart n S i :=
  TopologicalSpace.Opens.mem_iSup.mp
    ((projectiveSpaceOver.iSup_standardChart n S).ge (Set.mem_univ y))

/-- The pulled-back coordinate `g ^* Tᵢ` does not vanish at the points mapping into `D₊(Tᵢ)`. -/
private theorem mem_nonvanishingLocus_pullbackCoordSection {n : ℕ} {X : Scheme.{u}}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1)) {x : X}
    (hx : g.base x ∈ AlgebraicGeometry.Proj.basicOpen
      (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i)) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n))
      ((Stacks.NonvanishingSpelling.sectionsEquiv X _).symm (pullbackCoordSection.{u} g i)) := by
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq]
  exact mem_nonvanishingLocus_pullbackGlobalSections g (twistingSheafAtUniverse.{u} n)
    (coordGlobalSection.{u} n i) (mem_nonvanishingLocus_coordGlobalSection i hx)

/-- **A nowhere vanishing pulled-back coordinate section trivializes `g ^* 𝒪(1)`.** If the image
of `g : X ⟶ 𝐏ⁿ_ℤ` lies inside the standard chart `D₊(Tᵢ)`, then the pulled-back coordinate
`g ^* Tᵢ` is a global section of `g ^* 𝒪(1)` which generates every stalk, because `Tᵢ` generates
every stalk of `𝒪(1)` over `D₊(Tᵢ)` ([Stacks, Tag 01MV]) and nonvanishing is preserved by
pullback ([Stacks, Tag 0H78]). Multiplication by a nowhere vanishing global section of an
invertible module is an isomorphism `𝒪_X ⟶ g ^* 𝒪(1)` ([Stacks, Tag 01CY]). -/
theorem nonempty_pullback_twistingSheafAtUniverse_iso_unit {n : ℕ} {X : Scheme.{u}}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (hg : ∀ x : X, g.base x ∈ AlgebraicGeometry.Proj.basicOpen
      (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X i)) :
    Nonempty ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ≅
      SheafOfModules.unit X.ringCatSheaf) := by
  set L := (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n)
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g (twistingSheafAtUniverse.{u} n)
  set s : L.sections :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X L).symm (pullbackCoordSection.{u} g i)
  have hs : Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s = Set.univ :=
    Set.eq_univ_of_forall fun x => mem_nonvanishingLocus_pullbackCoordSection g i (hg x)
  have := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ L s hs
  exact ⟨(asIso (L.unitHomEquiv.symm s)).symm⟩

/-- **The pullback of `𝒪(1)` along a morphism to `𝐏ⁿ_S` whose image is a single point is
trivial.** This is the step the proof of [Stacks, Tag 0CCR] takes verbatim — "the pullback of an
invertible module by a constant morphism is trivial" — at the invertible module the tag applies
it to. The image point lies in one of the standard charts
(`AlgebraicGeometry.projectiveSpaceOver.iSup_standardChart`), so the whole of `X` maps into
`D₊(Tᵢ)` for that `i` and
`Stacks.LinearSeriesMorphism.nonempty_pullback_twistingSheafAtUniverse_iso_unit` applies. -/
theorem nonempty_pullback_projectiveSpaceTwistingSheaf_iso_unit {n : ℕ} {X S : Scheme.{u}}
    (p : X ⟶ projectiveSpaceOver n S) {y : projectiveSpaceOver n S} (hy : ∀ x : X, p.base x = y) :
    Nonempty ((Scheme.Modules.pullback
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).obj
      (twistingSheafAtUniverse.{u} n) ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨i, hi⟩ := exists_mem_standardChart n S y
  refine nonempty_pullback_twistingSheafAtUniverse_iso_unit _ i fun x => ?_
  rw [show (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S).base x =
    (projectiveSpaceOver.toIntegralAtUniverse n S).base (p.base x) from rfl, hy x]
  exact hi

/-! ### The degree of `𝒪(1)` on the projective line is positive -/

/-- **`deg 𝒪_{𝐏¹_k}(1) > 0`.** This is the only property of the degree of the hyperplane sheaf
that [Stacks, Tag 0CCR] consumes: the source computes `deg 𝒪_{𝐏¹_k}(1) = 1` and uses it only to
turn `deg(X/𝐏¹_k)·deg(𝒪(1)) ≤ d` into `deg(X/𝐏¹_k) ≤ d`, for which positivity is enough.

The proof is part (2) of [Stacks, Tag 0B40] at the pulled-back coordinate `Tᵢ`. Some chart
`D₊(Tᵢ)` contains a given point of `𝐏¹_k`
(`AlgebraicGeometry.projectiveSpaceOver.iSup_standardChart`), so `Tᵢ` is a global section of
`𝒪(1)` that does not vanish there and is therefore nonzero. And it must vanish *somewhere*: if it
did not, multiplication by it would be an isomorphism `𝒪_{𝐏¹_k} ⟶ 𝒪(1)` ([Stacks, Tag 01CY]),
and `𝒪(1)` is ample over the affine base `Spec k`
(`Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`) while the structure sheaf of a
proper curve is not (`AlgebraicGeometry.not_isAmple_unit_of_isCurve`), ampleness being an
isomorphism invariant. A nonzero global section with a zero forces positive degree. -/
theorem invertibleCurveDegree_projectiveSpaceTwistingSheaf_one_pos (k : Type u) [Field k] :
    0 < @invertibleCurveDegree k _ (projectiveSpaceOver 1 (Spec (.of k)))
      (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) inferInstance
      (topologicalKrullDim_projectiveSpace_one k).le
      (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) inferInstance := by
  classical
  have hint : IsIntegral (projectiveSpaceOver 1 (Spec (.of k))) := isIntegral_projectiveSpace_one k
  obtain ⟨x⟩ : Nonempty (projectiveSpaceOver 1 (Spec (.of k))) := inferInstance
  obtain ⟨i, hi⟩ := exists_mem_standardChart 1 (Spec (.of k)) x
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv (projectiveSpaceOver 1 (Spec (.of k)))
      (projectiveSpaceTwistingSheaf 1 (Spec (.of k)))).symm
    (pullbackCoordSection.{u} (projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i)
  have hx : x ∈ Stacks.SheafOfModules.nonvanishingLocus
      (X := (projectiveSpaceOver 1 (Spec (.of k))).toRingedSpace)
      (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) s := by
    exact mem_nonvanishingLocus_pullbackCoordSection _ i hi
  let hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (projectiveSpaceOver 1 (Spec (.of k))).sheaf.obj
      (projectiveSpaceOver 1 (Spec (.of k))).ringCatSheaf.property
      (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback
      (projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) (twistingSheafAtUniverse.{u} 1)
  refine invertibleCurveDegree_pos_of_eval_top_ne_zero k
    (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    (topologicalKrullDim_projectiveSpace_one k).le
    (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) s
    (eval_top_ne_zero_of_mem_nonvanishingLocus _ s hx) ?_
  by_contra hall
  push Not at hall
  have hiso := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ
    (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) s (Set.eq_univ_of_forall hall)
  exact not_isAmple_unit_of_isCurve k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    (Scheme.Modules.isAmple_of_iso
      (@asIso _ _ _ _ _ hiso).symm
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp
        (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf 1 (Spec (.of k)))))

/-- **`deg 𝒪_{𝐏¹_k}(1) ≥ 1`**, the rank-one `AlgebraicGeometry.curveDegree` spelling of
`Stacks.LinearSeriesMorphism.invertibleCurveDegree_projectiveSpaceTwistingSheaf_one_pos`. This is
the shape [Stacks, Tag 0AYZ] produces, and the form [Stacks, Tag 0CCR] consumes. -/
theorem one_le_curveDegree_projectiveSpaceTwistingSheaf_one (k : Type u) [Field k] :
    1 ≤ curveDegree k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
      (topologicalKrullDim_projectiveSpace_one k).le
      (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) 1 := by
  have h := invertibleCurveDegree_projectiveSpaceTwistingSheaf_one_pos k
  rw [invertibleCurveDegree_eq_curveDegree_one k
    (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    (topologicalKrullDim_projectiveSpace_one k).le
    (projectiveSpaceTwistingSheaf 1 (Spec (.of k)))] at h
  omega

/-! ### The image of a constant morphism -/

/-- **The image of a constant morphism out of a proper scheme is a closed point.** A morphism
whose composite with a proper structure morphism is proper is itself proper, hence closed, and the
image of the whole space is the singleton. -/
theorem isClosed_singleton_of_constant (k : Type u) [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k)) [IsProper πX] [IsProper πY] [Nonempty X]
    (p : X ⟶ Y) (hp : p ≫ πY = πX) {y : Y} (hy : ∀ x : X, p.base x = y) :
    IsClosed ({y} : Set Y) := by
  have : IsProper p := isProper_of_comp_eq hp
  have hrange : Set.range p.base = ({y} : Set Y) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro - ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (hy x)
    · obtain ⟨x⟩ : Nonempty X := inferInstance
      exact Set.singleton_subset_iff.mpr ⟨x, hy x⟩
  have h := p.isClosedMap _ isClosed_univ
  rw [Set.image_univ, hrange] at h
  exact h

/-! ### The conclusion of the second alternative -/

/-- **A trivialization of `φ ^* 𝒪(1)` forces `H⁰(X, 𝒪_X) ≠ k`.** Let `L'` be a module carrying a
map `α : L' ⟶ ℒ` whose values on a family `t` of global sections are the sections underlying a
basis `b` of the space of sections of a linear series of dimension one. Then `H⁰(X, L')` has rank
at least two, and so does `H⁰(X, 𝒪_X)` when `L' ≅ 𝒪_X`.

The `k`-linear map in play is `AlgebraicGeometry.cohomologyOverFieldMap k f α 0`; the bijection
`H⁰(X, ℱ) ≃ Γ(ℱ, ⊤)` intertwines it with `α.app ⊤`, so the classes `c i` corresponding to `t i`
satisfy `H⁰(α)(c i) = b i`. The family `b` is linearly independent in `H⁰(X, ℒ)`, hence so is `c`,
and the rank is an isomorphism invariant. -/
theorem one_lt_rank_cohomologyOverField_unit_of_iso_unit {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProper f]
    {hdim : topologicalKrullDim X ≤ 1} {d : ℕ} (E : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k E.V) {L' : X.Modules} (α : L' ⟶ E.L) (t : Fin 2 → Γ(L', ⊤))
    (hα : ∀ i, α.app ⊤ (t i) = seriesSections E b i)
    (e : L' ≅ SheafOfModules.unit X.ringCatSheaf) :
    1 < Module.rank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) := by
  classical
  have hAc : ∀ i : Fin 2,
      (cohomologyOverFieldMap k f α 0).hom
          ((cohomologyOverFieldZeroEquivSections k f L').symm (t i)) =
        (b i : cohomologyOverField k f E.L 0) := by
    intro i
    refine (cohomologyOverFieldZeroEquivSections k f E.L).injective ?_
    refine (cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f α
      ((cohomologyOverFieldZeroEquivSections k f L').symm (t i))).trans ?_
    rw [Equiv.apply_symm_apply]
    exact hα i
  have hb : LinearIndependent k fun i : Fin 2 =>
      ((b i : E.V) : cohomologyOverField k f E.L 0) :=
    b.linearIndependent.map' E.V.subtype (Submodule.ker_subtype _)
  have hcomp : LinearIndependent k
      ((cohomologyOverFieldMap k f α 0).hom ∘
        fun i : Fin 2 => (cohomologyOverFieldZeroEquivSections k f L').symm (t i)) := by
    convert hb using 1
    exact funext hAc
  have h2 : (2 : Cardinal.{u}) ≤ Module.rank k (cohomologyOverField k f L' 0) := by
    simpa using (hcomp.of_comp (cohomologyOverFieldMap k f α 0).hom).cardinal_lift_le_rank
  have hrank : Module.rank k (cohomologyOverField k f L' 0) =
      Module.rank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) :=
    (cohomologyOverFieldIso k f e 0).toLinearEquiv.rank_eq
  rw [← hrank]
  exact lt_of_lt_of_le (by exact_mod_cast one_lt_two) h2

/-! ### Comparing the two pullback spellings of the hyperplane sheaf -/

/-- **The two pullback spellings of `p ^* 𝒪(1)` agree.** The source of Tag 0CCP's comparison map
is the pullback of the twisting sheaf on the integral model along `p ≫ (𝐏ⁿ_S ⟶ 𝐏ⁿ_ℤ)`, and the
module Tag 0AYZ is applied to is
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S` on `𝐏ⁿ_S`. They are identified
by `AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
def pullbackProjectiveSpaceTwistingSheafIso {n : ℕ} {S X : Scheme.{u}}
    (p : X ⟶ projectiveSpaceOver n S) :
    (Scheme.Modules.pullback p).obj (projectiveSpaceTwistingSheaf n S) ≅
      (Scheme.Modules.pullback
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).obj (twistingSheafAtUniverse.{u} n) :=
  (Scheme.Modules.pullbackComp p (projectiveSpaceOver.toIntegralAtUniverse n S)).app
    (twistingSheafAtUniverse.{u} n)

/-! ### The two alternatives are exclusive, and the second one's conclusion is `H⁰ ≠ k` -/

/-- **The two alternatives of [Stacks, Tag 0CCR] are mutually exclusive**: the first asserts that
`p` is nonconstant and the second that it is constant, so exactly one of them holds of any `p`.
A disjunction can be true by accident; this records that it is not, and that the theorem below
really decides between the two cases. -/
theorem not_constant_of_not_exists_eq {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h₁ : ¬ ∃ y : Y, ∀ x : X, p.base x = y)
    (h₂ : ∃ y : Y, IsClosed ({y} : Set Y) ∧ ∀ x : X, p.base x = y) : False :=
  h₁ (h₂.imp fun _ h => h.2)

/-- **`1 < Module.rank k M` says exactly that `M` is not `k`**: there is then no `k`-linear
isomorphism `M ≃ k`. This is what makes the conclusion of the second alternative of
[Stacks, Tag 0CCR] the source's `H⁰(X, 𝒪_X) ≠ k` rather than a weaker statement. -/
theorem not_nonempty_linearEquiv_of_one_lt_rank {k M : Type u} [Field k] [AddCommGroup M]
    [Module k M] (h : 1 < Module.rank k M) : ¬ Nonempty (M ≃ₗ[k] k) := by
  rintro ⟨e⟩
  rw [e.rank_eq, Module.rank_self k] at h
  exact absurd h (lt_irrefl 1)

/-! ### Stacks Tag 0CCR -/

/-- **Both alternatives of [Stacks, Tag 0CCR], for a given pair `(p, α)`.** Let `k` be a field,
`X` a proper curve over `k`, and `(ℒ, V)` a `𝔤¹_d` on `X`. Let `p : X ⟶ 𝐏¹_k` be a morphism over
`k` and `α : p ^* 𝒪(1) ⟶ ℒ` a map carrying the pulled-back coordinates to the sections underlying
a basis `b` of `V` — that is, let `(p, α)` be the data [Stacks, Tag 0CCP] produces. Then either

1. `p` is nonconstant and `deg(X/𝐏¹_k) ≤ d`, or
2. `p` is constant with closed image, and `H⁰(X, 𝒪_X) ≠ k`.

`factors through a closed point` is rendered as constancy of `p` with closed image; the closed
point is not required to be `k`-rational. The degree of `p` is `AlgebraicGeometry.degreeOver`,
the degree of the extension of function fields ([Stacks, Tag 02NY]), which is what Tag 0AYZ
computes, and `H⁰(X, 𝒪_X) ≠ k` is `1 < Module.rank k H⁰(X, 𝒪_X)`.

**This is a component of Tag 0CCR and carries no `@[stacks]` attribute.** Read as a theorem
about one triple it says nothing about *the* morphism of Lemma 53.3.2; read with its arguments
universally quantified — which is how the tagged theorem below uses it — it says that every
morphism Tag 0CCP's property characterizes satisfies the alternative. Nonsingularity of `X` is
not among its hypotheses: nonsingularity is what Tag 0CCP needs in order to *produce*
`(b, p, α)`, while the disjunction itself holds on every proper curve carrying such data. The
tag is registered on
`Stacks.LinearSeriesMorphism.degreeOver_le_or_constant_of_isRegular`, which universally
quantifies this and adds Tag 0CCP's existence. -/
theorem degreeOver_le_or_constant (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    {hdim : topologicalKrullDim X ≤ 1} {d : ℕ} (E : LinearSeries k f hdim d 1)
    (b : Module.Basis (Fin 2) k E.V)
    (p : X ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (hp : p ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f)
    (α : (Scheme.Modules.pullback
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} 1) ⟶ E.L)
    (hα : ∀ i, α.app ⊤ (pullbackCoordSection.{u}
      (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i) = seriesSections E b i) :
    (∃ _hnc : ¬ ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, p.base x = y,
        @degreeOver X (projectiveSpaceOver 1 (Spec (.of k))) p inferInstance inferInstance
          (locallyOfFiniteType_of_isCurve_comp k f
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p hp)
          (isDominant_of_not_constant k f
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p _hnc) ≤ d) ∨
      ((∃ y : projectiveSpaceOver 1 (Spec (.of k)),
            IsClosed ({y} : Set (projectiveSpaceOver 1 (Spec (.of k)))) ∧
            ∀ x : X, p.base x = y) ∧
        1 < Module.rank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0)) := by
  classical
  have hL'inv : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} 1)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback
      (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)))
      (twistingSheafAtUniverse.{u} 1)
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E.L :=
    E.isInvertible
  -- `α` is nonzero: it does not kill the section underlying the first basis vector
  have hαne : α ≠ 0 := by
    intro h0
    refine seriesSections_ne_zero E b 0 ?_
    rw [← hα 0, h0, Scheme.Modules.Hom.zero_app]
    rfl
  -- part (5) of Tag 0B40 at `α`, and the degree of `ℒ`
  have hle : @invertibleCurveDegree k _ X f _ hdim _ hL'inv ≤ (d : ℤ) :=
    (invertibleCurveDegree_le_of_hom_ne_zero k f hdim _ E.L α hαne
      (hN := hL'inv) (hL := hLinv)).trans (le_of_eq E.degree_eq)
  by_cases hnc : ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, p.base x = y
  · -- constant: the image is a closed point, and `p ^* 𝒪(1)` is trivial
    right
    obtain ⟨y, hy⟩ := hnc
    refine ⟨⟨y, isClosed_singleton_of_constant k f
      (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p hp hy, hy⟩, ?_⟩
    obtain ⟨e0⟩ := nonempty_pullback_projectiveSpaceTwistingSheaf_iso_unit p hy
    exact one_lt_rank_cohomologyOverField_unit_of_iso_unit E b α
      (fun i => pullbackCoordSection.{u}
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i) (fun i => hα i) e0
  · -- nonconstant: Tag 0AYZ computes the degree of `p ^* 𝒪(1)`
    left
    refine ⟨hnc, ?_⟩
    have hAYZ := curveDegree_pullback_eq_degreeOver_mul k f
      (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p hp hnc
      (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) 1
    have hiso : curveDegree k f hdim ((Scheme.Modules.pullback p).obj
          (projectiveSpaceTwistingSheaf 1 (Spec (.of k)))) 1 =
        curveDegree k f hdim ((Scheme.Modules.pullback
          (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)))).obj
            (twistingSheafAtUniverse.{u} 1)) 1 :=
      curveDegree_eq_of_iso k f hdim 1 (pullbackProjectiveSpaceTwistingSheafIso p)
    have hdeg : @invertibleCurveDegree k _ X f _ hdim _ hL'inv =
        (@degreeOver X (projectiveSpaceOver 1 (Spec (.of k))) p inferInstance inferInstance
          (locallyOfFiniteType_of_isCurve_comp k f
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p hp)
          (isDominant_of_not_constant k f
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p hnc) : ℤ) *
          curveDegree k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
            (topologicalKrullDim_projectiveSpace_one k).le
            (projectiveSpaceTwistingSheaf 1 (Spec (.of k))) 1 := by
      rw [invertibleCurveDegree_eq_curveDegree_one k f hdim _, ← hiso]
      exact hAYZ
    rw [hdeg] at hle
    exact Nat.cast_le.mp
      ((le_mul_of_one_le_right (Int.natCast_nonneg _)
        (one_le_curveDegree_projectiveSpaceTwistingSheaf_one k)).trans hle)

/-- **Stacks Project, Tag 0CCR.** Let `k` be a field, `X` a nonsingular proper curve over `k`,
and `(ℒ, V)` a `𝔤¹_d` on `X`. Then the morphism `φ : X ⟶ 𝐏¹_k` of [Stacks, Tag 0CCP] either

1. is nonconstant and has degree `≤ d`, or
2. factors through a closed point of `𝐏¹_k`, and in this case `H⁰(X, 𝒪_X) ≠ k`.

The whole tag is this one statement. **"The morphism of Lemma 53.3.2" is rendered by its
characterizing property.** [Stacks, Tag 0CCP] asserts the existence of a basis `b` of `V`, a
morphism `p : X ⟶ 𝐏¹_k` over `k`, and a map `α : p ^* 𝒪(1) ⟶ ℒ` carrying the pulled-back
coordinates `p ^* T₀, p ^* T₁` to the sections underlying `b`; it does not single one out, so
there is no term `φ (ℒ, V)` to name. The definite article is therefore read as the conjunction of
two assertions: the first is that such a triple `(b, p, α)` **exists** — which is
`Stacks.LinearSeriesMorphism.exists_hom_over_and_hom_pullback_twistingSheafAtUniverse_of_isRegular`
— and the second that **every** such triple satisfies the alternative, which is
`Stacks.LinearSeriesMorphism.degreeOver_le_or_constant` with its arguments universally
quantified. The second assertion is what makes this a statement about `φ` itself: it holds of
every morphism Tag 0CCP's property characterizes, so it is independent of any choice, and it is
strictly stronger than the assertion that *some* morphism to `𝐏¹_k` over `k` satisfies the
alternative. The two alternatives are mutually exclusive, by
`Stacks.LinearSeriesMorphism.not_constant_of_not_exists_eq`.

Hypotheses: `k` is a field; `X` is a proper curve over `k` (`[IsProper f]`, `[IsCurve k f]`) and
nonsingular (`hreg : IsRegular X`, integrality being already part of `IsCurve`); and
`E : LinearSeries k f hdim d 1` is a `𝔤¹_d`, the degree-`d` dimension-one linear series of
[Stacks, Tag 0CCN]. Nothing else is assumed.

Readings: the degree of `φ` is `AlgebraicGeometry.degreeOver`, the degree of the extension of
function fields ([Stacks, Tag 02NY]); `H⁰(X, 𝒪_X) ≠ k` is `1 < Module.rank k H⁰(X, 𝒪_X)`, which
by `Stacks.LinearSeriesMorphism.not_nonempty_linearEquiv_of_one_lt_rank` rules out every
`k`-linear isomorphism `H⁰(X, 𝒪_X) ≃ₗ[k] k`; and "factors through a closed point" is constancy
of `φ` together with closedness of its image point. **The closed point is not required to be
`k`-rational**, which is the point of Tongmu He's comment on the tag: over a `k` that is not
algebraically closed the morphism attached to two `k`-linearly independent sections can land on
a closed point whose residue field properly extends `k`, and alternative (2) asserts of `y` only
`IsClosed {y}`. See the module documentation for all of these. -/
@[stacks 0CCR "the whole tag. `the morphism of Lemma 53.3.2` is rendered by the property that \
characterizes it: the data of Tag 0CCP exists for `(ℒ, V)`, and every datum of that shape \
satisfies the alternative. `factors through a closed point` is rendered as constancy of the \
morphism with closed image, nothing being asked of the residue field of that point, and \
`H⁰(X, 𝒪_X) ≠ k` as `1 < Module.rank k H⁰(X, 𝒪_X)`"]
theorem degreeOver_le_or_constant_of_isRegular (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] (hreg : IsRegular X)
    {hdim : topologicalKrullDim X ≤ 1} {d : ℕ} (E : LinearSeries k f hdim d 1) :
    (∃ (b : Module.Basis (Fin 2) k E.V) (p : X ⟶ projectiveSpaceOver 1 (Spec (.of k))),
        p ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f ∧
        ∃ α : (Scheme.Modules.pullback
            (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)))).obj
              (twistingSheafAtUniverse.{u} 1) ⟶ E.L,
          ∀ i, α.app ⊤ (pullbackCoordSection.{u}
            (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i) =
            seriesSections E b i) ∧
      ∀ (b : Module.Basis (Fin 2) k E.V) (p : X ⟶ projectiveSpaceOver 1 (Spec (.of k)))
        (hp : p ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f)
        (α : (Scheme.Modules.pullback
            (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)))).obj
              (twistingSheafAtUniverse.{u} 1) ⟶ E.L),
        (∀ i, α.app ⊤ (pullbackCoordSection.{u}
          (p ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))) i) =
          seriesSections E b i) →
        (∃ _hnc : ¬ ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, p.base x = y,
            @degreeOver X (projectiveSpaceOver 1 (Spec (.of k))) p inferInstance inferInstance
              (locallyOfFiniteType_of_isCurve_comp k f
                (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p hp)
              (isDominant_of_not_constant k f
                (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) p _hnc) ≤ d) ∨
          ((∃ y : projectiveSpaceOver 1 (Spec (.of k)),
                IsClosed ({y} : Set (projectiveSpaceOver 1 (Spec (.of k)))) ∧
                ∀ x : X, p.base x = y) ∧
            1 < Module.rank k
              (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0)) := by
  refine ⟨?_, fun b p hp α hα => degreeOver_le_or_constant k f E b p hp α hα⟩
  exact exists_hom_over_and_hom_pullback_twistingSheafAtUniverse_of_isRegular hreg E

end Stacks.LinearSeriesMorphism

end

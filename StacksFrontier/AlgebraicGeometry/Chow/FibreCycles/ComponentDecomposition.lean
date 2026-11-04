module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreCoefficientSum
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreFamilyReduction
public import Mathlib.Data.ENat.BigOperators
import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
import all StacksFrontier.AlgebraicGeometry.Blowup.Colength.LocalBound

/-!
# The family of components of a closed subscheme of the family of projective lines

Stacks Tag 02S5 compares the two fibre cycles of a closed subscheme `Z ⊆ X ×_S 𝐏¹_S`, and its
proof factors through a *claim*: writing `[Z]_{k+1} = ∑ nᵢ [Wᵢ]` over the irreducible components
of `Z` of delta-dimension `k + 1`, the fibre cycles of `Z` are the corresponding weighted sums of
the fibre cycles of the `Wᵢ`. The claim is stated in library vocabulary as
`Stacks.Chow.FibreCycleComponentDecomposition`, and as an implication from the hypotheses of the
tag as `Stacks.Chow.FibreCycleComponentDecompositionRule`.

This file constructs the family the source uses and verifies every structural condition of the
decomposition for it. The family is indexed by `Stacks.Chow.componentIndex`: a pair consisting of
a generic point `η` of an irreducible component of `Z` of relative dimension `k + 1` over the base
and an element of `Fin n` for `n` the multiplicity of that component in `[Z]_{k+1}`; a component
of multiplicity zero therefore contributes nothing, as it must, since it does not occur in
`[Z]_{k+1}`. Its member at `η` is `Stacks.Chow.integralComponentAt η`, the reduced induced
structure on the closure of `η`.

## Main definitions

* `Stacks.Chow.componentPoints` — the generic points of the components of `Z` of relative
  dimension `k + 1`.
* `Stacks.Chow.componentIndex` — the index type of the family of components, each component
  repeated as often as its multiplicity.
* `Stacks.Chow.componentFamily` — the family itself.

## Main results

* `Stacks.Chow.fibreCycleComponentDecompositionRule` — the claim in the proof of Stacks Tag 02S5,
  `Stacks.Chow.FibreCycleComponentDecompositionRule`, is proved.
* `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent_of_within` — consequently Stacks Tag
  02S5 holds as soon as `Stacks.Chow.FibreCyclesRationallyEquivalentWithin` does, that is, as
  soon as Tag 02S4 part (2) is available for a single integral closed subscheme.
* `Stacks.Chow.isIntegral_componentFamily`,
  `Stacks.Chow.relativeDimension_componentFamily`,
  `Stacks.Chow.not_range_componentFamily_subset_range_zeroSection`,
  `Stacks.Chow.not_range_componentFamily_subset_range_infinitySection`,
  `Stacks.Chow.locallyFinite_support_componentFamily` — the four structural conditions of the
  decomposition, for this family.
* `Stacks.Chow.cycleAssociatedToZeroFiber_apply_eq_finsum_componentFamily` and its infinity twin
  — the coefficient identity, at every point of relative dimension `k`.
* `Stacks.Chow.cycleAssociatedToZeroFiber_apply_eq_finsum_minimalPrimes` and its infinity twin —
  the local content of the tag, with the kernel of the stalk map of the section in place of a
  local equation of it and with `ENat.toNat` distributed over the sum.
* `Stacks.Chow.nonempty_componentIndex_of_isIntegral` and
  `Stacks.Chow.componentFamily_eq_of_isIntegral` — the family is not vacuous, and for an
  integral `Z` it is `Z` itself.

## Implementation notes

The relative dimension of a member of the family is read through
`Stacks.Chow.relativeDimension_comp_closedImmersion`: a member is integral, so it has a single
generic point, which maps to the point `η` indexing it, and the relative dimension of `Z` at `η`
is the relative dimension of the ambient family of projective lines there.

Local finiteness is the local finiteness of the images of the irreducible components of `Z`
(`AlgebraicGeometry.locallyFinite_irreducibleComponents_image`) transported along the injection
`TopologicalSpace.genericPoints.component`, exactly as
`Stacks.Chow.closedSubschemeCycleCoeff_locallyFiniteSupport` does; the `Fin n` fibres of the
index type are finite, so the transported family stays locally finite.

That no member lies inside a distinguished section is *derived*, not assumed: a member contained
in the zero section has its indexing point `η` on the zero section, and then the relative
dimension of `Z` at `η` is the relative dimension of `X` at the corresponding point of the zero
fibre, which the delta-dimension bound of Tag 02S5 caps at `k` — contradicting `k + 1`.

The coefficient identity is the source's local computation plus two reindexings onto one common
index set, the set `Stacks.Chow.componentGenericPointsThrough` of maximal points of the support of
`Z` specializing to the point of the section. On one side
`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes` matches the minimal primes of the stalk of the
ideal sheaf of `Z` with that set; on the other, the generic points of the components of `Z` of
relative dimension `k + 1` through the point match it too — surjectively because such a maximal
point cannot be the point of the section itself, which would make it an associated point of `Z`
of relative dimension `k` on a distinguished section, and injectively because the canonical
closed immersion of `Z` is injective. Both summands are then the one function
`Stacks.Chow.zeroComponentSummand`, respectively its infinity twin.

Passing from the length identity, which lives in `ℕ∞`, to the integer coefficients requires the
minimal primes to be finite in number (`Ideal.finite_minimalPrimes_of_isNoetherianRing`) and every
summand to be finite: the first factor because the quotient it is the colength of has Krull
dimension at most zero, the second by
`AlgebraicGeometry.localized_length_ne_top` at a minimal point of a support.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
  (Z : (projectiveLineProduct f).IdealSheafData)

/-! ### A delta-dimension bound is a pointwise bound -/

/-! ### The family of components -/

/-- The generic points of the irreducible components of `Z` whose relative dimension over the
base is `k + 1`: the components occurring in `[Z]_{k+1}`, indexed by their generic points. -/
abbrev componentPoints : Type u :=
  {η : genericPoints Z.subscheme //
    relativeDimension C.dimensionFunction (familyBase f Z) η.1 = k + 1}

/-- The index type of the family of components of `Z` the proof of Stacks Tag 02S5 uses: a
generic point of an irreducible component of `Z` whose relative dimension over the base is
`k + 1`, together with a repetition index running over the multiplicity of that component in
`[Z]_{k+1}`.

A component of multiplicity zero indexes an empty `Fin 0` and so contributes no member, which is
right: such a component does not occur in `[Z]_{k+1}`. -/
abbrev componentIndex : Type u :=
  Σ η : componentPoints C f k Z, Fin (componentMultiplicity Z.subschemeι η.1).toNat

/-- The family of components of `Z` the proof of Stacks Tag 02S5 uses: at the index `η` it is the
reduced induced structure on the closure of `η`, an integral closed subscheme of
`X ×_S 𝐏¹_S`. -/
def componentFamily (j : componentIndex C f k Z) :
    (projectiveLineProduct f).IdealSheafData :=
  integralComponentAt (Z.subschemeι j.1.1.1)

omit [LocallyOfFiniteType f] in
/-- The support of a member of the family of components is the closure of the point indexing
it. -/
theorem coe_support_componentFamily (j : componentIndex C f k Z) :
    ((componentFamily C f k Z j).support : Set (projectiveLineProduct f)) =
      closure {Z.subschemeι j.1.1.1} :=
  coe_support_integralComponentAt _

omit [LocallyOfFiniteType f] in
/-- **Condition (1) of the decomposition.** Every member of the family of components is an
integral closed subscheme. -/
theorem isIntegral_componentFamily (j : componentIndex C f k Z) :
    IsIntegral (componentFamily C f k Z j).subscheme :=
  isIntegral_integralComponentAt _

omit [LocallyOfFiniteType f] in
/-- The canonical closed immersion of a member of the family of components carries its generic
point to the point indexing it. -/
theorem subschemeι_componentFamily_eq (j : componentIndex C f k Z)
    (ξ : genericPoints (componentFamily C f k Z j).subscheme) :
    (componentFamily C f k Z j).subschemeι ξ.1 = Z.subschemeι j.1.1.1 := by
  have := isIntegral_componentFamily C f k Z j
  rw [show ξ.1 = genericPoint (componentFamily C f k Z j).subscheme by
    simpa [genericPoints_eq_singleton] using ξ.2]
  exact genericPointOf_integralComponentAt (Z.subschemeι j.1.1.1)

omit [LocallyOfFiniteType f] in
/-- **Condition (2) of the decomposition.** Every member of the family of components has
relative dimension `k + 1` over the base at each of its generic points: it is integral, so its
only generic point maps to the point indexing it, where the relative dimension of `Z` is
`k + 1`. -/
theorem relativeDimension_componentFamily (j : componentIndex C f k Z)
    (ξ : genericPoints (componentFamily C f k Z j).subscheme) :
    relativeDimension C.dimensionFunction (familyBase f (componentFamily C f k Z j)) ξ.1
      = k + 1 := by
  show relativeDimension C.dimensionFunction
    ((componentFamily C f k Z j).subschemeι ≫
      pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ.1 = k + 1
  have h : relativeDimension C.dimensionFunction
      (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) j.1.1.1
        = k + 1 := j.1.2
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction
    (componentFamily C f k Z j).subschemeι
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ.1,
    subschemeι_componentFamily_eq C f k Z j ξ]
  rwa [relativeDimension_comp_closedImmersion C.dimensionFunction Z.subschemeι
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) j.1.1.1] at h

omit [LocallyOfFiniteType f] in
/-- The point indexing a member of the family of components lies in the range of the canonical
closed immersion of that member. -/
theorem mem_range_subschemeι_componentFamily (j : componentIndex C f k Z) :
    Z.subschemeι j.1.1.1 ∈ Set.range (componentFamily C f k Z j).subschemeι := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_componentFamily C f k Z j]
  exact subset_closure rfl

/-- The support of the inverse image along `g` is the preimage of the support. -/
private theorem coe_support_comap {Y S : Scheme.{u}} {p : Y ⟶ S} (g : Y ⟶ projectiveLineProduct p)
    (W : (projectiveLineProduct p).IdealSheafData) :
    ((W.comap g).support : Set Y) = g ⁻¹' (W.support : Set (projectiveLineProduct p)) := by
  simp

/-- A point of the inverse image of `W` along `g` has relative dimension at most `k`, if the
inverse image has delta-dimension at most `k`. -/
private theorem relativeDimension_le_of_mem_support_comap (g : X ⟶ projectiveLineProduct f)
    (W : (projectiveLineProduct f).IdealSheafData)
    (h : schemeDeltaDimension C ((W.comap g).subschemeι ≫ f) ≤ (k : EInt)) {x : X}
    (hx : g x ∈ (W.support : Set (projectiveLineProduct f))) :
    relativeDimension C.dimensionFunction f x ≤ k := by
  have hx' : x ∈ ((W.comap g).support : Set X) := by rwa [coe_support_comap]
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx'
  obtain ⟨y, rfl⟩ := hx'
  have hle := relativeDimension_le_of_schemeDeltaDimension_le' C ((W.comap g).subschemeι ≫ f) h y
  rwa [relativeDimension_comp_closedImmersion] at hle

/-- The relative dimension of `X ×_S 𝐏¹_S` over the base at a point of a section `g` of the
projection is the relative dimension of `X` there. -/
private theorem relativeDimension_apply_of_comp_fst {Y : Scheme.{u}} (p : Y ⟶ C.S)
    (g : Y ⟶ projectiveLineProduct p) [IsClosedImmersion g]
    (hg : g ≫ pullback.fst p (relativeProjectiveLine C.S ↘ C.S) = 𝟙 Y) (x : Y) :
    relativeDimension C.dimensionFunction
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (g x) =
      relativeDimension C.dimensionFunction p x := by
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction g
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x]
  congr 1
  rw [← Category.assoc, hg, Category.id_comp]

/-- At a point of `Z` lying on a section `g` of the projection, the relative dimension of `Z` over
the base is the relative dimension of `X` at the corresponding point. -/
private theorem relativeDimension_familyBase_eq_of_comp_fst {Y : Scheme.{u}} (p : Y ⟶ C.S)
    (Z : (projectiveLineProduct p).IdealSheafData) (g : Y ⟶ projectiveLineProduct p)
    [IsClosedImmersion g] (hg : g ≫ pullback.fst p (relativeProjectiveLine C.S ↘ C.S) = 𝟙 Y)
    (w : Z.subscheme) (x : Y) (hw : Z.subschemeι w = g x) :
    relativeDimension C.dimensionFunction (familyBase p Z) w =
      relativeDimension C.dimensionFunction p x := by
  rw [familyBase, relativeDimension_comp_closedImmersion, hw,
    relativeDimension_apply_of_comp_fst C p g hg]

/-- No member of the family of components is contained in a section `g` of the projection, if the
inverse image of `Z` along `g` has delta-dimension at most `k`. -/
private theorem not_range_componentFamily_subset_range_of_comp_fst
    (g : X ⟶ projectiveLineProduct f) [IsClosedImmersion g]
    (hg : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) = 𝟙 X)
    (h : schemeDeltaDimension C ((Z.comap g).subschemeι ≫ f) ≤ (k : EInt))
    (j : componentIndex C f k Z) :
    ¬ Set.range (componentFamily C f k Z j).subschemeι ⊆ Set.range g := by
  intro hsub
  obtain ⟨x, hx⟩ := hsub (mem_range_subschemeι_componentFamily C f k Z j)
  have hmem : g x ∈ (Z.support : Set (projectiveLineProduct f)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨j.1.1.1, hx.symm⟩
  have hle := relativeDimension_le_of_mem_support_comap C f k g Z h hmem
  have heq := relativeDimension_familyBase_eq_of_comp_fst C f Z g hg j.1.1.1 x hx.symm
  have hdim := j.1.2
  omega

/-- **Condition (3) of the decomposition, at the zero section.** No member of the family of
components is contained in the zero section.

Were it contained there, the point `η` indexing it would lie on the zero section, so the
relative dimension of `Z` at `η` would be the relative dimension of `X` at the corresponding
point of the zero fibre of `Z`; the delta-dimension bound of Stacks Tag 02S5 on that fibre caps
the latter at `k`, contradicting `k + 1`. -/
theorem not_range_componentFamily_subset_range_zeroSection
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (j : componentIndex C f k Z) :
    ¬ Set.range (componentFamily C f k Z j).subschemeι ⊆ Set.range (zeroSection f) :=
  not_range_componentFamily_subset_range_of_comp_fst C f k Z _ (zeroSection_comp_fst f) h₀ j

/-- **Condition (3) of the decomposition, at the infinity section.** No member of the family of
components is contained in the infinity section, by the same argument as at the zero section. -/
theorem not_range_componentFamily_subset_range_infinitySection
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (j : componentIndex C f k Z) :
    ¬ Set.range (componentFamily C f k Z j).subschemeι ⊆ Set.range (infinitySection f) :=
  not_range_componentFamily_subset_range_of_comp_fst C f k Z _ (infinitySection_comp_fst f) hInf j

/-- The closures of the points indexing the family of components form a locally finite family of
subsets of `X ×_S 𝐏¹_S`.

They are the images under `Z.subschemeι` of the irreducible components of `Z`, which form a
locally finite family on a locally Noetherian scheme (Stacks Tag 02QW), and the index map to the
components is injective because `TopologicalSpace.genericPoints.component` is. -/
theorem locallyFinite_closure_componentPoints :
    LocallyFinite fun η : componentPoints C f k Z =>
      (closure {Z.subschemeι η.1.1} : Set (projectiveLineProduct f)) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian (projectiveLineProduct f) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S))
  have hinj : Function.Injective
      fun η : componentPoints C f k Z => genericPoints.component η.1 := fun a b hab =>
    Subtype.ext (genericPoints.component_injective hab)
  have hcomp := (locallyFinite_irreducibleComponents_image Z.subschemeι).comp_injective hinj
  have heq : (fun η : componentPoints C f k Z =>
        (closure {Z.subschemeι η.1.1} : Set (projectiveLineProduct f))) =
      (fun V : irreducibleComponents Z.subscheme =>
          ⇑Z.subschemeι '' (V : Set Z.subscheme)) ∘
        fun η : componentPoints C f k Z => genericPoints.component η.1 := by
    funext η
    calc (closure {Z.subschemeι η.1.1} : Set (projectiveLineProduct f))
        = ⇑Z.subschemeι '' closure {η.1.1} := by
          rw [← Set.image_singleton, Z.subschemeι.isClosedEmbedding.closure_image_eq]
      _ = ⇑Z.subschemeι ''
            ((genericPoints.component η.1 : irreducibleComponents Z.subscheme) :
              Set Z.subscheme) := by rw [genericPoints.isGenericPoint η.1]
  rw [heq]
  exact hcomp

/-- **Condition (4) of the decomposition.** The family of components is locally finite: its
supports are the closures of the points indexing it, and the `Fin n` fibres of the index type are
finite. -/
theorem locallyFinite_support_componentFamily :
    LocallyFinite fun j : componentIndex C f k Z =>
      ((componentFamily C f k Z j).support : Set (projectiveLineProduct f)) := by
  intro p
  obtain ⟨U, hU, hfin⟩ := locallyFinite_closure_componentPoints C f k Z p
  refine ⟨U, hU, Set.Finite.subset (Set.Finite.biUnion
    (t := fun η : componentPoints C f k Z => Set.range (Sigma.mk η)) hfin
    fun η _ => Set.finite_range _) ?_⟩
  intro j hj
  have hj' : (((componentFamily C f k Z j).support : Set (projectiveLineProduct f)) ∩ U).Nonempty :=
    hj
  refine Set.mem_iUnion₂.mpr ⟨j.1, ?_, j.2, rfl⟩
  show (closure {Z.subschemeι j.1.1.1} ∩ U).Nonempty
  rwa [← coe_support_componentFamily C f k Z j]

/-! ### Pointwise dimension bounds for a single component -/

/-- The support of the integral closed subscheme attached to a point of the support of `Z` is
contained in the support of `Z`. -/
theorem coe_support_integralComponentAt_subset
    {η : projectiveLineProduct f} (hη : η ∈ (Z.support : Set (projectiveLineProduct f))) :
    ((integralComponentAt η).support : Set (projectiveLineProduct f)) ⊆
      (Z.support : Set (projectiveLineProduct f)) := by
  rw [coe_support_integralComponentAt]
  exact Z.support.2.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)

/-- The inverse image along `g` of the integral closed subscheme attached to a point of the
support of `Z` inherits the delta-dimension bound on the inverse image of `Z`: its points are
points of the inverse image of `Z`. -/
private theorem schemeDeltaDimension_comap_integralComponentAt_le (g : X ⟶ projectiveLineProduct f)
    (h : schemeDeltaDimension C ((Z.comap g).subschemeι ≫ f) ≤ (k : EInt))
    {η : projectiveLineProduct f} (hη : η ∈ (Z.support : Set (projectiveLineProduct f))) :
    schemeDeltaDimension C (((integralComponentAt η).comap g).subschemeι ≫ f) ≤ (k : EInt) := by
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C f _ fun z => ?_
  refine relativeDimension_le_of_mem_support_comap C f k g Z h ?_
  have hz : ((integralComponentAt η).comap g).subschemeι z ∈
      (((integralComponentAt η).comap g).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  rw [coe_support_comap] at hz
  exact coe_support_integralComponentAt_subset C f Z hη hz

/-- The zero fibre of the integral closed subscheme attached to a point of the support of `Z`
inherits the delta-dimension bound of Stacks Tag 02S5 on the zero fibre of `Z`: its points are
points of the zero fibre of `Z`. -/
theorem schemeDeltaDimension_zeroFiber_integralComponentAt_le
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    {η : projectiveLineProduct f} (hη : η ∈ (Z.support : Set (projectiveLineProduct f))) :
    schemeDeltaDimension C ((zeroFiber f (integralComponentAt η)).subschemeι ≫ f)
      ≤ (k : EInt) :=
  schemeDeltaDimension_comap_integralComponentAt_le C f k Z _ h₀ hη

/-- The infinity fibre of the integral closed subscheme attached to a point of the support of
`Z` inherits the delta-dimension bound of Stacks Tag 02S5 on the infinity fibre of `Z`. -/
theorem schemeDeltaDimension_infinityFiber_integralComponentAt_le
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    {η : projectiveLineProduct f} (hη : η ∈ (Z.support : Set (projectiveLineProduct f))) :
    schemeDeltaDimension C ((infinityFiber f (integralComponentAt η)).subschemeι ≫ f)
      ≤ (k : EInt) :=
  schemeDeltaDimension_comap_integralComponentAt_le C f k Z _ hInf hη

/-! ### A sum over the repeated index type -/

/-- A sum over a sigma type with `Fin`-fibres whose summand depends only on the base index is
the sum of the integer multiples: each base index contributes its summand as many times as the
cardinality of its fibre.

This is the bookkeeping that turns the multiplicity-weighted sum over the components of `Z` into
an unweighted sum over the repeated index type of `Stacks.Chow.componentIndex`. -/
theorem finsum_sigma_fin_eq_finsum_mul {ι : Type u} {n : ι → ℕ} (c : ι → ℤ)
    (hc : (Function.support fun i => (n i : ℤ) * c i).Finite) :
    ∑ᶠ j : Σ i : ι, Fin (n i), c j.1 = ∑ᶠ i : ι, (n i : ℤ) * c i := by
  classical
  have hsub : Function.support (fun j : Σ i : ι, Fin (n i) => c j.1) ⊆
      ↑(hc.toFinset.sigma fun i => (Finset.univ : Finset (Fin (n i)))) := by
    intro j hj
    refine Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Set.Finite.mem_toFinset hc |>.mpr ?_,
      Finset.mem_univ _⟩)
    have hn : (n j.1 : ℤ) ≠ 0 := by have := j.2.pos; omega
    exact mul_ne_zero hn hj
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_sigma,
    finsum_eq_sum_of_support_subset _ hc.coe_toFinset.ge]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ _s : Fin (n i), c i = (n i : ℤ) * c i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The local identity, in integers -/

/-- The local length identity of Stacks Tag 02QG in the form Stacks Tag 02S5 uses it, with the
first ideal given only as a principal ideal rather than by a chosen generator: the ideal sheaf
of a distinguished section presents itself locally as the kernel of a stalk map, which is
principal but has no canonical generator. -/
private theorem length_quotient_sup_eq_sum_minimalPrimes_of_isPrincipal
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (J I : Ideal A)
    (hJ : ∃ t : A, J = Ideal.span {t})
    (hI : IsLocalRing.maximalIdeal A ∉ associatedPrimes A (A ⧸ I))
    (hdim : ringKrullDim (A ⧸ I) = 1)
    (hJI : ringKrullDim (A ⧸ (J ⊔ I)) ≤ 0) :
    Module.length A (A ⧸ (J ⊔ I)) =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | q.asIdeal ∈ I.minimalPrimes},
        Module.length A (A ⧸ (J ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl (A ⧸ I)) := by
  obtain ⟨t, rfl⟩ := hJ
  exact length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes t I hI hdim hJI

/-- The first factor of each summand of the local identity is finite: the quotient by `J` and a
minimal prime over `I` is a quotient of the quotient by `J` and `I`, which has Krull dimension
at most zero, so it is an Artinian local ring. -/
private theorem length_quotient_sup_ne_top {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (J I : Ideal A) (hJI : ringKrullDim (A ⧸ (J ⊔ I)) ≤ 0)
    {q : PrimeSpectrum A} (hq : q.asIdeal ∈ I.minimalPrimes) :
    Module.length A (A ⧸ (J ⊔ q.asIdeal)) ≠ ⊤ := by
  have hle : J ⊔ I ≤ J ⊔ q.asIdeal := sup_le_sup_left hq.1.2 J
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle) := fun b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.factor_mk hle a⟩
  have hdq : ringKrullDim (A ⧸ (J ⊔ q.asIdeal)) ≤ 0 :=
    (ringKrullDim_le_of_surjective _ hsurj).trans hJI
  refine Module.length_ne_top_iff.mpr (AlgebraicGeometry.finite_length_of_supportDim_le_zero ?_)
  rwa [Module.supportDim_quotient_eq_ringKrullDim]

/-- The second factor of each summand of the local identity is finite: it is the length of a
finite module localized at a minimal point of its support. -/
private theorem length_localizedModule_quotient_ne_top {A : Type*} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) {q : PrimeSpectrum A}
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (A ⧸ I)) ≠ ⊤ :=
  AlgebraicGeometry.localized_length_ne_top q
    ((AlgebraicGeometry.minimal_support_iff q).mpr (by rwa [Ideal.annihilator_quotient]))

/-- The local identity of Stacks Tag 02S5, read in the integers: the minimal primes over `I` are
finite in number and every summand is finite, so passing to `ENat.toNat` distributes over the
sum and over each product. -/
private theorem toNat_finsum_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (J I : Ideal A) (hJI : ringKrullDim (A ⧸ (J ⊔ I)) ≤ 0) :
    (((∑ᶠ q ∈ {q : PrimeSpectrum A | q.asIdeal ∈ I.minimalPrimes},
        Module.length A (A ⧸ (J ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl (A ⧸ I))).toNat : ℤ)) =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | q.asIdeal ∈ I.minimalPrimes},
        ((Module.length A (A ⧸ (J ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl (A ⧸ I))).toNat : ℤ) := by
  have hfin : {q : PrimeSpectrum A | q.asIdeal ∈ I.minimalPrimes}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).preimage
      fun _ _ _ _ h => PrimeSpectrum.ext h
  have hterms : ∀ q ∈ hfin.toFinset, Module.length A (A ⧸ (J ⊔ q.asIdeal)) *
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (A ⧸ I)) ≠ ⊤ := fun q hq =>
    WithTop.mul_ne_top (length_quotient_sup_ne_top J I hJI (hfin.mem_toFinset.mp hq))
      (length_localizedModule_quotient_ne_top I (hfin.mem_toFinset.mp hq))
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    ENat.toNat_sum hterms, Nat.cast_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [ENat.toNat_mul, Nat.cast_mul]

/-! ### Components of `Z` through a point of a distinguished section -/

omit [LocallyOfFiniteType f] in
/-- The image of a generic point of an irreducible component of `Z` is a maximal point of the
support of `Z`, hence one of the component generic points through every point it specializes to.

The canonical closed immersion of `Z` is a homeomorphism onto the support, so a point of the
support specializing to the image of `η` comes from a point `w` of `Z` with `w ⤳ η`; the closure
of `w` then contains the irreducible component `closure {η}`, hence equals it by maximality, and
`w = η` because a scheme is a T0 space. -/
theorem mem_componentGenericPointsThrough_subschemeι (η : genericPoints Z.subscheme)
    {ξ : projectiveLineProduct f} (hspec : Z.subschemeι η.1 ⤳ ξ) :
    Z.subschemeι η.1 ∈ componentGenericPointsThrough Z ξ := by
  refine ⟨?_, hspec, fun η' hη' hη'η => ?_⟩
  · rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨η.1, rfl⟩
  · rw [← Scheme.IdealSheafData.range_subschemeι] at hη'
    obtain ⟨w, rfl⟩ := hη'
    have hw : w ⤳ η.1 :=
      (Z.subschemeι.isClosedEmbedding.isEmbedding.isInducing.specializes_iff).mp hη'η
    have hsub : closure ({η.1} : Set Z.subscheme) ⊆ closure {w} :=
      closure_minimal (Set.singleton_subset_iff.mpr hw.mem_closure) isClosed_closure
    have hback : w ∈ closure ({η.1} : Set Z.subscheme) :=
      η.2.2 isIrreducible_singleton.closure hsub (subset_closure rfl)
    exact congrArg _ (hw.antisymm (specializes_iff_mem_closure.mpr hback)).eq

omit [LocallyOfFiniteType f] in
/-- Conversely, a component generic point of `Z` through `ξ` is the image of a generic point of
an irreducible component of `Z`: it is a maximal point of the support, so the irreducible closed
subsets of `Z` containing the point it comes from are carried into its closure. -/
theorem exists_genericPoints_subschemeι_eq_of_mem_componentGenericPointsThrough
    {ξ η : projectiveLineProduct f} (hη : η ∈ componentGenericPointsThrough Z ξ) :
    ∃ w : genericPoints Z.subscheme, Z.subschemeι w.1 = η := by
  obtain ⟨w, hw⟩ : ∃ w : Z.subscheme, Z.subschemeι w = η := by
    rw [← Set.mem_range, Z.range_subschemeι]
    exact hη.1
  have hmax := maximal_isIrreducible_closure_of_mem_componentGenericPointsThrough hη
  have hclosure : closure ({η} : Set (projectiveLineProduct f)) =
      ⇑Z.subschemeι '' closure {w} := by
    rw [← hw, ← Set.image_singleton, Z.subschemeι.isClosedEmbedding.closure_image_eq]
  refine ⟨⟨w, isIrreducible_singleton.closure, fun T hT hsub => ?_⟩, hw⟩
  have hTim : IsIrreducible (⇑Z.subschemeι '' T) :=
    hT.image _ Z.subschemeι.continuous.continuousOn
  have hTsub : (⇑Z.subschemeι '' T) ⊆ (Z.support : Set (projectiveLineProduct f)) := by
    rw [← Z.range_subschemeι]
    exact Set.image_subset_range _ _
  have hcl : closure ({η} : Set (projectiveLineProduct f)) ⊆ ⇑Z.subschemeι '' T := by
    rw [hclosure]
    exact Set.image_mono hsub
  have himg := hmax.2 ⟨hTim, hTsub⟩ hcl
  intro z hz
  have hzmem : Z.subschemeι z ∈ closure ({η} : Set (projectiveLineProduct f)) :=
    himg ⟨z, hz, rfl⟩
  rw [hclosure] at hzmem
  obtain ⟨z', hz', hzz'⟩ := hzmem
  exact Z.subschemeι.isClosedEmbedding.injective hzz' ▸ hz'

omit [LocallyOfFiniteType f] in
/-- The relative dimension of `X ×_S 𝐏¹_S` over the base at a point of the zero section is the
relative dimension of `X` over the base at the corresponding point: the zero section is a closed
immersion and a section of the projection. -/
theorem relativeDimension_zeroSection (x : X) :
    relativeDimension C.dimensionFunction
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) (zeroSection f x) =
      relativeDimension C.dimensionFunction f x :=
  relativeDimension_apply_of_comp_fst C f _ (zeroSection_comp_fst f) x

omit [LocallyOfFiniteType f] in
/-- The relative dimension of `X ×_S 𝐏¹_S` over the base at a point of the infinity section is
the relative dimension of `X` over the base at the corresponding point. -/
theorem relativeDimension_infinitySection (x : X) :
    relativeDimension C.dimensionFunction
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) (infinitySection f x) =
      relativeDimension C.dimensionFunction f x :=
  relativeDimension_apply_of_comp_fst C f _ (infinitySection_comp_fst f) x

/-- A point of `Z` that strictly generalizes a point of the family of relative dimension `k` has
relative dimension exactly `k + 1`: the dimension function of Stacks 02JW drops strictly along a
proper specialization, and the hypothesis of Stacks Tag 02S5 caps the relative dimension of `Z`
at `k + 1`. -/
theorem relativeDimension_eq_succ_of_specializes
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    {ξ : projectiveLineProduct f}
    (hξ : relativeDimension C.dimensionFunction
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ = k)
    (w : Z.subscheme) (hspec : Z.subschemeι w ⤳ ξ) (hne : Z.subschemeι w ≠ ξ) :
    relativeDimension C.dimensionFunction (familyBase f Z) w = k + 1 := by
  have hlt := (deltaDimensionFunction C
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f)).strictAnti_specializes hspec hne
  rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply, hξ] at hlt
  have h1 : relativeDimension C.dimensionFunction (familyBase f Z) w =
      relativeDimension C.dimensionFunction
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) (Z.subschemeι w) :=
    relativeDimension_comp_closedImmersion C.dimensionFunction Z.subschemeι
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) w
  have h2 := hZ w
  omega

/-! ### The fibre coefficient of a closed subscheme as a colength -/

/-- A point `x` of relative dimension `k` whose image under `g` lies in the support of `W` and
whose fibre over it has delta-dimension at most `k` is the image of a generic point of an
irreducible component of the inverse image of `W` along `g`. -/
private theorem exists_genericPoints_comap_eq (g : X ⟶ projectiveLineProduct f)
    (W : (projectiveLineProduct f).IdealSheafData)
    (hW : schemeDeltaDimension C ((W.comap g).subschemeι ≫ f) ≤ (k : EInt)) {x : X}
    (hx : relativeDimension C.dimensionFunction f x = k)
    (hxW : g x ∈ (W.support : Set (projectiveLineProduct f))) :
    ∃ ζ : genericPoints (W.comap g).subscheme, (W.comap g).subschemeι ζ.1 = x := by
  have hxmem : x ∈ ((W.comap g).support : Set X) := by rwa [coe_support_comap]
  rw [← Scheme.IdealSheafData.range_subschemeι] at hxmem
  obtain ⟨y, hy⟩ := hxmem
  obtain ⟨ζ, hζ⟩ := exists_genericPoints_of_relativeDimension_eq C f
    (W.comap g).subschemeι k hW y (by rw [hy]; exact hx)
  exact ⟨ζ, by rw [hζ, hy]⟩

/-- The coefficient at `x` of the cycle of the inverse image of a closed subscheme `W` along a
closed immersion `g`, at a point `x` of relative dimension `k` whose image lies in the support of
`W`, is the colength, in the local ring at that image, of the kernel of the stalk map of `g`
together with the stalk of the ideal sheaf of `W`. -/
private theorem cycle_comap_apply_eq_length (g : X ⟶ projectiveLineProduct f)
    [IsClosedImmersion g] (W : (projectiveLineProduct f).IdealSheafData)
    (hW : schemeDeltaDimension C ((W.comap g).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hxW : g x ∈ (W.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (W.comap g).subschemeι k).1 x =
      ((Module.length ((projectiveLineProduct f).presheaf.stalk (g x))
        ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
          (RingHom.ker (g.stalkMap x).hom ⊔ IdealSheafData.stalk W (g x)))).toNat : ℤ) := by
  obtain ⟨ζ, rfl⟩ := exists_genericPoints_comap_eq C f k g W hW hx hxW
  exact cycleAssociatedToComap_apply_eq_length C f g W k ζ hx

/-- The coefficient at `x` of the cycle of the inverse image of `W` along `g` vanishes if `g x` is
not in the support of `W`. -/
private theorem cycle_comap_apply_eq_zero (g : X ⟶ projectiveLineProduct f)
    (W : (projectiveLineProduct f).IdealSheafData) {x : X}
    (hx : g x ∉ (W.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (W.comap g).subschemeι k).1 x = 0 := by
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f _ k ?_
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap]
  exact hx

/-- A nonzero coefficient at `x` of the cycle of the inverse image of `W` along `g` puts `g x` in
the support of `W`. -/
private theorem mem_support_of_cycle_comap_apply_ne_zero (g : X ⟶ projectiveLineProduct f)
    (W : (projectiveLineProduct f).IdealSheafData) {x : X}
    (hne : (cycleAssociatedToClosedSubscheme C f (W.comap g).subschemeι k).1 x ≠ 0) :
    g x ∈ (W.support : Set (projectiveLineProduct f)) :=
  not_not.mp fun h => hne (cycle_comap_apply_eq_zero C f k g W h)

/-- The coefficient at `x` of the cycle of the zero fibre of a closed subscheme `W` of
`X ×_S 𝐏¹_S`, at a point `x` of relative dimension `k` whose image under the zero section lies in
the support of `W`: it is the colength, in the local ring of `X ×_S 𝐏¹_S` at that image, of the
kernel of the stalk map of the zero section together with the stalk of the ideal sheaf of `W`.

The generic point that `Stacks.Chow.cycleAssociatedToComap_apply_eq_length` is indexed by is
supplied by Stacks Tag 02QT from the delta-dimension bound on the zero fibre of `W`. -/
theorem cycleAssociatedToZeroFiber_apply_eq_length
    (W : (projectiveLineProduct f).IdealSheafData)
    (hW : schemeDeltaDimension C ((zeroFiber f W).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hxW : zeroSection f x ∈ (W.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k).1 x =
      ((Module.length ((projectiveLineProduct f).presheaf.stalk (zeroSection f x))
        ((projectiveLineProduct f).presheaf.stalk (zeroSection f x) ⧸
          (RingHom.ker ((zeroSection f).stalkMap x).hom ⊔
            IdealSheafData.stalk W (zeroSection f x)))).toNat : ℤ) :=
  cycle_comap_apply_eq_length C f k _ W hW hx hxW

/-- The coefficient at `x` of the cycle of the infinity fibre of a closed subscheme `W` of
`X ×_S 𝐏¹_S`, as the colength of the kernel of the stalk map of the infinity section together
with the stalk of the ideal sheaf of `W`. -/
theorem cycleAssociatedToInfinityFiber_apply_eq_length
    (W : (projectiveLineProduct f).IdealSheafData)
    (hW : schemeDeltaDimension C ((infinityFiber f W).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hxW : infinitySection f x ∈ (W.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k).1 x =
      ((Module.length ((projectiveLineProduct f).presheaf.stalk (infinitySection f x))
        ((projectiveLineProduct f).presheaf.stalk (infinitySection f x) ⧸
          (RingHom.ker ((infinitySection f).stalkMap x).hom ⊔
            IdealSheafData.stalk W (infinitySection f x)))).toNat : ℤ) :=
  cycle_comap_apply_eq_length C f k _ W hW hx hxW

omit [LocallyOfFiniteType f] in
/-- The stalk at `ξ` of the ideal sheaf of the integral closed subscheme attached to the point of
`Y` corresponding to a prime `q` of the local ring at `ξ` is `q` itself. -/
theorem idealStalk_integralComponentAt_fromSpecStalk {Y : Scheme.{u}} (ξ : Y)
    (q : PrimeSpectrum (Y.presheaf.stalk ξ)) :
    IdealSheafData.stalk (integralComponentAt (Y.fromSpecStalk ξ q)) ξ = q.asIdeal :=
  idealStalk_vanishingIdeal_closure_fromSpecStalk ξ q

/-- The colength of the kernel of the stalk map of `g` together with a prime `q` over the stalk of
the ideal sheaf of `Z` is the coefficient at `x` of the cycle of the inverse image along `g` of
the integral closed subscheme corresponding to `q`. -/
private theorem length_quotient_ker_sup_eq_cycle_comap (g : X ⟶ projectiveLineProduct f)
    [IsClosedImmersion g] (h : schemeDeltaDimension C ((Z.comap g).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (g x)))
    (hq : IdealSheafData.stalk Z (g x) ≤ q.asIdeal) :
    ((Module.length ((projectiveLineProduct f).presheaf.stalk (g x))
        ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
          (RingHom.ker (g.stalkMap x).hom ⊔ q.asIdeal))).toNat : ℤ) =
      (cycleAssociatedToClosedSubscheme C f
        ((integralComponentAt ((projectiveLineProduct f).fromSpecStalk (g x) q)).comap g).subschemeι
          k).1 x := by
  have hηZ := (le_iff_fromSpecStalk_mem_support Z (g x) q).mp hq
  have hspec : (projectiveLineProduct f).fromSpecStalk (g x) q ⤳ g x := by
    have hr : (projectiveLineProduct f).fromSpecStalk (g x) q ∈
        Set.range ⇑((projectiveLineProduct f).fromSpecStalk (g x)) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  have hxV : g x ∈ ((integralComponentAt
      ((projectiveLineProduct f).fromSpecStalk (g x) q)).support :
        Set (projectiveLineProduct f)) := by
    rw [coe_support_integralComponentAt]
    exact hspec.mem_closure
  rw [cycle_comap_apply_eq_length C f k g _
    (schemeDeltaDimension_comap_integralComponentAt_le C f k Z g h hηZ) hx hxV,
    idealStalk_integralComponentAt_fromSpecStalk]

/-- **The first factor of the local identity of Stacks Tag 02S5 is a fibre coefficient of a
component.** For a prime `q` of the local ring at the point `ξ = (x, 0)` containing the stalk of
the ideal sheaf of `Z`, the colength of the kernel of the stalk map of the zero section together
with `q` is the coefficient at `x` of the cycle of the zero fibre of the integral closed
subscheme supported on the closure of the point of `X ×_S 𝐏¹_S` corresponding to `q`.

That subscheme has `q` as the stalk of its ideal sheaf at `ξ`, by
`Stacks.Chow.idealStalk_integralComponentAt_fromSpecStalk`, and it inherits the
delta-dimension bound of Tag 02S5 on the zero fibre of `Z` because its support lies in the
support of `Z`. -/
theorem length_quotient_ker_sup_eq_cycleAssociatedToZeroFiber
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (zeroSection f x)))
    (hq : IdealSheafData.stalk Z (zeroSection f x) ≤ q.asIdeal) :
    ((Module.length ((projectiveLineProduct f).presheaf.stalk (zeroSection f x))
        ((projectiveLineProduct f).presheaf.stalk (zeroSection f x) ⧸
          (RingHom.ker ((zeroSection f).stalkMap x).hom ⊔ q.asIdeal))).toNat : ℤ) =
      (cycleAssociatedToClosedSubscheme C f
        (zeroFiber f (integralComponentAt
          ((projectiveLineProduct f).fromSpecStalk (zeroSection f x) q))).subschemeι k).1 x :=
  length_quotient_ker_sup_eq_cycle_comap C f k Z _ h₀ hx q hq

/-- The infinity-section twin: the colength of the kernel of the stalk map of the infinity
section together with a prime `q` over the stalk of the ideal sheaf of `Z` is the coefficient at
`x` of the cycle of the infinity fibre of the component corresponding to `q`. -/
theorem length_quotient_ker_sup_eq_cycleAssociatedToInfinityFiber
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (infinitySection f x)))
    (hq : IdealSheafData.stalk Z (infinitySection f x) ≤ q.asIdeal) :
    ((Module.length ((projectiveLineProduct f).presheaf.stalk (infinitySection f x))
        ((projectiveLineProduct f).presheaf.stalk (infinitySection f x) ⧸
          (RingHom.ker ((infinitySection f).stalkMap x).hom ⊔ q.asIdeal))).toNat : ℤ) =
      (cycleAssociatedToClosedSubscheme C f
        (infinityFiber f (integralComponentAt
          ((projectiveLineProduct f).fromSpecStalk (infinitySection f x) q))).subschemeι
            k).1 x :=
  length_quotient_ker_sup_eq_cycle_comap C f k Z _ hInf hx q hq

/-! ### The fibre coefficient of `Z` as an integer sum over the minimal primes -/

/-- The local content of Stacks Tag 02S5 along a section `g` of the projection, in integers: the
common proof of the zero- and infinity-section statements below. -/
private theorem cycle_comap_apply_eq_finsum_minimalPrimes (g : X ⟶ projectiveLineProduct f)
    [IsClosedImmersion g] (hg : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) = 𝟙 X)
    (hspan : ∀ y : X, ∃ t : (projectiveLineProduct f).presheaf.stalk (g y),
      RingHom.ker (g.stalkMap y).hom = Ideal.span {t})
    (hex : ∀ y : (Z.comap g).subscheme,
      ∃ w : Z.subscheme, Z.subschemeι w = g ((Z.comap g).subschemeι y))
    (hsec : ∀ y : X, g y ∈ Set.range (zeroSection f) ∨ g y ∈ Set.range (infinitySection f))
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h : schemeDeltaDimension C ((Z.comap g).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hxZ : g x ∈ (Z.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (Z.comap g).subschemeι k).1 x =
      ∑ᶠ q ∈ {q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (g x)) |
          q.asIdeal ∈ (IdealSheafData.stalk Z (g x)).minimalPrimes},
        ((Module.length ((projectiveLineProduct f).presheaf.stalk (g x))
            ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
              (RingHom.ker (g.stalkMap x).hom ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
                IdealSheafData.stalk Z (g x)))).toNat : ℤ) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian (projectiveLineProduct f) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S))
  obtain ⟨ζ, rfl⟩ := exists_genericPoints_comap_eq C f k g Z h hx hxZ
  obtain ⟨w, hw⟩ := hex ζ.1
  have hrange := hsec ((Z.comap g).subschemeι ζ.1)
  rw [← hw] at hrange
  have hwdim : relativeDimension C.dimensionFunction (familyBase f Z) w = k :=
    (relativeDimension_familyBase_eq_of_comp_fst C f Z g hg w _ hw).trans hx
  have hass : w ∉ Stacks.Divisors.schemeAssociatedPoints Z.subscheme :=
    notMem_schemeAssociatedPoints_of_relativeDimension_eq C f Z k w hrange hwdim (hAssociated w)
  have hI := notMem_associatedPrimes_idealStalk_of_notMem_schemeAssociatedPoints Z w hass
  rw [hw] at hI
  have hdim := ringKrullDim_quotient_idealStalk_eq_one C f Z k hZ hwdim hrange (hAssociated w)
  rw [hw] at hdim
  have hJI : ringKrullDim ((projectiveLineProduct f).presheaf.stalk
        (g ((Z.comap g).subschemeι ζ.1)) ⧸
      (RingHom.ker (g.stalkMap ((Z.comap g).subschemeι ζ.1)).hom ⊔
        IdealSheafData.stalk Z (g ((Z.comap g).subschemeι ζ.1)))) =
      ringKrullDim ((Z.comap g).subscheme.presheaf.stalk ζ.1) :=
    (ringKrullDim_quotient_stalk_comap_eq g Z ((Z.comap g).subschemeι ζ.1)).trans
      (ringKrullDim_quotient_idealStalk_eq (Z.comap g) ζ.1)
  rw [ringKrullDim_stalk_eq_zero_of_mem_genericPoints ζ] at hJI
  rw [cycleAssociatedToComap_apply_eq_length C f g Z k ζ hx,
    length_quotient_sup_eq_sum_minimalPrimes_of_isPrincipal _ _ (hspan _) hI hdim hJI.le]
  exact toNat_finsum_minimalPrimes _ _ hJI.le

/-- **The local content of Stacks Tag 02S5 at the zero section, in integers.** At a point `x` of
`X` of relative dimension `k` whose image `ξ` under the zero section lies in the support of `Z`,
the coefficient of `[Z₀]_k` is the sum, over the minimal primes `q` of the stalk `I` of the ideal
sheaf of `Z` at `ξ`, of the colength of the kernel of the stalk map of the zero section together
with `q`, times the length of `A ⧸ I` localized at `q`.

This is `Stacks.Chow.exists_localEquation_cycleAssociatedToZeroFiber_apply_eq_sum_minimalPrimes`
with the local equation replaced by the canonical ideal it generates — the kernel of the stalk
map, which is what the fibre coefficient of a component is computed from — and with `ENat.toNat`
distributed over the sum, which is legitimate because the minimal primes are finite in number and
every summand is finite. -/
theorem cycleAssociatedToZeroFiber_apply_eq_finsum_minimalPrimes
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hxZ : zeroSection f x ∈ (Z.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1 x =
      ∑ᶠ q ∈ {q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (zeroSection f x)) |
          q.asIdeal ∈ (IdealSheafData.stalk Z (zeroSection f x)).minimalPrimes},
        ((Module.length ((projectiveLineProduct f).presheaf.stalk (zeroSection f x))
            ((projectiveLineProduct f).presheaf.stalk (zeroSection f x) ⧸
              (RingHom.ker ((zeroSection f).stalkMap x).hom ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              ((projectiveLineProduct f).presheaf.stalk (zeroSection f x) ⧸
                IdealSheafData.stalk Z (zeroSection f x)))).toNat : ℤ) :=
  cycle_comap_apply_eq_finsum_minimalPrimes C f k Z _ (zeroSection_comp_fst f)
    (exists_span_eq_ker_stalkMap_zeroSection f) (exists_subschemeι_eq_zeroSection f Z)
    (fun _ => Or.inl ⟨_, rfl⟩) hZ h₀ hAssociated hx hxZ

/-- **The local content of Stacks Tag 02S5 at the infinity section, in integers.** The
infinity-section twin of
`Stacks.Chow.cycleAssociatedToZeroFiber_apply_eq_finsum_minimalPrimes`. -/
theorem cycleAssociatedToInfinityFiber_apply_eq_finsum_minimalPrimes
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hxZ : infinitySection f x ∈ (Z.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1 x =
      ∑ᶠ q ∈ {q : PrimeSpectrum
            ((projectiveLineProduct f).presheaf.stalk (infinitySection f x)) |
          q.asIdeal ∈ (IdealSheafData.stalk Z (infinitySection f x)).minimalPrimes},
        ((Module.length ((projectiveLineProduct f).presheaf.stalk (infinitySection f x))
            ((projectiveLineProduct f).presheaf.stalk (infinitySection f x) ⧸
              (RingHom.ker ((infinitySection f).stalkMap x).hom ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              ((projectiveLineProduct f).presheaf.stalk (infinitySection f x) ⧸
                IdealSheafData.stalk Z (infinitySection f x)))).toNat : ℤ) :=
  cycle_comap_apply_eq_finsum_minimalPrimes C f k Z _ (infinitySection_comp_fst f)
    (exists_span_eq_ker_stalkMap_infinitySection f) (exists_subschemeι_eq_infinitySection f Z)
    (fun _ => Or.inr ⟨_, rfl⟩) hZ hInf hAssociated hx hxZ

/-! ### The multiplicity of a component, read in the local ring at a specialization -/

omit [LocallyOfFiniteType f] in
/-- The length, over the localization at a prime `q` containing the stalk of the ideal sheaf of
`W` at `ξ`, of the localization there of `𝒪_{Y,ξ} ⧸ I` is the colength of the stalk of the ideal
sheaf of `W` at the point of `Y` corresponding to `q` — that is, the multiplicity of the
component of `W` through that point.

`Stacks.Chow.length_localizedModule_quotient_idealStalk_eq_length_stalk` identifies the left-hand
side with the length of the local ring of the subscheme there, and
`Stacks.Blowup.Colength.length_idealStalk_quotient_eq_subschemeStalk` identifies that with the
colength of the stalk of the ideal sheaf. -/
theorem length_localizedModule_quotient_idealStalk_eq_length_quotient_idealStalk
    {Y : Scheme.{u}} (W : Y.IdealSheafData) (ξ : Y) (q : PrimeSpectrum (Y.presheaf.stalk ξ))
    (hq : IdealSheafData.stalk W ξ ≤ q.asIdeal) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl
          (Y.presheaf.stalk ξ ⧸ IdealSheafData.stalk W ξ)) =
      Module.length (Y.presheaf.stalk (Y.fromSpecStalk ξ q))
        (Y.presheaf.stalk (Y.fromSpecStalk ξ q) ⧸
          IdealSheafData.stalk W (Y.fromSpecStalk ξ q)) := by
  obtain ⟨y, hy⟩ := exists_subschemeι_eq_fromSpecStalk W ξ q hq
  rw [length_localizedModule_quotient_idealStalk_eq_length_stalk W q y hy.symm, ← hy]
  exact (Stacks.Blowup.Colength.length_idealStalk_quotient_eq_subschemeStalk W y).symm

omit [LocallyOfFiniteType f] in
/-- The multiplicity of an irreducible component of `Z`, read as the colength of the stalk of the
ideal sheaf of `Z` at its generic point. -/
theorem componentMultiplicity_eq_toNat_length_quotient_idealStalk
    (η : genericPoints Z.subscheme) :
    componentMultiplicity Z.subschemeι η =
      ((Module.length ((projectiveLineProduct f).presheaf.stalk (Z.subschemeι η.1))
        ((projectiveLineProduct f).presheaf.stalk (Z.subschemeι η.1) ⧸
          IdealSheafData.stalk Z (Z.subschemeι η.1))).toNat : ℤ) := by
  rw [componentMultiplicity_eq_length_stalk,
    Stacks.Blowup.Colength.length_idealStalk_quotient_eq_subschemeStalk Z η.1]

/-! ### The components of `Z` through a point of a distinguished section have dimension `k + 1` -/

/-- A component generic point of `Z` through a point `g x` of a section `g` of the projection,
with `x` of relative dimension `k`, has relative dimension `k + 1` over the base. -/
private theorem relativeDimension_of_mem_componentGenericPointsThrough_comp_fst
    (g : X ⟶ projectiveLineProduct f) [IsClosedImmersion g]
    (hg : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) = 𝟙 X)
    (hsec : ∀ y : X, g y ∈ Set.range (zeroSection f) ∨ g y ∈ Set.range (infinitySection f))
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    {η : projectiveLineProduct f} (hη : η ∈ componentGenericPointsThrough Z (g x))
    (w : genericPoints Z.subscheme) (hw : Z.subschemeι w.1 = η) :
    relativeDimension C.dimensionFunction (familyBase f Z) w.1 = k + 1 := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (familyBase f Z)
  have hne : Z.subschemeι w.1 ≠ g x := by
    intro heq
    have hmem : w.1 ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme :=
      mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent Z.subscheme w.2
        isGenericPoint_closure
    exact notMem_schemeAssociatedPoints_of_relativeDimension_eq C f Z k w.1
      (by rw [heq]; exact hsec x)
      ((relativeDimension_familyBase_eq_of_comp_fst C f Z g hg w.1 x heq).trans hx)
      (hAssociated w.1) hmem
  exact relativeDimension_eq_succ_of_specializes C f k Z hZ
    ((relativeDimension_apply_of_comp_fst C f g hg x).trans hx) w.1 (by rw [hw]; exact hη.2.1) hne

/-- A component generic point of `Z` through a point `(x, 0)` of the zero section with `x` of
relative dimension `k` has relative dimension `k + 1` over the base.

It cannot be the point of the section itself: that point would then be the generic point of an
irreducible component of `Z`, hence an associated point of `Z` of relative dimension exactly `k`
lying on a distinguished section, which the hypothesis of Stacks Tag 02S5 on associated points
forbids. So it is a proper generalization, and the dimension function drops strictly. -/
theorem relativeDimension_of_mem_componentGenericPointsThrough_zeroSection
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    {η : projectiveLineProduct f}
    (hη : η ∈ componentGenericPointsThrough Z (zeroSection f x))
    (w : genericPoints Z.subscheme) (hw : Z.subschemeι w.1 = η) :
    relativeDimension C.dimensionFunction (familyBase f Z) w.1 = k + 1 :=
  relativeDimension_of_mem_componentGenericPointsThrough_comp_fst C f k Z _
    (zeroSection_comp_fst f) (fun _ => Or.inl ⟨_, rfl⟩) hZ hAssociated hx hη w hw

/-- The infinity-section twin of
`Stacks.Chow.relativeDimension_of_mem_componentGenericPointsThrough_zeroSection`. -/
theorem relativeDimension_of_mem_componentGenericPointsThrough_infinitySection
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    {η : projectiveLineProduct f}
    (hη : η ∈ componentGenericPointsThrough Z (infinitySection f x))
    (w : genericPoints Z.subscheme) (hw : Z.subschemeι w.1 = η) :
    relativeDimension C.dimensionFunction (familyBase f Z) w.1 = k + 1 :=
  relativeDimension_of_mem_componentGenericPointsThrough_comp_fst C f k Z _
    (infinitySection_comp_fst f) (fun _ => Or.inr ⟨_, rfl⟩) hZ hAssociated hx hη w hw

/-! ### The decomposition of the fibre coefficients -/

/-- The summand of the decomposition of the coefficient along a section `g`, as a function of the
point of `X ×_S 𝐏¹_S` indexing a component of `Z`: the multiplicity of that component in
`[Z]_{k+1}`, read as the colength of the stalk of the ideal sheaf of `Z` at the point, times the
coefficient at `x` of the cycle of the inverse image along `g` of that component.

Both reindexings of the local identity — along the minimal primes and along the generic points of
the components — land on this one function, which is why it is written as a function of a point of
the family rather than of either index. -/
private def componentSummand (g : X ⟶ projectiveLineProduct f) (x : X)
    (p : projectiveLineProduct f) : ℤ :=
  ((Module.length ((projectiveLineProduct f).presheaf.stalk p)
      ((projectiveLineProduct f).presheaf.stalk p ⧸ IdealSheafData.stalk Z p)).toNat : ℤ) *
    (cycleAssociatedToClosedSubscheme C f
      ((integralComponentAt p).comap g).subschemeι k).1 x

/-- The claim in the proof of Stacks Tag 02S5 along a section `g` of the projection: the common
proof of the zero- and infinity-section statements below. -/
private theorem cycle_comap_apply_eq_finsum_componentFamily (g : X ⟶ projectiveLineProduct f)
    [IsClosedImmersion g] (hg : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) = 𝟙 X)
    (hspan : ∀ y : X, ∃ t : (projectiveLineProduct f).presheaf.stalk (g y),
      RingHom.ker (g.stalkMap y).hom = Ideal.span {t})
    (hex : ∀ y : (Z.comap g).subscheme,
      ∃ w : Z.subscheme, Z.subschemeι w = g ((Z.comap g).subschemeι y))
    (hsec : ∀ y : X, g y ∈ Set.range (zeroSection f) ∨ g y ∈ Set.range (infinitySection f))
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h : schemeDeltaDimension C ((Z.comap g).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k) :
    (cycleAssociatedToClosedSubscheme C f (Z.comap g).subschemeι k).1 x =
      ∑ᶠ j : componentIndex C f k Z,
        (cycleAssociatedToClosedSubscheme C f
          ((componentFamily C f k Z j).comap g).subschemeι k).1 x := by
  classical
  have hmemZ : ∀ η : componentPoints C f k Z,
      Z.subschemeι η.1.1 ∈ (Z.support : Set (projectiveLineProduct f)) := by
    intro η
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨η.1.1, rfl⟩
  have hV : ∀ η : componentPoints C f k Z,
      (cycleAssociatedToClosedSubscheme C f
        ((integralComponentAt (Z.subschemeι η.1.1)).comap g).subschemeι k).1 x ≠ 0 →
      g x ∈ (closure {Z.subschemeι η.1.1} : Set (projectiveLineProduct f)) := fun η hne => by
    have h2 := mem_support_of_cycle_comap_apply_ne_zero C f k g _ hne
    rwa [coe_support_integralComponentAt] at h2
  by_cases hxZ : g x ∈ (Z.support : Set (projectiveLineProduct f))
  · have hcc : (Function.support fun η : componentPoints C f k Z =>
        ((componentMultiplicity Z.subschemeι η.1).toNat : ℤ) *
          (cycleAssociatedToClosedSubscheme C f
            ((integralComponentAt (Z.subschemeι η.1.1)).comap g).subschemeι k).1 x).Finite :=
      ((locallyFinite_closure_componentPoints C f k Z).point_finite (g x)).subset
        fun η hη => hV η (right_ne_zero_of_mul hη)
    have hmul : ∀ η : componentPoints C f k Z,
        ((componentMultiplicity Z.subschemeι η.1).toNat : ℤ) *
          (cycleAssociatedToClosedSubscheme C f
            ((integralComponentAt (Z.subschemeι η.1.1)).comap g).subschemeι k).1 x =
        componentSummand C f k Z g x (Z.subschemeι η.1.1) := by
      intro η
      rw [componentSummand,
        componentMultiplicity_eq_toNat_length_quotient_idealStalk C f Z η.1, Int.toNat_natCast]
    have hsigma : (∑ᶠ j : componentIndex C f k Z,
          (cycleAssociatedToClosedSubscheme C f
            ((componentFamily C f k Z j).comap g).subschemeι k).1 x) =
        ∑ᶠ η : componentPoints C f k Z, componentSummand C f k Z g x (Z.subschemeι η.1.1) :=
      (finsum_sigma_fin_eq_finsum_mul _ hcc).trans (finsum_congr hmul)
    have hGsupp : ∀ η ∈ Function.support fun η : componentPoints C f k Z =>
        componentSummand C f k Z g x (Z.subschemeι η.1.1),
        Z.subschemeι η.1.1 ∈ componentGenericPointsThrough Z (g x) := by
      intro η hη
      refine mem_componentGenericPointsThrough_subschemeι C f Z η.1
        (specializes_iff_mem_closure.mpr (hV η ?_))
      have hη' : componentSummand C f k Z g x (Z.subschemeι η.1.1) ≠ 0 := hη
      rw [← hmul η] at hη'
      exact right_ne_zero_of_mul hη'
    have hstep₀ : (∑ᶠ η : componentPoints C f k Z,
          componentSummand C f k Z g x (Z.subschemeι η.1.1)) =
        ∑ᶠ η ∈ {η : componentPoints C f k Z |
            Z.subschemeι η.1.1 ∈ componentGenericPointsThrough Z (g x)},
          componentSummand C f k Z g x (Z.subschemeι η.1.1) := by
      rw [← finsum_mem_univ fun η : componentPoints C f k Z =>
        componentSummand C f k Z g x (Z.subschemeι η.1.1)]
      exact finsum_mem_inter_support_eq' _ Set.univ _
        fun η hη => ⟨fun _ => hGsupp η hη, fun _ => trivial⟩
    have hbij₂ : Set.BijOn (fun η : componentPoints C f k Z => Z.subschemeι η.1.1)
        {η : componentPoints C f k Z |
          Z.subschemeι η.1.1 ∈ componentGenericPointsThrough Z (g x)}
        (componentGenericPointsThrough Z (g x)) := by
      refine ⟨fun η hη => hη, fun a _ b _ hab =>
        Subtype.ext (Subtype.ext (Z.subschemeι.isClosedEmbedding.injective hab)), fun p hp => ?_⟩
      obtain ⟨w, hw⟩ :=
        exists_genericPoints_subschemeι_eq_of_mem_componentGenericPointsThrough C f Z hp
      refine ⟨⟨w, relativeDimension_of_mem_componentGenericPointsThrough_comp_fst C f k Z g hg
        hsec hZ hAssociated hx hp w hw⟩, ?_, hw⟩
      change Z.subschemeι w.1 ∈ componentGenericPointsThrough Z (g x)
      rw [hw]
      exact hp
    have hstep₂ : (∑ᶠ η ∈ {η : componentPoints C f k Z |
          Z.subschemeι η.1.1 ∈ componentGenericPointsThrough Z (g x)},
          componentSummand C f k Z g x (Z.subschemeι η.1.1)) =
        ∑ᶠ p ∈ componentGenericPointsThrough Z (g x), componentSummand C f k Z g x p :=
      finsum_mem_eq_of_bijOn (fun η : componentPoints C f k Z => Z.subschemeι η.1.1) hbij₂
        fun η _ => rfl
    have hval₁ : ∀ q ∈ {q : PrimeSpectrum
          ((projectiveLineProduct f).presheaf.stalk (g x)) |
          q.asIdeal ∈ (IdealSheafData.stalk Z (g x)).minimalPrimes},
        ((Module.length ((projectiveLineProduct f).presheaf.stalk (g x))
            ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
              (RingHom.ker (g.stalkMap x).hom ⊔ q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
                IdealSheafData.stalk Z (g x)))).toNat : ℤ) =
        componentSummand C f k Z g x ((projectiveLineProduct f).fromSpecStalk (g x) q) := by
      intro q hq
      have hq' : IdealSheafData.stalk Z (g x) ≤ q.asIdeal := hq.1.2
      rw [componentSummand, length_quotient_ker_sup_eq_cycle_comap C f k Z g h hx q hq',
        length_localizedModule_quotient_idealStalk_eq_length_quotient_idealStalk Z (g x) q hq']
      exact mul_comm _ _
    have hstep₁ := finsum_mem_eq_of_bijOn ⇑((projectiveLineProduct f).fromSpecStalk (g x))
      (bijOn_fromSpecStalk_minimalPrimes Z (g x)) hval₁
    rw [cycle_comap_apply_eq_finsum_minimalPrimes C f k Z g hg hspan hex hsec hZ h hAssociated hx
      hxZ]
    exact hstep₁.trans (hstep₂.symm.trans (hstep₀.symm.trans hsigma.symm))
  · rw [cycle_comap_apply_eq_zero C f k g Z hxZ]
    exact ((finsum_congr fun j => cycle_comap_apply_eq_zero C f k g _ fun hj =>
      hxZ (coe_support_integralComponentAt_subset C f Z (hmemZ j.1) hj)).trans
        (finsum_zero (M := ℤ) (α := componentIndex C f k Z))).symm

/-- **The claim in the proof of Stacks Tag 02S5, at the zero section.** At every point `x` of `X`
of relative dimension `k` the coefficient of `[Z₀]_k` is the sum, over the family of components of
`Z`, of the coefficients of the cycles of their zero fibres.

If `(x, 0)` lies outside the support of `Z` then every term vanishes, the support of a member of
the family being contained in that of `Z`. Otherwise the coefficient of `[Z₀]_k` is the sum over
the minimal primes of the stalk of the ideal sheaf of `Z` at `(x, 0)`, and that sum is reindexed
by the components of `Z` through `(x, 0)` along
`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes`: each summand's first factor is the zero-fibre
coefficient of the corresponding component and its second factor is that component's
multiplicity, which the `Fin n` fibres of the index type turn into that many copies of the
first. -/
theorem cycleAssociatedToZeroFiber_apply_eq_finsum_componentFamily
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k) :
    (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1 x =
      ∑ᶠ j : componentIndex C f k Z,
        (cycleAssociatedToClosedSubscheme C f
          (zeroFiber f (componentFamily C f k Z j)).subschemeι k).1 x :=
  cycle_comap_apply_eq_finsum_componentFamily C f k Z _ (zeroSection_comp_fst f)
    (exists_span_eq_ker_stalkMap_zeroSection f) (exists_subschemeι_eq_zeroSection f Z)
    (fun _ => Or.inl ⟨_, rfl⟩) hZ h₀ hAssociated hx

/-- **The claim in the proof of Stacks Tag 02S5, at the infinity section.** The infinity-section
twin of `Stacks.Chow.cycleAssociatedToZeroFiber_apply_eq_finsum_componentFamily`: at every point
`x` of `X` of relative dimension `k` the coefficient of `[Z_∞]_k` is the sum, over the family of
components of `Z`, of the coefficients of the cycles of their infinity fibres. -/
theorem cycleAssociatedToInfinityFiber_apply_eq_finsum_componentFamily
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k) :
    (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1 x =
      ∑ᶠ j : componentIndex C f k Z,
        (cycleAssociatedToClosedSubscheme C f
          (infinityFiber f (componentFamily C f k Z j)).subschemeι k).1 x :=
  cycle_comap_apply_eq_finsum_componentFamily C f k Z _ (infinitySection_comp_fst f)
    (exists_span_eq_ker_stalkMap_infinitySection f) (exists_subschemeι_eq_infinitySection f Z)
    (fun _ => Or.inr ⟨_, rfl⟩) hZ hInf hAssociated hx

/-! ### The decomposition rule -/

/-- At every point of `X` the coefficients of the inverse images along `g` of the family of
components have finite support: a nonzero coefficient puts `g x` in the support of that member,
and the family is locally finite. -/
private theorem hasFiniteSupport_cycle_comap_componentFamily (g : X ⟶ projectiveLineProduct f)
    (x : X) :
    Function.HasFiniteSupport fun j : componentIndex C f k Z =>
      (cycleAssociatedToClosedSubscheme C f
        ((componentFamily C f k Z j).comap g).subschemeι k).1 x :=
  ((locallyFinite_support_componentFamily C f k Z).point_finite (g x)).subset fun _ hj =>
    mem_support_of_cycle_comap_apply_ne_zero C f k g _ hj

/-- At every point of `X` the zero-fibre coefficients of the family of components have finite
support: a nonzero coefficient puts the corresponding point of the zero section in the support of
that member, and the family is locally finite. -/
theorem hasFiniteSupport_cycleAssociatedToZeroFiber_componentFamily (x : X) :
    Function.HasFiniteSupport fun j : componentIndex C f k Z =>
      (cycleAssociatedToClosedSubscheme C f
        (zeroFiber f (componentFamily C f k Z j)).subschemeι k).1 x :=
  hasFiniteSupport_cycle_comap_componentFamily C f k Z _ x

/-- At every point of `X` the infinity-fibre coefficients of the family of components have finite
support. -/
theorem hasFiniteSupport_cycleAssociatedToInfinityFiber_componentFamily (x : X) :
    Function.HasFiniteSupport fun j : componentIndex C f k Z =>
      (cycleAssociatedToClosedSubscheme C f
        (infinityFiber f (componentFamily C f k Z j)).subschemeι k).1 x :=
  hasFiniteSupport_cycle_comap_componentFamily C f k Z _ x

/-- **The claim in the proof of Stacks Tag 02S5.** For every closed subscheme `Z ⊆ X ×_S 𝐏¹_S`
satisfying the four hypotheses of the tag, the fibre cycles of `Z` decompose over the family of
its irreducible components of relative dimension `k + 1`, each repeated as often as its
multiplicity in `[Z]_{k+1}`.

This is `Stacks.Chow.FibreCycleComponentDecompositionRule`, the first of the two inputs the proof
of Tag 02S5 needs; the other is Tag 02S4 part (2), whose one-member form is
`Stacks.Chow.FibreCyclesRationallyEquivalentWithin`. -/
theorem fibreCycleComponentDecompositionRule :
    FibreCycleComponentDecompositionRule C f k := by
  intro Z hZ h₀ hInf hAssociated
  refine fibreCycleComponentDecomposition_of_apply_of_relativeDimension_eq C f k Z
    (componentFamily C f k Z) (isIntegral_componentFamily C f k Z)
    (relativeDimension_componentFamily C f k Z)
    (not_range_componentFamily_subset_range_zeroSection C f k Z h₀)
    (not_range_componentFamily_subset_range_infinitySection C f k Z hInf)
    (locallyFinite_support_componentFamily C f k Z) fun x hx => ?_
  rw [cycleAssociatedToZeroFiber_apply_eq_finsum_componentFamily C f k Z hZ h₀ hAssociated hx,
    cycleAssociatedToInfinityFiber_apply_eq_finsum_componentFamily C f k Z hZ hInf hAssociated hx,
    familyFibreDifferenceCoefficient]
  exact (finsum_sub_distrib
    (hasFiniteSupport_cycleAssociatedToZeroFiber_componentFamily C f k Z x)
    (hasFiniteSupport_cycleAssociatedToInfinityFiber_componentFamily C f k Z x)).symm

/-- **Stacks Tag 02S5 from the one-member case of Tag 02S4 part (2) alone.** The decomposition
rule is no longer an assumption: for a closed subscheme of `X ×_S 𝐏¹_S` whose relative dimension
is at most `k + 1`, whose two fibres have delta-dimension at most `k`, and each of whose
associated points either misses both distinguished sections or has relative dimension below `k`,
the cycles of the two fibres are rationally equivalent as soon as the difference of the two fibre
cycles of a *single* integral closed subscheme of relative dimension `k + 1` meeting neither
section in its whole range is rationally equivalent to zero within its carrier. -/
theorem cycleAssociatedToFibres_rationallyEquivalent_of_within
    (Z : (projectiveLineProduct f).IdealSheafData)
    (hZ : ∀ ζ : Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k))
    (hwithin : FibreCyclesRationallyEquivalentWithin C f k) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k) :=
  cycleAssociatedToFibres_rationallyEquivalent_of_within_of_decompositionRule C f k Z hZ h₀ hInf
    hAssociated hwithin (fibreCycleComponentDecompositionRule C f k)

/-! ### The family of components is not vacuous -/

omit [LocallyOfFiniteType f] in
/-- **The family of components is not empty at the intended instance.** For an integral `Z` of
relative dimension `k + 1` the index type has an element: the generic point of `Z`, whose
multiplicity is one.

This is what makes `Stacks.Chow.componentIndex` and the statements about
`Stacks.Chow.componentFamily` non-vacuous; a component of multiplicity zero indexes an empty
`Fin 0` and drops out of the family, which is right, since it does not occur in `[Z]_{k+1}`. -/
theorem nonempty_componentIndex_of_isIntegral (hZ : IsIntegral Z.subscheme)
    (hdim : ∀ ξ : genericPoints Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ξ.1 = k + 1) :
    Nonempty (componentIndex C f k Z) := by
  have hg := genericPoint_mem_genericPoints Z.subscheme
  refine ⟨⟨⟨⟨genericPoint Z.subscheme, hg⟩, hdim _⟩, ⟨0, ?_⟩⟩⟩
  rw [componentMultiplicity_eq_one Z.subschemeι hg]
  decide

omit [LocallyOfFiniteType f] in
/-- **The family of components of an integral `Z` is `Z` itself.** Every member of the family is
`Z`, so the decomposition recovers the one-member family of
`Stacks.Chow.fibreCycleComponentDecomposition_of_isIntegral` in that case. -/
theorem componentFamily_eq_of_isIntegral (hZ : IsIntegral Z.subscheme)
    (j : componentIndex C f k Z) : componentFamily C f k Z j = Z := by
  rw [componentFamily]
  have h : Z.subschemeι j.1.1.1 = genericPointOf Z hZ := by
    rw [show j.1.1.1 = genericPoint Z.subscheme by
      simpa [genericPoints_eq_singleton] using j.1.1.2]
    rfl
  rw [h]
  exact integralComponentAt_genericPointOf Z hZ

end Stacks.Chow

end

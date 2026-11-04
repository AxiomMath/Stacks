module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhComparison

/-!
# ph coverings and V coverings of locally finitely presented families

Stacks 0ETR states that a family of morphisms of schemes which are locally of finite
presentation is a ph covering if and only if it is a V covering. The implication from ph to V
is `AlgebraicGeometry.isVCovering_of_isPHCovering`, proved in
`StacksFrontier.AlgebraicGeometry.Topologies.V.PhComparison`; it needs no finiteness hypothesis.

This file carries out the two reduction steps of the converse implication which are
independent of the flattening machinery, and isolates what is left as a single hypothesis.

The first step is the one the Stacks proof performs after reducing to an affine base: a family
refined by a standard V covering is already refined by a standard V covering whose members are
*affine opens of the members of the family*. This is
`AlgebraicGeometry.exists_isStandardVCovering_affineOpen_refinement`, and it is proved by
covering the (quasi-compact) source of each member of the refining covering by finitely many
affine opens of the member of the original family it factors through; the lifting property is
inherited because the spectrum of a valuation ring is a local scheme, so a morphism out of it
lands in any open containing the image of its closed point.

The second step assembles the affine-local definitions: granted that every *standard* V
covering of an affine scheme by finitely presented affine schemes is refined by a standard ph
covering — the predicate `AlgebraicGeometry.StandardVCoveringHasPHRefinement` — every V
covering by morphisms locally of finite presentation is a ph covering, and hence the two
notions agree.

## Main definitions

* `AlgebraicGeometry.StandardVCoveringHasPHRefinement` is the statement that a standard V
  covering of an affine scheme whose members are locally of finite presentation is refined by
  a standard ph covering.

## Main results

* `AlgebraicGeometry.exists_isStandardVCovering_affineOpen_refinement`: a family of morphisms
  to an affine scheme which is refined by a standard V covering is refined by a standard V
  covering whose members are affine opens of the members of the family.
* `AlgebraicGeometry.isPHCovering_of_isVCovering`: granted
  `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, a V covering by morphisms locally of
  finite presentation is a ph covering.
* `AlgebraicGeometry.isPHCovering_iff_isVCovering`: granted the same, the two covering
  conditions agree for families of morphisms locally of finite presentation.

## Implementation notes

`AlgebraicGeometry.IsStandardVCovering` takes the finiteness of the index type and the
affineness of the members as instance arguments, so the existential statements below carry
them as explicit components and apply the predicate with `@`. Both are `Prop`-valued classes,
so the choice of component is irrelevant up to definitional proof irrelevance.

`AlgebraicGeometry.StandardVCoveringHasPHRefinement` is *not* proved here. The Stacks argument
for it chooses a generic flatness stratification of the base (Stacks 0H3Z), flattens the family
by an admissible blowup (Stacks 0815) which may be taken to have scheme-theoretically dense
centre (Stacks 080Y), lifts points of the blowup along valuation rings (Stacks 02JQ) to see
that the flattened family is an fppf covering, and concludes with the fact that an fppf
covering is a ph covering (Stacks 0DBT).

Of those five inputs, four are available and one -- Stacks 0815 -- is not.

* 02JQ is available: it is `AlgebraicGeometry.exists_valuationRing_of_image_point`
  (`StacksFrontier/AlgebraicGeometry/Morphisms/Closure/ImageValuativeDiagram.lean:214`) together
  with `AlgebraicGeometry.exists_specializes_of_image_point` (same module, `:234`).
* 0DBT is available with no hypothesis at all, as
  `AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage` in
  `StacksFrontier/AlgebraicGeometry/Topologies/V/FppfAffineDomination.lean:179`: the weak form of
  Stacks 0CP0 that `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage`
  (`StacksFrontier/AlgebraicGeometry/Topologies/V/FppfPhComparison.lean:88`) still carries as the
  hypothesis `AlgebraicGeometry.FppfHasFiniteDomination` is only ever needed over an affine
  base, and there it is unconditional.
* 0H3Z is available in the generality of the tag, as
  `AlgebraicGeometry.HasFlatStratification.of_finitePresentation` in
  `StacksFrontier/AlgebraicGeometry/GenericFlatness/MorphismFlatStratificationQcqs.lean:92`, with
  the `Prop`-valued form `AlgebraicGeometry.finitePresentationHasFlatStratification` next to it
  at `:105`. It no longer goes through Stacks 0ASY, so the absolute Noetherian approximation
  cluster 01ZA, 01ZR and 01ZM part (1) is no longer an input to it; Stacks 052B is in the
  library in full generality as
  `AlgebraicGeometry.exists_dense_open_flat_finitePresentation`
  (`StacksFrontier/AlgebraicGeometry/Morphisms/FlatMorphisms/GenericFlatness.lean:1277`).
  The covering of the base by the closed subschemes of such a stratification is
  `AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_flat_stratum`, and over a
  Noetherian base the replacement of each of them by the scheme-theoretic closure of its
  stratum -- which is what makes the stratum a *dense* open, as the Stacks proof needs -- is
  `AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_dense_flat_stratum` in
  `StacksFrontier/AlgebraicGeometry/GenericFlatness/StratificationDensePhCovering.lean:120`.
* 080Y is available, as `AlgebraicGeometry.cartierBoundaryReduction` in
  `StacksFrontier/AlgebraicGeometry/Blowup/DominatedByBlowup.lean:173`.
* 0815 is not. It quantifies over `U`-admissible blowups (Stacks 080K) and over strict
  transforms of schemes and of modules (Stacks 080D), and both notions are in the library:
  `Stacks.Blowup.IsAdmissibleBlowup` in
  `StacksFrontier/AlgebraicGeometry/Blowup/Admissible.lean` and the strict transforms in
  `StacksFrontier/AlgebraicGeometry/Blowup/StrictTransform.lean` (with the ring-level version in
  `StacksFrontier/RingTheory/Blowup/StrictTransform.lean`). The blowup itself is
  `Stacks.Blowup.blowUp` in `StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`, with
  its exceptional ideal sheaf and divisor, separated over its base and proper when the centre
  is of finite type by `StacksFrontier/AlgebraicGeometry/Blowup/Proper.lean`. The statement itself
  is `AlgebraicGeometry.FinitePresentationHasFlatteningBlowup` in
  `StacksFrontier/AlgebraicGeometry/Flatness/RaynaudGrusonFlattening0815.lean`, and it is unproved;
  the affine case of its flatness assertion is available only granted
  `AlgebraicGeometry.AffineChartFlatteningCentre`.

What `AlgebraicGeometry.StandardVCoveringHasPHRefinement` still needs is therefore exactly the
flattening: `AlgebraicGeometry.IsStandardVCovering.exists_standardPHCovering_refinement_of_flat`
in `StacksFrontier/AlgebraicGeometry/Topologies/HTopology/FlatSubmersiveComparison.lean` proves it,
with no carried hypothesis at all, for a family which is already flat.

The analogous reduction for Stacks 0ETT -- the one that replaces its hypothesis by the case of a
family flat over a dense open of the base, leaving Stacks 0815 and the valuative argument it
feeds -- is `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement.of_denseFlat` in
`StacksFrontier/AlgebraicGeometry/Topologies/HTopology/DenseFlatSubmersiveReduction.lean`; that
remainder is discharged in
`StacksFrontier/AlgebraicGeometry/Topologies/HTopology/SubmersiveFlatteningRefinement.lean`, so
Stacks 0ETT holds with nothing granted. The reduction is not
carried out for 0ETR because the base there is affine rather than Noetherian, so
quasi-compactness of the stratum has to be read off the finite type clause of
`AlgebraicGeometry.HasFlatStratification` rather than off the ambient scheme.

## References

* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0ETB](https://stacks.math.columbia.edu/tag/0ETB)
* [Stacks Project, Tag 0DBG](https://stacks.math.columbia.edu/tag/0DBG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- A family of morphisms to an affine scheme `T` which is refined by a standard V covering is
refined by a standard V covering all of whose members are *affine opens* of members of the
given family.

This is the reduction the Stacks proof of 0ETR performs once the base is affine: each member
`Y j` of the
refining standard V covering is affine, hence quasi-compact, so finitely many affine opens of
the member `X (ρ.s₀ j)` it factors through cover the image of `Y j`; those affine opens, as `j`
ranges over the (finite) index set, form the asserted covering. The lifting property passes to
them because the spectrum of a valuation ring has a unique closed point to which every point
specializes, so a morphism from it into `X (ρ.s₀ j)` has image inside any open containing the
image of that closed point. -/
theorem exists_isStandardVCovering_affineOpen_refinement {T : Scheme.{u}} [IsAffine T]
    {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} {J : Type w} [Finite J]
    {Y : J → Scheme.{u}} [∀ j, IsAffine (Y j)] {g : ∀ j, Y j ⟶ T}
    (hg : IsStandardVCovering Y g)
    (ρ : ({ I₀ := J, X := Y, f := g } : PreZeroHypercover.{w} T).Hom
      ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T)) :
    ∃ (K : Type max u w) (A : K → Scheme.{u}) (idx : K → I) (a : ∀ κ, A κ ⟶ X (idx κ))
      (hK : Finite K) (hA : ∀ κ, IsAffine (A κ)),
      (∀ κ, IsOpenImmersion (a κ)) ∧
        @IsStandardVCovering T _ K hK A hA fun κ ↦ a κ ≫ f (idx κ) := by
  classical
  -- An affine open cover of the member of the given family that `Y j` factors through.
  set 𝒞 : ∀ j : J, (X (ρ.s₀ j)).AffineOpenCover := fun j ↦ (X (ρ.s₀ j)).affineOpenCover
  -- Finitely many of its members cover the image of `Y j`, which is compact.
  have hsubcover : ∀ j : J, ∃ S : Finset (𝒞 j).I₀,
      Set.range (ρ.h₀ j).base ⊆ ⋃ c ∈ S, Set.range ((𝒞 j).f c).base := by
    intro j
    refine (isCompact_range (ρ.h₀ j).continuous).elim_finite_subcover
      (fun c ↦ Set.range ((𝒞 j).f c).base) (fun c ↦ IsOpenImmersion.isOpen_range _)
      fun x _ ↦ Set.mem_iUnion.mpr ⟨(𝒞 j).idx x, (𝒞 j).covers x⟩
  choose S hS using hsubcover
  refine ⟨Σ j : J, {c : (𝒞 j).I₀ // c ∈ S j}, fun κ ↦ Spec ((𝒞 κ.1).X κ.2.1),
    fun κ ↦ ρ.s₀ κ.1, fun κ ↦ (𝒞 κ.1).f κ.2.1, inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, ?_⟩
  intro V _ _ _ gV
  obtain ⟨W, _, _, _, e, he, j, h, hcomm⟩ := hg V gV
  have hfac : ρ.h₀ j ≫ f (ρ.s₀ j) = g j := ρ.w₀ j
  -- The closed point of `Spec W` lands in one of the chosen affine opens.
  obtain ⟨c, hcS, hc⟩ := Set.mem_iUnion₂.mp (hS j (Set.mem_range_self (f := (ρ.h₀ j).base)
    (h (IsLocalRing.closedPoint W))))
  -- Hence so does all of `Spec W`, every point of which specializes to the closed point.
  have hrange : Set.range (h ≫ ρ.h₀ j).base ⊆ Set.range ((𝒞 j).f c).base := by
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map (h ≫ ρ.h₀ j).continuous).mem_open
      (IsOpenImmersion.isOpen_range _) hc
  refine ⟨W, inferInstance, inferInstance, inferInstance, e, he, ⟨j, c, hcS⟩,
    IsOpenImmersion.lift ((𝒞 j).f c) (h ≫ ρ.h₀ j) hrange, ?_⟩
  calc Spec.map (CommRingCat.ofHom e) ≫ gV = h ≫ g j := hcomm
    _ = (h ≫ ρ.h₀ j) ≫ f (ρ.s₀ j) := by rw [Category.assoc, hfac]
    _ = (IsOpenImmersion.lift ((𝒞 j).f c) (h ≫ ρ.h₀ j) hrange ≫ (𝒞 j).f c) ≫ f (ρ.s₀ j) := by
      rw [IsOpenImmersion.lift_fac]
    _ = IsOpenImmersion.lift ((𝒞 j).f c) (h ≫ ρ.h₀ j) hrange ≫ (𝒞 j).f c ≫ f (ρ.s₀ j) :=
      Category.assoc _ _ _

/-- The remaining input to Stacks 0ETR: every standard V covering of an affine scheme whose
members are locally of finite presentation is refined by a standard ph covering.

This is the case the Stacks proof of 0ETR reduces to, and the only one of its steps that uses
the flattening machinery: one stratifies the base by generic flatness, flattens the family by
an admissible blowup, and recognizes the result as an fppf and hence a ph covering. -/
def StandardVCoveringHasPHRefinement : Prop :=
  ∀ (U : Scheme.{u}) (hU : IsAffine U) (K : Type u) (hK : Finite K) (A : K → Scheme.{u})
    (hA : ∀ κ, IsAffine (A κ)) (a : ∀ κ, A κ ⟶ U), (∀ κ, LocallyOfFinitePresentation (a κ)) →
      @IsStandardVCovering U hU K hK A hA a →
        ∃ 𝒱 : PreZeroHypercover.{u} U, @StandardPHCovering 𝒱.I₀ U hU 𝒱.X 𝒱.f ∧
          Nonempty (𝒱.Hom ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} U))

/-- Granted `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, a V covering whose members
are locally of finite presentation is a ph covering. This is the implication (2) ⟹ (1) of
Stacks 0ETR, reduced to the standard case.

Over an affine open `U` of the target, the pullback of the family is refined by a standard V
covering, hence by `AlgebraicGeometry.exists_isStandardVCovering_affineOpen_refinement` by a
standard V covering consisting of affine opens of the pulled back members. Those are locally
of finite presentation over `U`, so the hypothesis refines them by a standard ph covering, and
composing refinements gives the one required by the definition of a ph covering. -/
theorem isPHCovering_of_isVCovering (H : StandardVCoveringHasPHRefinement.{u})
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) (hV : IsVCovering X f) :
    IsPHCovering X f := by
  refine ⟨fun i ↦ have := hfp i; inferInstance, fun U hU ↦ ?_⟩
  have : IsAffine U.toScheme := hU
  obtain ⟨𝒰, hfinite, haffine, hstd, ⟨ρ⟩⟩ := hV U hU
  have : Finite 𝒰.I₀ := hfinite
  have : ∀ j, IsAffine (𝒰.X j) := haffine
  obtain ⟨K, A, idx, a, hK, hA, hopen, hstdV⟩ :=
    exists_isStandardVCovering_affineOpen_refinement (T := U.toScheme) hstd ρ
  have hlfp : ∀ κ, LocallyOfFinitePresentation (a κ ≫ pullback.snd (f (idx κ)) U.ι) := by
    intro κ
    have h₁ := hopen κ
    have h₂ := hfp (idx κ)
    infer_instance
  obtain ⟨𝒱, h𝒱, ⟨φ⟩⟩ := H U.toScheme hU K hK A hA _ hlfp hstdV
  exact ⟨𝒱, h𝒱, ⟨φ.comp ⟨idx, a, fun _ ↦ rfl⟩⟩⟩

/-- Granted `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, a family of morphisms of
schemes which are locally of finite presentation is a ph covering if and only if it is a V
covering. This is the statement of Stacks 0ETR, reduced to the standard case. -/
theorem isPHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement
    (H : StandardVCoveringHasPHRefinement.{u})
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    IsPHCovering X f ↔ IsVCovering X f :=
  ⟨isVCovering_of_isPHCovering X f, isPHCovering_of_isVCovering H X f hfp⟩

end AlgebraicGeometry

end

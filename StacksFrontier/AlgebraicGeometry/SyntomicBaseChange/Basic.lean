module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.Algebra
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Basic

/-!
# The complete-intersection fibre locus and the syntomic locus commute with base change

Let `f : X ⟶ S` be a morphism of schemes and let `f' : X' ⟶ S'` be its base change along
`g : S' ⟶ S`, with projection `g' : X' ⟶ X`, presented as an arbitrary cartesian square.  The
fibres of `f'` are the base changes of the fibres of `f`, so the locus where the closed fibre is
a complete intersection over the residue field of the image point is the `g'`-preimage of the
corresponding locus for `f`.  For `f` flat and locally of finite presentation this is the
syntomic locus, by Stacks Lemma 01UE.

## Main results

* `AlgebraicGeometry.isCompleteIntersectionFibreAt_baseChange_iff`: the pointwise statement, for
  `f` locally of finite type.
* `AlgebraicGeometry.syntomicLocus_eq_preimage`: Stacks Lemma 02V3 for the syntomic locus of a
  flat morphism locally of finite presentation.

## Implementation notes

The affine chart is chosen as in Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`
and not as a product of three independent choices: with `U_S ⊆ S`, `U_X ⊆ X` and `U_T ⊆ S'`
affine, the open `U_Y = (g')^{-1}(U_X) ∩ (f')^{-1}(U_T)` of `X'` is the fibre product
`U_X ×_{U_S} U_T` and so is affine, and the four rings of sections then form a pushout square in
`CommRingCat` (`AlgebraicGeometry.isIso_pushoutSection_iff`), which
`CommRingCat.isPushout_iff_isPushout` turns into `Algebra.IsPushout`.  Reading the closed-fibre
condition in that chart on either side (`AlgebraicGeometry.isCompleteIntersectionFibreAt_iff_chart`)
reduces the statement to the ring-level base change
`Stacks.SyntomicBaseChange.isCompleteIntersection_fiber_baseChange_iff`.

## References

* [Stacks 02V3](https://stacks.math.columbia.edu/tag/02V3), Lemma 29.30.12.
* [Stacks 01UE](https://stacks.math.columbia.edu/tag/01UE), Lemma 29.30.11.
* [Stacks 00SI](https://stacks.math.columbia.edu/tag/00SI), Lemma 10.135.10.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X' X S' S : Scheme.{u}}

/-- **The closed-fibre complete-intersection condition is insensitive to base change.**  Let
`f : X ⟶ S` be locally of finite type and let the square `g'`, `f'`, `f`, `g` be cartesian, so
that `f' : X' ⟶ S'` is the base change of `f` along `g : S' ⟶ S`.  Then the closed fibre of `f'`
at `x'` is a complete intersection over `κ(f' x')` if and only if the closed fibre of `f` at
`g' x'` is a complete intersection over `κ(f (g' x'))`.

This is the pointwise form of Stacks Lemma 02V3; the proof reads both sides in a single chart
adapted to the square and applies Stacks Lemma 00SI. -/
theorem isCompleteIntersectionFibreAt_baseChange_iff
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (x' : X') :
    IsCompleteIntersectionFibreAt f' x' ↔ IsCompleteIntersectionFibreAt f (g' x') := by
  have hw (y : X') : f (g' y) = g (f' y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  -- the three affine charts, and the fourth one they force
  obtain ⟨-, ⟨US, hUS, rfl⟩, hsUS, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (g' x'))) isOpen_univ
  obtain ⟨-, ⟨UX, hUX, rfl⟩, hxUX, hUSX₀⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hsUS (US.2.preimage f.continuous)
  have hsUS' : f' x' ∈ (g ⁻¹ᵁ US : Set S') := by
    change g (f' x') ∈ (US : Set S); exact hw x' ▸ hsUS
  obtain ⟨-, ⟨UT, hUT, rfl⟩, hxUT, hUST₀⟩ := S'.isBasis_affineOpens.exists_subset_of_mem_open
    hsUS' (US.2.preimage g.continuous)
  have hUSX : UX ≤ f ⁻¹ᵁ US := hUSX₀
  have hUST : UT ≤ g ⁻¹ᵁ US := hUST₀
  have : IsAffine _ := hUS
  have : IsAffine _ := hUT
  have : IsAffine _ := hUX
  have hUY : IsAffineOpen (g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT) :=
    .of_isIso (Scheme.Hom.isPullback_resLE hpb hUST hUSX rfl).isoPullback.hom
  have hxUY : x' ∈ g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT := ⟨hxUX, hxUT⟩
  have hUYX : g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT ≤ g' ⁻¹ᵁ UX := inf_le_left
  have hUYT : g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT ≤ f' ⁻¹ᵁ UT := inf_le_right
  -- the four algebra structures of the chart, and the two scalar towers
  let := (g.appLE US UT hUST).hom.toAlgebra
  let := (f.appLE US UX hUSX).hom.toAlgebra
  let := (f'.appLE UT _ hUYT).hom.toAlgebra
  let := (g'.appLE UX _ hUYX).hom.toAlgebra
  let : Algebra Γ(S, US) Γ(X', g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT) :=
    ((f'.appLE UT _ hUYT).hom.comp (g.appLE US UT hUST).hom).toAlgebra
  have hcomm : f.appLE US UX hUSX ≫ g'.appLE UX _ hUYX
      = g.appLE US UT hUST ≫ f'.appLE UT _ hUYT := by
    simp only [Scheme.Hom.appLE_comp_appLE, hpb.w]
  have : IsScalarTower Γ(S, US) Γ(S', UT) Γ(X', g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(S, US) Γ(X, UX) Γ(X', g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT) :=
    .of_algebraMap_eq fun s ↦ (congr($hcomm s)).symm
  -- the chart square is a pushout square
  have : Algebra.IsPushout Γ(S, US) Γ(S', UT) Γ(X, UX) Γ(X', g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ UT) := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    exact ((isIso_pushoutSection_iff hpb hUST hUSX rfl).mp
      (isIso_pushoutSection_of_isAffineOpen hpb hUST hUSX rfl hUS hUT hUX)).flip
  have : Algebra.FiniteType Γ(S, US) Γ(X, UX) := f.finiteType_appLE hUS hUX hUSX
  -- the four primes, and the three `LiesOver` relations between them
  have hqp := liesOver_primeIdealOf_appLE f hUS hUX hUSX hxUX
  have hq'p' := liesOver_primeIdealOf_appLE f' hUT hUY hUYT hxUY
  have hq'q := liesOver_primeIdealOf_appLE g' hUX hUY hUYX hxUY
  have hp'p : let := (g.appLE US UT hUST).hom.toAlgebra
      (hUT.primeIdealOf ⟨f' x', hxUT⟩).asIdeal.LiesOver
        (hUS.primeIdealOf ⟨f (g' x'), hUSX hxUX⟩).asIdeal := by
    have h := liesOver_primeIdealOf_appLE g hUS hUT hUST hxUT
    rwa [show (⟨g (f' x'), hUST hxUT⟩ : ↥US) = ⟨f (g' x'), hUSX hxUX⟩ from
      Subtype.ext (hw x').symm] at h
  rw [isCompleteIntersectionFibreAt_iff_chart f' hUT hUY hUYT hxUY,
    isCompleteIntersectionFibreAt_iff_chart f hUS hUX hUSX hxUX]
  exact Stacks.SyntomicBaseChange.isCompleteIntersection_fiber_baseChange_iff
    (hUS.primeIdealOf ⟨f (g' x'), hUSX hxUX⟩).asIdeal
    (hUX.primeIdealOf ⟨g' x', hxUX⟩).asIdeal
    (hUT.primeIdealOf ⟨f' x', hxUT⟩).asIdeal
    (hUY.primeIdealOf ⟨x', hxUY⟩).asIdeal

/-- **Stacks Project, Tag 02V3.**  For a flat morphism locally of finite presentation, the
syntomic locus commutes with arbitrary base change: if the square `g'`, `f'`, `f`, `g` is
cartesian then the set of points where `f'` is syntomic is the `g'`-preimage of the set of points
where `f` is syntomic. -/
@[stacks 02V3 "syntomic locus"]
theorem syntomicLocus_eq_preimage
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f] :
    {x' : X' | IsSyntomicAt f' x'} = g' ⁻¹' {x : X | IsSyntomicAt f x} := by
  have : Flat f' := MorphismProperty.of_isPullback hpb ‹Flat f›
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback hpb ‹_›
  ext x'
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    isSyntomicAt_iff_isCompleteIntersectionFibreAt f' x',
    isSyntomicAt_iff_isCompleteIntersectionFibreAt f (g' x')]
  exact isCompleteIntersectionFibreAt_baseChange_iff g' f' f g hpb x'

end AlgebraicGeometry

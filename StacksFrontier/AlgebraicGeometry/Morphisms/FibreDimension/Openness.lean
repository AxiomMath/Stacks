module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity

/-!
# The bounded fibre-dimension locus

For a morphism locally of finite type, the points where the local dimension of the
scheme-theoretic fibre is bounded by a fixed natural number form an open subset, and for a
morphism locally of finite presentation that open subset is moreover retrocompact. Both
statements are local on source and target, so each reduces to the corresponding semicontinuity
statement for the relative dimension of a ring map — upper semicontinuity of
`Algebra.relativeDimensionAt` for openness, and its constructibility for retrocompactness.

## Main results

* `AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le` proves that the locus where the fibre has
  local dimension at most `n` is open.
* `AlgebraicGeometry.isRetrocompact_setOf_fiberDimensionAt_le` proves retrocompactness of that
  locus under local finite presentation.

## Implementation notes

The point `x` in the fibre over `f x` is represented canonically by `Scheme.Hom.asFiber x`, and
the dimension at that point is `topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`. The
source's nonnegative integer `n` is represented by a natural number and coerced to
`WithBot ℕ∞`, the codomain of topological Krull dimension. Mathlib's `IsRetrocompact` is the
source's notion of an open being retrocompact in the ambient scheme.

Transporting the dimension along the charts needs the local dimension of a fibre to be
unchanged by an open immersion in the source and by a monomorphism in the target; those two
transport lemmas are proved first and used by both results.

## References

* [EGA IV, Theorem 13.1.3]
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 02G0](https://stacks.math.columbia.edu/tag/02G0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On affine schemes, the local dimension of a fibre is the relative dimension of the
corresponding ring map. -/
public lemma affine_fiberDimensionAt_eq {R T : CommRingCat.{u}}
    (φ : R ⟶ T) (x : Spec T) :
    topologicalKrullDimAt ((Spec.map φ).fiber (Spec.map φ x))
        ((Spec.map φ).asFiber x) =
      @Algebra.relativeDimensionAt R T _ _ φ.hom.toAlgebra x.asIdeal x.isPrime := by
  let _ := φ.hom.toAlgebra
  rw [topologicalKrullDimAt_eq_of_homeomorph ((Spec.map φ).fiberHomeo _) _,
    Algebra.relativeDimensionAt]
  congr 1
  exact Subtype.ext ((Spec.map φ).fiberι_asFiber x)

/-- A subset is open if its preimage under each map of an open-immersion cover is open. -/
private lemma isOpen_of_forall_isOpen_preimage_cover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    [∀ i, IsOpenImmersion (𝒰.f i)] {s : Set X} (h : ∀ i, IsOpen (𝒰.f i ⁻¹' s)) : IsOpen s := by
  refine (isOpen_iff_of_cover (fun i ↦ IsOpenImmersion.isOpen_range (𝒰.f i))
    (Set.iUnion_eq_univ_iff.mpr fun x ↦ ⟨𝒰.idx x, 𝒰.covers x⟩)).2 fun i ↦ ?_
  rw [(𝒰.f i).isOpenEmbedding.isOpen_iff_preimage_isOpen Set.inter_subset_left,
    Set.preimage_inter, Set.preimage_range, Set.univ_inter]
  exact h i

/-- **Stacks Project, Tag 02FZ.** For a locally finite type morphism of schemes, the locus where
the local dimension of the fibre is at most `n` is open. -/
@[stacks 02FZ, ega "IV 13.1.3"]
public lemma isOpen_setOf_fiberDimensionAt_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (n : ℕ) :
    IsOpen {x : X |
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (n : WithBot ℕ∞)} := by
  wlog hS : ∃ R, S = Spec R generalizing X S
  · let Υ : Scheme.OpenCover X := S.affineCover.pullback₁ f
    refine isOpen_of_forall_isOpen_preimage_cover Υ fun i ↦ ?_
    dsimp only [Υ] at i ⊢
    have hopenTarget : IsOpenImmersion (S.affineCover.f i) := S.affineCover.map_prop i
    have hftPull : LocallyOfFiniteType (S.affineCover.pullbackHom f i) := by
      change LocallyOfFiniteType (pullback.snd f (S.affineCover.f i))
      infer_instance
    convert this (S.affineCover.pullbackHom f i) ⟨_, rfl⟩ using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [fiberDimensionAt_eq_of_open_square (Υ.f i) f (S.affineCover.pullbackHom f i)
      (S.affineCover.f i) (IsPullback.of_hasPullback f (S.affineCover.f i)).w x]
  obtain ⟨R, rfl⟩ := hS
  wlog hX : ∃ T, X = Spec T generalizing X f
  · refine isOpen_of_forall_isOpen_preimage_cover X.affineCover fun i ↦ ?_
    convert this (X.affineCover.f i ≫ f) ⟨_, rfl⟩ using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [fiberDimensionAt_eq_of_open_square (X.affineCover.f i) f
      (X.affineCover.f i ≫ f) (𝟙 _) (by simp) x]
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : RingHom.FiniteType φ.hom :=
    HasRingHomProperty.Spec_iff.mp (show LocallyOfFiniteType (Spec.map φ) from inferInstance)
  algebraize [φ.hom]
  change @IsOpen (PrimeSpectrum T) PrimeSpectrum.zariskiTopology {x : PrimeSpectrum T |
    topologicalKrullDimAt ((Spec.map φ).fiber (Spec.map φ x))
      ((Spec.map φ).asFiber x) ≤ (n : WithBot ℕ∞)}
  convert (Algebra.isOpen_setOf_relativeDimensionAt_le (R := R) (S := T) n) using 1
  ext x
  exact (congrArg (fun d : WithBot ℕ∞ ↦ d ≤ (n : WithBot ℕ∞))
    (affine_fiberDimensionAt_eq φ x)).to_iff

/-- The bounded fibre-dimension locus meets each affine chart in a compact set. -/
private lemma isCompact_inter_affineChart {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (n : ℕ) (U : S.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    IsCompact ({x : X |
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (n : WithBot ℕ∞)} ∩
      (V.1 : Set X)) := by
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, U.1) Γ(X, V.1) :=
    f.finitePresentation_appLE U.2 V.2 e
  let R : Set (PrimeSpectrum Γ(X, V.1)) :=
    {q | Algebra.relativeDimensionAt Γ(S, U.1) q.asIdeal ≤ (n : WithBot ℕ∞)}
  have hEq : V.2.fromSpec '' R =
      {x : X | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤
        (n : WithBot ℕ∞)} ∩ (V.1 : Set X) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hxV : V.2.fromSpec q ∈ V.1 := by
        change (V.2.isoSpec.inv q).1 ∈ V.1
        exact (V.2.isoSpec.inv q).property
      refine ⟨?_, hxV⟩
      change topologicalKrullDimAt (f.fiber (f (V.2.fromSpec q)))
          (f.asFiber (V.2.fromSpec q)) ≤ _
      rw [fiberDimensionAt_eq_relativeDimensionAt_chart f U V e _ hxV]
      have hqId : V.2.primeIdealOf ⟨V.2.fromSpec q, hxV⟩ = q := by
        change V.2.isoSpec.hom ⟨V.2.fromSpec q, hxV⟩ = q
        have hsub : (⟨V.2.fromSpec q, hxV⟩ : V.1) = V.2.isoSpec.inv q := Subtype.ext rfl
        rw [hsub]
        simp
      have : q.asIdeal.IsPrime := q.isPrime
      change Algebra.relativeDimensionAt Γ(S, U.1) q.asIdeal ≤ _ at hq
      simpa only [hqId] using hq
    · rintro ⟨hxL, hxV⟩
      refine ⟨V.2.primeIdealOf ⟨x, hxV⟩, ?_, V.2.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
      change Algebra.relativeDimensionAt Γ(S, U.1) (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal ≤ _
      rwa [← fiberDimensionAt_eq_relativeDimensionAt_chart f U V e x hxV]
  rw [← hEq]
  exact ((Algebra.isCompact_isOpen_setOf_relativeDimensionAt_le n).1).image
    V.2.fromSpec.continuous

/-- **Stacks Project, Tag 02G0.** For a morphism of schemes locally of finite presentation, the
locus where the local dimension of the fibre is at most `n` is retrocompact. -/
@[stacks 02G0]
public lemma isRetrocompact_setOf_fiberDimensionAt_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (n : ℕ) :
    IsRetrocompact {x : X |
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (n : WithBot ℕ∞)} := by
  let L : Set X := {x | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤
    (n : WithBot ℕ∞)}
  have hAffine (W : X.affineOpens) : IsCompact (L ∩ (W.1 : Set X)) := by
    have hc : ∀ x : W.1, ∃ U : S.affineOpens, ∃ V : X.affineOpens,
        ∃ e : V.1 ≤ f ⁻¹ᵁ U.1, V.1 ≤ W.1 ∧ x.1 ∈ V.1 := by
      intro x
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x.1)) isOpen_univ
      have hxWU : x.1 ∈ (W.1 : Set X) ∩ f ⁻¹' (U : Set S) := ⟨x.2, hxU⟩
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVWU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          hxWU (W.1.isOpen.inter (U.2.preimage f.continuous))
      exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hVWU.trans inf_le_right,
        hVWU.trans inf_le_left, hxV⟩
    choose U V e hVW hx using hc
    have hcover : (W.1 : Set X) ⊆ ⋃ x : W.1, (V x).1 :=
      fun x hxW => Set.mem_iUnion.mpr ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩
    obtain ⟨t, ht⟩ := W.2.isCompact.elim_finite_subcover
      (fun x : W.1 => ((V x).1 : Set X)) (fun x => (V x).1.isOpen) hcover
    have hW : (W.1 : Set X) = ⋃ x ∈ t, ((V x).1 : Set X) :=
      subset_antisymm ht (Set.iUnion₂_subset fun i _ => hVW i)
    rw [hW, Set.inter_iUnion₂]
    exact t.isCompact_biUnion fun i _ => isCompact_inter_affineChart f n (U i) (V i) (e i)
  intro K hKcomp hKopen
  obtain ⟨s, hs, hK⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hKcomp, hKopen⟩
  change IsCompact (L ∩ K)
  rw [hK]
  simp only [Set.inter_iUnion]
  exact hs.isCompact_biUnion fun W _ => hAffine W

end AlgebraicGeometry

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.RingTheory.RelativeDimension.Defs
import StacksFrontier.RingTheory.Flat.CompleteDevissageSpecTransport

/-!
# Reading the local fibre dimension of a morphism on an affine chart

Let `f : X ⟶ S` be a morphism of schemes, `x` a point of `X`, and let `U ⊆ S` and `V ⊆ X` be
affine opens with `x ∈ V` and `f(V) ⊆ U`. This file identifies the local dimension
`dim_x(X_{f x})` of the scheme-theoretic fibre of `f` through `x` with the relative dimension
`dim_𝔮(Γ(X, V) / Γ(S, U))` of the ring map on sections at the prime of `x`.

This is the "the question is local on `X` and `S`" step of Stacks 052E: it is what lets the
scheme-level fibre-dimension hypothesis be fed to the affine Stacks 0520.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_asFiber_eq_relativeDimensionAt`: the local
  dimension of the fibre at `x` equals the relative dimension of `Γ(S, U) → Γ(X, V)` at the
  prime corresponding to `x`.
* `AlgebraicGeometry.relativeDimensionAt_appLE_eq_of_fiber_dim`: the form in which the equality
  is used, transporting a numerical value of the fibre dimension to the affine chart.

## Implementation notes

The chain of identifications is purely topological. The scheme-theoretic fibre is replaced by
the topological fibre `f ⁻¹' {f x}` by `topologicalKrullDimAt_fiber_asFiber_eq_preimage`. The
composite of the homeomorphism `V ≃ Spec Γ(X, V)` with the inclusion `V ↪ X` is an open
embedding whose preimage of the topological fibre is exactly the fibre
`comap(Γ(S, U) → Γ(X, V)) ⁻¹' {𝔭}` appearing in `Algebra.relativeDimensionAt`, because
`IsAffineOpen.comap_primeIdealOf_appLE` computes the contraction of the prime of a point and
`IsAffineOpen.fromSpec_primeIdealOf` shows the correspondence between points and primes is
injective. Locality of `topologicalKrullDimAt` under open embeddings
(`Topology.IsOpenEmbedding.topologicalKrullDimAt_eq`) then finishes the proof.

The `Γ(S, U)`-algebra structure on `Γ(X, V)` is the one induced by the ring map on sections,
introduced in the statement by `RingHom.toAlgebra`, as in `RingHom.QuasiFiniteAt`.

## References

* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
* [Stacks Project, Tag 00QD](https://stacks.math.columbia.edu/tag/00QD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u


namespace AlgebraicGeometry

/-- **The affine-locality of the fibre dimension.** For affine opens `U ⊆ S` and `V ⊆ X` with
`x ∈ V` and `V ⊆ f⁻¹(U)`, the local dimension of the fibre of `f` through `x` equals the
relative dimension of `Γ(S, U) → Γ(X, V)` at the prime corresponding to `x`. -/
theorem topologicalKrullDimAt_fiber_asFiber_eq_relativeDimensionAt
    {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {U : S.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      Algebra.relativeDimensionAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  let _inst := (f.appLE U V hVU).hom.toAlgebra
  set φ := (f.appLE U V hVU).hom with hφ
  set e := Scheme.homeoOfIso hV.isoSpec with he
  set p : PrimeSpectrum Γ(S, U) := hU.primeIdealOf ⟨f x, hVU hxV⟩ with hp
  have heq : ∀ v : ↥V, e v = hV.primeIdealOf v := fun v => rfl
  have hcrit : ∀ v : ↥V, (f (v : X) = f x) ↔ PrimeSpectrum.comap φ (hV.primeIdealOf v) = p := by
    intro v
    rw [IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU v.2 (f := f)]
    refine ⟨fun h => by congr 1; exact Subtype.ext h, fun h => ?_⟩
    have h2 := congrArg hU.fromSpec h
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h2
  have hopen : Topology.IsOpenEmbedding (Subtype.val ∘ (e.symm : _ → ↥V)) :=
    (V.2.isOpenEmbedding_subtypeVal).comp e.symm.isOpenEmbedding
  have hpre : (Subtype.val ∘ (e.symm : _ → ↥V)) ⁻¹' ((f : X → S) ⁻¹' {f x}) =
      PrimeSpectrum.comap φ ⁻¹' {p} := by
    ext t
    have hid : hV.primeIdealOf (e.symm t) = t :=
      (heq (e.symm t)).symm.trans (e.apply_symm_apply t)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := (hcrit (e.symm t)).1 h
      rwa [hid] at h2
    · exact (hcrit (e.symm t)).2 (by rwa [hid])
  have hesym : e.symm (hV.primeIdealOf ⟨x, hxV⟩) = ⟨x, hxV⟩ :=
    e.symm_apply_eq.mpr (heq ⟨x, hxV⟩).symm
  have hmemq : hV.primeIdealOf ⟨x, hxV⟩ ∈
      (Subtype.val ∘ (e.symm : _ → ↥V)) ⁻¹' ((f : X → S) ⁻¹' {f x}) := by
    change f (Subtype.val (e.symm (hV.primeIdealOf ⟨x, hxV⟩))) = f x
    rw [hesym]
  rw [topologicalKrullDimAt_fiber_asFiber_eq_preimage f x]
  have key := (hopen.restrictPreimage ((f : X → S) ⁻¹' {f x})).topologicalKrullDimAt_eq
    ⟨hV.primeIdealOf ⟨x, hxV⟩, hmemq⟩
  have hval : (((f : X → S) ⁻¹' {f x}).restrictPreimage
        (Subtype.val ∘ (e.symm : _ → ↥V))) ⟨hV.primeIdealOf ⟨x, hxV⟩, hmemq⟩ =
      (⟨x, rfl⟩ : ↥((f : X → S) ⁻¹' {f x})) := by
    refine Subtype.ext ?_
    change Subtype.val (e.symm (hV.primeIdealOf ⟨x, hxV⟩)) = x
    rw [hesym]
  rw [hval] at key
  rw [key, Algebra.relativeDimensionAt]
  refine topologicalKrullDimAt_congr_set ?_ _ _ _
  rw [hpre]
  congr 1
  exact Set.singleton_eq_singleton_iff.mpr
    (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV (f := f)).symm

/-- The form in which `topologicalKrullDimAt_fiber_asFiber_eq_relativeDimensionAt` is used: a
numerical value of the local fibre dimension of `f` at `x` is also the relative dimension of
the ring map on sections over an affine chart around `x`. -/
theorem relativeDimensionAt_appLE_eq_of_fiber_dim
    {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {U : S.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V)
    {d : WithBot ℕ∞} (hd : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = d) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    Algebra.relativeDimensionAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal = d :=
  (topologicalKrullDimAt_fiber_asFiber_eq_relativeDimensionAt f hU hV hVU hxV).symm.trans hd

end AlgebraicGeometry

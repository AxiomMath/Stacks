module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity

/-!
# Comparing the local dimension of a fibre along a morphism

The local dimension of a fibre at a point is unchanged by precomposing with an open immersion
and by postcomposing with an injective morphism, and on affine charts it is the relative
dimension of the induced map of coordinate rings.

## Main results

* `fiberDimensionAt_specMap`: on affine schemes, the local dimension of a fibre is the relative
  dimension of the algebra.
* `fiberDimensionAt_comp_openImmersion`: precomposing with an open immersion does not change the
  local dimension of a fibre.
* `fiberDimensionAt_comp_embedding`: postcomposing with an injective morphism does not change the
  local dimension of a fibre.
* `fiberDimensionAt_eq_relativeDimensionAt_chart`: on compatible affine charts, the local
  dimension of a fibre is the relative dimension of the induced map of coordinate rings.
* `fiberDimensionAt_eq_of_open_square`: the local dimension of a fibre is unchanged along a
  commuting square of open immersions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On affine schemes, the local dimension of a fibre of the map induced by an algebra
structure is the relative dimension of that algebra. -/
theorem fiberDimensionAt_specMap {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (q : PrimeSpectrum B) :
    topologicalKrullDimAt
        ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap R B))) q))
        ((Spec.map (CommRingCat.ofHom (algebraMap R B))).asFiber q) =
      Algebra.relativeDimensionAt R q.asIdeal := by
  rw [topologicalKrullDimAt_eq_of_homeomorph
    ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiberHomeo _) _, Algebra.relativeDimensionAt]
  congr 1
  exact Subtype.ext ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiberι_asFiber q)

/-- The local dimension of the fibre at `f x` at the point `x` is that of the set `f ⁻¹' {f x}`. -/
private theorem topologicalKrullDimAt_fiber_eq {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f ⁻¹' {f x}) ⟨x, rfl⟩ :=
  (topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo _) _).trans
    (by rw [show f.fiberHomeo _ (f.asFiber x) = ⟨x, rfl⟩ from Subtype.ext (f.fiberι_asFiber x)])

/-- The local dimension of a subspace at a point only depends on the underlying set. -/
private theorem topologicalKrullDimAt_setCongr {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A = B) (x : X) (hA : x ∈ A) (hB : x ∈ B) :
    topologicalKrullDimAt A ⟨x, hA⟩ = topologicalKrullDimAt B ⟨x, hB⟩ := by
  subst h
  rfl

/-- Precomposing with an open immersion does not change the local dimension of a fibre. -/
theorem fiberDimensionAt_comp_openImmersion {U X S : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ S) (x : U) :
    topologicalKrullDimAt ((j ≫ f).fiber ((j ≫ f) x)) ((j ≫ f).asFiber x) =
      topologicalKrullDimAt (f.fiber (f (j x))) (f.asFiber (j x)) := by
  rw [topologicalKrullDimAt_fiber_eq, topologicalKrullDimAt_fiber_eq]
  have hC : (j ≫ f) ⁻¹' {(j ≫ f) x} = j ⁻¹' (f ⁻¹' {f (j x)}) := by ext; simp
  exact (topologicalKrullDimAt_setCongr hC x rfl rfl).trans
    ((j.isOpenEmbedding.restrictPreimage (f ⁻¹' {f (j x)})).topologicalKrullDimAt_eq ⟨x, rfl⟩).symm

/-- Postcomposing with an injective map does not change the local dimension of a fibre. -/
theorem fiberDimensionAt_comp_embedding {X V S : Scheme.{u}}
    (g : X ⟶ V) (k : V ⟶ S) (hk : Function.Injective k) (x : X) :
    topologicalKrullDimAt ((g ≫ k).fiber ((g ≫ k) x)) ((g ≫ k).asFiber x) =
      topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) := by
  rw [topologicalKrullDimAt_fiber_eq, topologicalKrullDimAt_fiber_eq]
  refine topologicalKrullDimAt_setCongr (Set.ext fun y ↦ ?_) _ _ _
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply] using hk.eq_iff

/-- On a pair of compatible affine charts, the local dimension of a fibre is the relative
dimension of the induced map of coordinate rings. -/
theorem fiberDimensionAt_eq_relativeDimensionAt_chart {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) (x : X) (hx : x ∈ V.1) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      letI := (f.appLE U V e).hom.toAlgebra
      Algebra.relativeDimensionAt Γ(S, U.1) (V.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let _ := (f.appLE U V e).hom.toAlgebra
  let q := V.2.primeIdealOf ⟨x, hx⟩
  have hq : V.2.fromSpec q = x := V.2.fromSpec_primeIdealOf ⟨x, hx⟩
  have hcomp : Spec.map (f.appLE U.1 V.1 e) ≫ U.2.fromSpec = V.2.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 e
  let D (m : Spec Γ(X, V.1) ⟶ S) : WithBot ℕ∞ :=
    topologicalKrullDimAt (m.fiber (m q)) (m.asFiber q)
  have h1 := (fiberDimensionAt_comp_openImmersion V.2.fromSpec f q).symm
  have h3 := fiberDimensionAt_comp_embedding
    (Spec.map (f.appLE U.1 V.1 e)) U.2.fromSpec U.2.fromSpec.isOpenEmbedding.injective q
  have h4 := fiberDimensionAt_specMap (R := Γ(S, U.1)) (B := Γ(X, V.1)) q
  rw [hq] at h1
  exact h1.trans ((congrArg D hcomp.symm).trans (h3.trans h4))

/-- The local dimension of a fibre is unchanged along a commuting square of open immersions. -/
theorem fiberDimensionAt_eq_of_open_square {P X Y' Y : Scheme.{u}}
    (j : P ⟶ X) (f : X ⟶ Y) (g : P ⟶ Y') (i : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion i] (h : j ≫ f = g ≫ i) (x : P) :
    topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) =
      topologicalKrullDimAt (f.fiber (f (j x))) (f.asFiber (j x)) := by
  have H : g ⁻¹' {g x} = j ⁻¹' (f ⁻¹' {f (j x)}) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hc (z : P) : f (j z) = i (g z) := by
      simpa only [← Scheme.Hom.comp_apply] using congrArg (fun k : P ⟶ Y ↦ k z) h
    exact ⟨fun ha ↦ (hc a).trans ((congrArg i ha).trans (hc x).symm),
      fun ha ↦ i.isOpenEmbedding.injective ((hc a).symm.trans (ha.trans (hc x)))⟩
  rw [topologicalKrullDimAt_fiber_eq, topologicalKrullDimAt_fiber_eq]
  exact (topologicalKrullDimAt_setCongr H x rfl rfl).trans
    ((j.isOpenEmbedding.restrictPreimage (f ⁻¹' {f (j x)})).topologicalKrullDimAt_eq ⟨x, rfl⟩).symm

end AlgebraicGeometry

end

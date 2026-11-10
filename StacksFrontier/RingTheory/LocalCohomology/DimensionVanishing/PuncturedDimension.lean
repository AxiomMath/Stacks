module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sets.Closeds

/-!
# Removing a closed point drops the dimension

Let `X` be a topological space with a point `x` whose singleton is closed and to which every
point of `X` specializes — the closed point of the spectrum of a local ring is the motivating
example. Then every chain of irreducible closed subsets of an open `U` not containing `x`
extends, by prepending `{x}`, to a strictly longer chain in `X`: the closure of a point of a
member of the chain already contains `x`, so `{x}` lies strictly below every member. Hence
`dim U < dim X` whenever `dim X` is finite.

Specialised to `X = Spec A` for a local ring `A` and `U` the complement of a nonempty zero
locus `V(I)`, this is the step of Stacks 0DXC which says that
`dim (Spec A ∖ V(I)) < dim A` "because the closed point is missing".

## Main results

* `Stacks.LocalCohomology.topologicalKrullDim_lt_of_open_avoids_specializingPoint` — the
  topological statement.
* `Stacks.LocalCohomology.localSpectrum_open_complement_dim_lt` — its specialisation to an
  open subset of the spectrum of a local ring avoiding the closed point.
* `Stacks.LocalCohomology.specOpenComplement_toScheme_dim_lt` — the same for the scheme
  `Spec A ∖ V(I)` attached to an ideal contained in the maximal ideal.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology

/-- If `{x}` is closed, every point of `X` specializes to `x`, and `U` is an open subset
missing `x`, then the Krull dimension of `U` is strictly smaller than any natural-number bound
on the Krull dimension of `X`: a chain in `U` lifts to `X` and can be extended downwards by
`{x}`. -/
theorem topologicalKrullDim_lt_of_open_avoids_specializingPoint
    {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (x : X) (hxU : x ∉ U)
    (hclosed : IsClosed ({x} : Set X))
    (hspec : ∀ y : X, x ∈ closure ({y} : Set X))
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim U < (d : WithBot ℕ∞) := by
  change Order.krullDim (TopologicalSpace.IrreducibleCloseds U) < (d : WithBot ℕ∞)
  rw [Order.krullDim_lt_coe_iff]
  intro p
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : U → X) hU.isOpenEmbedding_subtypeVal
  let f : TopologicalSpace.IrreducibleCloseds U → TopologicalSpace.IrreducibleCloseds X :=
    fun z => (e z).val
  have hf : StrictMono f := fun _ _ hab => e.strictMono hab
  let s : TopologicalSpace.IrreducibleCloseds X :=
    ⟨{x}, isIrreducible_singleton, hclosed⟩
  have hsub (c : TopologicalSpace.IrreducibleCloseds U) : ({x} : Set X) ⊆ f c := by
    rintro _ rfl
    obtain ⟨y, hy⟩ := c.2.nonempty
    have himage : ({(y : X)} : Set X) ⊆ (Subtype.val '' (c : Set U)) :=
      Set.singleton_subset_iff.mpr ⟨y, hy, rfl⟩
    exact closure_mono himage (hspec y)
  have hne (c : TopologicalSpace.IrreducibleCloseds U) : s ≠ f c := by
    intro heq
    obtain ⟨y, hy⟩ := (e c).property
    have hy' : (y : X) ∈ (f c : Set X) := hy
    rw [← heq] at hy'
    exact hxU (Set.mem_singleton_iff.mp hy' ▸ y.property)
  have hlt (c : TopologicalSpace.IrreducibleCloseds U) : s < f c :=
    lt_of_le_of_ne (SetLike.coe_subset_coe.mpr (hsub c)) (hne c)
  let q := (p.map f hf).cons s (hlt _)
  have hq : q.length = p.length + 1 := by simp [q, LTSeries.map]
  have hqd : q.length ≤ d := by
    exact_mod_cast (Order.LTSeries.length_le_krullDim q).trans hd
  omega

/-- An open subset of the spectrum of a local ring which misses the closed point has Krull
dimension strictly below any natural-number bound on the Krull dimension of the ring. -/
theorem localSpectrum_open_complement_dim_lt
    (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞))
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U)
    (hclosedPoint : IsLocalRing.closedPoint A ∉ U) :
    topologicalKrullDim U < (d : WithBot ℕ∞) := by
  apply topologicalKrullDim_lt_of_open_avoids_specializingPoint
    U hU (IsLocalRing.closedPoint A) hclosedPoint
    (IsLocalRing.isClosed_singleton_closedPoint A)
    (fun y => (IsLocalRing.specializes_closedPoint y).mem_closure)
  simpa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using hd

/-- **The dimension input of Stacks 0DXC.** For a local ring `A` and an ideal `I` contained in
the maximal ideal, the open subscheme `Spec A ∖ V(I)` has Krull dimension strictly below any
natural-number bound on `dim A`, because `V(I)` contains the closed point. -/
theorem specOpenComplement_toScheme_dim_lt
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hIm : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim (Scheme.Opens.toScheme (X := Spec (.of A))
      ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩) < (d : WithBot ℕ∞) := by
  let U : (Spec (.of A)).Opens := ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩
  have eu : U.toScheme ≃ₜ U :=
    U.ι.isOpenEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (by simp))
  rw [IsHomeomorph.topologicalKrullDim_eq _ eu.isHomeomorph]
  exact localSpectrum_open_complement_dim_lt A d hd (U : Set (Spec (.of A))) U.2
    fun hx => hx ((PrimeSpectrum.mem_zeroLocus _ _).mpr hIm)

end Stacks.LocalCohomology

end

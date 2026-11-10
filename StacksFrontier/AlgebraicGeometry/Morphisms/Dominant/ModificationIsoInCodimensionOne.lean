module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup

/-!
# A modification of a normal scheme is an isomorphism in codimension one

Let `h : Y ⟶ X` be a modification of a normal integral locally Noetherian scheme `X`. Then `h` is
an isomorphism over an open `V ⊆ X` containing every point `x` with `dim 𝒪_{X,x} ≤ 1`.

## The argument

The locus of `Y` where the fibre of `h` has local dimension `0` is open ([Stacks, Tag 02FZ]); its
complement is closed, and `h` is proper, so the image `B` of that complement is closed. Over
`V = X ∖ B` every fibre of `h` is zero-dimensional, so `h ∣_ V` is finite
([Stacks, Tag 02OH]), hence an isomorphism, being finite birational onto the normal scheme `V`
([Stacks, Tag 0AB1]). Over a point `x` with `dim 𝒪_{X,x} ≤ 1` the fibre is zero-dimensional
because the generic fibre is a single point ([Stacks, Tag 0B2I]), so `x ∈ V`.

## Main results

* `AlgebraicGeometry.IsModification.exists_isIso_morphismRestrict_of_isNormal`: the statement
  above.

## References

* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 0B2I](https://stacks.math.columbia.edu/tag/0B2I)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Over a point whose local ring has dimension at most one, the fibre of a birational morphism
of finite type out of an integral scheme has local dimension zero at every point. -/
theorem topologicalKrullDimAt_fiber_le_zero_of_ringKrullDim_stalk_le_one {X Y : Scheme.{u}}
    [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian X] (h : Y ⟶ X) [LocallyOfFiniteType h]
    (hh : IsBirational h) (y : Y) (hy : ringKrullDim (X.presheaf.stalk (h y)) ≤ 1) :
    topologicalKrullDimAt (h.fiber (h y)) (h.asFiber y) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  refine le_of_eq (topologicalKrullDimAt_fiber_eq_of_target_dim_le_one h y inferInstance hy 0
    fun η hη _ => ?_)
  obtain rfl : η = genericPoint Y := by
    rw [irreducibleComponents_eq_singleton] at hη
    exact IsGenericPoint.eq (by simpa [IsGenericPoint] using hη) (genericPoint_spec Y)
  simpa using topologicalKrullDimAt_fiber_genericPoint_eq_zero h hh

/-- **A modification of a normal scheme is an isomorphism over an open containing every point of
codimension at most one.** -/
theorem IsModification.exists_isIso_morphismRestrict_of_isNormal {X Y : Scheme.{u}}
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] (h : Y ⟶ X) (hh : IsModification h) :
    ∃ V : X.Opens, IsIso (h ∣_ V) ∧
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V := by
  have := hh.isProper
  have := hh.source_isIntegral
  set G : Set Y := {y : Y |
    topologicalKrullDimAt (h.fiber (h y)) (h.asFiber y) ≤ ((0 : ℕ) : WithBot ℕ∞)}
  let V : X.Opens := ⟨(h '' Gᶜ)ᶜ,
    (h.isClosedMap _ (isOpen_setOf_fiberDimensionAt_le h 0).isClosed_compl).isOpen_compl⟩
  have hmemV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V := by
    rintro x hx ⟨y, hyG, rfl⟩
    exact hyG (topologicalKrullDimAt_fiber_le_zero_of_ringKrullDim_stalk_le_one h
      hh.isBirational y hx)
  refine ⟨V, ?_, hmemV⟩
  have hgenV : genericPoint X ∈ V := hmemV _ (by
    change ringKrullDim X.functionField ≤ 1
    rw [ringKrullDim_eq_zero_of_field]
    exact zero_le_one)
  have : Nonempty V := ⟨⟨_, hgenV⟩⟩
  have : Nonempty (h ⁻¹ᵁ V) :=
    ⟨⟨genericPoint Y, by
      change h (genericPoint Y) ∈ V
      rwa [IsBirational.genericPoint_eq h hh.isBirational]⟩⟩
  -- Every fibre of `h ∣_ V` is zero-dimensional.
  have hdim : ∀ v : V.toScheme,
      topologicalKrullDim ((h ∣_ V).fiber v) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    intro v
    rw [topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun z => ?_
    set w := (h ∣_ V).fiberι v z
    have hx : (h ∣_ V) w = v :=
      Set.mem_singleton_iff.mp (Set.mem_preimage.mp ((h ∣_ V).fiberHomeo v z).2)
    have hpoint : fiberHomeomorphOfEq (h ∣_ V) hx ((h ∣_ V).asFiber w) = z := by
      refine ((h ∣_ V).fiberι v).isEmbedding.injective ?_
      rw [fiberι_fiberHomeomorphOfEq]
      simp [Scheme.Hom.fiberι_asFiber, w]
    rw [← topologicalKrullDimAt_eq_localKrullDim, ← hpoint,
      ← topologicalKrullDimAt_eq_of_homeomorph (fiberHomeomorphOfEq (h ∣_ V) hx),
      fiberDimensionAt_eq_of_open_square (h ⁻¹ᵁ V).ι h (h ∣_ V) V.ι (morphismRestrict_ι h V).symm w]
    by_contra hw
    exact (w.2 : h w.1 ∈ V) ⟨w.1, hw, rfl⟩
  have : IsFinite (h ∣_ V) :=
    isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero _ hdim
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal _
    (hh.isBirational.morphismRestrict V)

end AlgebraicGeometry

end

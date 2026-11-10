module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Closed points of a product of schemes locally of finite type over a field

Let `K` be a field and `X`, `Y` schemes locally of finite type over `K`. A point `z` of
`X ×_K Y` is closed if and only if both of its images in `X` and in `Y` are closed. The proof of
[Stacks, Tag 0F1H] uses this in the form: *"a point `z` of `X ×_K Y` is a closed point if and only
if both the image of `z` in `X` and in `Y` are closed."*

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_isFinite_of_subsingleton` — every point of a scheme
  finite over a one-point scheme is closed.
* `AlgebraicGeometry.isClosed_singleton_pullback_iff` — the equivalence.

## The proof

One direction is [Stacks, Tag 01TB]: a morphism locally of finite type to a Jacobson scheme maps
closed points to closed points. Conversely, if `x` and `y` are closed, then `Spec κ(x) ⟶ X` and
`Spec κ(y) ⟶ Y` are closed immersions finite over `K`, and `z` lies in the image of the fibre
product `P = Spec κ(x) ×_K Spec κ(y)`. The scheme `P` is finite over the point `Spec κ(x)`, so its
topology is discrete, and the morphism `P ⟶ X ×_K Y` is locally of finite type, so it maps the
closed points of `P` to closed points.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K))
  (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f] [LocallyOfFiniteType g]

/-- A point of a scheme finite over a scheme with one point, such as the spectrum of a field, is
closed. -/
theorem isClosed_singleton_of_isFinite_of_subsingleton {S P : Scheme.{u}} [Subsingleton S]
    (π : P ⟶ S) [IsFinite π] (t : P) : IsClosed ({t} : Set P) := by
  have hd := π.isDiscrete_preimage_singleton (π t)
  have huniv : π ⁻¹' {π t} = Set.univ := Set.eq_univ_of_forall fun s =>
    Subsingleton.elim (α := S) (π s) (π t)
  rw [huniv] at hd
  have : DiscreteTopology P := by
    have := hd.to_subtype
    exact (Homeomorph.Set.univ P).symm.isEmbedding.discreteTopology
  exact isClosed_discrete _

/-- The residue field of a closed point of a scheme locally of finite type over a field is a closed
immersion, finite over the field. -/
private theorem isClosedImmersion_and_isFinite_fromSpecResidueField {x : X}
    (hx : IsClosed ({x} : Set X)) :
    IsClosedImmersion (X.fromSpecResidueField x) ∧ IsFinite (X.fromSpecResidueField x ≫ f) := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  exact ⟨this, isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance⟩

/-- A point of `X ×_K Y` whose images in `X` and in `Y` are closed is closed. -/
theorem isClosed_singleton_of_isClosed_singleton_fst_snd (z : ↥(pullback f g))
    (hx : IsClosed ({pullback.fst f g z} : Set X))
    (hy : IsClosed ({pullback.snd f g z} : Set Y)) : IsClosed ({z} : Set ↥(pullback f g)) := by
  have : JacobsonSpace ↥(pullback f g) := LocallyOfFiniteType.jacobsonSpace (pullback.fst f g ≫ f)
  let ix := X.fromSpecResidueField (pullback.fst f g z)
  let iy := Y.fromSpecResidueField (pullback.snd f g z)
  obtain ⟨_, _⟩ := isClosedImmersion_and_isFinite_fromSpecResidueField f hx
  obtain ⟨_, _⟩ := isClosedImmersion_and_isFinite_fromSpecResidueField g hy
  let m := pullback.map (ix ≫ f) (iy ≫ g) f g ix iy (𝟙 _) (by simp) (by simp)
  obtain ⟨t, htz⟩ : z ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    exact ⟨by simp [ix, Scheme.range_fromSpecResidueField],
      by simp [iy, Scheme.range_fromSpecResidueField]⟩
  have : IsFinite (pullback.fst (ix ≫ f) (iy ≫ g)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (ix ≫ f) (iy ≫ g)).flip
      (inferInstanceAs (IsFinite (iy ≫ g)))
  have : LocallyOfFiniteType (m ≫ pullback.fst f g ≫ f) := by
    rw [pullback.lift_fst_assoc]
    infer_instance
  have : LocallyOfFiniteType m := locallyOfFiniteType_of_comp m (pullback.fst f g ≫ f)
  rw [← htz]
  exact m.closedPoints_subset_preimage_closedPoints
    (isClosed_singleton_of_isFinite_of_subsingleton (pullback.fst (ix ≫ f) (iy ≫ g)) t)

/-- **A point of `X ×_K Y` is closed if and only if its images in `X` and in `Y` are closed**,
for `X` and `Y` locally of finite type over a field `K`. -/
theorem isClosed_singleton_pullback_iff (z : ↥(pullback f g)) :
    IsClosed ({z} : Set ↥(pullback f g)) ↔
      IsClosed ({pullback.fst f g z} : Set X) ∧ IsClosed ({pullback.snd f g z} : Set Y) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace g
  exact ⟨fun hz => ⟨(pullback.fst f g).closedPoints_subset_preimage_closedPoints hz,
    (pullback.snd f g).closedPoints_subset_preimage_closedPoints hz⟩,
    fun ⟨hx, hy⟩ => isClosed_singleton_of_isClosed_singleton_fst_snd f g z hx hy⟩

end AlgebraicGeometry

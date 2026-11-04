module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Quasi-finiteness along one fibre

A finite-type morphism is quasi-finite only at finitely many points of any one fibre: the fibre
is a Noetherian space, so its isolated points form a compact discrete, hence finite, set.

Over a generic point of an irreducible component the situation is sharper still. There the
fibre consists of generic points of the source exactly when the morphism is quasi-finite at
every point of the fibre, and it is enough to test quasi-finiteness at the generic points of the
fibre — the other points are dominated by those.

## Main results

* `AlgebraicGeometry.finite_setOf_mapsTo_and_quasiFiniteAt` states that the quasi-finite points
  in a fixed fibre of a finite-type morphism form a finite set.
* `AlgebraicGeometry.quasiFiniteAt_over_genericPoint_tfae` gives the three equivalent conditions
  over a generic point.

## Implementation notes

Following Mathlib's convention, the finite-type hypothesis is represented by the two typeclasses
`AlgebraicGeometry.LocallyOfFiniteType f` and `AlgebraicGeometry.QuasiCompact f`. The fibre is
expressed as the set of points `x` satisfying `f x = s`. Mathlib's `genericPoints` is the set of
generic points of irreducible components, and the three numbered conditions of the second result
are recorded in their original order using `List.TFAE`.

## References

* [Stacks Project, Tag 0AAY](https://stacks.math.columbia.edu/tag/0AAY)
* [Stacks Project, Tag 0BAH](https://stacks.math.columbia.edu/tag/0BAH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For a finite-type morphism of schemes, the set of points over a fixed point at which the
morphism is quasi-finite is finite. -/
@[stacks 0AAY]
public theorem finite_setOf_mapsTo_and_quasiFiniteAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (s : S) :
    {x : X | f x = s ∧ quasiFiniteAt f x}.Finite := by
  let _ : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s)))
  let _ : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  let _ : IsNoetherian (f.fiber s) := { }
  have hfinite : {x : f.fiber s | IsIsolatedPoint x}.Finite :=
    (TopologicalSpace.NoetherianSpace.isCompact _).finite
      (isDiscrete_iff_forall_mem_exists_isOpen.mpr fun x hx =>
        ⟨{x}, (isIsolatedPoint_iff x).mp hx, by simp [hx]⟩)
  apply (hfinite.image (f.fiberι s)).subset
  rintro x ⟨hxs, hxqf⟩
  subst s
  exact ⟨f.asFiber x, ((quasiFiniteAt_tfae f x).out 1 2).mp hxqf,
    by simp [Scheme.Hom.asFiber]⟩

/-- Points of the fibre `f.fiber y` map to `y`. -/
private lemma apply_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    f (f.fiberι y z) = y :=
  (f.fiberHomeo y z).2

/-- A point of the fibre over `f x` whose image is `x` is the canonical point `f.asFiber x`. -/
private lemma eq_asFiber_of_fiberι_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    {z : f.fiber (f x)} (h : f.fiberι (f x) z = x) : z = f.asFiber x :=
  (f.fiberι (f x)).isEmbedding.injective (by simpa using h)

/-- A generic point of the fibre over a generic point of the target is a generic point of the
source. -/
private lemma genericPoints_fiber_maps_to_genericPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y) (hη : η ∈ genericPoints Y)
    (z : f.fiber η) (hz : z ∈ genericPoints (f.fiber η)) :
    f.fiberι η z ∈ genericPoints X := by
  rw [mem_genericPoints_iff_forall_specializes_eq]
  intro x' hx'
  have hfx' : f x' = η := by
    apply (mem_genericPoints_iff_forall_specializes_eq η).mp hη
    simpa only [apply_fiberι] using hx'.map f.continuous
  let z' : f.fiber η := (f.fiberHomeo η).symm ⟨x', hfx'⟩
  have hz'z : Specializes z' z := by
    have hs : Specializes (⟨x', hfx'⟩ : f ⁻¹' {η}) ((f.fiberHomeo η) z) := hx'
      |> (Topology.IsInducing.subtypeVal.specializes_iff).mp
    simpa [z'] using hs.map (f.fiberHomeo η).symm.continuous
  have hz'eq : z' = z :=
    (mem_genericPoints_iff_forall_specializes_eq z).mp hz z' hz'z
  rw [← hz'eq]
  exact (f.fiberι_fiberHomeo_symm η ⟨x', hfx'⟩).symm

/-- For a locally finite type morphism, the fibre over a generic point consists of generic
points if and only if the morphism is quasi-finite at every point of the fibre, equivalently
if it is quasi-finite at every generic point of the fibre. -/
@[stacks 0BAH]
public theorem quasiFiniteAt_over_genericPoint_tfae {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (η : Y) (hη : η ∈ genericPoints Y) :
    List.TFAE [
      f ⁻¹' {η} ⊆ genericPoints X,
      ∀ x : X, f x = η → quasiFiniteAt f x,
      ∀ ξ : X, ξ ∈ genericPoints X → f ξ = η → quasiFiniteAt f ξ] := by
  tfae_have 1 → 2 := by
    intro h x hx
    have hxgen : x ∈ genericPoints X := h hx
    apply (quasiFiniteAt_tfae f x).out 3 1 |>.mp
    constructor
    · rw [← closure_subset_iff_isClosed]
      intro z hz
      rw [Set.mem_singleton_iff]
      have hzspec : Specializes (f.asFiber x) z :=
        specializes_iff_mem_closure.mpr hz
      have hzgen : f.fiberι (f x) z ∈ genericPoints X :=
        h ((apply_fiberι f _ z).trans hx)
      have := (mem_genericPoints_iff_forall_specializes_eq _).mp hzgen x
        (by simpa using hzspec.map (f.fiberι (f x)).continuous)
      exact eq_asFiber_of_fiberι_eq f this.symm
    · rintro ⟨z, hz_ne, hzspec⟩
      exact hz_ne <| eq_asFiber_of_fiberι_eq f <|
        (mem_genericPoints_iff_forall_specializes_eq x).mp hxgen _
          (by simpa using hzspec.map (f.fiberι (f x)).continuous)
  tfae_have 2 → 3 := by aesop
  tfae_have 3 → 1 := by
    intro h x hx
    obtain ⟨z, rfl⟩ := f.range_fiberι η ▸ hx
    let C : irreducibleComponents (f.fiber η) :=
      ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
    let ξ : f.fiber η := genericPoints.ofComponent C
    have hξgenX : f.fiberι η ξ ∈ genericPoints X :=
      genericPoints_fiber_maps_to_genericPoints f η hη ξ (genericPoints.ofComponent C).2
    have hmapξ : f (f.fiberι η ξ) = η := apply_fiberι f η ξ
    have ⟨hclosed, _⟩ :
        IsClosed ({f.asFiber (f.fiberι η ξ)} : Set (f.fiber (f (f.fiberι η ξ)))) ∧
        (¬ ∃ x' : f.fiber (f (f.fiberι η ξ)), x' ≠ f.asFiber (f.fiberι η ξ) ∧
          x' ⤳ f.asFiber (f.fiberι η ξ)) :=
      ((quasiFiniteAt_tfae f (f.fiberι η ξ)).out 1 3).mp
        (h (f.fiberι η ξ) hξgenX hmapξ)
    let z' : f.fiber (f (f.fiberι η ξ)) := (f.fiberHomeo _).symm
      ⟨f.fiberι η z, (apply_fiberι f η z).trans hmapξ.symm⟩
    have hz'spec : Specializes (f.asFiber (f.fiberι η ξ)) z' := by
      apply Specializes.map _ (f.fiberHomeo _).symm.continuous
      apply (Topology.IsInducing.subtypeVal.specializes_iff).mp
      simpa only [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber,
        Scheme.Hom.fiberι_fiberHomeo_symm] using
        ((genericPoints.isGenericPoint_ofComponent C).specializes
          mem_irreducibleComponent).map (f.fiberι η).continuous
    have huz : f.fiberι η z = f.fiberι η ξ := by
      have := congrArg (f.fiberι (f (f.fiberι η ξ)))
        (Set.mem_singleton_iff.mp (hz'spec.mem_closed hclosed (Set.mem_singleton _)))
      simpa [z'] using this
    exact huz ▸ hξgenX
  tfae_finish

end AlgebraicGeometry

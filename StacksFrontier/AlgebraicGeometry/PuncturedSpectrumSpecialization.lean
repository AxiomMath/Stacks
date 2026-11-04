module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Immediate generalizations inside a locally closed set

On a locally Noetherian scheme `X`, fix a point `x` and a locally closed set `E` containing some
point `w ≠ x` with `w ⤳ x`. Then `E` already contains an *immediate* generalization of `x`: a
point `y ∈ E` with `y ⤳ x` admitting no intermediate point.

## Main results

* `AlgebraicGeometry.exists_isImmediateSpecialization_mem_of_isLocallyClosed`: the immediate
  generalization inside `E`.

## References

* [Stacks Project, Tag 02IM](https://stacks.math.columbia.edu/tag/02IM)
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A locally closed subset of a locally Noetherian scheme which contains a nontrivial
generalization `w` of a point `x` contains an immediate generalization of `x`. -/
theorem exists_isImmediateSpecialization_mem_of_isLocallyClosed
    (X : Scheme.{u}) [IsLocallyNoetherian X] {x w : X} {E : Set X}
    (hE : IsLocallyClosed E) (hw : w ∈ E) (hwx : w ⤳ x) (hne : w ≠ x) :
    ∃ y ∈ E, IsImmediateSpecialization y x := by
  let R := X.presheaf.stalk x
  let f := X.fromSpecStalk x
  let m : PrimeSpectrum R := IsLocalRing.closedPoint R
  let S : Set (PrimeSpectrum R) := ({m} : Set (PrimeSpectrum R))ᶜ
  have : IsNoetherianRing R := inferInstance
  have : JacobsonSpace ↥S := PrimeSpectrum.jacobsonSpace_compl_closedPoint R
  have hm : f m = x := Scheme.fromSpecStalk_closedPoint
  obtain ⟨t, ht⟩ : w ∈ Set.range f := by
    rw [Scheme.range_fromSpecStalk]
    exact hwx
  have htm : t ≠ m := fun e => hne (ht.symm.trans ((congrArg f e).trans hm))
  let V : Set S := Subtype.val ⁻¹' (f ⁻¹' E)
  have hVlc : IsLocallyClosed V :=
    (hE.preimage f.continuous).preimage continuous_subtype_val
  have hVne : V.Nonempty := by
    refine ⟨⟨t, htm⟩, ?_⟩
    show f t ∈ E
    exact ht ▸ hw
  obtain ⟨z, hzV, hzclosed⟩ := nonempty_inter_closedPoints (X := ↥S) hVne hVlc
  let z₀ : PrimeSpectrum R := z.1
  have hzS : z₀ ∈ S := z.2
  have hzm : z₀ ≠ m := hzS
  have hzclosed' : IsClosed ({z} : Set S) := hzclosed
  have hzE : f z₀ ∈ E := hzV
  have hno_intermediate : ∀ v : PrimeSpectrum R, z₀ ⤳ v → v ≠ m → v = z₀ := by
    intro v hzv hvm
    have hvS : v ∈ S := hvm
    let v' : S := ⟨v, hvS⟩
    have hzv' : (⟨z₀, hzS⟩ : S) ⤳ v' := (subtype_specializes_iff _ _).2 hzv
    have hvcl : v' ∈ closure ({(⟨z₀, hzS⟩ : S)} : Set S) := hzv'.mem_closure
    rw [closure_eq_iff_isClosed.mpr hzclosed'] at hvcl
    have heq : v' = (⟨z₀, hzS⟩ : S) := by simpa using hvcl
    exact congrArg Subtype.val heq
  have hrel : f z₀ ⤳ x := by
    have hz_m : z₀ ⤳ m := IsLocalRing.specializes_closedPoint z₀
    simpa only [hm] using hz_m.map f.continuous
  have hne' : f z₀ ≠ x := fun e =>
    hzm (f.isEmbedding.injective (e.trans hm.symm))
  refine ⟨f z₀, hzE, hrel, hne', ?_⟩
  intro v hyv hvx
  obtain ⟨v₀, hv₀⟩ : v ∈ Set.range f := by
    rw [Scheme.range_fromSpecStalk]
    exact hvx
  have hzv₀ : z₀ ⤳ v₀ := by
    apply (f.isEmbedding.isInducing.specializes_iff).mp
    simpa [hv₀] using hyv
  by_cases hvm : v₀ = m
  · right
    calc v = f v₀ := hv₀.symm
      _ = f m := congrArg f hvm
      _ = x := hm
  · left
    have heq := hno_intermediate v₀ hzv₀ hvm
    calc v = f v₀ := hv₀.symm
      _ = f z₀ := congrArg f heq

end AlgebraicGeometry

end

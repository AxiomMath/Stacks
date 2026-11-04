module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Weakly associated points under flat pullback

Let `f : X ⟶ S` be a morphism of schemes, let `𝒢` be an `𝒪_S`-module and let `x` be a point of
`X` at which `f` is flat and which is a generic point of its fibre. If `f x` is weakly
associated to `𝒢`, then `x` is weakly associated to `f^*𝒢`.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Divisors.IsWeaklyAssociatedPoint.pullback_of_isGenericPoint_fiber` is the statement
  above.

## Implementation notes

The point of the scheme-theoretic fibre corresponding to `x` is `f.asFiber x`, and the
hypothesis that it is generic in the fibre enters through
`radical_map_stalkMap_eq_maximalIdeal_of_generic`: the extension of the maximal ideal of
`𝒪_{S, f x}` to `𝒪_{X, x}` has radical the whole maximal ideal, because the quotient by that
extension is the local ring of the fibre at a generic point, in which every element of the
maximal ideal is nilpotent. That identification of the quotient is
`AlgebraicGeometry.quotientStalk_bridge`.

Flatness is used only through `ann_extension_eq_ann_baseChange_elem`, which computes the
annihilator of `1 ⊗ m` in a flat base change, and the stalk of the pullback is identified with
the base-changed stalk by `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`.
No quasi-coherence of the module is needed anywhere.

## References

* [Stacks Project, Tag 05F0](https://stacks.math.columbia.edu/tag/05F0)
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

namespace Stacks.Divisors

/-- Alias of `AlgebraicGeometry.maximalIdeal_isNilpotent_of_mem_genericPoints`. -/
private alias maximalIdeal_isLocallyNilpotent_of_mem_genericPoints :=
  AlgebraicGeometry.maximalIdeal_isNilpotent_of_mem_genericPoints

/-- The image of the radical of an ideal is contained in the radical of the image. -/
private lemma ideal_map_radical_le_radical_map
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) :
    Ideal.map φ I.radical ≤ (Ideal.map φ I).radical := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
  exact Ideal.mem_radical_iff.mpr ⟨n, by simpa using Ideal.mem_map_of_mem φ hn⟩

/-- Alias of `AlgebraicGeometry.annihilatorOfElem_semiring_eq_of_linearEquiv`. -/
private alias annihilator_eq_of_linearEquiv :=
  AlgebraicGeometry.annihilatorOfElem_semiring_eq_of_linearEquiv

/-- Alias of `AlgebraicGeometry.radical_map_stalkMap_maximalIdeal_eq_of_mem_genericPoints_fiber`.
-/
private alias radical_map_stalkMap_eq_maximalIdeal_of_generic :=
  AlgebraicGeometry.radical_map_stalkMap_maximalIdeal_eq_of_mem_genericPoints_fiber

open TensorProduct in
/-- The proof of Stacks 05F0, with the stalk computation done over the underlying ringed
space. -/
private lemma pullback_of_isGenericPoint_fiber_proof
    {X S : Scheme.{u}} (f : X ⟶ S) (G : S.Modules) (x : X)
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hgeneric : f.asFiber x ∈ genericPoints (f.fiber (f x)))
    (hweak : IsWeaklyAssociatedPoint G (f x)) :
    IsWeaklyAssociatedPoint ((Scheme.Modules.pullback f).obj G) x := by
  let g := f.toLRSHom.toShHom
  let A := S.presheaf.stalk (g.hom.base x)
  let B := X.presheaf.stalk x
  let φ : A →+* B := (f.stalkMap x).hom
  let : Algebra (↑A) (↑B) := φ.toAlgebra
  have : IsLocalHom φ := f.toLRSHom.prop x
  let M := ↑(TopCat.Presheaf.stalk G.val.presheaf (g.hom.base x))
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      G.val (g.hom.base x)
  change WeaklyAssociated (IsLocalRing.maximalIdeal A) M at hweak
  obtain ⟨m, hmrad⟩ :=
    (weaklyAssociated_maximalIdeal_iff_exists_radical_eq (S := A) (N := M)).mp hweak
  let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    ((RingedSpaceModuleAdjunction.modulePullback g).obj G).val
  let N := ↑(TopCat.Presheaf.stalk P'.presheaf x)
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier P' x
  let e : N ≃ₗ[B] TensorProduct A B M := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv g G x)
  let n : N := e.symm ((1 : B) ⊗ₜ[A] m)
  have : Module.Flat A B := hflat
  have hAnn :
      annihilatorOfElem_semiring (R := B) n =
        Ideal.map φ (annihilatorOfElem_semiring (R := A) m) := by
    calc
      _ = annihilatorOfElem_semiring (R := B) (e n) := annihilator_eq_of_linearEquiv e n
      _ = annihilatorOfElem_semiring (R := B) ((1 : B) ⊗ₜ[A] m) := by simp [n]
      _ = Ideal.torsionOf B (B ⊗[A] M) ((1 : B) ⊗ₜ[A] m) :=
        Ideal.annihilator_span_singleton_eq_torsionOf _
      _ = Ideal.map (algebraMap A B) (Ideal.torsionOf A M m) :=
        (ann_extension_eq_ann_baseChange_elem (R := A) (S := B) (M := M) m).symm
      _ = _ := congrArg (Ideal.map (algebraMap A B))
        (Ideal.annihilator_span_singleton_eq_torsionOf m).symm
  have hmaple := ideal_map_radical_le_radical_map φ (annihilatorOfElem_semiring (R := A) m)
  rw [hmrad] at hmaple
  have hrad :
      (annihilatorOfElem_semiring (R := B) n).radical = IsLocalRing.maximalIdeal B := by
    rw [hAnn]
    refine le_antisymm ((Ideal.radical_mono ((Ideal.map_mono
      (Ideal.le_radical.trans hmrad.le)).trans (IsLocalRing.map_maximalIdeal_le φ))).trans_eq
        (IsLocalRing.maximalIdeal.isMaximal B).isPrime.radical) ?_
    calc
      _ = (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical :=
        (radical_map_stalkMap_eq_maximalIdeal_of_generic f x hgeneric).symm
      _ ≤ _ := by simpa using Ideal.radical_mono hmaple
  change IsWeaklyAssociatedPrime B N (IsLocalRing.maximalIdeal B)
  simpa [IsWeaklyAssociatedPrime, WeaklyAssociated, annihilatorOfElem_semiring] using
    (weaklyAssociated_maximalIdeal_iff_exists_radical_eq (S := B) (N := N)).mpr ⟨n, hrad⟩

-- Keep the category's direct `Quiver` instance ahead of the `ReflQuiver` route added by
-- the proof imports, so the accepted `⟶` binder elaborates identically.
attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-- **Stacks Project, Tag 05F0.** A point which is generic in its fibre and at which a
morphism is flat is weakly associated to the pullback of a module whenever its image is weakly
associated to the original module. -/
@[stacks 05F0]
theorem IsWeaklyAssociatedPoint.pullback_of_isGenericPoint_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (G : S.Modules) (x : X)
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hgeneric : f.asFiber x ∈ genericPoints (f.fiber (f x)))
    (hweak : IsWeaklyAssociatedPoint G (f x)) :
    IsWeaklyAssociatedPoint ((Scheme.Modules.pullback f).obj G) x :=
  pullback_of_isGenericPoint_fiber_proof f G x hflat hgeneric hweak

end Stacks.Divisors

end

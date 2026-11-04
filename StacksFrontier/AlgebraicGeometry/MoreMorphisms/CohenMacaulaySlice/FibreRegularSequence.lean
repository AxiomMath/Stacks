module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence

/-!
# Lifting a maximal regular sequence of a Cohen–Macaulay fibre to the source

Let `f : X ⟶ S` be a morphism of schemes with locally Noetherian fibres and let `x : X` be a
point at which `f` is Cohen–Macaulay.  The local ring of the fibre through `x` then carries a
regular sequence whose length is its Krull dimension, and because the fibre inclusion is
surjective on stalks that sequence lifts to a family of germs at `x` on `X`.

## Main results

* `Stacks.AlgebraicGeometry.exists_lift_fibre_isRegular_of_isCohenMacaulayLocalRing`: a family
  of germs at `x` whose length is the Krull dimension of the fibre's local ring and whose image in
  that local ring is a regular sequence.

## Implementation notes

The sequence in the fibre comes from `exists_isRegular_length_eq_depth_of_cohenMacaulay`, whose
length is the depth; Cohen–Macaulayness is exactly the statement that the depth agrees with
`Module.supportDim`, which is the Krull dimension by `Module.supportDim_self_eq_ringKrullDim`.

The lift is a family `Fin r → 𝒪_{X, x}`; a germ at `x` is transported to a germ at the image of
the fibre point by the dependent rewrite along `Scheme.Hom.fiberι_asFiber`.

## References

* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry

/-- Transporting a germ along an equality of points and back is the identity. -/
theorem cast_symm_cast_eq {α : Sort*} {β : α → Sort*} {a b : α} (h : a = b) (y : β a) :
    h.symm ▸ (h ▸ y) = y := by
  cases h
  rfl

/-- Two successive transports of a germ along equalities of points compose. -/
theorem cast_cast_eq {α : Sort*} {β : α → Sort*} {a b c : α} (h : a = b) (g : b = c) (y : β a) :
    g ▸ (h ▸ y) = h.trans g ▸ y := by
  cases h
  cases g
  rfl

/-- **A maximal regular sequence of a Cohen–Macaulay fibre lifts to germs on the source.**  If
the local ring of the fibre of `f` through `x` is Cohen–Macaulay, there is a family of germs of
`𝒪_X` at `x` whose image in that local ring is a regular sequence of length its Krull
dimension. -/
theorem exists_lift_fibre_isRegular_of_isCohenMacaulayLocalRing {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y))
    (hCM : letI := hf (f x)
      IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    ∃ (r : ℕ) (h : Fin r → X.presheaf.stalk x),
      (r : WithBot ℕ∞) = ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ∧
        RingTheory.Sequence.IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
          (List.ofFn fun i : Fin r =>
            ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
              ((f.fiberι_asFiber x).symm ▸ h i)) := by
  classical
  let _ := hf (f x)
  set R := (f.fiber (f x)).presheaf.stalk (f.asFiber x)
  obtain ⟨ss, -, hssreg, hsslen⟩ := exists_isRegular_length_eq_depth_of_cohenMacaulay hCM
  have hdepth : (Module.depthSup R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) =
      ringKrullDim R := by
    rwa [← Module.supportDim_self_eq_ringKrullDim]
  have hssdim : (ss.length : WithBot ℕ∞) = ringKrullDim R :=
    (congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hsslen).trans hdepth
  choose h₀ hh₀ using fun i => (f.fiberι (f x)).stalkMap_surjective (f.asFiber x) (ss.get i)
  refine ⟨ss.length, fun i => f.fiberι_asFiber x ▸ h₀ i, hssdim, ?_⟩
  have hfun : (fun i : Fin ss.length =>
      ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((f.fiberι_asFiber x).symm ▸ (f.fiberι_asFiber x ▸ h₀ i))) = ss.get := by
    funext i
    rw [cast_symm_cast_eq (β := fun z => ↑(X.presheaf.stalk z)) (f.fiberι_asFiber x) (h₀ i)]
    exact hh₀ i
  rwa [hfun, List.ofFn_get]

end Stacks.AlgebraicGeometry

end

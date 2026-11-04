module

public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic

/-!
# The support of the defining ideal of a strict transform

Let `f : X ⟶ S` be a morphism of schemes, let `b : S' ⟶ S` be another one and let `E` be a
quasi-coherent ideal sheaf on `S'` — for a blowup, its exceptional ideal. The strict transform of
`X` is the closed subscheme of `X ×_S S'` cut out by `Stacks.StrictTransform.ideal f b E`, the
ideal of sections supported on the exceptional preimage `pr_{S'}^{-1}(Supp E)`.

That ideal is the kernel of the inclusion of the open complement of the exceptional preimage
(`Stacks.StrictTransform.ideal_eq_ker_ι`), so the strict transform is the scheme-theoretic image
of that open. Consequently its support — the underlying closed subset of the strict transform — is
exactly the closure of the complement of the exceptional preimage. In particular the strict
transform contains every point off the exceptional preimage, and is contained in the closure of
their set; both inclusions are used when comparing strict transforms of different subschemes
inside one blowup.

## Main results

* `Stacks.StrictTransform.support_ideal`: the support of the defining ideal of the strict
  transform is the closure of the complement of the exceptional preimage.
* `Stacks.StrictTransform.mem_support_ideal_of_notMem_exceptionalPreimage`: a point off the
  exceptional preimage lies in the strict transform.
* `Stacks.StrictTransform.support_ideal_subset_closure_compl_exceptionalPreimage`: the strict
  transform is contained in the closure of the complement of the exceptional preimage.

## Implementation notes

The quasi-compactness hypothesis `QuasiCompact (exceptionalComplement f b E).ι` is the one
`Stacks.StrictTransform.ideal_eq` already asks for; it is supplied by
`Stacks.StrictTransform.quasiCompact_exceptionalComplement_ι` as soon as the complement of
`Supp E` has quasi-compact inclusion into `S'`, which for a blowup is
`Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal`. It is needed because the
support of a kernel is the closure of the range only for a quasi-compact morphism
(`AlgebraicGeometry.Scheme.Hom.support_ker`).

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.StrictTransform

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (b : S' ⟶ S) (E : S'.IdealSheafData)
  [QuasiCompact (exceptionalComplement f b E).ι]

/-- **The strict transform is the closure of the part of the base change away from the
exceptional preimage.** The defining ideal of the strict transform is the kernel of the inclusion
of the open complement of `pr_{S'}^{-1}(Supp E)`, and the support of a kernel of a quasi-compact
morphism is the closure of its range. -/
theorem support_ideal :
    ((ideal f b E).support : Set (baseChange f b)) =
      closure ((exceptionalPreimage f b E)ᶜ) := by
  rw [ideal_eq_ker_ι, Scheme.Hom.support_ker, Scheme.Opens.range_ι, exceptionalPreimage_eq_compl,
    compl_compl]

/-- **Every point off the exceptional preimage lies in the strict transform.** On the complement
of `pr_{S'}^{-1}(Supp E)` the quotient defining the strict transform changes nothing, so no
section of the defining ideal can be a unit there. -/
theorem mem_support_ideal_of_notMem_exceptionalPreimage {x : baseChange f b}
    (hx : x ∉ exceptionalPreimage f b E) :
    x ∈ ((ideal f b E).support : Set (baseChange f b)) := by
  rw [support_ideal]
  exact subset_closure hx

/-- **The strict transform is contained in the closure of the complement of the exceptional
preimage.** It is the scheme-theoretic image of that complement. -/
theorem support_ideal_subset_closure_compl_exceptionalPreimage :
    ((ideal f b E).support : Set (baseChange f b)) ⊆
      closure ((exceptionalPreimage f b E)ᶜ) :=
  (support_ideal f b E).le

end Stacks.StrictTransform

end

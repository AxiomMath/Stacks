module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Logic.Function.Basic

/-!
# A comparison of two extensions with the same ends is bijective

Tag 040Q identifies the group of pairs `(ℒ, α)` with `H¹(S, μ_n)`. Both groups sit in an exact
sequence whose left end is the global units modulo `n`-th powers and whose right end is the
`n`-torsion of the Picard group, and the identification is a homomorphism compatible with both
ends. This file isolates the purely group-theoretic step: such a homomorphism is bijective.

The shape is the one both sides actually come in. On the left there is no quotient group but a
*set* `U` — the global units — mapping to both groups, so the left-hand exactness is stated as
"a class killed by the right-hand map comes from `U`" together with "an element of `U` whose
cohomology class vanishes has vanishing pair class". On the right there is no subgroup but the
statement that every element in the image of one right-hand map is in the image of the other.

## Main results

* `Stacks.Kummer.bijective_of_comparison`: the comparison homomorphism is bijective.

## Implementation notes

The two "ends" are not assumed to be groups and the two maps out of `U` are not assumed to be
homomorphisms: only the four implications below are used, and each of them is a statement the
Kummer long exact sequence and the pair calculus of Tag 040P supply directly. In particular no
five-lemma from homological algebra is invoked, and nothing is assumed about the orders of the
groups.

## References

* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace Stacks.Kummer

variable {A : Type u₁} {H : Type u₂} {P : Type u₃} {U : Type u₄}
  [AddCommGroup A] [AddCommGroup H] [AddCommGroup P]

/-- **A comparison of two extensions with the same ends is bijective.**

`c` is the comparison, `q` and `r` are the two maps to the common right end, `i` and `d` the two
maps from the common left end. The hypotheses are: `c` is compatible with the right end
(`hrc`) and with the left end (`hci`); an element of `A` killed by `q` comes from `U` (`hker`);
an element of `U` killed by `d` is killed by `i` (`hinj`); an element of `H` killed by `r` comes
from `U` (`hkerH`); and every element in the image of `r` is in the image of `q` (`himg`). -/
theorem bijective_of_comparison (c : A →+ H) (q : A →+ P) (r : H →+ P)
    (i : U → A) (d : U → H)
    (hrc : ∀ a : A, r (c a) = q a) (hci : ∀ u : U, c (i u) = d u)
    (hker : ∀ a : A, q a = 0 → ∃ u : U, i u = a)
    (hinj : ∀ u : U, d u = 0 → i u = 0)
    (hkerH : ∀ y : H, r y = 0 → ∃ u : U, d u = y)
    (himg : ∀ y : H, ∃ a : A, q a = r y) :
    Function.Bijective c := by
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have hz : c (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨u, hu⟩ := hker (a - b) (by rw [← hrc, hz, map_zero])
    rw [← sub_eq_zero, ← hu, hinj u (by rw [← hci, hu, hz])]
  · obtain ⟨a, ha⟩ := himg y
    obtain ⟨u, hu⟩ := hkerH (y - c a) (by rw [map_sub, hrc, ha, sub_self])
    exact ⟨a + i u, by rw [map_add, hci, hu, add_comm, sub_add_cancel]⟩

end Stacks.Kummer

end

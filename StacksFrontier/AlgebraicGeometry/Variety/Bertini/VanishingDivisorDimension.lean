module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionEquality
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingFamilyDivisorsOnX

/-!
# The dimension of the divisor of a member of the vanishing system

For the Bertini step of Stacks Tag 0FH7, a nonzero `w ∈ V_n` cuts out a divisor `H_w ⊆ X`.
The induction on `dim X` that step feeds has to treat `H_w` as a variety in its own right, and
for that it needs the *dimension* of `H_w`: if `dim X = d + 1` then `dim H_w = d`. This file
supplies that.

The dimension of `H_w` is the first of the three reasons
`Stacks.WeilCohomology.BertiniDivisorReduction` is carried as a hypothesis rather than derived,
and this file removes that reason; the other two — the Bertini input package not being
reconstructible from the inductive hypothesis, and the library's Bertini step assuming `k`
algebraically rather than separably closed — remain.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.isEffectiveCartierDivisor_divisorOnX`: `H_w` is an
  effective Cartier divisor on an integral `X`.
* `Stacks.SectionsVanishingOnSubscheme.topologicalKrullDim_divisorOnX_eq`: `dim H_w = d` when
  `dim X = d + 1`.

## The argument

`Stacks.Bertini.FamilyDivisors.divisor` is by definition the zero scheme of
`Stacks.Bertini.FamilyDivisors.sectionOf`, and for `familyDivisorsOnX` the scheme is `X`, the
module is `ℒ ^⊗ n` and the section of `w` is `w` itself; so `H_w` is literally `Z(w)`, with no
transport. On an integral scheme a nonzero global section of an invertible module is a
nonzerodivisor, so `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero` makes
`Z(w)` an effective Cartier divisor, and then
`Stacks.Chow.topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor_field` computes its
dimension.

## The hypotheses, and where each is consumed

Beyond the standing situation:

* `IsIntegral X`. Consumed twice: to make `w` a nonzerodivisor section, which is what
  `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero` needs, and again in the
  dimension equality, where the generic point of `X` is where the delta-dimension is read.
  Both Bertini results on `H_w` in the library already assume it.
* `LocallyOfFiniteType f`. What makes the relative dimension of [Stacks, Tag 02JW] a dimension
  function on `X`, which is the dimension theory the equality runs on. In the Bertini situation
  it is free from `Smooth f`, but it is the weaker hypothesis and so is the one asked for.
* `w ≠ 0`. The zero section has `Z(0) = X`, which is not a divisor at all. This is the
  hypothesis `Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair`
  already produces alongside the smoothness.
* `Nonempty H_w`. **Not removable, and not supplied here.** An effective Cartier divisor may be
  empty — the unit section cuts out the empty subscheme — and then `dim H_w = ⊥`, not `d`. On a
  proper `X` with `ℒ ^⊗ n` ample the divisor of a nonzero section *is* nonempty, but that is a
  statement about ampleness which this library does not have in the shape needed, so it is
  carried as an instance argument rather than derived. A discharge of
  `Stacks.WeilCohomology.BertiniDivisorReduction` still owes it.

No dimension *bound* on `X` is required: unlike
`Stacks.SectionsVanishingOnSubscheme.geometricallyIrreducible_divisorOnX_of_isAmple`, which needs
`dim X ≥ 2` through the depth condition of [Stacks, Tag 0FD9], the dimension equality holds in
every dimension. Nor is ampleness of `ℒ ^⊗ n`, properness of `f` or smoothness of `f` used.

## References

* Stacks Project, Tag 0FH7 — the Bertini step this serves; its induction is
  `Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne`.
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample
open Stacks.Chow Stacks.Divisors

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] (n : ℤ)
  [FiniteDimensional k (Stacks.Bertini.globalSections k f (tensorPowModule X L n))]
  [FiniteDimensional k (vanishingSections k f I L n)]

omit [FiniteDimensional k (vanishingSections k f I L n)] in
/-- **The divisor on `X` of a nonzero member of `V_n` is an effective Cartier divisor**, for `X`
integral.

`H_w` is the zero scheme of `w` as a section of `ℒ ^⊗ n`, and on an integral scheme a nonzero
global section of an invertible module is a nonzerodivisor ([Stacks, Tag 01WY]); the zero scheme
of such a section is an effective Cartier divisor. No ampleness, properness or smoothness is
used.

The invertibility of `ℒ ^⊗ n` in the spelling the zero-scheme theory asks for is the
`isInvertible` field of the standing situation, so it is read off
`familyDivisorsOnX` rather than re-derived. -/
theorem isEffectiveCartierDivisor_divisorOnX [AlgebraicGeometry.IsIntegral X]
    (w : vanishingSections k f I L n) (hw : w ≠ 0) :
    IsEffectiveCartierDivisor ((familyDivisorsOnX k f I (L := L) n).divisor w) := by
  have hinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L n) := (familyDivisorsOnX k f I (L := L) n).isInvertible
  exact AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero
    (tensorPowModule X L n) ((familyDivisorsOnX k f I (L := L) n).sectionOf w)
    (fun h => hw (Submodule.coe_eq_zero.mp h))

omit [FiniteDimensional k (vanishingSections k f I L n)] in
/-- **The divisor on `X` of a nonzero member of `V_n` has dimension one less than `X`**: if
`dim X = d + 1` then `dim H_w = d`, for `X` integral and locally of finite type over `k`, and
`H_w` nonempty.

This is the dimension obligation of `Stacks.WeilCohomology.BertiniDivisorReduction`, in that
statement's own shape — an equality `topologicalKrullDim H = (d : WithBot ℕ∞)` under an equality
`topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞)`, which is what makes the induction on `d` a
`Nat.le_induction` with no case analysis.

`H_w` is an effective Cartier divisor by
`Stacks.SectionsVanishingOnSubscheme.isEffectiveCartierDivisor_divisorOnX`, and
`Stacks.Chow.topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor_field` computes the
dimension of one. Nonemptiness of `H_w` is an instance argument and is genuinely needed; see the
module documentation.

The structure morphism is given with target `Spec k`, as the standing situation holds it, while
the dimension theory is stated over the base scheme of `Stacks.Chow.fieldChowSituation k`. The
two are the same scheme definitionally but not reducibly, so the `LocallyOfFiniteType` instance
is re-registered at the second spelling by hand. -/
theorem topologicalKrullDim_divisorOnX_eq [AlgebraicGeometry.IsIntegral X]
    [LocallyOfFiniteType f] (w : vanishingSections k f I L n) (hw : w ≠ 0)
    [Nonempty ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme] {d : ℕ}
    (hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim
        (((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme : Type u) =
      (d : WithBot ℕ∞) := by
  have : LocallyOfFiniteType (show X ⟶ (fieldChowSituation k).S from f) :=
    ‹LocallyOfFiniteType f›
  exact topologicalKrullDim_subscheme_eq_of_isEffectiveCartierDivisor_field
    (show X ⟶ (fieldChowSituation k).S from f) _
    (isEffectiveCartierDivisor_divisorOnX k f I n w hw) hdim

end Stacks.SectionsVanishingOnSubscheme

end

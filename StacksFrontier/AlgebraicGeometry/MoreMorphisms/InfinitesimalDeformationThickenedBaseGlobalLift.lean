module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action on the lifts over the whole space, for a datum coming from a lift

[Stacks Project, Tag 0CK2] makes `Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` act simply transitively on
the lifts of `a : X ⟶ Y` over an open of `X'`, for a conormal datum `A` compatible with the
base. The datum is not extra information: by the remark of that tag it is determined by `a`
(`Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap`), and any actual lift produces one
(`Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift`).

That production is stated for the restriction `i ∣_ V` of the thickening to an open `V` of `X'`,
because that is the shape the sheaf-theoretic statements of Tag 04FI need. The present file
states it for a lift defined on all of `X'`, where no restriction occurs, and packages the
action clause of Tag 0CK2 over the whole space with the datum discharged: if `a` admits one
lift `X' ⟶ Y'` over `Z'`, then the lifts of `a` over `Z'` form a simply transitive
`Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})`-set, with no conormal datum appearing in the statement.

## Main results

* `Stacks.Thickenings.isBaseCompatibleConormalMap_of_globalLift`: the canonical map of conormal
  sheaves attached to a lift defined on all of `X'` is compatible with the base.
* `Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBaseOfGlobalLift`: **the action
  clause of [Stacks Project, Tag 0CK2] over the whole space, from a lift.** The sections over
  `X` of `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` act on the morphisms `X' ⟶ Y'` over `Z'`
  restricting to `a`, with the group laws and simple transitivity.

## Implementation notes

The proof of `Stacks.Thickenings.isBaseCompatibleConormalMap_of_globalLift` is the proof of
`Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift` with the restriction removed
throughout: stacking the square of the lift on the cartesian square of the base gives the square
`i ≫ g' = (a ≫ h) ≫ k` whose canonical map does not mention the lift, which is
`Stacks.Thickenings.immersionConormalSheafMap_comp`, and the two spellings
`b ≫ h'` and `g'` of the right-hand edge are identified by
`Stacks.Immersion.immersionConormalSheafMap_congr`. Nothing is reproved: the restricted statement
is not an instance of the global one, nor the other way round, since the thickening itself
differs.

The action over the whole space is `Stacks.Thickenings.liftsOverBaseVAddOfBase` at `V = ⊤`,
whose compatibility-with-restriction clause is dropped: there is no larger open to restrict from.
Simple transitivity needs no hypothesis that an open carries a lift, because the lift supplied to
produce the conormal datum is one.

## References

* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

variable {X X' Y Y' Z Z' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {k : Z ⟶ Z'}
  [IsImmersion i] [IsImmersion j] [IsImmersion k]
  {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X ⟶ Y}

/-- **The conormal datum of a lift defined on all of `X'` is compatible with the base.** For a
morphism `b : X' ⟶ Y'` over `Z'` whose restriction along `i` is `a`, the square it forms with
`i` and `j` has a canonical map of conormal sheaves; stacking that square on the cartesian
square of the base gives the square `i ≫ g' = (a ≫ h) ≫ k`, whose canonical map does not
mention `b`. This is the assertion of [Stacks Project, Tag 0CK2] that the composite
`g^*𝒞_{Z/Z'} ⟶ a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` "has to be the canonical map induced by `g'`", read for
a lift over the whole space.

`Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift` is the same statement for a lift
defined on an open `V` of `X'`, where the thickening is `i ∣_ V`. -/
@[stacks 0CK2 "the composition g^*C_{Z/Z'} -> a^*C_{Y/Y'} -> C_{X/X'} is the canonical map \
induced by g', for the datum of a lift defined on all of X'"]
theorem isBaseCompatibleConormalMap_of_globalLift (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k) {b : X' ⟶ Y'} (hb₁ : b ≫ h' = g') (hb₂ : i ≫ b = a ≫ j) :
    IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci
      (immersionConormalSheafMap i j a b (toShHom_square hb₂)) := by
  refine Eq.trans ?_ (immersionConormalSheafMap_congr i k
    (rfl : a ≫ h = a ≫ h) hb₁
    (toShHom_square (square_comp hb₂ sq.w))
    (toShHom_square ci)).symm
  rw [eqToHom_refl, Category.id_comp]
  exact (immersionConormalSheafMap_comp i j k a b hb₂ h h' sq.w).symm

/-- **The action clause of [Stacks Project, Tag 0CK2] over the whole space, from a lift.** Let
`k : Z ⟶ Z'` be an immersion, let `i : X ⟶ X'` be a first order thickening and `j : Y ⟶ Y'` an
immersion, both over `Z'` by `g'` and `h'`, assume `Y = Z ×_{Z'} Y'`, and let `a : X ⟶ Y` admit
a lift `b : X' ⟶ Y'`, that is, a morphism over `Z'` whose restriction along `i` is `a`. Then the
additive group of sections over `X` of `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` — differentials
relative to `Z`, as the source writes them — **acts simply transitively** on the morphisms
`X' ⟶ Y'` over `Z'` restricting to `a` along `i`.

No conormal datum appears: the lift produces one, by
`Stacks.Thickenings.isBaseCompatibleConormalMap_of_globalLift`, and it is the only one
compatible with the base by `Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap`. No
affineness is assumed, of `Z'`, `X'` or `Y'`, and the hypothesis that the open carries a lift —
which is what makes the action of that tag simply transitive — is discharged by `b`. -/
@[stacks 0CK2 "the simply transitive action of Hom(a^*Omega_{Y/Z}, C_{X/X'}) on the lifts of a \
over the whole space, with the conormal datum discharged by an actual lift",
  sga "3 XII 9.4" "partial"]
theorem exists_simplyTransitive_addAction_liftsOverBaseOfGlobalLift [IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    {b : X' ⟶ Y'} (hb₁ : b ≫ h' = g') (hb₂ : i ≫ b = a ≫ j) :
    ∃ act : deformationHomSections i a h ⊤ →
        liftsOverBase i j g' h' a ⊤ → liftsOverBase i j g' h' a ⊤,
      (∀ c : liftsOverBase i j g' h' a ⊤, act 0 c = c) ∧
        (∀ (θ η : deformationHomSections i a h ⊤) (c : liftsOverBase i j g' h' a ⊤),
          act (θ + η) c = act θ (act η c)) ∧
          ∀ c₀ c₁ : liftsOverBase i j g' h' a ⊤, ∃! θ : deformationHomSections i a h ⊤,
            act θ c₀ = c₁ := by
  obtain ⟨act, hzero, hadd, _, htrans⟩ :=
    exists_simplyTransitive_addAction_liftsOverBaseOfBase hsq sq ci
      (isBaseCompatibleConormalMap_of_globalLift sq ci hb₁ hb₂)
  exact ⟨act ⊤, hzero ⊤, hadd ⊤, htrans ⊤⟩

end Stacks.Thickenings

end

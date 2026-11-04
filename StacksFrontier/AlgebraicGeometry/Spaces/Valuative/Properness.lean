module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.SeparatedUniversallyClosed

/-!
# The valuative criterion of properness

Let `B` be a big fppf site containing a scheme `S` and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is of finite type and quasi-separated. Three conditions on
`f` then agree: that `f` be proper; that `f` satisfy the valuative criterion of Stacks 03IX,
both its existence part and its uniqueness part; and that every valuative square for `f`
have exactly one dotted arrow over the given valuation ring, with no extension of the
fraction field and no domination, which is the valuative criterion of Schemes, Stacks 01KD. A
unique dotted arrow is expressed as `Nonempty q.Lift ∧ Subsingleton q.Lift`, and the valuation
rings range over those whose spectra belong to the chosen big site.

## Main results

* `AlgebraicGeometry.Space.isProper_tfae_of_isFiniteType_of_isQuasiSeparated`: the equivalence of
  those three conditions.
* `AlgebraicGeometry.Space`
  `.isProper_iff_valuativeCriterion_of_isFiniteType_of_isQuasiSeparated` and
  `AlgebraicGeometry.Space`
  `.isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated`: properness is
  equivalent to the second and to the third condition.

## References

* [Stacks Project, Tag 0A40](https://stacks.math.columbia.edu/tag/0A40)
* [Stacks Project, Tag 0A3Z](https://stacks.math.columbia.edu/tag/0A3Z)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` which is of finite type and
quasi-separated, being proper, satisfying the valuative criterion of Stacks 03IX, and having
exactly one dotted arrow in every valuative square over the given valuation ring are
equivalent. -/
@[stacks 0A40]
public theorem isProper_tfae_of_isFiniteType_of_isQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    List.TFAE
      [IsProper B S hS f,
        ValuativeCriterion f,
        ∀ q : ValuativeSquare f, Nonempty q.Lift ∧ Subsingleton q.Lift] := by
  have key := isSeparated_and_universallyClosed_tfae_of_isQuasiCompact_of_isQuasiSeparated
    hX hY f hft.2 hqs
  have hproper : IsProper B S hS f ↔ IsSeparated B S hS f ∧ UniversallyClosed B S hS f :=
    ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hft, h.2⟩⟩
  tfae_have 1 ↔ 2 := hproper.trans (key.out 1 2)
  tfae_have 2 ↔ 3 := key.out 2 3
  tfae_finish

/-- A morphism of algebraic spaces over `S` which is of finite type and quasi-separated is proper
exactly when it satisfies the valuative criterion of Stacks 03IX. -/
@[stacks 0A40 "conditions (1) and (2)"]
public theorem isProper_iff_valuativeCriterion_of_isFiniteType_of_isQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    IsProper B S hS f ↔ ValuativeCriterion f :=
  (isProper_tfae_of_isFiniteType_of_isQuasiSeparated hX hY f hft hqs).out 1 2

/-- A morphism of algebraic spaces over `S` which is of finite type and quasi-separated is proper
exactly when every valuative square for it has exactly one dotted arrow over the given valuation
ring, which is the valuative criterion of Schemes, Stacks 01KD. -/
@[stacks 0A40 "conditions (1) and (3)"]
public theorem isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    IsProper B S hS f ↔ ∀ q : ValuativeSquare f, Nonempty q.Lift ∧ Subsingleton q.Lift :=
  (isProper_tfae_of_isFiniteType_of_isQuasiSeparated hX hY f hft hqs).out 1 3

end AlgebraicGeometry.Space

end

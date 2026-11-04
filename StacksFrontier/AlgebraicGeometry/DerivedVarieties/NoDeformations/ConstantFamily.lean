module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCore.Tactic.StacksAttribute

/-!
# The constant family with the fibre at a rational point

Let `k` be a field, let `S` be a scheme over `k` with structure morphism `q : S ⟶ Spec k` and a
`k`-rational point `s : Spec k ⟶ S`, and let `g : Y ⟶ S` be a morphism of schemes. Write
`Y_s = Y ×_S Spec k` for the fibre of `g` at `s` and `X = Y_s ×_k S ⟶ S` for the constant family
with that fibre. This file constructs `Y_s`, `X` and the natural morphism
`Y_s ×_k Y_s ⟶ X ×_S Y`, the objects named in [Stacks, Tag 0G0R]: if `g` is smooth and proper
and `K` is the Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over `S`
([Stacks, Tag 0G0I]) whose restriction along `Y_s ×_k Y_s ⟶ X ×_S Y` is the diagonal kernel
`Δ_{Y_s/k,*}𝒪_{Y_s}` of [Stacks, Tag 0FYV], then `Y` is constant near `s`.

## Main definitions

* `AlgebraicGeometry.fibreAtRationalPoint` — the fibre `Y_s = Y ×_S Spec k`, with its structure
  morphism `AlgebraicGeometry.fibreAtRationalPointπ` and its inclusion
  `AlgebraicGeometry.fibreAtRationalPointι` into `Y`.
* `AlgebraicGeometry.constantFamily` — the constant family `Y_s ×_k S` with fibre `Y_s`, and
  `AlgebraicGeometry.constantFamilyπ`, its structure morphism to `S`.
* `AlgebraicGeometry.fibreSquareToProductComparison` — the natural morphism
  `Y_s ×_k Y_s ⟶ X ×_S Y`.

## Implementation notes

A `k`-rational point of `S` is a section `s : Spec k ⟶ S` of the structure morphism
`q : S ⟶ Spec k`, and the section condition `s ≫ q = 𝟙 _` is carried as a hypothesis.

The fibre `Y_s` is `Limits.pullback g s`, the pullback along the given morphism `s`. This is not
Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`, which is the pullback along
`S.fromSpecResidueField` at a topological point of `S`.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0G0Q](https://stacks.math.columbia.edu/tag/0G0Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, the one the diagonal
-- kernel of [Stacks, Tag 0FYV] and the convolution kernel of [Stacks, Tag 0FYS] are read at.
attribute [local instance 100000] HasDerivedCategory.standard

section ConstantFamily

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)

/-- **The fibre `Y_s = Y ×_S Spec k`** of `g : Y ⟶ S` at a `k`-rational point
`s : Spec k ⟶ S`. -/
abbrev fibreAtRationalPoint : Scheme.{u} := Limits.pullback g s

/-- The structure morphism `Y_s ⟶ Spec k` of the fibre at a `k`-rational point. -/
abbrev fibreAtRationalPointπ : fibreAtRationalPoint g s ⟶ Spec (.of k) :=
  Limits.pullback.snd g s

/-- The closed-point inclusion `Y_s ⟶ Y` of the fibre at a `k`-rational point. -/
abbrev fibreAtRationalPointι : fibreAtRationalPoint g s ⟶ Y := Limits.pullback.fst g s

/-- **The constant family `Y_s ×_k S`** with fibre the fibre `Y_s = Y ×_S Spec k` of `g` at a
`k`-rational point `s`. This is the scheme `X` of [Stacks, Tag 0G0R]. -/
abbrev constantFamily : Scheme.{u} :=
  Limits.pullback (fibreAtRationalPointπ g s) q

/-- The structure morphism `Y_s ×_k S ⟶ S` of the constant family, the projection to the second
factor. -/
abbrev constantFamilyπ : constantFamily q g s ⟶ S :=
  Limits.pullback.snd (fibreAtRationalPointπ g s) q

/-- **The comparison morphism `Y_s ×_k Y_s ⟶ X ×_S Y`**, for `X = Y_s ×_k S` the constant
family.

On the first factor it is the first projection of `Y_s ×_k Y_s`, read into `X` using that the
second projection lands in `S` through `Y`; on the second factor it is the second projection,
read into `Y`. -/
def fibreSquareToProductComparison (hs : s ≫ q = 𝟙 _) :
    Limits.pullback (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) ⟶
      Limits.pullback (constantFamilyπ q g s) g :=
  Limits.pullback.lift
    (Limits.pullback.lift
      (Limits.pullback.fst (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s))
      (Limits.pullback.snd (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) ≫
        fibreAtRationalPointι g s ≫ g)
      (by simp [Limits.pullback.condition, hs]))
    (Limits.pullback.snd (fibreAtRationalPointπ g s) (fibreAtRationalPointπ g s) ≫
      fibreAtRationalPointι g s)
    (by rw [Limits.pullback.lift_snd, Category.assoc])

end ConstantFamily

end AlgebraicGeometry

end

module

public import StacksFrontier.Deformation.Smooth.Versal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Minimal versal formal objects

Minimality for a versal formal object.

## Main definitions

* `IsMinimalVersal` is the predicate for a minimal versal formal object.

## Implementation notes

The special-fibre condition of a predeformation category is not needed to state
minimal versality: the cofibered-in-groupoids condition already used by versality
suffices. The abbreviated predicate exposes both versality and the surjectivity
condition directly to downstream statements.

## References

* [Stacks Project, Tag 06T4](https://stacks.math.columbia.edu/tag/06T4)
-/

@[expose] public section

namespace Deformation

/-! ### Minimal versal formal objects -/

section
open CategoryTheory
universe u v w uF vF


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A formal object is minimal versal if it is versal and every morphism from a
formal object into it is surjective on its underlying complete local algebra. -/
@[stacks 06T4, sga "7 VI 1.19" "(2)"]
public abbrev IsMinimalVersal (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) : Prop :=
  IsVersal hp ξ ∧
    ∀ (ξ' : FormalObject p) (f : ξ' ⟶ ξ), Function.Surjective f.base.hom

end

end Deformation

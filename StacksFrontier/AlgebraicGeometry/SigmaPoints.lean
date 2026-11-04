module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Points of a coproduct of schemes

A coproduct of schemes is covered by its summands (`AlgebraicGeometry.sigmaOpenCover`), so every
point of it comes from a point of one summand.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Every point of a coproduct of schemes lies in the image of one of the injections. -/
theorem exists_sigmaι_eq {ι : Type*} [Small.{u} ι] (g : ι → Scheme.{u})
    (x : ↥(∐ g : Scheme.{u})) :
    ∃ (i : ι) (y : ↥(g i)), (Sigma.ι g i).base y = x :=
  (sigmaOpenCover g).exists_eq x

end AlgebraicGeometry

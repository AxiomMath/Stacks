module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineAmbientObjects
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalBridge

/-!
# The objects of the cosimplicial system `(X, T(n)_e, δ(n))` are affine

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` affine, and a cosimplicial system
of objects of the small crystalline site `Cris(X/S)` consisting of thickenings of the whole of `X`,
in the sense of `IsWholeSpaceSystem`. We show that in every bidegree `(n, e)` both the thickened
scheme `U` and the ambient divided power scheme `T` of the object `(U, T, δ)` are affine: `U ⟶ X`
is an isomorphism, and `U ⟶ T` is a thickening, so `T` is affine by [Stacks, Tag 06AD]. In
particular this holds for the system `wholeSpaceSystem` of [Stacks, Proposition 60.20.1,
Tag 07JN].

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isAffineObject_of_isWholeSpaceSystem`: every object of a whole-space cosimplicial system over
  an affine `X` is an affine object of `Cris(X/S)`.
* `isAffine_source_of_isWholeSpaceSystem`, `isAffine_target_of_isWholeSpaceSystem`: its thickened
  scheme and its ambient divided power scheme are affine.
* `mem_affineAmbientObjects_of_isWholeSpaceSystem`: every such object lies in
  `affineAmbientObjects`.
* `isAffineObject_wholeSpaceSystem`, `isAffine_source_wholeSpaceSystem`,
  `isAffine_target_wholeSpaceSystem`, `mem_affineAmbientObjects_wholeSpaceSystem`: the same four
  statements for `wholeSpaceSystem`.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Simplicial

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X]

/-! ### A general whole-space system -/

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}

/-- Every object of a cosimplicial system of thickenings of the whole of an affine `X` is an
affine object of `Cris(X/S)`, in the sense of `IsAffineObject`: its thickened scheme and its
ambient divided power scheme are both affine. -/
theorem isAffineObject_of_isWholeSpaceSystem (hT : IsWholeSpaceSystem T) (n e : ℕ) :
    IsAffineObject S ((T.obj (op ⦋n⦌)).obj e) :=
  isAffineObject_of_isOverWholeSpace _ (hT n e)

/-- The thickened scheme of every object of a whole-space system over an affine `X` is affine. -/
theorem isAffine_source_of_isWholeSpaceSystem (hT : IsWholeSpaceSystem T) (n e : ℕ) :
    IsAffine ((T.obj (op ⦋n⦌)).obj e).obj.thickening.source :=
  (isAffineObject_of_isWholeSpaceSystem hT n e).1

/-- The ambient divided power scheme of every object of a whole-space system over an affine `X`
is affine. -/
theorem isAffine_target_of_isWholeSpaceSystem (hT : IsWholeSpaceSystem T) (n e : ℕ) :
    IsAffine ((T.obj (op ⦋n⦌)).obj e).obj.thickening.target.scheme :=
  (isAffineObject_of_isWholeSpaceSystem hT n e).2

/-- Every object of a whole-space system over an affine `X` lies in the collection
`affineAmbientObjects`. -/
theorem mem_affineAmbientObjects_of_isWholeSpaceSystem (hT : IsWholeSpaceSystem T) (n e : ℕ) :
    (T.obj (op ⦋n⦌)).obj e ∈ affineAmbientObjects S :=
  isAffine_target_of_isWholeSpaceSystem hT n e

/-! ### The source's own system -/

variable [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- Every object of the cosimplicial system `(X, T(n)_e, δ(n))` of [Stacks, Proposition 60.20.1,
Tag 07JN] is an affine object of `Cris(X/S)`. -/
theorem isAffineObject_wholeSpaceSystem (n e : ℕ) :
    IsAffineObject S (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e) :=
  isAffineObject_of_isWholeSpaceSystem (isWholeSpaceSystem_wholeSpaceSystem S hp) n e

/-- The thickened scheme of every object of `(X, T(n)_e, δ(n))` is affine. -/
theorem isAffine_source_wholeSpaceSystem (n e : ℕ) :
    IsAffine (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj.thickening.source :=
  (isAffineObject_wholeSpaceSystem hp n e).1

/-- The ambient divided power scheme of every object of `(X, T(n)_e, δ(n))` is affine. -/
theorem isAffine_target_wholeSpaceSystem (n e : ℕ) :
    IsAffine (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj.thickening.target.scheme :=
  (isAffineObject_wholeSpaceSystem hp n e).2

/-- Every object of `(X, T(n)_e, δ(n))` lies in `affineAmbientObjects`. -/
theorem mem_affineAmbientObjects_wholeSpaceSystem (n e : ℕ) :
    ((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e ∈ affineAmbientObjects S :=
  isAffine_target_wholeSpaceSystem hp n e

end Crystalline.GlobalCrystallineSituation.SmallSite

end

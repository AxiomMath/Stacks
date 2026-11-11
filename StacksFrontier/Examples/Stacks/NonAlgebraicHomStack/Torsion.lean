module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyTorsion
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack

/-!
# The input `htorsion` of Stacks 0AFB

In the situation of Section 0AF8 of the Stacks project the proof of Stacks 0AFB uses that
`H¹(X, A)` is torsion: "As `X` is regular and projective, by 0AFA and 0AF9 each `A₀`-torsor over
`X` is torsion". This file states that input in the shape of the hypothesis `htorsion` of
`Stacks.Examples.NonAlgebraicHomStack.exists_compatible_ne_restrictTotal` and
`Stacks.Examples.NonAlgebraicHomStack.not_surjective_toCompatibleSystems`, for the points sheaf
of an abelian scheme `A` over `S = Spec k⟦t⟧`, and for a total space `X` which is a two
dimensional regular integral Noetherian scheme.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.isAddTorsion_H1_totalObj`: `H¹(X, A)` is torsion.

## Implementation notes

The geometric hypotheses on `X` (integral, Noetherian, regular, of dimension two) are those under
which the source applies Stacks 0AF9; in the section's situation they follow from `X` being
regular, flat and projective over `k⟦t⟧` with geometrically connected curves as fibres, and they
are kept explicit here. The content is
`AlgebraicGeometry.isAddTorsion_H1_pointsSheaf_of_isRegular`.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Section 0AF8](https://stacks.math.columbia.edu/tag/0AF8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe w u

namespace Stacks.Examples.NonAlgebraicHomStack

/-- **`H¹(X, A)` is torsion**, the input `htorsion` of the source's proof of Stacks 0AFB. Let
`A` be an abelian scheme over `S = Spec k⟦t⟧` and let `X ⟶ S` be a family whose total space `X`
is a two dimensional regular integral Noetherian scheme. Then the first fppf cohomology of the
points sheaf of `A`, on the big fppf site over `S` at the object `X`, is torsion. -/
theorem isAddTorsion_H1_totalObj {k : Type u} [Field k] (B : BigFppfSite.{u})
    (hS : B.Contains (base k)) {X : Scheme.{u}} (fX : X ⟶ base k) (hX : B.Contains X)
    [IsIntegral X] [IsNoetherian X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X = (2 : WithBot ℕ∞))
    (A : Over (base k)) [GrpObj A] [IsAbelianScheme A] (hA : B.Contains A.left)
    [HasSheafify (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})] :
    IsAddTorsion (Sheaf.H' (pointsSheaf B (base k) hS A hA) 1 (totalObj B hS fX hX)) :=
  isAddTorsion_H1_pointsSheaf_of_isRegular B (base k) hS A hA hX fX hreg hdim

end Stacks.Examples.NonAlgebraicHomStack

end

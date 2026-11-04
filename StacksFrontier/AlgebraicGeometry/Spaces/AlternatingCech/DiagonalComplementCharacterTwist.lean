module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementOrbitQuotient
public import StacksFrontier.CategoryTheory.Sites.FreeQuotientCharacterTwist

/-!
# The rank one twist attached to a character of the symmetric group action on `W_p`

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S`, let
`W = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `n` factors be the complement of the diagonals in
the `n`-fold self-product, and let `U_p = W/S_n` be its quotient by the symmetric group. With
`n = p + 1` this is the space `W_p` of Stacks 0726 with its action of `S_{p+1}`.

`AlgebraicGeometry.Space.SpacesEtale.isOrbitQuotient_diagonalComplement` exhibits the final
object of the spaces-étale site of `U_p` as that quotient and
`AlgebraicGeometry.Space.SpacesEtale.actsFreelyOnObject_diagonalComplement` says the action is
free there, which are exactly the two hypotheses of
`CategoryTheory.characterTwistOfQuotient`. This file records the resulting conclusion: for
every character `χ` of the symmetric group there is a sheaf of `ℤ`-modules `ℤ(χ)` on the
spaces-étale site of `U_p`, locally free of rank one and trivialized over `W`, whose tensor
product with an abelian sheaf `F` has global sections the sections of `F` over `W` that
transform according to `χ`.

The character of interest is the sign character, for which `ℤ(χ)` is the sign twist of the
alternating Čech complex; it is the case
`χ = (Equiv.Perm.sign).comp MulEquiv.ulift.toMonoidHom` of what is proved here, the statement
being recorded for an arbitrary character.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.characterTwistOfDiagonalComplement`: **the twist
  `ℤ(χ)` on the spaces-étale site of `U_p`**, as an inhabitant of
  `CategoryTheory.CharacterTwistOfQuotient`: a sheaf of `ℤ`-modules on `U_p`, a covering of
  `U_p` by `W` on which it is the constant sheaf `ℤ`, and the identification of the
  `χ`-semi-invariant sections of an abelian sheaf over `W` with the global sections of its
  tensor product with that sheaf.

## Implementation notes

All the sheafification hypotheses of `CategoryTheory.characterTwistOfQuotient` are satisfied
here rather than assumed: the spaces-étale site of an algebraic space is essentially small at
the universe of its schemes, by Stacks 03G0, and so is the localization of that site at any of
its objects, so the existence of sheafification for abelian presheaves with sections one
universe up — and the identification of the morphisms inverted by it with the locally
bijective ones — are the general facts of
`StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse`.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The rank one twist attached to a character of the symmetric group action on `W`.**

For a character `χ` of the symmetric group on `n` letters there is a sheaf of `ℤ`-modules
`ℤ(χ)` on the spaces-étale site of the quotient `W/S_n`, locally free of rank one — trivial
over the covering of the quotient by `W` — with

```
H⁰(W, F|_W)^χ = H⁰(W/S_n, F ⊗_ℤ ℤ(χ))
```

for every abelian sheaf `F` on that site.

This is `CategoryTheory.characterTwistOfQuotient` instantiated at the spaces-étale site of
`W/S_n`: the action of the symmetric group on `W` is free there, and the projection exhibits
the final object as the quotient. -/
def characterTwistOfDiagonalComplement (χ : ULift.{u} (Equiv.Perm (Fin n)) →* ℤˣ) :
    CharacterTwistOfQuotient (diagonalComplementEtaleSource B S hS X U n hsep)
      (diagonalComplementQuotientAut B S hS X U n hsep) χ
      (topology B S hS (diagonalComplementQuotient B S hS X U n hsep))
      (final B S hS (diagonalComplementQuotient B S hS X U n hsep)) :=
  characterTwistOfQuotient (actsFreelyOnObject_diagonalComplement B S hS X U n hsep)
    (isOrbitQuotient_diagonalComplement B S hS X U n hsep)
    (final_isTerminal B S hS (diagonalComplementQuotient B S hS X U n hsep)) χ

end AlgebraicGeometry.Space.SpacesEtale

end

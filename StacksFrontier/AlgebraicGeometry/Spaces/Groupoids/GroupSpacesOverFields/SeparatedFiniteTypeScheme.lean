module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallySeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions

/-!
# A separated group algebraic space locally of finite type over a field is a scheme

Let `G` be a group algebraic space over a field `k`, read as a group object over the terminal
presheaf of the big fppf site of a scheme `S ≅ Spec k`. If `G` is separated over `k` and locally
of finite type over `k`, then `G` is a scheme.

## Main results

* `GroupOverField.isRepresentable_of_isSeparatedOver_of_isLocallyOfFiniteType`:
  **a separated group algebraic space locally of finite type over a field is a scheme.**

## Implementation notes

Separatedness enters only through decency: the diagonal of `G` is a closed immersion, hence an
immersion, so `G` is locally separated over `k` and therefore decent (Stacks 088J). A decent
group algebraic space locally of finite type over a field is a scheme by
`AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_isDecentSpace_of_isLocallyOfFiniteType`,
which is where all the work happens.

Separatedness of `G` over `k` is the relative notion `AlgebraicGeometry.Space.IsSeparatedOver`,
the diagonal over the base being a closed immersion. Over the affine base `Spec k` this agrees
with absolute separatedness, by
`AlgebraicGeometry.Space.isAbsolutelySeparated_iff_isSeparatedOver`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.GroupOverField

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {k : Type u} [Field k]

/-- **A separated group algebraic space locally of finite type over a field is a scheme.** Let
`G` be a group algebraic space over `S ≅ Spec k` which is separated over `k` and locally of
finite type over `k`. Then `G` is representable.

Being separated over `k`, the space `G` is locally separated over `k`, hence decent, and a decent
group algebraic space locally of finite type over a field is a scheme. -/
@[stacks 0B8F]
theorem isRepresentable_of_isSeparatedOver_of_isLocallyOfFiniteType (e : S ≅ Spec (.of k))
    (G : GroupAlgebraicSpace C S hS (yoneda.obj (⊤_ (BigFppfOver C S hS)))
      (isAlgebraicSpace_yoneda C S hS _))
    (hsep : IsSeparatedOver C S hS G.obj.X.left)
    (hlft : IsLocallyOfFiniteType C S hS
      ((isTerminal_yoneda_obj_base C S hS).from G.obj.X.left)) :
    G.obj.X.left.IsRepresentable :=
  isRepresentable_of_isDecentSpace_of_isLocallyOfFiniteType G e
    (isDecentSpace_of_isLocallySeparatedOver C S hS G.property
      (isImmersion_of_isClosedImmersion C S hS hsep))
    hlft

end AlgebraicGeometry.Space.GroupOverField

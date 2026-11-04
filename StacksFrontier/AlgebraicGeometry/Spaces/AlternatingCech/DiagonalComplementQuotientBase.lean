module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementOrbitQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite

/-!
# The quotient `U_p = W_p/S_{p+1}` as an object of the spaces-étale site of `X`

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S` and
let `W = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `n` factors be the complement of the diagonals
in the `n`-fold self-product, with its free action of the symmetric group on `n` letters. The
quotient `W/S_n` is an algebraic space by
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotient`, but it is produced there
only as an algebraic space over `S`: nothing yet relates it to `X`.

This file supplies that relation, which is the first sentence of the proof of Stacks 0728:
*since the action of `S_{p+1}` on `W_p` is over `X` we do obtain a morphism `U_p → X`; since
`W_p → X` is étale and `W_p → U_p` is surjective étale, also `U_p → X` is étale.* The two
steps are the universal property of the quotient sheaf and Stacks 0AHD.

With `U_p` an object of the spaces-étale site of `X`, the slice of that site at `U_p` is the
spaces-étale site of `U_p` (`AlgebraicGeometry.Space.SpacesEtale.sliceToSmall`), and `W_p`
with its projection to `U_p` is an object of the slice whose image is exactly the `W_p` of
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementEtaleSource`. That identification, and
the matching one for the action of the symmetric group, are the last results below; they are
what transports sections of a sheaf on `X` over `W_p` to sections of its restriction to `U_p`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientToBase`: **the morphism
  `U_p → X`**, the descent of the structure morphism of `W_p` along the quotient map.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientObject`: **`U_p` as an object
  of the spaces-étale site of `X`**.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementToQuotientObject`: the projection
  `W_p ⟶ U_p` read in the spaces-étale site of `X`, and
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementSlice`: the resulting object of the
  slice of that site at `U_p`.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementSliceAut`: the action of the
  symmetric group on that object of the slice.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isEtale_diagonalComplementQuotientToBase`: **`U_p → X`
  is étale.**
* `AlgebraicGeometry.Space.SpacesEtale.sliceToSmall_diagonalComplementSlice`: the object of
  the slice at `U_p` carried by `W_p ⟶ U_p` is `W_p` as an object of the spaces-étale site of
  `U_p`, on the nose.
* `AlgebraicGeometry.Space.SpacesEtale.sliceToSmall_map_diagonalComplementSliceAut`: the
  action of the symmetric group on the slice object is carried to the action
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientAut` on `W_p` over `U_p`.

## Implementation notes

The descent of the structure morphism is `AlgebraicGeometry.Space.orbitQuotientLift`, the
universal property of the quotient sheaf, applied to the structure morphism of `W_p` read on
presheaves of points; its invariance is the commutation of a morphism of the spaces-étale site
of `X` with the structure morphisms,
`AlgebraicGeometry.Space.SpacesEtale.hom_toSpaces_map_comp_structure`, since the permutation
automorphisms of `W_p` are morphisms of that site. The factorization of the structure
morphism through the quotient is then
`CategoryTheory.toSheafify_sheafifyLift`; it is what makes the étaleness of `W_p → X` an
étaleness hypothesis for Stacks 0AHD.

## References

* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)

/-! ### The action of the symmetric group read as an action on the presheaf of points -/

/-- The endomorphism of the presheaf of points of `W` given by the action of a permutation is
the presheaf morphism underlying the permutation automorphism of `W`. -/
theorem actionHom_diagonalComplement (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    actionHom B S hS (ULift.{u} (Equiv.Perm (Fin n)))
        (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1
        (isNaturalAction_diagonalComplement B S hS X U n hsep) σ =
      ((toSpaces B S hS X).map
        (diagonalComplementPerm B S hS X U n hsep σ.down)).hom := by
  ext T x
  rfl

/-- **The structure morphism of `W` is invariant under the symmetric group**: the action
permutes the factors of `U^n` over `X`. -/
theorem structure_invariant_diagonalComplement
    (T : (BigFppfOver B S hS)ᵒᵖ) (σ : ULift.{u} (Equiv.Perm (Fin n)))
    (x : (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1.obj T) :
    ((diagonalComplement B S hS X U n hsep).1.hom.hom).app T (σ • x) =
      ((diagonalComplement B S hS X U n hsep).1.hom.hom).app T x := by
  have h := hom_toSpaces_map_comp_structure B S hS X
    (diagonalComplementPerm B S hS X U n hsep σ.down)
  exact congrArg
    (fun k : (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 ⟶ X.1 =>
      k.app T x) h

/-! ### The quotient over `X` -/

section Quotient

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The morphism `U_p → X`.** The structure morphism of `W` is invariant under the symmetric
group, so it descends to the quotient `U_p = W/S_n` by the universal property of the quotient
sheaf. -/
def diagonalComplementQuotientToBase :
    diagonalComplementQuotient B S hS X U n hsep ⟶ X :=
  ObjectProperty.homMk
    (orbitQuotientLift B S hS (ULift.{u} (Equiv.Perm (Fin n)))
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1
      (isNaturalAction_diagonalComplement B S hS X U n hsep)
      ((diagonalComplement B S hS X U n hsep).1.hom.hom)
      (structure_invariant_diagonalComplement B S hS X U n hsep) X.2.isSheaf)

/-- **The structure morphism of `W` factors through the quotient `U_p`**, by construction of
the descended morphism. -/
theorem toOrbitQuotientSpace_comp_diagonalComplementQuotientToBase :
    (toOrbitQuotientSpace (isNaturalAction_diagonalComplement B S hS X U n hsep)
          (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
          (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)).hom ≫
        (diagonalComplementQuotientToBase B S hS X U n hsep).hom =
      (diagonalComplement B S hS X U n hsep).1.hom.hom := by
  change toOrbitPresheaf B S hS (ULift.{u} (Equiv.Perm (Fin n))) _
      (isNaturalAction_diagonalComplement B S hS X U n hsep) ≫
      toSheafify _ _ ≫ sheafifyLift _ _ _ = _
  rw [toSheafify_sheafifyLift]
  ext T x
  rfl

/-- **`U_p → X` is étale.** The projection `W → U_p` is surjective and étale and the composite
`W → U_p → X` is the étale structure morphism of `W`, so Stacks 0AHD applies. -/
theorem isEtale_diagonalComplementQuotientToBase :
    IsEtale B S hS (diagonalComplementQuotientToBase B S hS X U n hsep).hom := by
  have hcomp : IsEtale B S hS
      ((toOrbitQuotientSpace (isNaturalAction_diagonalComplement B S hS X U n hsep)
          (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
          (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep)).hom ≫
        (diagonalComplementQuotientToBase B S hS X U n hsep).hom) := by
    rw [toOrbitQuotientSpace_comp_diagonalComplementQuotientToBase]
    exact (diagonalComplement B S hS X U n hsep).property
  exact isEtale_of_comp_surjective_isEtale B S hS
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (diagonalComplementQuotient B S hS X U n hsep).2 X.2
    (toOrbitQuotient B S hS (ULift.{u} (Equiv.Perm (Fin n)))
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1
      (isNaturalAction_diagonalComplement B S hS X U n hsep)) _
    (diagonalComplementQuotientToBase B S hS X U n hsep).hom rfl
    (isSurjective_toOrbitQuotient
      (isNaturalAction_diagonalComplement B S hS X U n hsep)
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
      (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep))
    (isEtale_toOrbitQuotient
      (isNaturalAction_diagonalComplement B S hS X U n hsep)
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
      (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep))
    hcomp

/-- **`U_p = W/S_n` as an object of the spaces-étale site of `X`.** -/
def diagonalComplementQuotientObject : SpacesEtale B S hS X :=
  etaleObject B S hS (diagonalComplementQuotientToBase B S hS X U n hsep)
    (isEtale_diagonalComplementQuotientToBase B S hS X U n hsep)

/-- The projection `W ⟶ U_p`, read as a morphism of the spaces-étale site of `X`. -/
def diagonalComplementToQuotientObject :
    diagonalComplement B S hS X U n hsep ⟶
      diagonalComplementQuotientObject B S hS X U n hsep :=
  ObjectProperty.homMk
    (Over.homMk
      (toOrbitQuotientSpace (isNaturalAction_diagonalComplement B S hS X U n hsep)
        (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
        (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep))
      (ObjectProperty.hom_ext _
        (toOrbitQuotientSpace_comp_diagonalComplementQuotientToBase B S hS X U n hsep)))

/-- `W` with its projection to `U_p`, as an object of the slice of the spaces-étale site of
`X` at `U_p`. -/
def diagonalComplementSlice : Over (diagonalComplementQuotientObject B S hS X U n hsep) :=
  Over.mk (diagonalComplementToQuotientObject B S hS X U n hsep)

/-- **The object of the slice at `U_p` carried by `W ⟶ U_p` is `W` as an object of the
spaces-étale site of `U_p`**, on the nose: both are the projection `W ⟶ W/S_n` read as an
étale object. -/
theorem sliceToSmall_diagonalComplementSlice :
    (sliceToSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)).obj
        (diagonalComplementSlice B S hS X U n hsep) =
      diagonalComplementEtaleSource B S hS X U n hsep :=
  rfl

/-- A permutation automorphism of `W` is a morphism over `U_p`: the quotient morphism is
invariant. -/
theorem diagonalComplementAut_comp_toQuotientObject
    (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    (diagonalComplementAut B S hS X U n hsep σ.down).hom ≫
        diagonalComplementToQuotientObject B S hS X U n hsep =
      diagonalComplementToQuotientObject B S hS X U n hsep := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
  change ((toSpaces B S hS X).map
        (diagonalComplementPerm B S hS X U n hsep σ.down)).hom ≫
      (toOrbitQuotient B S hS (ULift.{u} (Equiv.Perm (Fin n)))
        (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1
        (isNaturalAction_diagonalComplement B S hS X U n hsep)) = _
  rw [← actionHom_diagonalComplement B S hS X U n hsep σ]
  exact actionHom_comp_toOrbitQuotientSpace
    (isNaturalAction_diagonalComplement B S hS X U n hsep)
    (underlying B S hS X (diagonalComplement B S hS X U n hsep)).2
    (isFreeOnNonemptyPoints_diagonalComplement B S hS X U n hsep) σ

/-- The action of the symmetric group on `W` read in the slice of the spaces-étale site of `X`
at `U_p`. -/
def diagonalComplementSliceAut (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    diagonalComplementSlice B S hS X U n hsep ⟶
      diagonalComplementSlice B S hS X U n hsep :=
  Over.homMk (diagonalComplementAut B S hS X U n hsep σ.down).hom
    (diagonalComplementAut_comp_toQuotientObject B S hS X U n hsep σ)

/-- **The action on the slice object is the action on `W` over `U_p`**: passing from the slice
at `U_p` to the spaces-étale site of `U_p` carries the permutation automorphism of `W` over
`X` to the one of
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientAut`. -/
theorem sliceToSmall_map_diagonalComplementSliceAut
    (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    (sliceToSmall B S hS (diagonalComplementQuotientObject B S hS X U n hsep)).map
        (diagonalComplementSliceAut B S hS X U n hsep σ) =
      (diagonalComplementQuotientAut B S hS X U n hsep σ).hom := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  refine ObjectProperty.hom_ext _ ?_
  exact (actionHom_diagonalComplement B S hS X U n hsep σ).symm

end Quotient

end AlgebraicGeometry.Space.SpacesEtale

end

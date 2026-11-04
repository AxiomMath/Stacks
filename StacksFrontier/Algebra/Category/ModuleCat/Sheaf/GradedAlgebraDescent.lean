module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# Descent of a sheaf of graded algebras along a quotient of the ring sheaf

Let `α : R ⟶ R'` be a locally surjective morphism of sheaves of rings on a site and let `A` be a
sheaf of graded `R`-algebras every homogeneous piece of which is annihilated by the kernel of
`α`. Then `A` is the restriction of scalars of a sheaf of graded `R'`-algebras: the pieces
descend, and the multiplication, which is `R`-bilinear by hypothesis, is automatically
`R'`-bilinear.

The typical case is `R' = R/I` for a sheaf of ideals `I` and an algebra all of whose pieces are
`I`-torsion, where the conclusion is that such an algebra is an algebra over the quotient.

## Main definitions

* `SheafOfModules.GradedAlgebra.descend`: the sheaf of graded `R'`-algebras.

## Main statements

* `SheafOfModules.GradedAlgebra.descend_mul_app` and
  `SheafOfModules.GradedAlgebra.descend_one_eval`: the multiplication and the unit of the
  descended algebra are those of the original, on sections.

## Implementation notes

**The pieces descend with the same underlying presheaf, but not definitionally.** The descended
piece is `Stacks.SheafOfModules.ChangeOfRings.liftedSheaf`, whose underlying presheaf of abelian
groups is the original one; nevertheless `(restrictScalars α).obj (liftedSheaf α M _)` is *not*
definitionally `M`. The two carry different `Module` instances — the lifted action of the image
of a scalar against the original action — and their agreement is the theorem
`ChangeOfRings.liftedSMul_app`, not a definitional unfolding. That is exactly why
`ChangeOfRings.restrictScalarsLiftedSheafIso` exists, and it is why the multiplication has to be
transported along three of its components rather than reused as it stands.

**The transports are nevertheless the identity on sections.** That isomorphism is built from the
identity of the underlying presheaf, so each of `Stacks.BilinearMap.compLeft`,
`Stacks.BilinearMap.compRight` and `Stacks.BilinearMap.postcomp` leaves the value of the
multiplication on a pair of local sections unchanged — each has a `rfl` lemma for its action — and
so does the ring upgrade `Stacks.BilinearMap.ofRestrictScalars`. The three laws of the descended
algebra are therefore the three laws of the original, applied unchanged; in particular the two
`HEq` statements need no transport of their own.

**The ring upgrade is where the local surjectivity is used.** `ofRestrictScalars` turns an
`R`-bilinear map of `R'`-modules into an `R'`-bilinear one: a scalar of `R'` is locally the image
of a scalar of `R`, and the target is separated, so linearity over `R` forces linearity over
`R'`. That is the only place either hypothesis enters.

**What not to reach for.** `SheafOfModules.GradedAlgebra.pushforward` with the identity functor is
restriction of scalars along a morphism `S ⟶ R`, which takes an algebra over the *larger* ring to
one over the smaller. It is the first thing one tries here and it is the wrong direction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u t a

namespace SheafOfModules.GradedAlgebra

open Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{t}} (α : R ⟶ R') [Presheaf.IsLocallySurjective J α.hom]
  (A : GradedAlgebra.{t, t} R)
  (hA : ∀ (n : ℤ) (X : Cᵒᵖ) (b : R.obj.obj X), b ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : (A.piece n).val.obj X, b • m = 0)

/-- **A sheaf of graded algebras annihilated by the kernel of a locally surjective morphism of
ring sheaves descends along it.** The pieces are the descended modules, the multiplication is the
original one read over the larger ring, and the unit is the original unit. -/
def descend : GradedAlgebra.{t, t} R' where
  piece n := liftedSheaf α (A.piece n) (hA n)
  mul i j :=
    Stacks.BilinearMap.ofRestrictScalars α.hom
      ((((A.mul i j).compLeft
            (restrictScalarsLiftedSheafIso α (A.piece i) (hA i)).hom.val).compRight
          (restrictScalarsLiftedSheafIso α (A.piece j) (hA j)).hom.val).postcomp
        (restrictScalarsLiftedSheafIso α (A.piece (i + j)) (hA (i + j))).inv.val)
      ((A.piece (i + j)).isSheaf.isSeparated)
  one := A.one
  mul_assoc i j k U x y z := A.mul_assoc i j k U x y z
  one_mul i U x := A.one_mul i U x
  mul_one i U x := A.mul_one i U x

/-- The multiplication of the descended algebra is that of the original, on local sections. -/
theorem descend_mul_app (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    ((descend α A hA).mul i j).app U x y = (A.mul i j).app U x y :=
  rfl

/-- The unit of the descended algebra is that of the original, on sections. -/
theorem descend_one_eval (U : Cᵒᵖ) : (descend α A hA).one.eval U = A.one.eval U :=
  rfl

/-- The pieces of the descended algebra restrict to the pieces of the original. -/
def restrictScalars_descend_piece_iso (n : ℤ) :
    (SheafOfModules.restrictScalars α).obj ((descend α A hA).piece n) ≅ A.piece n :=
  restrictScalarsLiftedSheafIso α (A.piece n) (hA n)

end SheafOfModules.GradedAlgebra

end

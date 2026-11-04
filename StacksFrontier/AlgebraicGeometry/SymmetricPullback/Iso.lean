module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.UniversalGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 01CI for the symmetric algebra: `f^*Sym(F) = Sym(f^*F)`

Let `f : X ⟶ Y` be a morphism of ringed spaces and `F` a sheaf of `𝒪_Y`-modules. Stacks 01CI
asserts that pullback commutes with the tensor, exterior and symmetric algebra constructions.
This file proves the symmetric case, as an **isomorphism** in every degree, compatibly with the
multiplication, the unit and the degree-one generators.

The statement is made through the universal property rather than through a chosen construction:
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι` says that `A` with the degree-one
generator `ι` is initial among sheaves of graded algebras with a pairwise commuting degree-one
generator, which pins `A` down up to canonical isomorphism. A statement quantified over all
such `A` is therefore a statement about *the* symmetric algebra, and is strictly stronger than
one about a single construction of it.

## The argument

Everything rests on two results that are already in the tree and one that is not.

* `Stacks.RingedSpace.pullbackGradedAlgebra` makes `f^*A` a sheaf of graded `𝒪_X`-algebras.
  Its multiplication is the pullback of the multiplication of `A`, which is Stacks 01CD, and
  its three laws are proved there on stalks. **This is what used to be missing**, and with it
  in hand the symmetric case of 01CI is an isomorphism rather than only a morphism.
* `Stacks.RingedSpace.transposeUnitalHom` is the adjunction `f^* ⊣ f_*` read on unital
  homomorphisms of sheaves of graded algebras.
* `Stacks.RingedSpace.pairwiseCommutes_pullbackGen` is the side condition: the pulled-back
  generator still pairwise commutes, on *all* local sections of `f^*F`.

Given those, `f^*A` is initial among sheaves of graded `𝒪_X`-algebras with a pairwise commuting
degree-one generator of `f^*F`, by transporting the initiality of `A` across the adjunction;
that is `Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra`. Initiality determines
`f^*A`, so it *is* a symmetric algebra of `f^*F` and is canonically isomorphic in every degree
to any other.

## Main results

* `Stacks.RingedSpace.pullbackSymmetricPieceIso`: **Stacks 01CI for the symmetric algebra** —
  `f^*(Symⁿ F) ≅ Symⁿ(f^*F)` in every degree, for any two symmetric algebras.
* `Stacks.RingedSpace.pullbackSymmetricPieceIso_generator`,
  `pullbackSymmetricPieceIso_mul`, `pullbackSymmetricPieceIso_one`: the isomorphism carries the
  pulled-back degree-one generator to the generator, and is multiplicative and unital.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
open SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)}
  {F : SheafOfModules.{u} (structureRingSheaf Y)}

/-- `SheafOfModules.GradedAlgebra.pushforwardGenerator`, named at the `structureRingSheaf`
spelling, as `Stacks.RingedSpace.pushforwardAlgebra` is. By definition it is the adjoint
transpose of `κ`. -/
noncomputable abbrev pushforwardGen
    {C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
    (κ : (pullbackFunctor f).obj F ⟶ C.piece 1) : F ⟶ (pushforwardAlgebra f C).piece 1 :=
  (pullbackAdjunction f).homEquiv F (C.piece 1) κ

variable {ι : F ⟶ A.piece 1}

variable {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj F ⟶ B.piece 1}

/-- **Stacks 01CI for the symmetric algebra.** For a morphism of ringed spaces `f : X ⟶ Y` and
a sheaf of `𝒪_Y`-modules `F`, the pullback of the degree-`n` symmetric power of `F` is the
degree-`n` symmetric power of `f^*F`:

`f^*(Symⁿ F) ≅ Symⁿ(f^*F)`.

The two symmetric algebras are given by their universal property, so this is a statement about
*the* symmetric algebras and not about one construction of them. -/
@[stacks 01CI "symmetric algebra", ega "II 1.7.5" "partial"]
noncomputable def pullbackSymmetricPieceIso (hA : IsSymmetricAlgebra A ι)
    (hB : IsSymmetricAlgebra B κ) (n : ℤ) :
    (pullbackFunctor f).obj (A.piece n) ≅ B.piece n :=
  (isSymmetricAlgebra_pullbackGradedAlgebra f hA).isUniversal.pieceIso hB.isUniversal n

/-- The isomorphism of Stacks 01CI carries the pulled-back degree-one generator to the
degree-one generator of the symmetric algebra of the pullback. -/
theorem pullbackSymmetricPieceIso_generator (hA : IsSymmetricAlgebra A ι)
    (hB : IsSymmetricAlgebra B κ) :
    pullbackGen f A ι ≫ (pullbackSymmetricPieceIso f hA hB 1).hom = κ :=
  (isSymmetricAlgebra_pullbackGradedAlgebra f hA).isUniversal.pieceIso_generator hB.isUniversal

/-- The isomorphism of Stacks 01CI is multiplicative on homogeneous local sections. -/
theorem pullbackSymmetricPieceIso_mul (hA : IsSymmetricAlgebra A ι)
    (hB : IsSymmetricAlgebra B κ) (i j : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj U)
    (y : ((pullbackFunctor f).obj (A.piece j)).val.obj U) :
    (pullbackSymmetricPieceIso f hA hB (i + j)).hom.val.app U
        (((pullbackGradedAlgebra f A).mul i j).app U x y) =
      (B.mul i j).app U ((pullbackSymmetricPieceIso f hA hB i).hom.val.app U x)
        ((pullbackSymmetricPieceIso f hA hB j).hom.val.app U y) :=
  (isSymmetricAlgebra_pullbackGradedAlgebra f hA).isUniversal.pieceIso_mul hB.isUniversal
    i j U x y

/-- The isomorphism of Stacks 01CI carries the unit of the pulled-back algebra to the unit. -/
theorem pullbackSymmetricPieceIso_one (hA : IsSymmetricAlgebra A ι)
    (hB : IsSymmetricAlgebra B κ) (U : (Opens X.carrier)ᵒᵖ) :
    (pullbackSymmetricPieceIso f hA hB 0).hom.val.app U
        ((pullbackGradedAlgebra f A).one.eval U) = B.one.eval U :=
  (isSymmetricAlgebra_pullbackGradedAlgebra f hA).isUniversal.pieceIso_one hB.isUniversal U

/-! ### At the constructed symmetric algebras

The statements above are quantified over symmetric algebras given by their universal property.
`SheafOfModules.ringedSpaceAlgebras` constructs one for every sheaf of modules on a ringed
space, so instantiating there shows the hypotheses are inhabited and gives the isomorphism
between the two constructed symmetric powers. -/

/-- **Stacks 01CI for the symmetric algebra, at the constructed symmetric algebras.** For a
morphism of ringed spaces `f : X ⟶ Y` and a sheaf of `𝒪_Y`-modules `F`, the pullback of the
degree-`n` symmetric power of `F` is the degree-`n` symmetric power of `f^*F`, both taken in
`SheafOfModules.ringedSpaceAlgebras`. -/
@[stacks 01CI "symmetric algebra, at the constructed symmetric algebras", ega "II 1.7.5" "partial"]
noncomputable def pullbackSymmetricPieceIsoOfRingedSpace
    (G : SheafOfModules.{u} (structureRingSheaf Y)) (n : ℤ) :
    (pullbackFunctor f).obj ((SheafOfModules.ringedSpaceAlgebras Y G).symmetric.piece n) ≅
      (SheafOfModules.ringedSpaceAlgebras X
        ((pullbackFunctor f).obj G)).symmetric.piece n :=
  pullbackSymmetricPieceIso f
    (SheafOfModules.ringedSpaceAlgebras Y G).symmetric_isSymmetricAlgebra
    (SheafOfModules.ringedSpaceAlgebras X
      ((pullbackFunctor f).obj G)).symmetric_isSymmetricAlgebra n

end Stacks.RingedSpace


end

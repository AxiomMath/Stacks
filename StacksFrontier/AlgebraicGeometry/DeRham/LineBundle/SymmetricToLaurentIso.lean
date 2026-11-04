module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerInvertible
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Laurent
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.CategoryTheory.IsIsoOfEqIsoHom

/-!
# The symmetric algebra of a line bundle against its Laurent algebra

Let `L` be an invertible module on a scheme `X`. The symmetric algebra `Sym(L)` and the Laurent
algebra `⨁_{n ∈ ℤ} L^{⊗ n}` are compared by the unique unital homomorphism
`Stacks.LineBundle.Situation.symmetricToLaurent` extending the degree-one generator, and that
comparison vanishes in negative degrees. This file identifies the nonnegative symmetric powers
of `L` with its tensor powers and settles the comparison in degree one.

The identification of the symmetric powers comes from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerInvertible`: the degree-one local
sections of the tensor algebra of an invertible module commute, so its tensor algebra is already
a symmetric algebra, and two symmetric algebras of one module are canonically isomorphic in
every degree. Transporting invertibility along that identification makes every nonnegative
symmetric power of `L` an invertible module, which is what reduces the comparison in a
nonnegative degree from an isomorphism to an epimorphism: both sides are then invertible, and an
epimorphism of invertible modules on a scheme is an isomorphism.

## Main definitions

* `Stacks.LineBundle.Situation.algebras`: the chosen tensor algebra of the line bundle with its
  exterior and symmetric quotients.
* `Stacks.LineBundle.Situation.symmetricPieceIsoAlgebras`: the degreewise comparison of `Sym(L)`
  with the symmetric quotient of that tensor algebra.
* `Stacks.LineBundle.Situation.symmetricPieceIsoTensorPower`: **`Symⁿ(L) ≅ L^{⊗ n}`** for the
  symmetric algebra of the line bundle and the `n`-fold tensor power of `L`, for `n : ℕ`.
* `Stacks.LineBundle.Situation.symmetricAlgebraGenIso` and
  `Stacks.LineBundle.Situation.laurentGenIso`: the degree-one identifications `L ≅ Sym¹(L)` and
  `L ≅ L^{⊗ 1}`.

## Main results

* `Stacks.LineBundle.Situation.isInvertible_symmetricAlgebra_piece` and
  `isInvertibleModule_symmetricAlgebra_piece`: **every nonnegative homogeneous piece of `Sym(L)`
  is an invertible module**, for both `Stacks.SheafOfModules.IsInvertible` and
  `AlgebraicGeometry.SheafOfModules.IsInvertible`.
* `Stacks.LineBundle.Situation.isSymmetricAlgebra_algebras_tensor`: the tensor algebra of the
  line bundle is a symmetric algebra of it.
* `Stacks.LineBundle.Situation.symmetricAlgebraGen_eq` and `isIso_symmetricAlgebraGen`: the
  degree-one generator `L ⟶ Sym¹(L)` of the symmetric algebra of the line bundle is an
  isomorphism.
* `Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_one`: **the comparison of `Sym(L)`
  with the Laurent algebra is an isomorphism in degree one.**
* `Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_of_epi` and
  `isIso_symmetricToLaurent_app_iff_epi`: **in a nonnegative degree the comparison is an
  isomorphism exactly when it is an epimorphism.**

## Implementation notes

The two spellings of the base of the category of modules on a scheme — `X.ringCatSheaf` and
`CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf` — agree definitionally,
being structure literals over the same presheaf of rings with a proposition for the second
component; the sheaf of commutative rings is nevertheless supplied by name when the chosen
package of algebras is formed, since reading it off the base would ask the elaborator to invert
a projection.

Degrees zero and at least two are settled in
`StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/SymmetricToLaurentEpi.lean`, which proves the
epimorphy the reduction above asks for and hence `IsIso (symmetricToLaurent.app n)` for every
`0 ≤ n`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The tensor algebra of the line bundle of a situation, with its exterior and symmetric
quotients**, as the chosen package of Section 17.21. -/
noncomputable def Situation.algebras :
    SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥D.X) D.L :=
  SheafOfModules.algebras (Osharp := D.X.sheaf) (Opens.grothendieckTopology ↥D.X) D.L

/-- The degree-one local sections of the tensor algebra of the line bundle commute, the symmetry
constraint of an invertible module with itself being the identity. -/
theorem Situation.pairwiseCommutes_tensorGenerator :
    SheafOfModules.GradedAlgebra.PairwiseCommutes D.algebras.tensorGenerator :=
  Stacks.SheafOfModules.pairwiseCommutes_tensorGenerator_of_isInvertible D.X.sheaf D.L
    D.algebras

/-- **The tensor algebra of the line bundle is a symmetric algebra of it**, its degree-one
sections commuting. -/
theorem Situation.isSymmetricAlgebra_algebras_tensor :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra D.algebras.tensor
      D.algebras.tensorGenerator :=
  D.algebras.isSymmetricAlgebra_tensor D.pairwiseCommutes_tensorGenerator

/-- The canonical degreewise comparison of the symmetric algebra of the line bundle with the
symmetric quotient of its chosen tensor algebra: two symmetric algebras of one module are
canonically isomorphic in every degree. -/
noncomputable def Situation.symmetricPieceIsoAlgebras (n : ℤ) :
    D.symmetricAlgebra.piece n ≅ D.algebras.symmetric.piece n :=
  SheafOfModules.GradedAlgebra.IsUniversal.pieceIso D.isSymmetricAlgebra_symmetricAlgebra
    D.algebras.symmetric_isSymmetricAlgebra n

/-- **`Symⁿ(L) ≅ L^{⊗ n}`:** the degree-`n` piece of the symmetric algebra of the line bundle is
the `n`-fold tensor power of `L`. The symmetric algebra of `L` is canonically isomorphic in each
degree to the tensor algebra of `L`, whose degree-`n` piece is that tensor power. -/
noncomputable def Situation.symmetricPieceIsoTensorPower (n : ℕ) :
    D.symmetricAlgebra.piece (n : ℤ) ≅
      SheafOfModules.tensorPower (Opens.grothendieckTopology ↥D.X) D.L n :=
  D.symmetricPieceIsoAlgebras (n : ℤ) ≪≫
    D.algebras.symmetricPowerIsoTensorPower D.pairwiseCommutes_tensorGenerator n

/-- **Every nonnegative homogeneous piece of the symmetric algebra of the line bundle is an
invertible module**, being a tensor power of an invertible module. -/
theorem Situation.isInvertible_symmetricAlgebra_piece (n : ℕ) :
    Stacks.SheafOfModules.IsInvertible D.X.presheaf D.X.ringCatSheaf.2
      (D.symmetricAlgebra.piece (n : ℤ)) :=
  @Stacks.SheafOfModules.isInvertible_of_iso _ _ _ D.X.presheaf D.X.ringCatSheaf.2 _ _ _ _
    (D.symmetricPieceIsoTensorPower n).symm
    (Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat D.L
      D.isInvertible_stacks n)

/-- Every nonnegative homogeneous piece of the symmetric algebra of the line bundle is
invertible in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem Situation.isInvertibleModule_symmetricAlgebra_piece (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible D.X.presheaf D.X.ringCatSheaf.2
      (D.symmetricAlgebra.piece (n : ℤ)) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    D.X.presheaf D.X.ringCatSheaf.2 _).mp (D.isInvertible_symmetricAlgebra_piece n)

/-- **`L ≅ Sym¹(L)`:** the degree-one generator of the symmetric algebra of the line bundle is an
isomorphism, since for an invertible module the symmetric algebra agrees with the tensor algebra,
whose degree-one piece is `L` itself. -/
noncomputable def Situation.symmetricAlgebraGenIso : D.L ≅ D.symmetricAlgebra.piece 1 :=
  D.algebras.symmetricGeneratorIso D.pairwiseCommutes_tensorGenerator ≪≫
    (D.symmetricPieceIsoAlgebras 1).symm

/-- The identification `L ≅ Sym¹(L)` is the degree-one generator of the symmetric algebra of the
line bundle. -/
theorem Situation.symmetricAlgebraGen_eq :
    D.symmetricAlgebraGen = D.symmetricAlgebraGenIso.hom :=
  (Iso.eq_comp_inv (D.symmetricPieceIsoAlgebras 1)).2
    ((SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_generator
        D.isSymmetricAlgebra_symmetricAlgebra D.algebras.symmetric_isSymmetricAlgebra).trans
      (D.algebras.symmetricGeneratorIso_hom D.pairwiseCommutes_tensorGenerator).symm)

/-- **The degree-one generator `L ⟶ Sym¹(L)` of the symmetric algebra of the line bundle is an
isomorphism.** -/
theorem Situation.isIso_symmetricAlgebraGen : IsIso D.symmetricAlgebraGen :=
  CategoryTheory.isIso_of_eq_iso_hom _ D.symmetricAlgebraGen_eq

/-- The degree-one generator `L ⟶ L^{⊗ 1}` of the Laurent algebra of the line bundle, as an
isomorphism: the first tensor power of `L` is `L`. -/
noncomputable def Situation.laurentGenIso : D.L ≅ D.laurentAlgebra.piece 1 :=
  (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
    D.X.ringCatSheaf.property D.L).symm

/-- **The comparison of the symmetric algebra of the line bundle with its Laurent algebra is an
isomorphism in degree one**: it is the composite of the inverse of the degree-one generator of
`Sym(L)` with the degree-one generator of the Laurent algebra, both isomorphisms. -/
theorem Situation.isIso_symmetricToLaurent_app_one : IsIso (D.symmetricToLaurent.app 1) :=
  CategoryTheory.isIso_of_eq_iso_hom (D.symmetricAlgebraGenIso.symm ≪≫ D.laurentGenIso)
    ((Iso.eq_inv_comp D.symmetricAlgebraGenIso).2
      ((congrArg (fun f => f ≫ D.symmetricToLaurent.app 1)
          D.symmetricAlgebraGen_eq).symm.trans
        D.symmetricAlgebraGen_comp_symmetricToLaurent))

/-- **In a nonnegative degree the comparison of the symmetric algebra of the line bundle with its
Laurent algebra is an isomorphism as soon as it is an epimorphism.** Its source is a symmetric
power of an invertible module, hence invertible, and so is its target; an epimorphism of
invertible modules on a scheme is an isomorphism. -/
theorem Situation.isIso_symmetricToLaurent_app_of_epi (n : ℕ)
    (h : Epi (D.symmetricToLaurent.app (n : ℤ))) :
    IsIso (D.symmetricToLaurent.app (n : ℤ)) :=
  @Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible D.X _ _ _ h
    (D.isInvertibleModule_symmetricAlgebra_piece n) (D.isInvertible_tensorPower (n : ℤ))

/-- **In a nonnegative degree the comparison of the symmetric algebra of the line bundle with its
Laurent algebra is an isomorphism exactly when it is an epimorphism**, both sides being
invertible modules. This is the remaining input in the form a local argument can attack:
epimorphy of a morphism of modules is local surjectivity. -/
theorem Situation.isIso_symmetricToLaurent_app_iff_epi (n : ℕ) :
    IsIso (D.symmetricToLaurent.app (n : ℤ)) ↔ Epi (D.symmetricToLaurent.app (n : ℤ)) :=
  ⟨fun _ => inferInstance, D.isIso_symmetricToLaurent_app_of_epi n⟩

end Stacks.LineBundle

end

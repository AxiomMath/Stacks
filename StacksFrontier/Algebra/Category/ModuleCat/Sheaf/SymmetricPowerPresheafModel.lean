module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerIsSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# The symmetric power of a sheaf of modules, from any presheaf model

Let `O` be a sheaf of commutative rings on a site `(C, J)`, let `F` be a sheaf of `O`-modules
and let `A` be a bundle of tensor, exterior and symmetric algebras on `F`
(`SheafOfModules.TensorExteriorSymmetricAlgebras`). If `P` is any presheaf of `O`-modules whose
sheafification is isomorphic to `F`, then the degree-`n` symmetric power
`Symⁿ F = A.symmetric.piece n` is the sheafification of `U ↦ Symⁿ_{O(U)}(P(U))`.

## Main results

* `SheafOfModules.isSymmetricAlgebra_sheafifyModulePresheaf`: the sheafified sectionwise
  symmetric algebra of `P` is a symmetric algebra of `F`, along the given isomorphism.
* `SheafOfModules.presheafModelSymmetricPowerIso`: the comparison
  `sheafify(U ↦ Symⁿ_{O(U)}(P(U))) ≅ Symⁿ F`, together with
  `presheafModelSymmetricPowerIso_one`, `_mul` and `_generator`: it carries the unit to the
  unit, is multiplicative on homogeneous local sections, and matches the degree-one generators.

## Implementation notes

`PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra` holds for an arbitrary presheaf
of modules, so the sheafified sectionwise symmetric algebra of `P` is a symmetric algebra of the
sheafification of `P`; `SheafOfModules.GradedAlgebra.isSymmetricAlgebra_ofIso` moves it along
`e` to a symmetric algebra of `F`, and two symmetric algebras of one sheaf of modules are compared
degreewise by `SheafOfModules.GradedAlgebra.IsUniversal.pieceIso`.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe v u w

namespace SheafOfModules

open PresheafOfModules Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (P : PresheafOfModules.{w} (toRingCat J Osharp).obj)

/-- The sheafification of a presheaf of modules over the structure sheaf. -/
noncomputable abbrev sheafifyModulePresheaf : SheafOfModules.{w} (toRingCat J Osharp) :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj P

variable {F : SheafOfModules.{w} (toRingCat J Osharp)}
  (A : TensorExteriorSymmetricAlgebras J F) (e : F ≅ sheafifyModulePresheaf J P)

/-- The sheafified sectionwise symmetric algebra of a presheaf model `P` of `F` is a symmetric
algebra of `F`, along `e : F ≅ sheafifyModulePresheaf J P`. -/
theorem isSymmetricAlgebra_sheafifyModulePresheaf :
    GradedAlgebra.IsSymmetricAlgebra
      ((symPowIntGradedAlgebra P).sheafify (𝟙 (toRingCat J Osharp).obj))
      (e.hom ≫ (symPowIntGradedAlgebra P).sheafifyGen
        (𝟙 (toRingCat J Osharp).obj) (symPowIntGen P)) :=
  GradedAlgebra.isSymmetricAlgebra_ofIso e
    (isSymmetricAlgebra_sheafify_symmetricAlgebra (𝟙 (toRingCat J Osharp).obj) P)

/-- The comparison between the sheafification of the sectionwise degree-`n` symmetric power of a
presheaf model `P` of `F` and the degree-`n` symmetric power of `F`. -/
noncomputable def presheafModelSymmetricPowerIso (n : ℤ) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
        (symPowInt n P) ≅ A.symmetric.piece n :=
  GradedAlgebra.IsUniversal.pieceIso
    (isSymmetricAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.symmetric_isSymmetricAlgebra.isUniversal n

/-- The comparison carries the unit to the unit. -/
theorem presheafModelSymmetricPowerIso_one (X : Cᵒᵖ) :
    (presheafModelSymmetricPowerIso J P A e 0).hom.val.app X
        (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt 0 P)) X ((symPowIntGradedAlgebra P).one.eval X)) =
      A.symmetric.one.eval X :=
  GradedAlgebra.IsUniversal.pieceIso_one
    (isSymmetricAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.symmetric_isSymmetricAlgebra.isUniversal X

/-- The comparison is multiplicative on homogeneous local sections. -/
theorem presheafModelSymmetricPowerIso_mul (i j : ℤ) (X : Cᵒᵖ)
    (x : ((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
      (symPowInt i P)).val.obj X)
    (y : ((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
      (symPowInt j P)).val.obj X) :
    (presheafModelSymmetricPowerIso J P A e (i + j)).hom.val.app X
        (((symPowIntGradedAlgebra P).sheafify
          (𝟙 (toRingCat J Osharp).obj)).mul i j |>.app X x y) =
      (A.symmetric.mul i j).app X
        ((presheafModelSymmetricPowerIso J P A e i).hom.val.app X x)
        ((presheafModelSymmetricPowerIso J P A e j).hom.val.app X y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul
    (isSymmetricAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.symmetric_isSymmetricAlgebra.isUniversal i j X x y

/-- The comparison matches the degree-one generators. -/
theorem presheafModelSymmetricPowerIso_generator :
    (e.hom ≫ (symPowIntGradedAlgebra P).sheafifyGen
          (𝟙 (toRingCat J Osharp).obj) (symPowIntGen P)) ≫
        (presheafModelSymmetricPowerIso J P A e 1).hom =
      A.symmetricGenerator :=
  GradedAlgebra.IsUniversal.pieceIso_generator
    (isSymmetricAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.symmetric_isSymmetricAlgebra.isUniversal

end SheafOfModules

end

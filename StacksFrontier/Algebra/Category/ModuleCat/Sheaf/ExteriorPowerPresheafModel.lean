module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresheafModel

/-!
# The exterior power of a sheaf of modules, from any presheaf model

Let `O` be a sheaf of commutative rings on a site `(C, J)`, let `F` be a sheaf of `O`-modules
and let `A` be a bundle of tensor, exterior and symmetric algebras on `F`
(`SheafOfModules.TensorExteriorSymmetricAlgebras`). If `P` is any presheaf of `O`-modules whose
sheafification is isomorphic to `F`, then the degree-`n` exterior power
`⋀ⁿ F = A.exterior.piece n` is the sheafification of `U ↦ ⋀ⁿ_{O(U)}(P(U))`.

## Main results

* `SheafOfModules.isExteriorAlgebra_sheafifyModulePresheaf`: the sheafified sectionwise exterior
  algebra of `P` is an exterior algebra *of `F`*, along the given isomorphism.
* `SheafOfModules.presheafModelExteriorPowerIso`: the comparison
  `sheafify(U ↦ ⋀ⁿ_{O(U)}(P(U))) ≅ ⋀ⁿ F`, together with `presheafModelExteriorPowerIso_one`,
  `_mul` and `_generator`: it carries the unit to the unit, is multiplicative on homogeneous local
  sections, and matches the degree-one generators.

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

variable {F : SheafOfModules.{w} (toRingCat J Osharp)}
  (A : TensorExteriorSymmetricAlgebras J F) (e : F ≅ sheafifyModulePresheaf J P)

/-- The sheafified sectionwise exterior algebra of a presheaf model of `F` is an exterior algebra
of `F`. -/
theorem isExteriorAlgebra_sheafifyModulePresheaf :
    GradedAlgebra.IsExteriorAlgebra
      ((exteriorAlgebraGradedAlgebra P).sheafify (𝟙 (toRingCat J Osharp).obj))
      (e.hom ≫ (exteriorAlgebraGradedAlgebra P).sheafifyGen
        (𝟙 (toRingCat J Osharp).obj) (exteriorAlgebraGen P)) :=
  GradedAlgebra.isExteriorAlgebra_ofIso e
    (isExteriorAlgebra_sheafify_exteriorAlgebra (𝟙 (toRingCat J Osharp).obj) P)

/-- The exterior power of a sheaf of modules is the sheafification of the sectionwise exterior
power of any presheaf model of it. -/
noncomputable def presheafModelExteriorPowerIso (n : ℤ) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
        (exteriorAlgebraPiece n P) ≅ A.exterior.piece n :=
  GradedAlgebra.IsUniversal.pieceIso
    (isExteriorAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.exterior_isExteriorAlgebra.isUniversal n

/-- The comparison carries the unit to the unit. -/
theorem presheafModelExteriorPowerIso_one (X : Cᵒᵖ) :
    (presheafModelExteriorPowerIso J P A e 0).hom.val.app X
        (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (exteriorAlgebraPiece 0 P)) X ((exteriorAlgebraGradedAlgebra P).one.eval X)) =
      A.exterior.one.eval X :=
  GradedAlgebra.IsUniversal.pieceIso_one
    (isExteriorAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.exterior_isExteriorAlgebra.isUniversal X

/-- The comparison is multiplicative on homogeneous local sections. -/
theorem presheafModelExteriorPowerIso_mul (i j : ℤ) (X : Cᵒᵖ)
    (x : ((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
      (exteriorAlgebraPiece i P)).val.obj X)
    (y : ((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
      (exteriorAlgebraPiece j P)).val.obj X) :
    (presheafModelExteriorPowerIso J P A e (i + j)).hom.val.app X
        (((exteriorAlgebraGradedAlgebra P).sheafify
          (𝟙 (toRingCat J Osharp).obj)).mul i j |>.app X x y) =
      (A.exterior.mul i j).app X
        ((presheafModelExteriorPowerIso J P A e i).hom.val.app X x)
        ((presheafModelExteriorPowerIso J P A e j).hom.val.app X y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul
    (isExteriorAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.exterior_isExteriorAlgebra.isUniversal i j X x y

/-- The comparison matches the degree-one generators. -/
theorem presheafModelExteriorPowerIso_generator :
    (e.hom ≫ (exteriorAlgebraGradedAlgebra P).sheafifyGen
          (𝟙 (toRingCat J Osharp).obj) (exteriorAlgebraGen P)) ≫
        (presheafModelExteriorPowerIso J P A e 1).hom =
      A.exteriorGenerator :=
  GradedAlgebra.IsUniversal.pieceIso_generator
    (isExteriorAlgebra_sheafifyModulePresheaf J P e).isUniversal
    A.exterior_isExteriorAlgebra.isUniversal

end SheafOfModules

end

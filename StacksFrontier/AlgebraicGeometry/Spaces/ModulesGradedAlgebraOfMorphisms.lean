module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraOfLocalizedMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Sheaves of graded algebras on an algebraic space from morphism-level data

Let `F` be an algebraic space.  A multiplication `M_i ⊗ M_j ⟶ M_{i+j}` on a degreewise family of
`𝒪_F`-modules, for the tensor product `AlgebraicGeometry.Space.modulesMonoidalCategory` of
`𝒪_F`-modules, together with a unit `𝒪_F ⟶ M_0`, associative and unital as equalities of
morphisms, is a sheaf of graded `𝒪_F`-algebras in the sense of `SheafOfModules.GradedAlgebra`.
This is `SheafOfModules.GradedAlgebra.ofLocalizedMorphismData` for the structure sheaf of the
small étale site of `F`.

## Main definitions

* `AlgebraicGeometry.Space.modulesGradedAlgebraOfMorphisms`: the sheaf of graded `𝒪_F`-algebras.

## Main results

* `AlgebraicGeometry.Space.modulesGradedAlgebraOfMorphisms_piece`,
  `AlgebraicGeometry.Space.mulSheaf_modulesGradedAlgebraOfMorphisms` and
  `AlgebraicGeometry.Space.oneHom_modulesGradedAlgebraOfMorphisms`: its pieces, its
  morphism-level multiplication and its morphism-level unit are the given ones.
* `AlgebraicGeometry.Space.modulesGradedAlgebraOfMorphisms_mul_comm`: a multiplication commuting
  with the braiding of `𝒪_F`-modules gives commuting homogeneous local sections.

## Implementation notes

The data are stated for `AlgebraicGeometry.Space.Modules` and its tensor product, and are passed to
`SheafOfModules.GradedAlgebra.ofLocalizedMorphismData` eta-expanded. The general lemmas are applied
with the structure sheaf and its sheaf condition passed explicitly: left as metavariables, the
instances of the site are synthesized before the site is known and the elaborator is left with an
unsolvable universe constraint.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (piece : ℤ → Modules.{u, u} B S hS F hF) (mul : ∀ i j : ℤ, piece i ⊗ piece j ⟶ piece (i + j))
  (one : 𝟙_ (Modules.{u, u} B S hS F hF) ⟶ piece 0)
  (hassoc : ∀ i j k : ℤ, mul i j ▷ piece k ≫ mul (i + j) k =
    (α_ (piece i) (piece j) (piece k)).hom ≫ piece i ◁ mul j k ≫ mul i (j + k) ≫
      eqToHom (congrArg piece (add_assoc i j k).symm))
  (hone : ∀ i : ℤ, one ▷ piece i ≫ mul 0 i =
    (λ_ (piece i)).hom ≫ eqToHom (congrArg piece (zero_add i).symm))
  (hone' : ∀ i : ℤ, piece i ◁ one ≫ mul i 0 =
    (ρ_ (piece i)).hom ≫ eqToHom (congrArg piece (add_zero i).symm))

/-- **A sheaf of graded `𝒪_F`-algebras on an algebraic space `F` from morphism-level data**:
`SheafOfModules.GradedAlgebra.ofLocalizedMorphismData` for the tensor product
`AlgebraicGeometry.Space.modulesMonoidalCategory` of `𝒪_F`-modules. -/
def modulesGradedAlgebraOfMorphisms :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS ⟨F, hF⟩) :=
  SheafOfModules.GradedAlgebra.ofLocalizedMorphismData (structureSheaf B S hS F hF)
    (structureRingPresheaf_isSheaf B S hS F hF) piece mul one (fun i j k => hassoc i j k)
    (fun i => hone i) (fun i => hone' i)

/-- The homogeneous pieces of `modulesGradedAlgebraOfMorphisms` are the given ones. -/
theorem modulesGradedAlgebraOfMorphisms_piece (n : ℤ) :
    (modulesGradedAlgebraOfMorphisms B S hS F hF piece mul one hassoc hone hone').piece n =
      piece n :=
  rfl

/-- **The morphism-level multiplication of `modulesGradedAlgebraOfMorphisms` is the given one**,
read out of the tensor product sheaf through `AlgebraicGeometry.Space.modulesTensorObjIso`. -/
theorem mulSheaf_modulesGradedAlgebraOfMorphisms (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u}
        (modulesGradedAlgebraOfMorphisms B S hS F hF piece mul one hassoc hone hone') i j =
      (modulesTensorObjIso B S hS F hF (piece i) (piece j)).inv ≫ mul i j :=
  SheafOfModules.GradedAlgebra.mulSheaf_ofLocalizedMorphismData (structureSheaf B S hS F hF)
    (structureRingPresheaf_isSheaf B S hS F hF) piece mul one
    (fun i j k => hassoc i j k) (fun i => hone i) (fun i => hone' i) i j

/-- **The morphism-level unit of `modulesGradedAlgebraOfMorphisms` is the given one.** -/
theorem oneHom_modulesGradedAlgebraOfMorphisms :
    SheafOfModules.GradedAlgebra.oneHom.{u, u + 1, u}
        (modulesGradedAlgebraOfMorphisms B S hS F hF piece mul one hassoc hone hone') = one :=
  SheafOfModules.GradedAlgebra.oneHom_ofLocalizedMorphismData (structureSheaf B S hS F hF)
    (structureRingPresheaf_isSheaf B S hS F hF) piece mul one
    (fun i j k => hassoc i j k) (fun i => hone i) (fun i => hone' i)

/-- **A commutative multiplication gives a commutative sheaf of graded `𝒪_F`-algebras**: if
`β ≫ mul j i = mul i j`, up to the identification of the degrees, for the braiding
`AlgebraicGeometry.Space.modulesBraidedCategory` of `𝒪_F`-modules, then homogeneous local sections
of `modulesGradedAlgebraOfMorphisms` commute. -/
theorem modulesGradedAlgebraOfMorphisms_mul_comm
    (hcomm : letI := modulesBraidedCategory B S hS F hF
      ∀ i j : ℤ, (β_ (piece i) (piece j)).hom ≫ mul j i =
        mul i j ≫ eqToHom (congrArg piece (add_comm i j)))
    (i j : ℤ) (U : (SmallEtale B S hS F)ᵒᵖ) (x : (piece i).val.obj U) (y : (piece j).val.obj U) :
    HEq (((modulesGradedAlgebraOfMorphisms B S hS F hF piece mul one hassoc hone hone').mul i
        j).app U x y)
      (((modulesGradedAlgebraOfMorphisms B S hS F hF piece mul one hassoc hone hone').mul j
        i).app U y x) :=
  SheafOfModules.GradedAlgebra.ofLocalizedMorphismData_mul_comm (structureSheaf B S hS F hF)
    (structureRingPresheaf_isSheaf B S hS F hF) piece mul one
    (fun i j k => hassoc i j k) (fun i => hone i) (fun i => hone' i) (fun i j => hcomm i j)
    i j U x y

end AlgebraicGeometry.Space

end

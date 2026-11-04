module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback

/-!
# The Laurent algebra is functorial in the invertible module

Let `T` be a scheme and `L`, `L'` invertible `𝒪_T`-modules. This file builds, from an isomorphism
`e : L ≅ L'`, an isomorphism

`⨁_{n ∈ ℤ} L^{⊗ n} ≅ ⨁_{n ∈ ℤ} (L')^{⊗ n}`

**of sheaves of graded algebras**, and identifies its degree-one component.

## Main definitions

The declarations below are in the namespace
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr`.

* `laurentCongrHom` and `laurentCongrInv`: the degreewise comparison and its inverse, as
  homomorphisms of sheaves of graded algebras.
* `laurentCongrIso`: an isomorphism `L ≅ L'` induces an isomorphism of the Laurent algebras.

## Main results

* `congrIso_mulSheaf`: the degreewise comparison commutes with the multiplications of the two
  Laurent algebras.
* `laurentCongrIso_app`: the components of the isomorphism are the degreewise comparisons.
* `laurentCongrIso_app_one`: the degree-one component is the given isomorphism, read through the
  identifications `L^{⊗ 1} = L` and `(L')^{⊗ 1} = L'` of Tag 01CU.

## Implementation notes

The degreewise comparison is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso`.
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr` is the same comparison in a second encoding,
so `congrIso` duplicates it.

The inverse is built degreewise as the inverse of each component, rather than as
`laurentCongrHom e.symm`, so that the two round-trip identities are those of the components.

The rearrangement in the multiplicativity of the inverse is `inv_square`, stated in a bare
category: in place, the goal mixes `Stacks.RingedSpace.structureRingSheaf` with
`Stacks.SheafOfModules.Tensor.sheafTensor` and is not type-correct at `implicit` transparency, and
`rw` then reports a missing pattern rather than the cause.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T : Scheme.{u}}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- **The degreewise comparison commutes with the multiplications of the two Laurent algebras**,
in the `SheafOfModules.GradedAlgebra.mulSheaf` vocabulary that a homomorphism of sheaves of
graded algebras is stated in. -/
theorem congrIso_mulSheaf (e : L ≅ L') (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (laurent L) i j ≫ (congrIso e (i + j)).hom =
      ((congrIso e i).hom ⊗ₘ (congrIso e j).hom) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent L') i j := by
  rw [mulSheaf_laurent, mulSheaf_laurent]
  exact congrIso_mul e i j

/-- **The degreewise comparison, as a homomorphism of sheaves of graded algebras.** -/
def laurentCongrHom (e : L ≅ L') : laurent L ⟶ laurent L' :=
  homOfMulSheaf _ _ (fun n => (congrIso e n).hom) (congrIso_mulSheaf e)

/-- The components of `laurentCongrHom e` are the degreewise comparisons. -/
@[simp] theorem laurentCongrHom_app (e : L ≅ L') (n : ℤ) :
    (laurentCongrHom e).app n = (congrIso e n).hom := rfl

/-- Inverting a commuting square: if `u ≫ b.hom = a ≫ v` and `a' ≫ a = 𝟙`, then
`v ≫ b.inv = a' ≫ u`. -/
private theorem inv_square {C : Type*} [Category C] {A B A' B' : C}
    (u : A ⟶ B) (v : A' ⟶ B') (a : A ⟶ A') (a' : A' ⟶ A) (b : B ≅ B')
    (haa : a' ≫ a = CategoryStruct.id A') (h : u ≫ b.hom = a ≫ v) :
    v ≫ b.inv = a' ≫ u := by
  rw [← Category.id_comp (v ≫ b.inv), ← haa, Category.assoc, ← Category.assoc a v,
    ← h, Category.assoc, b.hom_inv_id, Category.comp_id]

/-- The componentwise inverse commutes with the two multiplications. -/
theorem congrIso_inv_mulSheaf (e : L ≅ L') (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (laurent L') i j ≫ (congrIso e (i + j)).inv =
      ((congrIso e i).inv ⊗ₘ (congrIso e j).inv) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent L) i j := by
  exact inv_square _ _ _ _ (congrIso e (i + j))
    (MonoidalCategory.tensorIso (congrIso e i) (congrIso e j)).inv_hom_id (congrIso_mulSheaf e i j)

/-- **The componentwise inverse, as a homomorphism of sheaves of graded algebras.** -/
def laurentCongrInv (e : L ≅ L') : laurent L' ⟶ laurent L :=
  homOfMulSheaf _ _ (fun n => (congrIso e n).inv) (congrIso_inv_mulSheaf e)

/-- The components of `laurentCongrInv e` are the inverses of the degreewise comparisons. -/
@[simp] theorem laurentCongrInv_app (e : L ≅ L') (n : ℤ) :
    (laurentCongrInv e).app n = (congrIso e n).inv := rfl

/-- **The Laurent algebra of an invertible module is functorial in that module**: an isomorphism
`e : L ≅ L'` of invertible `𝒪_T`-modules induces an isomorphism
`⨁_n L^{⊗ n} ≅ ⨁_n (L')^{⊗ n}` of sheaves of graded algebras. -/
def laurentCongrIso (e : L ≅ L') : laurent L ≅ laurent L' where
  hom := laurentCongrHom e
  inv := laurentCongrInv e
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun n => (congrIso e n).hom_inv_id
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun n => (congrIso e n).inv_hom_id

/-- The forward map of `laurentCongrIso e` is `laurentCongrHom e`. -/
@[simp] theorem laurentCongrIso_hom (e : L ≅ L') :
    (laurentCongrIso e).hom = laurentCongrHom e := rfl

/-- The components of `laurentCongrIso e` are the degreewise comparisons. -/
@[simp] theorem laurentCongrIso_app (e : L ≅ L') (n : ℤ) :
    (laurentCongrIso e).hom.app n = (congrIso e n).hom := rfl

/-- **The degree-one component of the induced isomorphism is the given isomorphism**, read
through the identifications `L^{⊗ 1} = L` and `(L')^{⊗ 1} = L'` of Tag 01CU. -/
theorem laurentCongrIso_app_one (e : L ≅ L') :
    (laurentCongrIso e).hom.app 1 =
      (oneIsoL L).hom ≫ e.hom ≫ (oneIsoL L').inv := by
  refine Eq.trans (laurentCongrIso_app e 1) ?_
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv (oneIsoL L')).mpr (congrIso_oneIso e).symm

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

end

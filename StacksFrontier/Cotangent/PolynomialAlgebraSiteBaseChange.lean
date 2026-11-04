module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the site of a polynomial algebra

Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings. Then extension of scalars `P ↦ A' ⊗_A P` carries a polynomial
`A`-algebra augmented to `B` to a polynomial `A'`-algebra augmented to `B'`, the augmentation of
`A' ⊗_A P` being `a' ⊗ p ↦ a' · b(α(p))`. This file builds the resulting functor of sites

```
C_{B/A} ⟶ C_{B'/A'}
```

which is the horizontal arrow underlying the right-hand square of the double square of Stacks
08QN.

## Main definitions

* `CommAlgCat.baseChangeAugmentation`: the augmentation `A' ⊗_A P → B'`.
* `CommAlgCat.baseChangeOver`: extension of scalars on `A`-algebras augmented to `B`.
* `CommAlgCat.polynomialBaseChangeAugmentations` and `CommAlgCat.polynomialBaseChange`: the same
  functor restricted to polynomial algebras, and its opposite, the functor of sites.

## Main results

* `CommAlgCat.baseChangeAugmentation_tmul` and `CommAlgCat.baseChangeMap_tmul`: the
  augmentation and the action on morphisms, on a pure tensor.
* `CommAlgCat.isPolynomialAlgebra_baseChange`: extension of scalars takes a polynomial algebra to
  a polynomial algebra, since `A' ⊗_A A[S] = A'[S]`.

## Implementation notes

The square of rings is presented as `[Algebra A A']`, `[Algebra A B']`,
`[IsScalarTower A A' B']` together with an `A`-algebra map `b : B → B'`. That is the same datum
as four ring maps and a commutativity hypothesis — the commutativity is `b.commutes` on one edge
and `IsScalarTower.algebraMap_eq` on the other — and it is the form in which Mathlib's tensor
products are stated, so no transport along a `RingHom` equality is needed.

## References

* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace CommAlgCat

universe u

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u))

/-! ### Extension of scalars on augmented algebras -/

/-- The extension of scalars `A' ⊗_A P` of an `A`-algebra, as an `A'`-algebra. -/
abbrev baseChangeObj (P : CommAlgCat.{u} A) : CommAlgCat.{u} A' :=
  CommAlgCat.of A' (A' ⊗[A] (P : Type u))

/-- The augmentation of the extension of scalars: `a' ⊗ p ↦ a' · b(α(p))`, where `α` is the
augmentation of `P` to `B`. -/
def baseChangeAugmentation (X : Over B) :
    (A' ⊗[A] (X.left : Type u)) →ₐ[A'] (B' : Type u) :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId A' (B' : Type u))
    (b.comp X.hom.hom)

/-- The augmentation of `A' ⊗_A P` sends `a' ⊗ p` to `a' · b(α(p))`. -/
@[simp, stacks 08QN "base-change augmentation on a pure tensor"]
theorem baseChangeAugmentation_tmul (X : Over B) (a' : A') (p : (X.left : Type u)) :
    baseChangeAugmentation b X (a' ⊗ₜ[A] p) =
      algebraMap A' (B' : Type u) a' * b (X.hom.hom p) := by
  simp [baseChangeAugmentation, Algebra.TensorProduct.productLeftAlgHom, Algebra.ofId_apply]

/-- Extension of scalars on a morphism of augmented algebras: `a' ⊗ p ↦ a' ⊗ f(p)`. -/
def baseChangeMap {X Y : Over B} (f : X ⟶ Y) :
    (A' ⊗[A] (X.left : Type u)) →ₐ[A'] (A' ⊗[A] (Y.left : Type u)) :=
  Algebra.TensorProduct.map (AlgHom.id A' A') f.left.hom

/-- Extension of scalars of a morphism `f` of augmented algebras sends `a' ⊗ p` to `a' ⊗ f(p)`. -/
@[simp, stacks 08QN "base change of a morphism on a pure tensor"]
theorem baseChangeMap_tmul {X Y : Over B} (f : X ⟶ Y) (a' : A') (p : (X.left : Type u)) :
    baseChangeMap f (a' ⊗ₜ[A] p) = a' ⊗ₜ[A] f.left.hom p := by
  simp [baseChangeMap]

/-- Extension of scalars of a morphism `f : X ⟶ Y` of `A`-algebras augmented to `B` commutes with
the augmentations of `A' ⊗_A X` and `A' ⊗_A Y` to `B'`. -/
theorem baseChangeMap_comp_augmentation {X Y : Over B} (f : X ⟶ Y) :
    CommAlgCat.ofHom (baseChangeMap f) ≫ CommAlgCat.ofHom (baseChangeAugmentation b Y) =
      CommAlgCat.ofHom (baseChangeAugmentation b X) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      have h : (Y.hom.hom) (f.left.hom y) = (X.hom.hom) y :=
        congrArg (fun k : X.left ⟶ B => k.hom y) f.w
      simp [h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Extension of scalars as a functor from `A`-algebras augmented to `B` to `A'`-algebras
augmented to `B'`. -/
def baseChangeOver : Over B ⥤ Over B' where
  obj X := Over.mk (CommAlgCat.ofHom (baseChangeAugmentation b X))
  map {_ _} f := Over.homMk (CommAlgCat.ofHom (baseChangeMap f))
    (baseChangeMap_comp_augmentation b f)
  map_id X := by
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp {X Y Z} f g := by
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The augmentation of `baseChangeOver b` applied to `X` is `baseChangeAugmentation b X`. -/
@[simp]
theorem baseChangeOver_obj_hom (X : Over B) :
    ((baseChangeOver b).obj X).hom = CommAlgCat.ofHom (baseChangeAugmentation b X) := rfl

/-- The underlying algebra map of `baseChangeOver b` applied to `f` is `baseChangeMap f`. -/
@[simp]
theorem baseChangeOver_map_left {X Y : Over B} (f : X ⟶ Y) :
    ((baseChangeOver b).map f).left = CommAlgCat.ofHom (baseChangeMap f) := rfl

/-! ### The functor of sites -/

/-- Extension of scalars takes a polynomial `A`-algebra to a polynomial `A'`-algebra:
`A' ⊗_A A[S] = A'[S]`. -/
@[stacks 08QN "base change preserves polynomial algebras"]
theorem isPolynomialAlgebra_baseChange (P : CommAlgCat.{u} A)
    (hP : IsPolynomialAlgebra A P) :
    IsPolynomialAlgebra A' (baseChangeObj (A' := A') P) := by
  obtain ⟨ι, ⟨e⟩⟩ := hP
  refine ⟨ι, ⟨?_⟩⟩
  have hf : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id A' A') e.toAlgHom) :=
    Algebra.TensorProduct.map_bijective
      (f := (AlgHom.id A' A').restrictScalars A) (g := e.toAlgHom)
      Function.bijective_id e.bijective
  exact (MvPolynomial.scalarRTensorAlgEquiv (R := A) (N := A') (σ := ι)).symm.trans
    (AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id A' A') e.toAlgHom) hf)

/-- Extension of scalars as a functor between the categories of *polynomial* algebras augmented
to `B` and to `B'`. -/
def polynomialBaseChangeAugmentations :
    PolynomialAugmentation A B ⥤ PolynomialAugmentation A' B' :=
  (IsPolynomialAlgebraOver A' B').lift
    ((IsPolynomialAlgebraOver A B).ι ⋙ baseChangeOver b)
    (fun X => isPolynomialAlgebra_baseChange X.obj.left X.property)

/-- The functor of sites `C_{B/A} ⟶ C_{B'/A'}` induced by a commutative square of rings,
given by extension of scalars on polynomial algebras augmented to `B`. -/
@[stacks 08QN "polynomial-site base change"]
def polynomialBaseChange : polynomialSite A B ⥤ polynomialSite A' B' :=
  (polynomialBaseChangeAugmentations b).op

/-- The augmentation of the image of `X` under `polynomialBaseChange b` is
`baseChangeAugmentation b X`. -/
@[simp, stacks 08QN "polynomial-site base change on objects"]
theorem polynomialBaseChange_obj_hom (X : polynomialSite A B) :
    ((polynomialBaseChange b).obj X).unop.obj.hom =
      CommAlgCat.ofHom (baseChangeAugmentation b X.unop.obj) := rfl

/-- The underlying algebra map of the image of `f` under `polynomialBaseChange b` is
`baseChangeMap f`. -/
@[simp, stacks 08QN "polynomial-site base change on morphisms"]
theorem polynomialBaseChange_map_left {X Y : polynomialSite A B} (f : X ⟶ Y) :
    ((polynomialBaseChange b).map f).unop.hom.left =
      CommAlgCat.ofHom (baseChangeMap f.unop.hom) := rfl

end CommAlgCat

end

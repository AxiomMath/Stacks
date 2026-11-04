module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.Monoidal
public import StacksFrontier.Homology.Tor.CrossProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# The graded Tor algebra: definitions

The `ℤ`-graded family of Tor modules `GradedTor.torPiece`, its functoriality
`GradedTor.torPieceMap`, the multiplication `GradedTor.torMultiplication` in nonnegative
degrees, and the structures `GradedTor.Algebra` and `GradedTor.AlgebraHom` of graded Tor
algebras and their homomorphisms.
-/

universe u uR uA v

@[expose] public noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace GradedTor

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [_root_.Algebra R A]

/-- An `R`-algebra, transported to the common universe in which the Tor construction is
performed. -/
public abbrev liftedAlgebra (_A : Type uA) (B : AlgCat.{v, uR} R) :
    AlgCat.{max uR uA v, uR} R :=
  AlgCat.of R (ULift.{max uR uA, v} B)

/-- The underlying module of an `R`-algebra in the common universe used for Tor. -/
public abbrev liftedModule (A : Type uA) (B : AlgCat.{v, uR} R) :
    ModuleCat.{max uR uA v} R :=
  ModuleCat.of R (liftedAlgebra R A B)

/-- The lift of an `R`-algebra map to the common universe used for Tor. -/
public def liftedMap (A : Type uA) {B C : AlgCat.{v, uR} R} (g : B ⟶ C) :
    liftedAlgebra R A B ⟶ liftedAlgebra R A C :=
  AlgCat.ofHom <|
    ULift.algEquiv.symm.toAlgHom.comp (g.hom.comp ULift.algEquiv.toAlgHom)

/-- The monoidal tensor product of two `A`-modules. -/
public abbrev moduleTensor (X Y : ModuleCat.{max uA v} A) : ModuleCat.{max uA v} A :=
  (RingTheory.TorProducts.tensorBifunctor.{uA, v} A).obj (X, Y)

/-- The zero `A`-module in the common universe used for Tor. -/
public abbrev zeroModule (_R : Type uR) (A : Type uA) [CommRing A] :
    ModuleCat.{max uR uA v} A :=
  ModuleCat.of A (ULift.{max uR v, uA} (Fin 0 → A))

/-- The degree-`i` piece of `Tor⁽ᴿ⁾⋆(B, A)`, extended by zero in negative degrees. -/
public noncomputable def torPiece (B : AlgCat.{v, uR} R) :
    ℤ → ModuleCat.{max uR uA v} A
  | .ofNat n =>
    (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A n).obj (liftedModule R A B)
  | .negSucc _ => zeroModule.{uR, uA, v} R A

/-- In a nonnegative degree, `torPiece` is the corresponding Tor module. -/
@[simp]
public lemma torPiece_ofNat (B : AlgCat.{v, uR} R) (n : ℕ) :
    torPiece.{uR, uA, v} R A B (n : ℤ) =
      (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A n).obj
        (liftedModule R A B) := rfl

/-- Every negative graded piece of graded Tor is the zero module. -/
@[simp]
public lemma torPiece_negSucc (B : AlgCat.{v, uR} R) (n : ℕ) :
    torPiece.{uR, uA, v} R A B (Int.negSucc n) = zeroModule.{uR, uA, v} R A := rfl

/-- The degreewise map on graded Tor induced by an `R`-algebra map. -/
public noncomputable def torPieceMap {B C : AlgCat.{v, uR} R} (g : B ⟶ C) :
    (i : ℤ) → (torPiece.{uR, uA, v} R A B i ⟶ torPiece.{uR, uA, v} R A C i)
  | .ofNat n =>
    (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A n).map
      (ModuleCat.ofHom (liftedMap R A g).hom.toLinearMap)
  | .negSucc _ => 0

/-- In a nonnegative degree, the induced map is the map of the Tor functor. -/
public lemma torPieceMap_ofNat {B C : AlgCat.{v, uR} R} (g : B ⟶ C) (n : ℕ) :
    torPieceMap.{uR, uA, v} R A g n =
      (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A n).map
        (ModuleCat.ofHom (liftedMap R A g).hom.toLinearMap) := rfl

/-- In negative degrees the induced map is zero. -/
@[simp]
public lemma torPieceMap_negSucc {B C : AlgCat.{v, uR} R} (g : B ⟶ C) (n : ℕ) :
    torPieceMap.{uR, uA, v} R A g (Int.negSucc n) = 0 := rfl

/-- Multiplication in nonnegative degrees: the canonical Tor cross product, followed by the map on
Tor induced by multiplication `B ⊗[R] B → B`. -/
@[sga "6 VII 2.1" "partial"]
public noncomputable def torMultiplication (B : AlgCat.{v, uR} R) (n m : ℕ) :
    moduleTensor.{uA, max uR v} A
      (torPiece.{uR, uA, v} R A B (n : ℤ)) (torPiece.{uR, uA, v} R A B (m : ℤ)) ⟶
      torPiece.{uR, uA, v} R A B ((n + m : ℕ) : ℤ) :=
  (RingTheory.TorProducts.torProduct.{uR, uA, v} R A n m).app
      (liftedModule R A B, liftedModule R A B) ≫
    (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A (n + m)).map
      (ModuleCat.ofHom (TensorProduct.lift
        (LinearMap.mul R (liftedAlgebra R A B))))

/-- A unital `ℤ`-graded `A`-algebra structure on the fixed family of Tor modules. -/
public structure Algebra (B : AlgCat.{v, uR} R) where
  /-- The unit in degree zero. -/
  one : torPiece.{uR, uA, v} R A B 0
  /-- Multiplication of homogeneous elements. -/
  mul (i j : ℤ) : moduleTensor.{uA, max uR v} A
      (torPiece.{uR, uA, v} R A B i) (torPiece.{uR, uA, v} R A B j) ⟶
    torPiece.{uR, uA, v} R A B (i + j)
  /-- Left multiplication by the unit is the identity. -/
  one_mul (i : ℤ) (x : torPiece.{uR, uA, v} R A B i) :
    cast (by rw [zero_add]) (mul 0 i (one ⊗ₜ[A] x)) = x
  /-- Right multiplication by the unit is the identity. -/
  mul_one (i : ℤ) (x : torPiece.{uR, uA, v} R A B i) :
    cast (by rw [add_zero]) (mul i 0 (x ⊗ₜ[A] one)) = x
  /-- Multiplication is associative. -/
  mul_assoc (i j k : ℤ) (x : torPiece.{uR, uA, v} R A B i) (y : torPiece.{uR, uA, v} R A B j)
      (z : torPiece.{uR, uA, v} R A B k) :
    cast (by rw [add_assoc])
        (mul (i + j) k (mul i j (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      mul i (j + k) (x ⊗ₜ[A] mul j k (y ⊗ₜ[A] z))
  /-- In nonnegative degrees, multiplication is the canonical Tor multiplication. -/
  mul_ofNat (n m : ℕ) : mul n m = torMultiplication.{uR, uA, v} R A B n m

/-- A degree-preserving homomorphism of graded Tor algebras. -/
public structure AlgebraHom {B C : AlgCat.{v, uR} R} (X : Algebra.{uR, uA, v} R A B)
    (Y : Algebra.{uR, uA, v} R A C) where
  /-- The map on each homogeneous component. -/
  hom (i : ℤ) : torPiece.{uR, uA, v} R A B i ⟶ torPiece.{uR, uA, v} R A C i
  /-- The unit is preserved. -/
  map_one : hom 0 X.one = Y.one
  /-- Homogeneous multiplication is preserved. -/
  map_mul (i j : ℤ) (x : torPiece.{uR, uA, v} R A B i) (y : torPiece.{uR, uA, v} R A B j) :
    hom (i + j) (X.mul i j (x ⊗ₜ[A] y)) =
      Y.mul i j (hom i x ⊗ₜ[A] hom j y)

end GradedTor

end

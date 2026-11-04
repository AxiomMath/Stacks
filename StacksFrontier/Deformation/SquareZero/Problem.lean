module

public import Mathlib.RingTheory.Ideal.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# A square-zero extension problem for rings

Let `A' → A` be a surjective map of commutative rings with square-zero kernel `I`,
let `A → B` be a ring map, let `N` be a `B`-module, and let `c : I → N` be
`A`-linear.  A solution is a square-zero extension of `B` by `N` as an `A'`-algebra
whose map on kernels is `c`.

## Main definitions

* `Stacks.Deformation.SquareZeroExtensionProblem` packages the fixed lower row and the map `c`.
* `Stacks.Deformation.SquareZeroExtensionProblem.CompatibleExtension` is a choice of the middle
  ring in the upper row, including its identification of the kernel with `N`.
* `Stacks.Deformation.SquareZeroExtensionProblem.CompatibleExtension.Iso` is an isomorphism of
  solutions inducing the identity on both `B` and `N`.
* `Stacks.Deformation.SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses` is the
  quotient of solutions by these isomorphisms.

## Main results

The tagged structure `SquareZeroExtensionProblem.CompatibleExtension` is the precise
meaning of a solution to the displayed extension problem.

## Implementation notes

The two exact rows are represented by surjective ring maps together with explicit
identifications of their kernels.  The module structures on the kernels are bundled and
required to agree with multiplication by a lift.  Thus they are the canonical module
structures induced by the corresponding square-zero extensions.

## References

* [Stacks Project, Tag 08S4](https://stacks.math.columbia.edu/tag/08S4)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ v

namespace Stacks.Deformation
/-- The fixed data in a square-zero extension problem for rings.

The equality `kernel_eq` and surjectivity of `A' → A` encode the exact lower row
`0 → I → A' → A → 0`. -/
public structure SquareZeroExtensionProblem where
  /-- The ring being thickened. -/
  A' : Type u₁
  /-- The quotient of `A'`. -/
  A : Type u₂
  /-- The target `A`-algebra. -/
  B : Type u₃
  /-- The module by which `B` is to be extended. -/
  N : Type u₄
  [commRingA' : CommRing A']
  [commRingA : CommRing A]
  [commRingB : CommRing B]
  [addCommGroupN : AddCommGroup N]
  /-- The surjection `A' → A`. -/
  [algebraA'A : Algebra A' A]
  /-- The map `A → B`. -/
  [algebraAB : Algebra A B]
  /-- The composite `A' → B`. -/
  [algebraA'B : Algebra A' B]
  /-- The `A'`-algebra structure on `B` is the composite through `A`. -/
  [isScalarTowerA'AB : IsScalarTower A' A B]
  /-- The ideal in the lower-left corner. -/
  I : Ideal A'
  /-- The ideal `I` is the kernel of `A' → A`. -/
  kernel_eq : RingHom.ker (algebraMap A' A) = I
  /-- The map `A' → A` is surjective. -/
  surjective : Function.Surjective (algebraMap A' A)
  /-- The kernel of `A' → A` has square zero. -/
  sq_zero : I ^ 2 = ⊥
  /-- The canonical `A`-module structure on `I`. -/
  [moduleI : Module A I]
  /-- Scalar multiplication on `I` agrees with multiplication by any lift in `A'`. -/
  algebraMap_smul_I : ∀ (a' : A') (i : I), (algebraMap A' A a') • i = a' • i
  /-- The given `B`-module structure on `N`. -/
  [moduleBN : Module B N]
  /-- The restriction of the `B`-module structure to `A`. -/
  [moduleAN : Module A N]
  /-- The `A`-action on `N` is induced by `A → B`. -/
  [isScalarTowerABN : IsScalarTower A B N]
  /-- The prescribed map from the old kernel to the new kernel. -/
  c : I →ₗ[A] N

attribute [instance] SquareZeroExtensionProblem.commRingA' SquareZeroExtensionProblem.commRingA
  SquareZeroExtensionProblem.commRingB SquareZeroExtensionProblem.addCommGroupN
  SquareZeroExtensionProblem.algebraA'A SquareZeroExtensionProblem.algebraAB
  SquareZeroExtensionProblem.algebraA'B SquareZeroExtensionProblem.isScalarTowerA'AB
  SquareZeroExtensionProblem.moduleI SquareZeroExtensionProblem.moduleBN
  SquareZeroExtensionProblem.moduleAN SquareZeroExtensionProblem.isScalarTowerABN

namespace SquareZeroExtensionProblem

/-- A solution of a square-zero extension problem.

The map `toB` and its kernel give the exact upper row
`0 → N → B' → B → 0`; `kernelEquiv` supplies the displayed identification
with `N`, and `map_I` says that the left square is the prescribed map `c`. -/
@[stacks 08S4, stacks 08SN "the same extension problem diagram"]
public structure CompatibleExtension (S : SquareZeroExtensionProblem) where
  /-- The ring occupying the question mark in the diagram. -/
  B' : Type v
  [commRingB' : CommRing B']
  /-- The lift is an `A'`-algebra. -/
  [algebraA'B' : Algebra S.A' B']
  /-- The right-hand map in the upper exact row. -/
  toB : B' →ₐ[S.A'] S.B
  /-- The map `B' → B` is surjective. -/
  surjective : Function.Surjective toB
  /-- Its kernel is an ideal of square zero. -/
  sq_zero : RingHom.ker toB.toRingHom ^ 2 = ⊥
  /-- The canonical `B`-module structure on the kernel. -/
  [moduleKernel : Module S.B (RingHom.ker toB.toRingHom)]
  /-- Scalar multiplication on the kernel agrees with multiplication by any lift in `B'`. -/
  toB_smul_kernel : ∀ (b' : B') (x : RingHom.ker toB.toRingHom),
    toB b' • x = b' • x
  /-- The identification of the kernel of `B' → B` with `N`. -/
  kernelEquiv : S.N ≃ₗ[S.B] RingHom.ker toB.toRingHom
  /-- The map `A' → B'` induces the prescribed map `c : I → N` on kernels. -/
  map_I : ∀ i : S.I,
    ((kernelEquiv (S.c i) : RingHom.ker toB.toRingHom) : B') = algebraMap S.A' B' i

attribute [instance] CompatibleExtension.commRingB' CompatibleExtension.algebraA'B'
  CompatibleExtension.moduleKernel

namespace CompatibleExtension

/-- An isomorphism of solutions, commuting with the maps to `B` and with the chosen
identifications of their kernels with `N`. -/
public structure Iso {S : SquareZeroExtensionProblem} (X Y : S.CompatibleExtension) where
  /-- The underlying `A'`-algebra equivalence. -/
  toAlgEquiv : X.B' ≃ₐ[S.A'] Y.B'
  /-- The equivalence induces the identity on the quotient `B`. -/
  toB_comm : Y.toB.comp toAlgEquiv.toAlgHom = X.toB
  /-- The equivalence induces the identity on the identified kernel `N`. -/
  kernelEquiv_comm : ∀ n : S.N,
    toAlgEquiv ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') =
      ((Y.kernelEquiv n : RingHom.ker Y.toB.toRingHom) : Y.B')

/-- The identity isomorphism of a solution. -/
public def Iso.refl {S : SquareZeroExtensionProblem} (X : S.CompatibleExtension) : Iso X X where
  toAlgEquiv := AlgEquiv.refl
  toB_comm := rfl
  kernelEquiv_comm := fun _ ↦ rfl

/-- The inverse of an isomorphism of solutions. -/
public def Iso.symm {S : SquareZeroExtensionProblem} {X Y : S.CompatibleExtension}
    (e : Iso X Y) : Iso Y X where
  toAlgEquiv := e.toAlgEquiv.symm
  toB_comm := by
    ext y
    simpa using (DFunLike.congr_fun e.toB_comm (e.toAlgEquiv.symm y)).symm
  kernelEquiv_comm := fun n ↦ by
    simpa using (congrArg e.toAlgEquiv.symm (e.kernelEquiv_comm n)).symm

/-- The composite of two isomorphisms of solutions. -/
public def Iso.trans {S : SquareZeroExtensionProblem} {X Y Z : S.CompatibleExtension}
    (e : Iso X Y) (f : Iso Y Z) : Iso X Z where
  toAlgEquiv := e.toAlgEquiv.trans f.toAlgEquiv
  toB_comm := by
    ext x
    change Z.toB (f.toAlgEquiv (e.toAlgEquiv x)) = X.toB x
    rw [show Z.toB (f.toAlgEquiv (e.toAlgEquiv x)) = Y.toB (e.toAlgEquiv x) from
      DFunLike.congr_fun f.toB_comm (e.toAlgEquiv x)]
    exact DFunLike.congr_fun e.toB_comm x
  kernelEquiv_comm := fun n ↦ by
    change f.toAlgEquiv (e.toAlgEquiv
      ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B')) =
        ((Z.kernelEquiv n : RingHom.ker Z.toB.toRingHom) : Z.B')
    rw [e.kernelEquiv_comm n, f.kernelEquiv_comm n]

/-- Two solutions are isomorphic when there is an isomorphism fitting into the two exact
rows of the extension diagram. -/
public def Isomorphic {S : SquareZeroExtensionProblem} (X Y : S.CompatibleExtension) :
    Prop := Nonempty (Iso X Y)

/-- Isomorphism of solutions is an equivalence relation. -/
@[ega "0 18.2.2" "special case", ega "0 18.3.1" "special case"]
public def isomorphicSetoid (S : SquareZeroExtensionProblem) :
    Setoid S.CompatibleExtension where
  r := Isomorphic
  iseqv := {
    refl := fun X ↦ ⟨Iso.refl X⟩
    symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩ }

/-- Isomorphism classes of solutions to a square-zero extension problem. -/
public def IsomorphismClasses (S : SquareZeroExtensionProblem) := Quotient (isomorphicSetoid S)

end CompatibleExtension

end SquareZeroExtensionProblem

end Stacks.Deformation
end

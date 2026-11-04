module

public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import StacksFrontier.Deformation.SquareZero.Torsor

/-!
# Square-zero extensions of algebras (Stacks 0GPT)

Let `A → B` be a map of commutative rings and let `N` be a `B`-module.  Isomorphism classes
of square-zero extensions of the `A`-algebra `B` by `N` are classified by
`Ext¹_B(NL_{B/A}, N)`.

The Stacks proof is the specialisation of **Stacks 08S7** to the extension problem whose
lower row is the trivial thickening `0 → 0 → A → A → 0`: that problem has the split
extension `B ⋉ N` as a solution, so its isomorphism classes form a principal homogeneous
space under `Ext¹_B(NL_{B/A}, N)`, and subtracting the class of the split extension turns
that torsor into a bijection with the group itself.

## Main definitions

* `Stacks.Deformation.algebraExtensionProblem` is the extension problem whose lower row is
  the identity extension of `A`.
* `Stacks.Deformation.splitAlgebraExtension` is the split square-zero extension `B ⋉ N`.

## Main results

* `Stacks.Deformation.squareZeroAlgebraExtensionClassesEquivExtOne`: **Stacks 0GPT**, the
  canonical classification of square-zero algebra extensions by the first Ext group of the
  naive cotangent complex.
* `Stacks.Deformation.squareZeroAlgebraExtensionClassesEquivExtOne_sub`: **Stacks 0GPT**, the
  difference of two extension classes is their canonical obstruction class.
* `Stacks.Deformation.squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero`:
  **Stacks 0GPT**, the split extension has class zero.

## Implementation notes

An extension of `B` by `N` includes its `A`-algebra structure, its surjection to `B`, and its
chosen identification of the square-zero kernel with `N`.  Isomorphisms act identically on
both `B` and `N`, as encoded by
`Stacks.Deformation.SquareZeroExtensionProblem.CompatibleExtension`.
The homological degrees `1, 0` of the naive cotangent complex are read as cohomological degrees
`-1, 0` in `Stacks.Deformation.naiveCotangentExtOne`.  The universe of the middle ring of an
extension is fixed to contain the universes of `B` and `N`.
The difference formula specifies the classification compatibly with the canonical torsor
structure on extension classes.  The value on the split extension pins its origin and thus
specifies the canonical classification, rather than merely an affine bijection.

## References

* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
-/

@[expose] public section

universe uA uB uN

open CategoryTheory

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

/-- The square-zero extension problem for extensions of the `A`-algebra `B` by the
`B`-module `N`.  Its lower row is `0 → 0 → A → A → 0`. -/
public def algebraExtensionProblem (A : Type uA) (B : Type uB)
    [CommRing A] [CommRing B] [Algebra A B]
    (N : Type uN) [AddCommGroup N] [Module B N] :
    SquareZeroExtensionProblem.{uA, uA, uB, uN} := by
  letI : Module A N := Module.compHom N (algebraMap A B)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact
    { A' := A
      A := A
      B := B
      N := N
      I := ⊥
      kernel_eq := by ext x; simp
      surjective := by intro x; exact ⟨x, by simp⟩
      sq_zero := by simp
      algebraMap_smul_I := by simp
      c := 0 }

/-- The split square-zero extension of the `A`-algebra `B` by `N`. -/
public noncomputable def splitAlgebraExtension
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type uN) [AddCommGroup N] [Module B N] :
    (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN} := by
  let opToB : Bᵐᵒᵖ →+* B :=
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by intro x y; exact mul_comm _ _
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  letI : Module Bᵐᵒᵖ N := Module.compHom N opToB
  letI : IsCentralScalar B N := ⟨fun _ _ ↦ rfl⟩
  letI : Module A N := Module.compHom N (algebraMap A B)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Algebra A (TrivSqZeroExt B N) := TrivSqZeroExt.algebra' A B N
  let f : TrivSqZeroExt B N →ₐ[A] B := TrivSqZeroExt.fstHom A B N
  letI : Module B (RingHom.ker f.toRingHom) :=
    Module.compHom _ (TrivSqZeroExt.inlHom B N)
  let g : N →ₗ[B] RingHom.ker f.toRingHom :=
    { toFun := fun n ↦ ⟨TrivSqZeroExt.inr n, by simp [f]⟩
      map_add' := fun x y ↦ Subtype.ext (TrivSqZeroExt.inr_add B x y)
      map_smul' := by
        intro b n
        apply Subtype.ext
        change TrivSqZeroExt.inr (b • n) = TrivSqZeroExt.inl b * TrivSqZeroExt.inr n
        apply TrivSqZeroExt.ext <;> simp }
  let e : N ≃ₗ[B] RingHom.ker f.toRingHom :=
    LinearEquiv.ofBijective g
      (by
        constructor
        · exact fun x y h ↦ congrArg (fun z : RingHom.ker f.toRingHom ↦ z.1.snd) h
        · intro x
          refine ⟨x.1.snd, ?_⟩
          apply Subtype.ext
          apply TrivSqZeroExt.ext
          · change (TrivSqZeroExt.inr x.1.snd).fst = x.1.fst
            simpa [f] using x.2.symm
          · rfl)
  dsimp only [algebraExtensionProblem]
  exact
    { B' := TrivSqZeroExt B N
      toB := f
      surjective := fun b ↦ ⟨TrivSqZeroExt.inl b, by simp [f]⟩
      sq_zero := by
        change RingHom.ker (TrivSqZeroExt.fstHom B B N).toRingHom ^ 2 = ⊥
        exact TrivSqZeroExt.kerIdeal_sq B N
      toB_smul_kernel := by
        intro x y
        apply Subtype.ext
        apply TrivSqZeroExt.ext
        · change (TrivSqZeroExt.inl x.fst * y.1).fst = (x * y.1).fst
          simp [TrivSqZeroExt.fst_mul, show y.1.fst = 0 from y.2]
        · change (TrivSqZeroExt.inl x.fst * y.1).snd = (x * y.1).snd
          simp [TrivSqZeroExt.snd_mul, show y.1.fst = 0 from y.2]
      kernelEquiv := e
      map_I := by
        intro i
        have hi : (i : A) = 0 := i.2
        have h : i = 0 := Subtype.ext hi
        rw [h]
        simp only [map_zero, Submodule.coe_zero] }

/-- Isomorphism classes of square-zero extensions of an `A`-algebra `B` by a `B`-module `N`
are canonically equivalent to `Ext¹_B(NL_{B/A}, N)`. -/
@[stacks 0GPT]
public noncomputable def squareZeroAlgebraExtensionClassesEquivExtOne
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type uN) [AddCommGroup N] [Module B N] :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uA, uA, uB, uN,
        max uB uN}
        (algebraExtensionProblem A B N) ≃
      naiveCotangentExtOne A B N := by
  let S := algebraExtensionProblem A B N
  let h : Nonempty (S.CompatibleExtension.{max uB uN}) :=
    ⟨splitAlgebraExtension A B N⟩
  let torsor := isomorphismClassesTorsor S h
  let p := splitAlgebraExtension A B N
  exact
    { toFun := fun x => @VSub.vsub _ _ torsor.toVSub x
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) p)
      invFun := fun g => @VAdd.vadd _ _
        (torsor.toAddAction.toAddSemigroupAction.toVAdd) g
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) p)
      left_inv := by
        intro x
        exact torsor.vsub_vadd' x _
      right_inv := by
        intro g
        exact torsor.vadd_vsub' g _ }

/-- The classification sends an extension class to its difference from the split extension,
computed in the torsor structure. -/
private theorem squareZeroAlgebraExtensionClassesEquivExtOne_mk_eq_vsub
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type uN) [AddCommGroup N] [Module B N]
    (X : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    squareZeroAlgebraExtensionClassesEquivExtOne A B N
        (Quotient.mk
          (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
            (algebraExtensionProblem A B N)) X) =
      @VSub.vsub _ _
        (isomorphismClassesTorsor (algebraExtensionProblem A B N)
          ⟨splitAlgebraExtension A B N⟩).toVSub
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A B N)) X)
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A B N)) (splitAlgebraExtension A B N)) :=
  rfl

/-- The classification sends the difference between two square-zero extensions to the
canonical obstruction class comparing them. -/
@[stacks 0GPT "canonical difference"]
public theorem squareZeroAlgebraExtensionClassesEquivExtOne_sub
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type uN) [AddCommGroup N] [Module B N]
    (X Y : (algebraExtensionProblem A B N).CompatibleExtension.{max uB uN}) :
    squareZeroAlgebraExtensionClassesEquivExtOne A B N
        (Quotient.mk
          (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
            (algebraExtensionProblem A B N)) Y) -
      squareZeroAlgebraExtensionClassesEquivExtOne A B N
      (Quotient.mk
        (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A B N)) X) =
      (obstructionClass (comparisonDiagram X Y)).1 := by
  rw [squareZeroAlgebraExtensionClassesEquivExtOne_mk_eq_vsub,
    squareZeroAlgebraExtensionClassesEquivExtOne_mk_eq_vsub]
  exact (@vsub_sub_vsub_cancel_right _ _ _
    (isomorphismClassesTorsor (algebraExtensionProblem A B N) ⟨splitAlgebraExtension A B N⟩)
    _ _ _).trans (isomorphismClasses_vsub_eq_obstructionClass _ _ X Y)

/-- The canonical classification sends the split square-zero extension to zero. -/
@[stacks 0GPT "split extension"]
public theorem squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (N : Type uN) [AddCommGroup N] [Module B N] :
    squareZeroAlgebraExtensionClassesEquivExtOne A B N
      (Quotient.mk
        (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
          (algebraExtensionProblem A B N)) (splitAlgebraExtension A B N)) = 0 := by
  rw [squareZeroAlgebraExtensionClassesEquivExtOne_mk_eq_vsub]
  exact @vsub_self _ _ _
    (isomorphismClassesTorsor (algebraExtensionProblem A B N) ⟨splitAlgebraExtension A B N⟩) _

end Stacks.Deformation

end

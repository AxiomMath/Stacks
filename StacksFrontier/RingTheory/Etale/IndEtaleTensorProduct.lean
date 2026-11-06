module

public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse

/-!
# Ind-étaleness of a tensor product of ind-étale algebras

Let `k` be a commutative ring, let `k → B → A` and `k → B' → A'` be towers of `k`-algebras with
`A` ind-étale over `B` and `A'` ind-étale over `B'`, and give `A ⊗[k] A'` the structure of a
`B ⊗[k] B'`-algebra by `b ⊗ b' ↦ b ⊗ b'`. Then `A ⊗[k] A'` is ind-étale over `B ⊗[k] B'`.

## Main results

* `StacksDraft.indEtale_tensorProduct_left`: `A ⊗[k] D` is ind-étale over `B ⊗[k] D`.
* `StacksDraft.indEtale_tensorProduct_right`: `D ⊗[k] A` is ind-étale over `D ⊗[k] B`.
* `StacksDraft.indEtale_tensorProduct_map`: `A ⊗[k] A'` is ind-étale over `B ⊗[k] B'`.

## Implementation notes

Changing one tensor factor is a cobase change: `A ⊗[k] D = (B ⊗[k] D) ⊗_B A`, which is
`Algebra.IsPushout.tensorProduct_tensorProduct`, so ind-étaleness transports by
`CommAlgCat.ind_etale_of_isPushout`. Changing the other factor is the same statement conjugated
by `Algebra.TensorProduct.comm`, transported with `StacksDraft.indEtale_of_equiv`. Changing both
is the composite, by `StacksDraft.indEtale_comp`.

Mathlib has no canonical `B ⊗[k] D`-algebra structure on `A ⊗[k] D`, so each statement takes one
as an instance together with its value `b ⊗ d ↦ (algebraMap B A b) ⊗ d` on pure tensors, which
determines it. This is the convention of `Algebra.IsPushout.tensorProduct_tensorProduct`, and it
lets a caller that already carries such a structure apply these lemmas without rewriting along an
isomorphism.

## References

* [StacksProject 0BSH](https://stacks.math.columbia.edu/tag/0BSH), cobase change
* [StacksProject 0BSI](https://stacks.math.columbia.edu/tag/0BSI), composition
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace StacksDraft

/-- Swapping the two factors of a tensor product of algebras twice is the identity. -/
private theorem comm_comm_apply (k X Y : Type u) [CommRing k] [CommRing X] [CommRing Y]
    [Algebra k X] [Algebra k Y] (z : X ⊗[k] Y) :
    Algebra.TensorProduct.comm k Y X (Algebra.TensorProduct.comm k X Y z) = z := by
  induction z with
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

section Left

variable (k B A D : Type u) [CommRing k] [CommRing B] [CommRing A] [CommRing D]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra k D]
  [Algebra (B ⊗[k] D) (A ⊗[k] D)]

/-- Base changing the left factor of `B ⊗[k] D` along `B → A` makes `A ⊗[k] D` an algebra over
`B ⊗[k] D` compatibly with the two structure maps out of `B`. -/
theorem isScalarTower_tensorProduct_left
    (hmap : ∀ (b : B) (d : D),
      algebraMap (B ⊗[k] D) (A ⊗[k] D) (b ⊗ₜ d) = algebraMap B A b ⊗ₜ d) :
    IsScalarTower B (B ⊗[k] D) (A ⊗[k] D) := by
  refine IsScalarTower.of_algebraMap_eq fun b => ?_
  rw [show algebraMap B (B ⊗[k] D) b = b ⊗ₜ (1 : D) from rfl, hmap]
  rfl

/-- **`A ⊗[k] D` is the cobase change of `B → A` along `B → B ⊗[k] D`.** -/
theorem isPushout_tensorProduct_left [IsScalarTower B (B ⊗[k] D) (A ⊗[k] D)]
    (hmap : ∀ (b : B) (d : D),
      algebraMap (B ⊗[k] D) (A ⊗[k] D) (b ⊗ₜ d) = algebraMap B A b ⊗ₜ d) :
    Algebra.IsPushout B A (B ⊗[k] D) (A ⊗[k] D) := by
  refine Algebra.IsPushout.tensorProduct_tensorProduct k D B A ?_
  ext d
  show algebraMap (B ⊗[k] D) (A ⊗[k] D) ((1 : B) ⊗ₜ d) = (1 : A) ⊗ₜ d
  rw [hmap, map_one]

/-- **Ind-étaleness of a tensor product in the left factor.** If `A` is a filtered colimit of
étale `B`-algebras and `D` is a `k`-algebra, then `A ⊗[k] D` is a filtered colimit of étale
`B ⊗[k] D`-algebras. -/
theorem indEtale_tensorProduct_left
    (hmap : ∀ (b : B) (d : D),
      algebraMap (B ⊗[k] D) (A ⊗[k] D) (b ⊗ₜ d) = algebraMap B A b ⊗ₜ d)
    (h : IndEtale B A) :
    IndEtale (B ⊗[k] D) (A ⊗[k] D) := by
  have := isScalarTower_tensorProduct_left k B A D hmap
  have := (isPushout_tensorProduct_left k B A D hmap).symm
  exact indEtale_iff.mpr
    (CommAlgCat.ind_etale_of_isPushout B (B ⊗[k] D) A (A ⊗[k] D) (indEtale_iff.mp h))

end Left

section Right

variable (k B A D : Type u) [CommRing k] [CommRing B] [CommRing A] [CommRing D]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra k D]
  [Algebra (D ⊗[k] B) (D ⊗[k] A)]

/-- **Ind-étaleness of a tensor product in the right factor.** If `A` is a filtered colimit of
étale `B`-algebras and `D` is a `k`-algebra, then `D ⊗[k] A` is a filtered colimit of étale
`D ⊗[k] B`-algebras. -/
theorem indEtale_tensorProduct_right
    (hmap : ∀ (d : D) (b : B),
      algebraMap (D ⊗[k] B) (D ⊗[k] A) (d ⊗ₜ b) = d ⊗ₜ algebraMap B A b)
    (h : IndEtale B A) :
    IndEtale (D ⊗[k] B) (D ⊗[k] A) := by
  let : Algebra (B ⊗[k] D) (A ⊗[k] D) :=
    (((Algebra.TensorProduct.comm k D A).toRingEquiv.toRingHom.comp
      (algebraMap (D ⊗[k] B) (D ⊗[k] A))).comp
      (Algebra.TensorProduct.comm k B D).toRingEquiv.toRingHom).toAlgebra
  have hL : ∀ (b : B) (d : D),
      algebraMap (B ⊗[k] D) (A ⊗[k] D) (b ⊗ₜ d) = algebraMap B A b ⊗ₜ d := by
    intro b d
    show Algebra.TensorProduct.comm k D A
      (algebraMap (D ⊗[k] B) (D ⊗[k] A) (Algebra.TensorProduct.comm k B D (b ⊗ₜ d))) = _
    rw [show Algebra.TensorProduct.comm k B D (b ⊗ₜ d) = d ⊗ₜ b from rfl, hmap]
    rfl
  refine indEtale_of_equiv (Algebra.TensorProduct.comm k B D).toRingEquiv
    (Algebra.TensorProduct.comm k A D).toRingEquiv (fun x => ?_)
    (indEtale_tensorProduct_left k B A D hL h)
  show Algebra.TensorProduct.comm k A D
    (Algebra.TensorProduct.comm k D A
      (algebraMap (D ⊗[k] B) (D ⊗[k] A) (Algebra.TensorProduct.comm k B D x))) = _
  exact comm_comm_apply k D A _

end Right

section Map

variable (k B A B' A' : Type u) [CommRing k] [CommRing B] [CommRing A] [CommRing B']
  [CommRing A'] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
  [Algebra k B'] [Algebra k A'] [Algebra B' A'] [IsScalarTower k B' A']
  [Algebra (B ⊗[k] B') (A ⊗[k] A')]

/-- **Ind-étaleness of a tensor product in both factors.** Let `k → B → A` and `k → B' → A'` be
towers of `k`-algebras with `A` a filtered colimit of étale `B`-algebras and `A'` a filtered
colimit of étale `B'`-algebras. Then `A ⊗[k] A'` is a filtered colimit of étale
`B ⊗[k] B'`-algebras. -/
theorem indEtale_tensorProduct_map
    (hmap : ∀ (b : B) (b' : B'), algebraMap (B ⊗[k] B') (A ⊗[k] A') (b ⊗ₜ b') =
      algebraMap B A b ⊗ₜ algebraMap B' A' b')
    (h : IndEtale B A) (h' : IndEtale B' A') :
    IndEtale (B ⊗[k] B') (A ⊗[k] A') := by
  let : Algebra (B ⊗[k] B') (A ⊗[k] B') :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k B A) (AlgHom.id k B')).toAlgebra
  let : Algebra (A ⊗[k] B') (A ⊗[k] A') :=
    (Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k B' A')).toAlgebra
  have h1 : IndEtale (B ⊗[k] B') (A ⊗[k] B') :=
    indEtale_tensorProduct_left k B A B' (fun _ _ => rfl) h
  have h2 : IndEtale (A ⊗[k] B') (A ⊗[k] A') :=
    indEtale_tensorProduct_right k B' A' A (fun _ _ => rfl) h'
  have : IsScalarTower (B ⊗[k] B') (A ⊗[k] B') (A ⊗[k] A') := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    induction x with
    | tmul b b' => rw [hmap]; rfl
    | add x y hx hy => simp only [map_add]; rw [hx, hy]
  exact indEtale_comp h1 h2

end Map

end StacksDraft

end

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension of scalars along a finite separable algebra

Let `k''/k'/k` be finite separable algebras and let `X` be a smooth projective scheme over `k'`.
Writing `F' = H^0(Spec k')` and `F'' = H^0(Spec k'')`, the cohomology of the base change of `X`
to `k''` is obtained from that of `X` by extending scalars from `F'` to `F''`:

`H^*(X) ⊗_{F'} F'' = H^*(X ×_{Spec k'} Spec k'')`.

The argument is a comparison of two instances of the Künneth formula over `k`. Choose a finite
separable `k'`-algebra `l` with `k' ⊗_k k'' = k'' × l` and write `G = H^0(Spec l)`. Since
`Spec k' ×_{Spec k} Spec k''` is the disjoint union of `Spec k''` and `Spec l`, Künneth and
additivity on a disjoint union give a decomposition `F' ⊗_F F'' = F'' × G` whose first projection
is the multiplication map `F' ⊗_F F'' → F''`. The same two inputs applied to
`X ×_{Spec k} Spec k''`, which is the disjoint union of `X ×_{Spec k'} Spec k''` and
`X ×_{Spec k'} Spec l`, give

`H^*(X) ⊗_F F'' = H^*(X ×_{Spec k'} Spec k'') × H^*(X ×_{Spec k'} Spec l)`

compatibly with the first decomposition. The idempotent `e` of `F' ⊗_F F''` corresponding to
`(0, 1)` therefore acts as the identity on everything killed by the first projection, while it
dies in `F''`; so the kernel of `H^*(X) ⊗_F F'' → H^*(X ×_{Spec k'} Spec k'')` is exactly the
kernel of the surjection `H^*(X) ⊗_F F'' → H^*(X) ⊗_{F'} F''`.

## Main definitions

* `Stacks.WeilCohomology.tensorMulHom`: the multiplication map `F' ⊗_F F'' → F''`, which is the
  projection onto the first factor of `F' ⊗_F F'' = F'' × G`.
* `Stacks.WeilCohomology.tensorActionHom`: the action of `F' ⊗_F F''` on `H^*(X) ⊗_F F''`, as a
  map of algebras.
* `Stacks.WeilCohomology.scalarExtensionHom`: the canonical comparison map
  `H^*(X) ⊗_{F'} F'' → H^*(X ×_{Spec k'} Spec k'')`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`.
* `Stacks.WeilCohomology.scalarExtensionEquiv`: that map, packaged as an isomorphism.

## Main results

* `Stacks.WeilCohomology.scalarExtensionHom_tmul`: the comparison map on pure tensors.
* `Stacks.WeilCohomology.bijective_scalarExtensionHom_of_idempotent`: bijectivity of the
  comparison map, from an idempotent of `F' ⊗_F F''` dying in `F''` and cutting out the second
  summand of the cohomology of the base change to `k`.
* `Stacks.WeilCohomology.bijective_scalarExtensionHom`: bijectivity of the comparison map, from
  the two compatible product decompositions.

## Implementation notes

As elsewhere in this directory the cohomological data is supplied as explicit arguments rather
than through a bundled Weil cohomology theory; the bundled
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` assumes the base field algebraically
closed, over which every finite separable algebra is a product of copies of the field, so it
cannot express the statement. The dictionary is as follows.

* `F` is the coefficient field `H^0(Spec k)`, `A` is `F' = H^0(Spec k')`, `B` is
  `F'' = H^0(Spec k'')` and `G` is `H^0(Spec l)`. That the cohomology of a zero-dimensional
  smooth projective scheme is a finite separable `F`-algebra concentrated in degree zero is
  Stacks 0FHQ, which the source uses without further mention; it is used here by taking the
  cohomology of those three spectra to be the single algebras `A`, `B`, `G`.
* `M` is the total cohomology `H^*(X)`, a ring; its `A`-algebra structure is pullback along
  `X → Spec k'`, which lands in degree zero and is therefore central by graded commutativity.
* `N₁` is `H^*(X ×_{Spec k'} Spec k'')` and `N₂` is `H^*(X ×_{Spec k'} Spec l)`. The map `fM` is
  pullback along the projection `X ×_{Spec k'} Spec k'' → X` and `algebraMap B N₁` is pullback
  along the projection to `Spec k''`, both part of `(D1)`.
* `kunneth` is the Künneth isomorphism of axiom `(B)(a)` for `X ×_{Spec k} Spec k''` composed
  with the decomposition of Stacks 0FHJ along
  `X ×_{Spec k} Spec k'' = (X ×_{Spec k'} Spec k'') ⨿ (X ×_{Spec k'} Spec l)`, and
  `kunneth_tmul` says that it is the Künneth map `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` in the first
  coordinate.
* `split` is the same for `X = Spec k'`, that is the decomposition `F' ⊗_F F'' = F'' × G`, and
  `split_fst` identifies its first projection with the multiplication map, the source's
  statement that the map from left to right identifies `F''` with `F' ⊗_{F'} F''`.
* `kunneth_split` is the compatibility of the two decompositions, the source's "as modules over
  `F' ⊗_F F'' = F'' × G`".

The product decomposition `k' ⊗_k k'' = k'' × l` itself enters only through `split`, so no
separability hypothesis is needed: the statement proved is that the two compatible product
decompositions force the comparison map to be bijective.

Only the ring structure of the cohomology is used, not its grading, so the statement is about
total cohomology and the conclusion is an isomorphism of `F'`-algebras; `B`-linearity is part of
it, since `algebraMap B N₁` is the image of the second tensor factor.

## References

* [Stacks Project, Tag 0FHX](https://stacks.math.columbia.edu/tag/0FHX)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.WeilCohomology

/-- The multiplication map `F' ⊗_F F'' → F''`, `α ⊗ β ↦ αβ`, of a tower `F ⊆ F' ⊆ F''` of
commutative algebras. It is the projection onto the first factor in the decomposition
`F' ⊗_F F'' = F'' × G` of Stacks 0FHX, the one identifying `F''` with `F' ⊗_{F'} F''`. -/
noncomputable def tensorMulHom (F : Type*) [CommRing F] (A : Type*) [CommRing A]
    (B : Type*) [CommRing B] [Algebra F A] [Algebra F B] [Algebra A B]
    [IsScalarTower F A B] : A ⊗[F] B →ₐ[F] B :=
  Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom F A B) (AlgHom.id F B)

/-- The multiplication map `F' ⊗_F F'' → F''` sends `a ⊗ b` to `ab`. -/
@[simp]
theorem tensorMulHom_tmul {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B] (a : A) (b : B) :
    tensorMulHom F A B (a ⊗ₜ[F] b) = algebraMap A B a * b :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ a b

/-- The action of `F' ⊗_F F''` on `H^*(X) ⊗_F F''`, as the algebra map
`F' ⊗_F F'' → H^*(X) ⊗_F F''` induced by the structure map `F' → H^*(X)`. -/
noncomputable def tensorActionHom (F : Type*) [CommRing F] (A : Type*) [CommRing A]
    (B : Type*) [CommRing B] (M : Type*) [Ring M] [Algebra F A] [Algebra F B]
    [Algebra F M] [Algebra A M] [IsScalarTower F A M] : A ⊗[F] B →ₐ[F] M ⊗[F] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom F A M) (AlgHom.id F B)

/-- The action map `F' ⊗_F F'' → H^*(X) ⊗_F F''` sends `a ⊗ b` to the image of `a` in `H^*(X)`
tensored with `b`. -/
@[simp]
theorem tensorActionHom_tmul {F A B M : Type*} [CommRing F] [CommRing A] [CommRing B] [Ring M]
    [Algebra F A] [Algebra F B] [Algebra F M] [Algebra A M] [IsScalarTower F A M]
    (a : A) (b : B) :
    tensorActionHom F A B M (a ⊗ₜ[F] b) = algebraMap A M a ⊗ₜ[F] b :=
  Algebra.TensorProduct.map_tmul _ _ a b

variable {F A B G M N₁ N₂ : Type*}
  [CommRing F] [CommRing A] [CommRing B] [CommRing G]
  [Ring M] [Ring N₁] [Ring N₂]
  [Algebra F A] [Algebra F B] [Algebra F G] [Algebra A B] [IsScalarTower F A B]
  [Algebra F M] [Algebra A M] [IsScalarTower F A M]
  [Algebra F N₁] [Algebra F N₂] [Algebra A N₁] [Algebra B N₁] [IsScalarTower A B N₁]
  [Algebra G N₂]

/-- The canonical comparison map `H^*(X) ⊗_{F'} F'' → H^*(X ×_{Spec k'} Spec k'')` of Stacks
0FHX: on a pure tensor it is `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, where `fM` is pullback along the
projection to `X` and `algebraMap B N₁` is pullback along the projection to `Spec k''`. -/
noncomputable def scalarExtensionHom (fM : M →ₐ[A] N₁) : M ⊗[A] B →ₐ[A] N₁ :=
  Algebra.TensorProduct.lift fM (IsScalarTower.toAlgHom A B N₁)
    fun m b => (Algebra.commutes b (fM m)).symm

/-- The comparison map `H^*(X) ⊗_{F'} F'' → H^*(X ×_{Spec k'} Spec k'')` sends `m ⊗ b` to
`fM m * algebraMap B N₁ b`, that is `pr₁^*m ∪ pr₂^*b`. -/
@[simp]
theorem scalarExtensionHom_tmul (fM : M →ₐ[A] N₁) (m : M) (b : B) :
    scalarExtensionHom fM (m ⊗ₜ[A] b) = fM m * algebraMap B N₁ b :=
  Algebra.TensorProduct.lift_tmul _ _ _ m b

/-- The action of `F' ⊗_F F''` on `H^*(X) ⊗_F F''` becomes, after extending scalars to `F'`,
multiplication by the image of `F' ⊗_F F'' → F''`, that is `(α · a) ⊗ (βb) = a ⊗ ((αβ) b)`. -/
theorem mapOfCompatibleSMul_tensorActionHom (z : A ⊗[F] B) :
    Algebra.TensorProduct.mapOfCompatibleSMul A F F M B (tensorActionHom F A B M z) =
      Algebra.TensorProduct.includeRight (tensorMulHom F A B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a b =>
    simp only [tensorActionHom_tmul, tensorMulHom_tmul,
      Algebra.TensorProduct.mapOfCompatibleSMul_tmul, Algebra.TensorProduct.includeRight_apply]
    calc algebraMap A M a ⊗ₜ[A] b = (a • (1 : M)) ⊗ₜ[A] b := by rw [Algebra.smul_def, mul_one]
      _ = (1 : M) ⊗ₜ[A] (a • b) := TensorProduct.smul_tmul _ _ _
      _ = _ := by rw [Algebra.smul_def]

/-- The comparison map of Stacks 0FHX composed with the surjection
`H^*(X) ⊗_F F'' → H^*(X) ⊗_{F'} F''` is the Künneth map followed by restriction to the summand
`X ×_{Spec k'} Spec k''`. -/
theorem scalarExtensionHom_mapOfCompatibleSMul (fM : M →ₐ[A] N₁)
    (kunneth : M ⊗[F] B ≃ₐ[F] N₁ × N₂)
    (kunneth_tmul : ∀ (m : M) (b : B),
      (kunneth (m ⊗ₜ[F] b)).1 = fM m * algebraMap B N₁ b)
    (x : M ⊗[F] B) :
    scalarExtensionHom (B := B) fM
        (Algebra.TensorProduct.mapOfCompatibleSMul A F F M B x) = (kunneth x).1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add]
  | tmul m b =>
    rw [Algebra.TensorProduct.mapOfCompatibleSMul_tmul, scalarExtensionHom_tmul, kunneth_tmul]

/-- **Stacks Project, Tag 0FHX.** Bijectivity of the comparison map
`H^*(X) ⊗_{F'} F'' → H^*(X ×_{Spec k'} Spec k'')`, granted an element `e` of `F' ⊗_F F''` which
dies under the multiplication map to `F''` and whose image in `H^*(X) ⊗_F F''` is the idempotent
`(0, 1)` cutting out the summand `H^*(X ×_{Spec k'} Spec l)`.

Surjectivity is immediate. For injectivity, a class `z` of `H^*(X) ⊗_F F''` restricting to zero
on `X ×_{Spec k'} Spec k''` satisfies `e · z = z`, and `e · z` dies in `H^*(X) ⊗_{F'} F''`
because `e` does in `F''`. -/
theorem bijective_scalarExtensionHom_of_idempotent (fM : M →ₐ[A] N₁)
    (kunneth : M ⊗[F] B ≃ₐ[F] N₁ × N₂)
    (kunneth_tmul : ∀ (m : M) (b : B),
      (kunneth (m ⊗ₜ[F] b)).1 = fM m * algebraMap B N₁ b)
    (e : A ⊗[F] B) (he_mul : tensorMulHom F A B e = 0)
    (he_idem : kunneth (tensorActionHom F A B M e) = (0, 1)) :
    Function.Bijective (scalarExtensionHom (B := B) fM) := by
  have hfac := scalarExtensionHom_mapOfCompatibleSMul fM kunneth kunneth_tmul
  constructor
  · intro x y hxy
    obtain ⟨z, hz⟩ := Algebra.TensorProduct.mapOfCompatibleSMul_surjective A F F M B (x - y)
    have hz0 : (kunneth z).1 = 0 := by rw [← hfac, hz, map_sub, hxy, sub_self]
    have hez : tensorActionHom F A B M e * z = z := by
      apply kunneth.injective
      rw [map_mul, he_idem]
      exact Prod.ext (by simp [hz0]) (by simp)
    refine sub_eq_zero.mp ?_
    rw [← hz, ← hez, map_mul, mapOfCompatibleSMul_tensorActionHom, he_mul, map_zero, zero_mul]
  · intro n
    obtain ⟨x, hx⟩ := kunneth.surjective (n, 0)
    exact ⟨Algebra.TensorProduct.mapOfCompatibleSMul A F F M B x, by rw [hfac, hx]⟩

/-- **Stacks Project, Tag 0FHX.** Let `k''/k'/k` be finite separable algebras and let `X` be a
smooth projective scheme over `k'`. Then the canonical map

`H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') ⟶ H^*(X ×_{Spec k'} Spec k'')`

is bijective.

Write `k' ⊗_k k'' = k'' × l` and `G = H^0(Spec l)`. Künneth together with additivity on a
disjoint union, Stacks 0FHJ, decomposes `H^0(Spec k') ⊗_F H^0(Spec k'')` as `H^0(Spec k'') × G`
with first projection the multiplication map, and decomposes `H^*(X) ⊗_F H^0(Spec k'')` as
`H^*(X ×_{Spec k'} Spec k'') × H^*(X ×_{Spec k'} Spec l)` compatibly. The idempotent of the
first decomposition corresponding to `(0, 1)` then identifies the two kernels. -/
@[stacks 0FHX "the comparison map is bijective"]
theorem bijective_scalarExtensionHom (fM : M →ₐ[A] N₁)
    (kunneth : M ⊗[F] B ≃ₐ[F] N₁ × N₂)
    (kunneth_tmul : ∀ (m : M) (b : B),
      (kunneth (m ⊗ₜ[F] b)).1 = fM m * algebraMap B N₁ b)
    (split : A ⊗[F] B ≃ₐ[F] B × G)
    (split_fst : ∀ z : A ⊗[F] B, (split z).1 = tensorMulHom F A B z)
    (kunneth_split : ∀ z : A ⊗[F] B,
      kunneth (tensorActionHom F A B M z) =
        (algebraMap B N₁ (split z).1, algebraMap G N₂ (split z).2)) :
    Function.Bijective (scalarExtensionHom (B := B) fM) := by
  refine bijective_scalarExtensionHom_of_idempotent fM kunneth kunneth_tmul
    (split.symm (0, 1)) ?_ ?_
  · rw [← split_fst, split.apply_symm_apply]
  · rw [kunneth_split, split.apply_symm_apply, map_zero, map_one]

/-- **Stacks Project, Tag 0FHX.** The scalar extension isomorphism

`H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') ≃ H^*(X ×_{Spec k'} Spec k'')`

for `k''/k'/k` finite separable algebras and `X` smooth projective over `k'`, given by
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`. -/
@[stacks 0FHX "the scalar extension isomorphism"]
noncomputable def scalarExtensionEquiv (fM : M →ₐ[A] N₁)
    (kunneth : M ⊗[F] B ≃ₐ[F] N₁ × N₂)
    (kunneth_tmul : ∀ (m : M) (b : B),
      (kunneth (m ⊗ₜ[F] b)).1 = fM m * algebraMap B N₁ b)
    (split : A ⊗[F] B ≃ₐ[F] B × G)
    (split_fst : ∀ z : A ⊗[F] B, (split z).1 = tensorMulHom F A B z)
    (kunneth_split : ∀ z : A ⊗[F] B,
      kunneth (tensorActionHom F A B M z) =
        (algebraMap B N₁ (split z).1, algebraMap G N₂ (split z).2)) :
    M ⊗[A] B ≃ₐ[A] N₁ :=
  AlgEquiv.ofBijective (scalarExtensionHom fM)
    (bijective_scalarExtensionHom (G := G) (N₂ := N₂) fM kunneth kunneth_tmul split split_fst
      kunneth_split)

/-- The scalar extension isomorphism sends `m ⊗ b` to `fM m * algebraMap B N₁ b`, that is
`pr₁^*m ∪ pr₂^*b`. -/
@[simp]
theorem scalarExtensionEquiv_tmul (fM : M →ₐ[A] N₁)
    (kunneth : M ⊗[F] B ≃ₐ[F] N₁ × N₂)
    (kunneth_tmul : ∀ (m : M) (b : B),
      (kunneth (m ⊗ₜ[F] b)).1 = fM m * algebraMap B N₁ b)
    (split : A ⊗[F] B ≃ₐ[F] B × G)
    (split_fst : ∀ z : A ⊗[F] B, (split z).1 = tensorMulHom F A B z)
    (kunneth_split : ∀ z : A ⊗[F] B,
      kunneth (tensorActionHom F A B M z) =
        (algebraMap B N₁ (split z).1, algebraMap G N₂ (split z).2))
    (m : M) (b : B) :
    scalarExtensionEquiv fM kunneth kunneth_tmul split split_fst kunneth_split
        (m ⊗ₜ[A] b) = fM m * algebraMap B N₁ b :=
  scalarExtensionHom_tmul fM m b

end Stacks.WeilCohomology

end

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixFreeSheaf
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Monoidal
public import StacksFrontier.LinearAlgebra.Matrix.AlternatingTensorPower

/-!
# The iterated Kronecker law: the matrix of a tensor power of an endomorphism of a free sheaf

Let `S` be a scheme and let `F = 𝒪_S^d` be the free sheaf of `𝒪_S`-modules of rank `d`, in the
spelling of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixFreeSheaf`.
That file sets up the dictionary `freeEndMatrixEquiv` between endomorphisms of a free sheaf of
modules of finite rank and square matrices over the commutative ring `R₀ S = End 𝒪_S`, and proves
the **two-factor Kronecker law** `freeEndMatrixEquiv_tensorHom`: under the standard-basis
identification `𝒪_S^I ⊗ 𝒪_S^K ≅ 𝒪_S^{I × K}` the matrix of `f ⊗ₘ g` is the Kronecker product.

This file iterates that law `j` times for a single endomorphism `f` of `F`. The `j`-fold tensor
power `F^{⊗ j}` is identified with the free sheaf on `Fin j → Fin d` (`natTensorPowFreeIso`), the
`j`-fold tensor power of `f` is `natTensorPowMap`, and the conclusion is that its matrix is the
`j`-fold Kronecker power
$$
  u^{\otimes j}_{f', g'} = \prod_{k} u_{f'(k), g'(k)}, \qquad u = \text{matrix of } f .
$$

The identification is made at the index type `Fin j → Fin d` rather than at `Fin (d ^ j)` on
purpose: at `j = d` that is exactly the index type on which `Matrix.altProj` and
`Matrix.tensorPow` of `StacksFrontier.LinearAlgebra.Matrix.AlternatingTensorPower` live, so the
`d`-fold power of a conjugation acts on the alternating projector of [Stacks, Tag 0A2L] with no
further reindexing. `conj_natTensorPowMap_altProj` is that action: the projector is fixed.

## Main definitions

* `Matrix.tensorPowIdx`: the Kronecker power of a square matrix at an arbitrary finite index type
  `ι`, the matrix on `ι → n` with entry `∏ k, u (f k) (g k)`. For `ι = n` it is
  `Matrix.tensorPow` on the nose (`Matrix.tensorPowIdx_eq_tensorPow`).
* `CategoryTheory.MonoidalCategory.unitBiproductReindexIso`: the standard-basis reindexing
  `⨁_I 𝟙 ≅ ⨁_J 𝟙` along an equivalence `I ≃ J`, and
  `Stacks.EtaleCohomology.BrauerScheme.freeReindexIso` the same for free sheaves of modules.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowMap`: the `j`-fold tensor power
  `f^{⊗ j} : M^{⊗ j} ⟶ M^{⊗ j}` of an endomorphism of a sheaf of modules.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowFreeIso`: **the `j`-fold tensor power of
  `𝒪_S^d` is the free sheaf of modules on `Fin j → Fin d`.**
* `Stacks.EtaleCohomology.BrauerScheme.finSnocEquiv`: `Fin.succFunEquiv` read as the reindexing
  `(Fin j → Fin d) × Fin d ≃ (Fin (j+1) → Fin d)`, the index-type half of the recursion step of
  `natTensorPowFreeIso`.

## Main results

* `Matrix.tensorPowIdx_one` and `Matrix.tensorPowIdx_mul`: the Kronecker power at an arbitrary
  index type is multiplicative, exactly as `Matrix.tensorPow_one` and `Matrix.tensorPow_mul`.
* `CategoryTheory.MonoidalCategory.unitMatrixEquiv_reindex` and
  `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_reindex`: **the matrix of a conjugate
  by a reindexing isomorphism is the reindexed matrix**, `Matrix.reindex e e`.
* `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_tensorIso_reindex`: one Kronecker step,
  the two-factor law composed with a reindexing, stated at an arbitrary first factor. This is the
  form in which the induction below uses it; see the implementation notes.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowMap_id` and `natTensorPowMap_comp`: taking the
  `j`-fold tensor power of an endomorphism is functorial.
* **`Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_natTensorPowMap`: the iterated
  Kronecker law.** The matrix of `f^{⊗ j}`, read through `natTensorPowFreeIso`, is the `j`-fold
  Kronecker power `Matrix.tensorPowIdx (Fin j)` of the matrix of `f`; entrywise
  `freeEndMatrixEquiv_natTensorPowMap_apply`.
* `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_natTensorPowMap_self`: the same at
  `j = d`, where the Kronecker power is `Matrix.tensorPow`.
* `Stacks.EtaleCohomology.BrauerScheme.conj_natTensorPowMap_altProj`: **the `d`-fold Kronecker
  power of a conjugation fixes the alternating projector `Matrix.altProj`.** This is
  `Matrix.tensorPow_mul_altProj_mul_tensorPow` read through the dictionary, the agreement of two
  trivialisations in the proof of [Stacks, Tag 0A2L].

## Implementation notes

**Which identification `F^{⊗ j} ≅ 𝒪_S^{Fin j → Fin d}`.** `Stacks.TensorPowers.natTensorPow`
adds its factors on the right, `natTensorPow M (j+1) = natTensorPow M j ⊗ M`, so the recursion
step is the two-factor identification `freeTensorFreeBiproductIso` followed by a reindexing of
`(Fin j → Fin d) × Fin d` to `Fin (j+1) → Fin d`. The reindexing has to put the *new* factor
last, and that is what makes the Kronecker power come out as `∏ k, u (f' k) (g' k)` with `k`
ranging over all of `Fin (j+1)`: the inductive step is `Fin.prod_univ_castSucc`, splitting off the
last factor exactly as `finSnocEquiv` does. Choosing `Fin.cons` instead would give the same
matrix, since `Fin.prod_univ_succ` splits the product the other way, but the recursion of
`natTensorPow` would then have to be crossed with the braiding. The degree-zero case is the free
sheaf on `Fin 0 → Fin d`, a one-element type, which is the unit
(`Stacks.SheafOfModules.Invertible.freeUniqueIso`).

**Why the induction instantiates a lemma instead of rewriting.**
`Stacks.TensorPowers.natTensorPow M (j+1)` is `natTensorPow M j ⊗ M` *definitionally*, by the
equation compiler, and not syntactically. A `simp` or `rw` lemma whose left-hand side is keyed on
a tensor product — `tensorHom_comp_tensorHom`, `id_tensorHom_id`, even `Category.assoc` once one
of the composable objects is the power — therefore does not fire inside a goal carrying the
`natTensorPow M (j+1)` spelling, because keyed matching unfolds only reducible definitions. Every
step that needs the tensor shape is accordingly phrased as a separate statement, elaborated fresh
at `natTensorPow M j ⊗ M` so that those lemmas do apply, and then transported to the goal by
`exact`, which checks definitional equality at full transparency. That is what
`freeEndMatrixEquiv_tensorIso_reindex` is for — it keeps the first tensor factor as a variable `X`
— and it is also why `natTensorPowMap_id` and `natTensorPowMap_comp` prove an auxiliary `have`
rather than rewriting the goal directly. No rewriting up to defeq, no `eqToHom` and no raised
heartbeat limit is
needed anywhere as a result.

**Which reindexing isomorphism of free sheaves.** `freeReindexIso` is built from
`freeBiproductIso` and the biproduct reindexing `unitBiproductReindexIso`, not from
`SheafOfModules.freeFunctor` applied to the equivalence. Both are the standard-basis map
`e_i ↦ e_{e i}`, but only the first one is expressed in the vocabulary — `biproduct.ι`,
`biproduct.π` — in which `freeEndMatrixEquiv` is defined, so the matrix identity
`freeEndMatrixEquiv_reindex` is a two-line computation with `biproduct.ι_π`. Identifying it with
`(SheafOfModules.freeFunctor _).mapIso e.toIso` is the same kind of crossing between the
coproduct and the biproduct spelling that `MatrixFreeSheaf`'s implementation notes record for
`Stacks.SheafOfModules.freeTensorFreeIso`, and it is not done here either; nothing below needs
it. For the same reason `freeTensorFreeBiproductIso`, not
`Stacks.SheafOfModules.freeTensorFreeIso`, is the two-factor identification used throughout.

**`HasFiniteBiproducts (ModuleSheaf S)` and `MonoidalPreadditive (ModuleSheaf S)`** are the two
instances `MatrixFreeSheaf` declares `local`, which makes them ordinary declarations carrying no
instance attribute outside that file. They are re-enabled here with `attribute [local instance]`
rather than restated, so there is exactly one of each in the library.

**The commutativity of the coefficient ring** is `CategoryTheory.MonoidalCategory.commRingUnitEnd`,
a scoped instance, activated here by `open MonoidalCategory`. It is what `Matrix.tensorPow` and
`Matrix.altProj` need, both being stated over a commutative ring.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe v u

noncomputable section

namespace Matrix

variable (ι : Type*) [Fintype ι] {n : Type*} [Fintype n] {R : Type*} [CommRing R]

/-- **The Kronecker power of a square matrix at an arbitrary finite index type `ι`**: the matrix
on `ι → n` whose `(f, g)` entry is `∏ k, u (f k) (g k)`. It is the matrix by which `u` acts on the
`#ι`-fold tensor power of `R ^ n`, written on the index type of that tensor power. For `ι = n` it
is `Matrix.tensorPow`. -/
def tensorPowIdx (u : Matrix n n R) : Matrix (ι → n) (ι → n) R :=
  Matrix.of fun f g ↦ ∏ k, u (f k) (g k)

omit [Fintype n] in
/-- The `(f, g)` entry of `tensorPowIdx ι u` is `∏ k, u (f k) (g k)`. -/
@[simp]
theorem tensorPowIdx_apply (u : Matrix n n R) (f g : ι → n) :
    tensorPowIdx ι u f g = ∏ k, u (f k) (g k) :=
  rfl

variable [DecidableEq n]

omit [Fintype n] in
/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem tensorPowIdx_one : tensorPowIdx ι (1 : Matrix n n R) = 1 := by
  ext f g
  simp only [tensorPowIdx_apply, Matrix.one_apply]
  by_cases h : f = g
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ : ∃ k, f k ≠ g k := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

omit [DecidableEq n] in
/-- The Kronecker power is multiplicative:
`tensorPowIdx ι (u * v) = tensorPowIdx ι u * tensorPowIdx ι v`. -/
theorem tensorPowIdx_mul [DecidableEq ι] (u v : Matrix n n R) :
    tensorPowIdx ι (u * v) = tensorPowIdx ι u * tensorPowIdx ι v := by
  ext f h
  simp only [tensorPowIdx_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun g _ ↦ Finset.prod_mul_distrib

omit [DecidableEq n] in
/-- At the index type `n` itself, the Kronecker power of `Matrix.tensorPowIdx` is the one of
`Matrix.tensorPow`. -/
theorem tensorPowIdx_eq_tensorPow (u : Matrix n n R) : tensorPowIdx n u = Matrix.tensorPow u :=
  rfl

end Matrix

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- **The standard-basis reindexing `⨁_I 𝟙 ≅ ⨁_J 𝟙` along an equivalence `e : I ≃ J`** of finite
index types: it sends `e_i` to `e_{e i}`. -/
def unitBiproductReindexIso {I J : Type} [Finite I] [Finite J] (e : I ≃ J) :
    (⨁ fun _ : I => 𝟙_ C) ≅ ⨁ fun _ : J => 𝟙_ C where
  hom := biproduct.desc fun i => biproduct.ι (fun _ : J => 𝟙_ C) (e i)
  inv := biproduct.desc fun j => biproduct.ι (fun _ : I => 𝟙_ C) (e.symm j)
  hom_inv_id := biproduct.hom_ext' _ _ fun _ => by simp
  inv_hom_id := biproduct.hom_ext' _ _ fun _ => by simp

omit [MonoidalPreadditive C] in
/-- The reindexing isomorphism sends the `i`-th summand to the `e i`-th summand. -/
@[reassoc (attr := simp)]
lemma biproduct_ι_comp_unitBiproductReindexIso_hom {I J : Type} [Finite I] [Finite J]
    (e : I ≃ J) (i : I) :
    biproduct.ι (fun _ : I => 𝟙_ C) i ≫ (unitBiproductReindexIso e).hom =
      biproduct.ι (fun _ : J => 𝟙_ C) (e i) := by
  simp [unitBiproductReindexIso]

omit [MonoidalPreadditive C] in
/-- The inverse of the reindexing isomorphism sends the `j`-th summand to the `e.symm j`-th
summand. -/
@[reassoc (attr := simp)]
lemma biproduct_ι_comp_unitBiproductReindexIso_inv {I J : Type} [Finite I] [Finite J]
    (e : I ≃ J) (j : J) :
    biproduct.ι (fun _ : J => 𝟙_ C) j ≫ (unitBiproductReindexIso (C := C) e).inv =
      biproduct.ι (fun _ : I => 𝟙_ C) (e.symm j) := by
  simp [unitBiproductReindexIso]

omit [MonoidalPreadditive C] in
/-- The standard-basis reindexing read on the projections. -/
@[reassoc]
lemma unitBiproductReindexIso_hom_comp_biproduct_π {I J : Type} [Finite I] [Finite J]
    (e : I ≃ J) (j : J) :
    (unitBiproductReindexIso (C := C) e).hom ≫ biproduct.π (fun _ : J => 𝟙_ C) j =
      biproduct.π (fun _ : I => 𝟙_ C) (e.symm j) := by
  refine biproduct.hom_ext' _ _ fun i => ?_
  rw [biproduct_ι_comp_unitBiproductReindexIso_hom_assoc]
  rcases eq_or_ne i (e.symm j) with rfl | hi
  · simp
  · rw [biproduct.ι_π_ne _ (fun h => hi (e.eq_symm_apply.mpr h)), biproduct.ι_π_ne _ hi]

omit [MonoidalPreadditive C] in
/-- **The matrix of a conjugate by a reindexing isomorphism is the reindexed matrix.** -/
theorem unitMatrixEquiv_reindex {I J : Type} [Finite I] [Finite J] (e : I ≃ J)
    (H : (⨁ fun _ : I => 𝟙_ C) ⟶ ⨁ fun _ : I => 𝟙_ C) (j j' : J) :
    unitMatrixEquiv J ((unitBiproductReindexIso e).inv ≫ H ≫
        (unitBiproductReindexIso e).hom) j j' =
      unitMatrixEquiv I H (e.symm j) (e.symm j') := by
  rw [unitMatrixEquiv_apply, unitMatrixEquiv_apply]
  simp only [biproduct.components, Category.assoc]
  rw [biproduct_ι_comp_unitBiproductReindexIso_inv_assoc,
    unitBiproductReindexIso_hom_comp_biproduct_π]

end CategoryTheory.MonoidalCategory

namespace Stacks.EtaleCohomology.BrauerScheme

/-- **The reindexing `(Fin j → Fin d) × Fin d ≃ (Fin (j+1) → Fin d)`**, appending the second
component as the last entry. It is `Fin.succFunEquiv` read in the direction the recursion of
`Stacks.TensorPowers.natTensorPow` — which adds its new tensor factor on the right — needs it, and
it is the index-type half of the recursion step of `natTensorPowFreeIso`. -/
def finSnocEquiv (j d : ℕ) : ((Fin j → Fin d) × Fin d) ≃ (Fin (j + 1) → Fin d) :=
  (Fin.succFunEquiv (Fin d) j).symm

/-- The inverse of `finSnocEquiv` splits a tuple into its initial segment and its last entry. -/
@[simp]
lemma finSnocEquiv_symm_apply (j d : ℕ) (q : Fin (j + 1) → Fin d) :
    (finSnocEquiv j d).symm q = (Fin.init q, q (Fin.last j)) :=
  rfl

variable (S : Scheme.{u}) (d : ℕ)

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

/-- **The reindexing `𝒪_S^I ≅ 𝒪_S^J` of free sheaves of modules along an equivalence `e : I ≃ J`**
of finite index types, the standard-basis map `e_i ↦ e_{e i}`. It is spelled through
`freeBiproductIso`, so that the matrix identity `freeEndMatrixEquiv_reindex` is a computation with
`biproduct.ι` and `biproduct.π`; see the implementation notes. -/
def freeReindexIso {I J : Type} [Finite I] [Finite J] (e : I ≃ J) :
    _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ≅
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} J) :=
  freeBiproductIso S I ≪≫ unitBiproductReindexIso e ≪≫ (freeBiproductIso S J).symm

/-- **The matrix of a conjugate by a reindexing isomorphism is the reindexed matrix**, entrywise.
-/
theorem freeEndMatrixEquiv_reindex_apply {I J : Type} [Finite I] [Finite J] (e : I ≃ J)
    (g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) (j j' : J) :
    freeEndMatrixEquiv S J ((freeReindexIso S e).inv ≫ g ≫ (freeReindexIso S e).hom) j j' =
      freeEndMatrixEquiv S I g (e.symm j) (e.symm j') := by
  have key : (freeBiproductIso S J).inv ≫
      ((freeReindexIso S e).inv ≫ g ≫ (freeReindexIso S e).hom) ≫ (freeBiproductIso S J).hom =
      (unitBiproductReindexIso e).inv ≫
        ((freeBiproductIso S I).inv ≫ g ≫ (freeBiproductIso S I).hom) ≫
        (unitBiproductReindexIso e).hom := by
    simp only [freeReindexIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [freeEndMatrixEquiv_apply, key, unitMatrixEquiv_reindex, freeEndMatrixEquiv_apply]

/-- **The matrix of a conjugate by a reindexing isomorphism is the reindexed matrix.** -/
theorem freeEndMatrixEquiv_reindex {I J : Type} [Finite I] [Finite J] (e : I ≃ J)
    (g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I)) :
    freeEndMatrixEquiv S J ((freeReindexIso S e).inv ≫ g ≫ (freeReindexIso S e).hom) =
      Matrix.reindex e e (freeEndMatrixEquiv S I g) := by
  refine Matrix.ext fun j j' => ?_
  exact freeEndMatrixEquiv_reindex_apply S e g j j'

/-- **One Kronecker step: the matrix of `h ⊗ₘ k` conjugated by `tensorIso a (Iso.refl _)`, the
two-factor standard-basis identification and a reindexing.** Its entry at `(p, q)` is the product
of the entry of the matrix of the conjugate `a.inv ≫ h ≫ a.hom` at the first halves of `e.symm p`
and `e.symm q` and the entry of the matrix of `k` at the second halves.

The first factor `X` and its identification `a : X ≅ 𝒪_S^I` are *variables*, and that is the whole
point: `Stacks.TensorPowers.natTensorPow M (j+1)` is only definitionally `natTensorPow M j ⊗ M`,
so neither `simp` nor `rw` will match a pattern keyed on `_ ⊗ _` against it, while instantiating
this lemma at `X := natTensorPow M j` is checked at full transparency and goes through. -/
theorem freeEndMatrixEquiv_tensorIso_reindex (I K J : Type) [Finite I] [Finite K] [Finite J]
    (e : I × K ≃ J) {X : ModuleSheaf S}
    (a : X ≅ _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} I))
    (h : X ⟶ X)
    (k : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} K)) (p q : J) :
    freeEndMatrixEquiv S J
        ((tensorIso a (Iso.refl _) ≪≫ freeTensorFreeBiproductIso S I K ≪≫
            freeReindexIso S e).inv ≫ (h ⊗ₘ k) ≫
          (tensorIso a (Iso.refl _) ≪≫ freeTensorFreeBiproductIso S I K ≪≫
            freeReindexIso S e).hom) p q =
      freeEndMatrixEquiv S I (a.inv ≫ h ≫ a.hom) (e.symm p).1 (e.symm q).1 *
        freeEndMatrixEquiv S K k (e.symm p).2 (e.symm q).2 := by
  have hW : (tensorIso a (Iso.refl _) ≪≫ freeTensorFreeBiproductIso S I K ≪≫
          freeReindexIso S e).inv ≫ (h ⊗ₘ k) ≫
        (tensorIso a (Iso.refl _) ≪≫ freeTensorFreeBiproductIso S I K ≪≫
          freeReindexIso S e).hom =
      (freeReindexIso S e).inv ≫
        ((freeTensorFreeBiproductIso S I K).inv ≫ ((a.inv ≫ h ≫ a.hom) ⊗ₘ k) ≫
          (freeTensorFreeBiproductIso S I K).hom) ≫ (freeReindexIso S e).hom := by
    simp only [Iso.trans_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom,
      Iso.refl_inv, Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Category.comp_id]
  rw [hW, freeEndMatrixEquiv_reindex_apply]
  exact freeEndMatrixEquiv_tensorHom S I K (a.inv ≫ h ≫ a.hom) k
    (e.symm p).1 (e.symm q).1 (e.symm p).2 (e.symm q).2

/-- **The `j`-fold tensor power `f^{⊗ j} : M^{⊗ j} ⟶ M^{⊗ j}` of an endomorphism** of a sheaf of
`𝒪_S`-modules. `Stacks.TensorPowers.natTensorPow` adds its factors on the right, so the recursion
tensors the previous power with `f` on the right. -/
def natTensorPowMap {M : ModuleSheaf S} (f : M ⟶ M) :
    ∀ j : ℕ, Stacks.TensorPowers.natTensorPow M j ⟶ Stacks.TensorPowers.natTensorPow M j
  | 0 => 𝟙 _
  | j + 1 => natTensorPowMap f j ⊗ₘ f

/-- The `0`-fold tensor power of an endomorphism is the identity. -/
@[simp]
lemma natTensorPowMap_zero {M : ModuleSheaf S} (f : M ⟶ M) : natTensorPowMap S f 0 = 𝟙 _ :=
  rfl

/-- The `(j + 1)`-fold tensor power of `f` is the `j`-fold tensor power of `f` tensored with `f` on
the right. -/
@[simp]
lemma natTensorPowMap_succ {M : ModuleSheaf S} (f : M ⟶ M) (j : ℕ) :
    natTensorPowMap S f (j + 1) = natTensorPowMap S f j ⊗ₘ f :=
  rfl

/-- **The `j`-fold tensor power of the identity is the identity.** -/
@[simp]
theorem natTensorPowMap_id {M : ModuleSheaf S} :
    ∀ j : ℕ, natTensorPowMap S (𝟙 M) j = 𝟙 (Stacks.TensorPowers.natTensorPow M j)
  | 0 => rfl
  | j + 1 => by
    have h : natTensorPowMap S (𝟙 M) j ⊗ₘ 𝟙 M =
        𝟙 (Stacks.TensorPowers.natTensorPow M j ⊗ M) := by
      rw [natTensorPowMap_id j, id_tensorHom_id]
    exact h

/-- **Taking the `j`-fold tensor power of an endomorphism is multiplicative.** -/
theorem natTensorPowMap_comp {M : ModuleSheaf S} (f g : M ⟶ M) :
    ∀ j : ℕ, natTensorPowMap S (f ≫ g) j = natTensorPowMap S f j ≫ natTensorPowMap S g j
  | 0 => (Category.id_comp _).symm
  | j + 1 => by
    have h : natTensorPowMap S (f ≫ g) j ⊗ₘ (f ≫ g) =
        (natTensorPowMap S f j ⊗ₘ f) ≫ (natTensorPowMap S g j ⊗ₘ g) := by
      rw [natTensorPowMap_comp f g j, tensorHom_comp_tensorHom]
    exact h

/-- **The `j`-fold tensor power of `𝒪_S^d` is the free sheaf of `𝒪_S`-modules on
`Fin j → Fin d`.** The degree-zero case is `Stacks.SheafOfModules.Invertible.freeUniqueIso`, the
free sheaf on the one-element type `Fin 0 → Fin d` being the unit; each further factor is added
with the two-factor standard-basis identification `freeTensorFreeBiproductIso`, followed by the
reindexing `finSnocEquiv` which puts the new factor last. -/
def natTensorPowFreeIso : ∀ j : ℕ,
    Stacks.TensorPowers.natTensorPow
        (_root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d))) j ≅
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf)
        (ULift.{u, 0} (Fin j → Fin d))
  | 0 =>
    (Invertible.freeUniqueIso (R := Tensor.ringSheaf S.sheaf)
      (ULift.{u, 0} (Fin 0 → Fin d))).symm
  | j + 1 =>
    tensorIso (natTensorPowFreeIso j) (Iso.refl _) ≪≫
      freeTensorFreeBiproductIso S (Fin j → Fin d) (Fin d) ≪≫
      freeReindexIso S (finSnocEquiv j d)

/-- The recursion step of `natTensorPowFreeIso`, as a rewrite. -/
lemma natTensorPowFreeIso_succ (j : ℕ) :
    natTensorPowFreeIso S d (j + 1) =
      tensorIso (natTensorPowFreeIso S d j) (Iso.refl _) ≪≫
        freeTensorFreeBiproductIso S (Fin j → Fin d) (Fin d) ≪≫
        freeReindexIso S (finSnocEquiv j d) :=
  rfl

/-- **The iterated Kronecker law, entrywise.** The `(f', g')` entry of the matrix of the `j`-fold
tensor power of `f`, read through `natTensorPowFreeIso`, is `∏ k, u (f' k) (g' k)` for `u` the
matrix of `f`. The inductive step is `freeEndMatrixEquiv_tensorIso_reindex` — the two-factor
Kronecker law `freeEndMatrixEquiv_tensorHom` composed with the reindexing law
`freeEndMatrixEquiv_reindex_apply` — and `Fin.prod_univ_castSucc` splits off the last factor. -/
theorem freeEndMatrixEquiv_natTensorPowMap_apply
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d))) :
    ∀ (j : ℕ) (f' g' : Fin j → Fin d),
      freeEndMatrixEquiv S (Fin j → Fin d)
          ((natTensorPowFreeIso S d j).inv ≫ natTensorPowMap S f j ≫
            (natTensorPowFreeIso S d j).hom) f' g' =
        ∏ k, freeEndMatrixEquiv S (Fin d) f (f' k) (g' k)
  | 0, f', g' => by
    obtain rfl : f' = g' := Subsingleton.elim _ _
    rw [natTensorPowMap_zero, Category.id_comp, Iso.inv_hom_id, freeEndMatrixEquiv_id,
      Matrix.one_apply_eq]
    simp
  | j + 1, f', g' => by
    have step : freeEndMatrixEquiv S (Fin (j + 1) → Fin d)
          ((natTensorPowFreeIso S d (j + 1)).inv ≫ natTensorPowMap S f (j + 1) ≫
            (natTensorPowFreeIso S d (j + 1)).hom) f' g' =
        freeEndMatrixEquiv S (Fin j → Fin d)
            ((natTensorPowFreeIso S d j).inv ≫ natTensorPowMap S f j ≫
              (natTensorPowFreeIso S d j).hom) (Fin.init f') (Fin.init g') *
          freeEndMatrixEquiv S (Fin d) f (f' (Fin.last j)) (g' (Fin.last j)) :=
      freeEndMatrixEquiv_tensorIso_reindex S (Fin j → Fin d) (Fin d) (Fin (j + 1) → Fin d)
        (finSnocEquiv j d) (natTensorPowFreeIso S d j) (natTensorPowMap S f j) f f' g'
    rw [step, freeEndMatrixEquiv_natTensorPowMap_apply f j, Fin.prod_univ_castSucc]
    rfl

/-- **THE ITERATED KRONECKER LAW.** Under the identification `natTensorPowFreeIso` of the
`j`-fold tensor power of `𝒪_S^d` with the free sheaf of modules on `Fin j → Fin d`, the matrix of
the `j`-fold tensor power of an endomorphism `f` of `𝒪_S^d` is the `j`-fold Kronecker power of the
matrix of `f`. -/
theorem freeEndMatrixEquiv_natTensorPowMap (j : ℕ)
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d))) :
    freeEndMatrixEquiv S (Fin j → Fin d)
        ((natTensorPowFreeIso S d j).inv ≫ natTensorPowMap S f j ≫
          (natTensorPowFreeIso S d j).hom) =
      Matrix.tensorPowIdx (Fin j) (freeEndMatrixEquiv S (Fin d) f) := by
  refine Matrix.ext fun f' g' => ?_
  rw [Matrix.tensorPowIdx_apply]
  exact freeEndMatrixEquiv_natTensorPowMap_apply S d f j f' g'

/-- **The iterated Kronecker law at `j = d`**, where the Kronecker power is `Matrix.tensorPow`,
the one indexed by `Fin d → Fin d` on which the alternating vector and the projector
`Matrix.altProj` of [Stacks, Tag 0A2L] live. -/
theorem freeEndMatrixEquiv_natTensorPowMap_self
    (f : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d))) :
    freeEndMatrixEquiv S (Fin d → Fin d)
        ((natTensorPowFreeIso S d d).inv ≫ natTensorPowMap S f d ≫
          (natTensorPowFreeIso S d d).hom) =
      Matrix.tensorPow (freeEndMatrixEquiv S (Fin d) f) := by
  rw [freeEndMatrixEquiv_natTensorPowMap, Matrix.tensorPowIdx_eq_tensorPow]

/-- **The `d`-fold Kronecker power of a conjugation fixes the alternating projector.** If
`f ≫ g = 𝟙` then the matrices of `f` and `g` are mutually inverse, so by
`Matrix.tensorPow_mul_altProj_mul_tensorPow` the determinants their Kronecker powers pick up on
the two sides of `Matrix.altProj (R₀ S)` cancel. Through
`freeEndMatrixEquiv_natTensorPowMap_self` this is the statement that the `d`-fold tensor power of
the conjugation leaves the projector of [Stacks, Tag 0A2L] unchanged — the agreement of two
trivialisations of an Azumaya algebra. -/
theorem conj_natTensorPowMap_altProj
    (f g : _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)) ⟶
      _root_.SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)))
    (hfg : f ≫ g = 𝟙 _) :
    Matrix.tensorPow (freeEndMatrixEquiv S (Fin d) f) * Matrix.altProj (R₀ S) *
        Matrix.tensorPow (freeEndMatrixEquiv S (Fin d) g) = Matrix.altProj (R₀ S) :=
  Matrix.tensorPow_mul_altProj_mul_tensorPow
    (by rw [← freeEndMatrixEquiv_comp, hfg, freeEndMatrixEquiv_id])

end Stacks.EtaleCohomology.BrauerScheme

end

end

module

public import StacksFrontier.Homology.Perfect.BalancedDerivedTensor
public import StacksFrontier.Homology.Perfect.FiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import Mathlib.Algebra.Homology.BifunctorFlip
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
import all StacksFrontier.Homology.Perfect.FiniteTorDimension

/-!
# Perfectness from the vanishing of total complexes

Let `Λ` be a finite ring, not necessarily commutative. This file reduces the perfectness of a
complex `L` of left `Λ`-modules with finite cohomology to the vanishing of one cohomology module
of the total complexes `Tot(R ⊗[Λ] L)`, where `R` runs over the (truncated) finite free
resolutions of the finite right `Λ`-modules. This is the algebraic half of the proof of
[Stacks, Tag 03TV]: there `L` computes `RΓ(X_k̄, K)`, and `Tot(R ⊗[Λ] L)` is the global sections
of a complex of sheaves whose low-degree cohomology the finite cohomological dimension of a curve
controls. It replaces the projection formula `N ⊗ᴸ RΓ(X, K) = RΓ(X, N ⊗ᴸ K)` of the source: only
the finite free terms of `R` are ever tensored with a sheaf, and for those the tensor product is
a finite power.

## Main definitions

* `StacksDraft.Perfect.TorTotal.powFunctor`, `StacksDraft.Perfect.TorTotal.rightPowFunctor`: the
  functors `M ↦ (ι → M)` from left, resp. right, `Λ`-modules to abelian groups.
* `StacksDraft.Perfect.TorTotal.tensorBasisRightIso`,
  `StacksDraft.Perfect.TorTotal.tensorBasisLeftIso`:
  tensoring with a finite free module is a finite power.

## Main results

* `StacksDraft.Perfect.TorTotal.quasiIso_mapBifunctorMap_right`,
  `StacksDraft.Perfect.TorTotal.quasiIso_mapBifunctorMap_left`: quasi-isomorphisms of bounded
  above complexes induce quasi-isomorphisms of total complexes when the bifunctor is exact in the
  other variable at every term.
* `StacksDraft.Perfect.TorTotal.projective_cokernel_of_finite_tensor_exact`: the projectivity
  criterion of the proof of Tag 03TO with finite test modules.
* `StacksDraft.Perfect.TorTotal.isPerfect_of_isZero_homology_mapBifunctor`: **perfectness from
  the vanishing of total complexes.**

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03TO](https://stacks.math.columbia.edu/tag/03TO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace StacksDraft.Perfect.TorTotal

variable {Λ : Type u} [Ring Λ]

/-! ### Finite powers -/

/-- The functor `M ↦ (ι → M)` from left `Λ`-modules to abelian groups. -/
def powFunctor (ι : Type v) : ModuleCat.{v} Λ ⥤ ModuleCat.{v} ℤ where
  obj M := ModuleCat.of ℤ (ι → M)
  map f := ModuleCat.ofHom (intLinearMapOfAddHom
    (Pi.addMonoidHom fun i => f.hom.toAddMonoidHom.comp (Pi.evalAddMonoidHom _ i)))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `powFunctor ι` applies a morphism coordinatewise. -/
@[simp]
lemma powFunctor_map_apply (ι : Type v) {M M' : ModuleCat.{v} Λ} (f : M ⟶ M') (x : ι → M)
    (i : ι) : ((powFunctor ι).map f) x i = f (x i) :=
  rfl

/-- The functor `N ↦ (ι → N)` from right `Λ`-modules to abelian groups. -/
def rightPowFunctor (ι : Type v) : ModuleCat.{v} (MulOpposite Λ) ⥤ ModuleCat.{v} ℤ where
  obj N := ModuleCat.of ℤ (ι → N)
  map f := ModuleCat.ofHom (intLinearMapOfAddHom
    (Pi.addMonoidHom fun i => f.hom.toAddMonoidHom.comp (Pi.evalAddMonoidHom _ i)))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `rightPowFunctor ι` applies a morphism coordinatewise. -/
@[simp]
lemma rightPowFunctor_map_apply (ι : Type v) {N N' : ModuleCat.{v} (MulOpposite Λ)} (f : N ⟶ N')
    (x : ι → N) (i : ι) : ((rightPowFunctor ι).map f) x i = f (x i) :=
  rfl

/-! ### The universal property, as a lift -/

section Lift

variable (D : BalancedDerivedTensoring.{u, v} Λ)

/-- The morphism out of `N ⊗[Λ] M` determined by a balanced bilinear map. -/
def tensorLift (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ) (Q : ModuleCat.{v} ℤ)
    (f : N →ₗ[ℤ] M →ₗ[ℤ] Q)
    (hf : ∀ (n : N) (a : Λ) (m : M), f (MulOpposite.op a • n) m = f n (a • m)) :
    (D.ordinary.obj N).obj M ⟶ Q :=
  (D.universal N M Q f hf).exists.choose

/-- The lift of a balanced bilinear map `f` sends the pure tensor `n ⊗ m` to `f n m`. -/
@[simp]
lemma tensorLift_pure (N : ModuleCat.{v} (MulOpposite Λ)) (M : ModuleCat.{v} Λ)
    (Q : ModuleCat.{v} ℤ) (f : N →ₗ[ℤ] M →ₗ[ℤ] Q)
    (hf : ∀ (n : N) (a : Λ) (m : M), f (MulOpposite.op a • n) m = f n (a • m)) (n : N) (m : M) :
    tensorLift D N M Q f hf (D.pure N M n m) = f n m :=
  (D.universal N M Q f hf).exists.choose_spec n m

/-- Every element of `N ⊗[Λ] M` is a finite sum of pure tensors; in the form used here, two
additive maps out of `N ⊗[Λ] M` into an abelian group agreeing on pure tensors agree. -/
lemma tensor_ext {N : ModuleCat.{v} (MulOpposite Λ)} {M : ModuleCat.{v} Λ} {Q : ModuleCat.{v} ℤ}
    (f g : (D.ordinary.obj N).obj M ⟶ Q) (h : ∀ (n : N) (m : M), f (D.pure N M n m) =
      g (D.pure N M n m)) : f = g :=
  tensor_hom_ext D N M Q f g h

end Lift

/-! ### Tensoring with a right module with a basis -/

section RightBasis

variable (D : BalancedDerivedTensoring.{u, v} Λ) {N : ModuleCat.{v} (MulOpposite Λ)}
  {ι : Type v} [Fintype ι] (b : Module.Basis ι (MulOpposite Λ) N)

include b

/-- The coordinates `(n, m) ↦ (i ↦ nᵢ m)` of a pure tensor against a basis of the right
module. -/
def rightCoord (M : ModuleCat.{v} Λ) : N →ₗ[ℤ] M →ₗ[ℤ] (powFunctor ι).obj M :=
  intLinearMapOfAddHom
    { toFun := fun n => intLinearMapOfAddHom
        { toFun := fun m => (fun i => (b.repr n i).unop • m : ι → M)
          map_zero' := by funext i; exact smul_zero _
          map_add' := fun m m' => by funext i; exact smul_add _ _ _ }
      map_zero' := by
        refine LinearMap.ext fun m => ?_
        funext i
        change (b.repr 0 i).unop • m = 0
        simp
      map_add' := fun n n' => by
        refine LinearMap.ext fun m => ?_
        funext i
        change (b.repr (n + n') i).unop • m = (b.repr n i).unop • m + (b.repr n' i).unop • m
        simp [add_smul] }

/-- The `i`-th coordinate of `rightCoord b M n m` is `nᵢ m`. -/
@[simp]
lemma rightCoord_apply (M : ModuleCat.{v} Λ) (n : N) (m : M) (i : ι) :
    rightCoord b M n m i = (b.repr n i).unop • m :=
  rfl

/-- The bilinear map `rightCoord b M` is `Λ`-balanced: `(n a, m)` and `(n, a m)` have the same
coordinates. -/
lemma rightCoord_balanced (M : ModuleCat.{v} Λ) (n : N) (a : Λ) (m : M) :
    rightCoord b M (MulOpposite.op a • n) m = rightCoord b M n (a • m) := by
  funext i
  show (b.repr (MulOpposite.op a • n) i).unop • m = (b.repr n i).unop • a • m
  simp [mul_smul]

/-- The map `N ⊗[Λ] M → (ι → M)` taking coordinates against the basis of `N`. -/
def tensorBasisRightHom (M : ModuleCat.{v} Λ) : (D.ordinary.obj N).obj M ⟶ (powFunctor ι).obj M :=
  tensorLift D N M _ (rightCoord b M) (rightCoord_balanced b M)

/-- The map `tensorBasisRightHom D b M` sends `n ⊗ m` to `i ↦ nᵢ m`. -/
@[simp]
lemma tensorBasisRightHom_pure (M : ModuleCat.{v} Λ) (n : N) (m : M) :
    tensorBasisRightHom D b M (D.pure N M n m) = fun i => (b.repr n i).unop • m := by
  rw [tensorBasisRightHom, tensorLift_pure]
  rfl

/-- The map `(ι → M) → N ⊗[Λ] M`, `x ↦ ∑ᵢ bᵢ ⊗ xᵢ`. -/
def tensorBasisRightInv (M : ModuleCat.{v} Λ) : (powFunctor ι).obj M ⟶ (D.ordinary.obj N).obj M :=
  ModuleCat.ofHom (intLinearMapOfAddHom
    { toFun := fun x => ∑ i, D.pure N M (b i) (x i)
      map_zero' := by simp
      map_add' := by intros; simp [Finset.sum_add_distrib] })

/-- The map `tensorBasisRightInv D b M` sends `x` to `∑ᵢ bᵢ ⊗ xᵢ`. -/
@[simp]
lemma tensorBasisRightInv_apply (M : ModuleCat.{v} Λ) (x : ι → M) :
    tensorBasisRightInv D b M x = ∑ i, D.pure N M (b i) (x i) :=
  rfl

/-- `tensorBasisRightInv D b M` is a right inverse of `tensorBasisRightHom D b M`. -/
lemma tensorBasisRightHom_inv_apply (M : ModuleCat.{v} Λ) (x : ι → M) :
    tensorBasisRightHom D b M (tensorBasisRightInv D b M x) = x := by
  rw [tensorBasisRightInv_apply, map_sum]
  simp_rw [tensorBasisRightHom_pure]
  show (∑ k, (fun i => (b.repr (b k) i).unop • x k : ι → M)) = x
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Module.Basis.repr_self, Finsupp.single_apply, hk]
  · simp

/-- `tensorBasisRightInv D b M` is a left inverse of `tensorBasisRightHom D b M` on pure
tensors. -/
lemma tensorBasisRightInv_hom_pure (M : ModuleCat.{v} Λ) (n : N) (m : M) :
    tensorBasisRightInv D b M (tensorBasisRightHom D b M (D.pure N M n m)) = D.pure N M n m := by
  rw [tensorBasisRightHom_pure, tensorBasisRightInv_apply]
  simp_rw [← D.balanced, MulOpposite.op_unop]
  rw [← LinearMap.sum_apply, ← map_sum, b.sum_repr]

/-- **Tensoring with a right module with a finite basis indexed by `ι` is the `ι`-th power.** -/
def tensorBasisRightIso : D.ordinary.obj N ≅ powFunctor ι :=
  NatIso.ofComponents
    (fun M =>
      { hom := tensorBasisRightHom D b M
        inv := tensorBasisRightInv D b M
        hom_inv_id := tensor_ext D _ _ fun n m => tensorBasisRightInv_hom_pure D b M n m
        inv_hom_id := by
          ext x
          exact tensorBasisRightHom_inv_apply D b M x })
    (fun {M M'} g => by
      refine tensor_ext D (Q := (powFunctor ι).obj M') _ _ fun n m => ?_
      change tensorBasisRightHom D b M' ((D.ordinary.obj N).map g (D.pure N M n m)) =
        (powFunctor ι).map g (tensorBasisRightHom D b M (D.pure N M n m))
      rw [D.natural_right, tensorBasisRightHom_pure, tensorBasisRightHom_pure]
      funext i
      simp)

/-- The isomorphism `tensorBasisRightIso D b` sends `n ⊗ m` to `i ↦ nᵢ m`. -/
@[simp]
lemma tensorBasisRightIso_hom_app_pure (M : ModuleCat.{v} Λ) (n : N) (m : M) :
    (tensorBasisRightIso D b).hom.app M (D.pure N M n m) = fun i => (b.repr n i).unop • m :=
  tensorBasisRightHom_pure D b M n m

end RightBasis

/-! ### Tensoring with a left module with a basis -/

section LeftBasis

variable (D : BalancedDerivedTensoring.{u, v} Λ) {M : ModuleCat.{v} Λ}
  {ι : Type v} [Fintype ι] (b : Module.Basis ι Λ M)

include b

/-- The coordinates `(n, m) ↦ (i ↦ n mᵢ)` of a pure tensor against a basis of the left
module. -/
def leftCoord (N : ModuleCat.{v} (MulOpposite Λ)) : N →ₗ[ℤ] M →ₗ[ℤ] (rightPowFunctor ι).obj N :=
  intLinearMapOfAddHom
    { toFun := fun n => intLinearMapOfAddHom
        { toFun := fun m => (fun i => MulOpposite.op (b.repr m i) • n : ι → N)
          map_zero' := by
            funext i
            change MulOpposite.op (b.repr 0 i) • n = 0
            simp
          map_add' := fun m m' => by
            funext i
            change MulOpposite.op (b.repr (m + m') i) • n =
              MulOpposite.op (b.repr m i) • n + MulOpposite.op (b.repr m' i) • n
            simp [add_smul] }
      map_zero' := by
        refine LinearMap.ext fun m => ?_
        funext i
        exact smul_zero _
      map_add' := fun n n' => by
        refine LinearMap.ext fun m => ?_
        funext i
        exact smul_add _ _ _ }

/-- The `i`-th coordinate of `leftCoord b N n m` is `n mᵢ`. -/
@[simp]
lemma leftCoord_apply (N : ModuleCat.{v} (MulOpposite Λ)) (n : N) (m : M) (i : ι) :
    leftCoord b N n m i = MulOpposite.op (b.repr m i) • n :=
  rfl

/-- The bilinear map `leftCoord b N` is `Λ`-balanced: `(n a, m)` and `(n, a m)` have the same
coordinates. -/
lemma leftCoord_balanced (N : ModuleCat.{v} (MulOpposite Λ)) (n : N) (a : Λ) (m : M) :
    leftCoord b N (MulOpposite.op a • n) m = leftCoord b N n (a • m) := by
  funext i
  show MulOpposite.op (b.repr m i) • MulOpposite.op a • n = MulOpposite.op (b.repr (a • m) i) • n
  simp [← mul_smul]

/-- The map `N ⊗[Λ] M → (ι → N)` taking coordinates against the basis of `M`. -/
def tensorBasisLeftHom (N : ModuleCat.{v} (MulOpposite Λ)) :
    (D.ordinary.obj N).obj M ⟶ (rightPowFunctor ι).obj N :=
  tensorLift D N M _ (leftCoord b N) (leftCoord_balanced b N)

/-- The map `tensorBasisLeftHom D b N` sends `n ⊗ m` to `i ↦ n mᵢ`. -/
@[simp]
lemma tensorBasisLeftHom_pure (N : ModuleCat.{v} (MulOpposite Λ)) (n : N) (m : M) :
    tensorBasisLeftHom D b N (D.pure N M n m) = fun i => MulOpposite.op (b.repr m i) • n := by
  rw [tensorBasisLeftHom, tensorLift_pure]
  rfl

/-- The map `(ι → N) → N ⊗[Λ] M`, `x ↦ ∑ᵢ xᵢ ⊗ bᵢ`. -/
def tensorBasisLeftInv (N : ModuleCat.{v} (MulOpposite Λ)) :
    (rightPowFunctor ι).obj N ⟶ (D.ordinary.obj N).obj M :=
  ModuleCat.ofHom (intLinearMapOfAddHom
    { toFun := fun x => ∑ i, D.pure N M (x i) (b i)
      map_zero' := by simp
      map_add' := by intros; simp [Finset.sum_add_distrib] })

/-- The map `tensorBasisLeftInv D b N` sends `x` to `∑ᵢ xᵢ ⊗ bᵢ`. -/
@[simp]
lemma tensorBasisLeftInv_apply (N : ModuleCat.{v} (MulOpposite Λ)) (x : ι → N) :
    tensorBasisLeftInv D b N x = ∑ i, D.pure N M (x i) (b i) :=
  rfl

/-- `tensorBasisLeftInv D b N` is a right inverse of `tensorBasisLeftHom D b N`. -/
lemma tensorBasisLeftHom_inv_apply (N : ModuleCat.{v} (MulOpposite Λ)) (x : ι → N) :
    tensorBasisLeftHom D b N (tensorBasisLeftInv D b N x) = x := by
  rw [tensorBasisLeftInv_apply, map_sum]
  simp_rw [tensorBasisLeftHom_pure]
  show (∑ k, (fun i => MulOpposite.op (b.repr (b k) i) • x k : ι → N)) = x
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Module.Basis.repr_self, Finsupp.single_apply, hk]
  · simp

/-- `tensorBasisLeftInv D b N` is a left inverse of `tensorBasisLeftHom D b N` on pure
tensors. -/
lemma tensorBasisLeftInv_hom_pure (N : ModuleCat.{v} (MulOpposite Λ)) (n : N) (m : M) :
    tensorBasisLeftInv D b N (tensorBasisLeftHom D b N (D.pure N M n m)) = D.pure N M n m := by
  rw [tensorBasisLeftHom_pure, tensorBasisLeftInv_apply]
  simp_rw [D.balanced]
  rw [← map_sum, b.sum_repr]

/-- **Tensoring with a left module with a finite basis indexed by `ι` is the `ι`-th power.** -/
def tensorBasisLeftIso : D.ordinary.flip.obj M ≅ rightPowFunctor ι :=
  NatIso.ofComponents
    (fun N =>
      { hom := tensorBasisLeftHom D b N
        inv := tensorBasisLeftInv D b N
        hom_inv_id := tensor_ext D _ _ fun n m => tensorBasisLeftInv_hom_pure D b N n m
        inv_hom_id := by
          ext x
          exact tensorBasisLeftHom_inv_apply D b N x })
    (fun {N N'} g => by
      refine tensor_ext D (Q := (rightPowFunctor ι).obj N') _ _ fun n m => ?_
      change tensorBasisLeftHom D b N' ((D.ordinary.map g).app M (D.pure N M n m)) =
        (rightPowFunctor ι).map g (tensorBasisLeftHom D b N (D.pure N M n m))
      rw [D.natural_left, tensorBasisLeftHom_pure, tensorBasisLeftHom_pure]
      funext i
      simp)

/-- The isomorphism `tensorBasisLeftIso D b` sends `n ⊗ m` to `i ↦ n mᵢ`. -/
@[simp]
lemma tensorBasisLeftIso_hom_app_pure (N : ModuleCat.{v} (MulOpposite Λ)) (n : N) (m : M) :
    (tensorBasisLeftIso D b).hom.app N (D.pure N M n m) =
      fun i => MulOpposite.op (b.repr m i) • n :=
  tensorBasisLeftHom_pure D b N n m

end LeftBasis

/-! ### Exactness -/

section Exactness

/-- The `ι`-th power functor on left modules is additive. -/
instance powFunctor_additive (ι : Type v) : (powFunctor (Λ := Λ) ι).Additive where
  map_add := rfl

/-- The `ι`-th power functor on right modules is additive. -/
instance rightPowFunctor_additive (ι : Type v) : (rightPowFunctor (Λ := Λ) ι).Additive where
  map_add := rfl

/-- **The `ι`-th power functor preserves homology**: exactness of a sequence of modules is checked
elementwise, and so coordinatewise on the powers. -/
instance powFunctor_preservesHomology (ι : Type v) :
    (powFunctor (Λ := Λ) ι).PreservesHomology := by
  refine ((Functor.exact_tfae (powFunctor (Λ := Λ) ι)).out 2 3).1 fun S hS => ?_
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x hx
  have hx' : ∀ i, S.g (x i) = 0 := fun i => congrFun hx i
  choose y hy using fun i => hS (x i) (hx' i)
  exact ⟨y, funext hy⟩

/-- **The `ι`-th power functor on right modules preserves homology.** -/
instance rightPowFunctor_preservesHomology (ι : Type v) :
    (rightPowFunctor (Λ := Λ) ι).PreservesHomology := by
  refine ((Functor.exact_tfae (rightPowFunctor (Λ := Λ) ι)).out 2 3).1 fun S hS => ?_
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x hx
  have hx' : ∀ i, S.g (x i) = 0 := fun i => congrFun hx i
  choose y hy using fun i => hS (x i) (hx' i)
  exact ⟨y, funext hy⟩

/-- A functor naturally isomorphic to one preserving homology preserves homology. -/
lemma preservesHomology_of_iso {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁]
    [Abelian C₂] {F G : C₁ ⥤ C₂} [F.Additive] [G.Additive] (e : F ≅ G) [F.PreservesHomology] :
    G.PreservesHomology := by
  refine ((Functor.exact_tfae G).out 2 3).1 fun S hS => ?_
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso e)).1 (hS.map F)

end Exactness

/-! ### Tensoring with finite free modules preserves homology -/

section FreeExact

variable (D : BalancedDerivedTensoring.{u, v} Λ)

/-- Balanced tensoring is additive in each variable when the other one is fixed; in the first
variable this is read off pure tensors. -/
instance ordinary_obj_additive (N : ModuleCat.{v} (MulOpposite Λ)) : (D.ordinary.obj N).Additive :=
  D.additive N

/-- Balanced tensoring with a fixed left module is additive. -/
instance ordinary_flip_obj_additive (M : ModuleCat.{v} Λ) : (D.ordinary.flip.obj M).Additive where
  map_add {N N'} f g := by
    refine tensor_ext D _ _ fun n m => ?_
    change (D.ordinary.map (f + g)).app M (D.pure N M n m) =
      (D.ordinary.map f).app M (D.pure N M n m) + (D.ordinary.map g).app M (D.pure N M n m)
    rw [D.natural_left, D.natural_left, D.natural_left]
    simp

/-- The bifunctor of balanced tensoring is additive in its first variable. -/
instance ordinary_additive : D.ordinary.Additive where
  map_add {N N'} f g := by
    ext M : 2
    exact (D.ordinary.flip.obj M).map_add (f := f) (g := g)

/-- The bifunctor of balanced tensoring preserves zero morphisms in its first variable. -/
instance ordinary_preservesZeroMorphisms : D.ordinary.PreservesZeroMorphisms where
  map_zero N N' := by
    ext M : 2
    refine tensor_ext D _ _ fun n m => ?_
    change (D.ordinary.map 0).app M (D.pure N M n m) = 0
    rw [D.natural_left]
    simp

/-- **Tensoring with a right module with a finite basis preserves homology.** -/
lemma preservesHomology_ordinary_obj_of_basis {N : ModuleCat.{v} (MulOpposite Λ)} {ι : Type v}
    [Fintype ι] (b : Module.Basis ι (MulOpposite Λ) N) : (D.ordinary.obj N).PreservesHomology :=
  preservesHomology_of_iso (tensorBasisRightIso D b).symm

/-- **Tensoring with a left module with a finite basis preserves homology.** -/
lemma preservesHomology_ordinary_flip_obj_of_basis {M : ModuleCat.{v} Λ} {ι : Type v}
    [Fintype ι] (b : Module.Basis ι Λ M) : (D.ordinary.flip.obj M).PreservesHomology :=
  preservesHomology_of_iso (tensorBasisLeftIso D b).symm

/-- **Tensoring with a finite free right module preserves homology.** -/
lemma preservesHomology_ordinary_obj_of_free (N : ModuleCat.{v} (MulOpposite Λ))
    [Module.Free (MulOpposite Λ) N] [Module.Finite (MulOpposite Λ) N] :
    (D.ordinary.obj N).PreservesHomology :=
  preservesHomology_ordinary_obj_of_basis D (Module.Free.chooseBasis (MulOpposite Λ) N)

/-- **Tensoring with a finite free left module preserves homology.** -/
lemma preservesHomology_ordinary_flip_obj_of_free (M : ModuleCat.{v} Λ)
    [Module.Free Λ M] [Module.Finite Λ M] :
    (D.ordinary.flip.obj M).PreservesHomology :=
  preservesHomology_ordinary_flip_obj_of_basis D (Module.Free.chooseBasis Λ M)

end FreeExact

/-! ### Total complexes of bounded above double complexes built from a bifunctor -/

section Total

open HomologicalComplex

variable {C₁ C₂ E : Type*} [Category* C₁] [Category* C₂] [Category* E]
  [Abelian C₁] [Abelian C₂] [Abelian E] (G : C₁ ⥤ C₂ ⥤ E) [G.Additive]
  [∀ X, (G.obj X).Additive]

/-- A cochain complex all of whose terms vanish is zero. -/
lemma isZero_of_forall_isZero_X {A : Type*} [Category* A] [Abelian A] {K : CochainComplex A ℤ}
    (h : ∀ n, IsZero (K.X n)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  exact (h n).eq_of_src _ _

/-- The column of the double complex of a bifunctor over a vanishing term of the first complex
is zero. -/
private lemma isZero_mapBifunctorHomologicalComplex_obj_obj_X (K₁ : CochainComplex C₁ ℤ)
    (K₂ : CochainComplex C₂ ℤ) {p : ℤ} (h : IsZero (K₁.X p)) :
    IsZero ((((G.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K₁).obj K₂).X p) :=
  isZero_of_forall_isZero_X fun q => (G.map_isZero h).obj (K₂.X q)

/-- A quasi-isomorphism in the second variable is a columnwise quasi-isomorphism of the double
complexes, when the bifunctor with first variable fixed at the column preserves homology. -/
private lemma quasiIso_mapBifunctorHomologicalComplex_map_f (K₁ : CochainComplex C₁ ℤ)
    {K₂ K₂' : CochainComplex C₂ ℤ} (φ : K₂ ⟶ K₂') [QuasiIso φ] {p : ℤ}
    (hG : (G.obj (K₁.X p)).PreservesHomology) :
    QuasiIso ((((G.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K₁).map φ).f p) :=
  have := hG
  (inferInstance : QuasiIso (((G.obj (K₁.X p)).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))

/-- **A morphism in the second variable which is a quasi-isomorphism induces a quasi-isomorphism
of total complexes**, when the bifunctor with its first variable fixed at each term of the first
complex preserves homology and all three complexes are bounded above. -/
lemma quasiIso_mapBifunctorMap_right (K₁ : CochainComplex C₁ ℤ) {K₂ K₂' : CochainComplex C₂ ℤ}
    (φ : K₂ ⟶ K₂') [QuasiIso φ] (hG : ∀ p, (G.obj (K₁.X p)).PreservesHomology) (a b : ℤ)
    (h₁ : ∀ p, a < p → IsZero (K₁.X p)) (h₂ : ∀ q, b < q → IsZero (K₂.X q))
    (h₂' : ∀ q, b < q → IsZero (K₂'.X q))
    [HasMapBifunctor K₁ K₂ G (ComplexShape.up ℤ)] [HasMapBifunctor K₁ K₂' G (ComplexShape.up ℤ)] :
    QuasiIso (mapBifunctorMap (𝟙 K₁) φ G (ComplexShape.up ℤ)) := by
  unfold mapBifunctorMap
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound _ a b
    (fun p hp => isZero_mapBifunctorHomologicalComplex_obj_obj_X G K₁ K₂ (h₁ p hp))
    (fun p q hq => (G.obj (K₁.X p)).map_isZero (h₂ q hq))
    (fun p hp => isZero_mapBifunctorHomologicalComplex_obj_obj_X G K₁ K₂' (h₁ p hp))
    (fun p q hq => (G.obj (K₁.X p)).map_isZero (h₂' q hq)) fun p => ?_
  exact quasiIso_mapBifunctorHomologicalComplex_map_f G K₁ φ (hG p)

/-- **A morphism in the first variable which is a quasi-isomorphism induces a quasi-isomorphism of
total complexes**, when the bifunctor with its second variable fixed at each term of the second
complex preserves homology and all three complexes are bounded above. This is
`quasiIso_mapBifunctorMap_right` for the flipped bifunctor. -/
lemma quasiIso_mapBifunctorMap_left {K₁ K₁' : CochainComplex C₁ ℤ} (ψ : K₁ ⟶ K₁') [QuasiIso ψ]
    (K₂ : CochainComplex C₂ ℤ) (hG : ∀ q, (G.flip.obj (K₂.X q)).PreservesHomology) (a b : ℤ)
    (h₁ : ∀ p, a < p → IsZero (K₁.X p)) (h₁' : ∀ p, a < p → IsZero (K₁'.X p))
    (h₂ : ∀ q, b < q → IsZero (K₂.X q))
    [HasMapBifunctor K₁ K₂ G (ComplexShape.up ℤ)] [HasMapBifunctor K₁' K₂ G (ComplexShape.up ℤ)] :
    QuasiIso (mapBifunctorMap ψ (𝟙 K₂) G (ComplexShape.up ℤ)) := by
  have : G.flip.Additive := { }
  have (X : C₂) : (G.flip.obj X).Additive := { }
  have hflip := quasiIso_mapBifunctorMap_right G.flip K₂ ψ hG b a h₂ h₁ h₁'
  have hnat := mapBifunctorFlipIso_hom_naturality (φ₁ := ψ) (φ₂ := 𝟙 K₂) (F := G)
    (c := ComplexShape.up ℤ)
  have : QuasiIso (mapBifunctorMap (𝟙 K₂) ψ G.flip (ComplexShape.up ℤ) ≫
      (mapBifunctorFlipIso K₁' K₂ G (ComplexShape.up ℤ)).hom) := inferInstance
  rw [hnat] at this
  exact (quasiIso_iff_comp_left _ _).1 this

/-- Cohomology is invariant under a quasi-isomorphism: a quasi-isomorphism `K ⟶ L` makes
`Hⁱ(K)` vanish exactly when `Hⁱ(L)` does. -/
lemma isZero_homology_iff_of_quasiIso {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f] (i : ℤ) :
    IsZero (K.homology i) ↔ IsZero (L.homology i) := by
  have : IsIso (homologyMap f i) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact ⟨fun h => h.of_iso (asIso (homologyMap f i)).symm,
    fun h => h.of_iso (asIso (homologyMap f i))⟩

end Total

/-! ### Finitely many columns -/

section Columns

open HomologicalComplex

variable {C₁ C₂ E : Type*} [Category* C₁] [Category* C₂] [Category* E]
  [Abelian C₁] [Abelian C₂] [Abelian E] (G : C₁ ⥤ C₂ ⥤ E) [G.Additive]
  [∀ X, (G.obj X).Additive]

/-- The double complex of a bifunctor applied to a complex with finitely many nonzero terms has
finitely many nonzero columns, hence a total complex. -/
lemma hasMapBifunctor_of_bounds (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (a b : ℤ)
    (h : ∀ p, p < a ∨ b < p → IsZero (K₁.X p)) :
    HasMapBifunctor K₁ K₂ G (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_columnBounds _ a b fun p hp =>
    isZero_mapBifunctorHomologicalComplex_obj_obj_X G K₁ K₂ (h p hp)

/-- A double complex vanishing in first degrees `> a` and in second degrees `> b` has a total
complex: in each total degree `n` only the first degrees in `[n - b, a]` contribute. -/
lemma hasMapBifunctor_of_upperBounds (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
    (a b : ℤ) (h₁ : ∀ p, a < p → IsZero (K₁.X p)) (h₂ : ∀ q, b < q → IsZero (K₂.X q)) :
    HasMapBifunctor K₁ K₂ G (ComplexShape.up ℤ) := by
  apply HomologicalComplex₂.hasTotal_of_finite
  intro n
  refine Set.Finite.subset ((Set.finite_Icc (n - b) a).image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  refine ⟨p, ⟨?_, ?_⟩, by simp only [Prod.mk.injEq, true_and]; omega⟩
  · by_contra hp
    exact hz ((G.obj (K₁.X p)).map_isZero (h₂ q (by omega)))
  · by_contra hp
    exact hz ((G.map_isZero (h₁ p (by omega))).obj (K₂.X q))

/-- **A morphism in the second variable which is a quasi-isomorphism induces a quasi-isomorphism
of total complexes when the first complex has finitely many nonzero terms**, at each of which the
bifunctor preserves homology. -/
lemma quasiIso_mapBifunctorMap_right_of_bounds (K₁ : CochainComplex C₁ ℤ)
    {K₂ K₂' : CochainComplex C₂ ℤ} (φ : K₂ ⟶ K₂') [QuasiIso φ]
    (hG : ∀ p, (G.obj (K₁.X p)).PreservesHomology) (a b : ℤ)
    (h : ∀ p, p < a ∨ b < p → IsZero (K₁.X p))
    [HasMapBifunctor K₁ K₂ G (ComplexShape.up ℤ)] [HasMapBifunctor K₁ K₂' G (ComplexShape.up ℤ)] :
    QuasiIso (mapBifunctorMap (𝟙 K₁) φ G (ComplexShape.up ℤ)) := by
  unfold mapBifunctorMap
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_columnBounds (b + 1 - a).toNat
    _ a b (by omega) (fun p hp => isZero_mapBifunctorHomologicalComplex_obj_obj_X G K₁ K₂ (h p hp))
    (fun p hp => isZero_mapBifunctorHomologicalComplex_obj_obj_X G K₁ K₂' (h p hp)) fun p => ?_
  exact quasiIso_mapBifunctorHomologicalComplex_map_f G K₁ φ (hG p)

end Columns

/-! ### Homology isomorphisms from isomorphisms in three degrees -/

section ThreeDegrees

open HomologicalComplex

/-- A morphism of cochain complexes which is an isomorphism in the degrees `i - 1`, `i` and
`i + 1` is an isomorphism on `Hⁱ`. -/
lemma isIso_homologyMap_of_isIso_f {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (i : ℤ) [IsIso (f.f (i - 1))] [IsIso (f.f i)]
    [IsIso (f.f (i + 1))] : IsIso (homologyMap f i) := by
  have h₁ : (ComplexShape.up ℤ).prev i = i - 1 := by simp
  have h₃ : (ComplexShape.up ℤ).next i = i + 1 := by simp
  have : IsIso ((shortComplexFunctor A (ComplexShape.up ℤ) i).map f).τ₁ := by
    show IsIso (f.f ((ComplexShape.up ℤ).prev i))
    rw [h₁]; infer_instance
  have : IsIso ((shortComplexFunctor A (ComplexShape.up ℤ) i).map f).τ₂ := by
    show IsIso (f.f i); infer_instance
  have : IsIso ((shortComplexFunctor A (ComplexShape.up ℤ) i).map f).τ₃ := by
    show IsIso (f.f ((ComplexShape.up ℤ).next i))
    rw [h₃]; infer_instance
  have := ShortComplex.isIso_of_isIso ((shortComplexFunctor A (ComplexShape.up ℤ) i).map f)
  show IsIso (ShortComplex.homologyMap ((shortComplexFunctor A (ComplexShape.up ℤ) i).map f))
  infer_instance

/-- A morphism of cochain complexes which is an isomorphism in the degrees `i - 1`, `i` and
`i + 1` makes `Hⁱ` of the source vanish exactly when `Hⁱ` of the target does. -/
private lemma isZero_homology_iff_of_isIso_f {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (i : ℤ) [IsIso (f.f (i - 1))] [IsIso (f.f i)]
    [IsIso (f.f (i + 1))] : IsZero (K.homology i) ↔ IsZero (L.homology i) := by
  have := isIso_homologyMap_of_isIso_f f i
  exact ⟨fun h => h.of_iso (asIso (homologyMap f i)).symm,
    fun h => h.of_iso (asIso (homologyMap f i))⟩

end ThreeDegrees


/-! ### The projectivity criterion with finite test modules -/

section Projective

open HomologicalComplex

/-- **A finitely generated module is projective when tensoring a free presentation of it with
every finite right module stays exact.** This is the projectivity criterion of the proof of
Tag 03TO (`StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_finite_homology`), whose
only test module is finite as soon as the ring is: it is a quotient of the dual of a finite free
module. -/
lemma projective_cokernel_of_finite_tensor_exact {Λ : Type u} [Ring Λ] [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (S : ShortComplex (ModuleCat.{v} Λ))
    [Module.Finite Λ S.X₁] [Module.Free Λ S.X₁]
    [Module.Finite Λ S.X₂] [Module.Free Λ S.X₂]
    [Module.Finite Λ S.X₃] [Module.Free Λ S.X₃]
    [Finite Λ]
    (hex : ∀ (N : ModuleCat.{v} Λᵐᵒᵖ), Finite N → ∀ (x : (D.ordinary.obj N).obj S.X₂),
      (D.ordinary.obj N).map S.g x = 0 → ∃ y, (D.ordinary.obj N).map S.f y = x) :
    Module.Projective Λ (cokernel S.g : ModuleCat.{v} Λ) := by
  classical
  let bA := Module.Free.chooseBasis Λ S.X₂
  let bB := Module.Free.chooseBasis Λ S.X₃
  let bC := Module.Free.chooseBasis Λ S.X₁
  let V := LinearMap.range (LinearMap.lcomp Λᵐᵒᵖ Λ S.g.hom)
  have : Small.{v} (S.X₂ →ₗ[Λ] Λ) := small_of_injective DFunLike.coe_injective
  have : Small.{v} ((S.X₂ →ₗ[Λ] Λ) ⧸ V) := inferInstance
  let N := ModuleCat.of Λᵐᵒᵖ (Shrink.{v} ((S.X₂ →ₗ[Λ] Λ) ⧸ V))
  let q : (S.X₂ →ₗ[Λ] Λ) →ₗ[Λᵐᵒᵖ] N :=
    (Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm.toLinearMap.comp V.mkQ
  have hq_surj : Function.Surjective q :=
    (Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm.surjective.comp
      (Submodule.mkQ_surjective V)
  have hq_zero (φ : S.X₃ →ₗ[Λ] Λ) : q (φ.comp S.g.hom) = 0 := by
    have hv : V.mkQ (φ.comp S.g.hom) = 0 :=
      (Submodule.Quotient.mk_eq_zero V).2 ⟨φ, rfl⟩
    show (Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm
      (V.mkQ (φ.comp S.g.hom)) = 0
    rw [hv, map_zero]
  obtain ⟨cA, hcA, hrA⟩ := exists_tensor_coordinates D N S.X₂ bA
  obtain ⟨cB, hcB, hrB⟩ := exists_tensor_coordinates D N S.X₃ bB
  obtain ⟨cC, hcC, hrC⟩ := exists_tensor_coordinates D N S.X₁ bC
  let x := ∑ i, D.pure N S.X₂ (q (bA.coord i)) (bA i)
  have hx : (D.ordinary.obj N).map S.g x = 0 := by
    have hz : cB ((D.ordinary.obj N).map S.g x) = 0 := by
      funext j
      show cB ((D.ordinary.obj N).map S.g (∑ i, _)) j = 0
      simp +instances only [_root_.map_sum, Finset.sum_apply, D.natural_right, hcB]
      calc
        _ = q (∑ i, MulOpposite.op (bB.repr (S.g (bA i)) j) • bA.coord i) := by
          simp +instances
        _ = 0 := by
          show q (∑ i, MulOpposite.op (((bB.coord j).comp S.g.hom) (bA i)) •
            bA.coord i) = 0
          rw [sum_dual_basis]
          exact hq_zero _
    rw [← hrB ((D.ordinary.obj N).map S.g x), hz]
    simp
  have hfinN : Finite N := by
    have : Finite (S.X₂ →ₗ[Λ] Λ) :=
      Finite.of_injective (fun φ : S.X₂ →ₗ[Λ] Λ => fun i => φ (bA i))
        fun φ ψ h => bA.ext fun i => congrFun h i
    have : Finite ((S.X₂ →ₗ[Λ] Λ) ⧸ V) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective V)
    show Finite (Shrink.{v} ((S.X₂ →ₗ[Λ] Λ) ⧸ V))
    exact Finite.of_equiv _ (equivShrink.{v} ((S.X₂ →ₗ[Λ] Λ) ⧸ V))
  obtain ⟨y, hy⟩ := hex N hfinN x hx
  choose φ hφ using fun l => hq_surj (cC y l)
  let h : S.X₂ →ₗ[Λ] S.X₁ := ∑ l, (φ l).smulRight (bC l)
  have hycoord (i : Module.Free.ChooseBasisIndex Λ S.X₂) :
      q (bA.coord i) = q ((bA.coord i).comp (S.f.hom.comp h)) := by
    have he := congrArg (fun t => cA t i) hy
    rw [← hrC y] at he
    simp +instances only [_root_.map_sum, Finset.sum_apply, D.natural_right, hcA] at he
    have hxi : cA x i = q (bA.coord i) := by
      simp +instances only [_root_.map_sum, Finset.sum_apply, hcA, Module.Basis.repr_self,
        Finsupp.single_apply, apply_ite, MulOpposite.op_one, MulOpposite.op_zero, ite_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, x]
      exact one_smul Λᵐᵒᵖ _
    rw [hxi] at he
    rw [← he]
    simp +instances only [← hφ, ← _root_.map_smul, ← _root_.map_sum]
    congr 1
    ext a
    simp +instances [h, LinearMap.sum_apply, _root_.map_sum, _root_.map_smul,
      MulOpposite.smul_eq_mul_unop]
  have hmem (i : Module.Free.ChooseBasisIndex Λ S.X₂) :
      bA.coord i - (bA.coord i).comp (S.f.hom.comp h) ∈ V := by
    refine (Submodule.Quotient.mk_eq_zero V).1
      ((Shrink.linearEquiv.{v} Λᵐᵒᵖ ((S.X₂ →ₗ[Λ] Λ) ⧸ V)).symm.injective ?_)
    rw [map_zero]
    show q _ = 0
    rw [_root_.map_sub, hycoord, sub_self]
  choose ψ hψ using hmem
  let s : S.X₃ →ₗ[Λ] S.X₂ := ∑ i, (ψ i).smulRight (bA i)
  have hs (a : S.X₂) : s (S.g a) = a - S.f (h a) := by
    show (∑ i, (ψ i).smulRight (bA i)) (S.g a) = _
    simp +instances only [LinearMap.sum_apply, LinearMap.smulRight_apply]
    have hψ' (i : Module.Free.ChooseBasisIndex Λ S.X₂) :
        ψ i (S.g a) = bA.repr a i - bA.repr (S.f (h a)) i :=
      LinearMap.congr_fun (hψ i) a
    simp +instances only [hψ', sub_smul, Finset.sum_sub_distrib, bA.sum_repr]
  let s' : S.X₃ ⟶ S.X₂ := ModuleCat.ofHom s
  have hgs : S.g ≫ s' ≫ S.g = S.g := by
    ext a
    show S.g (s (S.g a)) = S.g a
    rw [hs, _root_.map_sub]
    have hz : S.g (S.f (h a)) = 0 :=
      congrArg (fun f : S.X₁ ⟶ S.X₃ => f (h a)) S.zero
    rw [hz, sub_zero]
  let i : cokernel S.g ⟶ S.X₃ := cokernel.desc S.g (𝟙 S.X₃ - s' ≫ S.g) (by
    simp +instances only [Preadditive.comp_sub, hgs, Category.comp_id, sub_self])
  have hi : i ≫ cokernel.π S.g = 𝟙 _ := by
    apply (cancel_epi (cokernel.π S.g)).1
    dsimp +instances [i]
    simp +instances [Preadditive.sub_comp, Category.id_comp]
  exact Module.Projective.of_split i.hom (cokernel.π S.g).hom
    (by simpa using congrArg ModuleCat.Hom.hom hi)

end Projective

/-! ### Finite Tor dimension from the vanishing of total complexes -/

section Criterion

open HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

variable {Λ : Type u} [Ring Λ]

/-- The morphism of complexes underlying an isomorphism of the derived category out of a
K-projective complex. -/
private lemma exists_quasiIso_of_isKProjective {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (P L : CochainComplex A ℤ) [P.IsKProjective]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj L) :
    ∃ f : P ⟶ L, QuasiIso f := by
  obtain ⟨m, hm⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app P ≫ e.hom ≫
      (DerivedCategory.quotientCompQhIso A).inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective m
  refine ⟨f, ?_⟩
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have h1 := (DerivedCategory.quotientCompQhIso A).hom.naturality f
  simp only [Functor.comp_map] at h1
  have : DerivedCategory.Q.map f = (DerivedCategory.quotientCompQhIso A).inv.app P ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app L := by
    rw [h1, Iso.inv_hom_id_app_assoc]
  rw [this, hm]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc]
  infer_instance

/-- **The degree `-1` Tor criterion.** Let `F` be a bounded above complex of finite free left
`Λ`-modules over a finite ring `Λ` and let `φ : F ⟶ L` be a quasi-isomorphism. If, for every
complex `R` of finite free right `Λ`-modules concentrated in degrees `[e, c]` with `e + w ≤ i` and
exact in the degrees `p > e` other than `0`, the total complex `Tot(R ⊗[Λ] L)` has no cohomology
in degree `i`, then `Hⁱ(N ⊗[Λ] F) = 0` for every finite right `Λ`-module `N`. Indeed a finite
free resolution `R` of `N`, truncated far enough below, computes `Hⁱ(N ⊗ F)` as
`Hⁱ(Tot(R ⊗ F))`, and `Tot(R ⊗ F) ⟶ Tot(R ⊗ L)` is a quasi-isomorphism, the terms of `R` and
of `F` being flat. -/
lemma isZero_homology_ordinary_of_isZero_homology_mapBifunctor [Finite Λ] [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) {F L : CochainComplex (ModuleCat.{v} Λ) ℤ}
    (φ : F ⟶ L) [QuasiIso φ] (b : ℤ) (hF : ∀ q, b < q → IsZero (F.X q))
    (hFfree : ∀ q, Module.Finite Λ (F.X q) ∧ Module.Free Λ (F.X q)) (i w : ℤ)
    (htor : ∀ (R : CochainComplex (ModuleCat.{v} (MulOpposite Λ)) ℤ) (e c : ℤ),
      (∀ p, p < e ∨ c < p → IsZero (R.X p)) →
      (∀ p, Module.Finite (MulOpposite Λ) (R.X p) ∧ Module.Free (MulOpposite Λ) (R.X p)) →
      (∀ p, e < p → p ≠ 0 → R.ExactAt p) → e + w ≤ i →
      ∀ (_ : HasMapBifunctor R L D.ordinary (ComplexShape.up ℤ)),
      IsZero ((mapBifunctor R L D.ordinary (ComplexShape.up ℤ)).homology i))
    (N : ModuleCat.{v} (MulOpposite Λ)) [Finite N] :
    IsZero ((((D.ordinary.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).homology i) := by
  have hFfree' (q : ℤ) : (D.ordinary.flip.obj (F.X q)).PreservesHomology := by
    obtain ⟨_, _⟩ := hFfree q
    exact preservesHomology_ordinary_flip_obj_of_free D (F.X q)
  have : Finite (MulOpposite Λ) := Finite.of_equiv _ MulOpposite.opEquiv
  have : IsNoetherianRing (MulOpposite Λ) := isNoetherian_of_finite _ _
  have : Small.{v} (MulOpposite Λ) := small_of_injective MulOpposite.unop_injective
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} (MulOpposite Λ)) 0).obj N
  let eK : K ≅ DerivedCategory.Q.obj ((single _ (ComplexShape.up ℤ) 0).obj N) :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app N
  have hKz (j : ℤ) (hj : j ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} (MulOpposite Λ)) j).obj K) :=
    (isZero_single_obj_homology _ 0 N j hj).of_iso
      ((DerivedCategory.homologyFunctor _ j).mapIso eK ≪≫
        (DerivedCategory.homologyFunctorFactors _ j).app _)
  let eK0 : (DerivedCategory.homologyFunctor (ModuleCat.{v} (MulOpposite Λ)) 0).obj K ≅ N :=
    (DerivedCategory.homologyFunctor _ 0).mapIso eK ≪≫
      (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫ singleObjHomologySelfIso _ 0 N
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
    refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology K 0
      (PUnit : Type v)).2.1.mpr ⟨⟨0, fun j hj => hKz j (by omega)⟩, fun j => ?_⟩
    by_cases hj : j = 0
    · subst hj
      have : Finite ((DerivedCategory.homologyFunctor (ModuleCat.{v} (MulOpposite Λ)) 0).obj K) :=
        Finite.of_equiv _ eK0.toLinearEquiv.toEquiv.symm
      exact Module.Finite.of_finite
    · have : Subsingleton
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} (MulOpposite Λ)) j).obj K) :=
        ModuleCat.isZero_iff_subsingleton.mp (hKz j hj)
      exact Module.Finite.of_finite
  obtain ⟨R, hR, ⟨eR⟩⟩ := hpc
  obtain ⟨c, hc⟩ := hR.upperBound
  have hRfree (p : ℤ) :
      Module.Finite (MulOpposite Λ) (R.X p) ∧ Module.Free (MulOpposite Λ) (R.X p) :=
    hR.finiteFree p
  have hRz (j : ℤ) (hj : j ≠ 0) : IsZero (R.homology j) :=
    (hKz j hj).of_iso (((DerivedCategory.homologyFunctorFactors _ j).app R).symm ≪≫
      (DerivedCategory.homologyFunctor _ j).mapIso eR)
  have hRexact (p : ℤ) (hp : p ≠ 0) : R.ExactAt p :=
    (exactAt_iff_isZero_homology R p).2 (hRz p hp)
  have hRF (p : ℤ) : (D.ordinary.obj (R.X p)).PreservesHomology := by
    obtain ⟨_, _⟩ := hRfree p
    exact preservesHomology_ordinary_obj_of_free D (R.X p)
  have hRc : ∀ p, c < p → IsZero (R.X p) := fun p hp => R.isZero_of_isStrictlyLE c p hp
  let e : ℤ := min (i - b - 2) (i - w)
  let σR := R.stupidTrunc (ComplexShape.embeddingUpIntGE e)
  have hσf {p : ℤ} (hp : e ≤ p) : (ComplexShape.embeddingUpIntGE e).f (p - e).toNat = p := by
    show e + ((p - e).toNat : ℤ) = p
    omega
  let eσ {p : ℤ} (hp : e ≤ p) : σR.X p ≅ R.X p := R.stupidTruncXIso _ (hσf hp)
  have hσz (p : ℤ) (hp : p < e) : IsZero (σR.X p) :=
    R.isZero_stupidTrunc_X _ p (by
      intro k hk
      change e + (k : ℤ) = p at hk
      omega)
  have hσbounds : ∀ p, p < e ∨ c < p → IsZero (σR.X p) := by
    rintro p (hp | hp)
    · exact hσz p hp
    · by_cases hpe : p < e
      · exact hσz p hpe
      · exact (hRc p hp).of_iso (eσ (by omega))
  have hσfree (p : ℤ) :
      Module.Finite (MulOpposite Λ) (σR.X p) ∧ Module.Free (MulOpposite Λ) (σR.X p) := by
    by_cases hp : p < e
    · have : Subsingleton (σR.X p) := ModuleCat.isZero_iff_subsingleton.mp (hσz p hp)
      exact ⟨inferInstance, inferInstance⟩
    · have := (hRfree p).1
      have := (hRfree p).2
      exact ⟨Module.Finite.equiv (eσ (by omega)).symm.toLinearEquiv,
        Module.Free.of_equiv (eσ (by omega)).symm.toLinearEquiv⟩
  have hιiso {p : ℤ} (hp : e ≤ p) : IsIso ((R.ιStupidTrunc
      (ComplexShape.embeddingUpIntGE e)).f p) :=
    R.isIso_ιStupidTrunc_f _ (hσf hp)
  have hσexact (p : ℤ) (hp : e < p) (hp0 : p ≠ 0) : σR.ExactAt p := by
    have := hιiso (p := p - 1) (by omega)
    have := hιiso (p := p) (by omega)
    have := hιiso (p := p + 1) (by omega)
    exact (exactAt_iff_isZero_homology σR p).2
      ((isZero_homology_iff_of_isIso_f (R.ιStupidTrunc (ComplexShape.embeddingUpIntGE e)) p).2
        ((exactAt_iff_isZero_homology R p).1 (hRexact p hp0)))
  have hσF (p : ℤ) : (D.ordinary.obj (σR.X p)).PreservesHomology := by
    obtain ⟨_, _⟩ := hσfree p
    exact preservesHomology_ordinary_obj_of_free D (σR.X p)
  have : HasMapBifunctor σR L D.ordinary (ComplexShape.up ℤ) :=
    hasMapBifunctor_of_bounds D.ordinary σR L e c hσbounds
  have : HasMapBifunctor σR F D.ordinary (ComplexShape.up ℤ) :=
    hasMapBifunctor_of_bounds D.ordinary σR F e c hσbounds
  have : HasMapBifunctor R F D.ordinary (ComplexShape.up ℤ) :=
    hasMapBifunctor_of_upperBounds D.ordinary R F c b hRc hF
  have h₀ : IsZero ((mapBifunctor σR F D.ordinary (ComplexShape.up ℤ)).homology i) := by
    have := quasiIso_mapBifunctorMap_right_of_bounds D.ordinary σR φ hσF e c hσbounds
    exact (isZero_homology_iff_of_quasiIso (mapBifunctorMap (𝟙 σR) φ D.ordinary
      (ComplexShape.up ℤ)) i).2
        (htor σR e c hσbounds hσfree hσexact (by omega) inferInstance)
  have hcomp (n : ℤ) (hn : i - 1 ≤ n) : IsIso ((mapBifunctorMap
      (R.ιStupidTrunc (ComplexShape.embeddingUpIntGE e)) (𝟙 F) D.ordinary
        (ComplexShape.up ℤ)).f n) := by
    unfold mapBifunctorMap
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    refine StacksDraft.TotalComplexQuasiIso.isIso_total_map_f _ n (fun p q hpq => ?_)
    simp only [Functor.mapBifunctorHomologicalComplex_map_app_f_f]
    by_cases hp : e ≤ p
    · have := hιiso hp
      exact (NatIso.isIso_app_of_isIso
        (D.ordinary.map ((R.ιStupidTrunc (ComplexShape.embeddingUpIntGE e)).f p)) (F.X q))
    · have hq : IsZero (F.X q) := hF q (by omega)
      exact ⟨0, ((D.ordinary.obj _).map_isZero hq).eq_of_src _ _,
        ((D.ordinary.obj _).map_isZero hq).eq_of_src _ _⟩
  have h₁ : IsZero ((mapBifunctor R F D.ordinary (ComplexShape.up ℤ)).homology i) := by
    have := hcomp (i - 1) le_rfl
    have := hcomp i (by omega)
    have := hcomp (i + 1) (by omega)
    exact (isZero_homology_iff_of_isIso_f (mapBifunctorMap
      (R.ιStupidTrunc (ComplexShape.embeddingUpIntGE e)) (𝟙 F) D.ordinary
        (ComplexShape.up ℤ)) i).1 h₀
  let T := R.truncLE 0
  have hT0 : ∀ p, 0 < p → IsZero (T.X p) := fun p hp => T.isZero_of_isStrictlyLE 0 p hp
  have hTc : ∀ p, max c 0 < p → IsZero (T.X p) := fun p hp => hT0 p (by omega)
  have hRc' : ∀ p, max c 0 < p → IsZero (R.X p) := fun p hp => hRc p (by omega)
  have : R.IsLE 0 := by
    rw [CochainComplex.isLE_iff]
    intro p hp
    exact hRexact p (by omega)
  have : HasMapBifunctor T F D.ordinary (ComplexShape.up ℤ) :=
    hasMapBifunctor_of_upperBounds D.ordinary T F (max c 0) b hTc hF
  have h₂ : IsZero ((mapBifunctor T F D.ordinary (ComplexShape.up ℤ)).homology i) := by
    have := quasiIso_mapBifunctorMap_left D.ordinary (R.ιTruncLE 0) F hFfree' (max c 0) b hTc
      hRc' hF
    exact (isZero_homology_iff_of_quasiIso (mapBifunctorMap (R.ιTruncLE 0) (𝟙 F) D.ordinary
      (ComplexShape.up ℤ)) i).2 h₁
  have : T.IsGE 0 := by
    rw [CochainComplex.isGE_iff]
    intro p hp
    have := (R.quasiIsoAt_ιTruncLE 0 p (by omega))
    exact (exactAt_iff_of_quasiIsoAt (R.ιTruncLE 0) p).2 (hRexact p (by omega))
  let U := T.truncGE 0
  have : U.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro p hp
    exact (hT0 p hp).of_iso (T.truncGEXIso 0 p hp)
  obtain ⟨M, ⟨eU⟩⟩ := CochainComplex.exists_iso_single U 0
  have hUc : ∀ p, max c 0 < p → IsZero (U.X p) := fun p hp =>
    U.isZero_of_isStrictlyLE 0 p (by omega)
  have : HasMapBifunctor U F D.ordinary (ComplexShape.up ℤ) :=
    hasMapBifunctor_of_upperBounds D.ordinary U F (max c 0) b hUc hF
  have hSc : ∀ p, max c 0 < p → IsZero (((single _ (ComplexShape.up ℤ) 0).obj M).X p) :=
    fun p hp => isZero_single_obj_X _ 0 M p (by omega)
  have : HasMapBifunctor ((single _ (ComplexShape.up ℤ) 0).obj M) F D.ordinary
      (ComplexShape.up ℤ) :=
    hasMapBifunctor_of_upperBounds D.ordinary _ F (max c 0) b hSc hF
  have h₃ : IsZero ((mapBifunctor ((single _ (ComplexShape.up ℤ) 0).obj M) F D.ordinary
      (ComplexShape.up ℤ)).homology i) := by
    have h₃₁ := quasiIso_mapBifunctorMap_left D.ordinary (T.πTruncGE 0) F hFfree' (max c 0) b
      hTc hUc hF
    have h₃₂ := quasiIso_mapBifunctorMap_left D.ordinary eU.hom F hFfree' (max c 0) b
      hUc hSc hF
    exact (isZero_homology_iff_of_quasiIso (mapBifunctorMap eU.hom (𝟙 F) D.ordinary
      (ComplexShape.up ℤ)) i).1 ((isZero_homology_iff_of_quasiIso (mapBifunctorMap (T.πTruncGE 0)
        (𝟙 F) D.ordinary (ComplexShape.up ℤ)) i).1 h₂)
  have h₄ : IsZero ((((D.ordinary.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).homology
      i) :=
    h₃.of_iso ((homologyFunctor _ _ i).mapIso (singleLeftIsoMapBifunctor D.ordinary M F))
  have : QuasiIso (T.πTruncGE 0) := inferInstance
  let eD : DerivedCategory.Q.obj ((single _ (ComplexShape.up ℤ) 0).obj M) ≅ K :=
    DerivedCategory.Q.mapIso eU.symm ≪≫ (asIso (DerivedCategory.Q.map (T.πTruncGE 0))).symm ≪≫
      asIso (DerivedCategory.Q.map (R.ιTruncLE 0)) ≪≫ eR
  let eM : M ≅ N := (singleObjHomologySelfIso _ 0 M).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors _ 0).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso eD ≪≫ eK0
  exact h₄.of_iso ((homologyFunctor _ _ i).mapIso
    ((NatIso.mapHomologicalComplex (D.ordinary.mapIso eM.symm) (ComplexShape.up ℤ)).app F))

/-- **Perfectness from the vanishing of total complexes.** Let `Λ` be a finite ring, not
necessarily commutative, and let `L` be a complex of left `Λ`-modules with finite cohomology
modules, vanishing in degrees `< a` and `> d`. Suppose that for every complex `R` of finite free
right `Λ`-modules concentrated in degrees `[e, c]` with `e + w ≤ a - 1`, exact in the degrees
`p > e` other than `0` — a truncated finite free resolution of the finite right module `H⁰(R)` —
the total complex `Tot(R ⊗[Λ] L)` has no cohomology in degree `a - 1`. Then `L` is a perfect
complex.

This is the criterion of Tag 03TO (`StacksDraft.Perfect.isPerfect_iff_hasFiniteTorDimension_and_
finite_homology`) with the Tor-dimension input read off resolutions of the finite right modules:
`L` is pseudo-coherent, so it is represented by a bounded above complex `F` of finite free
modules; `H^{a-1}(N ⊗ F) = 0` for every finite right module `N`
(`isZero_homology_ordinary_of_isZero_homology_mapBifunctor`), so the cokernel of
`F^{a-1} ⟶ F^a` is projective (`projective_cokernel_of_finite_tensor_exact`), and the truncation
of `F` in degrees `≥ a` is a bounded complex of finite projective modules representing `L`. -/
theorem isPerfect_of_isZero_homology_mapBifunctor [Finite Λ] [Small.{v} Λ]
    (D : BalancedDerivedTensoring.{u, v} Λ) (L : CochainComplex (ModuleCat.{v} Λ) ℤ) (a d : ℤ)
    (hneg : ∀ i < a, IsZero (L.homology i)) (htop : ∀ i, d < i → IsZero (L.homology i))
    (hfin : ∀ i, Module.Finite Λ (L.homology i)) (w : ℤ)
    (htor : ∀ (R : CochainComplex (ModuleCat.{v} (MulOpposite Λ)) ℤ) (e c : ℤ),
      (∀ p, p < e ∨ c < p → IsZero (R.X p)) →
      (∀ p, Module.Finite (MulOpposite Λ) (R.X p) ∧ Module.Free (MulOpposite Λ) (R.X p)) →
      (∀ p, e < p → p ≠ 0 → R.ExactAt p) → e + w ≤ a - 1 →
      ∀ (_ : HasMapBifunctor R L D.ordinary (ComplexShape.up ℤ)),
      IsZero ((mapBifunctor R L D.ordinary (ComplexShape.up ℤ)).homology (a - 1))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj L) := by
  have : IsNoetherianRing Λ := isNoetherian_of_finite _ _
  let eH (i : ℤ) := (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} Λ) i).app L
  have hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj L) := by
    refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology _ 0
      (PUnit : Type v)).2.1.mpr ⟨⟨d, fun i hi => ?_⟩, fun i => ?_⟩
    · exact (htop i hi).of_iso (eH i)
    · let : Module.Finite Λ
          ((HomologicalComplex.homologyFunctor (ModuleCat.{v} Λ) (ComplexShape.up ℤ) i).obj L) :=
        hfin i
      exact Module.Finite.equiv (eH i).symm.toLinearEquiv
  obtain ⟨F, hF, ⟨eF⟩⟩ := hpseudo
  obtain ⟨c, hFc⟩ := hF.upperBound
  have hFfin (i : ℤ) : Module.Finite Λ (F.X i) := (hF.finiteFree i).1
  have hFfree (i : ℤ) : Module.Free Λ (F.X i) := (hF.finiteFree i).2
  have : ∀ i, Module.Projective Λ (F.X i) := fun _ => inferInstance
  have : F.IsKProjective := CochainComplex.isKProjective_of_projective F c
  obtain ⟨φ, hφ⟩ := exists_quasiIso_of_isKProjective F L eF
  have hzero (i : ℤ) (hi : i < a) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} Λ) i).obj
        (DerivedCategory.Q.obj F)) :=
    (hneg i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eF ≪≫ eH i)
  have hFge : F.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hzero i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} Λ) i).app F).symm
  have hcoker : Module.Projective Λ (cokernel (F.d (a - 1) a) : ModuleCat.{v} Λ) := by
    let S := ShortComplex.mk (F.d (a - 2) (a - 1)) (F.d (a - 1) a) (F.d_comp_d _ _ _)
    apply projective_cokernel_of_finite_tensor_exact D S
    intro N hN x hx
    let T := (D.ordinary.obj N).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj F
    have hz : IsZero (T.homology (a - 1)) :=
      isZero_homology_ordinary_of_isZero_homology_mapBifunctor D φ c
        (fun q hq => F.isZero_of_isStrictlyLE c q hq)
        (fun q => ⟨hFfin q, hFfree q⟩) (a - 1) w htor N
    have hex := (HomologicalComplex.exactAt_iff_isZero_homology T (a - 1)).mpr hz
    rw [HomologicalComplex.exactAt_iff' T (a - 2) (a - 1) a
      (by simp; omega) (by simp), ShortComplex.moduleCat_exact_iff] at hex
    exact hex x hx
  let E := F.truncGE a
  have hEc : E.IsStrictlyLE c := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have : Epi ((F.πTruncGE a).f i) := by
      unfold CochainComplex.πTruncGE
      infer_instance
    exact IsZero.of_epi ((F.πTruncGE a).f i) (F.isZero_of_isStrictlyLE c i hi)
  have hE (i : ℤ) : Module.Finite Λ (E.X i) ∧ Module.Projective Λ (E.X i) := by
    by_cases hi : i < a
    · have : Subsingleton (E.X i) := ModuleCat.isZero_iff_subsingleton.mp
        (E.isZero_of_isStrictlyGE a i hi)
      exact ⟨inferInstance, inferInstance⟩
    · rcases (le_of_not_gt hi).eq_or_lt with rfl | hai
      · let e : E.X a ≅ cokernel (F.d (a - 1) a) :=
          F.truncGEXIsoOpcycles a ≪≫
            IsColimit.coconePointUniqueUpToIso
              (F.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
        have : Module.Finite Λ (cokernel (F.d (a - 1) a) : ModuleCat.{v} Λ) :=
          Module.Finite.of_surjective (cokernel.π (F.d (a - 1) a)).hom
            ((ModuleCat.epi_iff_surjective _).mp inferInstance)
        exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
          Module.Projective.of_equiv' e.toLinearEquiv.symm⟩
      · let e : E.X i ≅ F.X i := F.truncGEXIso a i hai
        exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
          Module.Projective.of_equiv' e.toLinearEquiv.symm⟩
  exact ⟨E, a, c, inferInstance, hEc, fun i => (hE i).1, fun i => (hE i).2,
    ⟨eF.symm ≪≫ asIso (DerivedCategory.Q.map (F.πTruncGE a))⟩⟩

end Criterion

end StacksDraft.Perfect.TorTotal

end

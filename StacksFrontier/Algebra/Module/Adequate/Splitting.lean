module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksFrontier.Algebra.Module.Adequate.Laurent
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.BaseChange
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Colimits
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Kernels
import StacksCore.Tactic.StacksAttribute

/-!
# Splitting extensions of a linearly adequate functor

Let `A` be a ring. An extension

`0 → F → E → L → 0`

of module-valued functors on `Alg_A` with `L` linearly adequate splits, provided `F` commutes
with flat base change and its weight-one part on the symmetric algebra of two copies of a
finitely presented module decomposes as the direct sum of the two factor images. This is the
content of Stacks 06V7, and applying it to `F = M` for an `A`-module `M` gives Stacks 06V6: an
extension of a linearly adequate functor by a module functor is adequate.

## Main definitions

* `AdequateFunctor.HasWeightOneCoproduct`: the weight-one direct-sum decomposition.

## Main results

* `AdequateFunctor.weightOne_eq_add_images` and `AdequateFunctor.weightOne_images_disjoint`
  (Stacks 06V7): the weight-one part of an adequate functor on the symmetric algebra of two
  copies of a finitely presented module is the direct sum of the two factor images.
* `AdequateFunctor.exists_retraction_of_shortExact_of_baseChange_weightOne` (Stacks 06V7): the
  splitting.
* `AdequateFunctor.isAdequate_of_moduleExtension_shortExact` (Stacks 06V6): the middle term of
  a short exact sequence `0 → M → G → L → 0` with `L` linearly adequate is adequate.

## Implementation notes

The splitting follows the argument of Stacks 06V6: present `L` as `Hom_A(B, -)` for
`B = A[x_1, ..., x_n]/(sum a_ij x_j)`, lift the tautological element to weight one in `E`, check
additivity on the symmetric algebra of two copies, and conclude with Stacks 06V5 that the
resulting transformation is a morphism of module-valued functors. Stacks 06V7 observes that only
the two properties named above are used, which is the form proved here.

Everything is stated at the single-universe diagonal `ModuleValuedFunctor.{u, u} A`. That is the
generality at which the inputs exist: the weight-space decomposition of Stacks 06UZ and the
lifting criterion of Stacks 06V5 are proved in
`StacksFrontier.Algebra.Module.Adequate.Laurent` for `AdequateFunctor.Laurent.ModuleValuedFunctor`,
which is itself pinned to one universe. An argument through vanishing of
`Ext^1(L, F)` would give independent universes, but it needs the Ext-vanishing of Stacks 06ZG,
which the library does not have.

## References

* [Stacks Project, Tag 06V6](https://stacks.math.columbia.edu/tag/06V6)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06V5](https://stacks.math.columbia.edu/tag/06V5)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct

universe u v w

namespace AdequateFunctor


add_to_stacks 06V7 "flat base change for adequate functors"
  AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective

private lemma adequate_preservesFlatBaseChange {A : Type u} [CommRing A]
    (F : Laurent.ModuleValuedFunctor A)
    (hF : AdequateFunctor.IsAdequate (𝟭 _) F) :
    Laurent.PreservesFlatBaseChange A F := by
  intro B C _ _ _ _ f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hflat
  let ι : CommAlgCat.{u} A ⥤ CommAlgCat.{u} A := 𝟭 _
  let g : CommAlgCat.of A B ⟶ CommAlgCat.of A C := CommAlgCat.ofHom f
  let : Algebra (↑(ι.obj (CommAlgCat.of A B))) (↑(ι.obj (CommAlgCat.of A C))) :=
    (ι.map g).hom.toRingHom.toAlgebra
  let : Algebra B (↑(ι.obj (CommAlgCat.of A C))) := g.hom.toRingHom.toAlgebra
  let : Module B (↑(ι.obj (CommAlgCat.of A C))) :=
    Module.compHom _ (algebraMap B (↑(ι.obj (CommAlgCat.of A C))))
  let m := moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} ι F g
  have hg : RingHom.Flat g.hom.toRingHom := by
    rwa [RingHom.Flat, RingHom.toAlgebra]
  have hb := AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective.{u, 0, u, u, u + 1}
    ι F hF g hg
  refine ⟨LinearEquiv.ofBijective m hb, fun x => ?_⟩
  show moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} ι F g
    ((1 : ↑(ι.obj (CommAlgCat.of A C))) ⊗ₜ[↑(ι.obj (CommAlgCat.of A B))] x) =
      F.map g.op.op x
  simpa only [one_smul] using
    moduleValuedFunctorBaseChangeMap_tmul.{u, 0, u, u, u + 1} ι F g
    (1 : C) x

private lemma weightSpace_zero {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (F : Laurent.ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) ∈
      AdequateFunctor.Laurent.weightSpace A B F 𝒜 k := by
  change _ = _
  rw [(F.map _).hom.map_zero, (F.map _).hom.map_zero]
  exact smul_zero _

private lemma weightSpace_sub {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (F : Laurent.ModuleValuedFunctor A) (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (k : ℤ) {x y : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))}
    (hx : x ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 k)
    (hy : y ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 k) :
    x - y ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 k := by
  change _ = _
  rw [(F.map _).hom.map_sub, (F.map _).hom.map_sub, smul_sub]
  exact congrArg₂ (· - ·) hx hy

/-- The single-term finsupp `k ↦ x` with `x` of weight `k` has weight `j` in every degree `j`. -/
private lemma weightSpace_single_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (F : Laurent.ModuleValuedFunctor A) (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    {x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))}
    (hx : x ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 k) (j : ℤ) :
    (Finsupp.single k x : ℤ →₀ F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) j ∈
      AdequateFunctor.Laurent.weightSpace A B F 𝒜 j := by
  by_cases hj : j = k
  · simpa [hj] using hx
  · simpa [Finsupp.single_apply, Ne.symm hj] using weightSpace_zero F 𝒜 j

private lemma weightSpace_eq_zero_of_mem_two_weights
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (F : Laurent.ModuleValuedFunctor A)
    (hF : Laurent.PreservesFlatBaseChange A F)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {k l : ℤ} (hkl : k ≠ l) {x : F.obj
      (Opposite.op (Opposite.op (CommAlgCat.of A B)))}
    (hk : x ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 k)
    (hl : x ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 l) : x = 0 := by
  classical
  obtain ⟨y, -, hyuniq⟩ :=
    AdequateFunctor.Laurent.existsUnique_finsupp_weightSpace_eq A B F hF 𝒜 x
  have hyk : y = Finsupp.single k x :=
    (hyuniq (Finsupp.single k x) ⟨weightSpace_single_apply F 𝒜 k hk, by simp⟩).symm
  have hyl : y = Finsupp.single l x :=
    (hyuniq (Finsupp.single l x) ⟨weightSpace_single_apply F 𝒜 l hl, by simp⟩).symm
  simpa [Finsupp.single_eq_of_ne hkl] using congrArg (fun z : ℤ →₀ F.obj
      (Opposite.op (Opposite.op (CommAlgCat.of A B))) => z k) (hyk.symm.trans hyl)

private noncomputable def symmetricAlgebraZeroMap {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A M :=
  SymmetricAlgebra.lift (0 : M →ₗ[A] SymmetricAlgebra A M)

private noncomputable def symmetricAlgebraLaurentDegreeOneMap {A M : Type u}
    [CommRing A] [AddCommGroup M] [Module A M] :
    SymmetricAlgebra A M →ₐ[A] LaurentPolynomial (SymmetricAlgebra A M) :=
  SymmetricAlgebra.lift
    ((LinearMap.mulRight A (LaurentPolynomial.T (1 : ℤ))).comp
      ((Laurent.constantLaurentMap A (SymmetricAlgebra A M)).toLinearMap.comp
        (SymmetricAlgebra.ι A M)))

private def symmetricPower06V7 (A : Type u) (V : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] (n : ℕ) : Submodule A (SymmetricAlgebra A V) :=
  (LinearMap.range (SymmetricAlgebra.ι A V)) ^ n

private noncomputable instance symmetricPower06V7GradedMonoid (A : Type u) (V : Type u)
    [CommRing A] [AddCommGroup V] [Module A V] :
    SetLike.GradedMonoid (symmetricPower06V7 A V) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι A V))

private noncomputable def symmetricAlgebra06V7GradedInclusion (A : Type u) (V : Type u)
    [CommRing A] [AddCommGroup V] [Module A V] :
    V →ₗ[A] ⨁ n : ℕ, symmetricPower06V7 A V n :=
  DirectSum.lof A ℕ (fun n => ↥(symmetricPower06V7 A V n)) 1 ∘ₗ
    (SymmetricAlgebra.ι A V).codRestrict _ (fun x => by
      simpa only [symmetricPower06V7, pow_one] using
        LinearMap.mem_range_self (SymmetricAlgebra.ι A V) x)

private noncomputable instance symmetricAlgebra06V7GradedAlgebra (A : Type u) (V : Type u)
    [CommRing A] [AddCommGroup V] [Module A V] :
    GradedAlgebra (symmetricPower06V7 A V) :=
  GradedAlgebra.ofAlgHom _
    (SymmetricAlgebra.lift (symmetricAlgebra06V7GradedInclusion A V))
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      change (DirectSum.coeAlgHom (symmetricPower06V7 A V))
        (SymmetricAlgebra.lift (symmetricAlgebra06V7GradedInclusion A V)
          (SymmetricAlgebra.ι A V x)) = SymmetricAlgebra.ι A V x
      rw [SymmetricAlgebra.lift_ι_apply, symmetricAlgebra06V7GradedInclusion,
        LinearMap.coe_comp, Function.comp_apply, DirectSum.lof_eq_of, DirectSum.coeAlgHom_of]
      rfl)
    (fun i x => by
      obtain ⟨x, hx⟩ := x
      dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
      induction hx using Submodule.pow_induction_on_left' with
      | algebraMap r =>
          rw [AlgHom.commutes, DirectSum.algebraMap_apply]
          rfl
      | add x y i hx hy ihx ihy =>
          rw [map_add, ihx, ihy, ← map_add]
          rfl
      | mem_mul m hm i x hx ih =>
          obtain ⟨_, rfl⟩ := hm
          rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply]
          change symmetricAlgebra06V7GradedInclusion A V _ * _ = _
          simp only [symmetricAlgebra06V7GradedInclusion, LinearMap.coe_comp,
            Function.comp_apply, DirectSum.lof_eq_of]
          rw [DirectSum.of_mul_of]
          exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl))

private lemma symmetricAlgebra06V7_generator_mem_degree_one (A V : Type u)
    [CommRing A] [AddCommGroup V] [Module A V] (v : V) :
    SymmetricAlgebra.ι A V v ∈ symmetricPower06V7 A V 1 := by
  simp [symmetricPower06V7]

private lemma gradedLaurentMap_symmetricPower06V7_mem (A V : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] (d : ℕ) (x : SymmetricAlgebra A V)
    (hx : x ∈ symmetricPower06V7 A V d) :
    Laurent.gradedLaurentMap A (SymmetricAlgebra A V) (symmetricPower06V7 A V) x =
      LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ) := by
  show (DirectSum.liftRingHom _) (DirectSum.decompose (symmetricPower06V7 A V) x) = _
  rw [DirectSum.decompose_of_mem (symmetricPower06V7 A V) hx]
  simp [DirectSum.liftRingHom_apply]

private lemma moduleExtension06V7_range_weightSpace (A B N : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (d : ℕ)
    (hg : ∀ x, x ∈ 𝒜 d →
      Laurent.gradedLaurentMap A B 𝒜 x = LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ))
    (z : TensorProduct A B N)
    (hz : z ∈ LinearMap.range ((𝒜 d).subtype.rTensor N)) :
    z ∈ AdequateFunctor.Laurent.weightSpace A B
      (moduleExtension A (ModuleCat.of A N)) 𝒜 (d : ℤ) := by
  obtain ⟨w, rfl⟩ := hz
  show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
      (TensorProduct.map (Laurent.constantLaurentMap A B).toLinearMap LinearMap.id)
        ((𝒜 d).subtype.rTensor N w) =
    (TensorProduct.map (Laurent.gradedLaurentMap A B 𝒜).toLinearMap LinearMap.id)
        ((𝒜 d).subtype.rTensor N w)
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x n =>
      show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (TensorProduct.map (Laurent.constantLaurentMap A B).toLinearMap LinearMap.id
            ((x : B) ⊗ₜ[A] n)) =
        TensorProduct.map (Laurent.gradedLaurentMap A B 𝒜).toLinearMap LinearMap.id
          ((x : B) ⊗ₜ[A] n)
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
      show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (Laurent.constantLaurentMap A B (x : B) ⊗ₜ[A] n) =
        Laurent.gradedLaurentMap A B 𝒜 (x : B) ⊗ₜ[A] n
      rw [hg x.1 x.2, TensorProduct.smul_tmul', mul_comm, smul_eq_mul]
      rfl
  | add w w' hw hw' =>
      simp only [map_add, smul_add]
      rw [hw, hw']

private lemma moduleExtension06V7_preservesFlatBaseChange (A N : Type u)
    [CommRing A] [AddCommGroup N] [Module A N] :
    Laurent.PreservesFlatBaseChange A
      (moduleExtension A (ModuleCat.of A N)) := by
  intro B C _ _ _ _ f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hflat
  refine ⟨TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N, fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero =>
      show (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N)
          (1 ⊗ₜ[B] (0 : TensorProduct A B N)) =
        (TensorProduct.map f.toLinearMap LinearMap.id) 0
      simp
  | tmul b n =>
      show (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N)
          (1 ⊗ₜ[B] (b ⊗ₜ[A] n)) = f b ⊗ₜ[A] n
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      simp [Algebra.smul_def]
      rfl
  | add x y hx hy =>
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N)
          (1 ⊗ₜ[B] x) = (TensorProduct.map f.toLinearMap LinearMap.id) x at hx
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N)
          (1 ⊗ₜ[B] y) = (TensorProduct.map f.toLinearMap LinearMap.id) y at hy
      show (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N)
          (1 ⊗ₜ[B] (x + y)) = (TensorProduct.map f.toLinearMap LinearMap.id) (x + y)
      rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]

private lemma moduleExtension06V7_weightOne_mem_degreeOne (A B N : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (hg : ∀ d x, x ∈ 𝒜 d →
      Laurent.gradedLaurentMap A B 𝒜 x = LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ))
    (y : TensorProduct A B N)
    (hy : y ∈ AdequateFunctor.Laurent.weightSpace A B
      (moduleExtension A (ModuleCat.of A N)) 𝒜 1) :
    y ∈ DirectSum.decomposeTensor 𝒜 N 1 := by
  classical
  let E : ℕ → Submodule A (TensorProduct A B N) := DirectSum.decomposeTensor 𝒜 N
  let : DirectSum.Decomposition E := DirectSum.tensorDecomposition 𝒜 N
  let G : (⨁ d, E d) →+ (ℤ →₀ TensorProduct A B N) := DirectSum.toAddMonoid
    (fun d : ℕ => (Finsupp.singleAddHom (d : ℤ)).comp (E d).subtype.toAddMonoidHom)
  let w : ℤ →₀ TensorProduct A B N := G (DirectSum.decompose E y)
  have hGof (d : ℕ) (x : E d) :
      G (DirectSum.of (fun d : ℕ => E d) d x) =
        Finsupp.single (d : ℤ) (x : TensorProduct A B N) := by
    show DirectSum.toAddMonoid
      (fun e : ℕ => (Finsupp.singleAddHom (e : ℤ)).comp (E e).subtype.toAddMonoidHom)
      (DirectSum.of (fun d : ℕ => E d) d x) = _
    rw [DirectSum.toAddMonoid_of]
    rfl
  have hGval (z : ⨁ d, E d) (d : ℕ) : G z (d : ℤ) = (z d : TensorProduct A B N) := by
    induction z using DirectSum.induction_on with
    | zero => simp [G]
    | of e x =>
        rw [hGof]
        by_cases h : e = d
        · subst d
          simp
        · simp [DirectSum.of_eq_of_ne, Ne.symm h]
    | add z z' hz hz' => simp [G, hz, hz']
  have hw : ∀ k, w k ∈ AdequateFunctor.Laurent.weightSpace A B
      (moduleExtension A (ModuleCat.of A N)) 𝒜 k := by
    intro k
    by_cases hk : ∃ d : ℕ, (d : ℤ) = k
    · obtain ⟨d, rfl⟩ := hk
      have hval : w (d : ℤ) = (DirectSum.decompose E y d : TensorProduct A B N) := hGval _ _
      rw [hval]
      apply moduleExtension06V7_range_weightSpace A B N 𝒜 d (hg d)
      rw [← DirectSum.decomposeTensor_apply]
      exact (DirectSum.decompose E y d).property
    · have hGneg (z : ⨁ d, E d) : G z k = 0 := by
        induction z using DirectSum.induction_on with
        | zero => simp [G]
        | of d x =>
            rw [hGof]
            have hdk : (d : ℤ) ≠ k := fun h => hk ⟨d, h⟩
            simp [hdk]
        | add z z' hz hz' => simp [G, hz, hz']
      rw [show w k = 0 from hGneg (DirectSum.decompose E y)]
      exact weightSpace_zero _ 𝒜 k
  have hsum : w.sum (fun _ z => z) = y := by
    let S : (ℤ →₀ TensorProduct A B N) →ₗ[A] TensorProduct A B N :=
      Finsupp.lsum A (fun _ : ℤ => LinearMap.id)
    have hcomp (z : ⨁ d, E d) : S (G z) = DirectSum.coeAddMonoidHom E z := by
      induction z using DirectSum.induction_on with
      | zero => simp [G, S]
      | of d x => rw [hGof]; simp [S]
      | add z z' hz hz' => simp only [map_add, hz, hz']
    exact (hcomp (DirectSum.decompose E y)).trans
      (DirectSum.Decomposition.left_inv (ℳ := E) y)
  let w₁ : ℤ →₀ TensorProduct A B N := Finsupp.single 1 y
  have hw₁ : ∀ k, w₁ k ∈ AdequateFunctor.Laurent.weightSpace A B
      (moduleExtension A (ModuleCat.of A N)) 𝒜 k :=
    weightSpace_single_apply _ 𝒜 1 hy
  have hsum₁ : w₁.sum (fun _ z => z) = y := by simp [w₁]
  obtain ⟨_, _, huniq⟩ := AdequateFunctor.Laurent.existsUnique_finsupp_weightSpace_eq
    A B (moduleExtension A (ModuleCat.of A N))
    (moduleExtension06V7_preservesFlatBaseChange A N) 𝒜 y
  have heq : w = w₁ := (huniq w ⟨hw, hsum⟩).trans (huniq w₁ ⟨hw₁, hsum₁⟩).symm
  have hdecomp : DirectSum.decompose E y =
      DirectSum.of (fun d : ℕ => E d) 1 (DirectSum.decompose E y 1) := by
    ext d
    by_cases hd : d = 1
    · subst d
      simp
    · have hz : (Finsupp.single 1 y : ℤ →₀ TensorProduct A B N) (d : ℤ) = 0 := by
        simp [hd]
      have h := congrArg (fun z : ℤ →₀ TensorProduct A B N => z (d : ℤ)) heq
      rw [hGval, hz] at h
      have hright : (DirectSum.of (fun d : ℕ => E d) 1
          (DirectSum.decompose E y 1) : ⨁ d, E d) d = 0 := by
        simp [DirectSum.of_eq_of_ne, hd]
      rwa [hright]
  have hyval : y = (DirectSum.decompose E y 1 : TensorProduct A B N) := by
    calc
      y = DirectSum.coeAddMonoidHom E (DirectSum.decompose E y) :=
        (DirectSum.Decomposition.left_inv (ℳ := E) y).symm
      _ = DirectSum.coeAddMonoidHom (A := E)
          (DirectSum.of (fun d : ℕ => E d) 1 (DirectSum.decompose E y 1)) :=
        congrArg (DirectSum.coeAddMonoidHom (A := E)) hdecomp
      _ = (DirectSum.decompose E y 1 : TensorProduct A B N) := by
        simp only [DirectSum.coeAddMonoidHom_of]
  rw [hyval]
  exact (DirectSum.decompose E y 1).property

private noncomputable def evaluatedKernelIso06V7 {A : Type u} [CommRing A]
    {F G : Laurent.ModuleValuedFunctor A} (q : F ⟶ G)
    (X : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ) :
    (PresheafOfModules.evaluation (Laurent.algebraRingFunctor A) X).obj (kernel q) ≅
      ModuleCat.of (X.unop.unop : Type u) ((q.app X).hom.ker) := by
  let E := PresheafOfModules.evaluation (Laurent.algebraRingFunctor A) X
  have hEval : IsLimit (E.mapCone (Fork.ofι (kernel.ι q) (kernel.condition q))) :=
    isLimitOfPreserves E (kernelIsKernel q)
  have hEval' : IsLimit (KernelFork.ofι (E.map (kernel.ι q)) (by
      rw [← E.map_comp, kernel.condition, E.map_zero])) :=
    (isLimitMapConeForkEquiv' E (kernel.condition q)) hEval
  exact hEval'.conePointUniqueUpToIso (ModuleCat.kernelIsLimit (E.map q))

private lemma evaluatedKernelIso06V7_hom_comp {A : Type u} [CommRing A]
    {F G : Laurent.ModuleValuedFunctor A} (q : F ⟶ G)
    (X : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ) :
    (evaluatedKernelIso06V7 q X).hom ≫
      ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
        (PresheafOfModules.evaluation (Laurent.algebraRingFunctor A) X).map
          (kernel.ι q) := by
  let E := PresheafOfModules.evaluation (Laurent.algebraRingFunctor A) X
  let hEval' : IsLimit (KernelFork.ofι (E.map (kernel.ι q)) (by
      rw [← E.map_comp, kernel.condition, E.map_zero])) :=
    (isLimitMapConeForkEquiv' E (kernel.condition q)) <|
      isLimitOfPreserves E (kernelIsKernel q)
  have hj := IsLimit.conePointUniqueUpToIso_hom_comp hEval'
    (ModuleCat.kernelIsLimit (E.map q)) WalkingParallelPair.zero
  simp only [ModuleCat.kernelCone] at hj
  exact hj

private lemma gradedLaurentMap_symmetricAlgebra_eq_degreeOne {A M : Type u}
    [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1) :
    Laurent.gradedLaurentMap A (SymmetricAlgebra A M) 𝒜 =
      symmetricAlgebraLaurentDegreeOneMap (A := A) (M := M) := by
  apply AlgHom.ext
  intro z
  induction z using SymmetricAlgebra.induction with
  | algebraMap a => simp [symmetricAlgebraLaurentDegreeOneMap]
  | ι m =>
      show (DirectSum.liftRingHom _)
          (DirectSum.decompose 𝒜 (SymmetricAlgebra.ι A M m)) = _
      rw [DirectSum.decompose_of_mem 𝒜 (h𝒜 m)]
      simp [symmetricAlgebraLaurentDegreeOneMap, SymmetricAlgebra.lift_ι_apply,
        LinearMap.mulRight_apply]
      rfl
  | mul z₁ z₂ hz₁ hz₂ => simp [map_mul, hz₁, hz₂]
  | add z₁ z₂ hz₁ hz₂ => simp [map_add, hz₁, hz₂]

private lemma weightSpace_one_iff_symmetricPower {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M]
    (F : Laurent.ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M))))) :
    x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ↔
      x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F
        (symmetricPower06V7 A M) 1 := by
  show _ = _ ↔ _ = _
  rw [gradedLaurentMap_symmetricAlgebra_eq_degreeOne 𝒜 h𝒜,
    gradedLaurentMap_symmetricAlgebra_eq_degreeOne (symmetricPower06V7 A M)
      (symmetricAlgebra06V7_generator_mem_degree_one A M)]

private lemma tensor_symmetricAlgebra_map_degreeOne {A V W N : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [AddCommGroup N] [Module A N] (f : V →ₗ[A] W)
    (t : TensorProduct A (SymmetricAlgebra A V) N)
    (ht : t ∈ DirectSum.decomposeTensor (symmetricPower06V7 A V) N 1) :
    TensorProduct.map (SymmetricAlgebra.lift ((SymmetricAlgebra.ι A W).comp f)).toLinearMap
      LinearMap.id t ∈ DirectSum.decomposeTensor (symmetricPower06V7 A W) N 1 := by
  rw [DirectSum.decomposeTensor_apply] at ht ⊢
  obtain ⟨w, rfl⟩ := ht
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x n =>
      have hx : (x : SymmetricAlgebra A V) ∈ LinearMap.range (SymmetricAlgebra.ι A V) := by
        simpa only [symmetricPower06V7, pow_one] using x.property
      obtain ⟨v, hv⟩ := hx
      refine ⟨(⟨SymmetricAlgebra.ι A W (f v),
        symmetricAlgebra06V7_generator_mem_degree_one A W (f v)⟩ :
        symmetricPower06V7 A W 1) ⊗ₜ[A] n, ?_⟩
      simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.subtype_apply, AlgHom.toLinearMap_apply, ← hv,
        SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
  | add w w' hw hw' =>
      simpa only [map_add] using Submodule.add_mem _ hw hw'

private lemma tensor_symmetricAlgebra_factor_sum {A M N : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (t : TensorProduct A (SymmetricAlgebra A (M × M)) N)
    (ht : t ∈ DirectSum.decomposeTensor (symmetricPower06V7 A (M × M)) N 1) :
    let p₁ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    let q₁ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
    let q₂ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
    TensorProduct.map p₁.toLinearMap LinearMap.id
        (TensorProduct.map q₁.toLinearMap LinearMap.id t) +
      TensorProduct.map p₂.toLinearMap LinearMap.id
        (TensorProduct.map q₂.toLinearMap LinearMap.id t) = t := by
  intro p₁ p₂ q₁ q₂
  rw [DirectSum.decomposeTensor_apply] at ht
  obtain ⟨w, rfl⟩ := ht
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x n =>
      have hx : (x : SymmetricAlgebra A (M × M)) ∈
          LinearMap.range (SymmetricAlgebra.ι A (M × M)) := by
        simpa only [symmetricPower06V7, pow_one] using x.property
      obtain ⟨m, hm⟩ := hx
      show p₁ (q₁ (x : SymmetricAlgebra A (M × M))) ⊗ₜ[A] n +
          p₂ (q₂ (x : SymmetricAlgebra A (M × M))) ⊗ₜ[A] n =
        (x : SymmetricAlgebra A (M × M)) ⊗ₜ[A] n
      rw [← hm]
      simp only [p₁, p₂, q₁, q₂, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, ← TensorProduct.add_tmul, ← map_add]
      congr 2
      ext <;> simp
  | add w w' hw hw' =>
      simp only [map_add]
      rw [add_add_add_comm, hw, hw']

/-- A morphism of module-valued functors is semilinear over the structure ring, which on the
Laurent algebra is `LaurentPolynomial B`. Stated at that spelling of the scalars so that it can
be used against goals coming from `AdequateFunctor.Laurent.weightSpace`. -/
private lemma app_smul_laurent {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {F G : Laurent.ModuleValuedFunctor A} (η : F ⟶ G) (c : LaurentPolynomial B)
    (z : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B))))) :
    η.app (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) (c • z) =
      c • η.app (Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))) z :=
  map_smul _ _ _

private lemma weightSpace_map_iff_of_mono {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {F G : Laurent.ModuleValuedFunctor A} (η : F ⟶ G) [Mono η]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))) :
    η.app _ x ∈ AdequateFunctor.Laurent.weightSpace A B G 𝒜 k ↔
      x ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 k := by
  let Y := Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))
  have hinj : Function.Injective (η.app Y) :=
    (ModuleCat.mono_iff_injective (η.app Y)).mp inferInstance
  show _ = _ ↔ _ = _
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact ⟨fun h => hinj ((app_smul_laurent η _ _).trans h),
    fun h => (app_smul_laurent η _ _).symm.trans (congrArg _ h)⟩

private lemma weightOne_iff_tensor_degreeOne {A V N : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup N] [Module A N]
    {F : Laurent.ModuleValuedFunctor A}
    (η : F ⟶ moduleExtension A (ModuleCat.of A N)) [Mono η]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A V)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ v, SymmetricAlgebra.ι A V v ∈ 𝒜 1)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A V))))) :
    x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A V) F 𝒜 1 ↔
      η.app _ x ∈ DirectSum.decomposeTensor (symmetricPower06V7 A V) N 1 := by
  rw [weightSpace_one_iff_symmetricPower F 𝒜 h𝒜,
    ← weightSpace_map_iff_of_mono η]
  refine ⟨moduleExtension06V7_weightOne_mem_degreeOne A (SymmetricAlgebra A V) N
    (symmetricPower06V7 A V) (gradedLaurentMap_symmetricPower06V7_mem A V) _, fun hx => ?_⟩
  apply moduleExtension06V7_range_weightSpace A (SymmetricAlgebra A V) N
    (symmetricPower06V7 A V) 1 (gradedLaurentMap_symmetricPower06V7_mem A V 1)
  rwa [← DirectSum.decomposeTensor_apply]

private lemma gradedLaurentMap_comp_symmetricAlgebraZeroMap {A M : Type u}
    [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜] :
    (Laurent.gradedLaurentMap A (SymmetricAlgebra A M) 𝒜).comp
        (symmetricAlgebraZeroMap (A := A) (M := M)) =
      (Laurent.constantLaurentMap A (SymmetricAlgebra A M)).comp
        (symmetricAlgebraZeroMap (A := A) (M := M)) := by
  apply AlgHom.ext
  intro z
  induction z using SymmetricAlgebra.induction with
  | algebraMap a => simp [symmetricAlgebraZeroMap]
  | ι m => simp [symmetricAlgebraZeroMap]
  | mul z₁ z₂ hz₁ hz₂ => simp [map_mul, hz₁, hz₂]
  | add z₁ z₂ hz₁ hz₂ => simp [map_add, hz₁, hz₂]

private lemma symmetricAlgebraZeroMap_mem_weightSpace_zero {A M : Type u}
    [CommRing A] [AddCommGroup M] [Module A M]
    (F : Laurent.ModuleValuedFunctor A)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (x : F.obj (Opposite.op (Opposite.op
      (CommAlgCat.of A (SymmetricAlgebra A M))))) :
    F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M))).op.op) x ∈
      AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 0 := by
  show _ = _
  have hcomp :
      CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M)) ≫
          CommAlgCat.ofHom (Laurent.constantLaurentMap A (SymmetricAlgebra A M)) =
        CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M)) ≫
          CommAlgCat.ofHom (Laurent.gradedLaurentMap A (SymmetricAlgebra A M) 𝒜) := by
    rw [← CommAlgCat.ofHom_comp, ← CommAlgCat.ofHom_comp]
    exact congrArg CommAlgCat.ofHom
      (gradedLaurentMap_comp_symmetricAlgebraZeroMap (A := A) (M := M) 𝒜).symm
  have hmap :
      (CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M))).op.op ≫
          (CommAlgCat.ofHom (Laurent.constantLaurentMap A (SymmetricAlgebra A M))).op.op =
        (CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M))).op.op ≫
          (CommAlgCat.ofHom (Laurent.gradedLaurentMap A (SymmetricAlgebra A M) 𝒜)).op.op := by
    simpa only [← op_comp] using congrArg (fun f => f.op.op) hcomp
  rw [← F.map_comp_apply, ← F.map_comp_apply, hmap]
  exact one_smul _ _

/-- In weight one on the symmetric algebra of two copies of a finitely presented
module, every element decomposes uniquely into the two factor images. -/
public def HasWeightOneCoproduct {A : Type u} [CommRing A]
    (F : Laurent.ModuleValuedFunctor A) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ],
    (∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1) →
    (∀ m, SymmetricAlgebra.ι A (M × M) m ∈ ℬ 1) →
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ z, z ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A (M × M)) F ℬ 1 ↔
      ∃! xy : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))) ×
          F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))),
        xy.1 ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        xy.2 ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        ∃ z₁ z₂ : F.obj (Opposite.op (Opposite.op
            (CommAlgCat.of A (SymmetricAlgebra A (M × M))))),
          z₁ = F.map ((CommAlgCat.ofHom p₁).op.op) xy.1 ∧
          z₂ = F.map ((CommAlgCat.ofHom p₂).op.op) xy.2 ∧ z = z₁ + z₂

/-- The weight-one part over the symmetric algebra on two copies of a finitely
presented module is the sum of the images from each copy. -/
@[stacks 06V7 "degree-one generation by the two factors"]
public lemma weightOne_eq_add_images {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (F : Laurent.ModuleValuedFunctor A) (hF : AdequateFunctor.IsAdequate (𝟭 _) F)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1)
    (hℬ : ∀ m, SymmetricAlgebra.ι A (M × M) m ∈ ℬ 1) :
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ z, z ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A (M × M)) F ℬ 1 ↔
      ∃ x y, ∃ z₁ z₂ : F.obj (Opposite.op (Opposite.op
          (CommAlgCat.of A (SymmetricAlgebra A (M × M))))),
        x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        y ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 ∧
        z₁ = F.map ((CommAlgCat.ofHom p₁).op.op) x ∧
        z₂ = F.map ((CommAlgCat.ofHom p₂).op.op) y ∧ z = z₁ + z₂ := by
  obtain ⟨N, P, f, ⟨e⟩⟩ := (isAdequate_iff F).mp hF
  let η : F ⟶ moduleExtension A N := e.hom ≫ kernel.ι f
  have : Mono η := inferInstance
  intro p₁ p₂ z
  let q₁ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
  let q₂ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
  let X := Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))
  let Y := Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
  have hηinj : Function.Injective (η.app Y) :=
    (ModuleCat.mono_iff_injective (η.app Y)).mp inferInstance
  constructor
  · intro hz
    have ht := (weightOne_iff_tensor_degreeOne η ℬ hℬ z).mp hz
    let x : F.obj X := F.map (CommAlgCat.ofHom q₁).op.op z
    let y : F.obj X := F.map (CommAlgCat.ofHom q₂).op.op z
    have hproj (f : M × M →ₗ[A] M) :
        F.map (CommAlgCat.ofHom (SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp f))).op.op z ∈
          AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
      apply (weightOne_iff_tensor_degreeOne η 𝒜 h𝒜 _).mpr
      rw [PresheafOfModules.naturality_apply η]
      exact tensor_symmetricAlgebra_map_degreeOne f _ ht
    have hx : x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 :=
      hproj (LinearMap.fst A M M)
    have hy : y ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 :=
      hproj (LinearMap.snd A M M)
    refine ⟨x, y, F.map (CommAlgCat.ofHom p₁).op.op x,
      F.map (CommAlgCat.ofHom p₂).op.op y, hx, hy, rfl, rfl, ?_⟩
    apply hηinj
    refine Eq.trans ?_ (map_add (ConcreteCategory.hom (η.app Y))
      (F.map (CommAlgCat.ofHom p₁).op.op x) (F.map (CommAlgCat.ofHom p₂).op.op y)).symm
    show η.app Y z = η.app Y (F.map (CommAlgCat.ofHom p₁).op.op x) +
      η.app Y (F.map (CommAlgCat.ofHom p₂).op.op y)
    rw [PresheafOfModules.naturality_apply η (CommAlgCat.ofHom p₁).op.op x,
      PresheafOfModules.naturality_apply η (CommAlgCat.ofHom p₂).op.op y]
    dsimp only [x, y]
    rw [PresheafOfModules.naturality_apply η (CommAlgCat.ofHom q₁).op.op z,
      PresheafOfModules.naturality_apply η (CommAlgCat.ofHom q₂).op.op z]
    exact (tensor_symmetricAlgebra_factor_sum (η.app Y z) ht).symm
  · rintro ⟨x, y, z₁, z₂, hx, hy, rfl, rfl, rfl⟩
    have key : η.app Y (F.map (CommAlgCat.ofHom p₁).op.op x) +
        η.app Y (F.map (CommAlgCat.ofHom p₂).op.op y) ∈
        DirectSum.decomposeTensor (symmetricPower06V7 A (M × M)) (↑N) 1 := by
      simp only [PresheafOfModules.naturality_apply]
      exact Submodule.add_mem _
        (tensor_symmetricAlgebra_map_degreeOne (LinearMap.inl A M M) _
          ((weightOne_iff_tensor_degreeOne η 𝒜 h𝒜 x).mp hx))
        (tensor_symmetricAlgebra_map_degreeOne (LinearMap.inr A M M) _
          ((weightOne_iff_tensor_degreeOne η 𝒜 h𝒜 y).mp hy))
    exact (weightOne_iff_tensor_degreeOne η ℬ hℬ _).mpr
      (Eq.subst (motive := fun w => w ∈ DirectSum.decomposeTensor
          (symmetricPower06V7 A (M × M)) (↑N) 1)
        (map_add (ConcreteCategory.hom (η.app Y))
          (F.map (CommAlgCat.ofHom p₁).op.op x)
          (F.map (CommAlgCat.ofHom p₂).op.op y)).symm key)

/-- The two factor images in weight one have zero intersection. -/
@[stacks 06V7 "directness of the degree-one sum"]
public lemma weightOne_images_disjoint {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (F : Laurent.ModuleValuedFunctor A) (hF : AdequateFunctor.IsAdequate (𝟭 _) F)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1)
    (hℬ : ∀ m, SymmetricAlgebra.ι A (M × M) m ∈ ℬ 1) :
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ x y, ∀ z₁ z₂ : F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (SymmetricAlgebra A (M × M))))),
      x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 →
      y ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 →
      z₁ = F.map ((CommAlgCat.ofHom p₁).op.op) x →
      z₂ = F.map ((CommAlgCat.ofHom p₂).op.op) y → z₁ + z₂ = 0 →
        x = 0 ∧ y = 0 := by
  intro p₁ p₂ x y z₁ z₂ hx hy hz₁ hz₂ hzero
  let q₁ : SymmetricAlgebra A (M × M) →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
  let q₂ : SymmetricAlgebra A (M × M) →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
  have hq₁p₁ : q₁.comp p₁ = AlgHom.id A (SymmetricAlgebra A M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [p₁, q₁]
  have hq₁p₂ : q₁.comp p₂ = symmetricAlgebraZeroMap (A := A) (M := M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [p₂, q₁, symmetricAlgebraZeroMap]
  have hq₂p₂ : q₂.comp p₂ = AlgHom.id A (SymmetricAlgebra A M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [p₂, q₂]
  have hq₂p₁ : q₂.comp p₁ = symmetricAlgebraZeroMap (A := A) (M := M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [p₁, q₂, symmetricAlgebraZeroMap]
  have hmap {u : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M)}
      {v : SymmetricAlgebra A (M × M) →ₐ[A] SymmetricAlgebra A M}
      {w : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A M} (h : v.comp u = w)
      (a : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M))))) :
      F.map ((CommAlgCat.ofHom v).op.op) (F.map ((CommAlgCat.ofHom u).op.op) a) =
        F.map ((CommAlgCat.ofHom w).op.op) a := by
    rw [← F.map_comp_apply, ← h]
    rfl
  have hmap₁₁ := (hmap hq₁p₁ x).trans (F.presheaf.map_id_apply _ x)
  have hmap₂₂ := (hmap hq₂p₂ y).trans (F.presheaf.map_id_apply _ y)
  have hmap₁₂ := hmap hq₁p₂ y
  have hmap₂₁ := hmap hq₂p₁ x
  have hzero₁ := congrArg (fun z => F.map ((CommAlgCat.ofHom q₁).op.op) z) hzero
  rw [(F.map ((CommAlgCat.ofHom q₁).op.op)).hom.map_add,
    (F.map ((CommAlgCat.ofHom q₁).op.op)).hom.map_zero, hz₁, hz₂, hmap₁₁, hmap₁₂] at hzero₁
  have hzero₂ := congrArg (fun z => F.map ((CommAlgCat.ofHom q₂).op.op) z) hzero
  rw [(F.map ((CommAlgCat.ofHom q₂).op.op)).hom.map_add,
    (F.map ((CommAlgCat.ofHom q₂).op.op)).hom.map_zero, hz₁, hz₂, hmap₂₁, hmap₂₂] at hzero₂
  have hflat := adequate_preservesFlatBaseChange F hF
  have hnx : -x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
    simpa using weightSpace_sub F 𝒜 1 (weightSpace_zero F 𝒜 1) hx
  have hny : -y ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
    simpa using weightSpace_sub F 𝒜 1 (weightSpace_zero F 𝒜 1) hy
  have hcy_one :
      F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M))).op.op) y ∈
        AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
    rwa [eq_neg_of_add_eq_zero_right hzero₁]
  have hcx_one :
      F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M))).op.op) x ∈
        AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F 𝒜 1 := by
    rwa [eq_neg_of_add_eq_zero_left hzero₂]
  have hcy : F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M))).op.op) y = 0 :=
    weightSpace_eq_zero_of_mem_two_weights F hflat 𝒜 (by norm_num) hcy_one
      (symmetricAlgebraZeroMap_mem_weightSpace_zero F 𝒜 y)
  have hcx : F.map ((CommAlgCat.ofHom (symmetricAlgebraZeroMap (A := A) (M := M))).op.op) x = 0 :=
    weightSpace_eq_zero_of_mem_two_weights F hflat 𝒜 (by norm_num) hcx_one
      (symmetricAlgebraZeroMap_mem_weightSpace_zero F 𝒜 x)
  constructor
  · rw [hcy] at hzero₁
    exact (add_zero x).symm.trans hzero₁
  · rw [hcx] at hzero₂
    exact (zero_add y).symm.trans hzero₂

private lemma adequate_hasWeightOneCoproduct {A : Type u} [CommRing A]
    (F : Laurent.ModuleValuedFunctor A) (hF : AdequateFunctor.IsAdequate (𝟭 _) F) :
    HasWeightOneCoproduct F := by
  intro M _ _ _ 𝒜 _ ℬ _ hgenA hgenB
  let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
  let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
  dsimp [HasWeightOneCoproduct]
  intro z
  constructor
  · intro hz
    obtain ⟨x, y, _, _, hx, hy, rfl, rfl, hsum⟩ :=
      (weightOne_eq_add_images F hF 𝒜 ℬ hgenA hgenB z).mp hz
    refine ⟨(x, y), ⟨hx, hy, _, _, rfl, rfl, hsum⟩, ?_⟩
    rintro xy ⟨hx', hy', _, _, rfl, rfl, hsum'⟩
    have hmapdiff₁ : F.map ((CommAlgCat.ofHom p₁).op.op) (x - xy.1) =
        F.map ((CommAlgCat.ofHom p₁).op.op) x - F.map ((CommAlgCat.ofHom p₁).op.op) xy.1 := by
      simp only [map_sub]
    have hmapdiff₂ : F.map ((CommAlgCat.ofHom p₂).op.op) (y - xy.2) =
        F.map ((CommAlgCat.ofHom p₂).op.op) y - F.map ((CommAlgCat.ofHom p₂).op.op) xy.2 := by
      simp only [map_sub]
    let a₁ : F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (SymmetricAlgebra A (M × M))))) :=
      F.map ((CommAlgCat.ofHom p₁).op.op) x
    let a₂ : F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (SymmetricAlgebra A (M × M))))) :=
      F.map ((CommAlgCat.ofHom p₂).op.op) y
    let b₁ : F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (SymmetricAlgebra A (M × M))))) :=
      F.map ((CommAlgCat.ofHom p₁).op.op) xy.1
    let b₂ : F.obj (Opposite.op (Opposite.op
        (CommAlgCat.of A (SymmetricAlgebra A (M × M))))) :=
      F.map ((CommAlgCat.ofHom p₂).op.op) xy.2
    have hsumA : z = a₁ + a₂ := by simpa [a₁, a₂] using hsum
    have hsumB : z = b₁ + b₂ := by simpa [b₁, b₂] using hsum'
    have hzero : (a₁ - b₁) + (a₂ - b₂) = 0 := by
      rw [sub_add_sub_comm, ← hsumA, ← hsumB, sub_self]
    have hxy0 := weightOne_images_disjoint F hF 𝒜 ℬ hgenA hgenB
      (x - xy.1) (y - xy.2)
      (a₁ - b₁) (a₂ - b₂)
      (weightSpace_sub F 𝒜 1 hx hx') (weightSpace_sub F 𝒜 1 hy hy')
      hmapdiff₁.symm hmapdiff₂.symm hzero
    exact Prod.ext (sub_eq_zero.mp hxy0.1).symm (sub_eq_zero.mp hxy0.2).symm
  · rintro ⟨xy, ⟨hx, hy, z₁, z₂, hz₁, hz₂, rfl⟩, -⟩
    exact (weightOne_eq_add_images F hF 𝒜 ℬ hgenA hgenB (z₁ + z₂)).mpr
      ⟨xy.1, xy.2, z₁, z₂, hx, hy, hz₁, hz₂, rfl⟩

private lemma weightSpace_map {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {F G : Laurent.ModuleValuedFunctor A} (η : F ⟶ G)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hx : x ∈ AdequateFunctor.Laurent.weightSpace A B F 𝒜 k) :
    η.app _ x ∈ AdequateFunctor.Laurent.weightSpace A B G 𝒜 k := by
  let Y := Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))
  change _ = _ at hx ⊢
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact (app_smul_laurent η _ _).symm.trans (congrArg (η.app Y) hx)

private lemma exists_weightSpace_lift_of_epi {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {E L : Laurent.ModuleValuedFunctor A} (p : E ⟶ L) [Epi p]
    (hE : Laurent.PreservesFlatBaseChange A E)
    (hL : Laurent.PreservesFlatBaseChange A L)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (z : L.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hz : z ∈ AdequateFunctor.Laurent.weightSpace A B L 𝒜 k) :
    ∃ y, y ∈ AdequateFunctor.Laurent.weightSpace A B E 𝒜 k ∧ p.app _ y = z := by
  classical
  let X := Opposite.op (Opposite.op (CommAlgCat.of A B))
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (p.app X)).mp inferInstance z
  obtain ⟨w, hw, _⟩ := AdequateFunctor.Laurent.existsUnique_finsupp_weightSpace_eq A B E hE 𝒜 y
  let t : ℤ →₀ L.obj X := Finsupp.mapRange (p.app X).hom (map_zero _) w
  have ht : ∀ j, t j ∈ AdequateFunctor.Laurent.weightSpace A B L 𝒜 j :=
    fun j => weightSpace_map p 𝒜 j (w j) (hw.1 j)
  have htsum : t.sum (fun _ x => x) = z := by
    dsimp only [t]
    rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
    calc
      w.sum (fun _ x => (p.app X).hom x) =
          (p.app X).hom (w.sum (fun _ x => x)) := by
        simp only [Finsupp.sum, map_sum]
      _ = z := by rw [hw.2]; exact hy
  obtain ⟨_, _, huniq⟩ := AdequateFunctor.Laurent.existsUnique_finsupp_weightSpace_eq A B L hL 𝒜 z
  have heq : t = Finsupp.single k z :=
    (huniq t ⟨ht, htsum⟩).trans (huniq _ ⟨weightSpace_single_apply L 𝒜 k hz, by simp⟩).symm
  refine ⟨w k, hw.1 k, ?_⟩
  simpa only [t, Finsupp.mapRange_apply, Finsupp.single_eq_same] using
    congrArg (fun a : ℤ →₀ L.obj X => a k) heq

private noncomputable instance commRingAlgebraRingFunctorObj {A : Type u} [CommRing A]
    (X : (CommAlgCat.{u} A)ᵒᵖᵒᵖ) : CommRing ((Laurent.algebraRingFunctor A).obj X) :=
  inferInstanceAs (CommRing X.unop.unop)

private noncomputable def baseChangeEvaluation {A : Type u} [CommRing A]
    {B C : CommAlgCat.{u} A} (f : B ⟶ C) :
    PresheafOfModules.evaluation (Laurent.algebraRingFunctor A) (Opposite.op (Opposite.op B)) ⋙
      MonoidalCategory.tensorLeft
        ((ModuleCat.restrictScalars f.hom.toRingHom).obj (ModuleCat.of C C)) ⟶
    PresheafOfModules.evaluation (Laurent.algebraRingFunctor A) (Opposite.op (Opposite.op C)) ⋙
      ModuleCat.restrictScalars f.hom.toRingHom where
  app F := by
    let ι : CommAlgCat.{u} A ⥤ CommAlgCat.{u} A := 𝟭 _
    letI : Algebra B C := f.hom.toRingHom.toAlgebra
    letI : Algebra (ι.obj B) (ι.obj C) := (ι.map f).hom.toRingHom.toAlgebra
    letI : Algebra B (ι.obj C) := f.hom.toRingHom.toAlgebra
    letI : Module B (ι.obj C) := Module.compHom _ (algebraMap B (ι.obj C))
    letI : Module B (F.obj (Opposite.op (Opposite.op C))) :=
      Module.compHom _ f.hom.toRingHom
    letI : Module ((Laurent.algebraRingFunctor A).obj (Opposite.op (Opposite.op B)))
        (F.obj (Opposite.op (Opposite.op C))) :=
      Module.compHom _ f.hom.toRingHom
    letI : Module ((Laurent.algebraRingFunctor A).obj (Opposite.op (Opposite.op B)))
        ((PresheafOfModules.evaluation (Laurent.algebraRingFunctor A)
          (Opposite.op (Opposite.op C))).obj F) :=
      Module.compHom _ f.hom.toRingHom
    letI : IsScalarTower B (ι.obj C) (F.obj (Opposite.op (Opposite.op C))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact ModuleCat.ofHom
      ((moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} ι F f).restrictScalars B)
  naturality {F G} η := by
    let hι : Algebra ((𝟭 (CommAlgCat.{u} A)).obj B)
        ((𝟭 (CommAlgCat.{u} A)).obj C) :=
      ((𝟭 (CommAlgCat.{u} A)).map f).hom.toRingHom.toAlgebra
    let : Module B ((𝟭 (CommAlgCat.{u} A)).obj C) :=
      (show Module ((𝟭 (CommAlgCat.{u} A)).obj B)
        ((𝟭 (CommAlgCat.{u} A)).obj C) from hι.toModule)
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
    | tmul c x =>
      change moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} (𝟭 _) G f
          (c ⊗ₜ[B] η.app _ x) =
        η.app _ (moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} (𝟭 _) F f (c ⊗ₜ[B] x))
      let c' : (C : Type u) := c
      refine Eq.trans (moduleValuedFunctorBaseChangeMap_tmul.{u, 0, u, u, u + 1} (𝟭 _) G f c'
        (η.app (Opposite.op (Opposite.op B)) x)) ?_
      refine Eq.trans (congrArg (fun w => c' • w)
        (PresheafOfModules.naturality_apply η f.op.op x).symm) ?_
      refine Eq.trans (map_smul (ConcreteCategory.hom
        (η.app (Opposite.op (Opposite.op C)))) c' (F.map f.op.op x)).symm ?_
      exact congrArg (η.app (Opposite.op (Opposite.op C)))
        (moduleValuedFunctorBaseChangeMap_tmul.{u, 0, u, u, u + 1} (𝟭 _) F f c' x).symm

private lemma baseChangeEvaluation_isIso {A : Type u} [CommRing A]
    (F : Laurent.ModuleValuedFunctor A) (hF : Laurent.PreservesFlatBaseChange A F)
    {B C : CommAlgCat.{u} A} (f : B ⟶ C) (hf : RingHom.Flat f.hom.toRingHom) :
    IsIso ((baseChangeEvaluation f).app F) := by
  let : Algebra B C := f.hom.toRingHom.toAlgebra
  let : Module B C := Module.compHom C f.hom.toRingHom
  let ι : CommAlgCat.{u} A ⥤ CommAlgCat.{u} A := 𝟭 _
  let : Algebra B (ι.obj C) := f.hom.toRingHom.toAlgebra
  let : Module B (ι.obj C) := Module.compHom _ (algebraMap B (ι.obj C))
  let : Module C (C ⊗[B] F.obj (Opposite.op (Opposite.op B))) :=
    TensorProduct.leftModule
  let : Module (ι.obj C) C := Module.compHom C (RingHom.id C)
  have : SMulCommClass B (ι.obj C) C := inferInstanceAs (SMulCommClass B C C)
  have : SMulCommClass B ((𝟭 (CommAlgCat.{u} A)).obj C) C :=
    inferInstanceAs (SMulCommClass B C C)
  let : Module (ι.obj C) (C ⊗[B] F.obj (Opposite.op (Opposite.op B))) :=
    TensorProduct.leftModule
  let : Module (↑((𝟭 (CommAlgCat.{u} A)).obj B))
      (↑((𝟭 (CommAlgCat.{u} A)).obj C)) :=
    Module.compHom _ ((𝟭 (CommAlgCat.{u} A)).map f).hom.toRingHom
  have hflat : Module.Flat B C := hf
  obtain ⟨e, he⟩ := hF B C f.hom hflat
  let : Module B (F.obj (Opposite.op (Opposite.op C))) :=
    Module.compHom _ (algebraMap B C)
  let : IsScalarTower B C (F.obj (Opposite.op (Opposite.op C))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hm : moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} (𝟭 _) F f =
      e.toLinearMap := by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      rw [moduleValuedFunctorBaseChangeMap_tmul]
      show c • F.map f.op.op x = e (c ⊗ₜ[B] x)
      have h1 : c • ((1 : C) ⊗ₜ[B] x) = c ⊗ₜ[B] x := by
        rw [TensorProduct.smul_tmul']; simp
      refine Eq.symm (Eq.trans (congrArg e h1.symm) (Eq.trans (e.map_smul c _) ?_))
      exact congrArg _ (he x)
    | add t t' ht ht' => simp only [map_add, ht, ht']
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  show Function.Bijective (moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1}
    (𝟭 _) F f)
  rw [hm]
  exact e.bijective

private lemma preservesFlatBaseChange_of_shortExact {A : Type u} [CommRing A]
    (S : ShortComplex (Laurent.ModuleValuedFunctor A)) (hS : S.ShortExact)
    (h₁ : Laurent.PreservesFlatBaseChange A S.X₁)
    (h₃ : Laurent.PreservesFlatBaseChange A S.X₃) :
    Laurent.PreservesFlatBaseChange A S.X₂ := by
  intro B C _ _ _ _ f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hf
  let g : CommAlgCat.of A B ⟶ CommAlgCat.of A C := CommAlgCat.ofHom f
  let τ := baseChangeEvaluation g
  let T := (ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of C C)
  have : Module.Flat B T := hf
  have htop := hS.map_of_exact
    (PresheafOfModules.evaluation (Laurent.algebraRingFunctor A)
      (Opposite.op (Opposite.op (CommAlgCat.of A B))) ⋙ MonoidalCategory.tensorLeft T)
  have hbot := hS.map_of_exact
    (PresheafOfModules.evaluation (Laurent.algebraRingFunctor A)
      (Opposite.op (Opposite.op (CommAlgCat.of A C))) ⋙ ModuleCat.restrictScalars f.toRingHom)
  have hgf : RingHom.Flat g.hom.toRingHom := hf
  have hleft : IsIso (S.mapNatTrans τ).τ₁ := baseChangeEvaluation_isIso S.X₁ h₁ g hgf
  have hright : IsIso (S.mapNatTrans τ).τ₃ := baseChangeEvaluation_isIso S.X₃ h₃ g hgf
  have hmid := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (S.mapNatTrans τ) htop hbot
  have hb := (ConcreteCategory.isIso_iff_bijective ((baseChangeEvaluation g).app S.X₂)).mp hmid
  let : Algebra (↑((𝟭 (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)))
      (↑((𝟭 (CommAlgCat.{u} A)).obj (CommAlgCat.of A C))) := g.hom.toRingHom.toAlgebra
  let m := moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} (𝟭 _) S.X₂ g
  refine ⟨LinearEquiv.ofBijective m hb, fun x => ?_⟩
  show moduleValuedFunctorBaseChangeMap.{u, 0, u, u, u + 1} (𝟭 _) S.X₂ g
    ((1 : ↑((𝟭 (CommAlgCat.{u} A)).obj (CommAlgCat.of A C))) ⊗ₜ[
      ↑((𝟭 (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))] x) = _
  rw [moduleValuedFunctorBaseChangeMap_tmul]
  exact one_smul C _

private abbrev algebraValue {A : Type u} [CommRing A]
    (F : Laurent.ModuleValuedFunctor A) (B : Type u) [CommRing B] [Algebra A B] :=
  F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))

private noncomputable abbrev algebraMapValue {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : Laurent.ModuleValuedFunctor A) (f : B →ₐ[A] C) :
    algebraValue F B →ₛₗ[f.toRingHom] algebraValue F C :=
  F.restrictₛₗ ((CommAlgCat.ofHom f).op.op)

private lemma algebraMapValue_comp {A B C D : Type u} [CommRing A]
    [CommRing B] [CommRing C] [CommRing D] [Algebra A B] [Algebra A C] [Algebra A D]
    (F : Laurent.ModuleValuedFunctor A) (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (x : algebraValue F B) :
    algebraMapValue F g (algebraMapValue F f x) = algebraMapValue F (g.comp f) x :=
  (F.map_comp_apply (CommAlgCat.ofHom f).op.op (CommAlgCat.ofHom g).op.op x).symm

private lemma algebraMapValue_id {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (F : Laurent.ModuleValuedFunctor A)
    (x : algebraValue F B) : algebraMapValue F (AlgHom.id A B) x = x :=
  F.presheaf.map_id_apply _ x

private lemma algebraMapValue_naturality {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {F G : Laurent.ModuleValuedFunctor A} (η : F ⟶ G) (f : B →ₐ[A] C)
    (x : algebraValue F B) :
    (η.app (Opposite.op (Opposite.op (CommAlgCat.of A C)))).hom (algebraMapValue F f x) =
      algebraMapValue G f ((η.app (Opposite.op (Opposite.op (CommAlgCat.of A B)))).hom x) :=
  PresheafOfModules.naturality_apply η (CommAlgCat.ofHom f).op.op x

/-- `algebraMapValue_naturality` with the morphism applied through the concrete-category
coercion, which is the spelling goals produced by `PresheafOfModules` use. -/
private lemma algebraMapValue_naturality' {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {F G : Laurent.ModuleValuedFunctor A} (η : F ⟶ G) (f : B →ₐ[A] C)
    (x : algebraValue F B) :
    η.app (Opposite.op (Opposite.op (CommAlgCat.of A C))) (algebraMapValue F f x) =
      algebraMapValue G f (η.app (Opposite.op (Opposite.op (CommAlgCat.of A B))) x) :=
  algebraMapValue_naturality η f x

private noncomputable def symmetricMap {A V W : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] (f : V →ₗ[A] W) :
    SymmetricAlgebra A V →ₐ[A] SymmetricAlgebra A W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι A W).comp f)

private lemma symmetricMap_comp {A V W T : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [AddCommGroup T] [Module A T] (f : V →ₗ[A] W) (g : W →ₗ[A] T) :
    (symmetricMap g).comp (symmetricMap f) = symmetricMap (g.comp f) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp [symmetricMap]

private lemma symmetricMap_id {A V : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] :
    symmetricMap (LinearMap.id : V →ₗ[A] V) = AlgHom.id A _ := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp [symmetricMap]

private noncomputable def laurentEvaluation {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (t : Cˣ) : LaurentPolynomial B →ₐ[A] C where
  toRingHom := LaurentPolynomial.eval₂ f.toRingHom t
  commutes' a := by simp [LaurentPolynomial.algebraMap_apply]

private lemma weightOne_unit_evaluation {A M B : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [CommRing B] [Algebra A B]
    (F : Laurent.ModuleValuedFunctor A)
    (x : algebraValue F (SymmetricAlgebra A M))
    (hx : x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F
      (symmetricPower06V7 A M) 1) (f : M →ₗ[A] B) (t : Bˣ) :
    algebraMapValue F (SymmetricAlgebra.lift ((t : B) • f)) x =
      (t : B) • algebraMapValue F (SymmetricAlgebra.lift f) x := by
  let e := laurentEvaluation (SymmetricAlgebra.lift f) t
  have hC : e.comp (Laurent.constantLaurentMap A (SymmetricAlgebra A M)) =
      SymmetricAlgebra.lift f :=
    AlgHom.ext fun b => LaurentPolynomial.eval₂_C (SymmetricAlgebra.lift f).toRingHom t b
  have hG : e.comp (Laurent.gradedLaurentMap A (SymmetricAlgebra A M)
      (symmetricPower06V7 A M)) = SymmetricAlgebra.lift ((t : B) • f) := by
    rw [gradedLaurentMap_symmetricAlgebra_eq_degreeOne _
      (symmetricAlgebra06V7_generator_mem_degree_one A M)]
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    show e (symmetricAlgebraLaurentDegreeOneMap (SymmetricAlgebra.ι A M m)) =
      SymmetricAlgebra.lift ((t : B) • f) (SymmetricAlgebra.ι A M m)
    rw [symmetricAlgebraLaurentDegreeOneMap, SymmetricAlgebra.lift_ι_apply,
      SymmetricAlgebra.lift_ι_apply]
    show LaurentPolynomial.eval₂ (SymmetricAlgebra.lift f).toRingHom t
      (LaurentPolynomial.C (SymmetricAlgebra.ι A M m) * LaurentPolynomial.T 1) =
        (t : B) * f m
    simp only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
      zpow_one, SymmetricAlgebra.lift_ι_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    exact mul_comm _ _
  have h := congrArg (algebraMapValue F e) hx
  change algebraMapValue F e ((LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
      algebraMapValue F (Laurent.constantLaurentMap A (SymmetricAlgebra A M)) x) =
    algebraMapValue F e (algebraMapValue F (Laurent.gradedLaurentMap A
      (SymmetricAlgebra A M) (symmetricPower06V7 A M)) x) at h
  rw [map_smulₛₗ, algebraMapValue_comp, algebraMapValue_comp, hC, hG] at h
  simpa [e, laurentEvaluation] using h.symm

private lemma weightOne_symmetricMap {A V W : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (F : Laurent.ModuleValuedFunctor A) (f : V →ₗ[A] W)
    (x : algebraValue F (SymmetricAlgebra A V))
    (hx : x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A V) F
      (symmetricPower06V7 A V) 1) :
    algebraMapValue F (symmetricMap f) x ∈
      AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A W) F
        (symmetricPower06V7 A W) 1 := by
  let t : (LaurentPolynomial (SymmetricAlgebra A W))ˣ :=
    ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by
      rw [← LaurentPolynomial.T_add]; norm_num, by
      rw [← LaurentPolynomial.T_add]; norm_num⟩
  let g := (Laurent.constantLaurentMap A (SymmetricAlgebra A W)).toLinearMap.comp
    ((SymmetricAlgebra.ι A W).comp f)
  have h := weightOne_unit_evaluation F x hx g t
  have hC : (Laurent.constantLaurentMap A (SymmetricAlgebra A W)).comp
      (symmetricMap f) = SymmetricAlgebra.lift g := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [symmetricMap, g]
  have hG : (Laurent.gradedLaurentMap A (SymmetricAlgebra A W)
      (symmetricPower06V7 A W)).comp (symmetricMap f) =
      SymmetricAlgebra.lift ((t : LaurentPolynomial (SymmetricAlgebra A W)) • g) := by
    rw [gradedLaurentMap_symmetricAlgebra_eq_degreeOne _
      (symmetricAlgebra06V7_generator_mem_degree_one A W)]
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    show symmetricAlgebraLaurentDegreeOneMap
        (symmetricMap f (SymmetricAlgebra.ι A V v)) =
      SymmetricAlgebra.lift ((t : LaurentPolynomial (SymmetricAlgebra A W)) • g)
        (SymmetricAlgebra.ι A V v)
    simp only [symmetricMap, symmetricAlgebraLaurentDegreeOneMap,
      SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.smul_apply]
    show LaurentPolynomial.C (SymmetricAlgebra.ι A W (f v)) * LaurentPolynomial.T 1 =
      LaurentPolynomial.T 1 * LaurentPolynomial.C (SymmetricAlgebra.ι A W (f v))
    exact mul_comm _ _
  show (LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A W)) •
    algebraMapValue F (Laurent.constantLaurentMap A (SymmetricAlgebra A W))
      (algebraMapValue F (symmetricMap f) x) =
    algebraMapValue F (Laurent.gradedLaurentMap A (SymmetricAlgebra A W)
      (symmetricPower06V7 A W)) (algebraMapValue F (symmetricMap f) x)
  rw [algebraMapValue_comp, algebraMapValue_comp, hC, hG]
  exact h.symm

private lemma weightOne_zeroMap {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] (F : Laurent.ModuleValuedFunctor A)
    (hF : Laurent.PreservesFlatBaseChange A F)
    (x : algebraValue F (SymmetricAlgebra A M))
    (hx : x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) F
      (symmetricPower06V7 A M) 1) :
    algebraMapValue F (symmetricMap (0 : M →ₗ[A] M)) x = 0 := by
  apply weightSpace_eq_zero_of_mem_two_weights F hF (symmetricPower06V7 A M)
    (k := 1) (l := 0) (by decide)
  · exact weightOne_symmetricMap F 0 x hx
  · have heq : symmetricMap (0 : M →ₗ[A] M) =
        symmetricAlgebraZeroMap (A := A) (M := M) := by
      simp only [symmetricMap, symmetricAlgebraZeroMap, LinearMap.comp_zero]
    rw [heq]
    exact symmetricAlgebraZeroMap_mem_weightSpace_zero F (symmetricPower06V7 A M) x

private lemma weightOne_eq_zero_of_projections {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (F : Laurent.ModuleValuedFunctor A)
    (hflat : Laurent.PreservesFlatBaseChange A F) (hweight : HasWeightOneCoproduct F)
    (z : algebraValue F (SymmetricAlgebra A (M × M)))
    (hz : z ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A (M × M)) F
      (symmetricPower06V7 A (M × M)) 1)
    (h₁ : algebraMapValue F (symmetricMap (LinearMap.fst A M M)) z = 0)
    (h₂ : algebraMapValue F (symmetricMap (LinearMap.snd A M M)) z = 0) : z = 0 := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy, z₁, z₂, rfl, rfl, rfl⟩, _⟩ :=
    (hweight M (symmetricPower06V7 A M) (symmetricPower06V7 A (M × M))
      (symmetricAlgebra06V7_generator_mem_degree_one A M)
      (symmetricAlgebra06V7_generator_mem_degree_one A (M × M)) z).mp hz
  change algebraMapValue F (symmetricMap (LinearMap.fst A M M))
    (algebraMapValue F (symmetricMap (LinearMap.inl A M M)) x +
      algebraMapValue F (symmetricMap (LinearMap.inr A M M)) y) = 0 at h₁
  change algebraMapValue F (symmetricMap (LinearMap.snd A M M))
    (algebraMapValue F (symmetricMap (LinearMap.inl A M M)) x +
      algebraMapValue F (symmetricMap (LinearMap.inr A M M)) y) = 0 at h₂
  have hfi : (LinearMap.fst A M M).comp (LinearMap.inl A M M) = LinearMap.id := rfl
  have hfj : (LinearMap.fst A M M).comp (LinearMap.inr A M M) = 0 := rfl
  have hsi : (LinearMap.snd A M M).comp (LinearMap.inl A M M) = 0 := rfl
  have hsj : (LinearMap.snd A M M).comp (LinearMap.inr A M M) = LinearMap.id := rfl
  rw [map_add, algebraMapValue_comp, algebraMapValue_comp, symmetricMap_comp,
    symmetricMap_comp, hfi, hfj, symmetricMap_id, algebraMapValue_id,
    weightOne_zeroMap F hflat y hy, add_zero] at h₁
  rw [map_add, algebraMapValue_comp, algebraMapValue_comp, symmetricMap_comp,
    symmetricMap_comp, hsi, hsj, symmetricMap_id, algebraMapValue_id,
    weightOne_zeroMap F hflat x hx, zero_add] at h₂
  subst x y
  show algebraMapValue F (symmetricMap (LinearMap.inl A M M)) 0 +
    algebraMapValue F (symmetricMap (LinearMap.inr A M M)) 0 = 0
  simp only [map_zero, add_zero]

private lemma weightOne_lift_additive {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    {F E L : Laurent.ModuleValuedFunctor A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hflat : Laurent.PreservesFlatBaseChange A F)
    (hweight : HasWeightOneCoproduct F)
    (hE : Laurent.PreservesFlatBaseChange A E)
    (x : algebraValue E (SymmetricAlgebra A M))
    (hx : x ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) E
      (symmetricPower06V7 A M) 1)
    (hpx : algebraMapValue L (symmetricMap
        (LinearMap.inl A M M + LinearMap.inr A M M)) (p.app _ x) =
      algebraMapValue L (symmetricMap (LinearMap.inl A M M)) (p.app _ x) +
      algebraMapValue L (symmetricMap (LinearMap.inr A M M)) (p.app _ x)) :
    algebraMapValue E (symmetricMap
        (LinearMap.inl A M M + LinearMap.inr A M M)) x =
      algebraMapValue E (symmetricMap (LinearMap.inl A M M)) x +
      algebraMapValue E (symmetricMap (LinearMap.inr A M M)) x := by
  let d := algebraMapValue E (symmetricMap
        (LinearMap.inl A M M + LinearMap.inr A M M)) x -
      algebraMapValue E (symmetricMap (LinearMap.inl A M M)) x -
      algebraMapValue E (symmetricMap (LinearMap.inr A M M)) x
  have hd : p.app _ d = 0 := by
    dsimp [d]
    rw [map_sub, map_sub]
    refine Eq.trans (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (algebraMapValue_naturality' p
        (symmetricMap (LinearMap.inl A M M + LinearMap.inr A M M)) x)
      (algebraMapValue_naturality' p (symmetricMap (LinearMap.inl A M M)) x))
      (algebraMapValue_naturality' p (symmetricMap (LinearMap.inr A M M)) x)) ?_
    rw [hpx]; abel
  let ev := PresheafOfModules.evaluation (Laurent.algebraRingFunctor A)
    (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A (M × M)))))
  have he := (ShortComplex.moduleCat_exact_iff _).mp (hS.map_of_exact ev).exact
  change ∀ y : algebraValue E (SymmetricAlgebra A (M × M)), p.app _ y = 0 →
    ∃ z : algebraValue F (SymmetricAlgebra A (M × M)), i.app _ z = y at he
  obtain ⟨z, hz⟩ := he d hd
  change i.app _ z = d at hz
  have hi : Mono i := hS.mono_f
  have hwz : z ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A (M × M)) F
      (symmetricPower06V7 A (M × M)) 1 := by
    apply (weightSpace_map_iff_of_mono i _ 1 z).mp
    rw [hz]
    exact weightSpace_sub E _ 1
      (weightSpace_sub E _ 1 (weightOne_symmetricMap E _ x hx)
        (weightOne_symmetricMap E _ x hx)) (weightOne_symmetricMap E _ x hx)
  have hproj (q : M × M →ₗ[A] M)
      (hqa : q.comp (LinearMap.inl A M M + LinearMap.inr A M M) = LinearMap.id)
      (hq : (q.comp (LinearMap.inl A M M) = LinearMap.id ∧
          q.comp (LinearMap.inr A M M) = 0) ∨
        (q.comp (LinearMap.inl A M M) = 0 ∧
          q.comp (LinearMap.inr A M M) = LinearMap.id)) :
      algebraMapValue F (symmetricMap q) z = 0 := by
    apply (ModuleCat.mono_iff_injective (i.app
      (Opposite.op (Opposite.op (CommAlgCat.of A (SymmetricAlgebra A M)))))).mp inferInstance
    rw [algebraMapValue_naturality, (i.app _).hom.map_zero, hz]
    show algebraMapValue E (symmetricMap q) (_ - _ - _) = 0
    rw [map_sub, map_sub, algebraMapValue_comp, algebraMapValue_comp,
      algebraMapValue_comp, symmetricMap_comp, symmetricMap_comp, symmetricMap_comp, hqa]
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb, symmetricMap_id, algebraMapValue_id, weightOne_zeroMap E hE x hx] <;> abel
  have hz0 : z = 0 := weightOne_eq_zero_of_projections F hflat hweight z hwz
    (hproj (LinearMap.fst A M M) (by ext; simp) (Or.inl ⟨rfl, rfl⟩))
    (hproj (LinearMap.snd A M M) (by ext; simp) (Or.inr ⟨rfl, rfl⟩))
  rw [hz0, (i.app _).hom.map_zero] at hz
  have hz' := hz.symm
  dsimp [d] at hz'
  exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hz')

private noncomputable def tensorDual (A V B : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] [CommRing B] [Algebra A B] :
    B ⊗[A] V →ₗ[B] (Module.Dual A V →ₗ[A] B) :=
  LinearMap.liftBaseChange B
    ((LinearMap.compRight A (Algebra.linearMap A B)).comp (Module.Dual.eval A V))

private lemma tensorDual_tmul (A V B : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] [CommRing B] [Algebra A B]
    (b : B) (v : V) (l : Module.Dual A V) :
    tensorDual A V B (b ⊗ₜ[A] v) l = b * algebraMap A B (l v) := rfl

private lemma tensorDual_bijective (A V B : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    [CommRing B] [Algebra A B] : Function.Bijective (tensorDual A V B) := by
  let e := ((TensorProduct.congr (LinearEquiv.refl A B) (Module.evalEquiv A V)).trans
    (TensorProduct.comm A B (Module.Dual A (Module.Dual A V)))).trans
      (dualTensorHomEquiv A (Module.Dual A V) B)
  have he : (tensorDual A V B).restrictScalars A = e.toLinearMap := by
    refine LinearMap.ext fun t => LinearMap.ext fun l => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b v =>
      simp only [LinearMap.restrictScalars_apply, tensorDual_tmul, e,
        LinearEquiv.trans_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, TensorProduct.comm_tmul, dualTensorHomEquiv,
        LinearEquiv.ofBijective_apply, dualTensorHom_apply,
        Module.evalEquiv_apply, Module.Dual.eval_apply, Algebra.smul_def]
      exact mul_comm _ _
    | add t t' ht ht' => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht ht'
  show Function.Bijective ((tensorDual A V B).restrictScalars A)
  rw [he]
  exact e.bijective

private lemma tensorDual_baseChange {A V W B : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W) (t : B ⊗[A] V)
    (l : Module.Dual A W) :
    tensorDual A W B (f.baseChange B t) l = tensorDual A V B t (l.comp f) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp only [LinearMap.baseChange_tmul, tensorDual_tmul, LinearMap.comp_apply]
  | add t t' ht ht' => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht ht'

private lemma tensorDual_naturality {A V B C : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] (f : B →ₐ[A] C) (t : B ⊗[A] V)
    (l : Module.Dual A V) :
    tensorDual A V C (TensorProduct.map f.toLinearMap LinearMap.id t) l =
      f (tensorDual A V B t l) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      AlgHom.toLinearMap_apply, tensorDual_tmul, map_mul, AlgHom.commutes]
  | add t t' ht ht' => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht ht'

private noncomputable def kernelTensorDual {A V W B : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W) :
    LinearMap.ker (f.baseChange B) →ₗ[B]
      ((Module.Dual A V ⧸ LinearMap.range f.dualMap) →ₗ[A] B) where
  toFun t := (LinearMap.range f.dualMap).liftQ (tensorDual A V B t.val) (by
    rintro _ ⟨l, rfl⟩
    change tensorDual A V B t.val (l.comp f) = 0
    rw [← tensorDual_baseChange, t.property, map_zero, LinearMap.zero_apply])
  map_add' x y := by
    apply LinearMap.ext
    intro q
    obtain ⟨l, rfl⟩ := (LinearMap.range f.dualMap).mkQ_surjective q
    simp [Submodule.liftQ_apply]
  map_smul' b x := by
    apply LinearMap.ext
    intro q
    obtain ⟨l, rfl⟩ := (LinearMap.range f.dualMap).mkQ_surjective q
    simp [Submodule.liftQ_apply]

private lemma kernelTensorDual_mkQ {A V W B : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W)
    (t : LinearMap.ker (f.baseChange B)) (l : Module.Dual A V) :
    kernelTensorDual f t ((LinearMap.range f.dualMap).mkQ l) = tensorDual A V B t.val l := rfl

private lemma kernelTensorDual_bijective {A V W B : Type u} [CommRing A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [Module.Finite A V] [Module.Free A V] [Module.Finite A W] [Module.Free A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W) :
    Function.Bijective (kernelTensorDual (B := B) f) := by
  refine ⟨fun x y h => Subtype.ext <| (tensorDual_bijective A V B).injective <|
    LinearMap.ext fun l => congrArg (fun z => z ((LinearMap.range f.dualMap).mkQ l)) h,
    fun h => ?_⟩
  obtain ⟨t, ht⟩ := (tensorDual_bijective A V B).surjective
    (h.comp (LinearMap.range f.dualMap).mkQ)
  have hf : f.baseChange B t = 0 := by
    apply (tensorDual_bijective A W B).injective
    ext l
    rw [tensorDual_baseChange, ht]
    show h ((LinearMap.range f.dualMap).mkQ (f.dualMap l)) = 0
    have hz : (LinearMap.range f.dualMap).mkQ (f.dualMap l) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range f.dualMap)).mpr ⟨l, rfl⟩
    rw [hz, map_zero]
  refine ⟨⟨t, hf⟩, LinearMap.ext fun q => ?_⟩
  obtain ⟨l, rfl⟩ := (LinearMap.range f.dualMap).mkQ_surjective q
  rw [kernelTensorDual_mkQ, ht]
  rfl

private lemma exists_linearRepresentation {A : Type u} [CommRing A]
    (L : Laurent.ModuleValuedFunctor A) (hL : AdequateFunctor.IsLinearlyAdequate (𝟭 _) L) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module A M),
      Module.FinitePresentation A M ∧
      ∃ e : ∀ B : CommAlgCat.{u} A,
          algebraValue L B ≃ₗ[B] (M →ₗ[A] B),
        ∀ (B C : CommAlgCat.{u} A) (f : B ⟶ C) (x : algebraValue L B),
          e C (algebraMapValue L f.hom x) = f.hom.toLinearMap.comp (e B x) := by
  obtain ⟨n, m, f, hf⟩ :=
    (isLinearlyAdequate_iff_exists_module_map L).mp hL
  obtain ⟨e⟩ := (isKernelPresentation_iff L f).mp hf
  let V := finiteFreeModule.{u} A n
  let W := finiteFreeModule.{u} A m
  let : Module.Free A V := Module.Free.of_equiv
    (ULift.moduleEquiv.symm : (Fin n → A) ≃ₗ[A] V)
  let : Module.Finite A V := Module.Finite.equiv
    (ULift.moduleEquiv.symm : (Fin n → A) ≃ₗ[A] V)
  let : Module.Free A W := Module.Free.of_equiv
    (ULift.moduleEquiv.symm : (Fin m → A) ≃ₗ[A] W)
  let : Module.Finite A W := Module.Finite.equiv
    (ULift.moduleEquiv.symm : (Fin m → A) ≃ₗ[A] W)
  let Q := LinearMap.range f.hom.dualMap
  let M := Module.Dual A V ⧸ Q
  have hM : Module.FinitePresentation A M :=
    Module.finitePresentation_of_free_of_surjective Q.mkQ Q.mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := A) (M := Module.Dual A W)).map f.hom.dualMap)
  let q := (moduleExtensionFunctor A).map f
  let η : L ⟶ moduleExtension A V := e.hom ≫ kernel.ι q
  let eB (B : CommAlgCat.{u} A) : algebraValue L B ≃ₗ[B] LinearMap.ker (f.hom.baseChange B) :=
    CategoryTheory.Iso.toLinearEquiv
      ((PresheafOfModules.evaluation (Laurent.algebraRingFunctor A)
        (Opposite.op (Opposite.op B))).mapIso e ≪≫ evaluatedKernelIso06V7 q _)
  have heB (B : CommAlgCat.{u} A) (x : algebraValue L B) :
      (eB B x).val = (η.app (Opposite.op (Opposite.op B))).hom x :=
    congrArg (fun g => g.hom ((e.hom.app (Opposite.op (Opposite.op B))).hom x))
      (evaluatedKernelIso06V7_hom_comp q (Opposite.op (Opposite.op B)))
  let r (B : CommAlgCat.{u} A) : algebraValue L B ≃ₗ[B] (M →ₗ[A] B) :=
    (eB B).trans
      (LinearEquiv.ofBijective (kernelTensorDual f.hom) (kernelTensorDual_bijective f.hom))
  refine ⟨M, inferInstance, inferInstance, hM, r, fun B C g x => LinearMap.ext fun z => ?_⟩
  obtain ⟨l, rfl⟩ := Q.mkQ_surjective z
  show tensorDual A V C (eB C (algebraMapValue L g.hom x)).val l =
    g.hom (tensorDual A V B (eB B x).val l)
  rw [heB, heB, algebraMapValue_naturality η g.hom x]
  exact tensorDual_naturality g.hom _ l

private lemma evaluate_primitive_add {A M B : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [CommRing B] [Algebra A B]
    (E : Laurent.ModuleValuedFunctor A) (x : algebraValue E (SymmetricAlgebra A M))
    (hx : algebraMapValue E (symmetricMap
        (LinearMap.inl A M M + LinearMap.inr A M M)) x =
      algebraMapValue E (symmetricMap (LinearMap.inl A M M)) x +
      algebraMapValue E (symmetricMap (LinearMap.inr A M M)) x)
    (f g : M →ₗ[A] B) :
    algebraMapValue E (SymmetricAlgebra.lift (f + g)) x =
      algebraMapValue E (SymmetricAlgebra.lift f) x +
      algebraMapValue E (SymmetricAlgebra.lift g) x := by
  let h := SymmetricAlgebra.lift (f.coprod g)
  have hcomp (j : M →ₗ[A] M × M) :
      h.comp (symmetricMap j) = SymmetricAlgebra.lift ((f.coprod g).comp j) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    show h (symmetricMap j (SymmetricAlgebra.ι A M m)) =
      SymmetricAlgebra.lift ((f.coprod g).comp j) (SymmetricAlgebra.ι A M m)
    simp only [h, symmetricMap, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
  have he := congrArg (algebraMapValue E h) hx
  rw [map_add, algebraMapValue_comp, algebraMapValue_comp, algebraMapValue_comp,
    hcomp, hcomp, hcomp] at he
  have hsum : (f.coprod g).comp (LinearMap.inl A M M + LinearMap.inr A M M) = f + g := by
    ext m; simp
  have hfst : (f.coprod g).comp (LinearMap.inl A M M) = f := by ext; simp
  have hsnd : (f.coprod g).comp (LinearMap.inr A M M) = g := by ext; simp
  rwa [hsum, hfst, hsnd] at he

-- The universal element is compared in several evaluated module structures.
private lemma exists_section_of_linearRepresentation {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    {F E L : Laurent.ModuleValuedFunctor A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hflat : Laurent.PreservesFlatBaseChange A F)
    (hweight : HasWeightOneCoproduct F)
    (hE : Laurent.PreservesFlatBaseChange A E)
    (hL : Laurent.PreservesFlatBaseChange A L)
    (e : ∀ B : CommAlgCat.{u} A, algebraValue L B ≃ₗ[B] (M →ₗ[A] B))
    (hnat : ∀ (B C : CommAlgCat.{u} A) (f : B ⟶ C) (x : algebraValue L B),
      e C (algebraMapValue L f.hom x) = f.hom.toLinearMap.comp (e B x)) :
    ∃ s : L ⟶ E, s ≫ p = 𝟙 L := by
  let B := CommAlgCat.of A (SymmetricAlgebra A M)
  let C := CommAlgCat.of A (SymmetricAlgebra A (M × M))
  let ξ := (e B).symm (SymmetricAlgebra.ι A M)
  have heξ : e B ξ = SymmetricAlgebra.ι A M := (e B).apply_symm_apply _
  have hwξ : ξ ∈ AdequateFunctor.Laurent.weightSpace A (SymmetricAlgebra A M) L
      (symmetricPower06V7 A M) 1 := by
    show (LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
      algebraMapValue L (Laurent.constantLaurentMap A (SymmetricAlgebra A M)) ξ =
      algebraMapValue L (Laurent.gradedLaurentMap A (SymmetricAlgebra A M)
        (symmetricPower06V7 A M)) ξ
    apply (e (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M)))).injective
    rw [map_smul, hnat B _ (CommAlgCat.ofHom (Laurent.constantLaurentMap A _)),
      hnat B _ (CommAlgCat.ofHom (Laurent.gradedLaurentMap A _ _)), heξ]
    refine LinearMap.ext fun m => ?_
    show LaurentPolynomial.T 1 * LaurentPolynomial.C (SymmetricAlgebra.ι A M m) =
      Laurent.gradedLaurentMap A (SymmetricAlgebra A M) (symmetricPower06V7 A M)
        (SymmetricAlgebra.ι A M m)
    rw [gradedLaurentMap_symmetricAlgebra_eq_degreeOne _
      (symmetricAlgebra06V7_generator_mem_degree_one A M), symmetricAlgebraLaurentDegreeOneMap,
      SymmetricAlgebra.lift_ι_apply]
    exact mul_comm _ _
  have hp : Epi p := hS.epi_g
  obtain ⟨θ, hθ, hpθ⟩ := exists_weightSpace_lift_of_epi p hE hL
    (symmetricPower06V7 A M) 1 ξ hwξ
  have hξadd : algebraMapValue L (symmetricMap
        (LinearMap.inl A M M + LinearMap.inr A M M)) (p.app _ θ) =
      algebraMapValue L (symmetricMap (LinearMap.inl A M M)) (p.app _ θ) +
      algebraMapValue L (symmetricMap (LinearMap.inr A M M)) (p.app _ θ) := by
    rw [hpθ]
    apply (e C).injective
    rw [map_add, hnat B C (CommAlgCat.ofHom (symmetricMap _)),
      hnat B C (CommAlgCat.ofHom (symmetricMap _)),
      hnat B C (CommAlgCat.ofHom (symmetricMap _)), heξ]
    refine LinearMap.ext fun m => ?_
    show symmetricMap _ (SymmetricAlgebra.ι A M m) =
      symmetricMap _ (SymmetricAlgebra.ι A M m) + symmetricMap _ (SymmetricAlgebra.ι A M m)
    simp only [symmetricMap, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      LinearMap.add_apply, map_add]
  have hθadd := weightOne_lift_additive i p hip hS hflat hweight hE θ hθ hξadd
  let s (D : CommAlgCat.{u} A) (x : algebraValue L D) : algebraValue E D :=
    algebraMapValue E (SymmetricAlgebra.lift (e D x)) θ
  have hsadd (D : CommAlgCat.{u} A) (x y : algebraValue L D) : s D (x + y) = s D x + s D y := by
    dsimp only [s]
    rw [map_add]
    exact evaluate_primitive_add E θ hθadd _ _
  have hsnat (D D' : CommAlgCat.{u} A) (f : D ⟶ D') (x : algebraValue L D) :
      s D' (algebraMapValue L f.hom x) = algebraMapValue E f.hom (s D x) := by
    dsimp only [s]
    rw [hnat, algebraMapValue_comp]
    have hh : SymmetricAlgebra.lift (f.hom.toLinearMap.comp (e D x)) =
        f.hom.comp (SymmetricAlgebra.lift (e D x)) := by
      apply SymmetricAlgebra.algHom_ext
      refine LinearMap.ext fun m => ?_
      show SymmetricAlgebra.lift (f.hom.toLinearMap.comp (e D x)) (SymmetricAlgebra.ι A M m) =
        f.hom (SymmetricAlgebra.lift (e D x) (SymmetricAlgebra.ι A M m))
      simp only [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [hh]
  let φ : L.presheaf ⟶ E.presheaf :=
    { app X := AddCommGrpCat.ofHom (AddMonoidHom.mk' (s X.unop.unop) (hsadd X.unop.unop))
      naturality := by
        intro X Y f
        ext x
        exact hsnat X.unop.unop Y.unop.unop f.unop.unop x }
  obtain ⟨s', hs'⟩ := Laurent.naturalTransformation_lifts_of_units_of_flatBaseChange A L E φ
    (by
      intro D x a
      rcases D with ⟨⟨D⟩⟩
      change Units D at a
      show s D ((a : D) • x) = (a : D) • s D x
      dsimp only [s]
      rw [map_smul]
      exact weightOne_unit_evaluation E θ hθ _ a)
    (by
      intro D D' f hf
      exact hE D.unop.unop D'.unop.unop f.unop.unop.hom hf)
  refine ⟨s', ?_⟩
  ext D x
  have hsx := congrArg (fun τ => (τ.app D).hom x) hs'
  change s'.app D x = s D.unop.unop x at hsx
  show p.app D (s'.app D x) = x
  rw [hsx]
  show p.app D (algebraMapValue E (SymmetricAlgebra.lift (e D.unop.unop x)) θ) = x
  rw [algebraMapValue_naturality, hpθ]
  apply (e D.unop.unop).injective
  rw [hnat B D.unop.unop (CommAlgCat.ofHom (SymmetricAlgebra.lift (e D.unop.unop x))), heξ]
  exact SymmetricAlgebra.lift_comp_ι _

-- Match the quiver instance used when the tagged statement is elaborated.
section
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver

/-- An extension of a linearly adequate functor splits if its kernel functor
commutes with flat base change and has a direct weight-one coproduct decomposition. -/
@[stacks 06V7 "splitting under flat base change and weight-one decomposition"]
public lemma exists_retraction_of_shortExact_of_baseChange_weightOne
    {A : Type u} [CommRing A]
    {F E L : ModuleValuedFunctor.{u, u} A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hflat : Laurent.PreservesFlatBaseChange A F)
    (hweight : HasWeightOneCoproduct F)
    (hL : AdequateFunctor.IsLinearlyAdequate (𝟭 _) L) :
    ∃ r : E ⟶ F, i ≫ r = 𝟙 F := by
  obtain ⟨M, _, _, _, e, he⟩ := exists_linearRepresentation L hL
  have hLa : AdequateFunctor.IsAdequate (𝟭 _) L := by
    obtain ⟨n, m, f, hf⟩ := (isLinearlyAdequate_iff L).mp hL
    exact (isAdequate_iff L).mpr ⟨_, _, f, hf⟩
  have hLf := adequate_preservesFlatBaseChange L hLa
  have hEf := preservesFlatBaseChange_of_shortExact (ShortComplex.mk i p hip) hS hflat hLf
  obtain ⟨s, hs⟩ := exists_section_of_linearRepresentation i p hip hS hflat hweight hEf hLf e he
  let splitting := ShortComplex.Splitting.ofExactOfSection _ hS.exact s hs hS.mono_f
  exact ⟨splitting.r, splitting.f_r⟩

end
/-- **Stacks 06V7.** An extension of a linearly adequate functor by an adequate functor admits a
retraction onto its kernel term. An adequate functor commutes with flat base change by
Stacks 06UW, and its weight-one part decomposes by Stacks 06UZ, which are the only two
properties of the kernel the splitting uses. -/
@[stacks 06V7 "splitting of extensions"]
public lemma exists_retraction_of_shortExact {A : Type u} [CommRing A]
    {F E L : ModuleValuedFunctor.{u, u} A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hF : AdequateFunctor.IsAdequate (𝟭 _) F)
    (hL : AdequateFunctor.IsLinearlyAdequate (𝟭 _) L) :
    ∃ r : E ⟶ F, i ≫ r = 𝟙 F :=
  exists_retraction_of_shortExact_of_baseChange_weightOne i p hip hS
    (adequate_preservesFlatBaseChange F hF) (adequate_hasWeightOneCoproduct F hF) hL

/-- The module-valued functor `B ↦ B ⊗[A] M` is adequate: it is the kernel of the zero map to
the functor of the zero module. -/
private lemma moduleExtension_isAdequate {A : Type u} [CommRing A] (M : ModuleCat.{u} A) :
    AdequateFunctor.IsAdequate (𝟭 _) (moduleExtension.{u, u} A M) := by
  refine (isAdequate_iff (moduleExtension.{u, u} A M)).mpr
    ⟨M, finiteFreeModule.{u} A 0, 0, ?_⟩
  let : IsIso (kernel.ι (0 : moduleExtension.{u, u} A M ⟶
      moduleExtension.{u, u} A (finiteFreeModule.{u} A 0))) :=
    kernel.ι_of_zero (by simp)
  exact ⟨(asIso (kernel.ι (0 : moduleExtension.{u, u} A M ⟶
    moduleExtension.{u, u} A (finiteFreeModule.{u} A 0)))).symm⟩

/-- **Stacks 06V6.** Let `A` be a ring and let `0 → M → G → L → 0` be a short exact sequence of
module-valued functors on `Alg_A`, where `M` is the functor `B ↦ B ⊗[A] M` of an `A`-module `M`
and `L` is linearly adequate. Then `G` is adequate. -/
@[stacks 06V6]
public lemma isAdequate_of_moduleExtension_shortExact {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) (G L : ModuleValuedFunctor.{u, u} A)
    (i : moduleExtension.{u, u} A M ⟶ G) (p : G ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hL : AdequateFunctor.IsLinearlyAdequate (𝟭 _) L) :
    AdequateFunctor.IsAdequate (𝟭 _) G := by
  let S := ShortComplex.mk i p hip
  have hM : AdequateFunctor.IsAdequate (𝟭 _) (moduleExtension.{u, u} A M) :=
    moduleExtension_isAdequate M
  obtain ⟨r, hr⟩ := exists_retraction_of_shortExact i p hip hS hM hL
  let hs : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hS.exact r hr hS.epi_g
  refine ((isAdequate_colimit (pair S.X₁ S.X₃) ?_).of_iso
    (biprod.isoCoprod S.X₁ S.X₃)).of_iso hs.isoBinaryBiproduct
  rintro ⟨_ | _⟩
  · exact hM
  · obtain ⟨_, _, f, h⟩ := (isLinearlyAdequate_iff_exists_module_map L).mp hL
    exact ⟨_, _, f, h⟩

end AdequateFunctor

end

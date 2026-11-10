module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.Flat.Prod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projectivity over a product of two rings

The proof of Stacks 05FS descends projectivity of `S` along the faithfully flat ring map
`R → R_f × R^∧`. This file provides the facts about a product of two rings that the descent
needs: that a product of two projective modules is projective, that projectivity composes
along a tower, and that projectivity of a base change to `A × B` follows from projectivity
of the base changes to `A` and to `B` separately.

## Main results

* `Module.Projective.prod`: a product of two projective modules is projective.
* `Module.Projective.trans`: projectivity composes along a tower `A' → A` in which `A` is a
  projective `A'`-module. This is the general form of transitivity used throughout the
  project; only the base ring has to be commutative.
* `Module.Projective.of_prod_tensorProduct`: if `A ⊗_R M` is projective over `A` and
  `B ⊗_R M` is projective over `B`, then `(A × B) ⊗_R M` is projective over `A × B`.
* `Module.faithfullyFlat_prod_of_forall_ne_top`: a criterion for `A × B` to be faithfully
  flat over `R`, namely that for every maximal ideal of `R` at least one of the two factors
  stays proper.

## Implementation notes

`Module.Projective.of_prod_tensorProduct` is proved without decomposing an `A × B`-module
into its two idempotent pieces. Instead the two projections `A × B → A` and `A × B → B` and
the two additive sections `a ↦ (a, 0)` and `b ↦ (0, b)` are tensored with `M`, giving
`A × B`-linear maps between `(A × B) ⊗_R M` and `A ⊗_R M`, respectively `B ⊗_R M`, whose
composites in one direction are the identity and whose composites in the other direction add
up to the identity. The `A × B`-module structures on `A` and `B` are the ones restricted
along the projections, and `Module.Projective.trans` turns `A`-projectivity of `A ⊗_R M` into
`A × B`-projectivity. Then `(A × B) ⊗_R M` is a direct summand of
`(A ⊗_R M) × (B ⊗_R M)`, which is `A × B`-projective by `Module.Projective.prod`.

That a product of two flat modules is flat is `Module.Flat.prod` of
`StacksFrontier.RingTheory.Flat.Prod`, which also records the two converse implications and the
resulting characterization `Module.Flat.prod_iff`.

## References

* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module

variable {R : Type u} [CommRing R]

/-- A product of two projective modules is projective: a splitting of `M` and a splitting of
`N` combine, after pushing the index sets into `M × N` along `m ↦ (m, 0)` and `n ↦ (0, n)`,
to a splitting of `M × N`. -/
theorem Projective.prod {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Projective R M] [Projective R N] : Projective R (M × N) := by
  obtain ⟨sM, hsM⟩ := projective_def'.mp ‹Projective R M›
  obtain ⟨sN, hsN⟩ := projective_def'.mp ‹Projective R N›
  have hsM' : ∀ m : M, Finsupp.linearCombination R (id : M → M) (sM m) = m :=
    fun m => LinearMap.congr_fun hsM m
  have hsN' : ∀ n : N, Finsupp.linearCombination R (id : N → N) (sN n) = n :=
    fun n => LinearMap.congr_fun hsN n
  refine projective_def'.mpr ⟨Finsupp.lmapDomain R R (fun m : M => (m, (0 : N))) ∘ₗ sM ∘ₗ
    LinearMap.fst R M N + Finsupp.lmapDomain R R (fun n : N => ((0 : M), n)) ∘ₗ sN ∘ₗ
      LinearMap.snd R M N, LinearMap.ext fun x => ?_⟩
  have hM : Finsupp.linearCombination R (id : M × N → M × N)
      (Finsupp.mapDomain (fun m : M => (m, (0 : N))) (sM x.1)) = (x.1, 0) := by
    rw [Finsupp.linearCombination_mapDomain]
    have h1 := Finsupp.apply_linearCombination R (LinearMap.inl R M N) (id : M → M) (sM x.1)
    rw [hsM' x.1] at h1
    exact h1.symm
  have hN : Finsupp.linearCombination R (id : M × N → M × N)
      (Finsupp.mapDomain (fun n : N => ((0 : M), n)) (sN x.2)) = (0, x.2) := by
    rw [Finsupp.linearCombination_mapDomain]
    have h2 := Finsupp.apply_linearCombination R (LinearMap.inr R M N) (id : N → N) (sN x.2)
    rw [hsN' x.2] at h2
    exact h2.symm
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Finsupp.lmapDomain_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_apply, hM, hN]
  exact Prod.ext (by simp) (by simp)

/-- Projectivity composes along a tower: if `A` is a projective `A'`-module and `X` is a
projective `A`-module, then `X` is a projective `A'`-module. Indeed `X` is a direct summand
of the `A`-module `X →₀ A`, which is a direct sum of copies of `A` and hence `A'`-projective,
and the splitting maps are `A`-linear, so in particular `A'`-linear.

Only `A'` has to be commutative, and `X` only has to be an additive monoid. -/
theorem Projective.trans (A' : Type*) (A : Type*) (X : Type*) [CommSemiring A'] [Semiring A]
    [Algebra A' A] [AddCommMonoid X] [Module A X] [Module A' X] [IsScalarTower A' A X]
    [Projective A' A] [Projective A X] : Projective A' X := by
  classical
  obtain ⟨s, hs⟩ := ‹Projective A X›
  have : Projective A' (X →₀ A) := Projective.of_equiv' (finsuppLequivDFinsupp A').symm
  exact Projective.of_split (R := A') (s.restrictScalars A')
    ((Finsupp.linearCombination A (id : X → X)).restrictScalars A')
    (LinearMap.ext hs)

section ProdRing

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- The first factor of `A × B`, as an algebra over `A × B`. -/
@[instance_reducible] private def fstAlgebra : Algebra (A × B) A := (RingHom.fst A B).toAlgebra

/-- The second factor of `A × B`, as an algebra over `A × B`. -/
@[instance_reducible] private def sndAlgebra : Algebra (A × B) B := (RingHom.snd A B).toAlgebra

attribute [local instance] fstAlgebra sndAlgebra

private instance : IsScalarTower R (A × B) A := IsScalarTower.of_algebraMap_eq fun _ => rfl

private instance : IsScalarTower R (A × B) B := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The additive section `a ↦ (a, 0)` of the first projection, as an `A × B`-linear map. -/
private def inlProd : A →ₗ[A × B] (A × B) where
  toFun a := (a, 0)
  map_add' _ _ := by simp
  map_smul' c a := by
    change ((c.1 * a : A), (0 : B)) = c • ((a, 0) : A × B)
    rw [smul_eq_mul, Prod.mk_mul_mk, mul_zero]

/-- The additive section `b ↦ (0, b)` of the second projection, as an `A × B`-linear map. -/
private def inrProd : B →ₗ[A × B] (A × B) where
  toFun b := (0, b)
  map_add' _ _ := by simp
  map_smul' c b := by
    change ((0 : A), (c.2 * b : B)) = c • ((0, b) : A × B)
    rw [smul_eq_mul, Prod.mk_mul_mk, mul_zero]

/-- The projection `A × B → A`, as an `A × B`-linear map. -/
private def fstProd : (A × B) →ₗ[A × B] A where
  toFun := Prod.fst
  map_add' _ _ := rfl
  map_smul' c x := by
    change (c * x).1 = c.1 * x.1
    rfl

/-- The projection `A × B → B`, as an `A × B`-linear map. -/
private def sndProd : (A × B) →ₗ[A × B] B where
  toFun := Prod.snd
  map_add' _ _ := rfl
  map_smul' c x := by
    change (c * x).2 = c.2 * x.2
    rfl

/-- `A` is projective over `A × B`: it is the direct summand `A × 0`. -/
private theorem projective_fst : Projective (A × B) A :=
  Projective.of_split (R := A × B) (inlProd A B) (fstProd A B) (LinearMap.ext fun _ => rfl)

/-- `B` is projective over `A × B`: it is the direct summand `0 × B`. -/
private theorem projective_snd : Projective (A × B) B :=
  Projective.of_split (R := A × B) (inrProd A B) (sndProd A B) (LinearMap.ext fun _ => rfl)

/-- If the base changes of `M` to `A` and to `B` are projective over `A` and over `B`, then
the base change to `A × B` is projective over `A × B`. -/
theorem Projective.of_prod_tensorProduct (hA : Projective A (A ⊗[R] M))
    (hB : Projective B (B ⊗[R] M)) : Projective (A × B) ((A × B) ⊗[R] M) := by
  have hA' : Projective (A × B) (A ⊗[R] M) :=
    have := projective_fst A B
    have := hA
    Projective.trans (A × B) A (A ⊗[R] M)
  have hB' : Projective (A × B) (B ⊗[R] M) :=
    have := projective_snd A B
    have := hB
    Projective.trans (A × B) B (B ⊗[R] M)
  have hP : Projective (A × B) ((A ⊗[R] M) × (B ⊗[R] M)) :=
    have := hA'
    have := hB'
    Projective.prod
  have := hP
  refine Projective.of_split (R := A × B)
    ((TensorProduct.AlgebraTensorModule.map (fstProd A B) (LinearMap.id (R := R) (M := M))).prod
      (TensorProduct.AlgebraTensorModule.map (sndProd A B) (LinearMap.id (R := R) (M := M))))
    (TensorProduct.AlgebraTensorModule.map (inlProd A B) (LinearMap.id (R := R) (M := M)) ∘ₗ
        LinearMap.fst _ _ _ +
      TensorProduct.AlgebraTensorModule.map (inrProd A B) (LinearMap.id (R := R) (M := M)) ∘ₗ
        LinearMap.snd _ _ _) (LinearMap.ext fun x => ?_)
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      simp only [LinearMap.comp_apply, LinearMap.prod_apply, Function.prod, LinearMap.add_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, TensorProduct.AlgebraTensorModule.map_tmul,
        LinearMap.id_apply, ← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (by simp [inlProd, inrProd, fstProd, sndProd])
        (by simp [inlProd, inrProd, fstProd, sndProd])
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.id_apply]

end ProdRing

/-- If `I` fills up a product of two modules then it fills up each factor: the projections
are surjective, and the image of `I • ⊤` under a surjection is `I • ⊤`. -/
private theorem smul_top_eq_top_of_prod {A B : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (I : Ideal R)
    (h : I • (⊤ : Submodule R (A × B)) = ⊤) :
    I • (⊤ : Submodule R A) = ⊤ ∧ I • (⊤ : Submodule R B) = ⊤ := by
  have key : ∀ (C : Type v) (_ : AddCommGroup C) (_ : Module R C) (f : (A × B) →ₗ[R] C),
      Function.Surjective f → I • (⊤ : Submodule R C) = ⊤ := by
    intro C _ _ f hf
    have hmap := congrArg (Submodule.map f) h
    rw [Submodule.map_smul'', Submodule.map_top] at hmap
    rwa [LinearMap.range_eq_top.mpr hf] at hmap
  exact ⟨key A _ _ (LinearMap.fst R A B) fun a => ⟨(a, 0), rfl⟩,
    key B _ _ (LinearMap.snd R A B) fun b => ⟨(0, b), rfl⟩⟩

/-- A criterion for `A × B` to be faithfully flat over `R`: both factors are flat, and for
every maximal ideal `m` of `R` at least one of `m • A` and `m • B` is a proper submodule.
This is the way faithful flatness of `R → R_f × R^∧` is checked in Stacks 05FS. -/
@[ega "0 6.4.1" "d), special case",
  ega "0 6.4.2" "more general",
  sga "1 IV 2.1" "(i), special case"]
theorem faithfullyFlat_prod_of_forall_ne_top {A B : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Flat R A] [Flat R B]
    (h : ∀ m : Ideal R, m.IsMaximal →
      m • (⊤ : Submodule R A) ≠ ⊤ ∨ m • (⊤ : Submodule R B) ≠ ⊤) :
    FaithfullyFlat R (A × B) := by
  rw [FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨Flat.prod, fun I hI hc => ?_⟩
  obtain ⟨m, hm, hle⟩ := I.exists_le_maximal hI
  have hmc : m • (⊤ : Submodule R (A × B)) = ⊤ :=
    top_unique (hc.ge.trans (Submodule.smul_mono hle le_rfl))
  obtain ⟨hA, hB⟩ := smul_top_eq_top_of_prod m hmc
  rcases h m hm with hA' | hB'
  · exact hA' hA
  · exact hB' hB

end Module

end

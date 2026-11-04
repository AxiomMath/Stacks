module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksCore.Tactic.StacksAttribute

/-!
# Algebras which are their own linear dual

An `R`-algebra `B` is *self-dual* when some `R`-linear functional `l` on `B` makes multiplication
a perfect pairing, i.e. when `x ↦ l(x · -)` is a bijection `B → Hom_R(B, R)`.  This is the
condition under which `B` is isomorphic to its `R`-linear dual *as a `B`-module*, the `B`-action
on `Hom_R(B, R)` being the one on the source argument; the isomorphism is `x ↦ l(x · -)` itself.

The property is what the proof of [Stacks, Tag 0C0G] establishes for `B = R[x]/(f)` with `f`
monic, through the top-coefficient functional `δ_{d-1}`, and it is *transitive*: a self-dual
algebra over a self-dual algebra is self-dual.  Transitivity is what carries the monogenic case to
a tower `R → R[x_1]/(f_1) → ⋯ → R[x_1, …, x_n]/(f_1, …, f_n)`, and it needs no finiteness —
`Hom_R(B, R) = Hom_A(B, Hom_R(A, R)) = Hom_A(B, A) = B`.

## Main definitions

* `Dualizing.IsSelfDualAlgebra` — some `R`-linear functional on `B` makes multiplication a
  perfect pairing.

## Main results

* `Dualizing.IsSelfDualAlgebra.iso` — **`B ≅ Hom_R(B, R)` as `B`-modules** for a self-dual `B`,
  with `Hom_R(B, R)` in the form in which derived coextension of scalars meets it,
  `ModuleCat.coextendScalars (algebraMap R B)` applied to `R`.
* `Dualizing.isSelfDualAlgebra_self` — a ring is self-dual over itself.
* `Dualizing.IsSelfDualAlgebra.trans` — self-duality composes along a tower.

## Implementation notes

The `R`-linear dual appears as
`(ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R)` rather than as
`Module.Dual R B`, because `Mathlib` puts the `B`-module structure of `Hom_R(B, R)` — the one
coming from the `B`-action on the *source* — only on the former.  That forces `R` and `B` into a
single universe for `Dualizing.IsSelfDualAlgebra.iso`; the predicate itself and its transitivity
are universe polymorphic.

## References

* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
-/

@[expose] public section

open CategoryTheory Module

namespace Dualizing

/-- **A self-dual algebra.**  An `R`-algebra `B` is self-dual when some `R`-linear functional `l`
on `B` makes multiplication a perfect pairing: `x ↦ l(x · -)` is a bijection from `B` onto
`Hom_R(B, R)`.

Equivalently `B` is a Frobenius algebra over `R` with `l` as its Frobenius form.  This is what the
proof of [Stacks, Tag 0C0G] establishes for `R[x]/(f)` with `f` monic, where `l` is the
coefficient of `x^{d-1}`. -/
def IsSelfDualAlgebra (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] : Prop :=
  ∃ l : B →ₗ[R] R, Function.Bijective ((LinearMap.mul R B).compr₂ l)

section Iso

universe u

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- **A self-dual algebra is its own `R`-linear dual, as a module over itself.**  For `B` a
self-dual `R`-algebra,

`B ≅ Hom_R(B, R)`

as `B`-modules, where the right-hand side carries the `B`-action by precomposition with
multiplication, i.e. is `ModuleCat.coextendScalars (algebraMap R B)` applied to `R`.

The isomorphism is `x ↦ l(x · -)` for a functional `l` making multiplication a perfect pairing.
-/
noncomputable def IsSelfDualAlgebra.iso (h : IsSelfDualAlgebra R B) :
    ModuleCat.of B B ≅ (ModuleCat.coextendScalars (algebraMap R B)).obj (ModuleCat.of R R) := by
  let l := Classical.choose h
  have hl := Classical.choose_spec h
  let l' : (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B) ⟶
      ModuleCat.of R R := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B))
    { toFun := fun x => l (x : B)
      map_add' := l.map_add
      map_smul' := fun r x => by
        change l (algebraMap R B r * (show B from x)) = r • l x
        rw [← Algebra.smul_def, l.map_smul] }
  let m := ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction (algebraMap R B) l'
  have hm (x y : B) : m x y = l (x * y) := by
    change l (y * x) = l (x * y)
    rw [mul_comm]
  have hinj : Function.Injective m := by
    intro x y hxy
    apply hl.1
    ext z
    change l (x * z) = l (y * z)
    simpa only [hm] using congrArg (fun k => k z) hxy
  have hsurj : Function.Surjective m := by
    intro k
    let k' : B →ₗ[R] R :=
      { toFun := fun x => k x
        map_add' := fun x y => (ModuleCat.CoextendScalars.equiv _ _ k).map_add x y
        map_smul' := fun r x => by
          change k (r • x) = r • k x
          rw [Algebra.smul_def]
          exact (ModuleCat.CoextendScalars.equiv _ _ k).map_smul r x }
    obtain ⟨x, hx⟩ := hl.2 k'
    refine ⟨x, ?_⟩
    apply ModuleCat.CoextendScalars.ext
    ext y
    exact (hm x (y : B)).trans (DFunLike.congr_fun hx y)
  exact (LinearEquiv.ofBijective m.hom ⟨hinj, hsurj⟩).toModuleIso

end Iso

/-- **A ring is self-dual over itself.**  Multiplication of `R` paired with the identity
functional is perfect: `x ↦ (z ↦ x * z)` is injective because it may be evaluated at `1`, and
surjective because an `R`-linear form `k` on `R` is multiplication by `k 1`. -/
theorem isSelfDualAlgebra_self (R : Type*) [CommRing R] : IsSelfDualAlgebra R R := by
  refine ⟨LinearMap.id, ?_, ?_⟩
  · intro x y hxy
    simpa using congrArg (fun m => m (1 : R)) hxy
  · intro k
    refine ⟨k 1, LinearMap.ext fun z => ?_⟩
    show k 1 * z = k z
    rw [mul_comm (k 1) z, ← smul_eq_mul, ← k.map_smul, smul_eq_mul, mul_one]

/-- **Self-duality composes along a tower.**  If `A` is self-dual over `R` and `B` is self-dual
over `A`, then `B` is self-dual over `R`, with the composite functional `l_R = l_A ∘ l_B`. No
finiteness is assumed. -/
theorem IsSelfDualAlgebra.trans {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hA : IsSelfDualAlgebra R A) (hB : IsSelfDualAlgebra A B) : IsSelfDualAlgebra R B := by
  obtain ⟨lA, hlA⟩ := hA
  obtain ⟨lB, hlB⟩ := hB
  let eA : A ≃ₗ[R] (A →ₗ[R] R) :=
    LinearEquiv.ofBijective ((LinearMap.mul R A).compr₂ lA) hlA
  have heA (a a' : A) : eA a a' = lA (a * a') := rfl
  refine ⟨lA.comp (lB.restrictScalars R), ?_, ?_⟩
  · intro x y hxy
    apply hlB.1
    refine LinearMap.ext fun z => ?_
    show lB (x * z) = lB (y * z)
    apply hlA.1
    refine LinearMap.ext fun a => ?_
    show lA (lB (x * z) * a) = lA (lB (y * z) * a)
    have hx : lA (lB (x * (a • z))) = lA (lB (y * (a • z))) :=
      congrArg (fun m => m (a • z)) hxy
    have hsmul : ∀ w : B, lB (w * (a • z)) = a * lB (w * z) := fun w => by
      rw [mul_smul_comm, lB.map_smul, smul_eq_mul]
    rw [hsmul, hsmul] at hx
    rwa [mul_comm (lB (x * z)) a, mul_comm (lB (y * z)) a]
  · intro k
    let φ : B → (A →ₗ[R] R) := fun b =>
      { toFun := fun a => k (a • b)
        map_add' := fun a a' => by rw [add_smul, k.map_add]
        map_smul' := fun r a => by
          rw [smul_assoc, k.map_smul]
          rfl }
    have hφ (b : B) (a : A) : φ b a = k (a • b) := rfl
    have hφsmul (a' : A) (b : B) (a : A) : φ (a' • b) a = φ b (a * a') := by
      rw [hφ, hφ, smul_smul]
    let g : B →ₗ[A] A :=
      { toFun := fun b => eA.symm (φ b)
        map_add' := fun b b' => by
          rw [← eA.symm.map_add]
          congr 1
          refine LinearMap.ext fun a => ?_
          rw [hφ, LinearMap.add_apply, hφ, hφ, smul_add, k.map_add]
        map_smul' := fun a' b => by
          apply eA.injective
          rw [eA.apply_symm_apply]
          refine LinearMap.ext fun a => ?_
          rw [hφsmul, heA, smul_eq_mul, RingHom.id_apply,
            show a' * eA.symm (φ b) * a = eA.symm (φ b) * (a * a') by ring,
            ← heA, eA.apply_symm_apply] }
    obtain ⟨x, hx⟩ := hlB.2 g
    refine ⟨x, LinearMap.ext fun z => ?_⟩
    show lA (lB (x * z)) = k z
    have hz : lB (x * z) = eA.symm (φ z) := congrArg (fun m => m z) hx
    rw [hz, ← mul_one (eA.symm (φ z)), ← heA, eA.apply_symm_apply, hφ, one_smul]

end Dualizing

end

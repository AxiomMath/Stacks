module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainTowerSemilinear
public import StacksFrontier.RingTheory.Koszul.OppositeTensorCellFiltration
public import StacksFrontier.RingTheory.Koszul.PowStrictAlgebraSystem

/-!
# The transition homomorphisms of `K_N ⊗_R K_t`, and the Koszul tower of derived tensor products

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_N = R⟨ξ₁, …, ξ_r⟩` be the Koszul
differential graded algebra with `d ξᵢ = fᵢ ^ N`, and let `τ_{N,n} : K_N → K_n` be the transition
homomorphism for `1 ≤ n ≤ N`, which scales `ξᵢ` by `fᵢ ^ (N - n)`. Tensoring with a fixed `K_t`
turns the tower of Koszul algebras into a tower of left differential graded modules
`{}_N(K_N ⊗_R K_t) = ` `Koszul.powBaseTensorRestrictedModule`, and this file provides its
transition homomorphisms
$$\tau_{N,n} \otimes \mathrm{id} :
  {}_N(K_N \otimes_R K_t) \longrightarrow {}_n(K_n \otimes_R K_t)\big|_{\tau_{N,n}},$$
that is, homomorphisms of left differential graded `K_N`-modules into the restriction of scalars
along `τ_{N,n}` — `τ_{N,n}`-semilinear homomorphisms `K_N ⊗_R K_t → K_n ⊗_R K_t`.

This is the datum `DifferentialGraded.Bimodule.DerivedTensorTower.modTrans` of a tower of derived
tensor products over the varying algebras `K_{b}, K_{b+1}, K_{b+2}, …`; the other datum, the left
orthogonality `Koszul.leftOrthogonal_acyclic_powBaseTensorRestrictedModule` of these modules to
the acyclic ones, holds as well, so a tower of derived tensor products of Tag 0GZJ is obtained
from a family of differential graded `(K_{b+k}, B)`-bimodules with semilinear transition
homomorphisms and nothing else: `Koszul.powBaseTensorDerivedTensorTower`.

## Main definitions

* `DifferentialGradedModule.restrictedRegularHom'`: a homomorphism of differential graded algebras
  over a common base, as a homomorphism of the restricted regular modules. This generalizes
  `DifferentialGradedModule.restrictedRegularHom` by allowing arbitrary homomorphisms to restrict
  along, in particular composites, rather than only graded opposites of homomorphisms.
* `DifferentialGradedModule.restrictedRegularHomRestrict`: the same for a commuting square, with
  the target presented as a restriction of a restriction, which is the shape a semilinear
  transition homomorphism of restricted regular modules has.
* `Koszul.powBaseTensorTransitionHom`: **the transition homomorphism `τ_{N,n} ⊗ id` of the modules
  `{}_N(K_N ⊗_R K_t)`**, a `τ_{N,n}`-semilinear homomorphism of left differential graded modules.
* `Koszul.powBaseTensorDerivedTensorTower`: the tower of derived tensor products
  `P_k ⊗_{K_{b+k}}^𝐋 (K_{b+k} ⊗_R K_t)` built from it.

## Main results

* `Koszul.oppHom_tensorHomLeft_comp_oppHom_tensorInclLeft`: the square of algebra homomorphisms
  underlying the transition homomorphism commutes; everything else in the construction holds by
  definition.

## Implementation notes

Restriction of scalars along a composite *is* the composite of the restrictions
(`DifferentialGradedModule.restrictScalars_comp`, an equality of terms), so the target
`{}_n(K_n ⊗_R K_t)|_{τ_{N,n}}` of the transition homomorphism is the regular module of
`K_n ⊗_R K_t`, restricted along the single homomorphism
`K_N → K_n → K_n ⊗_R K_t`. That composite is not *definitionally* the graded opposite of a
homomorphism of Koszul algebras — the graded opposite of a composite is the composite of the
graded opposites only up to the identification `DifferentialGradedAlgebra.oppHom_comp`, because
the underlying module of a graded opposite algebra is produced by a choice — which is why
`DifferentialGradedModule.restrictedRegularHom` does not apply and the slightly more general
`DifferentialGradedModule.restrictedRegularHom'` is used instead. Taking that generality avoids
transporting the homomorphism along an equality of objects of the category of differential graded
modules.

The construction goes through `DifferentialGradedModule.restrictedRegularHomRestrict`, which
states the identification of the two restrictions with the one along the composite for *abstract*
differential graded algebras. Instantiating it at the Koszul algebras is then a matter of
unfolding `Koszul.powBaseTensorRestrictedModule`, with no comparison of the two actions on the
tensor product left for the kernel to do.

## References

* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGraded.Bimodule

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- **A homomorphism of differential graded algebras over a common base, as a homomorphism of the
restricted regular right modules.** If `ψ : A → B`, `χ : A → C` and `φ : B → C` are homomorphisms
of differential graded algebras with `φ ∘ ψ = χ`, then `φ` is a homomorphism of right differential
graded `A`-modules from `B` restricted along `ψ` to `C` restricted along `χ`.

This is `DifferentialGradedModule.restrictedRegularHom` without the graded opposites: there the
three homomorphisms are the graded opposites of homomorphisms of differential graded algebras,
here they are arbitrary, which is what is needed when the homomorphism to restrict along is a
composite. -/
def restrictedRegularHom' (ψ : A.Hom B) (χ : A.Hom C) (φ : B.Hom C)
    (hcomp : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = χ.toAlgebraHom a) :
    restrictScalars ψ (regularModule B) ⟶ restrictScalars χ (regularModule C) where
  toFun := φ.toAlgebraHom.toLinearMap
  map_smul x a := by
    have key : ∀ y : B.A,
        φ.toAlgebraHom (y * ψ.toAlgebraHom a) = φ.toAlgebraHom y * χ.toAlgebraHom a := by
      intro y
      rw [map_mul, hcomp]
    exact key x
  map_grading n x hx := φ.map_grading n x hx
  map_d := LinearMap.ext fun x => φ.map_d x

/-- The underlying linear map of `DifferentialGradedModule.restrictedRegularHom'` is the one of
the homomorphism of algebras it is built from. -/
theorem restrictedRegularHom'_toFun (ψ : A.Hom B) (χ : A.Hom C) (φ : B.Hom C)
    (hcomp : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = χ.toAlgebraHom a) :
    (restrictedRegularHom' ψ χ φ hcomp).toFun = φ.toAlgebraHom.toLinearMap := rfl

/-- **A commuting square of homomorphisms of differential graded algebras, as a semilinear
homomorphism of the restricted regular modules.** Let `ψ : A → B`, `φ' : A → C`, `ψ' : C → D` and
`φ : B → D` be homomorphisms of differential graded algebras with `φ ∘ ψ = ψ' ∘ φ'`. Then `φ` is a
homomorphism of right differential graded `A`-modules from `B` restricted along `ψ` to the
restriction along `φ'` of `D` restricted along `ψ'` — that is, a `φ'`-semilinear homomorphism from
the regular `B`-module to the regular `D`-module.

Restricting along `ψ'` and then along `φ'` is restricting along `ψ' ∘ φ'`
(`DifferentialGradedModule.restrictScalars_comp`), so this is
`DifferentialGradedModule.restrictedRegularHom'`; stating it with the two restrictions kept apart
is what lets it be used where the target is presented as a restriction of a module that is itself
presented as a restriction. -/
def restrictedRegularHomRestrict {D : DifferentialGradedAlgebra.{u, u} R} (ψ : A.Hom B)
    (φ' : A.Hom C) (ψ' : C.Hom D) (φ : B.Hom D)
    (hcomp : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = ψ'.toAlgebraHom (φ'.toAlgebraHom a)) :
    restrictScalars ψ (regularModule B) ⟶
      restrictScalars φ' (restrictScalars ψ' (regularModule D)) :=
  restrictedRegularHom' ψ (ψ'.comp φ') φ hcomp

/-- The underlying linear map of `DifferentialGradedModule.restrictedRegularHomRestrict` is the
one of the homomorphism of algebras it is built from. -/
theorem restrictedRegularHomRestrict_toFun {D : DifferentialGradedAlgebra.{u, u} R} (ψ : A.Hom B)
    (φ' : A.Hom C) (ψ' : C.Hom D) (φ : B.Hom D)
    (hcomp : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = ψ'.toAlgebraHom (φ'.toAlgebraHom a)) :
    (restrictedRegularHomRestrict ψ φ' ψ' φ hcomp).toFun = φ.toAlgebraHom.toLinearMap := rfl

end DifferentialGradedModule

namespace Koszul

open DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The transition homomorphism of the Koszul algebras, read on the graded opposite algebras, is
the graded opposite of the transition homomorphism. -/
theorem oppPowTransition_eq_oppHom (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    oppPowTransition f ht htm = oppHom (powTransition f ht htm) := rfl

/-- **The square of algebra homomorphisms underlying the transition homomorphism of the modules
`{}_N(K_N ⊗_R K_t)` commutes:** both `τ_{N,n} ⊗ id` after `a ↦ a ⊗ 1` and `a ↦ a ⊗ 1` after
`τ_{N,n}` send `a` to `τ_{N,n}(a) ⊗ 1`, read on the graded opposite algebras. -/
theorem oppHom_tensorHomLeft_comp_oppHom_tensorInclLeft (f : Fin r → R) (t : ℕ) {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    (oppHom (tensorHomLeft (powTransition f hn hnN) (powAlgebra f t))).comp
        (oppHom (tensorInclLeft (powAlgebra f N) (powAlgebra f t))) =
      (oppHom (tensorInclLeft (powAlgebra f n) (powAlgebra f t))).comp
        (oppPowTransition f hn hnN) := by
  rw [oppPowTransition_eq_oppHom, oppHom_comp, oppHom_comp]
  exact congrArg oppHom (hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun a =>
    tensorHomLeft_tmul (powTransition f hn hnN) (powAlgebra f t) a 1))

/-- **The transition homomorphism `τ_{N,n} ⊗ id : K_N ⊗_R K_t → K_n ⊗_R K_t` of the modules
`{}_N(K_N ⊗_R K_t)`**, as a homomorphism of left differential graded `K_N`-modules into the
restriction of scalars along `τ_{N,n}` — that is, a `τ_{N,n}`-semilinear homomorphism of left
differential graded modules.

This is the transition homomorphism of the modules that a tower of derived tensor products over
the Koszul algebras asks for; unlike `Koszul.powTransitionTensorHom`, whose target is the single
module `{}_N(K_n ⊗_R K_t)` over the fixed algebra `K_N`, its target is the module
`{}_n(K_n ⊗_R K_t)` over `K_n`, pulled back to `K_N`. -/
def powBaseTensorTransitionHom (f : Fin r → R) (t : ℕ) {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    powBaseTensorRestrictedModule f t N ⟶
      restrictScalars (oppPowTransition f hn hnN) (powBaseTensorRestrictedModule f t n) :=
  restrictedRegularHomRestrict (oppHom (tensorInclLeft (powAlgebra f N) (powAlgebra f t)))
    (oppPowTransition f hn hnN) (oppHom (tensorInclLeft (powAlgebra f n) (powAlgebra f t)))
    (oppHom (tensorHomLeft (powTransition f hn hnN) (powAlgebra f t)))
    fun a => congrArg (fun φ => φ.toAlgebraHom a)
      (oppHom_tensorHomLeft_comp_oppHom_tensorInclLeft f t hn hnN)

/-- The transition homomorphism of the modules `{}_N(K_N ⊗_R K_t)` is `τ_{N,n} ⊗ id` on underlying
modules, read on the graded opposite algebras. -/
theorem powBaseTensorTransitionHom_toFun (f : Fin r → R) (t : ℕ) {n N : ℕ} (hn : 1 ≤ n)
    (hnN : n ≤ N) :
    (powBaseTensorTransitionHom f t hn hnN).toFun =
      (oppHom
        (tensorHomLeft (powTransition f hn hnN) (powAlgebra f t))).toAlgebraHom.toLinearMap :=
  rfl

section Tower

variable {B : DifferentialGradedAlgebra.{u, u} R} (f : Fin r → R) (t : ℕ) {b : ℕ} (hb : 1 ≤ b)

/-- The transition homomorphism `K_{b+k+1} → K_{b+k}` of the Koszul system reindexed from the
base `b`, read on the graded opposite algebras. This is the transition of
`Koszul.powStrictAlgebraSystem` at `Nat.le_succ`. -/
abbrev powSuccTransition (k : ℕ) :
    (oppAlgebra (powAlgebra f (b + (k + 1)))).Hom (oppAlgebra (powAlgebra f (b + k))) :=
  oppPowTransition f (hb.trans (Nat.le_add_right b k)) (Nat.add_le_add_left (Nat.le_succ k) b)

/-- The one-step transitions of `Koszul.powStrictAlgebraSystem` are
`Koszul.powSuccTransition`. -/
theorem powStrictAlgebraSystem_trans_le_succ (k : ℕ) :
    (powStrictAlgebraSystem f hb).trans (Nat.le_succ k) = powSuccTransition f hb k := rfl

/-- **The Koszul tower of derived tensor products.** Given a family of differential graded
`(K_{b+k}, B)`-bimodules `P_k` with `τ`-semilinear transition homomorphisms
`P_{k+1} ⟶ P_k|_{τ}`, the objects `P_k ⊗_{K_{b+k}}^𝐋 (K_{b+k} ⊗_R K_t)` of `D(B, d)` and the
transition maps built from `Koszul.powBaseTensorTransitionHom` form a tower of derived tensor
products over the varying Koszul algebras. The left orthogonality of the modules to the acyclic
ones, which makes each term computed by the plain tensor product, is
`Koszul.leftOrthogonal_acyclic_powBaseTensorRestrictedModule`. -/
def powBaseTensorDerivedTensorTower
    (bimod : ∀ k : ℕ, Bimodule (oppAlgebra (powAlgebra f (b + k))) B)
    (bimodTrans : ∀ k : ℕ,
      bimod (k + 1) ⟶ Bimodule.restrictLeft (powSuccTransition f hb k) (bimod k)) :
    DerivedTensorTower B :=
  DerivedTensorTower.ofSemilinear (fun k => oppAlgebra (powAlgebra f (b + k)))
    (fun k => powSuccTransition f hb k) bimod bimodTrans
    (fun k => powBaseTensorRestrictedModule f t (b + k))
    (fun k => powBaseTensorTransitionHom f t (hb.trans (Nat.le_add_right b k))
      (Nat.add_le_add_left (Nat.le_succ k) b))
    fun k => leftOrthogonal_acyclic_powBaseTensorRestrictedModule f t (b + k)

variable (bimod : ∀ k : ℕ, Bimodule (oppAlgebra (powAlgebra f (b + k))) B)
  (bimodTrans : ∀ k : ℕ,
    bimod (k + 1) ⟶ Bimodule.restrictLeft (powSuccTransition f hb k) (bimod k))

/-- The `k`-th algebra of the Koszul tower of derived tensor products is the graded opposite of
`K_{b+k}`. -/
@[simp] theorem powBaseTensorDerivedTensorTower_alg (k : ℕ) :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).alg k =
      oppAlgebra (powAlgebra f (b + k)) := rfl

/-- The transitions of the Koszul tower of derived tensor products are the transition
homomorphisms of the Koszul algebras. -/
theorem powBaseTensorDerivedTensorTower_trans (k : ℕ) :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).trans k =
      powSuccTransition f hb k := rfl

/-- The `k`-th module of the Koszul tower of derived tensor products is `K_{b+k} ⊗_R K_t` as a
left differential graded `K_{b+k}`-module. -/
@[simp] theorem powBaseTensorDerivedTensorTower_mod (k : ℕ) :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).mod k =
      powBaseTensorRestrictedModule f t (b + k) := rfl

/-- The transitions of the modules of the Koszul tower of derived tensor products are the
semilinear transition homomorphisms `τ ⊗ id`. -/
theorem powBaseTensorDerivedTensorTower_modTrans (k : ℕ) :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).modTrans k =
      powBaseTensorTransitionHom f t (hb.trans (Nat.le_add_right b k))
        (Nat.add_le_add_left (Nat.le_succ k) b) := rfl

end Tower

end Koszul

end

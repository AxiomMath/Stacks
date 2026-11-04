module

public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrictModule
public import StacksFrontier.RingTheory.Koszul.PowBaseTensorTransition

/-!
# The two Koszul systems of modules

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_m` be the Koszul differential
graded algebra with `d ξᵢ = fᵢ ^ m` and fix `t ≥ 1`. Over the inverse system
`K_t, K_{t+1}, K_{t+2}, …` of Koszul algebras there are two inverse systems of left differential
graded modules:

* `{}_{t+n}K_t`, the algebra `K_t` with `K_{t+n}` acting through the transition homomorphism
  `τ_{t+n,t}`, whose transition homomorphisms are the identity of `K_t`; and
* `K_{t+n} ⊗_R K_t`, read over `K_{t+n}` through `a ↦ a ⊗ 1`, whose transition homomorphisms are
  the maps `τ_{t+m,t+n} ⊗ id` of `Koszul.powBaseTensorTransitionHom`.

Both are *strict*: their transition homomorphisms compose on the nose, over the composition of
the transition homomorphisms of the Koszul algebras. This file records them as
`DifferentialGraded.StrictModuleSystem`s over `Koszul.powStrictAlgebraSystem`, and hence — through
`DifferentialGraded.StrictModuleSystem.toModuleSystem` — as inverse systems of left differential
graded modules in the sense of `DifferentialGraded.ModuleSystem`, which is the shape the two
systems have to be in before they can be compared.

## Main definitions

* `DifferentialGradedModule.restrictedRegularIdHom`: a triangle of homomorphisms of differential
  graded algebras over a common target, as a semilinear homomorphism of the restricted regular
  modules whose underlying map is the identity.
* `DifferentialGraded.StrictModuleSystem.ofRestrictedRegular` and
  `DifferentialGraded.StrictModuleSystem.ofRestrictedRegularId`: a strict inverse system of
  differential graded modules whose terms are regular modules read through homomorphisms of
  algebras, built from a commuting ladder of homomorphisms of differential graded algebras.
* `Koszul.powRestrictedStrictModuleSystem`: the system `({}_{t+n}K_t)`.
* `Koszul.powBaseTensorStrictModuleSystem`: the system `(K_{t+n} ⊗_R K_t)`.
* `Koszul.powRestrictedModuleSystem` and `Koszul.powBaseTensorModuleSystem`: the two inverse
  systems of left differential graded modules they give, over `Koszul.powAlgebraSystem`.

## Main results

* `DifferentialGradedAlgebra.tensorHomLeft_comp`: tensoring a composite of homomorphisms of
  differential graded algebras with a third algebra is the composite of the tensorings.
* `DifferentialGradedModule.restrict_trans_comp`: three morphisms of restricted modules whose
  underlying linear maps compose satisfy the compatibility a strict inverse system of
  differential graded modules asks for.
* `Koszul.oppHom_tensorHomLeft_comp_oppHom_tensorHomLeft`: the homomorphisms `τ ⊗ id` compose,
  read on the graded opposite algebras.

## Implementation notes

*Why the transition homomorphisms of the first system are not the identity morphism.* The module
`{}_{t+m}K_t` is `K_t` restricted along `τ_{t+m,t}`, and the restriction along `τ_{t+m,t+n}` of
`{}_{t+n}K_t` is `K_t` restricted along `τ_{t+n,t} ∘ τ_{t+m,t+n}`. The two composites of
transition homomorphisms agree — `Koszul.oppPowTransition_comp` — but they are not the same term,
so the two modules are not the same object of the category of differential graded
`K_{t+m}`-modules and the identity of `K_t` has to be presented as a morphism between them. That
is what `DifferentialGradedModule.restrictedRegularIdHom` does; no transport along an equality of
objects is involved.

*Everything is proved over abstract algebras and instantiated.* The underlying module of a graded
opposite algebra is produced by a choice, so any expression evaluating a homomorphism of graded
opposite Koszul algebras on an element — or carrying an `R`-module structure on one of them
inside a rewrite motive — is out of the kernel's reach. The two systems below therefore cannot be
assembled by giving the fields of `DifferentialGraded.StrictModuleSystem` at the Koszul algebras
directly: its compatibility `DifferentialGraded.StrictModuleSystem.trans_comp`, which composes
underlying linear maps across `CategoryTheory.eqToHom` of an equality of objects, does not
typecheck there within any reasonable bound. Each step is instead carried out for abstract
differential graded algebras, where the same identities hold by `rfl`, and the two Koszul systems
are *applications* of the resulting constructors
`DifferentialGraded.StrictModuleSystem.ofRestrictedRegularId` and
`DifferentialGraded.StrictModuleSystem.ofRestrictedRegular`; every hypothesis those ask for is an
equation between homomorphisms of algebras, which the Koszul development already provides. For
the same reason `DifferentialGradedModule.restrictedRegularIdHom` takes the single equation
`ψ' ∘ φ' = ψ` rather than the pointwise hypothesis of
`DifferentialGradedModule.restrictedRegularHomRestrict`.

## References

* [Stacks Project, Tag 0GZ3](https://stacks.math.columbia.edu/tag/0GZ3)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGraded.Bimodule
open scoped TensorProduct

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- **Tensoring with a fixed algebra is compatible with composition:** for homomorphisms
`ε : A → B` and `ε' : B → C` of differential graded algebras and a differential graded algebra
`D`, the composite of `ε ⊗ id` and `ε' ⊗ id` is `(ε' ∘ ε) ⊗ id`. -/
theorem tensorHomLeft_comp (ε : A.Hom B) (ε' : B.Hom C)
    (D : DifferentialGradedAlgebra.{u, u} R) :
    (tensorHomLeft ε' D).comp (tensorHomLeft ε D) = tensorHomLeft (ε'.comp ε) D := by
  refine hom_eq_of_toAlgebraHom_eq
    (tensorHom_ext (AlgHom.ext fun a => ?_) (AlgHom.ext fun c => ?_))
  · show (tensorHomLeft ε' D).toAlgebraHom
      ((tensorHomLeft ε D).toAlgebraHom (a ᵍ⊗ₜ[R] (1 : D.A) : A.grading ᵍ⊗[R] D.grading)) =
      (tensorHomLeft (ε'.comp ε) D).toAlgebraHom
        (a ᵍ⊗ₜ[R] (1 : D.A) : A.grading ᵍ⊗[R] D.grading)
    rw [tensorHomLeft_tmul, tensorHomLeft_tmul, tensorHomLeft_tmul]
    rfl
  · show (tensorHomLeft ε' D).toAlgebraHom
      ((tensorHomLeft ε D).toAlgebraHom ((1 : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] D.grading)) =
      (tensorHomLeft (ε'.comp ε) D).toAlgebraHom
        ((1 : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] D.grading)
    rw [tensorHomLeft_tmul, tensorHomLeft_tmul, tensorHomLeft_tmul, map_one, map_one, map_one]

/-- The identity homomorphism of a differential graded algebra is idempotent under
composition. -/
theorem idHom_comp_idHom (A : DifferentialGradedAlgebra.{u, u} R) :
    (idHom A).comp (idHom A) = idHom A :=
  hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun _ => rfl)

/-- The underlying linear maps of two composable homomorphisms of differential graded algebras
compose to the underlying linear map of any homomorphism identified with their composite. -/
theorem toLinearMap_comp (χ : A.Hom B) (χ' : B.Hom C) (χ'' : A.Hom C) (e : χ'.comp χ = χ'') :
    χ'.toAlgebraHom.toLinearMap ∘ₗ χ.toAlgebraHom.toLinearMap =
      χ''.toAlgebraHom.toLinearMap := by
  subst e
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- The underlying map of the transport along an equality of the homomorphisms to restrict a
differential graded module along is the identity. -/
theorem eqToHom_restrictScalars_toFun_apply {φ ψ : A.Hom B} (e : φ = ψ)
    (N : DifferentialGradedModule.{u, u, u} B) (x : (restrictScalars φ N).M) :
    (eqToHom (congrArg (fun α : A.Hom B => restrictScalars α N) e)).toFun x = x := by
  subst e
  rfl

/-- **A triangle of homomorphisms of differential graded algebras over a common target, as a
semilinear homomorphism of the restricted regular modules.** If `ψ : A → B`, `φ' : A → C` and
`ψ' : C → B` satisfy `ψ' ∘ φ' = ψ`, then the identity of `B` is a `φ'`-semilinear homomorphism
from the regular `B`-module restricted along `ψ` to the one restricted along `ψ'`.

This is `DifferentialGradedModule.restrictedRegularHomRestrict` at the identity homomorphism of
`B`, with the composition hypothesis taken as an equality of homomorphisms rather than pointwise;
that is what keeps the identity homomorphism from ever being evaluated on an element. -/
def restrictedRegularIdHom (ψ : A.Hom B) (φ' : A.Hom C) (ψ' : C.Hom B)
    (hcomp : ψ'.comp φ' = ψ) :
    restrictScalars ψ (regularModule B) ⟶
      restrictScalars φ' (restrictScalars ψ' (regularModule B)) :=
  restrictedRegularHomRestrict ψ φ' ψ' (idHom B)
    fun a => congrArg (fun χ : A.Hom B => χ.toAlgebraHom a) hcomp.symm

/-- The underlying map of `DifferentialGradedModule.restrictedRegularIdHom` is the identity of
`B`. -/
theorem restrictedRegularIdHom_toFun (ψ : A.Hom B) (φ' : A.Hom C) (ψ' : C.Hom B)
    (hcomp : ψ'.comp φ' = ψ) :
    (restrictedRegularIdHom ψ φ' ψ' hcomp).toFun = (idHom B).toAlgebraHom.toLinearMap := rfl

/-- **The compatibility that a strict inverse system of differential graded modules asks for,
reduced to the composition of underlying linear maps.** For transitions `u`, `v`, `w` of the base
algebras with `v ∘ u = w` and morphisms `a`, `b`, `c` of the restricted modules, the two-step
composite of `a` and `b`, compared with `c` across the transport along `v ∘ u = w`, is determined
by the composition of the underlying linear maps. -/
theorem restrict_trans_comp {A₁ A₂ A₃ : DifferentialGradedAlgebra.{u, u} R}
    {X₁ : DifferentialGradedModule.{u, u, u} A₁} {X₂ : DifferentialGradedModule.{u, u, u} A₂}
    {X₃ : DifferentialGradedModule.{u, u, u} A₃}
    (u : A₃.Hom A₂) (v : A₂.Hom A₁) (w : A₃.Hom A₁) (e : v.comp u = w)
    (a : X₃ ⟶ restrictScalars u X₂) (b : X₂ ⟶ restrictScalars v X₁)
    (c : X₃ ⟶ restrictScalars w X₁) (habc : b.toFun ∘ₗ a.toFun = c.toFun) :
    a ≫ (restrictScalarsFunctor u).map b ≫
        eqToHom (congrArg (fun α : A₃.Hom A₁ => restrictScalars α X₁) e) = c := by
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
  exact (eqToHom_restrictScalars_toFun_apply e X₁ (b.toFun (a.toFun x))).trans
    (LinearMap.congr_fun habc x)

end DifferentialGradedModule

namespace DifferentialGraded.StrictModuleSystem

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **A strict inverse system of regular modules read through a fixed algebra.** Let `(A_n)` be a
strict inverse system of differential graded algebras, let `B` be a differential graded algebra
and let `ψ_n : A_n → B` be homomorphisms compatible with the transitions, `ψ_n ∘ τ_{m,n} = ψ_m`.
Then `B`, read over `A_n` through `ψ_n`, is a strict inverse system of differential graded
modules whose transition homomorphisms are the identity of `B`. -/
def ofRestrictedRegularId (T : StrictAlgebraSystem R) (B : DifferentialGradedAlgebra.{u, u} R)
    (ψ : ∀ n : ℕ, (T.alg n).Hom B)
    (hsq : ∀ {n m : ℕ} (h : n ≤ m), (ψ n).comp (T.trans h) = ψ m) :
    StrictModuleSystem T where
  mod n := restrictScalars (ψ n) (regularModule B)
  trans h := restrictedRegularIdHom (ψ _) (T.trans h) (ψ _) (hsq h)
  trans_comp h h' :=
    restrict_trans_comp _ _ _ (T.trans_comp h h') _ _ _
      (toLinearMap_comp _ _ _ (idHom_comp_idHom B))

/-- **A strict inverse system of regular modules read through a system of algebras.** Let `(A_n)`
be a strict inverse system of differential graded algebras, let `(B_n)` be differential graded
algebras with homomorphisms `g_{m,n} : B_m → B_n` composing on the nose, and let
`ψ_n : A_n → B_n` make the squares `g_{m,n} ∘ ψ_m = ψ_n ∘ τ_{m,n}` commute. Then `B_n`, read over
`A_n` through `ψ_n`, is a strict inverse system of differential graded modules whose transition
homomorphisms are the `g_{m,n}`. -/
def ofRestrictedRegular (T : StrictAlgebraSystem R) (B : ℕ → DifferentialGradedAlgebra.{u, u} R)
    (ψ : ∀ n : ℕ, (T.alg n).Hom (B n))
    (g : ∀ {n m : ℕ}, n ≤ m → (B m).Hom (B n))
    (hg : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k), (g h).comp (g h') = g (h.trans h'))
    (hsq : ∀ {n m : ℕ} (h : n ≤ m) (a : (T.alg m).A),
      (g h).toAlgebraHom ((ψ m).toAlgebraHom a) =
        (ψ n).toAlgebraHom ((T.trans h).toAlgebraHom a)) :
    StrictModuleSystem T where
  mod n := restrictScalars (ψ n) (regularModule (B n))
  trans h := restrictedRegularHomRestrict (ψ _) (T.trans h) (ψ _) (g h) (hsq h)
  trans_comp h h' :=
    restrict_trans_comp _ _ _ (T.trans_comp h h') _ _ _ (toLinearMap_comp _ _ _ (hg h h'))

end DifferentialGraded.StrictModuleSystem

namespace Koszul

open DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)

/-! ### The system `({}_{t+n}K_t)` -/

/-- **The transition homomorphism of the system `({}_{t+n}K_t)`:** the identity of `K_t`, read as
a homomorphism of left differential graded `K_{t+m}`-modules from `{}_{t+m}K_t` to the
restriction along `τ_{t+m,t+n}` of `{}_{t+n}K_t`. -/
def powRestrictedSystemTrans {n m : ℕ} (h : n ≤ m) :
    powRestrictedModule f ht (Nat.le_add_right t m) ⟶
      restrictScalars
        (oppPowTransition f (ht.trans (Nat.le_add_right t n)) (Nat.add_le_add_left h t))
        (powRestrictedModule f ht (Nat.le_add_right t n)) :=
  restrictedRegularIdHom (oppPowTransition f ht (Nat.le_add_right t m))
    (oppPowTransition f (ht.trans (Nat.le_add_right t n)) (Nat.add_le_add_left h t))
    (oppPowTransition f ht (Nat.le_add_right t n))
    (oppPowTransition_comp f ht (Nat.le_add_right t n) (Nat.add_le_add_left h t))

/-- The underlying map of the transition homomorphism of the system `({}_{t+n}K_t)` is the
identity of `K_t`. -/
theorem powRestrictedSystemTrans_toFun {n m : ℕ} (h : n ≤ m) :
    (powRestrictedSystemTrans f ht h).toFun =
      (idHom (oppAlgebra (powAlgebra f t))).toAlgebraHom.toLinearMap := rfl

/-- **The system `({}_{t+n}K_t)` of left differential graded modules over the Koszul algebras**,
as a strict inverse system: the `n`-th module is `K_t` with `K_{t+n}` acting through the
transition homomorphism, and the transition homomorphisms are the identity of `K_t`, which
compose on the nose. -/
def powRestrictedStrictModuleSystem : StrictModuleSystem (powStrictAlgebraSystem f ht) :=
  StrictModuleSystem.ofRestrictedRegularId (powStrictAlgebraSystem f ht)
    (oppAlgebra (powAlgebra f t)) (fun n => oppPowTransition f ht (Nat.le_add_right t n))
    fun h => oppPowTransition_comp f ht (Nat.le_add_right t _) (Nat.add_le_add_left h t)

/-- The `n`-th module of the system `({}_{t+n}K_t)` is `{}_{t+n}K_t`. -/
@[simp] theorem powRestrictedStrictModuleSystem_mod (n : ℕ) :
    (powRestrictedStrictModuleSystem f ht).mod n =
      powRestrictedModule f ht (Nat.le_add_right t n) := rfl

/-- The transition homomorphisms of the system `({}_{t+n}K_t)` are
`Koszul.powRestrictedSystemTrans`. -/
theorem powRestrictedStrictModuleSystem_trans {n m : ℕ} (h : n ≤ m) :
    (powRestrictedStrictModuleSystem f ht).trans h = powRestrictedSystemTrans f ht h := rfl

/-- The system `({}_{t+n}K_t)`, read levelwise in the derived categories of the Koszul algebras:
an inverse system of left differential graded modules over `Koszul.powAlgebraSystem`, which is
`Koszul.powStrictAlgebraSystem_toAlgebraSystem` the system underlying the strict one. That is the
spelling used, so that a projection out of this system carries the same system of algebras as one
out of a system built from the strict one; the two spellings are definitionally equal but not
syntactically, and the components of `DifferentialGraded.AlgebraSystem.restrComp` are produced by
a universal property, so a mismatch there is not decided in reasonable time. -/
def powRestrictedModuleSystem : ModuleSystem (powStrictAlgebraSystem f ht).toAlgebraSystem :=
  (powRestrictedStrictModuleSystem f ht).toModuleSystem

/-! ### The system `(K_{t+n} ⊗_R K_t)` -/

/-- **The homomorphisms `τ ⊗ id` compose**, read on the graded opposite algebras: for
`1 ≤ p ≤ n ≤ m` the composite of `τ_{m,n} ⊗ id` and `τ_{n,p} ⊗ id` is `τ_{m,p} ⊗ id`. -/
theorem oppHom_tensorHomLeft_comp_oppHom_tensorHomLeft (f : Fin r → R) (t : ℕ) {p n m : ℕ}
    (hp : 1 ≤ p) (hpn : p ≤ n) (hnm : n ≤ m) :
    (oppHom (tensorHomLeft (powTransition f hp hpn) (powAlgebra f t))).comp
        (oppHom (tensorHomLeft (powTransition f (hp.trans hpn) hnm) (powAlgebra f t))) =
      oppHom (tensorHomLeft (powTransition f hp (hpn.trans hnm)) (powAlgebra f t)) := by
  rw [oppHom_comp, tensorHomLeft_comp]
  exact congrArg (fun ψ => oppHom (tensorHomLeft ψ (powAlgebra f t)))
    (hom_eq_of_toAlgebraHom_eq (powTransition_comp f hp hpn hnm))

/-- **The system `(K_{t+n} ⊗_R K_t)` of left differential graded modules over the Koszul
algebras**, as a strict inverse system: the `n`-th module is `K_{t+n} ⊗_R K_t` read over
`K_{t+n}` through `a ↦ a ⊗ 1`, and the transition homomorphisms are
`Koszul.powBaseTensorTransitionHom`, which compose on the nose. -/
def powBaseTensorStrictModuleSystem : StrictModuleSystem (powStrictAlgebraSystem f ht) :=
  StrictModuleSystem.ofRestrictedRegular (powStrictAlgebraSystem f ht)
    (fun n => oppAlgebra (tensorProduct (powAlgebra f (t + n)) (powAlgebra f t)))
    (fun n => oppHom (tensorInclLeft (powAlgebra f (t + n)) (powAlgebra f t)))
    (fun h => oppHom (tensorHomLeft
      (powTransition f (ht.trans (Nat.le_add_right t _)) (Nat.add_le_add_left h t))
      (powAlgebra f t)))
    (fun h h' => oppHom_tensorHomLeft_comp_oppHom_tensorHomLeft f t
      (ht.trans (Nat.le_add_right t _)) (Nat.add_le_add_left h t) (Nat.add_le_add_left h' t))
    fun h a => congrArg (fun φ => φ.toAlgebraHom a)
      (oppHom_tensorHomLeft_comp_oppHom_tensorInclLeft f t
        (ht.trans (Nat.le_add_right t _)) (Nat.add_le_add_left h t))

/-- The `n`-th module of the system `(K_{t+n} ⊗_R K_t)` is `{}_{t+n}(K_{t+n} ⊗_R K_t)`. -/
@[simp] theorem powBaseTensorStrictModuleSystem_mod (n : ℕ) :
    (powBaseTensorStrictModuleSystem f ht).mod n =
      powBaseTensorRestrictedModule f t (t + n) := rfl

/-- The transition homomorphisms of the system `(K_{t+n} ⊗_R K_t)` are the maps `τ ⊗ id` of
`Koszul.powBaseTensorTransitionHom`. -/
theorem powBaseTensorStrictModuleSystem_trans {n m : ℕ} (h : n ≤ m) :
    (powBaseTensorStrictModuleSystem f ht).trans h =
      powBaseTensorTransitionHom f t (ht.trans (Nat.le_add_right t n))
        (Nat.add_le_add_left h t) := rfl

/-- The system `(K_{t+n} ⊗_R K_t)`, read levelwise in the derived categories of the Koszul
algebras: an inverse system of left differential graded modules over
`Koszul.powAlgebraSystem`, spelled as the system underlying the strict one for the reason
recorded at `Koszul.powRestrictedModuleSystem`. -/
def powBaseTensorModuleSystem : ModuleSystem (powStrictAlgebraSystem f ht).toAlgebraSystem :=
  (powBaseTensorStrictModuleSystem f ht).toModuleSystem

end Koszul

end

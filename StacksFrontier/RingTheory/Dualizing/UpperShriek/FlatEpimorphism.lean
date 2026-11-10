module

public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.Homology.Devissage.DerivedHomCoproductsLargeUniverse
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.LocalizationAway
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialBaseChangeIso

/-!
# Upper shriek along a map whose spectrum map is an open immersion

[Stacks, Tag 0C0H] computes the algebraic upper shriek functor of a ring map `φ : R → R'` whose
spectrum map `Spec(R') → Spec(R)` is an open immersion: `φ^!` is `- ⊗_R^L R'`.  This file proves
that general clause, at every polynomial presentation of `φ` and every module universe; the
clause of a localization at one element is in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.LocalizationAway`.

What the argument uses of an open immersion is that `φ` is flat, of finite presentation and an
epimorphism of rings, that is `R' ⊗_R R' = R'`; the statements below are made in that generality,
and `Dualizing.flat_finitePresentation_isEpi_of_isOpenImmersion` reads the three properties off
the open immersion.

## Main definitions

* `Dualizing.FlatEpimorphism.evalHom` — for a presentation `ψ : P = R[x_1, …, x_n] → R'`, the
  evaluation `P' = R'[x_1, …, x_n] → R'` at the images of the variables: the base change of `ψ`
  along `φ`, read through `R' ⊗_R R' = R'`.
* `Dualizing.FlatEpimorphism.evalPresentation` — that evaluation, as a polynomial presentation of
  the identity of `R'`.
* `Dualizing.FlatEpimorphism.baseChangeIso` — for an `R'`-module `N`, the identification
  `N|_P ⊗_P P' = N|_{P'}`, which is where the epimorphism property enters.
* `Dualizing.FlatEpimorphism.extendScalarsDerivedHomHomologyIso` — [Stacks, Tag 0A6A] in
  cohomology: for a flat `P → P'` and a perfect `P`-module `M`, base change carries the cohomology
  of `RHom_P(M, K)` to that of `RHom_{P'}(M ⊗_P P', K ⊗_P^L P')`.

## Main results

* `Dualizing.FlatEpimorphism.nonempty_homologyIso` — `RHom_P(R', P)` and `RHom_{P'}(R', P')`
  have the same cohomology, as `R'`-modules, in every degree.
* `Dualizing.FlatEpimorphism.nonempty_upperShriekFunctor_unitObject_iso` — **`ω_{R'/R} = R'`**
  for a flat epimorphism of finite presentation, at any presentation.
* `Dualizing.FlatEpimorphism.nonempty_upperShriekFunctor_iso_derivedTensorProduct` — `φ^!` is
  `- ⊗_R^L R'` for a flat epimorphism of finite presentation.
* `Dualizing.flat_finitePresentation_isEpi_of_isOpenImmersion` — a ring map whose spectrum map is
  an open immersion is flat, of finite presentation and an epimorphism.
* `Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion` — the
  general clause of [Stacks, Tag 0C0H].
* `Dualizing.upperShriekFunctor_iso_derivedTensorProduct_away_and_of_isOpenImmersion` —
  **[Stacks, Tag 0C0H]**, both clauses.

## Implementation notes

The source deduces the general clause from `R' ⊗_R R' = R'` and flat base change for `φ^!`,
[Stacks, Tag 0BZN] or [Stacks, Tag 0BZR], applied to the base change of `φ` along itself, which is
an isomorphism.  Here the base change is made on cohomology instead, where it is
[Stacks, Tag 0A6A] for the flat map `P → P'`, and no compatibility of projection formulas is
involved.  Writing `ψ : P → R'` for the presentation and `ψ' : P' → R'` for the evaluation, the
cohomology of `RHom_P(R', P)` is `Ext_P(R', P)` ([Stacks, Tag 0A71]), whose base change to `P'` is
`Ext_{P'}(R' ⊗_P P', P')` because `R'` is perfect over `P`; `R' ⊗_P P'` is `R'` with `P'` acting
through `ψ'`, and an `R'`-module is its own base change to `P'`, both by
`Dualizing.FlatEpimorphism.baseChangeIso`.  This compares the two cohomologies as `P'`-modules,
hence as `R'`-modules since `ψ'` is surjective.  The second complex is known: `ψ'` presents the
identity of `R'`, whose upper shriek is computed by the clause of a localization at `1 ∈ R'`
together with [Stacks, Tag 0BZJ], so `RHom_{P'}(R', P')` is `R'` in degree `n`.  Hence so is
`RHom_P(R', P)`, an object of `D(R')` with the cohomology of a single module in a single degree
being that single complex, and `φ^!(R) = RHom_P(R', P)[n] = R'`.  [Stacks, Tag 0BZU] turns this
into the statement about the functor, `φ` being flat of finite presentation, hence perfect.

The source assumes `R` Noetherian.  Nothing here needs it: an open immersion is of finite
presentation by itself, and the perfectness of `R'` over the polynomial algebra comes from
[Stacks, Tag 067J] and [Stacks, Tag 068Y] in their finite presentation forms.

## References

* [Stacks Project, Tag 0C0H](https://stacks.math.columbia.edu/tag/0C0H)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
* [Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing.FlatEpimorphism

section ExtBaseChange

variable {P P' : Type u} [CommRing P] [CommRing P'] (g : P →+* P') (hg : g.Flat)

/-- **Derived Hom out of a perfect module commutes with flat base change, degreewise.**  For a
flat `g : P → P'`, a module `M` over `P` that is perfect in degree zero, and an object `K` of
`D(P)`, extension of scalars along `g` carries the cohomology of `RHom_P(M, K)` to that of
`RHom_{P'}(M ⊗_P P', K ⊗_P^L P')`, the two base changes being read through given
identifications.  This is [Stacks, Tag 0A6A] read in cohomology. -/
def extendScalarsDerivedHomHomologyIso (M : ModuleCat.{max v u} P)
    (hM : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj M))
    (M' : ModuleCat.{max v u} P') (eM : (ModuleCat.extendScalars.{u, u, max v u} g).obj M ≅ M')
    (K : DerivedCategory (ModuleCat.{max v u} P)) (K' : DerivedCategory (ModuleCat.{max v u} P'))
    (eK : letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} g) :=
        extendScalars_preservesFiniteLimits_of_flat'.{u, v} g hg
      (ModuleCat.extendScalars.{u, u, max v u} g).mapDerivedCategory.obj K ≅ K')
    (i : ℤ) :
    (ModuleCat.extendScalars.{u, u, max v u} g).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) i).obj
          ((Dualizing.dualizingDerivedHomFunctor.{u, max u v} P K).obj
            (.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj M)))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} P') i).obj
          ((Dualizing.dualizingDerivedHomFunctor.{u, max u v} P' K').obj
            (.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} P') 0).obj M'))) := by
  let F := ModuleCat.extendScalars.{u, u, max v u} g
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v u} P) (ComplexShape.up ℤ)
  letI : F.Additive := (ModuleCat.extendRestrictScalarsAdj g).left_adjoint_additive
  letI : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat'.{u, v} g hg
  letI : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj g).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  letI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactors
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj M
  let X' := (DerivedCategory.singleFunctor (ModuleCat.{max v u} P') 0).obj M'
  let HA := (Dualizing.dualizingDerivedHomFunctor.{u, max u v} P K).obj (.op X)
  let HB := (Dualizing.dualizingDerivedHomFunctor.{u, max u v} P' K').obj (.op X')
  let eX : F.mapDerivedCategory.obj X ≅ X' :=
    (F.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} P') 0).mapIso eM
  let β := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, v}
    g F.mapDerivedCategory F.mapDerivedCategoryFactors.hom X K
  have hβ : IsIso β := Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, v}
    g F.mapDerivedCategory F.mapDerivedCategoryFactors.hom X K (Or.inl hM)
  let eHom : F.mapDerivedCategory.obj HA ≅ HB := by
    change F.mapDerivedCategory.obj ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom P).obj
      (.op X, K)) ≅ _
    exact asIso β ≪≫
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom P').mapIso (eX.symm.op.prod eK)
  exact ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F i).app HA).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} P') i).mapIso eHom

end ExtBaseChange


section Epi

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {n : ℕ}
  (ψ : MvPolynomial (Fin n) R →+* R') (hψ : ψ.comp MvPolynomial.C = algebraMap R R')

/-- The base change `MvPolynomial (Fin n) R → MvPolynomial (Fin n) R'` of `R → R'`. -/
abbrev polyMap : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R' :=
  MvPolynomial.map (algebraMap R R')

/-- The evaluation `R'[x_1, …, x_n] → R'` at the images under `ψ` of the variables. -/
def evalHom : MvPolynomial (Fin n) R' →+* R' :=
  MvPolynomial.eval₂Hom (RingHom.id R') fun i => ψ (MvPolynomial.X i)

omit [Algebra R R'] in
theorem evalHom_C (c : R') : evalHom ψ (MvPolynomial.C c) = c := by
  simp [evalHom]

omit [Algebra R R'] in
theorem evalHom_surjective : Function.Surjective (evalHom ψ) :=
  fun c => ⟨MvPolynomial.C c, evalHom_C ψ c⟩

include hψ in
theorem evalHom_comp_polyMap : (evalHom ψ).comp (polyMap (R := R) (R' := R') (n := n)) = ψ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [evalHom, polyMap, ← hψ]
  · intro i
    simp [evalHom, polyMap]

/-- The comparison `(N|_P) ⊗_P P' → N|_{P'}`, `q ⊗ m ↦ q • m`, for an `R'`-module `N`. -/
def baseChangeHom (N : ModuleCat.{max v u} R') :
    (ModuleCat.extendScalars.{u, u, max v u} (polyMap (R := R) (R' := R') (n := n))).obj
        ((ModuleCat.restrictScalars ψ).obj N) ⟶
      (ModuleCat.restrictScalars (evalHom ψ)).obj N :=
  ((ModuleCat.extendRestrictScalarsAdj.{v} (polyMap (R := R) (R' := R') (n := n))).homEquiv
    _ _).symm (ModuleCat.restrictScalarsComp'App _ (evalHom ψ) ψ
      (evalHom_comp_polyMap ψ hψ).symm N).hom

theorem baseChangeHom_tmul (N : ModuleCat.{max v u} R') (q : MvPolynomial (Fin n) R') (m : N) :
    baseChangeHom ψ hψ N (q ⊗ₜ[MvPolynomial (Fin n) R, polyMap] m) =
      (evalHom ψ q • m : N) :=
  rfl

/-- `R'[x_1, …, x_n]` as a module over `R[x_1, …, x_n]`, the left factor of the base change. -/
abbrev leftFactor (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (n : ℕ) :
    ModuleCat (MvPolynomial (Fin n) R) :=
  (ModuleCat.restrictScalars (polyMap (R := R) (R' := R') (n := n))).obj
    (ModuleCat.of (MvPolynomial (Fin n) R') (MvPolynomial (Fin n) R'))

/-- An `R'`-module read over `R[x_1, …, x_n]` through `ψ`. -/
abbrev restricted (N : ModuleCat.{max v u} R') : ModuleCat.{max v u} (MvPolynomial (Fin n) R) :=
  (ModuleCat.restrictScalars ψ).obj N

/-- A polynomial over `R'`, read in `leftFactor`. -/
def toQ (R : Type u) {R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {n : ℕ}
    (q : MvPolynomial (Fin n) R') : leftFactor R R' n := q

/-- An element of an `R'`-module, read in its restriction along `ψ`. -/
def toM {N : ModuleCat.{max v u} R'} (m : N) : restricted ψ N := m

section

variable (N : ModuleCat.{max v u} R')

local notation "P₀" => MvPolynomial (Fin n) R
local notation "P₁" => MvPolynomial (Fin n) R'
local notation "Q" => leftFactor R R' n
local notation "Mψ" => restricted ψ N

variable [Algebra.IsEpi R R']

include hψ in
/-- **Constants pass through the tensor product.**  Since `R → R'` is an epimorphism,
`c ⊗ m = 1 ⊗ c m` for a constant `c ∈ R'` of `R'[x_1, …, x_n]`. -/
theorem one_tmul_smul_eq_C_tmul (c : R') (m : N) :
    (toQ R (1 : P₁)) ⊗ₜ[P₀] (toM ψ (c • m : N)) =
      (toQ R (MvPolynomial.C c : P₁)) ⊗ₜ[P₀] (toM ψ m) := by
  let f : R' →+ R' →+ TensorProduct P₀ Q Mψ :=
    AddMonoidHom.mk' (fun c => AddMonoidHom.mk'
      (fun d => (toQ R (MvPolynomial.C c : P₁)) ⊗ₜ[P₀] (toM ψ (d • m : N)))
      (fun d d' => by rw [add_smul]; exact TensorProduct.tmul_add _ _ _))
      (fun c c' => by
        ext d
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add]
        exact TensorProduct.add_tmul _ _ _)
  have hf : ∀ (r : R) (c d : R'), f (r • c) d = f c (r • d) := by
    intro r c d
    have hr : ψ (MvPolynomial.C r) = algebraMap R R' r := by
      rw [← hψ]; rfl
    have hC : toQ R (MvPolynomial.C (r • c) : P₁) =
        (MvPolynomial.C r : P₀) • toQ R (MvPolynomial.C c : P₁) := by
      change (MvPolynomial.C (r • c) : P₁) = polyMap (MvPolynomial.C r) * MvPolynomial.C c
      rw [Algebra.smul_def, MvPolynomial.C_mul]
      simp [polyMap]
    have hm : (toM ψ ((r • d) • m : N)) = (MvPolynomial.C r : P₀) • (toM ψ (d • m : N)) := by
      change ((r • d) • m : N) = ψ (MvPolynomial.C r) • (d • m)
      rw [hr, Algebra.smul_def, mul_smul]
    change (toQ R (MvPolynomial.C (r • c) : P₁)) ⊗ₜ[P₀] (toM ψ (d • m : N)) =
      (toQ R (MvPolynomial.C c : P₁)) ⊗ₜ[P₀] (toM ψ ((r • d) • m : N))
    rw [hC, hm]
    exact TensorProduct.smul_tmul _ _ _
  let β := TensorProduct.liftAddHom f hf
  have h := congrArg β ((Algebra.isEpi_iff_forall_one_tmul_eq R R').mp inferInstance c)
  simp only [β, TensorProduct.liftAddHom_tmul] at h
  change (toQ R (MvPolynomial.C 1 : P₁)) ⊗ₜ[P₀] (toM ψ (c • m : N)) =
    (toQ R (MvPolynomial.C c : P₁)) ⊗ₜ[P₀] (toM ψ ((1 : R') • m : N)) at h
  rwa [MvPolynomial.C_1, one_smul] at h

include hψ in
/-- Every tensor `q ⊗ m` is `1 ⊗ q m`. -/
theorem one_tmul_evalHom_smul (q : P₁) (m : N) :
    (toQ R (1 : P₁)) ⊗ₜ[P₀] (toM ψ (evalHom ψ q • m : N)) = (toQ R q) ⊗ₜ[P₀] (toM ψ m) := by
  induction q using MvPolynomial.induction_on generalizing m with
  | C c => rw [evalHom_C]; exact one_tmul_smul_eq_C_tmul ψ hψ N c m
  | add p q hp hq =>
    rw [map_add, add_smul]
    change (toQ R (1 : P₁)) ⊗ₜ[P₀] (toM ψ ((evalHom ψ p • m : N)) + (toM ψ (evalHom ψ q • m : N))) =
      ((toQ R p) + (toQ R q)) ⊗ₜ[P₀] (toM ψ m)
    rw [TensorProduct.tmul_add, hp, hq, TensorProduct.add_tmul]
  | mul_X p i hp =>
    have hX : (toQ R (p * MvPolynomial.X i : P₁)) = (MvPolynomial.X i : P₀) • (toQ R p) := by
      change (p * MvPolynomial.X i : P₁) = polyMap (MvPolynomial.X i) * p
      simp [polyMap, mul_comm]
    have hm : (toM ψ (ψ (MvPolynomial.X i) • m : N)) = (MvPolynomial.X i : P₀) • (toM ψ m) := rfl
    have he : evalHom ψ (p * MvPolynomial.X i) = evalHom ψ p * ψ (MvPolynomial.X i) := by
      simp [evalHom]
    rw [he, mul_smul, hp, hX, hm]
    exact (TensorProduct.smul_tmul _ _ _).symm

include hψ in
/-- The comparison `N|_P ⊗_P P' → N|_{P'}` is bijective, its inverse being `m ↦ 1 ⊗ m`. -/
theorem baseChangeHom_bijective : Function.Bijective (baseChangeHom ψ hψ N) := by
  refine ⟨fun x y hxy => ?_, fun m => ⟨(toQ R (1 : P₁)) ⊗ₜ[P₀] (toM ψ m), ?_⟩⟩
  · have key : ∀ x : TensorProduct P₀ Q Mψ,
        (toQ R (1 : P₁)) ⊗ₜ[P₀] (toM ψ (baseChangeHom ψ hψ N x : N)) = x := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul q m => exact one_tmul_evalHom_smul ψ hψ N q m
      | add x y hx hy =>
        exact (congrArg (fun z => toQ R (1 : P₁) ⊗ₜ[P₀] toM ψ z)
          (map_add (baseChangeHom ψ hψ N).hom x y)).trans
            ((TensorProduct.tmul_add _ _ _).trans (congrArg₂ (· + ·) hx hy))
    rw [← key x, ← key y]
    exact congrArg _ hxy
  · change evalHom ψ 1 • m = m
    rw [map_one, one_smul]

/-- **Base change along `P → P'` of an `R'`-module is the module itself.**  For `R → R'` an
epimorphism, `P = R[x_1, …, x_n]`, `P' = R'[x_1, …, x_n]` and a map `ψ : P → R'` over `R`,
every `R'`-module `N` satisfies `N|_P ⊗_P P' = N|_{P'}`, the second restriction being along the
evaluation `P' → R'` at the images of the variables. -/
def baseChangeIso :
    (ModuleCat.extendScalars.{u, u, max v u} (polyMap (R := R) (R' := R') (n := n))).obj Mψ ≅
      (ModuleCat.restrictScalars (evalHom ψ)).obj N :=
  (LinearEquiv.ofBijective (baseChangeHom ψ hψ N).hom (baseChangeHom_bijective ψ hψ N)).toModuleIso

end

end Epi

section Homology

variable {P B : Type u} [CommRing P] [CommRing B] (ψ : P →+* B)

/-- **The cohomology of `RHom_ψ(K)` is that of `RHom_P(B, K)`**, as modules over `P`: both are
`Ext^q_P(B, K)`, by [Stacks, Tag 0A71] on the one side and by the comparison of `Ext` with the
cohomology of derived Hom on the other. -/
def derivedHomHomologyIso (K : DerivedCategory (ModuleCat.{max v u} P)) (q : ℤ) :
    (ModuleCat.restrictScalars ψ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj
          ((Dualizing.derivedHom.{u, v} ψ).obj K)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) q).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, max u v} P K).obj
          (.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj
            ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of B (ULift.{v} B)))))) := by
  letI : Algebra P B := ψ.toAlgebra
  let e := (Dualizing.derivedCoextendScalarsHomologyLinearEquivExt ψ
    (Dualizing.derivedHom.{u, v} ψ) (InvertibleKernel.derivedHomUnit.{u, v} ψ)).linearEquiv K q
  let M := (ModuleCat.restrictScalars ψ).obj (ModuleCat.of B (ULift.{v} B))
  let e₂ : DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj M)
      K q ≃ₗ[P] (DerivedCategory.homologyFunctor (ModuleCat.{max v u} P) q).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, max u v} P K).obj
          (.op ((DerivedCategory.singleFunctor (ModuleCat.{max v u} P) 0).obj M))) :=
    Dualizing.extIntoOmegaAtLinearEquiv.{u, max u v} P K q M
  exact (e.trans e₂).toModuleIso

end Homology

section Single

variable {A : Type u} [CommRing A]

/-- An object of `D(A)` with the cohomology of a single complex `W[-c]` is that single complex. -/
theorem nonempty_iso_single_of_homologyIso (X : DerivedCategory (ModuleCat.{max v u} A))
    (W : ModuleCat.{max v u} A) (c : ℤ)
    (h : ∀ q : ℤ, Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).obj X ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) c).obj W))) :
    Nonempty (X ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) c).obj W) := by
  have hzero : ∀ q : ℤ, q ≠ c → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} A) q).obj X) := by
    intro q hq
    obtain ⟨κ⟩ := h q
    refine IsZero.of_iso ?_ κ
    rcases lt_or_gt_of_ne hq with h | h
    · exact DerivedCategory.isZero_of_isGE _ c q h
    · exact DerivedCategory.isZero_of_isLE _ c q h
  have hLE : X.IsLE c := (DerivedCategory.isLE_iff X c).2 fun q hq => hzero q (by omega)
  have hGE : X.IsGE c := (DerivedCategory.isGE_iff X c).2 fun q hq => hzero q (by omega)
  obtain ⟨V, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X c
  obtain ⟨κc⟩ := h c
  refine ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) c).mapIso ?_⟩
  exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) c).app V).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) c).mapIso e.symm ≪≫ κc ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max v u} A) c).app W

end Single

section Main

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- The presentation of the identity of `R'` by `R'[x_1, …, x_n] → R'`, evaluation at the images
of the variables of a presentation `p` of `R → R'`. -/
def evalPresentation (p : PolynomialPresentation (algebraMap R R')) :
    PolynomialPresentation (algebraMap R' R') where
  variableCount := p.variableCount
  toRingHom := evalHom p.toRingHom
  commutes := RingHom.ext fun c => by
    rw [RingHom.comp_apply, evalHom_C]
    rfl
  surjective := evalHom_surjective _

/-- **`ω_{R'/R'} = R'` at the presentation `evalPresentation p`**, by [Stacks, Tag 0BZJ] and the
one-variable computation at the localization of `R'` away from `1`. -/
theorem nonempty_evalPresentation_upperShriek_unit (p : PolynomialPresentation (algebraMap R R')) :
    Nonempty ((evalPresentation p).upperShriekFunctor.{u, v}.obj
      (Stacks0BZE.unitObject.{u, v} R') ≅ Stacks0BZE.unitObject.{u, v} R') := by
  let : IsLocalization.Away (1 : R') R' :=
    IsLocalization.away_of_isUnit_of_bijective R' isUnit_one Function.bijective_id
  obtain ⟨e⟩ := PolynomialPresentation.nonempty_upperShriekFunctor_iso.{u, v} (algebraMap R' R')
    (evalPresentation p) (awayPresentation (1 : R') (S := R'))
  exact ⟨e.app _ ≪≫ upperShriekFunctor_unitObject_iso_away (1 : R')⟩

/-- `R[x_1, …, x_n] → R'[x_1, …, x_n]` is flat when `R → R'` is. -/
theorem polyMap_flat [Module.Flat R R'] (n : ℕ) : (polyMap (R := R) (R' := R') (n := n)).Flat := by
  let := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := R) (S := R')
  exact RingHom.flat_algebraMap_iff.mpr (flat_mvPolynomial_of_flat (Fin n))

variable [Module.Flat R R'] [Algebra.IsEpi R R'] [Algebra.FinitePresentation R R']

/-- **The relative dualizing complex of `R → R'` and that of `R' → R'` have the same cohomology.**
Write `P = R[x_1, …, x_n] → R'` for a presentation and `P' = R'[x_1, …, x_n] → R'` for the
evaluation at the images of the variables.  Then `RHom_P(R', P)` and `RHom_{P'}(R', P')` have
isomorphic cohomology in every degree.  Indeed `P → P'` is flat and `R'` is perfect over `P`, so
[Stacks, Tag 0A6A] identifies the base change to `P'` of the cohomology of the first with the
cohomology of `RHom_{P'}(R' ⊗_P P', P')`; and since `R → R'` is an epimorphism, both
`R' ⊗_P P'` and the base change of an `R'`-module are the module itself. -/
theorem nonempty_homologyIso (p : PolynomialPresentation (algebraMap R R')) (q : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R') q).obj
        ((Dualizing.derivedHom.{u, v} p.toRingHom).obj (Stacks0BZE.unitObject.{u, v} p.Poly)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} R') q).obj
        ((Dualizing.derivedHom.{u, v} (evalHom p.toRingHom)).obj
          (Stacks0BZE.unitObject.{u, v} (MvPolynomial (Fin p.variableCount) R')))) := by
  let ψ := p.toRingHom
  have hψ : ψ.comp MvPolynomial.C = algebraMap R R' := p.commutes
  let g := polyMap (R := R) (R' := R') (n := p.variableCount)
  have hg : g.Flat := polyMap_flat p.variableCount
  let ψ' := evalHom ψ
  let N₀ := ModuleCat.of R' (ULift.{v} R')
  have hM : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} p.Poly) 0).obj
        ((ModuleCat.restrictScalars ψ).obj N₀)) := by
    let : Algebra p.Poly R' := ψ.toAlgebra
    have hA : StacksDraft.Perfect.IsPerfectModule (R := p.Poly) R' :=
      p.isPerfectModule_of_flat_of_finitePresentation
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
        (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    have hU : StacksDraft.Perfect.IsPerfectModule (R := p.Poly) (ULift.{v} R') :=
      StacksDraft.Perfect.isPerfectModule_ulift R' hA
    exact StacksDraft.Perfect.isPerfect_of_iso
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} p.Poly) 0).mapIso
        (InvertibleKernel.restrictedLiftIso.{u, v} (R := p.Poly) (A := R'))) hU
  let eK : let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} g) :=
        extendScalars_preservesFiniteLimits_of_flat'.{u, v} g hg
      (ModuleCat.extendScalars.{u, u, max v u} g).mapDerivedCategory.obj
          (Stacks0BZE.unitObject.{u, v} p.Poly) ≅
        Stacks0BZE.unitObject.{u, v} (MvPolynomial (Fin p.variableCount) R') := by
    let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} g) :=
      extendScalars_preservesFiniteLimits_of_flat'.{u, v} g hg
    exact ((ModuleCat.extendScalars.{u, u, max v u} g).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of p.Poly (ULift.{max v u} p.Poly)) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} _) 0).mapIso
        (extendScalarsULiftIso.{u, v} g)
  let HX := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} R') q).obj
    ((Dualizing.derivedHom.{u, v} ψ).obj (Stacks0BZE.unitObject.{u, v} p.Poly))
  let HY := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} R') q).obj
    ((Dualizing.derivedHom.{u, v} ψ').obj
      (Stacks0BZE.unitObject.{u, v} (MvPolynomial (Fin p.variableCount) R')))
  let e : (ModuleCat.restrictScalars ψ').obj HX ≅ (ModuleCat.restrictScalars ψ').obj HY :=
    (baseChangeIso ψ hψ HX).symm ≪≫
      (ModuleCat.extendScalars.{u, u, max v u} g).mapIso
        (derivedHomHomologyIso ψ (Stacks0BZE.unitObject.{u, v} p.Poly) q) ≪≫
      extendScalarsDerivedHomHomologyIso g hg _ hM _ (baseChangeIso ψ hψ N₀) _ _ eK q ≪≫
      (derivedHomHomologyIso ψ' _ q).symm
  let : Algebra (MvPolynomial (Fin p.variableCount) R') R' := ψ'.toAlgebra
  exact ⟨(InvertibleKernel.linearEquivOfSurjectiveRestriction.{u, v} ψ'
    (evalHom_surjective ψ) HX HY e.toLinearEquiv).toModuleIso⟩

/-- **`ω_{R'/R} = R'` for a flat epimorphism of finite presentation.**  Let `R → R'` be flat, of
finite presentation and an epimorphism of rings.  Then the relative dualizing complex
`φ^!(R)` of any polynomial presentation of `R → R'` is `R'` in degree zero. -/
theorem nonempty_upperShriekFunctor_unitObject_iso (p : PolynomialPresentation (algebraMap R R')) :
    Nonempty (p.upperShriekFunctor.{u, v}.obj (Stacks0BZE.unitObject.{u, v} R) ≅
      Stacks0BZE.unitObject.{u, v} R') := by
  let n : ℤ := (p.variableCount : ℤ)
  let W := ModuleCat.of R' (ULift.{max v u} R')
  let D := DerivedCategory (ModuleCat.{max v u} R')
  let X := (Dualizing.derivedHom.{u, v} p.toRingHom).obj (Stacks0BZE.unitObject.{u, v} p.Poly)
  let Y := (Dualizing.derivedHom.{u, v} (evalHom p.toRingHom)).obj
    (Stacks0BZE.unitObject.{u, v} (MvPolynomial (Fin p.variableCount) R'))
  obtain ⟨e₁⟩ := nonempty_evalPresentation_upperShriek_unit.{u, v} p
  let eY₀ : (shiftFunctor D n).obj Y ≅ (DerivedCategory.singleFunctor _ 0).obj W :=
    (shiftFunctor D n).mapIso ((Dualizing.derivedHom.{u, v} (evalHom p.toRingHom)).mapIso
      (evalPresentation p).derivedExtensionUnitObjectIso.symm) ≪≫ e₁
  let eY : Y ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} R') n).obj W :=
    (shiftFunctorCompIsoId D n (-n) (by omega)).symm.app Y ≪≫ (shiftFunctor D (-n)).mapIso eY₀ ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat.{max v u} R')).shiftIso (-n) n 0
        (by omega)).app W
  obtain ⟨eX⟩ := nonempty_iso_single_of_homologyIso X W n fun q => by
    obtain ⟨κ⟩ := nonempty_homologyIso.{u, v} p q
    exact ⟨κ ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso eY⟩
  exact ⟨(shiftFunctor D n).mapIso ((Dualizing.derivedHom.{u, v} p.toRingHom).mapIso
      p.derivedExtensionUnitObjectIso ≪≫ eX) ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat.{max v u} R')).shiftIso n 0 n (by omega)).app W⟩

/-- **[Stacks, Tag 0C0H] for a flat epimorphism of finite presentation.**  Let `R → R'` be flat,
of finite presentation and an epimorphism of rings.  Then the algebraic upper shriek functor of
`φ : R → R'`, read at any polynomial presentation, is `- ⊗_R^L R'`. -/
theorem nonempty_upperShriekFunctor_iso_derivedTensorProduct
    (p : PolynomialPresentation (algebraMap R R')) :
    Nonempty (p.upperShriekFunctor.{u, v} ≅
      derivedTensorProductOver.{u, v} (algebraMap R R') (Stacks0BZE.unitObject.{u, v} R')) := by
  obtain ⟨e₀⟩ := p.upperShriekFunctor_iso_derivedTensorProduct.{u, v}
    (p.isPerfectModule_of_flat_of_finitePresentation
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (RingHom.finitePresentation_algebraMap.mpr inferInstance))
  obtain ⟨e₁⟩ := nonempty_upperShriekFunctor_unitObject_iso.{u, v} p
  exact ⟨e₀ ≪≫ derivedTensorProductOverIsoCongr _ e₁⟩

end Main

end Dualizing.FlatEpimorphism

namespace Dualizing

open AlgebraicGeometry

/-- **A ring map whose spectrum map is an open immersion is a flat epimorphism of finite
presentation.**  An open immersion is flat and locally of finite presentation, and these are read
off the ring map for a morphism of affine schemes; it is a monomorphism, and `Spec` is faithful, so
the ring map is an epimorphism. -/
@[ega "IV 17.9.1" "(a) ⇒ (b), special case"]
theorem flat_finitePresentation_isEpi_of_isOpenImmersion {R R' : Type u} [CommRing R]
    [CommRing R'] (φ : R →+* R') (hφ : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) :
    letI : Algebra R R' := φ.toAlgebra
    Module.Flat R R' ∧ Algebra.FinitePresentation R R' ∧ Algebra.IsEpi R R' := by
  let : Algebra R R' := φ.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · have h : (CommRingCat.ofHom φ).hom.Flat :=
      (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)
        (φ := CommRingCat.ofHom φ)).mp inferInstance
    exact RingHom.flat_algebraMap_iff.mp h
  · have h : (CommRingCat.ofHom φ).hom.FinitePresentation :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)
        (φ := CommRingCat.ofHom φ)).mp inferInstance
    exact RingHom.finitePresentation_algebraMap.mp h
  · have : Mono (Scheme.Spec.map (CommRingCat.ofHom φ).op) :=
      inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom φ)))
    have : Mono (CommRingCat.ofHom φ).op := Scheme.Spec.mono_of_mono_map this
    have : Epi (CommRingCat.ofHom (algebraMap R R')) :=
      inferInstanceAs (Epi (CommRingCat.ofHom φ).op.unop)
    exact CommRingCat.epi_iff_epi.mp this

/-- **The general clause of [Stacks, Tag 0C0H].**  Let `φ : R → R'` be a ring map such that
`Spec(R') → Spec(R)` is an open immersion.  Then `φ` admits a polynomial presentation, and the
algebraic upper shriek functor `φ^!` read at any polynomial presentation of `φ` is isomorphic to
`- ⊗_R^L R'`, at an arbitrary module universe.

The source states this for `R` Noetherian, which is not needed: an open immersion is of finite
presentation by itself.  The source's argument is that `R' ⊗_R R' = R'`, so that flat base change
along `φ` itself reduces `φ^!` to the upper shriek of an isomorphism.  The base change used here is
that of [Stacks, Tag 0A6A] on cohomology, which needs nothing beyond flatness and perfectness: it
identifies the cohomology of `ω_{R'/R} = φ^!(R)` with that of `ω_{R'/R'}` computed at the
presentation `R'[x_1, …, x_n] → R'` obtained by base change, which is `R'` by the localization
clause at `1 ∈ R'`.  So `φ^!(R) = R'`, and [Stacks, Tag 0BZU] — `φ` being flat of finite
presentation, hence perfect — gives `φ^!(K) = K ⊗_R^L R'`. -/
theorem nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) :
    Nonempty (PolynomialPresentation φ) ∧
      ∀ p : PolynomialPresentation φ, Nonempty (p.upperShriekFunctor.{u, v} ≅
        derivedTensorProductOver.{u, v} φ (Stacks0BZE.unitObject.{u, v} R')) := by
  let : Algebra R R' := φ.toAlgebra
  obtain ⟨hflat, hfp, hepi⟩ := flat_finitePresentation_isEpi_of_isOpenImmersion φ hφ
  refine ⟨nonempty_polynomialPresentation φ
    (RingHom.FiniteType.of_finitePresentation (RingHom.finitePresentation_algebraMap.mpr hfp)),
    fun p => ?_⟩
  exact FlatEpimorphism.nonempty_upperShriekFunctor_iso_derivedTensorProduct.{u, v}
    (R := R) (R' := R') p

/-- **[Stacks, Tag 0C0H].**  Let `R` be a ring.

1. For `f ∈ R` and `φ : R → R_f` the localization away from `f`, the algebraic upper shriek
   functor `φ^!`, read at any polynomial presentation of `φ`, is isomorphic to `- ⊗_R^L R_f`.
2. More generally, if `φ : R → R'` is a ring map such that `Spec(R') → Spec(R)` is an open
   immersion, then `φ` admits a polynomial presentation, and `φ^!` read at any of them is
   isomorphic to `- ⊗_R^L R'`.

Both hold at an arbitrary module universe.  `- ⊗_R^L R'` is derived tensor product over `R` with
`R'` in degree zero, `Dualizing.derivedTensorProductOver`; `R_f` is any localization of `R` away
from `f`.  The source assumes `R` Noetherian, which neither clause needs.  The first clause is
`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_away`, computed from
[Stacks, Tag 0BZH] at `R[x] → R[x]/(fx - 1)` as in the source; the second is
`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion`. -/
@[stacks 0C0H]
theorem upperShriekFunctor_iso_derivedTensorProduct_away_and_of_isOpenImmersion
    {R : Type u} [CommRing R] :
    (∀ (f : R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away f S]
        (p : PolynomialPresentation (algebraMap R S)),
        Nonempty (p.upperShriekFunctor.{u, v} ≅
          derivedTensorProductOver.{u, v} (algebraMap R S) (Stacks0BZE.unitObject.{u, v} S))) ∧
      ∀ (R' : Type u) [CommRing R'] (φ : R →+* R'),
        IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) →
          Nonempty (PolynomialPresentation φ) ∧
            ∀ p : PolynomialPresentation φ, Nonempty (p.upperShriekFunctor.{u, v} ≅
              derivedTensorProductOver.{u, v} φ (Stacks0BZE.unitObject.{u, v} R')) :=
  ⟨fun f _ _ _ _ p => nonempty_upperShriekFunctor_iso_derivedTensorProduct_away.{u, v} f p,
    fun _ _ φ hφ => nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion.{u, v}
      φ hφ⟩

end Dualizing

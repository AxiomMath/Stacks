module

public import StacksFrontier.Cotangent.Biderivation
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerRelations
public import StacksFrontier.Cotangent.NaiveComparisonChainMap
public import StacksFrontier.Cotangent.StandardResolutionConormalSquares
public import Mathlib.Tactic.Module

/-!
# The comparison map from the cotangent complex to the Lichtenbaum–Schlessinger complex

Let `P → B` be a polynomial presentation of an `A`-algebra `B` with chosen generators `f_t` of
its kernel `I`, and let `P_• → B` be the standard resolution. Following [Stacks, Tag 09CG] we
choose an `A`-algebra map `ψ : P₀ → P` over `B` and an `A`-linear map `λ : P₁ → F/TrivRel` with

`λ(x y) = ψ(d₀ x) λ(y) + ψ(d₁ y) λ(x)` and `ρ(λ(x)) = ψ(d₀ x) - ψ(d₁ x)`,

the biderivation of Tag 09CF for the bimodule structure on `F/TrivRel` given by
`(ψ ∘ d₀, ψ ∘ d₁)`. From these we obtain the three components

* `dψ ⊗ 1 : Ω_{P₀/A} ⊗ B → Ω_{P/A} ⊗ B`,
* `λ̄ : Ω_{P₁/A} ⊗ B → F ⊗ B`, `dx ↦ λ(x) ⊗ 1`,
* `q : Ω_{P₂/A} ⊗ B → Rel/TrivRel`, `dg ↦ λ(d₀ g - d₁ g + d₂ g)`,

and prove that they form a map of complexes.

## Main definitions

* `Algebra.Extension.cotangentSpaceLift`: the map out of the cotangent space of an extension
  attached to a derivation.
* `Algebra.Presentation.lsSection`: the map `ψ : P₀ → P`.
* `Algebra.Presentation.lsBiderivation`: the map `λ : P₁ → F/TrivRel`.
* `Algebra.Presentation.lsComponentZero`, `lsComponentOne`, `lsComponentTwo`: the three
  components, as linear maps out of the cotangent spaces of `P₀ → B`, `P₁ → B`, `P₂ → B`.

## Main results

* `Algebra.Presentation.lsBiderivation_mul` and
  `Algebra.Presentation.freeQuotientRelationMap_lsBiderivation`: the two properties of `λ`.
* `Algebra.Presentation.lsComponent_square_zero`, `lsComponent_square_one`,
  `lsComponent_square_two`: the three commuting squares of the diagram of the source.

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
* [Stacks Project, Tag 09CF](https://stacks.math.columbia.edu/tag/09CF)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial TensorProduct KaehlerDifferential

universe u v w

noncomputable section

/-! ### Maps out of the cotangent space of an extension -/

namespace Algebra.Extension

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (E : Algebra.Extension R S) {N : Type*} [AddCommGroup N] [Module S N] [Module R N]
  [IsScalarTower R S N]

/-- The `S`-linear map `S ⊗_P Ω_{P/R} → N`, `s ⊗ dx ↦ s D(x)`, attached to a map `D : P → N`
which is an `R`-derivation for the `P`-module structure of `N` through `P → S`. -/
def cotangentSpaceLift (D : E.Ring → N) (hadd : ∀ x y, D (x + y) = D x + D y)
    (halg : ∀ r : R, D (algebraMap R E.Ring r) = 0)
    (hmul : ∀ x y, D (x * y) = algebraMap E.Ring S x • D y + algebraMap E.Ring S y • D x) :
    E.CotangentSpace →ₗ[S] N := by
  letI : Module E.Ring N := Module.compHom N (algebraMap E.Ring S)
  haveI : IsScalarTower E.Ring S N :=
    ⟨fun x s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI : IsScalarTower R E.Ring N :=
    ⟨fun r x n => by
      change algebraMap E.Ring S (r • x) • n = r • (algebraMap E.Ring S x • n)
      rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply,
        algebraMap_smul]⟩
  let δ : Derivation R E.Ring N :=
    { toFun := D
      map_add' := hadd
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, hmul, halg, smul_zero, add_zero]
        change algebraMap E.Ring S (algebraMap R E.Ring r) • D x = r • D x
        rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
      map_one_eq_zero' := by
        have := hmul 1 1
        rw [mul_one, map_one, one_smul] at this
        simpa using this
      leibniz' := fun x y => by
        change D (x * y) = _
        rw [hmul]
        rfl }
  exact LinearMap.liftBaseChange S δ.liftKaehlerDifferential

/-- `cotangentSpaceLift` sends `s ⊗ dx` to `s • D x`. -/
theorem cotangentSpaceLift_tmul (D : E.Ring → N) (hadd : ∀ x y, D (x + y) = D x + D y)
    (halg : ∀ r : R, D (algebraMap R E.Ring r) = 0)
    (hmul : ∀ x y, D (x * y) = algebraMap E.Ring S x • D y + algebraMap E.Ring S y • D x)
    (s : S) (x : E.Ring) :
    E.cotangentSpaceLift D hadd halg hmul (s ⊗ₜ KaehlerDifferential.D R E.Ring x) = s • D x := by
  simp [cotangentSpaceLift]

end Algebra.Extension

namespace Algebra.Presentation

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
variable {X T : Type w} (P : Algebra.Presentation A B X T)

/-- The standard resolution of `B` over `A`. -/
local notation "𝒫" => (CommAlgCat.standardResolution A (CommAlgCat.of A B))

/-! ### The map `ψ : P₀ → P` -/

/-- **The choice `ψ : P₀ → P`** of [Stacks, Tag 09CG]: the `A`-algebra map `A[B] → P` sending
the variable `[b]` to the chosen preimage `σ(b)` of `b`. -/
def lsSection : (𝒫).left.obj (op ⦋0⦌) →ₐ[A] P.Ring :=
  (MvPolynomial.aeval P.σ).comp
    (CommAlgCat.standardResolutionZeroAlgEquiv A (CommAlgCat.of A B)).toAlgHom

/-- `ψ` lies over `B`. -/
theorem algebraMap_lsSection (p : (𝒫).left.obj (op ⦋0⦌)) :
    algebraMap P.Ring B (P.lsSection p) = (𝒫).hom.app (op ⦋0⦌) p := by
  have h : ((IsScalarTower.toAlgHom A P.Ring B).comp P.lsSection).comp
      (CommAlgCat.standardResolutionZeroAlgEquiv A (CommAlgCat.of A B)).symm.toAlgHom =
      ((𝒫).hom.app (op ⦋0⦌)).hom.comp
        (CommAlgCat.standardResolutionZeroAlgEquiv A (CommAlgCat.of A B)).symm.toAlgHom := by
    refine MvPolynomial.algHom_ext fun b => ?_
    have e1 : ((IsScalarTower.toAlgHom A P.Ring B).comp P.lsSection).comp
        (CommAlgCat.standardResolutionZeroAlgEquiv A (CommAlgCat.of A B)).symm.toAlgHom
          (MvPolynomial.X b) = algebraMap P.Ring B (P.σ b) := by
      simp [lsSection]
    rw [e1]
    exact (P.toExtension.algebraMap_σ b).trans
      (CommAlgCat.standardResolution_augmentation_X A (CommAlgCat.of A B) b).symm
  simpa using congrArg (fun f => f (CommAlgCat.standardResolutionZeroAlgEquiv A
    (CommAlgCat.of A B) p)) h

/-! ### The biderivation `λ : P₁ → F/TrivRel` -/

/-- The identification `P₁ = A[P₀]`. -/
abbrev lsOneEquiv : (𝒫).left.obj (op ⦋1⦌) ≃ₐ[A] MvPolynomial ((𝒫).left.obj (op ⦋0⦌)) A :=
  CommAlgCat.standardResolutionSuccAlgEquiv A (CommAlgCat.of A B) 0

/-- The left action `ψ ∘ d₀`, read on `A[P₀]`. -/
def lsLeft : MvPolynomial ((𝒫).left.obj (op ⦋0⦌)) A →ₐ[A] P.Ring :=
  (P.lsSection.comp ((𝒫).left.δ (0 : Fin 2)).hom).comp (lsOneEquiv (A := A) (B := B)).symm.toAlgHom

/-- The right action `ψ ∘ d₁`, read on `A[P₀]`. -/
def lsRight : MvPolynomial ((𝒫).left.obj (op ⦋0⦌)) A →ₐ[A] P.Ring :=
  (P.lsSection.comp ((𝒫).left.δ (1 : Fin 2)).hom).comp (lsOneEquiv (A := A) (B := B)).symm.toAlgHom

/-- For `x ∈ P₁`, the difference `ψ(d₀ x) - ψ(d₁ x)` lies in the kernel `I` of `P → B`. -/
theorem lsSection_δ_sub_mem (x : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsSection ((𝒫).left.δ (0 : Fin 2) x) - P.lsSection ((𝒫).left.δ (1 : Fin 2) x) ∈ P.ker := by
  change algebraMap P.Ring B _ = 0
  rw [map_sub, algebraMap_lsSection, algebraMap_lsSection,
    CommAlgCat.standardResolution_augmentation_δ, CommAlgCat.standardResolution_augmentation_δ,
    sub_self]

/-- The value `λ([q])`: an element of `F` with `ρ = ψ(q) - ψ([ε q])`. -/
def lsValue (q : (𝒫).left.obj (op ⦋0⦌)) : freeQuotient P :=
  Submodule.Quotient.mk (kerLift P ⟨_, P.lsSection_δ_sub_mem
    (CommAlgCat.standardResolutionX A (CommAlgCat.of A B) 0 q)⟩)

/-- `ρ(lsValue q) = lsLeft [q] - lsRight [q]`. -/
theorem freeQuotientRelationMap_lsValue (q : (𝒫).left.obj (op ⦋0⦌)) :
    freeQuotientRelationMap P (P.lsValue q) =
      P.lsLeft (MvPolynomial.X q) - P.lsRight (MvPolynomial.X q) := by
  rw [lsValue, freeQuotientRelationMap_mk, relationMap_kerLift]
  rfl

/-- The biderivation of Tag 09CF on `A[P₀]`. -/
def lsBiderivationPoly :
    Biderivation A (MvPolynomial ((𝒫).left.obj (op ⦋0⦌)) A)
      (TwistedFreeQuotient P P.lsLeft P.lsRight) :=
  (exists_biderivation_twisted P P.lsLeft P.lsRight P.lsValue
    P.freeQuotientRelationMap_lsValue).choose

/-- **The choice `λ : P₁ → F/TrivRel`** of [Stacks, Tag 09CG]: the `A`-biderivation for the
bimodule structure `(ψ ∘ d₀, ψ ∘ d₁)` whose value on the variable `[q]` of `P₁ = A[P₀]` is an
element of `F` mapping to `ψ(d₀ [q]) - ψ(d₁ [q])`. -/
def lsBiderivation (x : (𝒫).left.obj (op ⦋1⦌)) : freeQuotient P :=
  TwistedFreeQuotient.equiv P P.lsLeft P.lsRight (P.lsBiderivationPoly (lsOneEquiv x))

/-- `λ` sends the variable `[q]` of `P₁ = A[P₀]` to `lsValue q`. -/
theorem lsBiderivation_X (q : (𝒫).left.obj (op ⦋0⦌)) :
    P.lsBiderivation (CommAlgCat.standardResolutionX A (CommAlgCat.of A B) 0 q) = P.lsValue q := by
  have h := (exists_biderivation_twisted P P.lsLeft P.lsRight P.lsValue
    P.freeQuotientRelationMap_lsValue).choose_spec q
  rw [lsBiderivation, CommAlgCat.standardResolutionX, AlgEquiv.apply_symm_apply]
  exact (congrArg (TwistedFreeQuotient.equiv P P.lsLeft P.lsRight) h).trans
    (AddEquiv.apply_symm_apply _ _)

/-- `λ` is additive. -/
theorem lsBiderivation_add (x y : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsBiderivation (x + y) = P.lsBiderivation x + P.lsBiderivation y := by
  simp only [lsBiderivation, map_add]

/-- `λ` is `A`-linear. -/
theorem lsBiderivation_smul (a : A) (x : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsBiderivation (a • x) = a • P.lsBiderivation x := by
  rw [lsBiderivation, map_smul]
  exact (P.lsBiderivationPoly.toLinearMap.map_smul a _).symm ▸ rfl

/-- **The first property of `λ`**: `λ(x y) = ψ(d₀ x) λ(y) + ψ(d₁ y) λ(x)`. -/
theorem lsBiderivation_mul (x y : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsBiderivation (x * y) =
      P.lsSection ((𝒫).left.δ (0 : Fin 2) x) • P.lsBiderivation y +
        P.lsSection ((𝒫).left.δ (1 : Fin 2) y) • P.lsBiderivation x := by
  rw [lsBiderivation, map_mul]
  have h := P.lsBiderivationPoly.leibniz (lsOneEquiv x) (lsOneEquiv y)
  have h' : P.lsBiderivationPoly (lsOneEquiv x * lsOneEquiv y) =
      P.lsBiderivationPoly.toLinearMap (lsOneEquiv x * lsOneEquiv y) := rfl
  rw [h', h, map_add, TwistedFreeQuotient.equiv_smul, TwistedFreeQuotient.equiv_op_smul]
  simp only [lsLeft, lsRight, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  rfl

/-- `λ(1) = 0`. -/
theorem lsBiderivation_one : P.lsBiderivation 1 = 0 := by
  have h := P.lsBiderivation_mul 1 1
  simp only [mul_one, map_one, one_smul] at h
  exact add_eq_left.1 h.symm

/-- `λ` vanishes on the image of `A`. -/
theorem lsBiderivation_algebraMap (a : A) :
    P.lsBiderivation (algebraMap A ((𝒫).left.obj (op ⦋1⦌)) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, lsBiderivation_smul, lsBiderivation_one, smul_zero]

/-- **The second property of `λ`**: `ρ(λ(x)) = ψ(d₀ x) - ψ(d₁ x)`. -/
theorem freeQuotientRelationMap_lsBiderivation (x : (𝒫).left.obj (op ⦋1⦌)) :
    freeQuotientRelationMap P (P.lsBiderivation x) =
      P.lsSection ((𝒫).left.δ (0 : Fin 2) x) - P.lsSection ((𝒫).left.δ (1 : Fin 2) x) := by
  obtain ⟨y, rfl⟩ := (lsOneEquiv (A := A) (B := B)).symm.surjective x
  induction y using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, lsBiderivation_algebraMap, map_zero]
    simp
  | add p q hp hq =>
    rw [map_add, lsBiderivation_add, map_add, hp, hq, map_add, map_add, map_add, map_add]
    abel
  | mul_X p q hp =>
    have hw : (lsOneEquiv (A := A) (B := B)).symm (MvPolynomial.X q) =
        CommAlgCat.standardResolutionX A (CommAlgCat.of A B) 0 q := rfl
    have hl : P.lsLeft (MvPolynomial.X q) =
        P.lsSection ((𝒫).left.δ (0 : Fin 2) (CommAlgCat.standardResolutionX A
          (CommAlgCat.of A B) 0 q)) := rfl
    have hr : P.lsRight (MvPolynomial.X q) =
        P.lsSection ((𝒫).left.δ (1 : Fin 2) (CommAlgCat.standardResolutionX A
          (CommAlgCat.of A B) 0 q)) := rfl
    rw [map_mul, hw, lsBiderivation_mul, map_add, map_smul, map_smul, hp, lsBiderivation_X,
      freeQuotientRelationMap_lsValue, hl, hr, map_mul, map_mul, map_mul, map_mul, smul_eq_mul,
      smul_eq_mul]
    ring

/-! ### The three components -/

/-- The presentation `P_n → B` given by a term of the standard resolution. -/
local notation "𝓔" n => (CommAlgCat.standardResolutionExtension A (CommAlgCat.of A B) n)

omit P in
/-- The structure map `P_n → B` of the presentation `𝓔 n` is the augmentation of the standard
resolution in degree `n`. -/
theorem lsExt_algebraMap (n : ℕ) (x : (𝓔 n).Ring) :
    algebraMap (𝓔 n).Ring B x = (𝒫).hom.app (op ⦋n⦌) x := rfl

/-- The derivation `x ↦ 1 ⊗ d ψ(x)` of `P₀`. -/
def lsDerivZero (x : (𝒫).left.obj (op ⦋0⦌)) : B ⊗[P.Ring] Ω[P.Ring⁄A] :=
  (1 : B) ⊗ₜ D A P.Ring (P.lsSection x)

/-- `lsDerivZero` is additive. -/
theorem lsDerivZero_add (x y : (𝒫).left.obj (op ⦋0⦌)) :
    P.lsDerivZero (x + y) = P.lsDerivZero x + P.lsDerivZero y := by
  rw [lsDerivZero, map_add, map_add, tmul_add]; rfl

/-- `lsDerivZero` vanishes on the image of `A`. -/
theorem lsDerivZero_algebraMap (a : A) :
    P.lsDerivZero (algebraMap A ((𝒫).left.obj (op ⦋0⦌)) a) = 0 := by
  rw [lsDerivZero, AlgHom.commutes, Derivation.map_algebraMap, tmul_zero]

/-- The Leibniz rule for `lsDerivZero`, for the `P₀`-module structure through `P₀ → B`. -/
theorem lsDerivZero_mul (x y : (𝒫).left.obj (op ⦋0⦌)) :
    P.lsDerivZero (x * y) =
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) x •
      P.lsDerivZero y +
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) y •
        P.lsDerivZero x := by
  rw [lsDerivZero, map_mul, Derivation.leibniz, tmul_add, tmul_smul_eq_algebraMap_smul,
    tmul_smul_eq_algebraMap_smul, algebraMap_lsSection, algebraMap_lsSection]
  rfl

/-- **The degree `0` component** `dψ ⊗ 1 : Ω_{P₀/A} ⊗ B → Ω_{P/A} ⊗ B`. -/
def lsComponentZero : (𝓔 0).CotangentSpace →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄A] :=
  (𝓔 0).cotangentSpaceLift P.lsDerivZero P.lsDerivZero_add P.lsDerivZero_algebraMap
    P.lsDerivZero_mul

/-- `lsComponentZero` sends `1 ⊗ dx` to `1 ⊗ dψ(x)`. -/
theorem lsComponentZero_tmul (x : (𝒫).left.obj (op ⦋0⦌)) :
    P.lsComponentZero ((1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring x) = P.lsDerivZero x :=
  (Algebra.Extension.cotangentSpaceLift_tmul _ _ _ _ _ _ _).trans (one_smul _ _)

/-- The derivation `x ↦ λ(x) ⊗ 1` of `P₁`. -/
def lsDerivOne (x : (𝒫).left.obj (op ⦋1⦌)) : B ⊗[P.Ring] (T →₀ P.Ring) :=
  freeQuotientToTensor P (P.lsBiderivation x)

/-- `lsDerivOne` is additive. -/
theorem lsDerivOne_add (x y : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsDerivOne (x + y) = P.lsDerivOne x + P.lsDerivOne y := by
  rw [lsDerivOne, lsBiderivation_add, map_add]; rfl

/-- `lsDerivOne` vanishes on the image of `A`. -/
theorem lsDerivOne_algebraMap (a : A) :
    P.lsDerivOne (algebraMap A ((𝒫).left.obj (op ⦋1⦌)) a) = 0 := by
  rw [lsDerivOne, lsBiderivation_algebraMap, map_zero]

/-- The Leibniz rule for `lsDerivOne`, for the `P₁`-module structure through `P₁ → B`. -/
theorem lsDerivOne_mul (x y : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsDerivOne (x * y) =
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋1⦌) x •
      P.lsDerivOne y +
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋1⦌) y •
        P.lsDerivOne x := by
  rw [lsDerivOne, lsBiderivation_mul, map_add, freeQuotientToTensor_smul,
    freeQuotientToTensor_smul, algebraMap_lsSection, algebraMap_lsSection,
    CommAlgCat.standardResolution_augmentation_δ, CommAlgCat.standardResolution_augmentation_δ]
  rfl

/-- **The degree `-1` component** `λ̄ : Ω_{P₁/A} ⊗ B → F ⊗ B`, `dx ↦ λ(x) ⊗ 1`. -/
def lsComponentOne : (𝓔 1).CotangentSpace →ₗ[B] B ⊗[P.Ring] (T →₀ P.Ring) :=
  (𝓔 1).cotangentSpaceLift P.lsDerivOne P.lsDerivOne_add P.lsDerivOne_algebraMap
    P.lsDerivOne_mul

/-- `lsComponentOne` sends `1 ⊗ dx` to `λ(x) ⊗ 1`. -/
theorem lsComponentOne_tmul (x : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsComponentOne ((1 : B) ⊗ₜ[(𝓔 1).Ring] D A (𝓔 1).Ring x) = P.lsDerivOne x :=
  (Algebra.Extension.cotangentSpaceLift_tmul _ _ _ _ _ _ _).trans (one_smul _ _)

/-! ### The degree `-2` component -/

omit P in
/-- The simplicial identities `d₀ d₁ = d₀ d₀`, `d₀ d₂ = d₁ d₀` and `d₁ d₂ = d₁ d₁` among the
faces `P₂ → P₁ → P₀`. -/
theorem δ_δ_identities (g : (𝒫).left.obj (op ⦋2⦌)) :
    (𝒫).left.δ (0 : Fin 2) ((𝒫).left.δ (1 : Fin 3) g) =
        (𝒫).left.δ (0 : Fin 2) ((𝒫).left.δ (0 : Fin 3) g) ∧
      (𝒫).left.δ (0 : Fin 2) ((𝒫).left.δ (2 : Fin 3) g) =
        (𝒫).left.δ (1 : Fin 2) ((𝒫).left.δ (0 : Fin 3) g) ∧
      (𝒫).left.δ (1 : Fin 2) ((𝒫).left.δ (2 : Fin 3) g) =
        (𝒫).left.δ (1 : Fin 2) ((𝒫).left.δ (1 : Fin 3) g) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (CommAlgCat.apply_of_comp_eq
      ((𝒫).left.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl) g).trans
      (CommAlgCat.comp_apply _ _ _)
  · exact (CommAlgCat.apply_of_comp_eq
      ((𝒫).left.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)) g).trans
      (CommAlgCat.comp_apply _ _ _)
  · exact (CommAlgCat.apply_of_comp_eq
      ((𝒫).left.δ_comp_δ (i := (1 : Fin 2)) (j := (1 : Fin 2)) le_rfl) g).trans
      (CommAlgCat.comp_apply _ _ _)

/-- `ρ(λ(d₀ g - d₁ g + d₂ g)) = 0`: the value of `λ` on a boundary is a relation. -/
theorem freeQuotientRelationMap_lsBiderivation_faceSumTwo (g : (𝒫).left.obj (op ⦋2⦌)) :
    freeQuotientRelationMap P (P.lsBiderivation (CommAlgCat.faceSumTwo A _ g)) = 0 := by
  obtain ⟨h1, h2, h3⟩ := δ_δ_identities (A := A) (B := B) g
  rw [freeQuotientRelationMap_lsBiderivation, CommAlgCat.faceSumTwo_apply]
  simp only [map_add, map_sub, h1, h2, h3]
  abel

/-- The twisted Leibniz rule on boundaries:
`λ(∂(g h)) = ψ(d₀ d₀ g) λ(∂ h) + ψ(d₁ d₂ h) λ(∂ g)` for `∂ = d₀ - d₁ + d₂`. -/
theorem lsBiderivation_faceSumTwo_mul (g h : (𝒫).left.obj (op ⦋2⦌)) :
    P.lsBiderivation (CommAlgCat.faceSumTwo A _ (g * h)) =
      P.lsSection ((𝒫).left.δ (0 : Fin 2) ((𝒫).left.δ (0 : Fin 3) g)) •
          P.lsBiderivation (CommAlgCat.faceSumTwo A _ h) +
        P.lsSection ((𝒫).left.δ (1 : Fin 2) ((𝒫).left.δ (2 : Fin 3) h)) •
          P.lsBiderivation (CommAlgCat.faceSumTwo A _ g) := by
  obtain ⟨g1, g2, g3⟩ := δ_δ_identities (A := A) (B := B) g
  obtain ⟨k1, k2, k3⟩ := δ_δ_identities (A := A) (B := B) h
  have hc := freeQuotientRelationMap_smul_comm P
    (P.lsBiderivation ((𝒫).left.δ (0 : Fin 3) g)) (P.lsBiderivation ((𝒫).left.δ (2 : Fin 3) h))
  rw [freeQuotientRelationMap_lsBiderivation, freeQuotientRelationMap_lsBiderivation, k2,
    sub_smul, sub_smul] at hc
  simp only [CommAlgCat.faceSumTwo_apply, map_mul, lsBiderivation_add, lsBiderivation_mul,
    smul_add, g2, k3]
  have e : ∀ x y : (𝒫).left.obj (op ⦋1⦌),
      P.lsBiderivation (x - y) = P.lsBiderivation x - P.lsBiderivation y :=
    (AddMonoidHom.mk' _ P.lsBiderivation_add).map_sub
  simp only [e, lsBiderivation_mul, smul_sub, g1]
  simp only [k3] at hc
  linear_combination (norm := module) hc

/-- The relation `λ(d₀ g - d₁ g + d₂ g)` modulo trivial relations. -/
def lsRelation (g : (𝒫).left.obj (op ⦋2⦌)) : relationQuotient P :=
  (exists_relationQuotientToFree_eq P _
    (P.freeQuotientRelationMap_lsBiderivation_faceSumTwo g)).choose

/-- The image of `lsRelation g` in `F/TrivRel` is `λ(d₀ g - d₁ g + d₂ g)`. -/
theorem relationQuotientToFree_lsRelation (g : (𝒫).left.obj (op ⦋2⦌)) :
    relationQuotientToFree P (P.lsRelation g) = P.lsBiderivation (CommAlgCat.faceSumTwo A _ g) :=
  (exists_relationQuotientToFree_eq P _
    (P.freeQuotientRelationMap_lsBiderivation_faceSumTwo g)).choose_spec

/-- `lsRelation g` is the unique element of `Rel/TrivRel` whose image in `F/TrivRel` is
`λ(d₀ g - d₁ g + d₂ g)`. -/
theorem lsRelation_eq_iff (g : (𝒫).left.obj (op ⦋2⦌)) (r : relationQuotient P) :
    P.lsRelation g = r ↔
      relationQuotientToFree P r = P.lsBiderivation (CommAlgCat.faceSumTwo A _ g) := by
  rw [← relationQuotientToFree_lsRelation]
  exact ⟨fun h => h ▸ rfl, fun h => relationQuotientToFree_injective P h.symm⟩

/-- `lsRelation` is additive. -/
theorem lsRelation_add (g h : (𝒫).left.obj (op ⦋2⦌)) :
    P.lsRelation (g + h) = P.lsRelation g + P.lsRelation h := by
  rw [lsRelation_eq_iff, map_add, relationQuotientToFree_lsRelation,
    relationQuotientToFree_lsRelation, map_add, lsBiderivation_add]

/-- `lsRelation` vanishes on the image of `A`. -/
theorem lsRelation_algebraMap (a : A) :
    P.lsRelation (algebraMap A ((𝒫).left.obj (op ⦋2⦌)) a) = 0 := by
  rw [lsRelation_eq_iff, map_zero, CommAlgCat.faceSumTwo_apply]
  have hc : ∀ i : Fin 3, (𝒫).left.δ i (algebraMap A ((𝒫).left.obj (op ⦋2⦌)) a) =
      algebraMap A ((𝒫).left.obj (op ⦋1⦌)) a := fun i => ((𝒫).left.δ i).hom.commutes a
  rw [hc, hc, hc, sub_self, zero_add, lsBiderivation_algebraMap]

/-- The twisted Leibniz rule for `lsRelation`:
`q(g h) = ψ(d₀ d₀ g) q(h) + ψ(d₁ d₂ h) q(g)`. -/
theorem lsRelation_mul (g h : (𝒫).left.obj (op ⦋2⦌)) :
    P.lsRelation (g * h) =
      P.lsSection ((𝒫).left.δ (0 : Fin 2) ((𝒫).left.δ (0 : Fin 3) g)) • P.lsRelation h +
        P.lsSection ((𝒫).left.δ (1 : Fin 2) ((𝒫).left.δ (2 : Fin 3) h)) • P.lsRelation g := by
  rw [lsRelation_eq_iff, map_add, map_smul, map_smul, relationQuotientToFree_lsRelation,
    relationQuotientToFree_lsRelation, lsBiderivation_faceSumTwo_mul]

/-- The derivation `g ↦ 1 ⊗ λ(d₀ g - d₁ g + d₂ g)` of `P₂`. -/
def lsDerivTwo (g : (𝒫).left.obj (op ⦋2⦌)) : B ⊗[P.Ring] relationQuotient P :=
  (1 : B) ⊗ₜ P.lsRelation g

/-- `lsDerivTwo` is additive. -/
theorem lsDerivTwo_add (x y : (𝒫).left.obj (op ⦋2⦌)) :
    P.lsDerivTwo (x + y) = P.lsDerivTwo x + P.lsDerivTwo y := by
  rw [lsDerivTwo, lsRelation_add, tmul_add]; rfl

/-- `lsDerivTwo` vanishes on the image of `A`. -/
theorem lsDerivTwo_algebraMap (a : A) :
    P.lsDerivTwo (algebraMap A ((𝒫).left.obj (op ⦋2⦌)) a) = 0 := by
  rw [lsDerivTwo, lsRelation_algebraMap, tmul_zero]

/-- The Leibniz rule for `lsDerivTwo`, for the `P₂`-module structure through `P₂ → B`. -/
theorem lsDerivTwo_mul (x y : (𝒫).left.obj (op ⦋2⦌)) :
    P.lsDerivTwo (x * y) =
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋2⦌) x •
        P.lsDerivTwo y +
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋2⦌) y •
        P.lsDerivTwo x := by
  rw [lsDerivTwo, lsRelation_mul, tmul_add, tmul_smul_eq_algebraMap_smul,
    tmul_smul_eq_algebraMap_smul, algebraMap_lsSection, algebraMap_lsSection,
    CommAlgCat.standardResolution_augmentation_δ, CommAlgCat.standardResolution_augmentation_δ,
    CommAlgCat.standardResolution_augmentation_δ, CommAlgCat.standardResolution_augmentation_δ]
  rfl

/-- **The degree `-2` component** `q : Ω_{P₂/A} ⊗ B → Rel/TrivRel`,
`dg ↦ λ(d₀ g - d₁ g + d₂ g)`. -/
def lsComponentTwo : (𝓔 2).CotangentSpace →ₗ[B] B ⊗[P.Ring] relationQuotient P :=
  (𝓔 2).cotangentSpaceLift P.lsDerivTwo P.lsDerivTwo_add P.lsDerivTwo_algebraMap
    P.lsDerivTwo_mul

/-- `lsComponentTwo` sends `1 ⊗ dg` to `1 ⊗ lsRelation g`. -/
theorem lsComponentTwo_tmul (x : (𝒫).left.obj (op ⦋2⦌)) :
    P.lsComponentTwo ((1 : B) ⊗ₜ[(𝓔 2).Ring] D A (𝓔 2).Ring x) = P.lsDerivTwo x :=
  (Algebra.Extension.cotangentSpaceLift_tmul _ _ _ _ _ _ _).trans (one_smul _ _)

/-! ### The commuting squares -/

omit P in
/-- The map of cotangent spaces induced by the face `dᵢ : P_{n+1} → P_n` sends `1 ⊗ dx` to
`1 ⊗ d(dᵢ x)`. -/
theorem cotangentSpaceMap_face_tmul (n : ℕ) (i : Fin (n + 2))
    (x : (𝒫).left.obj (op ⦋n + 1⦌)) :
    Algebra.Extension.CotangentSpace.map
        (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) n i)
        ((1 : B) ⊗ₜ[(𝓔 (n + 1)).Ring] D A (𝓔 (n + 1)).Ring x) =
      (1 : B) ⊗ₜ[(𝓔 n).Ring] D A (𝓔 n).Ring ((𝒫).left.δ i x) :=
  (Algebra.Extension.CotangentSpace.map_tmul _ _ _).trans
    (congrArg (· ⊗ₜ[(𝓔 n).Ring] D A (𝓔 n).Ring ((𝒫).left.δ i x)) (map_one _))

/-- **The square in degrees `-1, 0`**: `d_L ∘ λ̄ = (dψ ⊗ 1) ∘ (d₀ - d₁)`. -/
theorem lsComponent_square_zero :
    relationDifferentialB P ∘ₗ P.lsComponentOne =
      P.lsComponentZero ∘ₗ
        (Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 0 0) -
          Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 0 1)) := by
  refine Algebra.Extension.cotangentSpace_hom_ext _ _ _
    fun (x : (𝒫).left.obj (op ⦋1⦌)) => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sub_apply, cotangentSpaceMap_face_tmul,
    cotangentSpaceMap_face_tmul, map_sub, lsComponentOne_tmul, lsComponentZero_tmul,
    lsComponentZero_tmul, lsDerivOne, relationDifferentialB_freeQuotientToTensor,
    freeQuotientRelationMap_lsBiderivation, lsDerivZero, lsDerivZero, map_sub, tmul_sub]

/-- `λ(x - y) = λ(x) - λ(y)`. -/
theorem lsBiderivation_sub (x y : (𝒫).left.obj (op ⦋1⦌)) :
    P.lsBiderivation (x - y) = P.lsBiderivation x - P.lsBiderivation y := by
  exact (AddMonoidHom.mk' _ P.lsBiderivation_add).map_sub x y

/-- **The square in degrees `-2, -1`**: `d_L ∘ q = λ̄ ∘ (d₀ - d₁ + d₂)`. -/
theorem lsComponent_square_one :
    letI := relationModule P
    relationBoundary P ∘ₗ P.lsComponentTwo =
      P.lsComponentOne ∘ₗ
        (Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 0) -
          Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 1) +
          Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 1 2)) := by
  let := relationModule P
  refine Algebra.Extension.cotangentSpace_hom_ext _ _ _
    fun (x : (𝒫).left.obj (op ⦋2⦌)) => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    cotangentSpaceMap_face_tmul, cotangentSpaceMap_face_tmul, cotangentSpaceMap_face_tmul,
    map_add, map_sub, lsComponentOne_tmul, lsComponentOne_tmul, lsComponentOne_tmul,
    lsComponentTwo_tmul, lsDerivTwo, relationBoundary_tmul_one, relationQuotientToFree_lsRelation,
    lsDerivOne, lsDerivOne, lsDerivOne, ← map_sub, ← map_add, CommAlgCat.faceSumTwo_apply,
    lsBiderivation_add, lsBiderivation_sub]

omit P in
/-- `d ∘ d = 0` from simplicial degree three to one. -/
theorem faceSumTwo_faceSumThree (h : (𝒫).left.obj (op ⦋3⦌)) :
    CommAlgCat.faceSumTwo A _ ((𝒫).left.δ (0 : Fin 4) h - (𝒫).left.δ (1 : Fin 4) h +
      (𝒫).left.δ (2 : Fin 4) h - (𝒫).left.δ (3 : Fin 4) h) = 0 := by
  have hdd := congrArg (fun f => f h)
    ((CommAlgCat.standardResolutionMooreComplex.{u, v} A (CommAlgCat.of A B)).d_comp_d 3 2 1)
  simp only [CategoryTheory.comp_apply] at hdd
  have hd32 : (CommAlgCat.standardResolutionMooreComplex.{u, v} A (CommAlgCat.of A B)).d 3 2 =
      (CommAlgCat.standardResolutionSimplicialAddCommGrp.{u, v} A (CommAlgCat.of A B)).δ 0 -
          (CommAlgCat.standardResolutionSimplicialAddCommGrp.{u, v} A (CommAlgCat.of A B)).δ 1 +
        (CommAlgCat.standardResolutionSimplicialAddCommGrp.{u, v} A (CommAlgCat.of A B)).δ 2 -
          (CommAlgCat.standardResolutionSimplicialAddCommGrp.{u, v} A (CommAlgCat.of A B)).δ 3 := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
      AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_four]
    simp [sub_eq_add_neg]
  rwa [hd32, CommAlgCat.standardResolutionMooreComplex_d_two_one] at hdd

/-- `lsRelation (x - y) = lsRelation x - lsRelation y`. -/
theorem lsRelation_sub (x y : (𝒫).left.obj (op ⦋2⦌)) :
    P.lsRelation (x - y) = P.lsRelation x - P.lsRelation y := by
  exact (AddMonoidHom.mk' _ P.lsRelation_add).map_sub x y

/-- **The square in degrees `-3, -2`**: `q ∘ (d₀ - d₁ + d₂ - d₃) = 0`. -/
theorem lsComponent_square_two :
    P.lsComponentTwo ∘ₗ
        (Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 0) -
          Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 1) +
          Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 2) -
          Algebra.Extension.CotangentSpace.map
            (CommAlgCat.standardResolutionExtensionFace A (CommAlgCat.of A B) 2 3)) = 0 := by
  refine Algebra.Extension.cotangentSpace_hom_ext _ _ _
    fun (x : (𝒫).left.obj (op ⦋3⦌)) => ?_
  rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sub_apply,
    cotangentSpaceMap_face_tmul, cotangentSpaceMap_face_tmul, cotangentSpaceMap_face_tmul,
    cotangentSpaceMap_face_tmul, map_sub, map_add, map_sub, lsComponentTwo_tmul,
    lsComponentTwo_tmul, lsComponentTwo_tmul, lsComponentTwo_tmul, lsDerivTwo, lsDerivTwo,
    lsDerivTwo, lsDerivTwo, ← tmul_sub, ← tmul_add, ← tmul_sub, ← lsRelation_sub,
    ← lsRelation_add, ← lsRelation_sub, LinearMap.zero_apply]
  have : P.lsRelation ((𝒫).left.δ (0 : Fin 4) x - (𝒫).left.δ (1 : Fin 4) x +
      (𝒫).left.δ (2 : Fin 4) x - (𝒫).left.δ (3 : Fin 4) x) = 0 := by
    rw [lsRelation_eq_iff, map_zero, faceSumTwo_faceSumThree, lsBiderivation_algebraMap.{u, v} P 0
      |>.symm.trans (by rw [map_zero])]
  rw [this, tmul_zero]

end Algebra.Presentation

end

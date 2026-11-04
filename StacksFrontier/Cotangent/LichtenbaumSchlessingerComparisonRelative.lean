module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonIndependence
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerFunctorialityComplex

/-!
# Relative comparison maps `L_{B/A} → L'` over a square of rings

Let `A → A'`, `B → B'` be a commutative square of rings and `P' → B'` a presentation of `B'`
over `A'` with chosen generators of its kernel. A *relative choice* is an `A`-algebra map
`ψ : P₀ → P'` lying over `B → B'`, together with an `A`-biderivation `λ : P₁ → F'/TrivRel'` for
the bimodule structure `(ψ ∘ d₀, ψ ∘ d₁)` with `ρ' ∘ λ = ψ ∘ d₀ - ψ ∘ d₁`; here `P_•` is the
standard resolution of `B` over `A`. The formulas `dψ ⊗ 1`, `λ̄`, `q` of [Stacks, Tag 09CG]
then describe a `B`-linear map of complexes `L_{B/A} → L'`, and any two maps of complexes given
by these formulas, for any two relative choices, are homotopic. This is what is needed to compare
the comparison maps of Tag 09CG along a square of rings, as in [Stacks, Tag 09D7].

## Main definitions

* `Algebra.Presentation.LichtenbaumSchlessingerRelativeChoice`: a relative choice.
* `Algebra.Presentation.IsLichtenbaumSchlessingerRelativeComparison`: a map of complexes is given
  by the formulas of the source for a relative choice.

## Main results

* `Algebra.Presentation.homotopyOfIsLichtenbaumSchlessingerRelativeComparison`: two maps of
  complexes given by the formulas for two relative choices are homotopic.

## Implementation notes

The homotopy is that of `StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonIndependence`:
for relative choices `(ψ₁, λ₁)` and `(ψ₂, λ₂)`, the `(ψ₁, ψ₂)`-biderivation `θ : P₀ → F'/TrivRel'`
with `ρ' ∘ θ = ψ₁ - ψ₂` and the derivation `u = λ₁ - λ₂ - θ ∘ d₀ + θ ∘ d₁ : P₁ → Rel'/TrivRel'`
give `dx ↦ θ(x) ⊗ 1` and `dx ↦ u(x) ⊗ 1`. The cotangent complex is lifted to the module universe
of `L'` along `ModuleCat.uliftFunctor`.

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
* [Stacks Project, Tag 09D7](https://stacks.math.columbia.edu/tag/09D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TensorProduct KaehlerDifferential
open Stacks.Cotangent

universe u u' v w

noncomputable section

namespace Algebra.Presentation

variable {A : Type u} {A' : Type u'} {B B' : Type (max u v)}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B']
variable {X' T' : Type w} (P' : Algebra.Presentation A' B' X' T')

local notation "𝒫" => (CommAlgCat.standardResolution A (CommAlgCat.of A B))
local notation "𝓔" n => (CommAlgCat.standardResolutionExtension A (CommAlgCat.of A B) n)
local notation "𝕂" => (CommAlgCat.cotangentComplex A (CommAlgCat.of A B))
local notation "𝓡" => ModuleCat.restrictScalars (algebraMap B B')

/-! ### Relative choices -/

variable (A B) in
/-- **A relative choice** for the comparison of [Stacks, Tag 09CG] along the square `A → A'`,
`B → B'`: an `A`-algebra map `ψ : P₀ → P'` over `B → B'`, and an `A`-biderivation
`λ : P₁ → F'/TrivRel'` for the bimodule structure `(ψ ∘ d₀, ψ ∘ d₁)` with
`ρ' ∘ λ = ψ ∘ d₀ - ψ ∘ d₁`. -/
structure LichtenbaumSchlessingerRelativeChoice where
  /-- The map `ψ : P₀ → P'`. -/
  ψ : (𝒫).left.obj (op ⦋0⦌) →ₐ[A] P'.Ring
  /-- `ψ` lies over `B → B'`. -/
  algebraMap_ψ : ∀ p, algebraMap P'.Ring B' (ψ p) = algebraMap B B' ((𝒫).hom.app (op ⦋0⦌) p)
  /-- The biderivation `λ : P₁ → F'/TrivRel'`. -/
  lam : (𝒫).left.obj (op ⦋1⦌) →ₗ[A] freeQuotient P'
  /-- `λ` is a biderivation for the bimodule structure `(ψ ∘ d₀, ψ ∘ d₁)`. -/
  lam_mul : ∀ x y, lam (x * y) =
    ψ ((𝒫).left.δ (0 : Fin 2) x) • lam y + ψ ((𝒫).left.δ (1 : Fin 2) y) • lam x
  /-- `ρ' ∘ λ = ψ ∘ d₀ - ψ ∘ d₁`. -/
  freeQuotientRelationMap_lam : ∀ x, freeQuotientRelationMap P' (lam x) =
    ψ ((𝒫).left.δ (0 : Fin 2) x) - ψ ((𝒫).left.δ (1 : Fin 2) x)

namespace LichtenbaumSchlessingerRelativeChoice

variable {P'} (c : LichtenbaumSchlessingerRelativeChoice A B P')

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `ρ'` vanishes on `λ(d₀ g - d₁ g + d₂ g)`. -/
theorem freeQuotientRelationMap_lam_faceSumTwo (g : (𝒫).left.obj (op ⦋2⦌)) :
    freeQuotientRelationMap P' (c.lam (CommAlgCat.faceSumTwo A _ g)) = 0 := by
  rw [c.freeQuotientRelationMap_lam, δ_faceSumTwo, sub_self]

/-- The class `q(dg) ∈ Rel'/TrivRel'` of `λ(d₀ g - d₁ g + d₂ g)`. -/
def relation (g : (𝒫).left.obj (op ⦋2⦌)) : relationQuotient P' :=
  (exists_relationQuotientToFree_eq P' _ (c.freeQuotientRelationMap_lam_faceSumTwo g)).choose

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- The image of `q(dg)` in `F'/TrivRel'` is `λ(d₀ g - d₁ g + d₂ g)`. -/
theorem relationQuotientToFree_relation (g : (𝒫).left.obj (op ⦋2⦌)) :
    relationQuotientToFree P' (c.relation g) = c.lam (CommAlgCat.faceSumTwo A _ g) :=
  (exists_relationQuotientToFree_eq P' _ (c.freeQuotientRelationMap_lam_faceSumTwo g)).choose_spec

/-! ### The homotopy between two relative choices -/

variable (c' : LichtenbaumSchlessingerRelativeChoice A B P')

local notation "e₀" => CommAlgCat.standardResolutionZeroAlgEquiv A (CommAlgCat.of A B)

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- For two relative choices, `ψ(p) - ψ'(p)` lies in the kernel of `P' → B'`. -/
theorem ψ_sub_ψ_mem (p : (𝒫).left.obj (op ⦋0⦌)) : c.ψ p - c'.ψ p ∈ P'.ker := by
  show algebraMap P'.Ring B' _ = 0
  rw [map_sub, c.algebraMap_ψ, c'.algebraMap_ψ, sub_self]

/-- A biderivation `f` with `a 1 = b 1 = 1` vanishes at `1`. -/
private theorem eq_zero_of_mul_eq_smul_add_smul {X R M : Type*} [MulOneClass X] [Semiring R]
    [AddCommGroup M] [Module R M] {f : X → M} {a b : X → R}
    (h : ∀ x y, f (x * y) = a x • f y + b y • f x) (ha : a 1 = 1) (hb : b 1 = 1) : f 1 = 0 := by
  simpa [ha, hb] using h 1 1

/-- The biderivation `θ` read on `A[B]`. -/
def differencePoly : MvPolynomial (CommAlgCat.of A B) A →ₗ[A] freeQuotient P' :=
  (exists_biderivation_freeQuotient P' (c.ψ.comp (e₀).symm.toAlgHom)
    (c'.ψ.comp (e₀).symm.toAlgHom) fun _ => c.ψ_sub_ψ_mem c' _).choose

/-- **The biderivation `θ : P₀ → F'/TrivRel'`** for the bimodule structure `(ψ, ψ')`, with
`ρ' ∘ θ = ψ - ψ'`, comparing the relative choices `c = (ψ, λ)` and `c' = (ψ', λ')`. -/
def difference : (𝒫).left.obj (op ⦋0⦌) →ₗ[A] freeQuotient P' :=
  c.differencePoly c' ∘ₗ (e₀).toLinearMap

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `θ` is a biderivation for the bimodule structure `(ψ, ψ')`. -/
theorem difference_mul (x y : (𝒫).left.obj (op ⦋0⦌)) :
    c.difference c' (x * y) = c.ψ x • c.difference c' y + c'.ψ y • c.difference c' x := by
  have h := (exists_biderivation_freeQuotient P' (c.ψ.comp (e₀).symm.toAlgHom)
    (c'.ψ.comp (e₀).symm.toAlgHom) fun _ => c.ψ_sub_ψ_mem c' _).choose_spec.1
      ((e₀) x) ((e₀) y)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, ← map_mul] at h
  exact h

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `ρ' ∘ θ = ψ - ψ'`. -/
theorem freeQuotientRelationMap_difference (x : (𝒫).left.obj (op ⦋0⦌)) :
    freeQuotientRelationMap P' (c.difference c' x) = c.ψ x - c'.ψ x := by
  have h := (exists_biderivation_freeQuotient P' (c.ψ.comp (e₀).symm.toAlgHom)
    (c'.ψ.comp (e₀).symm.toAlgHom) fun _ => c.ψ_sub_ψ_mem c' _).choose_spec.2 ((e₀) x)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply] at h
  exact h

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `θ(1) = 0`. -/
theorem difference_one : c.difference c' 1 = 0 := by
  exact eq_zero_of_mul_eq_smul_add_smul (c.difference_mul c') (map_one _) (map_one _)

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `θ` vanishes on the image of `A` in `P₀`. -/
theorem difference_algebraMap (a : A) :
    c.difference c' (algebraMap A ((𝒫).left.obj (op ⦋0⦌)) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, difference_one, smul_zero]

/-- `λ(x) - λ'(x) - θ(d₀ x) + θ(d₁ x) ∈ F'/TrivRel'`, which lies in `Rel'/TrivRel'`. -/
def correctionFree (x : (𝒫).left.obj (op ⦋1⦌)) : freeQuotient P' :=
  c.lam x - c'.lam x - c.difference c' ((𝒫).left.δ (0 : Fin 2) x) +
    c.difference c' ((𝒫).left.δ (1 : Fin 2) x)

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `ρ'` vanishes on `λ(x) - λ'(x) - θ(d₀ x) + θ(d₁ x)`. -/
theorem freeQuotientRelationMap_correctionFree (x : (𝒫).left.obj (op ⦋1⦌)) :
    freeQuotientRelationMap P' (c.correctionFree c' x) = 0 := by
  rw [correctionFree, map_add, map_sub, map_sub, c.freeQuotientRelationMap_lam,
    c'.freeQuotientRelationMap_lam, freeQuotientRelationMap_difference,
    freeQuotientRelationMap_difference]
  abel

/-- **The derivation `u : P₁ → Rel'/TrivRel'`**, `u = λ - λ' - θ ∘ d₀ + θ ∘ d₁`. -/
def correction (x : (𝒫).left.obj (op ⦋1⦌)) : relationQuotient P' :=
  (exists_relationQuotientToFree_eq P' _ (c.freeQuotientRelationMap_correctionFree c' x)).choose

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- The image of `u(x)` in `F'/TrivRel'` is `λ(x) - λ'(x) - θ(d₀ x) + θ(d₁ x)`. -/
theorem relationQuotientToFree_correction (x : (𝒫).left.obj (op ⦋1⦌)) :
    relationQuotientToFree P' (c.correction c' x) = c.correctionFree c' x :=
  (exists_relationQuotientToFree_eq P' _
    (c.freeQuotientRelationMap_correctionFree c' x)).choose_spec

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `u` is additive. -/
theorem correction_add (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction c' (x + y) = c.correction c' x + c.correction c' y := by
  apply relationQuotientToFree_injective P'
  simp only [map_add, relationQuotientToFree_correction, correctionFree]
  abel

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `u(x - y) = u(x) - u(y)`. -/
theorem correction_sub (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction c' (x - y) = c.correction c' x - c.correction c' y := by
  rw [eq_sub_iff_add_eq, ← correction_add, sub_add_cancel]

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `u` is a biderivation for the bimodule structure `(ψ ∘ d₀, ψ' ∘ d₁)`. -/
theorem correction_mul (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction c' (x * y) = c.ψ ((𝒫).left.δ (0 : Fin 2) x) • c.correction c' y +
      c'.ψ ((𝒫).left.δ (1 : Fin 2) y) • c.correction c' x := by
  apply relationQuotientToFree_injective P'
  rw [map_add, map_smul, map_smul, relationQuotientToFree_correction,
    relationQuotientToFree_correction, relationQuotientToFree_correction]
  exact freeQuotient_sub_sub_add_mul P' (fun x => c.ψ ((𝒫).left.δ (0 : Fin 2) x))
    (fun x => c.ψ ((𝒫).left.δ (1 : Fin 2) x)) (fun x => c'.ψ ((𝒫).left.δ (0 : Fin 2) x))
    (fun x => c'.ψ ((𝒫).left.δ (1 : Fin 2) x)) c.lam c'.lam
    (fun x => c.difference c' ((𝒫).left.δ (0 : Fin 2) x))
    (fun x => c.difference c' ((𝒫).left.δ (1 : Fin 2) x)) x y (c.lam_mul x y)
    (c'.lam_mul x y) (by rw [map_mul, difference_mul]) (by rw [map_mul, difference_mul])
    (c.freeQuotientRelationMap_lam x) (c'.freeQuotientRelationMap_lam y)
    (c.freeQuotientRelationMap_difference c' _) (c.freeQuotientRelationMap_difference c' _)

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `u(1) = 0`. -/
theorem correction_one : c.correction c' 1 = 0 := by
  exact eq_zero_of_mul_eq_smul_add_smul (c.correction_mul c') (by simp) (by simp)

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `u` is `A`-linear. -/
theorem correction_smul (a : A) (x : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction c' (a • x) = a • c.correction c' x := by
  apply relationQuotientToFree_injective P'
  simp only [LinearMap.map_smul_of_tower, relationQuotientToFree_correction, correctionFree,
    map_smul, smul_sub, smul_add]

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `u` vanishes on the image of `A` in `P₁`. -/
theorem correction_algebraMap (a : A) :
    c.correction c' (algebraMap A ((𝒫).left.obj (op ⦋1⦌)) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, correction_smul, correction_one, smul_zero]

end LichtenbaumSchlessingerRelativeChoice

/-! ### The formulas of the source -/

/-- **A map of complexes `L_{B/A} → L'` given by the formulas of [Stacks, Tag 09CG]** for the
relative choice `c = (ψ, λ)`: `dx ↦ dψ(x) ⊗ 1` in degree `0`, `dx ↦ λ(x) ⊗ 1` in degree `-1`,
and `dg ↦ [λ(d₀ g - d₁ g + d₂ g)]` in degree `-2`. -/
structure IsLichtenbaumSchlessingerRelativeComparison
    (c : LichtenbaumSchlessingerRelativeChoice A B P')
    (g : cotangentComplexULift.{u, v, max u' w} A B ⟶
      ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (lichtenbaumSchlessingerComplex P').complex) : Prop where
  /-- In degree `0`, `dx ↦ dψ(x) ⊗ 1`. -/
  zero : ∀ x, (lichtenbaumSchlessingerComplex P').differentialIso.hom (g.f 0 (generatorZero x)) =
    (1 : B') ⊗ₜ D A' P'.Ring (c.ψ x)
  /-- In degree `-1`, `dx ↦ λ(x) ⊗ 1`. -/
  negOne : ∀ x, (lichtenbaumSchlessingerComplex P').freeIso.hom (g.f (-1) (generatorOne x)) =
    freeQuotientToTensor P' (c.lam x)
  /-- In degree `-2`, `dg ↦ [λ(d₀ g - d₁ g + d₂ g)]`. -/
  negTwo : ∀ g', (lichtenbaumSchlessingerComplex P').relationIso.hom
    (g.f (-2) (generatorTwo g')) = (1 : B') ⊗ₜ c.relation g'

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- **A map of complexes given by the formulas for a relative choice is determined by it.** -/
theorem eq_of_isLichtenbaumSchlessingerRelativeComparison
    {c : LichtenbaumSchlessingerRelativeChoice A B P'}
    {g₁ g₂ : cotangentComplexULift.{u, v, max u' w} A B ⟶
      ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (lichtenbaumSchlessingerComplex P').complex}
    (h₁ : IsLichtenbaumSchlessingerRelativeComparison P' c g₁)
    (h₂ : IsLichtenbaumSchlessingerRelativeComparison P' c g₂) : g₁ = g₂ := by
  ext i : 1
  by_cases h0 : i = 0
  · subst h0
    rw [← cancel_mono ((𝓡).map (lichtenbaumSchlessingerComplex P').differentialIso.hom)]
    refine cotangentComplexULift_hom_ext (cotangentDegreeIsoZero (A := A) (B := B)) fun x => ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact (h₁.zero x).trans (h₂.zero x).symm
  by_cases h1 : i = -1
  · subst h1
    rw [← cancel_mono ((𝓡).map (lichtenbaumSchlessingerComplex P').freeIso.hom)]
    refine cotangentComplexULift_hom_ext (cotangentDegreeIsoOne (A := A) (B := B)) fun x => ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact (h₁.negOne x).trans (h₂.negOne x).symm
  by_cases h2 : i = -2
  · subst h2
    rw [← cancel_mono ((𝓡).map (lichtenbaumSchlessingerComplex P').relationIso.hom)]
    refine cotangentComplexULift_hom_ext (cotangentDegreeIsoTwo (A := A) (B := B)) fun x => ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact (h₁.negTwo x).trans (h₂.negTwo x).symm
  exact (Functor.map_isZero (𝓡)
    ((lichtenbaumSchlessingerComplex P').isZero_X i h2 h1 h0)).eq_of_tgt _ _

/-! ### The homotopy on cotangent spaces -/

namespace LichtenbaumSchlessingerRelativeChoice

variable {P'} (c c' : LichtenbaumSchlessingerRelativeChoice A B P')

/-- `x ↦ θ(x) ⊗ 1`. -/
def homotopyDerivZero (x : (𝒫).left.obj (op ⦋0⦌)) : B' ⊗[P'.Ring] (T' →₀ P'.Ring) :=
  freeQuotientToTensor P' (c.difference c' x)

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `x ↦ θ(x) ⊗ 1` is additive. -/
theorem homotopyDerivZero_add (x y : (𝒫).left.obj (op ⦋0⦌)) :
    c.homotopyDerivZero c' (x + y) = c.homotopyDerivZero c' x + c.homotopyDerivZero c' y := by
  rw [homotopyDerivZero, map_add, map_add]
  rfl

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `x ↦ θ(x) ⊗ 1` vanishes on the image of `A` in `P₀`. -/
theorem homotopyDerivZero_algebraMap (a : A) :
    c.homotopyDerivZero c' (algebraMap A ((𝒫).left.obj (op ⦋0⦌)) a) = 0 := by
  rw [homotopyDerivZero, c.difference_algebraMap, map_zero]

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `x ↦ θ(x) ⊗ 1` is a derivation along the augmentation `P₀ → B`. -/
theorem homotopyDerivZero_mul (x y : (𝒫).left.obj (op ⦋0⦌)) :
    c.homotopyDerivZero c' (x * y) =
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) x •
        c.homotopyDerivZero c' y +
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) y •
        c.homotopyDerivZero c' x := by
  rw [homotopyDerivZero, c.difference_mul, map_add, freeQuotientToTensor_smul,
    freeQuotientToTensor_smul, c.algebraMap_ψ, c'.algebraMap_ψ, algebraMap_smul,
    algebraMap_smul]
  rfl

/-- The degree `0` part of the homotopy, `dx ↦ θ(x) ⊗ 1 : Ω_{P₀/A} ⊗ B → F' ⊗ B'`. -/
def homotopyZero : (𝓔 0).CotangentSpace →ₗ[B] B' ⊗[P'.Ring] (T' →₀ P'.Ring) :=
  (𝓔 0).cotangentSpaceLift (c.homotopyDerivZero c') (c.homotopyDerivZero_add c')
    (c.homotopyDerivZero_algebraMap c') (c.homotopyDerivZero_mul c')

/-- `homotopyZero` sends `dx ⊗ 1` to `θ(x) ⊗ 1`. -/
theorem homotopyZero_tmul (x : (𝒫).left.obj (op ⦋0⦌)) :
    c.homotopyZero c' ((1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring x) = c.homotopyDerivZero c' x :=
  (Algebra.Extension.cotangentSpaceLift_tmul _ _ _ _ _ _ _).trans (one_smul _ _)

/-- `x ↦ u(x) ⊗ 1`. -/
def homotopyDerivOne (x : (𝒫).left.obj (op ⦋1⦌)) : B' ⊗[P'.Ring] relationQuotient P' :=
  (1 : B') ⊗ₜ c.correction c' x

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `x ↦ u(x) ⊗ 1` is additive. -/
theorem homotopyDerivOne_add (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.homotopyDerivOne c' (x + y) = c.homotopyDerivOne c' x + c.homotopyDerivOne c' y := by
  rw [homotopyDerivOne, c.correction_add, tmul_add]
  rfl

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `x ↦ u(x) ⊗ 1` vanishes on the image of `A` in `P₁`. -/
theorem homotopyDerivOne_algebraMap (a : A) :
    c.homotopyDerivOne c' (algebraMap A ((𝒫).left.obj (op ⦋1⦌)) a) = 0 := by
  rw [homotopyDerivOne, c.correction_algebraMap, tmul_zero]

omit [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'] in
/-- `x ↦ u(x) ⊗ 1` is a derivation along the augmentation `P₁ → B`. -/
theorem homotopyDerivOne_mul (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.homotopyDerivOne c' (x * y) =
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋1⦌) x •
        c.homotopyDerivOne c' y +
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋1⦌) y •
        c.homotopyDerivOne c' x := by
  rw [homotopyDerivOne, c.correction_mul, tmul_add, tmul_smul_eq_algebraMap_smul,
    tmul_smul_eq_algebraMap_smul, c.algebraMap_ψ, c'.algebraMap_ψ,
    CommAlgCat.standardResolution_augmentation_δ, CommAlgCat.standardResolution_augmentation_δ,
    algebraMap_smul, algebraMap_smul]
  rfl

/-- The degree `-1` part of the homotopy, `dx ↦ u(x) ⊗ 1 : Ω_{P₁/A} ⊗ B → Rel'/TrivRel' ⊗ B'`. -/
def homotopyOne : (𝓔 1).CotangentSpace →ₗ[B] B' ⊗[P'.Ring] relationQuotient P' :=
  (𝓔 1).cotangentSpaceLift (c.homotopyDerivOne c') (c.homotopyDerivOne_add c')
    (c.homotopyDerivOne_algebraMap c') (c.homotopyDerivOne_mul c')

/-- `homotopyOne` sends `dx ⊗ 1` to `u(x) ⊗ 1`. -/
theorem homotopyOne_tmul (x : (𝒫).left.obj (op ⦋1⦌)) :
    c.homotopyOne c' ((1 : B) ⊗ₜ[(𝓔 1).Ring] D A (𝓔 1).Ring x) = c.homotopyDerivOne c' x :=
  (Algebra.Extension.cotangentSpaceLift_tmul _ _ _ _ _ _ _).trans (one_smul _ _)

end LichtenbaumSchlessingerRelativeChoice

/-! ### The homotopy on the complexes -/

namespace LichtenbaumSchlessingerRelativeChoice

variable {P'} (c c' : LichtenbaumSchlessingerRelativeChoice A B P')

/-- The homotopy `L_{B/A}^0 → L'^{-1}`. -/
def homotopyHomZero : (cotangentComplexULift.{u, v, max u' w} A B).X 0 ⟶
    (𝓡).obj ((lichtenbaumSchlessingerComplex P').complex.X (-1)) :=
  ConcreteCategory.ofHom (C := ModuleCat B)
      (X := (cotangentComplexULift.{u, v, max u' w} A B).X 0)
      (Y := (𝓡).obj (ModuleCat.of B' (B' ⊗[P'.Ring] (T' →₀ P'.Ring))))
      (toRestrictScalarsₗ (B' ⊗[P'.Ring] (T' →₀ P'.Ring)) ∘ₗ (c.homotopyZero c' ∘ₗ
        ((cotangentDegreeIsoZero (A := A) (B := B)).hom.hom ∘ₗ uliftDown (A := A) (B := B) 0))) ≫
    (𝓡).map (lichtenbaumSchlessingerComplex P').freeIso.inv

/-- Read through `freeIso`, `homotopyHomZero` is `homotopyZero`. -/
theorem homotopyHomZero_apply (z : (cotangentComplexULift.{u, v, max u' w} A B).X 0) :
    (lichtenbaumSchlessingerComplex P').freeIso.hom (c.homotopyHomZero c' z) =
      c.homotopyZero c' ((cotangentDegreeIsoZero (A := A) (B := B)).hom z.down) :=
  Iso.inv_hom_id_apply _ _

/-- Read through `differentialIso`, `homotopyHomZero` followed by the differential
`L'^{-1} → L'^0` is `relationDifferentialB` applied to `homotopyZero`. -/
theorem homotopyHomZero_d_apply (z : (cotangentComplexULift.{u, v, max u' w} A B).X 0) :
    (lichtenbaumSchlessingerComplex P').differentialIso.hom
      ((c.homotopyHomZero c' ≫ (𝓡).map ((lichtenbaumSchlessingerComplex P').complex.d (-1) 0)) z) =
      relationDifferentialB P'
        (c.homotopyZero c' ((cotangentDegreeIsoZero (A := A) (B := B)).hom z.down)) := by
  rw [ConcreteCategory.comp_apply, ModuleCat.restrictScalars.map_apply]
  exact lsComplex_d_negOne_inv_apply P'
    (c.homotopyZero c' ((cotangentDegreeIsoZero (A := A) (B := B)).hom z.down))

/-- The homotopy `L_{B/A}^{-1} → L'^{-2}`. -/
def homotopyHomOne : (cotangentComplexULift.{u, v, max u' w} A B).X (-1) ⟶
    (𝓡).obj ((lichtenbaumSchlessingerComplex P').complex.X (-2)) :=
  ConcreteCategory.ofHom (C := ModuleCat B)
      (X := (cotangentComplexULift.{u, v, max u' w} A B).X (-1))
      (Y := (𝓡).obj (ModuleCat.of B' (B' ⊗[P'.Ring] relationQuotient P')))
      (toRestrictScalarsₗ (B' ⊗[P'.Ring] relationQuotient P') ∘ₗ (c.homotopyOne c' ∘ₗ
        ((cotangentDegreeIsoOne (A := A) (B := B)).hom.hom ∘ₗ
          uliftDown (A := A) (B := B) (-1)))) ≫
    (𝓡).map (lichtenbaumSchlessingerComplex P').relationIso.inv

/-- Read through `relationIso`, `homotopyHomOne` is `homotopyOne`. -/
theorem homotopyHomOne_apply (z : (cotangentComplexULift.{u, v, max u' w} A B).X (-1)) :
    (lichtenbaumSchlessingerComplex P').relationIso.hom (c.homotopyHomOne c' z) =
      c.homotopyOne c' ((cotangentDegreeIsoOne (A := A) (B := B)).hom z.down) :=
  Iso.inv_hom_id_apply _ _

/-- Read through `freeIso`, `homotopyHomOne` followed by the differential `L'^{-2} → L'^{-1}`
is `relationBoundary` applied to `homotopyOne`. -/
theorem homotopyHomOne_d_apply (z : (cotangentComplexULift.{u, v, max u' w} A B).X (-1)) :
    letI := relationModule P'
    (lichtenbaumSchlessingerComplex P').freeIso.hom
      ((c.homotopyHomOne c' ≫ (𝓡).map ((lichtenbaumSchlessingerComplex P').complex.d (-2) (-1)))
        z) =
      relationBoundary P'
        (c.homotopyOne c' ((cotangentDegreeIsoOne (A := A) (B := B)).hom z.down)) := by
  let := relationModule P'
  rw [ConcreteCategory.comp_apply, ModuleCat.restrictScalars.map_apply]
  exact lsComplex_d_negTwo_inv_apply P'
    (c.homotopyOne c' ((cotangentDegreeIsoOne (A := A) (B := B)).hom z.down))

/-- The homotopy, as a family of maps `L_{B/A}^i → L'^{i-1}`. -/
def homotopyHom (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
    (cotangentComplexULift.{u, v, max u' w} A B).X i ⟶
      (((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (lichtenbaumSchlessingerComplex P').complex).X j :=
  if h : i = 0 then
    eqToHom (by rw [h]) ≫ c.homotopyHomZero c' ≫
      eqToHom (by rw [show j = -1 by change j + 1 = i at hij; omega]; rfl)
  else if h' : i = -1 then
    eqToHom (by rw [h']) ≫ c.homotopyHomOne c' ≫
      eqToHom (by rw [show j = -2 by change j + 1 = i at hij; omega]; rfl)
  else 0

/-- In degree `0`, `homotopyHom` is `homotopyHomZero`. -/
theorem homotopyHom_zero (h : (ComplexShape.up ℤ).Rel (-1) 0) :
    c.homotopyHom c' 0 (-1) h = c.homotopyHomZero c' := by
  rw [homotopyHom, dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- In degree `-1`, `homotopyHom` is `homotopyHomOne`. -/
theorem homotopyHom_negOne (h : (ComplexShape.up ℤ).Rel (-2) (-1)) :
    c.homotopyHom c' (-1) (-2) h = c.homotopyHomOne c' := by
  rw [homotopyHom, dif_neg (by decide), dif_pos rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- `homotopyHom` vanishes outside degrees `0` and `-1`. -/
theorem homotopyHom_eq_zero (i j : ℤ) (h : (ComplexShape.up ℤ).Rel j i) (h0 : i ≠ 0)
    (h1 : i ≠ -1) : c.homotopyHom c' i j h = 0 := by
  rw [homotopyHom, dif_neg h0, dif_neg h1]

/-- `g` corrected by the null-homotopic map of the homotopy `(θ, u)` between `c` and `c'`. -/
def correctedMap (g : cotangentComplexULift.{u, v, max u' w} A B ⟶
    ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex) :
    cotangentComplexULift.{u, v, max u' w} A B ⟶
    ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex :=
  g + Homotopy.nullHomotopicMap' (c.homotopyHom c')

/-- The corrected map is homotopic to `g`. -/
def correctedMapHomotopy (g : cotangentComplexULift.{u, v, max u' w} A B ⟶
    ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex) :
    Homotopy (c.correctedMap c' g) g := by
  refine ((Homotopy.refl g).add (Homotopy.nullHomotopy' (c.homotopyHom c'))).trans
    (Homotopy.ofEq ?_)
  exact add_zero g

/-- In degree `0`, the corrected map is `g⁰ + d ∘ h⁰`. -/
theorem correctedMap_f_zero (g : cotangentComplexULift.{u, v, max u' w} A B ⟶
    ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex) :
    (c.correctedMap c' g).f 0 =
    g.f 0 + (c.homotopyHomZero c' ≫ (𝓡).map ((lichtenbaumSchlessingerComplex P').complex.d (-1) 0) :
      (cotangentComplexULift.{u, v, max u' w} A B).X 0 ⟶
        (((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (lichtenbaumSchlessingerComplex P').complex).X 0) := by
  show g.f 0 + (Homotopy.nullHomotopicMap' (c.homotopyHom c')).f 0 = _
  rw [Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₀ := 1) (by simp) (by simp),
    c.homotopyHom_eq_zero c' 1 0 _ (by decide) (by decide), Limits.comp_zero, zero_add,
    homotopyHom_zero]
  rfl

/-- In degree `-1`, the corrected map is `g⁻¹ + h⁰ ∘ d + d ∘ h⁻¹`. -/
theorem correctedMap_f_negOne (g : cotangentComplexULift.{u, v, max u' w} A B ⟶
    ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex) :
    (c.correctedMap c' g).f (-1) = g.f (-1) +
      ((cotangentComplexULift.{u, v, max u' w} A B).d (-1) 0 ≫ c.homotopyHomZero c' :
        (cotangentComplexULift.{u, v, max u' w} A B).X (-1) ⟶
          (((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (lichtenbaumSchlessingerComplex P').complex).X (-1)) +
      (c.homotopyHomOne c' ≫ (𝓡).map ((lichtenbaumSchlessingerComplex P').complex.d (-2) (-1)) :
        (cotangentComplexULift.{u, v, max u' w} A B).X (-1) ⟶
          (((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (lichtenbaumSchlessingerComplex P').complex).X (-1)) := by
  show g.f (-1) + (Homotopy.nullHomotopicMap' (c.homotopyHom c')).f (-1) = _
  rw [Homotopy.nullHomotopicMap'_f (k₂ := -2) (k₀ := 0) (by simp) (by simp), homotopyHom_zero,
    homotopyHom_negOne, add_assoc]
  rfl

/-- In degree `-2`, the corrected map is `g⁻² + h⁻¹ ∘ d`. -/
theorem correctedMap_f_negTwo (g : cotangentComplexULift.{u, v, max u' w} A B ⟶
    ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex) :
    (c.correctedMap c' g).f (-2) =
    g.f (-2) + ((cotangentComplexULift.{u, v, max u' w} A B).d (-2) (-1) ≫ c.homotopyHomOne c' :
      (cotangentComplexULift.{u, v, max u' w} A B).X (-2) ⟶
        (((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (lichtenbaumSchlessingerComplex P').complex).X (-2)) := by
  show g.f (-2) + (Homotopy.nullHomotopicMap' (c.homotopyHom c')).f (-2) = _
  rw [Homotopy.nullHomotopicMap'_f (k₂ := -3) (k₀ := -1) (by simp) (by simp), homotopyHom_negOne,
    c.homotopyHom_eq_zero c' (-2) (-3) _ (by decide) (by decide), Limits.zero_comp, add_zero]

end LichtenbaumSchlessingerRelativeChoice

/-! ### The corrected map is given by the formulas for the other choice -/

omit P' in
/-- A morphism of modules is additive on the module with restricted scalars. -/
theorem restrictScalars_hom_add {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    {M N : ModuleCat S} (h : M ⟶ N) (a b : (ModuleCat.restrictScalars φ).obj M) :
    h (a + b) = h a + h b :=
  map_add h.hom a b

namespace LichtenbaumSchlessingerRelativeChoice

variable {P'} (c c' : LichtenbaumSchlessingerRelativeChoice A B P')

/-- If `g` is given by the formulas for `c'`, then in degree `0` the corrected map sends `dx`
to `dψ(x) ⊗ 1`, for `ψ` the map of `c`. -/
theorem correctedMap_zero
    {g : cotangentComplexULift.{u, v, max u' w} A B ⟶
      ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex}
    (h : IsLichtenbaumSchlessingerRelativeComparison P' c' g)
    (x : (𝒫).left.obj (op ⦋0⦌)) :
    (lichtenbaumSchlessingerComplex P').differentialIso.hom
      ((c.correctedMap c' g).f 0 (generatorZero x)) = (1 : B') ⊗ₜ D A' P'.Ring (c.ψ x) := by
  rw [correctedMap_f_zero, moduleCat_add_apply, restrictScalars_hom_add (algebraMap B B'), h.zero x,
    homotopyHomZero_d_apply,
    generatorZero, uliftUp_down, Iso.inv_hom_id_apply, homotopyZero_tmul, homotopyDerivZero,
    relationDifferentialB_freeQuotientToTensor, freeQuotientRelationMap_difference, map_sub,
    tmul_sub, add_sub_cancel]

/-- If `g` is given by the formulas for `c'`, then in degree `-1` the corrected map sends `dx`
to `λ(x) ⊗ 1`, for `λ` the biderivation of `c`. -/
theorem correctedMap_negOne
    {g : cotangentComplexULift.{u, v, max u' w} A B ⟶
      ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex}
    (h : IsLichtenbaumSchlessingerRelativeComparison P' c' g)
    (x : (𝒫).left.obj (op ⦋1⦌)) :
    (lichtenbaumSchlessingerComplex P').freeIso.hom
      ((c.correctedMap c' g).f (-1) (generatorOne x)) = freeQuotientToTensor P' (c.lam x) := by
  let := relationModule P'
  have hd : (cotangentDegreeIsoZero (A := A) (B := B)).hom
      ((cotangentComplexULift.{u, v, max u' w} A B).d (-1) 0 (generatorOne x)).down =
      (1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring ((𝒫).left.δ (0 : Fin 2) x) -
        (1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring ((𝒫).left.δ (1 : Fin 2) x) := by
    rw [cotangentComplexULift_d_apply, cotangentComplex_d_negOne_zero_apply, generatorOne,
      uliftUp_down, Iso.inv_hom_id_apply, LinearMap.sub_apply, cotangentSpaceMap_face_tmul,
      cotangentSpaceMap_face_tmul]
  rw [correctedMap_f_negOne, moduleCat_add_apply, moduleCat_add_apply,
    restrictScalars_hom_add (algebraMap B B'),
    restrictScalars_hom_add (algebraMap B B'),
    h.negOne x, ConcreteCategory.comp_apply, homotopyHomZero_apply, hd, map_sub,
    homotopyZero_tmul, homotopyZero_tmul, homotopyHomOne_d_apply, generatorOne, uliftUp_down,
    Iso.inv_hom_id_apply, homotopyOne_tmul, homotopyDerivOne, relationBoundary_tmul_one,
    relationQuotientToFree_correction, homotopyDerivZero, homotopyDerivZero, ← map_sub,
    ← map_add, ← map_add, correctionFree]
  congr 1
  abel

/-- If `g` is given by the formulas for `c'`, then in degree `-2` the corrected map sends `dg`
to `[λ(d₀ g - d₁ g + d₂ g)]`, for `λ` the biderivation of `c`. -/
theorem correctedMap_negTwo
    {g : cotangentComplexULift.{u, v, max u' w} A B ⟶
      ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex}
    (h : IsLichtenbaumSchlessingerRelativeComparison P' c' g)
    (g' : (𝒫).left.obj (op ⦋2⦌)) :
    (lichtenbaumSchlessingerComplex P').relationIso.hom
      ((c.correctedMap c' g).f (-2) (generatorTwo g')) = (1 : B') ⊗ₜ c.relation g' := by
  rw [correctedMap_f_negTwo, moduleCat_add_apply, restrictScalars_hom_add (algebraMap B B'),
    h.negTwo g',
    ConcreteCategory.comp_apply, homotopyHomOne_apply, cotangentComplexULift_d_apply,
    generatorTwo, uliftUp_down, cotangentComplex_d_negTwo_negOne_inv, Iso.inv_hom_id_apply,
    LinearMap.add_apply, LinearMap.sub_apply, cotangentSpaceMap_face_tmul,
    cotangentSpaceMap_face_tmul, cotangentSpaceMap_face_tmul, map_add, map_sub,
    homotopyOne_tmul, homotopyOne_tmul, homotopyOne_tmul, homotopyDerivOne, homotopyDerivOne,
    homotopyDerivOne, ← tmul_sub, ← tmul_add, ← tmul_add, ← c.correction_sub,
    ← c.correction_add, ← CommAlgCat.faceSumTwo_apply]
  congr 1
  apply relationQuotientToFree_injective P'
  rw [map_add, relationQuotientToFree_relation, relationQuotientToFree_correction,
    relationQuotientToFree_relation, correctionFree, δ_faceSumTwo]
  abel

/-- If `g` is given by the formulas for `c'`, then `c.correctedMap c' g` is given by the
formulas for `c`. -/
theorem isLichtenbaumSchlessingerRelativeComparison_correctedMap
    {g : cotangentComplexULift.{u, v, max u' w} A B ⟶
      ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex}
    (h : IsLichtenbaumSchlessingerRelativeComparison P' c' g) :
    IsLichtenbaumSchlessingerRelativeComparison P' c (c.correctedMap c' g) where
  zero := c.correctedMap_zero c' h
  negOne := c.correctedMap_negOne c' h
  negTwo := c.correctedMap_negTwo c' h

end LichtenbaumSchlessingerRelativeChoice

/-- **Two maps of complexes `L_{B/A} → L'` given by the formulas of the source, for any two
relative choices, are homotopic.** -/
def homotopyOfIsLichtenbaumSchlessingerRelativeComparison
    {c c' : LichtenbaumSchlessingerRelativeChoice A B P'}
    {g g' : cotangentComplexULift.{u, v, max u' w} A B ⟶
      ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex}
    (hg : IsLichtenbaumSchlessingerRelativeComparison P' c g)
    (hg' : IsLichtenbaumSchlessingerRelativeComparison P' c' g') : Homotopy g g' :=
  (Homotopy.ofEq (eq_of_isLichtenbaumSchlessingerRelativeComparison P' hg
    (c.isLichtenbaumSchlessingerRelativeComparison_correctedMap c' hg'))).trans
    (c.correctedMapHomotopy c' g')

end Algebra.Presentation

end

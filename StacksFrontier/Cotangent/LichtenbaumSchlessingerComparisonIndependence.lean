module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonCanonical

/-!
# The comparison map `L_{B/A} → L` does not depend on the choices

The map of complexes `L_{B/A} → L` of [Stacks, Tag 09CG] is built from two choices: an
`A`-algebra map `ψ : P₀ → P` over `B`, and an `A`-biderivation `λ : P₁ → F/TrivRel` for the
bimodule structure `(ψ ∘ d₀, ψ ∘ d₁)` with `ρ ∘ λ = ψ ∘ d₀ - ψ ∘ d₁`. For every such choice, the
formulas `dψ ⊗ 1`, `λ̄` and `q` of the source define a map of complexes, and all of them give the
same morphism in `D(B)`.

## Main definitions

* `Algebra.Presentation.LichtenbaumSchlessingerChoice`: a permissible choice `(ψ, λ)`.
* `Algebra.Presentation.IsLichtenbaumSchlessingerComparison`: a map of complexes is given by the
  formulas of the source for a choice.

## Main results

* `Algebra.Presentation.exists_isLichtenbaumSchlessingerComparison`: every choice gives a map of
  complexes.
* `Algebra.Presentation.Q_map_eq_canonicalCotangentToLichtenbaumSchlessinger`: every such map
  represents the canonical map `L_{B/A} → L` in `D(B)`.

## Implementation notes

For a choice `(ψ', λ')` and the fixed choice `(ψ, λ)` of
`Algebra.Presentation.lsChainMap`, let `θ : P₀ → F/TrivRel` be the `(ψ', ψ)`-biderivation with
`ρ ∘ θ = ψ' - ψ`, and let `u = λ' - λ - θ ∘ d₀ + θ ∘ d₁ : P₁ → Rel/TrivRel`, a derivation over
`B`. Then `dx ↦ θ(x) ⊗ 1` and `dx ↦ u(x) ⊗ 1` form a homotopy from `lsChainMap` to a map of
complexes given by the formulas of the source for `(ψ', λ')`. Since the formulas determine a map
of complexes, every map of complexes given by them is homotopic to `lsChainMap`.

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TensorProduct KaehlerDifferential
open Stacks.Cotangent

universe u v w

noncomputable section

namespace Algebra.Presentation

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
variable {X T : Type w} (P : Algebra.Presentation A B X T)

local notation "𝒫" => (CommAlgCat.standardResolution A (CommAlgCat.of A B))
local notation "𝓔" n => (CommAlgCat.standardResolutionExtension A (CommAlgCat.of A B) n)
local notation "𝕂" => (CommAlgCat.cotangentComplex A (CommAlgCat.of A B))

/-! ### Choices -/

/-- **A permissible choice for [Stacks, Tag 09CG]**: an `A`-algebra map `ψ : P₀ → P` compatible
with the maps to `B`, and an `A`-biderivation `λ : P₁ → F/TrivRel` for the bimodule structure
`(ψ ∘ d₀, ψ ∘ d₁)` with `ρ ∘ λ = ψ ∘ d₀ - ψ ∘ d₁`. -/
structure LichtenbaumSchlessingerChoice where
  /-- The map `ψ : P₀ → P`. -/
  ψ : (𝒫).left.obj (op ⦋0⦌) →ₐ[A] P.Ring
  /-- `ψ` lies over `B`. -/
  algebraMap_ψ : ∀ p, algebraMap P.Ring B (ψ p) = (𝒫).hom.app (op ⦋0⦌) p
  /-- The biderivation `λ : P₁ → F/TrivRel`. -/
  lam : (𝒫).left.obj (op ⦋1⦌) →ₗ[A] freeQuotient P
  /-- `λ` is a biderivation for the bimodule structure `(ψ ∘ d₀, ψ ∘ d₁)`. -/
  lam_mul : ∀ x y, lam (x * y) =
    ψ ((𝒫).left.δ (0 : Fin 2) x) • lam y + ψ ((𝒫).left.δ (1 : Fin 2) y) • lam x
  /-- `ρ ∘ λ = ψ ∘ d₀ - ψ ∘ d₁`. -/
  freeQuotientRelationMap_lam : ∀ x, freeQuotientRelationMap P (lam x) =
    ψ ((𝒫).left.δ (0 : Fin 2) x) - ψ ((𝒫).left.δ (1 : Fin 2) x)

/-- The choice `(lsSection, lsBiderivation)` used by `Algebra.Presentation.lsChainMap`. -/
def lsChoice : LichtenbaumSchlessingerChoice P where
  ψ := P.lsSection
  algebraMap_ψ := P.algebraMap_lsSection
  lam :=
    { toFun := P.lsBiderivation
      map_add' := P.lsBiderivation_add
      map_smul' := P.lsBiderivation_smul }
  lam_mul := P.lsBiderivation_mul
  freeQuotientRelationMap_lam := P.freeQuotientRelationMap_lsBiderivation

namespace LichtenbaumSchlessingerChoice

variable {P} (c : LichtenbaumSchlessingerChoice P)

/-- `ρ(λ(d₀ g - d₁ g + d₂ g)) = 0` for `g ∈ P₂`. -/
theorem freeQuotientRelationMap_lam_faceSumTwo (g : (𝒫).left.obj (op ⦋2⦌)) :
    freeQuotientRelationMap P (c.lam (CommAlgCat.faceSumTwo A _ g)) = 0 := by
  rw [c.freeQuotientRelationMap_lam, δ_faceSumTwo, sub_self]

/-- The class `q(dg) ∈ Rel/TrivRel` of `λ(d₀ g - d₁ g + d₂ g)`. -/
def relation (g : (𝒫).left.obj (op ⦋2⦌)) : relationQuotient P :=
  (exists_relationQuotientToFree_eq P _ (c.freeQuotientRelationMap_lam_faceSumTwo g)).choose

/-- The image of `relation g` in `F/TrivRel` is `λ(d₀ g - d₁ g + d₂ g)`. -/
theorem relationQuotientToFree_relation (g : (𝒫).left.obj (op ⦋2⦌)) :
    relationQuotientToFree P (c.relation g) = c.lam (CommAlgCat.faceSumTwo A _ g) :=
  (exists_relationQuotientToFree_eq P _ (c.freeQuotientRelationMap_lam_faceSumTwo g)).choose_spec

end LichtenbaumSchlessingerChoice

/-! ### The formulas of the source -/

omit P in
/-- The generator `d x` of `L_{B/A}` in degree `0`. -/
def generatorZero (x : (𝒫).left.obj (op ⦋0⦌)) : (cotangentComplexULift.{u, v, w} A B).X 0 :=
  uliftUp.{u, v, w} (A := A) (B := B) 0 ((cotangentDegreeIsoZero (A := A) (B := B)).inv
    ((1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring x))

omit P in
/-- The generator `d x` of `L_{B/A}` in degree `-1`. -/
def generatorOne (x : (𝒫).left.obj (op ⦋1⦌)) : (cotangentComplexULift.{u, v, w} A B).X (-1) :=
  uliftUp.{u, v, w} (A := A) (B := B) (-1) ((cotangentDegreeIsoOne (A := A) (B := B)).inv
    ((1 : B) ⊗ₜ[(𝓔 1).Ring] D A (𝓔 1).Ring x))

omit P in
/-- The generator `d g` of `L_{B/A}` in degree `-2`. -/
def generatorTwo (g : (𝒫).left.obj (op ⦋2⦌)) : (cotangentComplexULift.{u, v, w} A B).X (-2) :=
  uliftUp.{u, v, w} (A := A) (B := B) (-2) ((cotangentDegreeIsoTwo (A := A) (B := B)).inv
    ((1 : B) ⊗ₜ[(𝓔 2).Ring] D A (𝓔 2).Ring g))

/-- **A map of complexes `L_{B/A} → L` given by the formulas of [Stacks, Tag 09CG]** for the
choice `c = (ψ, λ)`: `dψ ⊗ 1` in degree `0`, `λ̄ : dx ↦ λ(x) ⊗ 1` in degree `-1`, and
`q : dg ↦ [λ(d₀ g - d₁ g + d₂ g)]` in degree `-2`. -/
structure IsLichtenbaumSchlessingerComparison (c : LichtenbaumSchlessingerChoice P)
    (f : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex) :
    Prop where
  /-- In degree `0`, `dx ↦ dψ(x) ⊗ 1`. -/
  zero : ∀ x, (lichtenbaumSchlessingerComplex P).differentialIso.hom (f.f 0 (generatorZero x)) =
    (1 : B) ⊗ₜ D A P.Ring (c.ψ x)
  /-- In degree `-1`, `dx ↦ λ(x) ⊗ 1`. -/
  negOne : ∀ x, (lichtenbaumSchlessingerComplex P).freeIso.hom (f.f (-1) (generatorOne x)) =
    freeQuotientToTensor P (c.lam x)
  /-- In degree `-2`, `dg ↦ [λ(d₀ g - d₁ g + d₂ g)]`. -/
  negTwo : ∀ g, (lichtenbaumSchlessingerComplex P).relationIso.hom (f.f (-2) (generatorTwo g)) =
    (1 : B) ⊗ₜ c.relation g

/-- `Algebra.Presentation.lsChainMap` is given by the formulas of the source for the choice
`Algebra.Presentation.lsChoice`. -/
theorem isLichtenbaumSchlessingerComparison_lsChainMap :
    IsLichtenbaumSchlessingerComparison P P.lsChoice P.lsChainMap where
  zero x := by
    rw [lsChainMap_f, lsChainComponent_zero, lsChainZero_apply, generatorZero, uliftUp_down,
      Iso.inv_hom_id_apply, lsComponentZero_tmul]
    rfl
  negOne x := by
    rw [lsChainMap_f, lsChainComponent_negOne, lsChainOne_apply, generatorOne, uliftUp_down,
      Iso.inv_hom_id_apply, lsComponentOne_tmul]
    rfl
  negTwo g := by
    rw [lsChainMap_f, lsChainComponent_negTwo, lsChainTwo_apply, generatorTwo, uliftUp_down,
      Iso.inv_hom_id_apply, lsComponentTwo_tmul, lsDerivTwo]
    congr 1

/-! ### The homotopy between two choices -/

namespace LichtenbaumSchlessingerChoice

variable {P} (c : LichtenbaumSchlessingerChoice P)

local notation "e₀" => CommAlgCat.standardResolutionZeroAlgEquiv A (CommAlgCat.of A B)

/-- `ψ'(p) - ψ(p)` lies in the kernel of `P → B`. -/
theorem ψ_sub_lsSection_mem (p : (𝒫).left.obj (op ⦋0⦌)) : c.ψ p - P.lsSection p ∈ P.ker := by
  change algebraMap P.Ring B _ = 0
  rw [map_sub, c.algebraMap_ψ, P.algebraMap_lsSection, sub_self]

/-- The biderivation `θ` read on `A[B]`. -/
def differencePoly : MvPolynomial (CommAlgCat.of A B) A →ₗ[A] freeQuotient P :=
  (exists_biderivation_freeQuotient P (c.ψ.comp (e₀).symm.toAlgHom)
    (P.lsSection.comp (e₀).symm.toAlgHom) fun _ => c.ψ_sub_lsSection_mem _).choose

/-- The defining properties of the biderivation `θ` read on `A[B]`. -/
private theorem differencePoly_spec :
    (∀ x y, c.differencePoly (x * y) = (c.ψ.comp (e₀).symm.toAlgHom) x • c.differencePoly y +
      (P.lsSection.comp (e₀).symm.toAlgHom) y • c.differencePoly x) ∧
    ∀ x, freeQuotientRelationMap P (c.differencePoly x) =
      (c.ψ.comp (e₀).symm.toAlgHom) x - (P.lsSection.comp (e₀).symm.toAlgHom) x :=
  (exists_biderivation_freeQuotient P (c.ψ.comp (e₀).symm.toAlgHom)
    (P.lsSection.comp (e₀).symm.toAlgHom) fun _ => c.ψ_sub_lsSection_mem _).choose_spec

/-- **The biderivation `θ : P₀ → F/TrivRel`** for the bimodule structure `(ψ', ψ)`, with
`ρ ∘ θ = ψ' - ψ`, comparing the choice `c = (ψ', λ')` with `lsChoice = (ψ, λ)`. -/
def difference : (𝒫).left.obj (op ⦋0⦌) →ₗ[A] freeQuotient P :=
  c.differencePoly ∘ₗ (e₀).toLinearMap

/-- `θ` is a biderivation: `θ(xy) = ψ'(x) θ(y) + ψ(y) θ(x)`. -/
theorem difference_mul (x y : (𝒫).left.obj (op ⦋0⦌)) :
    c.difference (x * y) = c.ψ x • c.difference y + P.lsSection y • c.difference x := by
  have h := c.differencePoly_spec.1 ((e₀) x) ((e₀) y)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, ← map_mul] at h
  exact h

/-- `ρ ∘ θ = ψ' - ψ`. -/
theorem freeQuotientRelationMap_difference (x : (𝒫).left.obj (op ⦋0⦌)) :
    freeQuotientRelationMap P (c.difference x) = c.ψ x - P.lsSection x := by
  have h := c.differencePoly_spec.2 ((e₀) x)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at h
  exact h

/-- `θ(1) = 0`. -/
theorem difference_one : c.difference 1 = 0 := by
  have h := c.difference_mul 1 1
  simp only [mul_one, map_one, one_smul] at h
  exact add_eq_left.1 h.symm

/-- `θ` vanishes on the image of `A`. -/
theorem difference_algebraMap (a : A) :
    c.difference (algebraMap A ((𝒫).left.obj (op ⦋0⦌)) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, difference_one, smul_zero]

/-- `λ'(x) - λ(x) - θ(d₀ x) + θ(d₁ x) ∈ F/TrivRel`, which lies in `Rel/TrivRel`. -/
def correctionFree (x : (𝒫).left.obj (op ⦋1⦌)) : freeQuotient P :=
  c.lam x - P.lsBiderivation x - c.difference ((𝒫).left.δ (0 : Fin 2) x) +
    c.difference ((𝒫).left.δ (1 : Fin 2) x)

/-- `ρ(λ'(x) - λ(x) - θ(d₀ x) + θ(d₁ x)) = 0`. -/
theorem freeQuotientRelationMap_correctionFree (x : (𝒫).left.obj (op ⦋1⦌)) :
    freeQuotientRelationMap P (c.correctionFree x) = 0 := by
  rw [correctionFree, map_add, map_sub, map_sub, c.freeQuotientRelationMap_lam,
    freeQuotientRelationMap_lsBiderivation, freeQuotientRelationMap_difference,
    freeQuotientRelationMap_difference]
  abel

/-- **The derivation `u : P₁ → Rel/TrivRel`**, `u = λ' - λ - θ ∘ d₀ + θ ∘ d₁`. -/
def correction (x : (𝒫).left.obj (op ⦋1⦌)) : relationQuotient P :=
  (exists_relationQuotientToFree_eq P _ (c.freeQuotientRelationMap_correctionFree x)).choose

/-- The image of `u(x)` in `F/TrivRel` is `λ'(x) - λ(x) - θ(d₀ x) + θ(d₁ x)`. -/
theorem relationQuotientToFree_correction (x : (𝒫).left.obj (op ⦋1⦌)) :
    relationQuotientToFree P (c.correction x) = c.correctionFree x :=
  (exists_relationQuotientToFree_eq P _ (c.freeQuotientRelationMap_correctionFree x)).choose_spec

/-- `u` is additive. -/
theorem correction_add (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction (x + y) = c.correction x + c.correction y := by
  apply relationQuotientToFree_injective P
  simp only [map_add, relationQuotientToFree_correction, correctionFree, lsBiderivation_add]
  abel

/-- The Leibniz rule `u(xy) = ψ'(d₀ x) u(y) + ψ(d₁ y) u(x)`. -/
theorem correction_mul (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction (x * y) = c.ψ ((𝒫).left.δ (0 : Fin 2) x) • c.correction y +
      P.lsSection ((𝒫).left.δ (1 : Fin 2) y) • c.correction x := by
  apply relationQuotientToFree_injective P
  rw [map_add, map_smul, map_smul, relationQuotientToFree_correction,
    relationQuotientToFree_correction, relationQuotientToFree_correction]
  exact freeQuotient_sub_sub_add_mul P (fun x => c.ψ ((𝒫).left.δ (0 : Fin 2) x))
    (fun x => c.ψ ((𝒫).left.δ (1 : Fin 2) x)) (fun x => P.lsSection ((𝒫).left.δ (0 : Fin 2) x))
    (fun x => P.lsSection ((𝒫).left.δ (1 : Fin 2) x)) c.lam P.lsBiderivation
    (fun x => c.difference ((𝒫).left.δ (0 : Fin 2) x))
    (fun x => c.difference ((𝒫).left.δ (1 : Fin 2) x)) x y (c.lam_mul x y)
    (P.lsBiderivation_mul x y) (by rw [map_mul, difference_mul]) (by rw [map_mul, difference_mul])
    (c.freeQuotientRelationMap_lam x) (P.freeQuotientRelationMap_lsBiderivation y)
    (c.freeQuotientRelationMap_difference _) (c.freeQuotientRelationMap_difference _)

/-- `u` preserves subtraction. -/
theorem correction_sub (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction (x - y) = c.correction x - c.correction y := by
  rw [eq_sub_iff_add_eq, ← correction_add, sub_add_cancel]

/-- `u(1) = 0`. -/
theorem correction_one : c.correction 1 = 0 := by
  have h := c.correction_mul 1 1
  simp only [mul_one, map_one, one_smul] at h
  exact add_eq_left.1 h.symm

/-- `u` is `A`-linear. -/
theorem correction_smul (a : A) (x : (𝒫).left.obj (op ⦋1⦌)) :
    c.correction (a • x) = a • c.correction x := by
  apply relationQuotientToFree_injective P
  rw [LinearMap.map_smul_of_tower, relationQuotientToFree_correction,
    relationQuotientToFree_correction, correctionFree, correctionFree, map_smul,
    lsBiderivation_smul, map_smul, map_smul, map_smul, map_smul]
  simp only [smul_sub, smul_add]

/-- `u` vanishes on the image of `A`. -/
theorem correction_algebraMap (a : A) :
    c.correction (algebraMap A ((𝒫).left.obj (op ⦋1⦌)) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, correction_smul, correction_one, smul_zero]

end LichtenbaumSchlessingerChoice

/-! ### The homotopy on cotangent spaces -/

namespace LichtenbaumSchlessingerChoice

variable {P} (c : LichtenbaumSchlessingerChoice P)

/-- `x ↦ θ(x) ⊗ 1`. -/
def homotopyDerivZero (x : (𝒫).left.obj (op ⦋0⦌)) : B ⊗[P.Ring] (T →₀ P.Ring) :=
  freeQuotientToTensor P (c.difference x)

/-- `x ↦ θ(x) ⊗ 1` is additive. -/
theorem homotopyDerivZero_add (x y : (𝒫).left.obj (op ⦋0⦌)) :
    c.homotopyDerivZero (x + y) = c.homotopyDerivZero x + c.homotopyDerivZero y := by
  rw [homotopyDerivZero, map_add, map_add]
  rfl

/-- `x ↦ θ(x) ⊗ 1` vanishes on the image of `A`. -/
theorem homotopyDerivZero_algebraMap (a : A) :
    c.homotopyDerivZero (algebraMap A ((𝒫).left.obj (op ⦋0⦌)) a) = 0 := by
  rw [homotopyDerivZero, c.difference_algebraMap, map_zero]

/-- `x ↦ θ(x) ⊗ 1` is a derivation for the `P₀`-module structure through `P₀ → B`. -/
theorem homotopyDerivZero_mul (x y : (𝒫).left.obj (op ⦋0⦌)) :
    c.homotopyDerivZero (x * y) =
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) x •
        c.homotopyDerivZero y +
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋0⦌) y •
        c.homotopyDerivZero x := by
  rw [homotopyDerivZero, c.difference_mul, map_add, freeQuotientToTensor_smul,
    freeQuotientToTensor_smul, c.algebraMap_ψ, P.algebraMap_lsSection]
  rfl

/-- The degree `0` part of the homotopy, `dx ↦ θ(x) ⊗ 1 : Ω_{P₀/A} ⊗ B → F ⊗ B`. -/
def homotopyZero : (𝓔 0).CotangentSpace →ₗ[B] B ⊗[P.Ring] (T →₀ P.Ring) :=
  (𝓔 0).cotangentSpaceLift c.homotopyDerivZero c.homotopyDerivZero_add
    c.homotopyDerivZero_algebraMap c.homotopyDerivZero_mul

/-- `homotopyZero` sends `1 ⊗ dx` to `θ(x) ⊗ 1`. -/
theorem homotopyZero_tmul (x : (𝒫).left.obj (op ⦋0⦌)) :
    c.homotopyZero ((1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring x) =
      c.homotopyDerivZero x :=
  (Algebra.Extension.cotangentSpaceLift_tmul _ _ _ _ _ _ _).trans (one_smul _ _)

/-- `x ↦ u(x) ⊗ 1`. -/
def homotopyDerivOne (x : (𝒫).left.obj (op ⦋1⦌)) : B ⊗[P.Ring] relationQuotient P :=
  (1 : B) ⊗ₜ c.correction x

/-- `x ↦ u(x) ⊗ 1` is additive. -/
theorem homotopyDerivOne_add (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.homotopyDerivOne (x + y) = c.homotopyDerivOne x + c.homotopyDerivOne y := by
  rw [homotopyDerivOne, c.correction_add, tmul_add]
  rfl

/-- `x ↦ u(x) ⊗ 1` vanishes on the image of `A`. -/
theorem homotopyDerivOne_algebraMap (a : A) :
    c.homotopyDerivOne (algebraMap A ((𝒫).left.obj (op ⦋1⦌)) a) = 0 := by
  rw [homotopyDerivOne, c.correction_algebraMap, tmul_zero]

/-- `x ↦ u(x) ⊗ 1` is a derivation for the `P₁`-module structure through `P₁ → B`. -/
theorem homotopyDerivOne_mul (x y : (𝒫).left.obj (op ⦋1⦌)) :
    c.homotopyDerivOne (x * y) =
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋1⦌) x •
        c.homotopyDerivOne y +
      CommAlgCat.standardResolutionAugmentationHom A (CommAlgCat.of A B) (op ⦋1⦌) y •
        c.homotopyDerivOne x := by
  rw [homotopyDerivOne, c.correction_mul, tmul_add, tmul_smul_eq_algebraMap_smul,
    tmul_smul_eq_algebraMap_smul, c.algebraMap_ψ, P.algebraMap_lsSection,
    CommAlgCat.standardResolution_augmentation_δ, CommAlgCat.standardResolution_augmentation_δ]
  rfl

/-- The degree `-1` part of the homotopy, `dx ↦ u(x) ⊗ 1 : Ω_{P₁/A} ⊗ B → Rel/TrivRel ⊗ B`. -/
def homotopyOne : (𝓔 1).CotangentSpace →ₗ[B] B ⊗[P.Ring] relationQuotient P :=
  (𝓔 1).cotangentSpaceLift c.homotopyDerivOne c.homotopyDerivOne_add
    c.homotopyDerivOne_algebraMap c.homotopyDerivOne_mul

/-- `homotopyOne` sends `1 ⊗ dx` to `u(x) ⊗ 1`. -/
theorem homotopyOne_tmul (x : (𝒫).left.obj (op ⦋1⦌)) :
    c.homotopyOne ((1 : B) ⊗ₜ[(𝓔 1).Ring] D A (𝓔 1).Ring x) = c.homotopyDerivOne x :=
  (Algebra.Extension.cotangentSpaceLift_tmul _ _ _ _ _ _ _).trans (one_smul _ _)

end LichtenbaumSchlessingerChoice

/-! ### The homotopy and the map of complexes of a choice -/

namespace LichtenbaumSchlessingerChoice

variable {P} (c : LichtenbaumSchlessingerChoice P)

/-- The homotopy `L_{B/A}^0 → L^{-1}`. -/
def homotopyHomZero : (cotangentComplexULift.{u, v, w} A B).X 0 ⟶
    (lichtenbaumSchlessingerComplex P).complex.X (-1) :=
  (ConcreteCategory.ofHom (C := ModuleCat B) (X := (cotangentComplexULift.{u, v, w} A B).X 0)
    (c.homotopyZero ∘ₗ ((cotangentDegreeIsoZero (A := A) (B := B)).hom.hom ∘ₗ
      uliftDown (A := A) (B := B) 0))) ≫
    (lichtenbaumSchlessingerComplex P).freeIso.inv

/-- The value of `homotopyHomZero` on an element. -/
theorem homotopyHomZero_apply (z : (cotangentComplexULift.{u, v, w} A B).X 0) :
    c.homotopyHomZero z = (lichtenbaumSchlessingerComplex P).freeIso.inv
      (c.homotopyZero ((cotangentDegreeIsoZero (A := A) (B := B)).hom z.down)) := rfl

/-- The homotopy `L_{B/A}^{-1} → L^{-2}`. -/
def homotopyHomOne : (cotangentComplexULift.{u, v, w} A B).X (-1) ⟶
    (lichtenbaumSchlessingerComplex P).complex.X (-2) :=
  (ConcreteCategory.ofHom (C := ModuleCat B) (X := (cotangentComplexULift.{u, v, w} A B).X (-1))
    (c.homotopyOne ∘ₗ ((cotangentDegreeIsoOne (A := A) (B := B)).hom.hom ∘ₗ
      uliftDown (A := A) (B := B) (-1)))) ≫
    (lichtenbaumSchlessingerComplex P).relationIso.inv

/-- The value of `homotopyHomOne` on an element. -/
theorem homotopyHomOne_apply (z : (cotangentComplexULift.{u, v, w} A B).X (-1)) :
    c.homotopyHomOne z = (lichtenbaumSchlessingerComplex P).relationIso.inv
      (c.homotopyOne ((cotangentDegreeIsoOne (A := A) (B := B)).hom z.down)) := rfl

/-- The homotopy, as a family of maps `L_{B/A}^i → L^{i-1}`. -/
def homotopyHom (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
    (cotangentComplexULift.{u, v, w} A B).X i ⟶ (lichtenbaumSchlessingerComplex P).complex.X j :=
  if h : i = 0 then
    eqToHom (by rw [h]) ≫ c.homotopyHomZero ≫
      eqToHom (by rw [show j = -1 by change j + 1 = i at hij; omega])
  else if h' : i = -1 then
    eqToHom (by rw [h']) ≫ c.homotopyHomOne ≫
      eqToHom (by rw [show j = -2 by change j + 1 = i at hij; omega])
  else 0

/-- In degree `0`, the homotopy is `homotopyHomZero`. -/
theorem homotopyHom_zero (h : (ComplexShape.up ℤ).Rel (-1) 0) :
    c.homotopyHom 0 (-1) h = c.homotopyHomZero := by
  rw [homotopyHom, dite_eq_left rfl, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- In degree `-1`, the homotopy is `homotopyHomOne`. -/
theorem homotopyHom_negOne (h : (ComplexShape.up ℤ).Rel (-2) (-1)) :
    c.homotopyHom (-1) (-2) h = c.homotopyHomOne := by
  rw [homotopyHom, dite_eq_right (by decide), dite_eq_left rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- In degrees other than `0` and `-1`, the homotopy vanishes. -/
theorem homotopyHom_eq_zero (i j : ℤ) (h : (ComplexShape.up ℤ).Rel j i) (h0 : i ≠ 0)
    (h1 : i ≠ -1) : c.homotopyHom i j h = 0 := by
  rw [homotopyHom, dite_eq_right h0, dite_eq_right h1]

/-- **The map of complexes `L_{B/A} → L` of the choice `c`**: `lsChainMap` corrected by the
null-homotopic map of the homotopy `(θ, u)`. -/
def chainMap : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex :=
  P.lsChainMap + Homotopy.nullHomotopicMap' c.homotopyHom

/-- The map of complexes of a choice is homotopic to `lsChainMap`. -/
def homotopy : Homotopy c.chainMap P.lsChainMap :=
  ((Homotopy.refl P.lsChainMap).add (Homotopy.nullHomotopy' c.homotopyHom)).trans
    (Homotopy.ofEq (add_zero _))

/-- The degree `0` component of `chainMap` is that of `lsChainMap` plus `d ∘ homotopyHomZero`. -/
theorem chainMap_f_zero : c.chainMap.f 0 =
    P.lsChainMap.f 0 + c.homotopyHomZero ≫ (lichtenbaumSchlessingerComplex P).complex.d (-1) 0 := by
  change P.lsChainMap.f 0 + (Homotopy.nullHomotopicMap' c.homotopyHom).f 0 = _
  rw [Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₀ := 1) (by simp) (by simp),
    c.homotopyHom_eq_zero 1 0 _ (by decide) (by decide), Limits.comp_zero, zero_add,
    homotopyHom_zero]

/-- The degree `-1` component of `chainMap` is that of `lsChainMap` plus
`homotopyHomZero ∘ d + d ∘ homotopyHomOne`. -/
theorem chainMap_f_negOne : c.chainMap.f (-1) =
    P.lsChainMap.f (-1) + ((cotangentComplexULift.{u, v, w} A B).d (-1) 0 ≫ c.homotopyHomZero +
      c.homotopyHomOne ≫ (lichtenbaumSchlessingerComplex P).complex.d (-2) (-1)) := by
  change P.lsChainMap.f (-1) + (Homotopy.nullHomotopicMap' c.homotopyHom).f (-1) = _
  rw [Homotopy.nullHomotopicMap'_f (k₂ := -2) (k₀ := 0) (by simp) (by simp), homotopyHom_zero,
    homotopyHom_negOne]

/-- The degree `-2` component of `chainMap` is that of `lsChainMap` plus `homotopyHomOne ∘ d`. -/
theorem chainMap_f_negTwo : c.chainMap.f (-2) =
    P.lsChainMap.f (-2) + (cotangentComplexULift.{u, v, w} A B).d (-2) (-1) ≫ c.homotopyHomOne := by
  change P.lsChainMap.f (-2) + (Homotopy.nullHomotopicMap' c.homotopyHom).f (-2) = _
  rw [Homotopy.nullHomotopicMap'_f (k₂ := -3) (k₀ := -1) (by simp) (by simp), homotopyHom_negOne,
    c.homotopyHom_eq_zero (-2) (-3) _ (by decide) (by decide), Limits.zero_comp, add_zero]

end LichtenbaumSchlessingerChoice

/-! ### The map of complexes of a choice is given by the formulas of the source -/

omit P in
/-- The sum of two morphisms of modules is evaluated pointwise. -/
theorem moduleCat_add_apply {R : Type*} [Ring R] {M N : ModuleCat R} (f g : M ⟶ N) (z : M) :
    (f + g) z = f z + g z := rfl

namespace LichtenbaumSchlessingerChoice

variable {P} (c : LichtenbaumSchlessingerChoice P)

/-- In degree `0`, `chainMap` sends `dx` to `dψ'(x) ⊗ 1`. -/
theorem chainMap_zero (x : (𝒫).left.obj (op ⦋0⦌)) :
    (lichtenbaumSchlessingerComplex P).differentialIso.hom (c.chainMap.f 0 (generatorZero x)) =
      (1 : B) ⊗ₜ D A P.Ring (c.ψ x) := by
  have e : (lichtenbaumSchlessingerComplex P).differentialIso.hom
      (P.lsChainMap.f 0 (generatorZero x)) = (1 : B) ⊗ₜ D A P.Ring (P.lsSection x) :=
    (isLichtenbaumSchlessingerComparison_lsChainMap P).zero x
  rw [chainMap_f_zero, moduleCat_add_apply, map_add, e,
    ConcreteCategory.comp_apply, homotopyHomZero_apply, lsComplex_d_negOne_inv_apply,
    generatorZero, uliftUp_down, Iso.inv_hom_id_apply, homotopyZero_tmul, homotopyDerivZero,
    relationDifferentialB_freeQuotientToTensor, freeQuotientRelationMap_difference, map_sub,
    tmul_sub, add_sub_cancel]

/-- In degree `-1`, `chainMap` sends `dx` to `λ'(x) ⊗ 1`. -/
theorem chainMap_negOne (x : (𝒫).left.obj (op ⦋1⦌)) :
    (lichtenbaumSchlessingerComplex P).freeIso.hom (c.chainMap.f (-1) (generatorOne x)) =
      freeQuotientToTensor P (c.lam x) := by
  let := relationModule P
  have e : (lichtenbaumSchlessingerComplex P).freeIso.hom
      (P.lsChainMap.f (-1) (generatorOne x)) = freeQuotientToTensor P (P.lsBiderivation x) :=
    (isLichtenbaumSchlessingerComparison_lsChainMap P).negOne x
  have hd : (cotangentDegreeIsoZero (A := A) (B := B)).hom
      ((cotangentComplexULift.{u, v, w} A B).d (-1) 0 (generatorOne x)).down =
      (1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring ((𝒫).left.δ (0 : Fin 2) x) -
        (1 : B) ⊗ₜ[(𝓔 0).Ring] D A (𝓔 0).Ring ((𝒫).left.δ (1 : Fin 2) x) := by
    rw [cotangentComplexULift_d_apply, cotangentComplex_d_negOne_zero_apply, generatorOne,
      uliftUp_down, Iso.inv_hom_id_apply, LinearMap.sub_apply, cotangentSpaceMap_face_tmul,
      cotangentSpaceMap_face_tmul]
  rw [chainMap_f_negOne, moduleCat_add_apply, moduleCat_add_apply, map_add, map_add, e,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, homotopyHomZero_apply,
    Iso.inv_hom_id_apply, hd, map_sub,
    homotopyZero_tmul, homotopyZero_tmul, homotopyHomOne_apply, lsComplex_d_negTwo_inv_apply,
    generatorOne, uliftUp_down, Iso.inv_hom_id_apply, homotopyOne_tmul, homotopyDerivOne,
    relationBoundary_tmul_one, relationQuotientToFree_correction, homotopyDerivZero,
    homotopyDerivZero, ← map_sub, ← map_add, ← map_add, correctionFree]
  congr 1
  abel

/-- In degree `-2`, `chainMap` sends `dg` to `[λ'(d₀ g - d₁ g + d₂ g)]`. -/
theorem chainMap_negTwo (g : (𝒫).left.obj (op ⦋2⦌)) :
    (lichtenbaumSchlessingerComplex P).relationIso.hom (c.chainMap.f (-2) (generatorTwo g)) =
      (1 : B) ⊗ₜ c.relation g := by
  have e : (lichtenbaumSchlessingerComplex P).relationIso.hom
      (P.lsChainMap.f (-2) (generatorTwo g)) = (1 : B) ⊗ₜ P.lsRelation g :=
    (isLichtenbaumSchlessingerComparison_lsChainMap P).negTwo g
  rw [chainMap_f_negTwo, moduleCat_add_apply, map_add, e,
    ConcreteCategory.comp_apply, homotopyHomOne_apply, Iso.inv_hom_id_apply,
    cotangentComplexULift_d_apply, generatorTwo, uliftUp_down,
    cotangentComplex_d_negTwo_negOne_inv, Iso.inv_hom_id_apply, LinearMap.add_apply,
    LinearMap.sub_apply, cotangentSpaceMap_face_tmul, cotangentSpaceMap_face_tmul,
    cotangentSpaceMap_face_tmul, map_add, map_sub, homotopyOne_tmul, homotopyOne_tmul,
    homotopyOne_tmul, homotopyDerivOne, homotopyDerivOne, homotopyDerivOne, ← tmul_sub,
    ← tmul_add, ← tmul_add, ← c.correction_sub, ← c.correction_add,
    ← CommAlgCat.faceSumTwo_apply]
  congr 1
  apply relationQuotientToFree_injective P
  rw [map_add, relationQuotientToFree_lsRelation, relationQuotientToFree_correction,
    relationQuotientToFree_relation, correctionFree, δ_faceSumTwo]
  abel

/-- `chainMap` is given by the formulas of the source for the choice `c`. -/
theorem isLichtenbaumSchlessingerComparison_chainMap :
    IsLichtenbaumSchlessingerComparison P c c.chainMap where
  zero := c.chainMap_zero
  negOne := c.chainMap_negOne
  negTwo := c.chainMap_negTwo

end LichtenbaumSchlessingerChoice

/-! ### Independence of the choices -/

omit P in
/-- Maps out of a term of `L_{B/A}` agree once they agree on the generators `d x`. -/
theorem cotangentComplexULift_hom_ext {i : ℤ} {n : ℕ}
    (e : (𝕂).X i ≅ ModuleCat.of B (𝓔 n).CotangentSpace) {M : ModuleCat.{max u v w} B}
    {φ φ' : (cotangentComplexULift.{u, v, w} A B).X i ⟶ M}
    (h : ∀ x : (𝒫).left.obj (op ⦋n⦌),
      φ (uliftUp.{u, v, w} (A := A) (B := B) i (e.inv ((1 : B) ⊗ₜ[(𝓔 n).Ring] D A (𝓔 n).Ring x))) =
        φ' (uliftUp.{u, v, w} (A := A) (B := B) i
          (e.inv ((1 : B) ⊗ₜ[(𝓔 n).Ring] D A (𝓔 n).Ring x)))) : φ = φ' := by
  have key := Algebra.Extension.cotangentSpace_hom_ext (𝓔 n)
    ((φ.hom ∘ₗ uliftUp.{u, v, w} (A := A) (B := B) i) ∘ₗ e.inv.hom)
    ((φ'.hom ∘ₗ uliftUp.{u, v, w} (A := A) (B := B) i) ∘ₗ e.inv.hom) h
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  obtain ⟨m, rfl⟩ : ∃ m, z = uliftUp.{u, v, w} (A := A) (B := B) i m := ⟨z.down, rfl⟩
  have hz := LinearMap.congr_fun key (e.hom m)
  change φ (uliftUp.{u, v, w} (A := A) (B := B) i (e.inv (e.hom m))) =
    φ' (uliftUp.{u, v, w} (A := A) (B := B) i (e.inv (e.hom m))) at hz
  rwa [Iso.hom_inv_id_apply] at hz

/-- Maps out of a term of `L_{B/A}` agree once their composites with a monomorphism agree on the
generators `d x`. -/
private theorem cotangentComplexULift_hom_ext_comp {i : ℤ} {n : ℕ}
    (e : (𝕂).X i ≅ ModuleCat.of B (𝓔 n).CotangentSpace) {M N : ModuleCat.{max u v w} B}
    (m : M ⟶ N) [Mono m] {φ φ' : (cotangentComplexULift.{u, v, w} A B).X i ⟶ M}
    (h : ∀ x : (𝒫).left.obj (op ⦋n⦌),
      m (φ (uliftUp.{u, v, w} (A := A) (B := B) i
          (e.inv ((1 : B) ⊗ₜ[(𝓔 n).Ring] D A (𝓔 n).Ring x)))) =
        m (φ' (uliftUp.{u, v, w} (A := A) (B := B) i
          (e.inv ((1 : B) ⊗ₜ[(𝓔 n).Ring] D A (𝓔 n).Ring x))))) : φ = φ' := by
  rw [← cancel_mono m]
  exact cotangentComplexULift_hom_ext e fun x => by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact h x

/-- **A map of complexes given by the formulas of the source is determined by the choice.** -/
theorem eq_of_isLichtenbaumSchlessingerComparison {c : LichtenbaumSchlessingerChoice P}
    {f g : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex}
    (hf : IsLichtenbaumSchlessingerComparison P c f)
    (hg : IsLichtenbaumSchlessingerComparison P c g) : f = g := by
  ext i : 1
  by_cases h0 : i = 0
  · subst h0
    exact cotangentComplexULift_hom_ext_comp (cotangentDegreeIsoZero (A := A) (B := B))
      (lichtenbaumSchlessingerComplex P).differentialIso.hom fun x =>
        (hf.zero x).trans (hg.zero x).symm
  by_cases h1 : i = -1
  · subst h1
    exact cotangentComplexULift_hom_ext_comp (cotangentDegreeIsoOne (A := A) (B := B))
      (lichtenbaumSchlessingerComplex P).freeIso.hom fun x =>
        (hf.negOne x).trans (hg.negOne x).symm
  by_cases h2 : i = -2
  · subst h2
    exact cotangentComplexULift_hom_ext_comp (cotangentDegreeIsoTwo (A := A) (B := B))
      (lichtenbaumSchlessingerComplex P).relationIso.hom fun x =>
        (hf.negTwo x).trans (hg.negTwo x).symm
  exact ((lichtenbaumSchlessingerComplex P).isZero_X i h2 h1 h0).eq_of_tgt _ _

/-- **Every choice gives a map of complexes `L_{B/A} → L` by the formulas of the source.** -/
theorem exists_isLichtenbaumSchlessingerComparison (c : LichtenbaumSchlessingerChoice P) :
    ∃ f : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex,
      IsLichtenbaumSchlessingerComparison P c f :=
  ⟨c.chainMap, c.isLichtenbaumSchlessingerComparison_chainMap⟩

/-- For every permissible choice `(ψ, λ)`, a map of complexes `L_{B/A} → L` given by the formulas
`dψ ⊗ 1`, `λ̄`, `q` of the source is homotopic to `Algebra.Presentation.lsChainMap`; in particular
it represents the canonical map `L_{B/A} → L` in `D(B)`. -/
def homotopyOfIsLichtenbaumSchlessingerComparison (c : LichtenbaumSchlessingerChoice P)
    {f : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex}
    (hf : IsLichtenbaumSchlessingerComparison P c f) : Homotopy f P.lsChainMap :=
  (Homotopy.ofEq (eq_of_isLichtenbaumSchlessingerComparison P hf
    c.isLichtenbaumSchlessingerComparison_chainMap)).trans c.homotopy

/-- **Independence of the choices.** Every map of complexes `L_{B/A} → L` given by the formulas
`dψ ⊗ 1`, `λ̄`, `q` of the source, for any permissible choice of `ψ : P₀ → P` and of the
biderivation `λ : P₁ → F/TrivRel`, represents the canonical map
`Algebra.Presentation.canonicalCotangentToLichtenbaumSchlessinger` in `D(B)`. -/
@[stacks 09CG "the formulas dψ ⊗ 1, λ̄, q specify the comparison for every permissible choice of
ψ and λ, and changing these choices gives the same morphism in D(B)"]
theorem Q_map_eq_canonicalCotangentToLichtenbaumSchlessinger (c : LichtenbaumSchlessingerChoice P)
    (f : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex)
    (hf : IsLichtenbaumSchlessingerComparison P c f) :
    DerivedCategory.Q.map f = canonicalCotangentToLichtenbaumSchlessinger P :=
  DerivedCategory.Q_map_eq_of_homotopy _ (P.homotopyOfIsLichtenbaumSchlessingerComparison c hf)

/-- Two maps of complexes given by the formulas of the source, for any two permissible choices,
are equal in `D(B)`. -/
theorem Q_map_eq_of_isLichtenbaumSchlessingerComparison {c c' : LichtenbaumSchlessingerChoice P}
    {f f' : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex}
    (hf : IsLichtenbaumSchlessingerComparison P c f)
    (hf' : IsLichtenbaumSchlessingerComparison P c' f') :
    DerivedCategory.Q.map f = DerivedCategory.Q.map f' :=
  (P.Q_map_eq_canonicalCotangentToLichtenbaumSchlessinger c f hf).trans
    (P.Q_map_eq_canonicalCotangentToLichtenbaumSchlessinger c' f' hf').symm

end Algebra.Presentation

end

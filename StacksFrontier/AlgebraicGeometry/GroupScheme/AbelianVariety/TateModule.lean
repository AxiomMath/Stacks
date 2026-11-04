module

public import StacksFrontier.Algebra.Group.TateModule
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.IsogenyKernelCount
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tate modules of abelian varieties

Let `A` be a commutative group scheme over a field `k` and `ℓ` a prime. The `ℓ`-adic Tate module
`T_ℓ A = lim_n A(k)[ℓ^n]` is the Tate module (`Stacks.AbelianGroup.tateModule`) of the group
`A(k)` of rational points, written additively. A homomorphism `α : A ⟶ B` of group schemes induces
the `ℤ_ℓ`-linear map `T_ℓ α`.

## Main definitions

* `Stacks.Groupoids.tateModule A ℓ`: the `ℓ`-adic Tate module of `A`, a `ℤ_[ℓ]`-module.
* `Stacks.Groupoids.tateModuleMap α ℓ`: the map `T_ℓ A →ₗ[ℤ_[ℓ]] T_ℓ B` induced by `α`.
* `Stacks.Groupoids.tateModuleQuotientEquiv A ℓ n`: `T_ℓ A ⧸ ℓ^n ≃+ A(k)[ℓ^n]` for `k`
  algebraically closed and `A` an abelian variety.

## Main results

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `k`, and `ℓ`
a prime invertible in `k`.

* `Stacks.Groupoids.nonempty_linearEquiv_tateModule`: `T_ℓ A ≅ ℤ_ℓ^(2g)`, so `T_ℓ A` is free
  (`Stacks.Groupoids.module_free_tateModule`) of rank `2g`
  (`Stacks.Groupoids.finrank_tateModule`). This uses Tag 03RP, parts (4) and (7).
* `Stacks.Groupoids.tateModuleQuotientEquiv_mapQ`: `T_ℓ A ⧸ ℓ^n ≃+ A(k)[ℓ^n]` is equivariant for
  homomorphisms.
* `Stacks.Groupoids.toZModPow_trace_tateModuleMap`: for an endomorphism `α` of `A`, the trace of
  `T_ℓ α` modulo `ℓ^n` is the trace of `α` on `A(k)[ℓ^n]` over `ℤ/ℓ^n`, in a form transported along
  any isomorphism of `A(k)[ℓ^n]` with a `ℤ/ℓ^n`-module.

## References

* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [D. Mumford, *Abelian varieties*, §18]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory PadicInt Pointwise
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k]

section Hom

variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj B]

/- The product of two homomorphisms into a commutative group object is a homomorphism. -/
attribute [instance] isMonHom_mul

/-- The constant homomorphism into a group object. -/
instance isMonHom_one : IsMonHom (1 : A ⟶ B) := by
  rw [Hom.one_def]
  infer_instance

/-- An integer power of a homomorphism into a commutative group object is a homomorphism. -/
instance isMonHom_zpow_of_isCommMonObj (α : A ⟶ B) [IsMonHom α] (n : ℤ) :
    IsMonHom (α ^ n) := by
  rw [← Category.comp_id α, ← GrpObj.comp_zpow]
  infer_instance

end Hom

section Tate

variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The `ℓ`-adic Tate module `T_ℓ A = lim_n A(k)[ℓ^n]` of a commutative group scheme `A` over
`k`: the Tate module of its group of rational points `A(k)`, written additively. -/
@[sga "1 XI 2.1", sga "7 I 6.1" "partial"]
abbrev tateModule : Type u :=
  AbelianGroup.tateModule (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ℓ

variable {A ℓ}

variable {B C : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]

variable (ℓ) in
/-- The `ℤ_ℓ`-linear map `T_ℓ α : T_ℓ A → T_ℓ B` induced by a homomorphism `α : A ⟶ B` of
commutative group schemes over `k`: postcomposition with `α` on rational points. -/
def tateModuleMap (α : A ⟶ B) [IsMonHom α] : tateModule A ℓ →ₗ[ℤ_[ℓ]] tateModule B ℓ :=
  AbelianGroup.tateModuleMap ℓ (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).toAdditive

/-- The `n`-th component of `T_ℓ α x` is the `n`-th component of `x` postcomposed with `α`. -/
theorem tateModuleMap_seq (α : A ⟶ B) [IsMonHom α] (x : tateModule A ℓ) (n : ℕ) :
    ((tateModuleMap ℓ α x : tateModule B ℓ) : ℕ → Additive (𝟙_ (Over (Spec (.of k))) ⟶ B)) n =
      Additive.ofMul (((x : ℕ → Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) n).toMul ≫ α) :=
  rfl

/-- Linear maps between Tate modules agree when their components agree on every element. -/
private theorem linearMap_ext_tateModule {f g : tateModule A ℓ →ₗ[ℤ_[ℓ]] tateModule B ℓ}
    (h : ∀ (x : tateModule A ℓ) (n : ℕ),
      (f x : ℕ → Additive (𝟙_ (Over (Spec (.of k))) ⟶ B)) n = (g x : ℕ → _) n) : f = g :=
  LinearMap.ext fun x => AbelianGroup.tateModule_ext (h x)

variable (A ℓ) in
/-- `T_ℓ` sends the identity of `A` to the identity of `T_ℓ A`. -/
@[simp]
theorem tateModuleMap_id : tateModuleMap ℓ (𝟙 A) = LinearMap.id :=
  linearMap_ext_tateModule fun x n => Category.comp_id (x.1 n).toMul

/-- `T_ℓ (α ≫ β) = T_ℓ β ∘ T_ℓ α`. -/
theorem tateModuleMap_comp (α : A ⟶ B) (β : B ⟶ C) [IsMonHom α] [IsMonHom β] :
    tateModuleMap ℓ (α ≫ β) = tateModuleMap ℓ β ∘ₗ tateModuleMap ℓ α :=
  linearMap_ext_tateModule fun x n => (Category.assoc (x.1 n).toMul α β).symm

/-- `T_ℓ` sends the product of homomorphisms to the sum of the induced maps. -/
theorem tateModuleMap_mul (α β : A ⟶ B) [IsMonHom α] [IsMonHom β] :
    tateModuleMap ℓ (α * β) = tateModuleMap ℓ α + tateModuleMap ℓ β :=
  linearMap_ext_tateModule fun x n => MonObj.comp_mul (x.1 n).toMul α β

/-- `T_ℓ` sends the constant homomorphism `1` to the zero map. -/
@[simp]
theorem tateModuleMap_one : tateModuleMap ℓ (1 : A ⟶ B) = 0 :=
  linearMap_ext_tateModule fun x n => MonObj.comp_one (M := B) (x.1 n).toMul

/-- `T_ℓ (α⁻¹) = -T_ℓ α`. -/
theorem tateModuleMap_inv (α : A ⟶ B) [IsMonHom α] :
    tateModuleMap ℓ α⁻¹ = -tateModuleMap ℓ α :=
  linearMap_ext_tateModule fun x n => GrpObj.comp_inv (x.1 n).toMul α

/-- `T_ℓ (α ^ m) = m • T_ℓ α` for an integer `m`. -/
theorem tateModuleMap_zpow (α : A ⟶ B) [IsMonHom α] (m : ℤ) :
    tateModuleMap ℓ (α ^ m) = m • tateModuleMap ℓ α :=
  linearMap_ext_tateModule fun x n => GrpObj.comp_zpow (x.1 n).toMul α m

/-- Reduction modulo `ℓ^n` is equivariant: the `n`-th component of `T_ℓ α x` is the
postcomposition of the `n`-th component of `x` with `α`. -/
theorem tateReduction_tateModuleMap (α : A ⟶ B) [IsMonHom α] (n : ℕ) (x : tateModule A ℓ) :
    AbelianGroup.tateReduction ℓ n (tateModuleMap ℓ α x) =
      AbelianGroup.torsionMap (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).toAdditive _
        (AbelianGroup.tateReduction ℓ n x) :=
  rfl

end Tate

section AbelianVariety

variable [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- The group `A(k)` of rational points of an abelian variety over an algebraically closed field
is `ℓ`-divisible (Tag 03RP, part (4)). -/
@[sga "3 VIII 7.11" "special case"]
theorem exists_nsmul_eq_point (x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ∃ y, ℓ • y = x := by
  obtain ⟨y, hy⟩ := exists_pow_eq k A ℓ hℓ.out.ne_zero x.toMul
  exact ⟨Additive.ofMul y, by rw [← ofMul_pow, hy, ofMul_toMul]⟩

omit hℓ in
/-- `A(k)[ℓ^n] ≅ (ℤ/ℓ^n)^(2g)` for `ℓ` invertible in `k` (Tag 03RP, part (7)). -/
theorem nonempty_torsionBy_pow_addEquiv (hℓk : IsUnit (ℓ : k)) (n : ℕ) :
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ n : ℕ) : ℤ) ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod (ℓ ^ n))) :=
  nonempty_torsionBy_addEquiv_of_isUnit k A (ℓ ^ n) (by rw [Nat.cast_pow]; exact hℓk.pow n)

/-- **The Tate module of an abelian variety is free of rank `2g`.** Let `A` be an abelian variety
of dimension `g` over an algebraically closed field `k` and `ℓ` a prime invertible in `k`. Then
`T_ℓ A ≅ ℤ_ℓ^(2g)`. -/
@[sga "7 IX 2.1.12" "special case", sga "7 IX 2.1.5" "partial, special case"]
theorem nonempty_linearEquiv_tateModule (hℓk : IsUnit (ℓ : k)) :
    Nonempty (tateModule A ℓ ≃ₗ[ℤ_[ℓ]] (Fin (2 * abelianVarietyDimension A) → ℤ_[ℓ])) :=
  AbelianGroup.nonempty_linearEquiv_tateModule (exists_nsmul_eq_point A ℓ)
    (nonempty_torsionBy_pow_addEquiv A ℓ hℓk)

/-- The Tate module `T_ℓ A` of an abelian variety is a free `ℤ_ℓ`-module. -/
theorem module_free_tateModule (hℓk : IsUnit (ℓ : k)) : Module.Free ℤ_[ℓ] (tateModule A ℓ) :=
  AbelianGroup.module_free_tateModule (exists_nsmul_eq_point A ℓ)
    (nonempty_torsionBy_pow_addEquiv A ℓ hℓk)

/-- The Tate module `T_ℓ A` of an abelian variety is a finitely generated `ℤ_ℓ`-module. -/
theorem module_finite_tateModule (hℓk : IsUnit (ℓ : k)) : Module.Finite ℤ_[ℓ] (tateModule A ℓ) :=
  AbelianGroup.module_finite_tateModule (exists_nsmul_eq_point A ℓ)
    (nonempty_torsionBy_pow_addEquiv A ℓ hℓk)

/-- The Tate module `T_ℓ A` of an abelian variety of dimension `g` has rank `2g` over `ℤ_ℓ`. -/
@[sga "7 IX 2.1.12" "special case", sga "7 IX 2.1.5" "partial, special case"]
theorem finrank_tateModule (hℓk : IsUnit (ℓ : k)) :
    Module.finrank ℤ_[ℓ] (tateModule A ℓ) = 2 * abelianVarietyDimension A :=
  AbelianGroup.finrank_tateModule (exists_nsmul_eq_point A ℓ)
    (nonempty_torsionBy_pow_addEquiv A ℓ hℓk)

/-- **The Tate module modulo `ℓ^n`.** For an abelian variety `A` over an algebraically closed
field, `T_ℓ A ⧸ ℓ^n T_ℓ A ≃+ A(k)[ℓ^n]`, induced by `x ↦ x n`. -/
def tateModuleQuotientEquiv (n : ℕ) :
    (tateModule A ℓ ⧸ ((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule A ℓ))) ≃+
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ n : ℕ) : ℤ) :=
  AbelianGroup.tateQuotientEquiv (exists_nsmul_eq_point A ℓ) n

/-- The isomorphism `T_ℓ A ⧸ ℓ^n ≃+ A(k)[ℓ^n]` sends the class of `x` to its `n`-th component. -/
@[simp]
theorem tateModuleQuotientEquiv_mk (n : ℕ) (x : tateModule A ℓ) :
    tateModuleQuotientEquiv A ℓ n (Submodule.Quotient.mk x) = AbelianGroup.tateReduction ℓ n x :=
  rfl

variable {A} in
/-- The isomorphism `T_ℓ A ⧸ ℓ^n ≃+ A(k)[ℓ^n]` is equivariant for homomorphisms of abelian
varieties. -/
theorem tateModuleQuotientEquiv_mapQ {B : Over (Spec (.of k))} [GrpObj B]
    [AlgebraicGeometry.IsAbelianVariety k B]
    (α : A ⟶ B) [IsMonHom α] (n : ℕ)
    (q : tateModule A ℓ ⧸ ((ℓ : ℤ_[ℓ]) ^ n) • (⊤ : Submodule ℤ_[ℓ] (tateModule A ℓ))) :
    tateModuleQuotientEquiv B ℓ n (Submodule.mapQ _ _ (tateModuleMap ℓ α)
        (AbelianGroup.pow_smul_top_le_comap_tateModuleMap n _) q) =
      AbelianGroup.torsionMap (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).toAdditive _
        (tateModuleQuotientEquiv A ℓ n q) :=
  AbelianGroup.tateQuotientEquiv_mapQ _ _ n _ q

variable {A} in
/-- **Trace of `T_ℓ α` modulo `ℓ^n`.** Let `A` be an abelian variety over an algebraically closed
field `k`, `ℓ` a prime invertible in `k` and `α` an endomorphism of `A`. Let `e : A(k)[ℓ^n] ≃+ N`
be an isomorphism with a `ℤ/ℓ^n`-module `N` and `g` an endomorphism of `N` corresponding to `α`
under `e`. Then `Tr(T_ℓ α) mod ℓ^n = Tr_{ℤ/ℓ^n}(g)`. -/
theorem toZModPow_trace_tateModuleMap (hℓk : IsUnit (ℓ : k)) (α : A ⟶ A) [IsMonHom α] {n : ℕ}
    {N : Type*} [AddCommGroup N] [Module (ZMod (ℓ ^ n)) N]
    (e : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ n : ℕ) : ℤ) ≃+ N)
    (g : N →+ N)
    (hg : ∀ x, g (e x) = e (AbelianGroup.torsionMap
      (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).toAdditive _ x)) :
    toZModPow n (LinearMap.trace ℤ_[ℓ] (tateModule A ℓ) (tateModuleMap ℓ α)) =
      LinearMap.trace (ZMod (ℓ ^ n)) N (g.toZModLinearMap (ℓ ^ n)) :=
  have := module_free_tateModule A ℓ hℓk
  have := module_finite_tateModule A ℓ hℓk
  AbelianGroup.toZModPow_trace_tateModuleMap (exists_nsmul_eq_point A ℓ) _ e g hg

variable {A} in
/-- The trace of `T_ℓ α` modulo `ℓ^n` is the trace over `ℤ/ℓ^n` of `α` on `A(k)[ℓ^n]`. -/
theorem toZModPow_trace_tateModuleMap_torsion (hℓk : IsUnit (ℓ : k)) (α : A ⟶ A) [IsMonHom α]
    (n : ℕ) :
    letI := AddSubgroup.torsionBy.zmodModule
      (A := Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n := ℓ ^ n)
    toZModPow n (LinearMap.trace ℤ_[ℓ] (tateModule A ℓ) (tateModuleMap ℓ α)) =
      LinearMap.trace (ZMod (ℓ ^ n)) _ ((AbelianGroup.torsionMap
        (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).toAdditive
          ((ℓ ^ n : ℕ) : ℤ)).toZModLinearMap (ℓ ^ n)) :=
  let := AddSubgroup.torsionBy.zmodModule
    (A := Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n := ℓ ^ n)
  toZModPow_trace_tateModuleMap ℓ hℓk α (AddEquiv.refl _) _ fun _ => rfl

end AbelianVariety

end Stacks.Groupoids

end

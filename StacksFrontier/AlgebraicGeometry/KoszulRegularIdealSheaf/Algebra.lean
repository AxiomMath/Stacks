module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integer
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.H1RegularIdealSheaf.Algebra

/-!
# Koszul-regularity of a sequence is local on the base

Let `A` be a commutative ring and `f : Fin r → A` a finite sequence.  Koszul-regularity of `f`
is the vanishing of `Hᵢ(K_•(f))` for every `i ≠ 0`; written out, it says that for every `n` the
degree-`n` Koszul cycles are Koszul boundaries,

`ker (d : ⋀ⁿ⁺¹(Aʳ) → ⋀ⁿ(Aʳ)) ≤ range (d : ⋀ⁿ⁺²(Aʳ) → ⋀ⁿ⁺¹(Aʳ))`.

This file supplies the two halves of the local-global principle for that containment, in all
degrees at once: clearing denominators over a localization, and passing to a localization.

The one piece of machinery needed beyond the degree-one case is base change of exterior powers.
`extRes ρ n` is the map `⋀ⁿ(Aʳ) → ⋀ⁿ(Bʳ)` induced by a ring homomorphism `ρ : A → B`; it is
characterized by its values on the `ιMulti` generators together with additivity and
`ρ`-semilinearity (`ext_of_ιMulti`), which is how every statement about it is proved here and
why none of them depends on how `B` is presented as an `A`-algebra.  For a localization
`A → S` the map `extRes` *is* the localization map of the module `⋀ⁿ(Aʳ)`
(`exists_natEquiv_extRes` together with `isLocalizedModule_tmulExt`), because exterior powers of
a finite free module commute with base change; the two halves of the local-global principle are
then its surjectivity up to denominators and the torsion-ness of its kernel.

## Main results

* `extRes`, `extRes_ιMulti`, `extRes_add`, `extRes_smul`, `ext_of_ιMulti`: base change of
  exterior powers and its characterization.
* `extRes_comp`: functoriality in the ring homomorphism.
* `extRes_d`: base change commutes with the Koszul differential.
* `exists_natEquiv_extRes`, `isLocalizedModule_tmulExt`, `exists_smul_eq_extRes`,
  `exists_smul_eq_zero`: over a localization, `extRes` is the localization map.
* `isKoszulRegular_iff_forall`: Koszul-regularity as a cycle-is-a-boundary condition.
* `exists_smul_mem_range_d`: clearing denominators in a Koszul boundary expansion.
* `isKoszulRegular_localization`: Koszul-regularity passes to any localization.
* `not_isKoszulRegular_zero`: Koszul-regularity is a genuine condition — the sequence `(0)`
  over a nontrivial ring fails it.

## Implementation notes

The localizations are left abstract — an arbitrary `S` with `[IsLocalization T S]` — because the
intended instances are the rings of sections on the basic opens of an affine open, which are
localizations only through the canonical identification.

## References

* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.20.4 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
-/

@[expose] public section

namespace Stacks.RingTheory.KoszulRegularIdealSheaf

open scoped ExteriorAlgebra TensorProduct
open CategoryTheory Koszul

/-! ### Base change of exterior powers of a finite free module -/

section Ext

variable {A B : Type*} [CommRing A] [CommRing B] {r : ℕ}

/-- The base-change homomorphism `KoszulC.extBaseChange` maps `⋀ⁿ(Aʳ)` into `⋀ⁿ(Bʳ)`. -/
theorem extBaseChange_mem [Algebra A B] (n : ℕ) {y : ExteriorAlgebra A (Fin r → A)}
    (hy : y ∈ ⋀[A]^n (Fin r → A)) :
    KoszulC.extBaseChange (S := B) (r := r) y ∈ ⋀[B]^n (Fin r → B) := by
  rw [← exteriorPower.ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    rw [KoszulC.extBaseChange_ιMulti]
    exact Koszul.ιMulti_mem n _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | smul c z _ hz =>
    rw [map_smul, ← IsScalarTower.algebraMap_smul B c]
    exact Submodule.smul_mem _ _ hz

/-- **Base change of exterior powers.**  The map `⋀ⁿ(Aʳ) → ⋀ⁿ(Bʳ)` induced by a ring
homomorphism `ρ : A → B`, sending `v₁ ∧ ⋯ ∧ vₙ` to `(ρ ∘ v₁) ∧ ⋯ ∧ (ρ ∘ vₙ)`. -/
noncomputable def extRes (ρ : A →+* B) (n : ℕ) (x : ⋀[A]^n (Fin r → A)) :
    ⋀[B]^n (Fin r → B) :=
  let : Algebra A B := ρ.toAlgebra
  ⟨KoszulC.extBaseChange (S := B) (r := r) (x : ExteriorAlgebra A (Fin r → A)),
    extBaseChange_mem n x.2⟩

/-- `extRes ρ n` sends `v₁ ∧ ⋯ ∧ vₙ` to `(ρ ∘ v₁) ∧ ⋯ ∧ (ρ ∘ vₙ)`. -/
@[simp]
theorem extRes_ιMulti (ρ : A →+* B) (n : ℕ) (v : Fin n → (Fin r → A)) :
    extRes ρ n (exteriorPower.ιMulti A n v)
      = exteriorPower.ιMulti B n (fun i j => ρ (v i j)) := by
  let _i : Algebra A B := ρ.toAlgebra
  refine Subtype.ext ?_
  show KoszulC.extBaseChange
      ((exteriorPower.ιMulti A n v : ⋀[A]^n (Fin r → A)) : ExteriorAlgebra A (Fin r → A))
    = ((exteriorPower.ιMulti B n (fun i j => ρ (v i j)) : ⋀[B]^n (Fin r → B)) :
        ExteriorAlgebra B (Fin r → B))
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    KoszulC.extBaseChange_ιMulti]
  rfl

/-- `extRes ρ n` is additive. -/
@[simp]
theorem extRes_add (ρ : A →+* B) (n : ℕ) (x y : ⋀[A]^n (Fin r → A)) :
    extRes ρ n (x + y) = extRes ρ n x + extRes ρ n y := by
  let _i : Algebra A B := ρ.toAlgebra
  refine Subtype.ext ?_
  show KoszulC.extBaseChange
      ((x : ExteriorAlgebra A (Fin r → A)) + (y : ExteriorAlgebra A (Fin r → A)))
    = KoszulC.extBaseChange (x : ExteriorAlgebra A (Fin r → A))
      + KoszulC.extBaseChange (y : ExteriorAlgebra A (Fin r → A))
  exact map_add _ _ _

/-- `extRes ρ n` is `ρ`-semilinear: `extRes ρ n (c • x) = ρ c • extRes ρ n x`. -/
@[simp]
theorem extRes_smul (ρ : A →+* B) (n : ℕ) (c : A) (x : ⋀[A]^n (Fin r → A)) :
    extRes ρ n (c • x) = ρ c • extRes ρ n x := by
  let _i : Algebra A B := ρ.toAlgebra
  refine Subtype.ext ?_
  show KoszulC.extBaseChange (c • (x : ExteriorAlgebra A (Fin r → A)))
    = ρ c • KoszulC.extBaseChange (x : ExteriorAlgebra A (Fin r → A))
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul B c _).symm

/-- A `ρ`-semilinear map sends `0` to `0`. -/
private theorem map_zero_of_map_smul {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] (ρ : A →+* B) {F : M → N}
    (hFs : ∀ (c : A) x, F (c • x) = ρ c • F x) : F 0 = 0 := by
  have h := hFs 0 0
  rwa [zero_smul, map_zero, zero_smul] at h

/-- `extRes ρ n` sends `0` to `0`. -/
@[simp]
theorem extRes_zero (ρ : A →+* B) (n : ℕ) : extRes ρ n (0 : ⋀[A]^n (Fin r → A)) = 0 :=
  map_zero_of_map_smul ρ (extRes_smul ρ n)

/-- `extRes ρ n` commutes with negation. -/
@[simp]
theorem extRes_neg (ρ : A →+* B) (n : ℕ) (x : ⋀[A]^n (Fin r → A)) :
    extRes ρ n (-x) = -extRes ρ n x := by
  have h := extRes_smul ρ n (-1 : A) x
  rwa [neg_one_smul, map_neg, map_one, neg_one_smul] at h

/-- `extRes ρ n` commutes with subtraction. -/
@[simp]
theorem extRes_sub (ρ : A →+* B) (n : ℕ) (x y : ⋀[A]^n (Fin r → A)) :
    extRes ρ n (x - y) = extRes ρ n x - extRes ρ n y := by
  rw [sub_eq_add_neg, extRes_add, extRes_neg, sub_eq_add_neg]

/-- **Characterization of base change on exterior powers.**  Two additive, `ρ`-semilinear maps
out of `⋀ⁿ(Aʳ)` that agree on the wedges of `n` vectors agree everywhere. -/
theorem ext_of_ιMulti (ρ : A →+* B) (n : ℕ)
    {F G : ⋀[A]^n (Fin r → A) → ⋀[B]^n (Fin r → B)}
    (hFa : ∀ x y, F (x + y) = F x + F y) (hFs : ∀ (c : A) x, F (c • x) = ρ c • F x)
    (hGa : ∀ x y, G (x + y) = G x + G y) (hGs : ∀ (c : A) x, G (c • x) = ρ c • G x)
    (h : ∀ v : Fin n → (Fin r → A),
      F (exteriorPower.ιMulti A n v) = G (exteriorPower.ιMulti A n v))
    (x : ⋀[A]^n (Fin r → A)) : F x = G x := by
  have hx : x ∈ Submodule.span A (Set.range ⇑(exteriorPower.ιMulti A n (M := Fin r → A))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨v, rfl⟩ := hz; exact h v
  | zero => rw [map_zero_of_map_smul ρ hFs, map_zero_of_map_smul ρ hGs]
  | add z w _ _ hz hw => rw [hFa, hGa, hz, hw]
  | smul c z _ hz => rw [hFs, hGs, hz]

/-- **Base change of exterior powers is functorial.** -/
theorem extRes_comp {C : Type*} [CommRing C] (ρ : A →+* B) (σ : B →+* C) (n : ℕ)
    (x : ⋀[A]^n (Fin r → A)) :
    extRes σ n (extRes ρ n x) = extRes (σ.comp ρ) n x := by
  refine ext_of_ιMulti (σ.comp ρ) n (F := fun y => extRes σ n (extRes ρ n y))
    (G := fun y => extRes (σ.comp ρ) n y) (fun y z => by rw [extRes_add, extRes_add])
    (fun c y => by rw [extRes_smul, extRes_smul]; rfl)
    (fun y z => extRes_add _ _ _ _) (fun c y => extRes_smul _ _ _ _) (fun v => ?_) x
  rw [extRes_ιMulti, extRes_ιMulti, extRes_ιMulti]
  rfl

/-- **Base change commutes with the Koszul differential.** -/
theorem extRes_d (ρ : A →+* B) (f : Fin r → A) (n : ℕ) (x : ⋀[A]^(n + 1) (Fin r → A)) :
    extRes ρ n (d (seqDual f) n x)
      = d (seqDual fun i => ρ (f i)) n (extRes ρ (n + 1) x) := by
  let _i : Algebra A B := ρ.toAlgebra
  refine Subtype.ext ?_
  show KoszulC.extBaseChange
      ((d (seqDual f) n x : ⋀[A]^n (Fin r → A)) : ExteriorAlgebra A (Fin r → A))
    = ((d (seqDual fun i => ρ (f i)) n (extRes ρ (n + 1) x) : ⋀[B]^n (Fin r → B)) :
        ExteriorAlgebra B (Fin r → B))
  rw [d_apply_coe, d_apply_coe]
  exact (KoszulC.contractLeft_extBaseChange_comm (S := B) f (n + 1) _ x.2).symm

end Ext

/-! ### Over a localization, base change is the localization map -/

section Localization

variable {A : Type*} [CommRing A] (S : Type*) [CommRing S] [Algebra A S] {r : ℕ}

/-- The canonical `A`-linear map `⋀ⁿ(Aʳ) → S ⊗[A] ⋀ⁿ(Aʳ)`, `x ↦ 1 ⊗ x`. -/
noncomputable def tmulExt (n : ℕ) :
    (⋀[A]^n (Fin r → A)) →ₗ[A] (S ⊗[A] (⋀[A]^n (Fin r → A))) :=
  TensorProduct.mk A S (⋀[A]^n (Fin r → A)) 1

/-- **Base change of exterior powers is base change.**  The map `extRes` along `A → S` is, up to
the canonical isomorphism `S ⊗[A] ⋀ⁿ(Aʳ) ≅ ⋀ⁿ(Sʳ)`, the map `x ↦ 1 ⊗ x`; exterior powers of a
finite free module commute with base change. -/
theorem exists_natEquiv_extRes (n : ℕ) :
    ∃ β : (S ⊗[A] (⋀[A]^n (Fin r → A))) ≃ₗ[S] (⋀[S]^n (Fin r → S)),
      ∀ x : ⋀[A]^n (Fin r → A),
        β (tmulExt S n x) = extRes (algebraMap A S) n x := by
  obtain ⟨β, hβ⟩ := KoszulC.extPow_baseChange_natEquiv (R := A) (S := S) (r := r) n
  refine ⟨β, fun x => ?_⟩
  refine ext_of_ιMulti (algebraMap A S) n (F := fun y => β (tmulExt S n y))
    (G := fun y => extRes (algebraMap A S) n y) (fun y z => ?_) (fun c y => ?_)
    (fun y z => extRes_add _ _ _ _) (fun c y => extRes_smul _ _ _ _) (fun v => ?_) x
  · rw [LinearMap.map_add, map_add]
  · have h : tmulExt S n (c • y) = (algebraMap A S c) • tmulExt S n y := by
      rw [LinearMap.map_smul, IsScalarTower.algebraMap_smul]
    rw [h, LinearEquiv.map_smul]
  · rw [extRes_ιMulti]
    exact hβ v

variable (T : Submonoid A) [IsLocalization T S]

/-- **Over a localization, `S ⊗[A] ⋀ⁿ(Aʳ)` is the localization of the module `⋀ⁿ(Aʳ)`.** -/
instance isLocalizedModule_tmulExt (n : ℕ) : IsLocalizedModule T (tmulExt S n (r := r)) := by
  change IsLocalizedModule T (TensorProduct.mk A S (⋀[A]^n (Fin r → A)) 1)
  exact IsLocalization.tensorProduct_isLocalizedModule T S

/-- **Surjectivity up to denominators.**  Every element of `⋀ⁿ(Sʳ)` becomes a base-changed
element of `⋀ⁿ(Aʳ)` after multiplication by an element of the localizing submonoid. -/
theorem exists_smul_eq_extRes (n : ℕ) (z : ⋀[S]^n (Fin r → S)) :
    ∃ t ∈ T, ∃ x : ⋀[A]^n (Fin r → A),
      algebraMap A S t • z = extRes (algebraMap A S) n x := by
  obtain ⟨β, hβ⟩ := exists_natEquiv_extRes (A := A) S (r := r) n
  obtain ⟨⟨x, t⟩, ht⟩ := IsLocalizedModule.surj T (tmulExt S n (r := r)) (β.symm z)
  refine ⟨(t : A), t.2, x, ?_⟩
  have h : β ((t : A) • β.symm z) = β (tmulExt S n x) := congrArg β ht
  rwa [← IsScalarTower.algebraMap_smul S (t : A) (β.symm z), LinearEquiv.map_smul,
    β.apply_symm_apply, hβ] at h

/-- **The kernel of base change is torsion.**  An element of `⋀ⁿ(Aʳ)` dying in `⋀ⁿ(Sʳ)` is
killed by an element of the localizing submonoid. -/
theorem exists_smul_eq_zero (n : ℕ) (x : ⋀[A]^n (Fin r → A))
    (hx : extRes (algebraMap A S) n x = 0) : ∃ t ∈ T, t • x = 0 := by
  obtain ⟨β, hβ⟩ := exists_natEquiv_extRes (A := A) S (r := r) n
  have h : tmulExt S n x = tmulExt S n (0 : ⋀[A]^n (Fin r → A)) := by
    refine β.injective ?_
    rw [hβ, hβ, hx, extRes_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists T (tmulExt S n (r := r))).mp h
  exact ⟨(t : A), t.2, by rwa [smul_zero] at ht⟩

end Localization

/-! ### Koszul-regularity as a cycle-is-a-boundary condition -/

section Criterion

variable {A : Type*} [CommRing A] {r : ℕ}

/-- **Koszul-regularity spelled out.**  A sequence is Koszul-regular exactly when, in every
degree, a Koszul cycle is a Koszul boundary. -/
theorem isKoszulRegular_iff_forall (f : Fin r → A) :
    IsKoszulRegular f ↔ ∀ (n : ℕ) (z : ⋀[A]^(n + 1) (Fin r → A)), d (seqDual f) n z = 0 →
      ∃ w : ⋀[A]^(n + 2) (Fin r → A), d (seqDual f) (n + 1) w = z := by
  have key : ∀ n : ℕ, Limits.IsZero ((seqComplex f).homology (n + 1)) ↔
      ∀ z : ⋀[A]^(n + 1) (Fin r → A), d (seqDual f) n z = 0 →
        ∃ w : ⋀[A]^(n + 2) (Fin r → A), d (seqDual f) (n + 1) w = z := by
    intro n
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    show LinearMap.ker ((seqComplex f).d (n + 1) n).hom ≤
      LinearMap.range ((seqComplex f).d (n + 2) (n + 1)).hom ↔ _
    simp only [seqComplex_d]
    rfl
  constructor
  · intro h n
    exact (key n).mp (h (n + 1) (Nat.succ_ne_zero n))
  · intro h i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    exact (key n).mpr (h n)

end Criterion

/-! ### The local-global principle -/

section LocalGlobal

variable {A : Type*} [CommRing A] (T : Submonoid A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization T S] {r : ℕ}

/-- **Clearing denominators in a Koszul boundary expansion.**  If the image of a degree-`n+1`
Koszul chain in a localization is a boundary there, then some element of the localizing submonoid
multiplies it into the boundaries over `A`. -/
theorem exists_smul_mem_range_d (f : Fin r → A) (n : ℕ) (z : ⋀[A]^(n + 1) (Fin r → A))
    (h : extRes (algebraMap A S) (n + 1) z
      ∈ LinearMap.range (d (seqDual fun i => algebraMap A S (f i)) (n + 1))) :
    ∃ t ∈ T, t • z ∈ LinearMap.range (d (seqDual f) (n + 1)) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, htT, x, hx⟩ := exists_smul_eq_extRes (A := A) S T (n + 2) w
  have key : extRes (algebraMap A S) (n + 1) (t • z - d (seqDual f) (n + 1) x) = 0 := by
    rw [extRes_sub, extRes_smul, extRes_d, ← hx, LinearMap.map_smul, hw, sub_self]
  obtain ⟨u, huT, hu⟩ := exists_smul_eq_zero (A := A) S T (n + 1) _ key
  refine ⟨u * t, mul_mem huT htT, u • x, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul] at hu
  rw [LinearMap.map_smul, ← hu]

include T in
/-- **Koszul-regularity passes to a localization.** -/
theorem isKoszulRegular_localization (f : Fin r → A) (hf : IsKoszulRegular f) :
    IsKoszulRegular fun i => algebraMap A S (f i) := by
  rw [isKoszulRegular_iff_forall] at hf ⊢
  intro n z hz
  obtain ⟨t, htT, x, hx⟩ := exists_smul_eq_extRes (A := A) S T (n + 1) z
  have h1 : extRes (algebraMap A S) n (d (seqDual f) n x) = 0 := by
    rw [extRes_d, ← hx, LinearMap.map_smul, hz, smul_zero]
  obtain ⟨u, huT, hu⟩ := exists_smul_eq_zero (A := A) S T n _ h1
  rw [← LinearMap.map_smul] at hu
  obtain ⟨y, hy⟩ := hf n (u • x) hu
  obtain ⟨v, hv⟩ := IsLocalization.map_units S (⟨u * t, mul_mem huT htT⟩ : T)
  have hdy : d (seqDual fun i => algebraMap A S (f i)) (n + 1)
      (extRes (algebraMap A S) (n + 2) y) = ((v : Sˣ) : S) • z := by
    rw [← extRes_d, hy, extRes_smul, ← hx, smul_smul, ← map_mul]
    exact congrArg (· • z) hv.symm
  refine ⟨((v⁻¹ : Sˣ) : S) • extRes (algebraMap A S) (n + 2) y, ?_⟩
  rw [LinearMap.map_smul, hdy, smul_smul, Units.inv_mul, one_smul]

end LocalGlobal

/-! ### Non-degeneracy -/

section Nondegeneracy

/-- **Koszul-regularity is a genuine condition.**  The one-term sequence `(0)` over a nontrivial
ring is not Koszul-regular: its first Koszul homology is already nonzero, since the span of the
trivial relations is `⊥` while every ring element is a relation.  Recorded because the affine
criterion of Stacks tag 063G identifies the sheaf-theoretic condition with this one, and an
identification with a condition that always held would say nothing. -/
theorem not_isKoszulRegular_zero {A : Type*} [CommRing A] [Nontrivial A] :
    ¬ IsKoszulRegular (fun _ : Fin 1 => (0 : A)) := fun h =>
  Stacks.RingTheory.H1RegularIdealSheaf.not_isH1Regular_zero (h 1 one_ne_zero)

end Nondegeneracy

end Stacks.RingTheory.KoszulRegularIdealSheaf

end

module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.CategoryTheory.Abelian.PowExact

/-!
# The image of multiplication by `ℓᴺ` is pow-exact once torsion is divisible

Let `M` be an object of an abelian category in which, for some `N ≤ m`, every generalized
element killed by `ℓᵐ` becomes divisible by `ℓᴺ⁺¹` after multiplication by `ℓᴺ`. Then an element
of `ℓᴺ M` killed by `ℓᵃ` lies in `ℓᵐ⁺¹⁻ᵃ M`, so the image `A = ℓᴺ M` of multiplication by `ℓᴺ`
is pow-exact of exponent `m + 1 - N`: for a sheaf of `ℤ/ℓᵐ⁺¹ℤ`-modules it is a flat sheaf of
`ℤ/ℓᵐ⁺¹⁻ᴺℤ`-modules.

Moreover the images of `ℓᴺ` along a map `t : M' ⟶ M` exhibiting `M` as `M' / ℓᴺ⁺ⁿ⁺¹ M'` are
again related by a quotient by `ℓⁿ⁺¹`.

These are the two properties of the torsion-free model `ℓᴺ F` of an ℓ-adic sheaf `F` used in the
proof of [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2): its levels are flat, and they
form an ℓ-adic sheaf.

## Main results

* `CategoryTheory.Abelian.exists_pow_nsmul_eq_of_divisible`: an element `ℓᴺ h` of `ℓᴺ M` killed
  by `ℓᵃ` is `ℓᵐ⁺¹⁻ᵃ` times an element, up to refinement.
* `CategoryTheory.Abelian.powExact_of_image`: the image of `ℓᴺ` is pow-exact.
* `CategoryTheory.Abelian.isColimitImageTransition`: the images of `ℓᴺ` along a quotient by
  `ℓᴺ⁺ⁿ⁺¹` are related by a quotient by `ℓⁿ⁺¹`.
* `CategoryTheory.Abelian.PowExact.of_map`: pow-exactness descends along a faithful exact
  functor.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public section

namespace CategoryTheory.Abelian

open CategoryTheory Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C] {ℓ : ℕ}

/-- Multiplying a generalized element by `ℓⁱ` and then by `ℓʲ` is multiplying it by `ℓʲ⁺ⁱ`. -/
theorem pow_nsmul_pow_nsmul {T M : C} (f : T ⟶ M) (i j : ℕ) :
    (ℓ ^ j) • (ℓ ^ i) • f = (ℓ ^ (i + j)) • f := by
  rw [smul_smul, ← pow_add, add_comm]

/-- Multiplying by `ℓⁱ` and then by `ℓʲ` is multiplying by `ℓᵏ` whenever `i + j = k`. -/
private theorem pow_nsmul_pow_nsmul_of_add_eq {T M : C} (f : T ⟶ M) {i j k : ℕ} (h : i + j = k) :
    (ℓ ^ j) • (ℓ ^ i) • f = (ℓ ^ k) • f := by
  rw [pow_nsmul_pow_nsmul, h]

/-- **Iterated divisibility.** If every element killed by `ℓᵐ` becomes divisible by `ℓᴺ⁺¹` after
multiplication by `ℓᴺ`, then `ℓᴺ h` is divisible by `ℓᵐ` for every `h` killed by `ℓᴺ⁺¹`. -/
theorem exists_pow_nsmul_eq_of_divisible_of_succ {M : C} {N m : ℕ} (hNm : N ≤ m)
    (hdiv : ∀ ⦃T : C⦄ (g : T ⟶ M), (ℓ ^ m) • g = 0 →
      ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ M), π ≫ ((ℓ ^ N) • g) = (ℓ ^ (N + 1)) • y)
    {T : C} (h : T ⟶ M) (hh : (ℓ ^ (N + 1)) • h = 0) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ M), π ≫ ((ℓ ^ N) • h) = (ℓ ^ m) • y := by
  suffices H : ∀ j, j ≤ m - N → ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ M),
      π ≫ ((ℓ ^ N) • h) = (ℓ ^ (N + j)) • y ∧ (ℓ ^ (N + j + 1)) • y = 0 by
    obtain ⟨T', π, hπ, y, hy, -⟩ := H (m - N) le_rfl
    exact ⟨T', π, hπ, y, by rwa [Nat.add_sub_cancel' hNm] at hy⟩
  intro j
  induction j with
  | zero => exact fun _ => ⟨T, 𝟙 T, inferInstance, h, by simp, by simpa using hh⟩
  | succ j ih =>
    intro hj
    obtain ⟨T₁, π₁, hπ₁, y₁, hy₁, hz₁⟩ := ih (by omega)
    have hm : (ℓ ^ m) • y₁ = 0 := by
      obtain ⟨d, hd⟩ : ∃ d, m = N + j + 1 + d := ⟨m - (N + j + 1), by omega⟩
      rw [hd, ← pow_nsmul_pow_nsmul, hz₁, smul_zero]
    obtain ⟨T₂, π₂, hπ₂, y₂, hy₂⟩ := hdiv y₁ hm
    refine ⟨T₂, π₂ ≫ π₁, inferInstance, y₂, ?_, ?_⟩
    · rw [Category.assoc, hy₁,
        show (ℓ ^ (N + j)) • y₁ = (ℓ ^ j) • (ℓ ^ N) • y₁ from (pow_nsmul_pow_nsmul y₁ N j).symm,
        comp_nsmul, hy₂]
      exact pow_nsmul_pow_nsmul_of_add_eq _ (by omega)
    · have e : (ℓ ^ (N + (j + 1) + 1)) • y₂ = (ℓ ^ (j + 1)) • (ℓ ^ (N + 1)) • y₂ := by
        exact (pow_nsmul_pow_nsmul_of_add_eq _ (by omega)).symm
      rw [e, ← hy₂, ← comp_nsmul, pow_nsmul_pow_nsmul,
        show N + (j + 1) = N + j + 1 by omega, hz₁, comp_zero]

/-- **Torsion in `ℓᴺ M` is as divisible as in a free module.** Under the divisibility hypothesis
of `CategoryTheory.Abelian.exists_pow_nsmul_eq_of_divisible_of_succ`, an element `ℓᴺ h` killed by
`ℓᵃ`, `N + a ≤ m + 1`, is `ℓᵐ⁺¹⁻ᵃ` times an element, up to refinement. -/
theorem exists_pow_nsmul_eq_of_divisible {M : C} {N m : ℕ} (hNm : N ≤ m)
    (hdiv : ∀ ⦃T : C⦄ (g : T ⟶ M), (ℓ ^ m) • g = 0 →
      ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ M), π ≫ ((ℓ ^ N) • g) = (ℓ ^ (N + 1)) • y)
    (a : ℕ) (ha : N + a ≤ m + 1) {T : C} (h : T ⟶ M) (hh : (ℓ ^ (N + a)) • h = 0) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (w : T' ⟶ M),
      π ≫ ((ℓ ^ N) • h) = (ℓ ^ (m + 1 - a)) • w := by
  induction a generalizing T with
  | zero => exact ⟨T, 𝟙 T, inferInstance, 0, by simpa using hh⟩
  | succ a ih =>
    obtain ⟨e, he⟩ : ∃ e, m = N + e + a := ⟨m - a - N, by omega⟩
    subst he
    obtain ⟨T₁, π₁, hπ₁, w₁, hw₁⟩ := ih (by omega) (ℓ • h) (by
      rw [smul_smul, ← pow_succ, show N + a + 1 = N + (a + 1) by omega]
      exact hh)
    have hw₁' : π₁ ≫ ((ℓ ^ (N + 1)) • h) = (ℓ ^ (N + e + 1)) • w₁ := by
      rw [show N + e + a + 1 - a = N + e + 1 by omega, smul_smul, ← pow_succ] at hw₁
      exact hw₁
    obtain ⟨T₂, π₂, hπ₂, y, hy⟩ := exists_pow_nsmul_eq_of_divisible_of_succ (by omega) hdiv
      (π₁ ≫ h - (ℓ ^ e) • w₁) (by
        rw [smul_sub, ← comp_nsmul, hw₁', sub_eq_zero]
        exact (pow_nsmul_pow_nsmul_of_add_eq _ (by omega)).symm)
    refine ⟨T₂, π₂ ≫ π₁, inferInstance, (ℓ ^ a) • y + π₂ ≫ w₁, ?_⟩
    have e₁ : π₂ ≫ π₁ ≫ ((ℓ ^ N) • h) = π₂ ≫ ((ℓ ^ N) • (π₁ ≫ h - (ℓ ^ e) • w₁)) +
        (ℓ ^ (N + e)) • (π₂ ≫ w₁) := by
      simp only [smul_sub, comp_sub, comp_nsmul, pow_nsmul_pow_nsmul, add_comm e N,
        sub_add_cancel]
    rw [Category.assoc, e₁, hy, show N + e + a + 1 - (a + 1) = N + e by omega, smul_add,
      pow_nsmul_pow_nsmul, show a + (N + e) = N + e + a by omega]

/-- Through the factorisation `p ≫ ι` of `ℓᴺ`, `ℓᵃ` on the image is `ℓᴺ⁺ᵃ` on `M`. -/
private theorem comp_pow_nsmul_comp_eq {M A : C} {N : ℕ} (a : ℕ) (p : M ⟶ A) (ι : A ⟶ M)
    (hpι : p ≫ ι = (ℓ ^ N) • 𝟙 M) : p ≫ ((ℓ ^ a) • 𝟙 A) ≫ ι = (ℓ ^ (N + a)) • 𝟙 M := by
  rw [nsmul_comp, comp_nsmul, Category.id_comp, hpι,
    pow_nsmul_pow_nsmul]

/-- **The image of `ℓᴺ` is pow-exact.** If `p ≫ ι` is a factorisation of `ℓᴺ` on `M` through an
epimorphism and a monomorphism, and torsion in `M` is divisible as in
`CategoryTheory.Abelian.exists_pow_nsmul_eq_of_divisible_of_succ` at `m = N + n`, the image is
pow-exact of exponent `n + 1`. -/
theorem powExact_of_image {M A : C} {N n : ℕ}
    (hdiv : ∀ ⦃T : C⦄ (g : T ⟶ M), (ℓ ^ (N + n)) • g = 0 →
      ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ M), π ≫ ((ℓ ^ N) • g) = (ℓ ^ (N + 1)) • y)
    (p : M ⟶ A) [Epi p] (ι : A ⟶ M) [Mono ι] (hpι : p ≫ ι = (ℓ ^ N) • 𝟙 M) :
    PowExact ℓ (n + 1) A := by
  intro a ha T x hx
  obtain ⟨T₁, π₁, hπ₁, h, hh⟩ := surjective_up_to_refinements_of_epi p x
  have hh' : (ℓ ^ (N + a)) • h = 0 := by
    have e : (ℓ ^ (N + a)) • h = π₁ ≫ x ≫ ((ℓ ^ a) • 𝟙 A) ≫ ι := by
      rw [reassoc_of% hh, comp_pow_nsmul_comp_eq a p ι hpι, comp_nsmul, Category.comp_id]
    rw [e, ← Category.assoc x, hx, zero_comp, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, w, hw⟩ := exists_pow_nsmul_eq_of_divisible (by omega) hdiv a
    (by omega) h hh'
  refine ⟨T₂, π₂ ≫ π₁, inferInstance, w ≫ p, ?_⟩
  rw [← cancel_mono ι]
  simp only [Category.assoc]
  rw [reassoc_of% hh, hpι]
  simp only [comp_nsmul, nsmul_comp, Category.comp_id, Category.id_comp] at hw ⊢
  rw [hpι, comp_nsmul, Category.comp_id, hw]
  exact (pow_nsmul_pow_nsmul_of_add_eq _ (by omega)).symm

/-- The image of `ℓᴺ` on an object killed by `ℓᴺ⁺ᵏ` is killed by `ℓᵏ`. -/
theorem image_pow_nsmul_eq_zero {M A : C} {N k : ℕ} (hM : (ℓ ^ (N + k)) • 𝟙 M = 0)
    (p : M ⟶ A) [Epi p] (ι : A ⟶ M) [Mono ι] (hpι : p ≫ ι = (ℓ ^ N) • 𝟙 M) :
    (ℓ ^ k) • 𝟙 A = 0 := by
  rw [← cancel_epi p, ← cancel_mono ι, comp_zero, zero_comp, Category.assoc,
    comp_pow_nsmul_comp_eq k p ι hpι, hM]

/-- `ℓⁿ⁺¹` kills the map induced on images of `ℓᴺ` by a map into an object killed by
`ℓᴺ⁺ⁿ⁺¹`. -/
theorem image_transition_condition {M A' A : C} {N n : ℕ} (hM : (ℓ ^ (N + (n + 1))) • 𝟙 M = 0)
    (p : M ⟶ A) [Epi p] (ι : A ⟶ M) [Mono ι] (hpι : p ≫ ι = (ℓ ^ N) • 𝟙 M) (τ : A' ⟶ A) :
    ((ℓ ^ (n + 1)) • 𝟙 A') ≫ τ = 0 := by
  rw [nsmul_comp, Category.id_comp, ← Category.comp_id τ, ← comp_nsmul,
    image_pow_nsmul_eq_zero hM p ι hpι, comp_zero]

/-- **Images of `ℓᴺ` along a quotient by `ℓᴺ⁺ⁿ⁺¹`.** If `t : M' ⟶ M` exhibits `M` as the quotient
of `M'` by `ℓᴺ⁺ⁿ⁺¹`, the map `τ` it induces between the images of `ℓᴺ` exhibits the image in `M`
as the quotient of the image in `M'` by `ℓⁿ⁺¹`. -/
noncomputable def isColimitImageTransition {M' M A' A : C} {N n : ℕ}
    (hM : (ℓ ^ (N + (n + 1))) • 𝟙 M = 0) (t : M' ⟶ M)
    (ht : ((ℓ ^ (N + (n + 1))) • 𝟙 M') ≫ t = 0)
    (htc : IsColimit (CokernelCofork.ofπ t ht))
    (p' : M' ⟶ A') [Epi p'] (ι' : A' ⟶ M') [Mono ι'] (hpι' : p' ≫ ι' = (ℓ ^ N) • 𝟙 M')
    (p : M ⟶ A) [Epi p] (ι : A ⟶ M) [Mono ι] (hpι : p ≫ ι = (ℓ ^ N) • 𝟙 M)
    (τ : A' ⟶ A) (hτ : p' ≫ τ = t ≫ p) :
    IsColimit (CokernelCofork.ofπ τ (image_transition_condition hM p ι hpι τ)) := by
  have : Epi t := Cofork.IsColimit.epi htc
  have : Epi τ := epi_of_epi_fac hτ
  let S := ShortComplex.mk _ _ (image_transition_condition hM p ι hpι τ)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    obtain ⟨T₁, π₁, hπ₁, h, hh⟩ := surjective_up_to_refinements_of_epi p' x
    have h0 : ((ℓ ^ N) • h) ≫ t = 0 := by
      have e : ((ℓ ^ N) • h) ≫ t = ((π₁ ≫ x) ≫ τ) ≫ ι := by
        rw [hh]
        simp only [Category.assoc]
        rw [reassoc_of% hτ, hpι]
        simp only [comp_nsmul, nsmul_comp, Category.comp_id]
      change x ≫ τ = 0 at hx
      rw [e, Category.assoc π₁, hx, comp_zero, zero_comp]
    obtain ⟨T₂, π₂, hπ₂, y, hy⟩ :=
      (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk _ t ht) htc).exact_up_to_refinements
        _ h0
    refine ⟨T₂, π₂ ≫ π₁, inferInstance, y ≫ p', ?_⟩
    change (π₂ ≫ π₁) ≫ x = (y ≫ p') ≫ ((ℓ ^ (n + 1)) • 𝟙 A')
    change π₂ ≫ ((ℓ ^ N) • h) = y ≫ ((ℓ ^ (N + (n + 1))) • 𝟙 M') at hy
    rw [← cancel_mono ι']
    simp only [Category.assoc]
    rw [reassoc_of% hh, hpι']
    simp only [comp_nsmul, nsmul_comp, Category.comp_id, Category.id_comp] at hy ⊢
    rw [hpι', comp_nsmul, Category.comp_id, hy, pow_nsmul_pow_nsmul]
  exact hS.gIsCokernel

/-! ### The abelian image of `ℓᴺ`, read through an isomorphism

Stated for an arbitrary abelian category, so that applying them to a concrete one involves no
instance search there. -/

/-- The abelian image of `ℓᴺ` on an object killed by `ℓᴺ⁺ᵏ` is killed by `ℓᵏ`. -/
theorem abelianImage_pow_nsmul_eq_zero {M : C} {N k : ℕ} (hM : (ℓ ^ (N + k)) • 𝟙 M = 0) :
    (ℓ ^ k) • 𝟙 (Abelian.image ((ℓ ^ N) • 𝟙 M)) = 0 :=
  image_pow_nsmul_eq_zero hM _ _ (Abelian.image.fac _)

/-- The factorisation through the abelian image, followed by an isomorphism, is an epimorphism. -/
theorem epi_factorThruImage_comp_inv {M D A : C} (f : M ⟶ D) (e : A ≅ Abelian.image f) :
    Epi (Abelian.factorThruImage f ≫ e.inv) :=
  inferInstance

/-- An isomorphism followed by the inclusion of the abelian image is a monomorphism. -/
theorem mono_hom_comp_image_ι {M D A : C} (f : M ⟶ D) (e : A ≅ Abelian.image f) :
    Mono (e.hom ≫ Abelian.image.ι f) :=
  inferInstance

/-- The image factorisation, read through an isomorphism. -/
theorem factorThruImage_comp_inv_comp_hom_comp_image_ι {M D A : C} (f : M ⟶ D)
    (e : A ≅ Abelian.image f) :
    (Abelian.factorThruImage f ≫ e.inv) ≫ e.hom ≫ Abelian.image.ι f = f := by
  simp

/-- **Pow-exactness descends along a faithful exact functor.** -/
theorem PowExact.of_map {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]
    [PreservesLimitsOfShape WalkingParallelPair G] [G.IsLeftAdjoint] [G.Faithful] {m : ℕ} {X : C}
    (hX : (ℓ ^ m) • 𝟙 X = 0) (h : PowExact ℓ m (G.obj X)) : PowExact ℓ m X := by
  have : PreservesFiniteLimits G := Functor.preservesFiniteLimits_of_preservesKernels G
  have hGX : (ℓ ^ m) • 𝟙 (G.obj X) = 0 := by
    rw [← G.map_id, ← G.map_nsmul, hX, G.map_zero]
  refine powExact_of_exact hX (fun a ha => ?_)
  rw [← ShortComplex.exact_map_iff_of_faithful _ G]
  refine (ShortComplex.exact_iff_of_iso ?_).1 (h.exact hGX ha)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [G.map_nsmul]) (by simp [G.map_nsmul])

end CategoryTheory.Abelian

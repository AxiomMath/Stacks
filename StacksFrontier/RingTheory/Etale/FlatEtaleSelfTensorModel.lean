module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# A flat algebra with étale self-tensor product is étale-locally a localization of an étale one

Let `B → C` be a flat ring map such that the first inclusion `C → C ⊗_B C` is étale. This is the
algebra of a flat morphism `Spec C ⟶ Spec B` whose fibre square with itself is an étale cover of
`Spec C`; it is what an affine étale chart of a flat monomorphism of algebraic spaces into
`Spec B` looks like, since for a monomorphism the fibre product of the chart with itself over the
space is its fibre product over `Spec B`.

The algebra `C` need not be of finite presentation over `B`, but its localization at a prime `p`
of `B` in the image of `Spec C` is étale over `B_p`: it is faithfully flat over `B_p`, and its
base change `C_p ⊗_{B_p} C_p` along itself is the étale `C_p`-algebra `C_p ⊗_C (C ⊗_B C)`, so
étaleness descends. An étale `B_p`-algebra is the localization of a finitely presented
`B`-algebra `D` with a map `D → C`, and the étale locus, the image on spectra, and the
bijectivity of `C ⊗_B D → C ⊗_B C` (both sides finitely presented over `C`) all spread out from
`p` to a basic open neighbourhood `D(g)`. The upshot is an étale `B_g`-algebra `D_g`, surjective
on spectra, with a map `ψ : D_g → C_g` such that `C ⊗_B D_g → C ⊗_B C_g` is bijective: in
geometric terms, after base change to `Spec C`, the chart `Spec C_g ⟶ Spec B_g` and the étale
cover `Spec D_g ⟶ Spec B_g` become isomorphic.

## Main results

* `Algebra.etale_localization_of_etale_tensorProduct`: the localization `C_p` is étale over
  `B_p`.
* `Algebra.exists_etale_bijective_map`: the étale model over a basic open neighbourhood.

## Implementation notes

The localization of an algebra map at a submonoid of the base is Mathlib's `IsLocalization.map`,
at the canonical localizations `Localization (Algebra.algebraMapSubmonoid _ _)`. Its
bijectivity is tracked through two elementwise conditions — every element becomes an image after
multiplication by an element of the submonoid, and every element of the kernel is killed by one
— which are what spread out from a localization at a prime to a localization at one element.
The spreading of bijectivity for a map of finitely presented algebras uses the finite
generation of the kernel of a surjection between finitely presented algebras
(`Algebra.FinitePresentation.ker_fG_of_surjective`); the bijectivity of the base change along
the flat algebra `C` uses exactness of `C ⊗_B -` (`Module.Flat.lTensor_exact`).

## References

* [Stacks Project, Tag 0B8A](https://stacks.math.columbia.edu/tag/0B8A)
* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
-/

@[expose] public section

open TensorProduct

universe u

namespace Algebra

variable {A P Q : Type u} [CommRing A] [CommRing P] [CommRing Q] [Algebra A P] [Algebra A Q]

/-- The localization `P_N → Q_N` of an algebra map at a submonoid `N` of the base. -/
private noncomputable abbrev locMap (Ψ : P →ₐ[A] Q) (N : Submonoid A) :
    Localization (Algebra.algebraMapSubmonoid P N) →+*
      Localization (Algebra.algebraMapSubmonoid Q N) :=
  IsLocalization.map _ Ψ.toRingHom (Algebra.algebraMapSubmonoid_le_comap N Ψ)

/-- The localized map extends the given one. -/
private theorem locMap_algebraMap (Ψ : P →ₐ[A] Q) (N : Submonoid A) (x : P) :
    locMap Ψ N (algebraMap P _ x) = algebraMap Q _ (Ψ x) :=
  IsLocalization.map_eq (S := Localization (Algebra.algebraMapSubmonoid P N)) _ _

/-- The localized map is compatible with the base. -/
private theorem locMap_algebraMap_base (Ψ : P →ₐ[A] Q) (N : Submonoid A) (r : A) :
    locMap Ψ N (algebraMap A _ r) = algebraMap A _ r := by
  rw [IsScalarTower.algebraMap_apply A P, locMap_algebraMap, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]

/-- A divisor of an element of `N` becomes a unit in the localization at `N`. -/
private theorem isUnit_algebraMap_of_dvd (X : Type u) [CommRing X] [Algebra A X] {N : Submonoid A}
    {m n : A} (hn : n ∈ N) (hmn : m ∣ n) :
    IsUnit (algebraMap A (Localization (Algebra.algebraMapSubmonoid X N)) m) := by
  have hu : IsUnit (algebraMap A (Localization (Algebra.algebraMapSubmonoid X N)) n) := by
    rw [IsScalarTower.algebraMap_apply A X]
    exact IsLocalization.map_units _ (⟨algebraMap A X n, n, hn, rfl⟩ :
      Algebra.algebraMapSubmonoid X N)
  exact isUnit_of_dvd_unit (map_dvd _ hmn) hu

/-- If the localization of `Ψ` at `M` is surjective, every element of the target is, after
multiplication by an element of `M`, in the image of `Ψ`. -/
private theorem forall_exists_smul_eq_of_surjective_locMap (Ψ : P →ₐ[A] Q) (M : Submonoid A)
    (h : Function.Surjective (locMap Ψ M)) (y : Q) : ∃ e ∈ M, ∃ a : P, e • y = Ψ a := by
  obtain ⟨z, hz⟩ := h (algebraMap Q _ y)
  obtain ⟨⟨a, ⟨_, s, hs, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid P M) z
  rw [IsLocalization.map_mk', eq_comm, IsLocalization.eq_mk'_iff_mul_eq, ← map_mul,
    IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid Q M)] at hz
  obtain ⟨⟨_, c, hc, rfl⟩, hc'⟩ := hz
  refine ⟨c * s, M.mul_mem hc hs, c • a, ?_⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] at hc'
  rw [map_smul, Algebra.smul_def, Algebra.smul_def, ← hc', map_mul]
  ring

/-- If `Ψ` is of finite type and every element of the target is, after multiplication by an
element of `M`, in its image, then a single element of `M` and its powers suffice. -/
private theorem exists_mem_forall_exists_pow_smul_eq (Ψ : P →ₐ[A] Q) (hΨ : Ψ.toRingHom.FiniteType)
    (M : Submonoid A) (h : ∀ y : Q, ∃ e ∈ M, ∃ a : P, e • y = Ψ a) :
    ∃ m ∈ M, ∀ y : Q, ∃ k : ℕ, ∃ a : P, m ^ k • y = Ψ a := by
  classical
  let : Algebra P Q := Ψ.toRingHom.toAlgebra
  obtain ⟨t, ht⟩ := hΨ.out
  choose! e he a ha using h
  refine ⟨∏ y ∈ t, e y, M.prod_mem fun y _ => he y, fun y => ?_⟩
  have hy : y ∈ Algebra.adjoin P (t : Set Q) := ht ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    refine ⟨1, (∏ w ∈ t.erase z, e w) • a z, ?_⟩
    rw [map_smul, ← ha z, pow_one, ← Finset.mul_prod_erase t e hz, smul_smul, mul_comm]
  | algebraMap r => exact ⟨0, r, by rw [pow_zero, one_smul]; rfl⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨k₁, a₁, e₁⟩ := h₁
    obtain ⟨k₂, a₂, e₂⟩ := h₂
    refine ⟨k₁ + k₂, (∏ y ∈ t, e y) ^ k₂ • a₁ + (∏ y ∈ t, e y) ^ k₁ • a₂, ?_⟩
    rw [map_add, map_smul, map_smul, ← e₁, ← e₂, smul_add, pow_add, smul_smul, smul_smul,
      mul_comm ((∏ y ∈ t, e y) ^ k₁)]
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨k₁, a₁, e₁⟩ := h₁
    obtain ⟨k₂, a₂, e₂⟩ := h₂
    refine ⟨k₁ + k₂, a₁ * a₂, ?_⟩
    rw [map_mul, ← e₁, ← e₂, pow_add, smul_mul_smul_comm]

/-- If every element of the target is in the image of `Ψ` after multiplication by an element of
`N`, the localization of `Ψ` at `N` is surjective. -/
private theorem surjective_locMap_of_forall' (Ψ : P →ₐ[A] Q) (N : Submonoid A)
    (h : ∀ y : Q, ∃ e ∈ N, ∃ a : P, e • y = Ψ a) : Function.Surjective (locMap Ψ N) := by
  intro z
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid Q N) z
  obtain ⟨s, s', hs', hss'⟩ := s
  subst hss'
  obtain ⟨e, he, a, hea⟩ := h y
  obtain ⟨w, hw⟩ := isUnit_algebraMap_of_dvd P (N.mul_mem he hs') (dvd_refl (e * s'))
  refine ⟨algebraMap P _ a * ↑w⁻¹, ?_⟩
  dsimp only
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have key : locMap Ψ N ↑w⁻¹ * algebraMap A (Localization (Algebra.algebraMapSubmonoid Q N))
      (e * s') = 1 := by
    rw [← locMap_algebraMap_base Ψ N, ← map_mul, ← hw, Units.inv_mul, map_one]
  have hy : algebraMap Q (Localization (Algebra.algebraMapSubmonoid Q N)) (Ψ a) =
      algebraMap A _ e * algebraMap Q _ y := by
    rw [← hea, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  rw [map_mul, locMap_algebraMap, hy, ← IsScalarTower.algebraMap_apply]
  rw [map_mul] at key
  linear_combination (algebraMap Q (Localization (Algebra.algebraMapSubmonoid Q N)) y) * key

/-- If every element of the target is in the image of `Ψ` after multiplication by a power of
`m`, then the localization of `Ψ` at any submonoid containing a multiple of `m` is surjective. -/
private theorem surjective_locMap_of_forall (Ψ : P →ₐ[A] Q) {m : A}
    (h : ∀ y : Q, ∃ k : ℕ, ∃ a : P, m ^ k • y = Ψ a) {N : Submonoid A} {n : A} (hn : n ∈ N)
    (hmn : m ∣ n) : Function.Surjective (locMap Ψ N) := by
  obtain ⟨c, rfl⟩ := hmn
  refine surjective_locMap_of_forall' Ψ N fun y => ?_
  obtain ⟨k, a, hka⟩ := h y
  refine ⟨(m * c) ^ k, N.pow_mem hn k, c ^ k • a, ?_⟩
  rw [map_smul, ← hka, smul_smul, mul_pow, mul_comm]

/-- If every element of the kernel of `Ψ` is killed by an element of `N`, the localization of `Ψ`
at `N` is injective. -/
private theorem injective_locMap_of_forall (Ψ : P →ₐ[A] Q) (N : Submonoid A)
    (h : ∀ a : P, Ψ a = 0 → ∃ e ∈ N, e • a = 0) : Function.Injective (locMap Ψ N) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid P N) z
  dsimp only at hz ⊢
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨⟨_, c, hc, rfl⟩, hca⟩ := hz
  have : Ψ (c • a) = 0 := by
    rw [map_smul, Algebra.smul_def]
    simpa using hca
  obtain ⟨e, he, hea⟩ := h _ this
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨algebraMap A P (e * c), e * c, N.mul_mem he hc, rfl⟩, ?_⟩
  rw [← Algebra.smul_def, mul_smul, hea]

/-- If the kernel of the localization of `Ψ` at `M` is finitely generated, then the kernel of `Ψ`
is, up to multiplication by elements of `M`, generated by finitely many of its elements. -/
private theorem exists_finset_forall_mem_ker (Ψ : P →ₐ[A] Q) (M : Submonoid A)
    (hK : (RingHom.ker (locMap Ψ M)).FG) :
    ∃ G : Finset P, (∀ g ∈ G, Ψ g = 0) ∧
      ∀ a : P, Ψ a = 0 → ∃ e ∈ M, e • a ∈ Ideal.span (G : Set P) := by
  classical
  obtain ⟨κ, hκ⟩ := hK
  -- write each generator as a fraction whose numerator lies in the kernel of `Ψ`
  have hgen : ∀ k ∈ κ, ∃ g : P, Ψ g = 0 ∧ ∃ e ∈ M,
      algebraMap P (Localization (Algebra.algebraMapSubmonoid P M)) g =
        algebraMap A _ e * k := by
    intro k hk
    have hk0 : locMap Ψ M k = 0 := by
      have : k ∈ RingHom.ker (locMap Ψ M) := hκ ▸ Ideal.subset_span hk
      exact this
    obtain ⟨⟨π, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid P M) k
    obtain ⟨s, hs, hst⟩ := t.2
    dsimp only at hk0 ⊢
    rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hk0
    obtain ⟨⟨_, c, hc, rfl⟩, hcπ⟩ := hk0
    refine ⟨c • π, ?_, c * s, M.mul_mem hc hs, ?_⟩
    · rw [map_smul, Algebra.smul_def]
      simpa using hcπ
    · rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, map_mul, mul_assoc,
        IsScalarTower.algebraMap_apply A P (Localization (Algebra.algebraMapSubmonoid P M)) s,
        hst, IsLocalization.mk'_spec'_mk]
  choose! g hg e he hge using hgen
  refine ⟨κ.image g, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact hg k hk
  · intro a ha
    have hmem : algebraMap P (Localization (Algebra.algebraMapSubmonoid P M)) a ∈
        Ideal.map (algebraMap P _) (Ideal.span ((κ.image g : Finset P) : Set P)) := by
      have : algebraMap P (Localization (Algebra.algebraMapSubmonoid P M)) a ∈
          RingHom.ker (locMap Ψ M) := by
        show locMap Ψ M _ = 0
        rw [locMap_algebraMap, ha, map_zero]
      rw [← hκ] at this
      refine (Ideal.span_le.2 ?_) this
      intro k hk
      obtain ⟨w, hw⟩ :=
        isUnit_algebraMap_of_dvd (N := M) P (he k hk) (dvd_refl (e k))
      have : k = ↑w⁻¹ * algebraMap P _ (g k) := by
        rw [hge k hk, ← mul_assoc, ← hw, Units.inv_mul, one_mul]
      rw [SetLike.mem_coe, this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem g hk))))
    obtain ⟨⟨x, ⟨_, s, hs, rfl⟩⟩, hx⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid P M) _).1 hmem
    dsimp only at hx
    rw [← map_mul, IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid P M)] at hx
    obtain ⟨⟨_, c, hc, rfl⟩, hcx⟩ := hx
    refine ⟨c * s, M.mul_mem hc hs, ?_⟩
    have : (c * s) • a = algebraMap A P c * (x : P) := by
      rw [Algebra.smul_def, map_mul, mul_assoc, mul_comm (algebraMap A P s)]
      exact hcx
    rw [this]
    exact Ideal.mul_mem_left _ _ x.2

/-- The localization at the image of the powers of `m` is the localization away from the image
of `m`. -/
private theorem isLocalization_away_algebraMapSubmonoid_powers (X : Type u) [CommRing X]
    [Algebra A X]
    (m : A) : IsLocalization.Away (algebraMap A X m)
      (Localization (Algebra.algebraMapSubmonoid X (Submonoid.powers m))) := by
  have h : Algebra.algebraMapSubmonoid X (Submonoid.powers m) =
      Submonoid.powers (algebraMap A X m) := Submonoid.map_powers _ _
  unfold IsLocalization.Away
  rw [← h]
  infer_instance

/-- The localization of a finitely presented algebra map away from an element is finitely
presented. -/
private theorem finitePresentation_locMap_powers (Ψ : P →ₐ[A] Q)
    (hΨ : Ψ.toRingHom.FinitePresentation)
    (m : A) : (locMap Ψ (Submonoid.powers m)).FinitePresentation := by
  have := isLocalization_away_algebraMapSubmonoid_powers P m
  have := isLocalization_away_algebraMapSubmonoid_powers Q m
  refine RingHom.FinitePresentation.of_comp_finiteType
    (algebraMap P (Localization (Algebra.algebraMapSubmonoid P (Submonoid.powers m)))) ?_ ?_
  · rw [IsLocalization.map_comp]
    refine RingHom.FinitePresentation.comp ?_ hΨ
    rw [RingHom.finitePresentation_algebraMap]
    exact IsLocalization.Away.finitePresentation (algebraMap A Q m)
  · have := IsLocalization.Away.finitePresentation (S := Localization
      (Algebra.algebraMapSubmonoid P (Submonoid.powers m))) (algebraMap A P m)
    exact RingHom.FiniteType.of_finitePresentation
      (RingHom.finitePresentation_algebraMap.2 this)

/-- **Spreading out bijectivity.** If a finitely presented map `Ψ` becomes bijective after
localization at `M`, in the elementwise sense, then it does so after inverting a single element of
`M`. -/
private theorem exists_mem_forall_pow_smul (Ψ : P →ₐ[A] Q) (hΨ : Ψ.toRingHom.FinitePresentation)
    (M : Submonoid A)
    (hs : ∀ y : Q, ∃ e ∈ M, ∃ a : P, e • y = Ψ a)
    (hi : ∀ a : P, Ψ a = 0 → ∃ e ∈ M, e • a = 0) :
    ∃ h ∈ M, (∀ y : Q, ∃ k : ℕ, ∃ a : P, h ^ k • y = Ψ a) ∧
      (∀ a : P, Ψ a = 0 → ∃ k : ℕ, h ^ k • a = 0) := by
  classical
  obtain ⟨m, hm, hmsurj⟩ := exists_mem_forall_exists_pow_smul_eq Ψ
    (RingHom.FiniteType.of_finitePresentation hΨ)
    M hs
  have hsurj : Function.Surjective (locMap Ψ (Submonoid.powers m)) :=
    surjective_locMap_of_forall Ψ hmsurj (Submonoid.mem_powers m) dvd_rfl
  have hK : (RingHom.ker (locMap Ψ (Submonoid.powers m))).FG := by
    let := (locMap Ψ (Submonoid.powers m)).toAlgebra
    have : Algebra.FinitePresentation _ _ := finitePresentation_locMap_powers Ψ hΨ m
    exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId _ _) hsurj
  obtain ⟨G, hG, hGspan⟩ := exists_finset_forall_mem_ker Ψ _ hK
  choose! e he hea using fun g (hg : g ∈ G) => hi g (hG g hg)
  refine ⟨m * ∏ g ∈ G, e g, M.mul_mem hm (M.prod_mem fun g hg => he g hg), ?_, ?_⟩
  · intro y
    obtain ⟨k, a, hka⟩ := hmsurj y
    refine ⟨k, (∏ g ∈ G, e g) ^ k • a, ?_⟩
    rw [map_smul, ← hka, smul_smul, mul_pow, mul_comm]
  · intro a ha
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hGspan a ha
    -- `∏ e` kills the ideal spanned by `G`
    have hkill : ∀ x ∈ Ideal.span (G : Set P), (∏ g ∈ G, e g) • x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        rw [← Finset.mul_prod_erase G e hx, mul_comm, mul_smul, hea x hx, smul_zero]
      | zero => rw [smul_zero]
      | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
      | smul r x _ hx => rw [smul_comm, hx, smul_zero]
    refine ⟨k + 1, ?_⟩
    have : (m * ∏ g ∈ G, e g) ^ (k + 1) • a =
        (m * (∏ g ∈ G, e g) ^ k) • ((∏ g ∈ G, e g) • (m ^ k • a)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [this, hkill _ hk, smul_zero]

section Tensor

variable {D E : Type u} [CommRing D] [CommRing E] [Algebra A D] [Algebra A E]
  (C : Type u) [CommRing C] [Algebra A C]

/-- Base change along `C` preserves the elementwise surjectivity condition. -/
private theorem forall_exists_smul_eq_map_of_forall (ψ : D →ₐ[A] E) (N : Submonoid A)
    (h : ∀ y : E, ∃ e ∈ N, ∃ a : D, e • y = ψ a) (y : C ⊗[A] E) :
    ∃ e ∈ N, ∃ a : C ⊗[A] D, e • y = Algebra.TensorProduct.map (AlgHom.id A C) ψ a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, N.one_mem, 0, by simp⟩
  | tmul c x =>
    obtain ⟨e, he, a, hea⟩ := h x
    exact ⟨e, he, c ⊗ₜ a, by rw [← TensorProduct.tmul_smul, hea]; rfl⟩
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨e₁, he₁, a₁, ha₁⟩ := h₁
    obtain ⟨e₂, he₂, a₂, ha₂⟩ := h₂
    refine ⟨e₁ * e₂, N.mul_mem he₁ he₂, e₂ • a₁ + e₁ • a₂, ?_⟩
    rw [map_add, map_smul, map_smul, ← ha₁, ← ha₂, smul_add, smul_smul, smul_smul,
      mul_comm e₂]

/-- Base change along a flat `C` preserves the elementwise injectivity condition: the kernel of
`C ⊗ ψ` is `C ⊗ ker ψ`, whose elements are killed by elements of `N`. -/
private theorem forall_exists_smul_eq_zero_map_of_forall [Module.Flat A C] (ψ : D →ₐ[A] E)
    (N : Submonoid A) (h : ∀ a : D, ψ a = 0 → ∃ e ∈ N, e • a = 0) (a : C ⊗[A] D)
    (ha : Algebra.TensorProduct.map (AlgHom.id A C) ψ a = 0) : ∃ e ∈ N, e • a = 0 := by
  have hex : Function.Exact (LinearMap.ker ψ.toLinearMap).subtype ψ.toLinearMap :=
    LinearMap.exact_subtype_ker_map _
  have hex' := Module.Flat.lTensor_exact C hex
  have : a ∈ LinearMap.ker (LinearMap.lTensor C ψ.toLinearMap) := ha
  rw [hex'.linearMap_ker_eq] at this
  obtain ⟨a', rfl⟩ := this
  suffices H : ∀ x : C ⊗[A] (LinearMap.ker ψ.toLinearMap), ∃ e ∈ N, e • x = 0 by
    obtain ⟨e, he, hx⟩ := H a'
    exact ⟨e, he, by rw [← LinearMap.map_smul, hx, map_zero]⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, N.one_mem, smul_zero _⟩
  | tmul c k =>
    obtain ⟨e, he, hk⟩ := h k k.2
    refine ⟨e, he, ?_⟩
    have : e • k = 0 := Subtype.ext hk
    rw [← TensorProduct.tmul_smul, this, TensorProduct.tmul_zero]
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨e₁, he₁, h₁⟩ := h₁
    obtain ⟨e₂, he₂, h₂⟩ := h₂
    refine ⟨e₁ * e₂, N.mul_mem he₁ he₂, ?_⟩
    rw [smul_add, mul_smul, mul_smul, h₂, smul_zero, smul_comm, h₁, smul_zero, add_zero]

end Tensor

/-- The localized map is linear over the localized base. -/
private theorem locMap_comp_algebraMap_loc (Ψ : P →ₐ[A] Q) (N : Submonoid A) :
    (locMap Ψ N).comp (algebraMap (Localization N) _) = algebraMap (Localization N) _ := by
  apply IsLocalization.ringHom_ext N
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    locMap_algebraMap_base]

/-- The localized map is surjective as soon as its image contains generators of the target. -/
private theorem surjective_locMap_of_adjoin_eq_top (Ψ : P →ₐ[A] Q) (N : Submonoid A)
    (t : Set (Localization (Algebra.algebraMapSubmonoid Q N)))
    (ht : Algebra.adjoin (Localization N) t = ⊤) (htr : t ⊆ Set.range (locMap Ψ N)) :
    Function.Surjective (locMap Ψ N) := by
  let R : Subalgebra (Localization N) (Localization (Algebra.algebraMapSubmonoid Q N)) :=
    { (locMap Ψ N).range with
      algebraMap_mem' := fun r => ⟨algebraMap _ _ r,
        congrArg (fun f => f r) (locMap_comp_algebraMap_loc Ψ N)⟩ }
  have hle : Algebra.adjoin (Localization N) t ≤ R := Algebra.adjoin_le htr
  intro z
  exact hle (ht ▸ Algebra.mem_top : z ∈ Algebra.adjoin (Localization N) t)

section Model

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

/-- The localization of a finitely presented algebra at a submonoid of the base is finitely
presented over the localized base. -/
private theorem finitePresentation_localization_algebraMapSubmonoid (X : Type u) [CommRing X]
    [Algebra B X]
    [Algebra.FinitePresentation B X] (S : Submonoid B) :
    Algebra.FinitePresentation (Localization S)
      (Localization (Algebra.algebraMapSubmonoid X S)) := by
  have : Algebra.IsPushout B (Localization S) X (Localization (Algebra.algebraMapSubmonoid X S)) :=
    (Algebra.isPushout_of_isLocalization S (Localization S) X _).symm
  exact Algebra.FinitePresentation.equiv
    (Algebra.IsPushout.equiv B (Localization S) X (Localization (Algebra.algebraMapSubmonoid X S)))

/-- The localization of an algebra map at a submonoid `S` of the base, as an algebra map over the
localization of the base: Mathlib's `IsLocalization.mapₐ` at the canonical localizations. -/
private noncomputable abbrev locAlgHom {P Q : Type u} [CommRing P] [CommRing Q] [Algebra B P]
    [Algebra B Q] (Ψ : P →ₐ[B] Q) (S : Submonoid B) :
    Localization (Algebra.algebraMapSubmonoid P S) →ₐ[Localization S]
      Localization (Algebra.algebraMapSubmonoid Q S) :=
  IsLocalization.mapₐ S (Localization S) _ _ Ψ

/-- A finitely presented model of an algebra whose localization at a submonoid is finitely
presented: a finitely presented algebra with a map to it which becomes bijective after
localization, in the elementwise form. -/
private theorem exists_finitePresentation_model (S : Submonoid B)
    [Algebra.FinitePresentation (Localization S) (Localization (Algebra.algebraMapSubmonoid C S))] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.FinitePresentation B D)
      (φ₀ : D →ₐ[B] C), (∀ y : C, ∃ e ∈ S, ∃ a, e • y = φ₀ a) ∧
        (∀ a, φ₀ a = 0 → ∃ e ∈ S, e • a = 0) := by
  classical
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := Localization S)
    (A := Localization (Algebra.algebraMapSubmonoid C S))
  have hz : ∀ z : t, ∃ (x : C) (b : B) (hb : b ∈ S),
      IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid C S)) x
        (⟨algebraMap B C b, b, hb, rfl⟩ : Algebra.algebraMapSubmonoid C S) = z.1 := by
    intro z
    obtain ⟨⟨x, ⟨_, b, hb, rfl⟩⟩, h⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid C S) z.1
    exact ⟨x, b, hb, h⟩
  choose c b hb hcb using hz
  let Φ : MvPolynomial t B →ₐ[B] C := MvPolynomial.aeval c
  have hsurj : Function.Surjective (locMap Φ S) := by
    refine surjective_locMap_of_adjoin_eq_top Φ S t ht ?_
    intro z hz
    refine ⟨IsLocalization.mk' _ (MvPolynomial.X ⟨z, hz⟩)
      (⟨algebraMap B _ (b ⟨z, hz⟩), b ⟨z, hz⟩, hb ⟨z, hz⟩, rfl⟩ :
        Algebra.algebraMapSubmonoid (MvPolynomial t B) S), ?_⟩
    rw [IsLocalization.map_mk']
    refine Eq.trans ?_ (hcb ⟨z, hz⟩)
    congr 1
    · simp [Φ]
    · ext
      simp [Φ]
  have : Algebra.FinitePresentation (Localization S)
      (Localization (Algebra.algebraMapSubmonoid (MvPolynomial t B) S)) :=
    finitePresentation_localization_algebraMapSubmonoid _ S
  have hK : (RingHom.ker (locMap Φ S)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (locAlgHom Φ S) hsurj
  obtain ⟨G, hG, hGspan⟩ := exists_finset_forall_mem_ker Φ S hK
  let I : Ideal (MvPolynomial t B) := Ideal.span (G : Set (MvPolynomial t B))
  have hI : I ≤ RingHom.ker Φ := Ideal.span_le.2 fun g hg => hG g hg
  refine ⟨MvPolynomial t B ⧸ I, inferInstance, inferInstance,
    Algebra.FinitePresentation.quotient ⟨G, rfl⟩, Ideal.Quotient.liftₐ I Φ hI, ?_, ?_⟩
  · intro y
    obtain ⟨e, he, a, hea⟩ := forall_exists_smul_eq_of_surjective_locMap Φ S hsurj y
    exact ⟨e, he, Ideal.Quotient.mk I a, by rw [hea]; rfl⟩
  · intro d hd
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨e, he, hea⟩ := hGspan a hd
    refine ⟨e, he, ?_⟩
    rw [← Ideal.Quotient.mkₐ_eq_mk B, ← map_smul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hea

/-- An algebra whose localization at a prime `p` of the base is étale is étale at every prime
lying over a generalization of `p`. -/
private theorem isEtaleAt_of_etale_localization {D : Type u} [CommRing D] [Algebra B D]
    (p : Ideal B) [p.IsPrime]
    [Algebra.Etale (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid D p.primeCompl))]
    (Q : Ideal D) [Q.IsPrime] (hQ : Q.comap (algebraMap B D) ≤ p) : Algebra.IsEtaleAt B Q := by
  let Dp := Localization (Algebra.algebraMapSubmonoid D p.primeCompl)
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid D p.primeCompl : Set D) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxQ
    exact hx (hQ hxQ)
  let Q' : Ideal Dp := Q.map (algebraMap D Dp)
  have hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ Q ‹_› hdisj
  have hQ'c : Q'.comap (algebraMap D Dp) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint _ Dp ‹_› hdisj
  have h₁ : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime Q') := by
    have : (⟨Q', hQ'⟩ : PrimeSpectrum Dp) ∈ Algebra.etaleLocus (Localization.AtPrime p) Dp := by
      rw [(Algebra.etaleLocus_eq_univ_iff).2 inferInstance]
      trivial
    exact this
  have h₂ : Algebra.FormallyEtale B (Localization.AtPrime Q') :=
    Algebra.FormallyEtale.comp B (Localization.AtPrime p) _
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Algebra.algebraMapSubmonoid D p.primeCompl) Q'
  have h₃ : Algebra.FormallyEtale B (Localization.AtPrime (Q'.comap (algebraMap D Dp))) :=
    Algebra.FormallyEtale.of_equiv (e.symm.restrictScalars B)
  have key : ∀ (Q₁ Q₂ : Ideal D) [Q₁.IsPrime] [Q₂.IsPrime], Q₁ = Q₂ →
      Algebra.IsEtaleAt B Q₁ → Algebra.IsEtaleAt B Q₂ := by
    intro Q₁ Q₂ _ _ h h'
    subst h
    exact h'
  exact key _ _ hQ'c h₃

/-- If a finitely presented algebra is étale at every prime missing the image of a submonoid `S`
of the base, then it is étale over a basic open set defined by an element of `S`. -/
private theorem exists_mem_basicOpen_subset_etaleLocus {D : Type u} [CommRing D] [Algebra B D]
    [Algebra.FinitePresentation B D] (S : Submonoid B)
    (h : ∀ (Q : Ideal D) [Q.IsPrime],
      Disjoint (Algebra.algebraMapSubmonoid D S : Set D) Q → Algebra.IsEtaleAt B Q) :
    ∃ e ∈ S, (PrimeSpectrum.basicOpen (algebraMap B D e) : Set (PrimeSpectrum D)) ⊆
      Algebra.etaleLocus B D := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1
    (Algebra.isOpen_etaleLocus (R := B) (A := D)).isClosed_compl
  by_cases hdisj : Disjoint (I : Set D) (Algebra.algebraMapSubmonoid D S)
  · exfalso
    obtain ⟨Q, hQ, hIQ, hQS⟩ := Ideal.exists_le_prime_disjoint I _ hdisj
    have hmem : (⟨Q, hQ⟩ : PrimeSpectrum D) ∈ (Algebra.etaleLocus B D)ᶜ := by
      rw [hI]
      exact hIQ
    exact hmem (h Q hQS.symm)
  · rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨_, hxI, ⟨e, he, rfl⟩⟩ := hdisj
    refine ⟨e, he, fun x hx => ?_⟩
    by_contra hx'
    have : x ∈ PrimeSpectrum.zeroLocus (I : Set D) := hI ▸ hx'
    exact hx (this hxI)

/-- The image of the étale part of a finitely presented algebra contains a basic open
neighbourhood of every prime it contains. -/
private theorem exists_notMem_forall_exists_comap_eq {D : Type u} [CommRing D] [Algebra B D]
    [Algebra.FinitePresentation B D] (s₁ : B)
    (hs₁ : (PrimeSpectrum.basicOpen (algebraMap B D s₁) : Set (PrimeSpectrum D)) ⊆
      Algebra.etaleLocus B D)
    (Q₀ : PrimeSpectrum D) (hQ₀ : algebraMap B D s₁ ∉ Q₀.asIdeal) :
    ∃ s₂ : B, s₂ ∉ (PrimeSpectrum.comap (algebraMap B D) Q₀).asIdeal ∧
      ∀ q : PrimeSpectrum B, s₂ ∉ q.asIdeal → ∃ Q : PrimeSpectrum D,
        algebraMap B D s₁ ∉ Q.asIdeal ∧ PrimeSpectrum.comap (algebraMap B D) Q = q := by
  let D₁ := Localization.Away (algebraMap B D s₁)
  have : Algebra.Etale B D₁ := (Algebra.basicOpen_subset_etaleLocus_iff_etale).1 hs₁
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap B D₁))) := by
    rw [← Set.image_univ]
    exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ isOpen_univ
  have hrange := PrimeSpectrum.localization_away_comap_range D₁ (algebraMap B D s₁)
  have hcomp : PrimeSpectrum.comap (algebraMap B D₁) =
      PrimeSpectrum.comap (algebraMap B D) ∘ PrimeSpectrum.comap (algebraMap D D₁) := by
    ext1 x
    rw [IsScalarTower.algebraMap_eq B D D₁, PrimeSpectrum.comap_comp]
  have hmem : PrimeSpectrum.comap (algebraMap B D) Q₀ ∈
      Set.range (PrimeSpectrum.comap (algebraMap B D₁)) := by
    have : Q₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap D D₁)) := by
      rw [hrange]
      exact hQ₀
    obtain ⟨Q₁, hQ₁⟩ := this
    exact ⟨Q₁, by rw [hcomp, Function.comp_apply, hQ₁]⟩
  obtain ⟨_, ⟨s₂, rfl⟩, hs₂, hs₂U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem hopen
  refine ⟨s₂, hs₂, fun q hq => ?_⟩
  obtain ⟨Q₁, hQ₁⟩ := hs₂U hq
  refine ⟨PrimeSpectrum.comap (algebraMap D D₁) Q₁, ?_, ?_⟩
  · have : PrimeSpectrum.comap (algebraMap D D₁) Q₁ ∈
        Set.range (PrimeSpectrum.comap (algebraMap D D₁)) := ⟨Q₁, rfl⟩
    rw [hrange] at this
    exact this
  · rw [← hQ₁, hcomp]
    rfl

section TensorLocalization

variable (M X : Type u) [CommRing M] [CommRing X] [Algebra B M] [Algebra B X] (g : B)

/-- The map `M ⊗ X → M ⊗ X_g`. -/
private noncomputable abbrev tensorLocMap :
    M ⊗[B] X →ₐ[B] M ⊗[B] Localization (Algebra.algebraMapSubmonoid X (Submonoid.powers g)) :=
  Algebra.TensorProduct.map (AlgHom.id B M) (IsScalarTower.toAlgHom B X _)

/-- Every element of `M ⊗ X_g` is the image of an element of `M ⊗ X` after multiplication by a
power of `g`. -/
private theorem exists_pow_smul_eq_tensorLocMap
    (y : M ⊗[B] Localization (Algebra.algebraMapSubmonoid X (Submonoid.powers g))) :
    ∃ n : ℕ, ∃ x : M ⊗[B] X, g ^ n • y = tensorLocMap M X g x := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul m z =>
    obtain ⟨⟨a, t⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid X (Submonoid.powers g)) z
    obtain ⟨_, ⟨n, rfl⟩, hst⟩ := t.2
    refine ⟨n, m ⊗ₜ a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    simp only [tensorLocMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      IsScalarTower.coe_toAlgHom']
    congr 1
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply B X]
    simp only at hst
    rw [hst, IsLocalization.mk'_spec']
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨n₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, g ^ n₂ • x₁ + g ^ n₁ • x₂, ?_⟩
    rw [map_add, map_smul, map_smul, ← e₁, ← e₂, smul_add, smul_smul, smul_smul, pow_add,
      mul_comm (g ^ n₁)]

/-- For flat `M`, an element of the kernel of `M ⊗ X → M ⊗ X_g` is killed by a power of `g`. -/
private theorem exists_pow_smul_eq_zero_of_tensorLocMap_eq_zero [Module.Flat B M] (x : M ⊗[B] X)
    (hx : tensorLocMap M X g x = 0) : ∃ n : ℕ, g ^ n • x = 0 := by
  obtain ⟨e, ⟨n, rfl⟩, h⟩ := forall_exists_smul_eq_zero_map_of_forall M
    (IsScalarTower.toAlgHom B X (Localization (Algebra.algebraMapSubmonoid X (Submonoid.powers g))))
    (Submonoid.powers g) (fun a ha => by
      have : algebraMap X (Localization (Algebra.algebraMapSubmonoid X (Submonoid.powers g))) a =
          0 := ha
      rw [← map_zero (algebraMap X (Localization (Algebra.algebraMapSubmonoid X
        (Submonoid.powers g)))), IsLocalization.eq_iff_exists
        (Algebra.algebraMapSubmonoid X (Submonoid.powers g))] at this
      obtain ⟨⟨_, s, hs, rfl⟩, hc⟩ := this
      exact ⟨s, hs, by rw [Algebra.smul_def]; simpa using hc⟩) x hx
  exact ⟨n, h⟩

end TensorLocalization

/-- A divisor of `g` is a unit in `M ⊗ X_g`. -/
private theorem isUnit_algebraMap_tensor_localization (M X : Type u) [CommRing M] [CommRing X]
    [Algebra B M] [Algebra B X] {g r : B} (hr : r ∣ g) :
    IsUnit (algebraMap B (M ⊗[B] Localization (Algebra.algebraMapSubmonoid X
      (Submonoid.powers g))) r) := by
  have h := isUnit_algebraMap_of_dvd (N := Submonoid.powers g) X (Submonoid.mem_powers g) hr
  have : algebraMap B (M ⊗[B] Localization (Algebra.algebraMapSubmonoid X
      (Submonoid.powers g))) r = Algebra.TensorProduct.includeRight (algebraMap B _ r) := by
    rw [AlgHom.commutes]
  rw [this]
  exact h.map _

/-- The localization of a flat algebra at a prime `p` of the base lying under a prime of the
algebra is surjective on spectra over `B_p`: generalizations lift along flat maps. -/
private theorem surjective_comap_localization_atPrime [Module.Flat B C] (p : Ideal B) [p.IsPrime]
    (Q : Ideal C) [Q.IsPrime] (hQ : Q.comap (algebraMap B C) = p) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid C p.primeCompl)))) := by
  intro P
  set q : Ideal B := P.asIdeal.comap (algebraMap B (Localization.AtPrime p)) with hq
  have hqp : q ≤ p := by
    intro x hx
    by_contra hxp
    have hu : IsUnit (algebraMap B (Localization.AtPrime p) x) :=
      IsLocalization.map_units _ (⟨x, hxp⟩ : p.primeCompl)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver p := ⟨hQ.symm⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'q⟩ := Ideal.exists_ideal_le_liesOver_of_le (S := C) Q hqp
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C p.primeCompl : Set C) Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    have : s ∈ Q.comap (algebraMap B C) := hQ'Q hsQ
    rw [hQ] at this
    exact hs this
  let P' : PrimeSpectrum (Localization (Algebra.algebraMapSubmonoid C p.primeCompl)) :=
    ⟨Q'.map (algebraMap C _), IsLocalization.isPrime_of_isPrime_disjoint _ _ Q' hQ'prime hdisj⟩
  refine ⟨P', ?_⟩
  ext1
  apply (IsLocalization.orderEmbedding p.primeCompl (Localization.AtPrime p)).injective
  show Ideal.comap _ (Ideal.comap _ _) = Ideal.comap _ _
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq B C (Localization (Algebra.algebraMapSubmonoid C p.primeCompl)),
    ← Ideal.comap_comap]
  have := IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid C p.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid C p.primeCompl)) hQ'prime hdisj
  show Ideal.comap _ (Ideal.comap _ (Q'.map _)) = q
  rw [show Ideal.comap _ (Q'.map _) = Q' from this]
  exact (hQ'q.over).symm

/-- Let `B → C` be flat with `C → C ⊗_B C` étale, and let `p` be a prime of `B` lying under a
prime of `C`. Then the localization `C_p` of `C` at `p` is étale over `B_p`: it is faithfully flat
over `B_p`, and `C_p ⊗_{B_p} C_p` is the base change of `C ⊗_B C` along `C → C_p`, hence étale over
`C_p`; étaleness descends along faithfully flat maps. -/
theorem etale_localization_of_etale_tensorProduct [Module.Flat B C] [Algebra.Etale C (C ⊗[B] C)]
    (p : Ideal B) [p.IsPrime] (Q : Ideal C) [Q.IsPrime] (hQ : Q.comap (algebraMap B C) = p) :
    Algebra.Etale (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid C p.primeCompl)) := by
  let Bp := Localization.AtPrime p
  let Cp := Localization (Algebra.algebraMapSubmonoid C p.primeCompl)
  have : Algebra.IsPushout B Bp C Cp :=
    (Algebra.isPushout_of_isLocalization p.primeCompl Bp C Cp).symm
  let e₀ : Bp ⊗[B] C ≃ₐ[Bp] Cp := Algebra.IsPushout.equiv B Bp C Cp
  let e₁ : Cp ⊗[Bp] (Bp ⊗[B] C) ≃ₐ[Cp] Cp ⊗[B] C :=
    Algebra.TensorProduct.cancelBaseChange B Bp Cp Cp C
  let e₂ : Cp ⊗[C] (C ⊗[B] C) ≃ₐ[Cp] Cp ⊗[B] C :=
    Algebra.TensorProduct.cancelBaseChange B C Cp Cp C
  let e₃ : Cp ⊗[Bp] (Bp ⊗[B] C) ≃ₐ[Cp] Cp ⊗[Bp] Cp :=
    Algebra.TensorProduct.congr AlgEquiv.refl e₀
  have : Algebra.Etale Cp (Cp ⊗[Bp] Cp) := Algebra.Etale.of_equiv ((e₂.trans e₁.symm).trans e₃)
  have : Module.Flat Bp Cp := (Module.flat_iff_of_isLocalization Bp p.primeCompl Cp).2 inferInstance
  have : Module.FaithfullyFlat Bp Cp :=
    Module.FaithfullyFlat.of_comap_surjective (surjective_comap_localization_atPrime p Q hQ)
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Cp

/-- An element killed by a scalar which is a unit vanishes. -/
private theorem eq_zero_of_isUnit_smul_eq_zero {R X : Type u} [CommRing R] [CommRing X]
    [Algebra R X]
    {r : R} (hr : IsUnit (algebraMap R X r)) {x : X} (h : r • x = 0) : x = 0 := by
  rw [Algebra.smul_def] at h
  exact (hr.mul_right_eq_zero).1 h

/-- **An étale model of a flat algebra with étale self-tensor product.** Let `B → C` be flat with
`C → C ⊗_B C` étale, and let `p` be a prime of `B` lying under a prime of `C`. Then there are
`g ∉ p` and a `B`-algebra `D` such that `D_g` is étale over `B_g` with surjective spectrum map,
together with a `B_g`-algebra map `ψ : D_g → C_g` for which `C ⊗_B D_g → C ⊗_B C_g` is
bijective. -/
theorem exists_etale_bijective_map [Module.Flat B C] [Algebra.Etale C (C ⊗[B] C)]
    (p : Ideal B) [p.IsPrime] (Q : Ideal C) [Q.IsPrime] (hQ : Q.comap (algebraMap B C) = p) :
    ∃ g ∉ p, ∃ (D : Type u) (_ : CommRing D) (_ : Algebra B D),
      Algebra.Etale (Localization.Away g)
        (Localization (Algebra.algebraMapSubmonoid D (Submonoid.powers g))) ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap (Localization.Away g)
        (Localization (Algebra.algebraMapSubmonoid D (Submonoid.powers g))))) ∧
      ∃ ψ : Localization (Algebra.algebraMapSubmonoid D (Submonoid.powers g))
          →ₐ[Localization.Away g] Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers g)),
        Function.Bijective (Algebra.TensorProduct.map (AlgHom.id B C) (ψ.restrictScalars B)) := by
  classical
  let S := p.primeCompl
  have hEt : Algebra.Etale (Localization S) (Localization (Algebra.algebraMapSubmonoid C S)) :=
    etale_localization_of_etale_tensorProduct p Q hQ
  obtain ⟨D, _, _, _, φ₀, hφs, hφi⟩ := exists_finitePresentation_model (C := C) S
  have hbij : Function.Bijective (locAlgHom φ₀ S) :=
    ⟨injective_locMap_of_forall φ₀ S hφi, surjective_locMap_of_forall' φ₀ S hφs⟩
  have hEtD : Algebra.Etale (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid D S)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective _ hbij).symm
  obtain ⟨e₁, he₁, hloc⟩ := exists_mem_basicOpen_subset_etaleLocus (D := D) S (by
    intro Q' _ hdisj
    refine isEtaleAt_of_etale_localization p Q' fun x hx => ?_
    by_contra hxp
    exact Set.disjoint_left.1 hdisj ⟨x, hxp, rfl⟩ hx)
  -- a prime of `D` over `p`
  let Q₀ : PrimeSpectrum D := ⟨Q.comap φ₀.toRingHom, Ideal.comap_isPrime _ _⟩
  have hQ₀ : PrimeSpectrum.comap (algebraMap B D) Q₀ = ⟨p, inferInstance⟩ := by
    ext1
    show Ideal.comap _ (Ideal.comap _ Q) = p
    rw [Ideal.comap_comap, ← hQ]
    congr 1
    ext x
    simp
  have he₁Q₀ : algebraMap B D e₁ ∉ Q₀.asIdeal := by
    intro h
    have : e₁ ∈ (PrimeSpectrum.comap (algebraMap B D) Q₀).asIdeal := h
    rw [hQ₀] at this
    exact he₁ this
  obtain ⟨s₂, hs₂, hlift⟩ := exists_notMem_forall_exists_comap_eq e₁ hloc Q₀ he₁Q₀
  rw [hQ₀] at hs₂
  -- spreading the bijectivity of `C ⊗ φ₀`
  let Ψ : C ⊗[B] D →ₐ[C] C ⊗[B] C := Algebra.TensorProduct.map (AlgHom.id C C) φ₀
  have hΨfp : Ψ.toRingHom.FinitePresentation := by
    refine RingHom.FinitePresentation.of_comp_finiteType (algebraMap C (C ⊗[B] D)) ?_ ?_
    · have : Ψ.toRingHom.comp (algebraMap C (C ⊗[B] D)) = algebraMap C (C ⊗[B] C) :=
        Ψ.comp_algebraMap
      rw [this, RingHom.finitePresentation_algebraMap]
      infer_instance
    · rw [RingHom.finiteType_algebraMap]
      infer_instance
  have hs : ∀ y : C ⊗[B] C, ∃ e ∈ Algebra.algebraMapSubmonoid C S, ∃ a, e • y = Ψ a := by
    intro y
    obtain ⟨e, he, a, hea⟩ := forall_exists_smul_eq_map_of_forall C φ₀ S hφs y
    exact ⟨algebraMap B C e, ⟨e, he, rfl⟩, a, by rw [algebraMap_smul]; exact hea⟩
  have hi : ∀ a, Ψ a = 0 → ∃ e ∈ Algebra.algebraMapSubmonoid C S, e • a = 0 := by
    intro a ha
    obtain ⟨e, he, hea⟩ := forall_exists_smul_eq_zero_map_of_forall C φ₀ S hφi a ha
    exact ⟨algebraMap B C e, ⟨e, he, rfl⟩, by rw [algebraMap_smul]; exact hea⟩
  obtain ⟨_, ⟨m₀, hm₀, rfl⟩, hmsurj, hminj⟩ := exists_mem_forall_pow_smul Ψ hΨfp _ hs hi
  -- the element `g`
  set g := e₁ * s₂ * m₀ with hg
  have hgp : g ∉ p := S.mul_mem (S.mul_mem he₁ hs₂) hm₀
  let C' := Localization (Algebra.algebraMapSubmonoid D (Submonoid.powers g))
  refine ⟨g, hgp, D, inferInstance, inferInstance, ?_, ?_, locAlgHom φ₀ _, ?_⟩
  · -- étaleness
    have hsub : (PrimeSpectrum.basicOpen (algebraMap B D g) : Set (PrimeSpectrum D)) ⊆
        Algebra.etaleLocus B D := by
      refine subset_trans ?_ hloc
      intro x hx hx'
      apply hx
      rw [hg, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hx')
    have h₁ : Algebra.Etale B (Localization.Away (algebraMap B D g)) :=
      (Algebra.basicOpen_subset_etaleLocus_iff_etale).1 hsub
    have := isLocalization_away_algebraMapSubmonoid_powers D g
    have : Algebra.Etale B C' :=
      Algebra.Etale.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap B D g))
        (Localization.Away (algebraMap B D g)) C').restrictScalars B)
    exact Algebra.Etale.of_restrictScalars B _ _
  · -- surjectivity on spectra
    intro P
    set q := PrimeSpectrum.comap (algebraMap B (Localization.Away g)) P with hq
    have hgq : g ∉ q.asIdeal := fun h =>
      P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.map_units (Localization.Away g) (⟨g, Submonoid.mem_powers g⟩ :
          Submonoid.powers g)))
    have hs₂q : s₂ ∉ q.asIdeal := fun h => hgq (by
      rw [hg, mul_comm e₁, mul_assoc]
      exact Ideal.mul_mem_right _ _ h)
    obtain ⟨Q₁, -, hQ₁⟩ := hlift q hs₂q
    have hdisj : Disjoint (Algebra.algebraMapSubmonoid D (Submonoid.powers g) : Set D)
        Q₁.asIdeal := by
      rw [Set.disjoint_left]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩ hk
      have : g ^ k ∈ (PrimeSpectrum.comap (algebraMap B D) Q₁).asIdeal := hk
      rw [hQ₁] at this
      exact hgq (q.isPrime.mem_of_pow_mem k this)
    let Q₂ : PrimeSpectrum C' := ⟨Q₁.asIdeal.map (algebraMap D C'),
      IsLocalization.isPrime_of_isPrime_disjoint _ _ _ Q₁.isPrime hdisj⟩
    refine ⟨Q₂, PrimeSpectrum.localization_comap_injective (Localization.Away g)
      (Submonoid.powers g) ?_⟩
    rw [← hq, ← hQ₁, ← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq B D C', PrimeSpectrum.comap_comp_apply]
    congr 1
    ext1
    exact IsLocalization.under_map_of_isPrime_disjoint _ C' Q₁.isPrime hdisj
  · -- bijectivity
    let Θ := Algebra.TensorProduct.map (AlgHom.id B C)
      ((locAlgHom φ₀ (Submonoid.powers g)).restrictScalars B)
    let Ψ₀ : C ⊗[B] D →ₐ[B] C ⊗[B] C := Algebra.TensorProduct.map (AlgHom.id B C) φ₀
    have hcomm : ∀ x, Θ (tensorLocMap C D g x) = tensorLocMap C C g (Ψ₀ x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        simp only [Θ, Ψ₀, tensorLocMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          IsScalarTower.coe_toAlgHom', AlgHom.coe_restrictScalars']
        congr 1
        exact locMap_algebraMap φ₀ _ d
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    have hunit : ∀ (X : Type u) [CommRing X] [Algebra B X] (k : ℕ) {r : B}, r ∣ g →
        IsUnit (algebraMap B (C ⊗[B] Localization (Algebra.algebraMapSubmonoid X
          (Submonoid.powers g))) (r ^ k)) := fun X _ _ k r hr => by
      rw [map_pow]
      exact (isUnit_algebraMap_tensor_localization C X hr).pow k
    have hm₀g : m₀ ∣ g := ⟨e₁ * s₂, by rw [hg]; ring⟩
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨n, x₀, hx₀⟩ := exists_pow_smul_eq_tensorLocMap C D g x
      have h1 : tensorLocMap C C g (Ψ₀ x₀) = 0 := by
        rw [← hcomm, ← hx₀, map_smul, hx, smul_zero]
      obtain ⟨n₁, hn₁⟩ := exists_pow_smul_eq_zero_of_tensorLocMap_eq_zero C C g _ h1
      have h2 : Ψ (g ^ n₁ • x₀) = 0 := by
        show Ψ₀ (g ^ n₁ • x₀) = 0
        rw [map_smul, hn₁]
      obtain ⟨k, hk⟩ := hminj _ h2
      rw [← map_pow, algebraMap_smul, smul_smul] at hk
      have h3 : (m₀ ^ k * g ^ n₁ * g ^ n) • x = 0 := by
        rw [mul_smul, hx₀, ← map_smul, hk, map_zero]
      refine eq_zero_of_isUnit_smul_eq_zero ?_ h3
      rw [map_mul, map_mul]
      exact ((hunit D k hm₀g).mul (hunit D n₁ dvd_rfl)).mul (hunit D n dvd_rfl)
    · intro y
      obtain ⟨n, y₀, hy₀⟩ := exists_pow_smul_eq_tensorLocMap C C g y
      obtain ⟨k, x₀, hx₀⟩ := hmsurj y₀
      rw [← map_pow, algebraMap_smul] at hx₀
      obtain ⟨u, hu⟩ := (hunit D k hm₀g).mul (hunit D n dvd_rfl)
      refine ⟨↑u⁻¹ * tensorLocMap C D g x₀, ?_⟩
      have hΘu : Θ ↑u = algebraMap B _ (m₀ ^ k * g ^ n) := by
        rw [hu, ← map_mul, AlgHom.commutes]
      have hΘu' : Θ ↑u⁻¹ * algebraMap B _ (m₀ ^ k * g ^ n) = 1 := by
        rw [← hΘu, ← map_mul, Units.inv_mul, map_one]
      rw [map_mul, hcomm]
      show Θ ↑u⁻¹ * tensorLocMap C C g (Ψ x₀) = y
      rw [← hx₀, map_smul, ← hy₀, smul_smul, Algebra.smul_def, ← mul_assoc, hΘu', one_mul]

end Model

end Algebra

end

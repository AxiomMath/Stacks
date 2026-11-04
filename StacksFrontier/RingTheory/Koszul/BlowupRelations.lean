module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Functoriality
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular

@[expose] public section

/-!
# The Koszul complex of the blowup relations

Let `A` be a commutative ring, `a ∈ A` and `b₁, …, b_r ∈ A`. The *blowup relations* attached to
this data are the elements

`f_j = a·X_j - b_j ∈ P = A[X₁, …, X_r]`,

the relations cutting out the affine blowup algebra `A[(b₁, …, b_r)/a]` inside `P`. This file
records two facts about their Koszul complex `K_•(f₁, …, f_r)`.

The first is formal: the Koszul complex of a sequence of length `r` is built from the exterior
powers of a free module of rank `r`, so all its terms in degrees above `r` vanish.

The second is the key finiteness statement. Inverting `a` turns `f_j` into the unit multiple
`a·(X_j - b_j/a)` of a translated variable, and translated variables form a regular sequence; so
over `P[1/a]` the sequence `f` is Koszul-regular. Since `P[1/a]` is a flat `P`-algebra, the
positive Koszul homology of `f` over `P` dies after inverting `a`, and since `P` is Noetherian
these homology modules are finite, so each is annihilated by a power of `a`. Only the degrees
`1 ≤ i ≤ r` carry homology, so one exponent works for all of them at once.

## Main results

* `Koszul.subsingleton_exteriorPower_of_rank_lt`: `⋀ⁿ(Rʳ) = 0` for `n > r`.
* `Koszul.isZero_seqComplex_X_of_rank_lt`: the degree-`n` term of the Koszul complex of a
  sequence of length `r` is zero for `n > r`.
* `Koszul.exists_pow_smul_koszul_homology_eq_zero`: a single power of `a` annihilates
  `Hᵢ(K_•(f))` for every `i ≥ 1`.
* `Koszul.exists_pow_smul_ker_le_range`: the same statement spelled out on the Koszul
  differentials, as `aᶜ · ker(dᵢ) ⊆ im(dᵢ₊₁)` for every `i`.

## Implementation notes

The localization of `P = A[X₁, …, X_r]` away from `a` is realized as the polynomial ring
`A[1/a][X₁, …, X_r]`, which is a localization of `P` at the powers of `a` by
`MvPolynomial.isLocalization`; this uses `MvPolynomial.algebraMvPolynomial`, a local instance
here as it is in Mathlib.

The passage from the categorical `HomologicalComplex.homology` to the explicit quotient
`ker(dᵢ)/im(dᵢ₊₁)` goes through `CategoryTheory.ShortComplex.moduleCatHomologyIso`.
-/

open scoped ExteriorAlgebra TensorProduct
open CategoryTheory

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace Koszul

universe u

/-! ### Vanishing above the rank -/

/-- The `n`-th exterior power of a free module of rank `r` vanishes once `n` exceeds `r`: its
basis is indexed by the `n`-element subsets of `Fin r`, and there are none. -/
theorem subsingleton_exteriorPower_of_rank_lt {R : Type*} [CommRing R] {r n : ℕ} (h : r < n) :
    Subsingleton (⋀[R]^n (Fin r → R)) := by
  have hempty : IsEmpty (Set.powersetCard (Fin r) n) := by
    refine ⟨fun s => ?_⟩
    have h1 : (s : Finset (Fin r)).card = n := Set.powersetCard.card_eq s
    have h2 : (s : Finset (Fin r)).card ≤ r := by
      simpa using Finset.card_le_univ (s : Finset (Fin r))
    omega
  exact (Module.Basis.exteriorPower (R := R) n (Pi.basisFun R (Fin r))).repr.toEquiv.subsingleton

/-- The degree-`n` term of the Koszul complex of a sequence `f₁, …, f_r` is `⋀ⁿ(Rʳ)`. -/
theorem seqComplex_X {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    (seqComplex f).X n = ModuleCat.of R (⋀[R]^n (Fin r → R)) :=
  rfl

/-- The Koszul complex of a sequence of length `r` is concentrated in degrees `≤ r`. -/
theorem isZero_seqComplex_X_of_rank_lt {R : Type u} [CommRing R] {r n : ℕ} (f : Fin r → R)
    (h : r < n) : Limits.IsZero ((seqComplex f).X n) := by
  rw [seqComplex_X, ModuleCat.isZero_iff_subsingleton]
  exact subsingleton_exteriorPower_of_rank_lt h

/-! ### Generalities on the homology of a complex of modules -/

/-- The homology of a complex of modules vanishes in any degree in which the complex itself
vanishes, being a subquotient of that term. -/
private theorem subsingleton_homology_of_subsingleton_X {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) (h : Subsingleton (C.X i)) :
    Subsingleton (C.homology i) := by
  have _ : Subsingleton (C.cycles i) :=
    Function.Injective.subsingleton ((ModuleCat.mono_iff_injective (C.iCycles i)).1 inferInstance)
  exact Function.Surjective.subsingleton
    ((ModuleCat.epi_iff_surjective (C.homologyπ i)).1 inferInstance)

/-- Over a Noetherian ring, the homology of a complex of finite modules is finite, being a
subquotient of a finite module. -/
private theorem finite_homology {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) (h : Module.Finite R (C.X i)) :
    Module.Finite R (C.homology i) := by
  have _ := h
  have _ : IsNoetherian R (C.X i) := inferInstance
  have hinj : Function.Injective (C.iCycles i).hom :=
    (ModuleCat.mono_iff_injective (C.iCycles i)).1 inferInstance
  have _ : Module.Finite R (C.cycles i) :=
    Module.Finite.equiv (LinearEquiv.ofInjective (C.iCycles i).hom hinj).symm
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (C.homologyπ i)).1 inferInstance)

/-- If a scalar `t` annihilates the homology of a short complex of modules, then `t·z` lies in
the image of the first map for every `z` in the kernel of the second. The two maps are supplied
as linear maps `g₁` and `g₂`. -/
private theorem mem_range_of_smul_homology_eq_zero {R : Type u} [CommRing R]
    (D : ShortComplex (ModuleCat.{u} R)) [D.HasHomology] (t : R)
    (h : ∀ q : D.homology, t • q = 0)
    {g₁ : D.X₁ →ₗ[R] D.X₂} (hg₁ : D.f.hom = g₁)
    {g₂ : D.X₂ →ₗ[R] D.X₃} (hg₂ : D.g.hom = g₂)
    (x : D.X₂) (hx : g₂ x = 0) :
    t • x ∈ LinearMap.range g₁ := by
  subst hg₁
  subst hg₂
  have hzero : ∀ q : D.moduleCatLeftHomologyData.H, t • q = 0 := by
    intro q
    obtain ⟨p, hp⟩ := D.moduleCatHomologyIso.toLinearEquiv.surjective q
    rw [← hp, ← map_smul, h p, map_zero]
  have hq : (Submodule.Quotient.mk (t • (⟨x, hx⟩ : LinearMap.ker D.g.hom)) :
      LinearMap.ker D.g.hom ⧸ LinearMap.range D.moduleCatToCycles) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact hzero _
  rw [Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨z, hz⟩ := hq
  exact ⟨z, congrArg Subtype.val hz⟩

/-- If a scalar `t` annihilates the degree-`i+1` homology of a chain complex of modules, then
`t·z` is a boundary for every cycle `z` of degree `i+1`. The two differentials around degree
`i+1` are supplied as linear maps `g₁` and `g₂`. -/
private theorem mem_range_d_of_smul_homology_eq_zero {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) (t : R)
    (h : ∀ q : C.homology (i + 1), t • q = 0)
    {g₁ : C.X (i + 1 + 1) →ₗ[R] C.X (i + 1)}
    (hg₁ : C.d (i + 1 + 1) (i + 1) = ModuleCat.ofHom g₁)
    {g₂ : C.X (i + 1) →ₗ[R] C.X i} (hg₂ : C.d (i + 1) i = ModuleCat.ofHom g₂)
    (x : C.X (i + 1)) (hx : g₂ x = 0) :
    t • x ∈ LinearMap.range g₁ := by
  have h' : ∀ q : (C.sc' (i + 1 + 1) (i + 1) i).homology, t • q = 0 := by
    intro q
    obtain ⟨p, hp⟩ := (C.homologyIsoSc' (i + 1 + 1) (i + 1) i (by simp)
      (by simp)).toLinearEquiv.surjective q
    rw [← hp, ← map_smul, h p, map_zero]
  have hff : (C.sc' (i + 1 + 1) (i + 1) i).f.hom = g₁ :=
    congrArg (fun φ => ModuleCat.Hom.hom φ) hg₁
  have hgg : (C.sc' (i + 1 + 1) (i + 1) i).g.hom = g₂ :=
    congrArg (fun φ => ModuleCat.Hom.hom φ) hg₂
  exact mem_range_of_smul_homology_eq_zero _ t h' hff hgg x hx

/-! ### Uniform annihilation of a finite module -/

/-- If `tⁿ` kills `x`, then so does every higher power of `t`. -/
private theorem pow_smul_eq_zero_of_le {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (t : R) {x : M} {n m : ℕ} (h : t ^ n • x = 0) (hnm : n ≤ m) :
    t ^ m • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  rw [pow_add, mul_smul, h, smul_zero]

/-- If every element of a finite module is annihilated by some power of `t`, then one power of
`t` annihilates the whole module. -/
private theorem exists_pow_smul_eq_zero_of_finite {R : Type*} [CommRing R] (t : R)
    (M : Type*) [AddCommGroup M] [Module R M] (hM : Module.Finite R M)
    (h : ∀ x : M, ∃ n : ℕ, t ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, t ^ n • x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨s.sup fun x => (h x).choose, fun x => ?_⟩
  have hle : Submodule.span R (s : Set M)
      ≤ LinearMap.ker (LinearMap.lsmul R M (t ^ s.sup fun x => (h x).choose)) := by
    rw [Submodule.span_le]
    intro y hy
    have hy' : y ∈ s := by simpa using hy
    exact pow_smul_eq_zero_of_le t (h y).choose_spec
      (Finset.le_sup (f := fun x => (h x).choose) hy')
  have hmem : x ∈ Submodule.span R (s : Set M) := by rw [hs]; exact Submodule.mem_top
  simpa using hle hmem

/-- If `S` is a localization of `R` at the powers of `t` and `S ⊗[R] M` vanishes, then every
element of `M` is annihilated by some power of `t`. -/
private theorem exists_pow_smul_eq_zero_of_subsingleton_tensor {R : Type u} [CommRing R] (t : R)
    (S : Type u) [CommRing S] [Algebra R S] (hS : IsLocalization (Submonoid.powers t) S)
    (M : Type u) [AddCommGroup M] [Module R M] (h : Subsingleton (S ⊗[R] M)) (x : M) :
    ∃ n : ℕ, t ^ n • x = 0 := by
  have _ := hS
  have _ := h
  have h0 : (TensorProduct.mk R S M 1) x = 0 := Subsingleton.elim _ _
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers t) (TensorProduct.mk R S M 1)).1 h0
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 s.2
  exact ⟨n, by rw [hn]; simpa [Submonoid.smul_def] using hs⟩

/-! ### Regularity of the blowup relations after inverting `a` -/

/-- Multiplying every member of a Koszul-regular sequence by one unit keeps it Koszul-regular:
the two sequences differ by the invertible diagonal matrix `u·1`. -/
private theorem isKoszulRegular_unit_mul {R : Type u} [CommRing R] {r : ℕ} (u : R) (hu : IsUnit u)
    (h : Fin r → R) (hh : IsKoszulRegular h) :
    IsKoszulRegular (fun j => u * h j) := by
  have hx : IsUnit (Matrix.diagonal fun _ : Fin r => u) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    simpa using hu.pow r
  obtain ⟨e⟩ := seqComplex_mulVec_iso h _ hx
  have hmul : Matrix.mulVec (Matrix.diagonal fun _ : Fin r => u) h = fun j => u * h j := by
    funext j
    simp [Matrix.mulVec_diagonal]
  rw [hmul] at e
  exact fun i hi => (hh i hi).of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso e.symm)

/-- The translation automorphism `X_j ↦ X_j - c_j` of a polynomial ring. -/
private noncomputable def translate {L : Type u} [CommRing L] {r : ℕ} (c : Fin r → L) :
    MvPolynomial (Fin r) L ≃ₐ[L] MvPolynomial (Fin r) L :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun j => MvPolynomial.X j - MvPolynomial.C (c j))
    (MvPolynomial.aeval fun j => MvPolynomial.X j + MvPolynomial.C (c j))
    (by apply MvPolynomial.algHom_ext; intro j; simp)
    (by apply MvPolynomial.algHom_ext; intro j; simp)

/-- The translation automorphism sends `X_j` to `X_j - c_j`. -/
private theorem translate_X {L : Type u} [CommRing L] {r : ℕ} (c : Fin r → L) (j : Fin r) :
    translate c (MvPolynomial.X j) = MvPolynomial.X j - MvPolynomial.C (c j) := by
  show MvPolynomial.aeval (fun k => MvPolynomial.X k - MvPolynomial.C (c k))
    (MvPolynomial.X j) = _
  simp

/-- The translated variables `X₁ - c₁, …, X_r - c_r` form a weakly regular sequence in a
polynomial ring, being the image of the variables under a translation automorphism. -/
private theorem isWeaklyRegular_ofFn_X_sub_C {L : Type u} [CommRing L] (r : ℕ) (c : Fin r → L) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin r) L)
      (List.ofFn fun j => MvPolynomial.X j - MvPolynomial.C (c j)) := by
  cases r with
  | zero => simp
  | succ m =>
    have hmap : (List.ofFn (MvPolynomial.X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) L)).map
        (translate c).toRingEquiv
        = List.ofFn fun j => MvPolynomial.X j - MvPolynomial.C (c j) := by
      rw [List.map_ofFn]
      exact congrArg List.ofFn (funext fun j => translate_X c j)
    have := (isWeaklyRegular_ringEquiv (translate c).toRingEquiv
      (List.ofFn (MvPolynomial.X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) L))).1
      (MvPolynomial.isWeaklyRegular_ofFn_X m)
    rwa [hmap] at this

/-- In a polynomial ring over a ring in which `u` is a unit, the sequence `u·X_j - u·c_j` is
Koszul-regular: it is `u` times the translated variables. -/
private theorem isKoszulRegular_unit_mul_X_sub_C {L : Type u} [CommRing L] {r : ℕ} (u : L)
    (hu : IsUnit u) (c : Fin r → L) :
    IsKoszulRegular fun j : Fin r =>
      (MvPolynomial.C u : MvPolynomial (Fin r) L)
        * (MvPolynomial.X j - MvPolynomial.C (c j)) := by
  refine isKoszulRegular_unit_mul _ (hu.map MvPolynomial.C) _ ?_
  exact (isKoszulRegularOn_self_iff _).1
    ((isKoszulRegularOn_and_isKoszulRegular_of_regular
      (M := MvPolynomial (Fin r) L)).1 (isWeaklyRegular_ofFn_X_sub_C r c))

/-! ### Annihilating the positive Koszul homology -/

/-- The polynomial ring over the localization `A[1/a]` is the localization of `A[X₁, …, X_r]` at
the powers of the constant `a`. -/
private theorem isLocalization_mvPolynomial_away {A : Type u} [CommRing A] (a : A) (r : ℕ) :
    IsLocalization (Submonoid.powers (MvPolynomial.C a : MvPolynomial (Fin r) A))
      (MvPolynomial (Fin r) (Localization.Away a)) :=
  Submonoid.map_powers (MvPolynomial.C (σ := Fin r)) a ▸
    MvPolynomial.isLocalization (σ := Fin r) (Submonoid.powers a) (Localization.Away a)

/-- After inverting `a`, the positive Koszul homology of the blowup relations vanishes: the
polynomial ring over `A[1/a]` is a flat localization of `P` in which the relations become a
unit multiple of a translated set of variables, hence Koszul-regular. -/
private theorem subsingleton_tensor_homology {A : Type u} [CommRing A] (a : A) {r : ℕ}
    (b : Fin r → A) (i : ℕ) (hi : i ≠ 0) :
    Subsingleton (MvPolynomial (Fin r) (Localization.Away a)
      ⊗[MvPolynomial (Fin r) A] ((seqComplex fun j : Fin r =>
        MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j)).homology i)) := by
  have _ := isLocalization_mvPolynomial_away a r
  have _ : Module.Flat (MvPolynomial (Fin r) A) (MvPolynomial (Fin r) (Localization.Away a)) :=
    IsLocalization.flat _ (Submonoid.powers (MvPolynomial.C a : MvPolynomial (Fin r) A))
  -- the image of the blowup relations is a unit multiple of translated variables
  have hunit : IsUnit (algebraMap A (Localization.Away a) a) :=
    IsLocalization.Away.algebraMap_isUnit a
  have himg : (fun j : Fin r => algebraMap (MvPolynomial (Fin r) A)
        (MvPolynomial (Fin r) (Localization.Away a))
        (MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j)))
      = fun j : Fin r => MvPolynomial.C (algebraMap A (Localization.Away a) a)
        * (MvPolynomial.X j - MvPolynomial.C (IsLocalization.Away.invSelf a
            * algebraMap A (Localization.Away a) (b j))) := by
    funext j
    rw [MvPolynomial.algebraMap_def]
    rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_X, mul_sub,
      ← MvPolynomial.C_mul, ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  have hreg : IsKoszulRegular fun j : Fin r => algebraMap (MvPolynomial (Fin r) A)
      (MvPolynomial (Fin r) (Localization.Away a))
      (MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j)) := by
    rw [himg]
    exact isKoszulRegular_unit_mul_X_sub_C _ hunit _
  -- flat base change
  have h1 : IsKoszulRegularOn (fun j : Fin r => algebraMap (MvPolynomial (Fin r) A)
        (MvPolynomial (Fin r) (Localization.Away a))
        (MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j)))
      (MvPolynomial (Fin r) (Localization.Away a) ⊗[MvPolynomial (Fin r) A]
        MvPolynomial (Fin r) A) :=
    isKoszulRegularOn_of_linearEquiv _
      (TensorProduct.AlgebraTensorModule.rid (MvPolynomial (Fin r) A)
        (MvPolynomial (Fin r) (Localization.Away a))
        (MvPolynomial (Fin r) (Localization.Away a))).symm
      ((isKoszulRegularOn_self_iff _).2 hreg)
  have _ := ModuleCat.isZero_iff_subsingleton.1 (h1 i hi)
  obtain ⟨e⟩ := KoszulC.homology_baseChange_linearEquiv
    (S := MvPolynomial (Fin r) (Localization.Away a))
    (fun j : Fin r => MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j))
    (MvPolynomial (Fin r) A) i
  have _ := e.symm.toEquiv.subsingleton
  have ecoeff := TensorProduct.congr
    (LinearEquiv.refl (MvPolynomial (Fin r) A) (MvPolynomial (Fin r) (Localization.Away a)))
    (homologySelfIso (fun j : Fin r =>
      MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j)) i).toLinearEquiv
  exact ecoeff.symm.toEquiv.subsingleton

/-- **One power of `a` annihilates all positive Koszul homology of the blowup relations.**
For `a, b₁, …, b_r` in a Noetherian ring `A` there is an exponent `c` with
`aᶜ · Hᵢ(K_•(a·X₁ - b₁, …, a·X_r - b_r)) = 0` for every `i ≥ 1`, uniformly in `i`. -/
theorem exists_pow_smul_koszul_homology_eq_zero {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a : A) {r : ℕ} (b : Fin r → A) :
    ∃ c : ℕ, ∀ i : ℕ, 1 ≤ i → ∀ x : (seqComplex
        (fun j : Fin r => MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j))).homology i,
      (MvPolynomial.C a ^ c : MvPolynomial (Fin r) A) • x = 0 := by
  classical
  have hdeg : ∀ i : ℕ, ∃ n : ℕ, ∀ x : (seqComplex
      (fun j : Fin r => MvPolynomial.C a * MvPolynomial.X j
        - MvPolynomial.C (b j))).homology (i + 1),
      (MvPolynomial.C a ^ n : MvPolynomial (Fin r) A) • x = 0 := by
    intro i
    have hfin : Module.Finite (MvPolynomial (Fin r) A) ((seqComplex
        (fun j : Fin r => MvPolynomial.C a * MvPolynomial.X j
          - MvPolynomial.C (b j))).homology (i + 1)) := by
      refine finite_homology _ _ ?_
      rw [seqComplex_X]
      exact inferInstanceAs (Module.Finite (MvPolynomial (Fin r) A)
        (⋀[MvPolynomial (Fin r) A]^(i + 1) (Fin r → MvPolynomial (Fin r) A)))
    refine exists_pow_smul_eq_zero_of_finite _ _ hfin fun x => ?_
    exact exists_pow_smul_eq_zero_of_subsingleton_tensor _
      (MvPolynomial (Fin r) (Localization.Away a)) (isLocalization_mvPolynomial_away a r) _
      (subsingleton_tensor_homology a b (i + 1) (Nat.succ_ne_zero i)) x
  choose n hn using hdeg
  refine ⟨(Finset.range (r + 1)).sup n, fun i hi x => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rcases Nat.lt_or_ge r (j + 1) with hbig | hsmall
  · have hzero : Subsingleton ((seqComplex
        (fun j : Fin r => MvPolynomial.C a * MvPolynomial.X j
          - MvPolynomial.C (b j))).homology (j + 1)) := by
      refine subsingleton_homology_of_subsingleton_X _ _ ?_
      rw [seqComplex_X]
      exact subsingleton_exteriorPower_of_rank_lt hbig
    rw [Subsingleton.elim x 0, smul_zero]
  · have hjmem : j ∈ Finset.range (r + 1) := by simp; omega
    exact pow_smul_eq_zero_of_le _ (hn j x) (Finset.le_sup hjmem)

/-- **The same annihilation, written out on the Koszul differentials.** For `a, b₁, …, b_r` in a
Noetherian ring `A` there is an exponent `c` such that `aᶜ` carries every cycle of the Koszul
complex of `a·X₁ - b₁, …, a·X_r - b_r` into the boundaries, in every positive degree. -/
theorem exists_pow_smul_ker_le_range {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a : A) {r : ℕ} (b : Fin r → A) :
    ∃ c : ℕ, ∀ (i : ℕ) (x : ⋀[MvPolynomial (Fin r) A]^(i + 1) (Fin r → MvPolynomial (Fin r) A)),
      Koszul.d (Koszul.seqDual (fun j : Fin r =>
          MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j))) i x = 0 →
      (MvPolynomial.C a ^ c : MvPolynomial (Fin r) A) • x
        ∈ LinearMap.range (Koszul.d (Koszul.seqDual (fun j : Fin r =>
            MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j))) (i + 1)) := by
  obtain ⟨c, hc⟩ := exists_pow_smul_koszul_homology_eq_zero a b
  refine ⟨c, fun i x hx => ?_⟩
  exact mem_range_d_of_smul_homology_eq_zero
    (seqComplex fun j : Fin r => MvPolynomial.C a * MvPolynomial.X j - MvPolynomial.C (b j))
    i (MvPolynomial.C a ^ c) (hc (i + 1) (Nat.le_add_left 1 i))
    (seqComplex_d _ (i + 1)) (seqComplex_d _ i) x hx

end Koszul

end

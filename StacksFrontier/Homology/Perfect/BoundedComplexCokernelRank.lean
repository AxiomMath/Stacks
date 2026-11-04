module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneModule.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealAlternatingRank
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
public import StacksFrontier.RingTheory.Fitting.ProjectiveDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cokernels of the differentials of a bounded complex of finite free modules

Let `C` be a bounded complex of finite free modules over a commutative ring `A`, written in chosen
bases as a `BoundedComplex A`, so that `d^i` is an `r_{i+1} × r_i` matrix. This file studies the
cokernel `coker d^i = A^{r_{i+1}} / d^i(A^{r_i})`: its Fitting ideals are ideals of minors of
`d^i`, its rank is computed from the ranks of the cohomology when the cohomology modules are
finite locally free, and principal ideals of minors give resolutions of length one of the
cohomology by finite projective modules. These are the module-theoretic steps of the proof of
[Stacks, Tag 0ESQ].

## Main definitions

* `BoundedComplex.cokernelD`: the cokernel of `d^i`.
* `BoundedComplex.cokernelDToRange`: the surjection `coker d^i → im d^{i+1}` induced by `d^{i+1}`;
  its kernel is `H^{i+1}` (`BoundedComplex.homologyEquivKerCokernelDToRange`).

## Main results

* `BoundedComplex.fittingIdeal_cokernelD` and `BoundedComplex.fittingIdeal_cokernelD_sub_one`:
  the Fitting ideals of `coker d^i` at the indices `r_{i+1} - n` and `r_{i+1} - n - 1` are the
  ideals of `n × n` and of `(n + 1) × (n + 1)` minors of `d^i`.
* `BoundedComplex.isFiniteLocallyFreeOfRank_cokernelD`: if `C` vanishes above `m` and each `H^j` is
  finite locally free of rank `h_j`, then `coker d^i` is finite locally free of rank
  `r_{i+1} - ρ_i`, where `ρ_i = χ_{≥ i+1}(C) - (h_{i+1} - h_{i+2} + ⋯)`; over a nontrivial ring
  `0 ≤ ρ_i ≤ r_{i+1}` (`BoundedComplex.tailEulerCharacteristic_sub_alternatingRankSum_mem_Icc`).
* `BoundedComplex.minorIdeal_d_eq_top_and_minorIdeal_d_succ_eq_bot`: consequently the
  `ρ_i × ρ_i` minors of `d^i` generate the unit ideal and its `(ρ_i + 1) × (ρ_i + 1)` minors
  vanish.
* `BoundedComplex.exists_shortExact_homology_of_minorIdeal`: if the `ρ_i × ρ_i` minors of every
  `d^i` generate the ideal of a nonzerodivisor and the `(ρ_i + 1) × (ρ_i + 1)` minors vanish, then
  every cohomology module has a resolution `0 → P₁ → P₀ → H^i → 0` by finite projective modules.

## Implementation notes

The rank computation is a descending induction on `i` along the short exact sequences
`0 → H^{i+1} → coker d^i → im d^{i+1} → 0` and `0 → im d^{i+1} → A^{r_{i+2}} → coker d^{i+1} → 0`,
which split because their last terms are projective; ranks are compared with
`Module.rankAtStalk`. The resolutions come from [Stacks, Tag 0F7M]: the Fitting ideals of
`coker d^i` make its projective dimension at most one, so `im d^i` and `ker d^i` are projective,
and `0 → im d^{i-1} → ker d^i → H^i → 0` is the resolution.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 0F7M](https://stacks.math.columbia.edu/tag/0F7M)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace Stacks.CokernelRank

variable {A : Type u} [CommRing A]

/-! ### Homology of a short complex of modules -/

/-- The homology of a short complex of modules `X₁ → X₂ → X₃` is `ker g / (im f ∩ ker g)`, the
quotient of `ker g` by the preimage of `im f`. -/
def homologyEquivQuotientComap (S : ShortComplex (ModuleCat.{u} A)) :
    S.homology ≃ₗ[A] LinearMap.ker S.g.hom ⧸
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype :=
  S.moduleCatHomologyIso.toLinearEquiv ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)

/-- For linear maps `f : M → N` and `g : N → P` with `g ∘ f = 0`, the quotient of `ker g` by the
preimage of `im f` is the kernel of the map `N / im f → P` induced by `g`. -/
def quotientComapEquivKerLiftQ {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : LinearMap.range f ≤ LinearMap.ker g) :
    (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[A]
      LinearMap.ker ((LinearMap.range f).liftQ g hfg) := by
  let φ : LinearMap.ker g →ₗ[A] LinearMap.ker ((LinearMap.range f).liftQ g hfg) :=
    LinearMap.codRestrict _ ((LinearMap.range f).mkQ ∘ₗ (LinearMap.ker g).subtype)
      (fun x => by simp)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (LinearMap.range f).mkQ_surjective y
    have hx : g x = 0 := by simpa using hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : LinearMap.ker φ = (LinearMap.range f).comap (LinearMap.ker g).subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro hx
      exact (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 hx)
  exact Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ φ.quotKerEquivOfSurjective hφ

/-! ### Split short exact sequences and ranks -/

/-- A short exact sequence `0 → K → M → N → 0` whose last term is projective splits:
`M ≅ K × N`. -/
theorem nonempty_linearEquiv_prod_of_exact {K M N : Type*} [AddCommGroup K] [Module A K]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module.Projective A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N) (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g) : Nonempty (M ≃ₗ[A] K × N) := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
  exact ⟨(H.splitSurjectiveEquiv hf ⟨l, hl⟩).1⟩

/-- The kernel of a surjection from a finite projective module onto a projective module is
finite and projective, and ranks at stalks add up. -/
@[sga "6 I 1.3" "special case"]
theorem finite_projective_ker_and_rankAtStalk_of_surjective {M N : Type u} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] [Module.Finite A M] [Module.Projective A M]
    [Module.Projective A N] (g : M →ₗ[A] N) (hg : Function.Surjective g) :
    Module.Finite A (LinearMap.ker g) ∧ Module.Projective A (LinearMap.ker g) ∧
      Module.rankAtStalk (R := A) M =
        Module.rankAtStalk (R := A) (LinearMap.ker g) + Module.rankAtStalk (R := A) N := by
  obtain ⟨e⟩ := nonempty_linearEquiv_prod_of_exact _ g (LinearMap.ker g).injective_subtype hg
    (LinearMap.exact_subtype_ker_map g)
  have : Module.Finite A N := Module.Finite.of_surjective g hg
  have hfin : Module.Finite A (LinearMap.ker g) :=
    Module.Finite.of_surjective (LinearMap.fst A _ N ∘ₗ e.toLinearMap)
      (Prod.fst_surjective.comp e.surjective)
  have hproj : Module.Projective A (LinearMap.ker g) :=
    Module.Projective.of_split (e.symm.toLinearMap ∘ₗ LinearMap.inl A _ N)
      (LinearMap.fst A _ N ∘ₗ e.toLinearMap) (by ext x; simp)
  refine ⟨hfin, hproj, ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]

/-- In a short exact sequence `0 → K → M → N → 0` of modules with `K` and `N` finite and
projective, `M` is projective and ranks at stalks add up. -/
theorem projective_and_rankAtStalk_of_exact {K M N : Type u} [AddCommGroup K] [Module A K]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module.Finite A K]
    [Module.Projective A K] [Module.Finite A N] [Module.Projective A N]
    (f : K →ₗ[A] M) (g : M →ₗ[A] N) (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g) :
    Module.Projective A M ∧
      Module.rankAtStalk (R := A) M =
        Module.rankAtStalk (R := A) K + Module.rankAtStalk (R := A) N := by
  obtain ⟨e⟩ := nonempty_linearEquiv_prod_of_exact f g hf hg H
  exact ⟨Module.Projective.of_equiv e.symm, by
    rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]⟩

/-- A finite free module `A^n` has rank `n` at every prime. -/
theorem rankAtStalk_fin_fun (n : ℕ) (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (Fin n → A) p = n := by
  have : Nontrivial A := ⟨⟨0, 1, fun h => p.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (h ▸ p.asIdeal.zero_mem))⟩⟩
  simp

end Stacks.CokernelRank

open Stacks.CokernelRank

namespace BoundedComplex

variable {A : Type u} [CommRing A] (C : BoundedComplex A)

/-- The cokernel `A^{r_{i+1}} / d^i(A^{r_i})` of the `i`th differential of a bounded complex of
finite free modules. -/
abbrev cokernelD (i : ℤ) : Type u :=
  (Fin (C.rank (i + 1)) → A) ⧸ LinearMap.range (C.d i).mulVecLin

/-- The Fitting ideal of the cokernel of `d^i` at the index `r_{i+1} - n` is the ideal of
`n × n` minors of the matrix of `d^i`. -/
theorem fittingIdeal_cokernelD (i : ℤ) {n : ℕ} (hn : n ≤ C.rank (i + 1)) :
    fittingIdeal (R := A) (M := C.cokernelD i) ((C.rank (i + 1) - n : ℕ) : ℤ) =
      minorIdeal (C.d i) n := by
  let e : ((Fin (C.rank (i + 1)) → A) ⧸ Submodule.span A
      (Set.range (fun j : Fin (C.rank i) => fun k => C.d i k j))) ≃ₗ[A] C.cokernelD i :=
    Submodule.quotEquivOfEq _ _ (by rw [Matrix.range_mulVecLin]; rfl)
  rw [fittingIdeal_eq_minorIdeal_of_presentation (C.d i) _ e, Nat.sub_sub_self hn]

/-- The Fitting ideal of the cokernel of `d^i` at the index `r_{i+1} - n - 1` is the ideal of
`(n + 1) × (n + 1)` minors of the matrix of `d^i`; for `n = r_{i+1}` both sides vanish. -/
theorem fittingIdeal_cokernelD_sub_one (i : ℤ) {n : ℕ} (hn : n ≤ C.rank (i + 1)) :
    fittingIdeal (R := A) (M := C.cokernelD i) ((C.rank (i + 1) : ℤ) - n - 1) =
      minorIdeal (C.d i) (n + 1) := by
  rcases hn.lt_or_eq with hlt | heq
  · have h : ((C.rank (i + 1) : ℤ) - n - 1) = ((C.rank (i + 1) - (n + 1) : ℕ) : ℤ) := by omega
    rw [h, C.fittingIdeal_cokernelD i hlt]
  · rw [fittingIdeal_eq_bot_of_lt_zero (by omega),
      minorIdeal_eq_bot_of_card_lt _ _ (Or.inl (by simp [heq]))]

/-- The cokernel of a differential is finitely presented. -/
instance (i : ℤ) : Module.FinitePresentation A (C.cokernelD i) :=
  Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective _)
    (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range _)

/-- Consecutive differentials compose to zero. -/
theorem mulVecLin_d_comp_mulVecLin_d (i : ℤ) :
    (C.d (i + 1)).mulVecLin ∘ₗ (C.d i).mulVecLin = 0 := by
  rw [← Matrix.mulVecLin_mul, C.dd]
  ext
  simp

/-- The short complex `A^{r_i} → A^{r_{i+1}} → A^{r_{i+2}}` of the differentials `d^i`
and `d^{i+1}`. -/
abbrev shortComplexD (i : ℤ) : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (C.d i).mulVecLin (C.d (i + 1)).mulVecLin (by
    rw [← Matrix.mulVecLin_mul, C.dd]
    ext
    simp)

/-- The cohomology of a bounded complex of finite free modules in degree `i + 1` is the
homology of the short complex `shortComplexD i`. -/
def homologyIsoShortComplexD (i : ℤ) :
    C.toCochainComplex.homology (i + 1) ≅ (C.shortComplexD i).homology :=
  C.toCochainComplex.homologyIsoSc' i (i + 1) (i + 1 + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso
      (ShortComplex.isoMk (S₁ := C.toCochainComplex.sc' i (i + 1) (i + 1 + 1))
        (S₂ := C.shortComplexD i) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl)
        (by simp; rfl))

/-! ### The induced map out of the cokernel -/

/-- The image of `d^i` lies in the kernel of `d^{i+1}`. -/
theorem range_d_le_ker_d (i : ℤ) :
    LinearMap.range (C.d i).mulVecLin ≤ LinearMap.ker (C.d (i + 1)).mulVecLin :=
  LinearMap.range_le_ker_iff.2 (C.mulVecLin_d_comp_mulVecLin_d i)

/-- The surjection `coker d^i → im d^{i+1}` induced by `d^{i+1}`. -/
def cokernelDToRange (i : ℤ) :
    C.cokernelD i →ₗ[A] LinearMap.range (C.d (i + 1)).mulVecLin :=
  (LinearMap.range (C.d i).mulVecLin).liftQ (C.d (i + 1)).mulVecLin.rangeRestrict (by
    rw [LinearMap.ker_rangeRestrict]
    exact C.range_d_le_ker_d i)

/-- The map `coker d^i → im d^{i+1}` is surjective. -/
theorem cokernelDToRange_surjective (i : ℤ) : Function.Surjective (C.cokernelDToRange i) :=
  Function.Surjective.of_comp (g := (LinearMap.range (C.d i).mulVecLin).mkQ)
    (LinearMap.surjective_rangeRestrict _)

/-- The cohomology `H^{i+1}` is the kernel of the surjection `coker d^i → im d^{i+1}`. -/
def homologyEquivKerCokernelDToRange (i : ℤ) :
    C.toCochainComplex.homology (i + 1) ≃ₗ[A] LinearMap.ker (C.cokernelDToRange i) :=
  (C.homologyIsoShortComplexD i).toLinearEquiv ≪≫ₗ
    homologyEquivQuotientComap (C.shortComplexD i) ≪≫ₗ
    quotientComapEquivKerLiftQ (C.d i).mulVecLin (C.d (i + 1)).mulVecLin (C.range_d_le_ker_d i)
    ≪≫ₗ LinearEquiv.ofEq _ _ (by
      ext x
      obtain ⟨y, rfl⟩ := (LinearMap.range (C.d i).mulVecLin).mkQ_surjective x
      simp [cokernelDToRange, Subtype.ext_iff])

/-! ### The rank of the cokernel of a differential -/

open Stacks.FittingComplex

/-- The tail Euler characteristic vanishes above the degrees where the complex lives. -/
theorem tailEulerCharacteristic_eq_zero_of_lt {m i : ℤ} (hm : ∀ j, m < j → C.rank j = 0)
    (hi : m < i) : C.tailEulerCharacteristic i = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_filter] at hj
  rw [hm j (by omega)]
  simp

/-- Two consecutive tail Euler characteristics add up to a rank:
`χ_{≥ i} + χ_{≥ i+1} = r_i`. -/
theorem tailEulerCharacteristic_add_tailEulerCharacteristic_succ (i : ℤ) :
    C.tailEulerCharacteristic i + C.tailEulerCharacteristic (i + 1) = C.rank i := by
  classical
  unfold tailEulerCharacteristic
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (g := fun j => if i = j then (C.rank j : ℤ) else 0), Finset.sum_ite_eq]
  · split_ifs with h
    · rfl
    · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h
      simp [h]
  · intro j _
    by_cases h1 : i = j
    · subst h1
      simp
    · by_cases h2 : i + 1 ≤ j
      · have h3 : (j - i).toNat = (j - (i + 1)).toNat + 1 := by omega
        rw [ite_eq_left (by omega), ite_eq_left h2, ite_eq_right h1, h3, pow_succ]
        ring
      · rw [ite_eq_right (by omega), ite_eq_right h2, ite_eq_right h1]
        simp

/-- Two consecutive alternating rank sums add up to a rank: below the bound `m`,
`r_{i+1} - r_{i+2} + ⋯` plus `r_{i+2} - r_{i+3} + ⋯` is `r_{i+1}`. -/
theorem alternatingRankSum_add_alternatingRankSum_succ (r : ℤ → ℕ) {m i : ℤ} (hi : i < m) :
    alternatingRankSum r m i + alternatingRankSum r m (i + 1) = r (i + 1) := by
  unfold alternatingRankSum
  have h : (m - i).toNat = (m - (i + 1)).toNat + 1 := by omega
  have h' : ∀ j : ℕ, (-1 : ℤ) ^ (j + 1) * (r (i + 1 + ((j + 1 : ℕ) : ℤ)) : ℤ) =
      -((-1) ^ j * (r (i + 1 + 1 + (j : ℤ)) : ℤ)) := by
    intro j
    rw [show i + 1 + ((j + 1 : ℕ) : ℤ) = i + 1 + 1 + (j : ℤ) by push_cast; ring]
    ring
  rw [h, Finset.sum_range_succ']
  simp only [h', Finset.sum_neg_distrib, pow_zero, one_mul, Nat.cast_zero, add_zero]
  ring

/-- The invariant of the descending induction: the cokernel of `d^i` is projective, of rank
`r_{i+1} - ρ_i` at every prime, where `ρ_i = χ_{≥ i+1} - (h_{i+1} - h_{i+2} + ⋯)`. -/
private def CokernelGood (r : ℤ → ℕ) (m i : ℤ) : Prop :=
  Module.Projective A (C.cokernelD i) ∧ ∀ p : PrimeSpectrum A,
    (Module.rankAtStalk (R := A) (C.cokernelD i) p : ℤ) =
      C.rank (i + 1) - (C.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i)

/-- If the cokernel of `d^i` is projective then so is the image of `d^i`, and the ranks of the
image and the cokernel add up to `r_{i+1}`. -/
theorem projective_range_d_and_rankAtStalk (i : ℤ) [Module.Projective A (C.cokernelD i)] :
    Module.Projective A (LinearMap.range (C.d i).mulVecLin) ∧ ∀ p : PrimeSpectrum A,
      Module.rankAtStalk (R := A) (LinearMap.range (C.d i).mulVecLin) p +
        Module.rankAtStalk (R := A) (C.cokernelD i) p = C.rank (i + 1) := by
  obtain ⟨-, hproj, hrank⟩ := finite_projective_ker_and_rankAtStalk_of_surjective
    (LinearMap.range (C.d i).mulVecLin).mkQ (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ] at hproj hrank
  refine ⟨hproj, fun p => ?_⟩
  have := congrFun hrank p
  rw [Pi.add_apply, rankAtStalk_fin_fun] at this
  exact this.symm

/-- The start of the induction: above the top degree the cokernel of `d^i` is zero. -/
private theorem cokernelGood_of_le (r : ℤ → ℕ) {m i : ℤ} (hm : ∀ j, m < j → C.rank j = 0)
    (hi : m ≤ i) : C.CokernelGood r m i := by
  have h0 : C.rank (i + 1) = 0 := hm _ (by omega)
  have : IsEmpty (Fin (C.rank (i + 1))) := by rw [h0]; infer_instance
  have : Subsingleton (C.cokernelD i) := (Submodule.mkQ_surjective _).subsingleton
  refine ⟨inferInstance, fun p => ?_⟩
  rw [Module.rankAtStalk_eq_zero_of_subsingleton, C.tailEulerCharacteristic_eq_zero_of_lt hm
    (by omega), alternatingRankSum_of_le hi, h0]
  simp

/-- The inductive step, along `0 → H^{i+1} → coker d^i → im d^{i+1} → 0`. -/
private theorem cokernelGood_of_succ {r : ℤ → ℕ} {m i : ℤ}
    (hr : Module.IsFiniteLocallyFreeOfRank A (C.toCochainComplex.homology (i + 1)) (r (i + 1)))
    (hi : i < m) (h : C.CokernelGood r m (i + 1)) : C.CokernelGood r m i := by
  obtain ⟨hQ, hQr⟩ := h
  obtain ⟨hB, hBr⟩ := C.projective_range_d_and_rankAtStalk (i + 1)
  let eH := C.homologyEquivKerCokernelDToRange i
  have : Module.FinitePresentation A (LinearMap.ker (C.cokernelDToRange i)) :=
    Module.finitePresentation_of_projective_of_exact _ _ (Submodule.injective_subtype _)
      (C.cokernelDToRange_surjective i) (LinearMap.exact_subtype_ker_map _)
  have : Module.Flat A (C.toCochainComplex.homology (i + 1)) :=
    Module.flat_of_isFiniteLocallyFreeOfRank hr
  have : Module.Flat A (LinearMap.ker (C.cokernelDToRange i)) := Module.Flat.of_linearEquiv eH.symm
  have : Module.Projective A (LinearMap.ker (C.cokernelDToRange i)) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨hproj, hrank⟩ := projective_and_rankAtStalk_of_exact _ _
    (Submodule.injective_subtype _) (C.cokernelDToRange_surjective i)
    (LinearMap.exact_subtype_ker_map _)
  refine ⟨hproj, fun p => ?_⟩
  have h1 := congrFun hrank p
  rw [Pi.add_apply, ← Module.rankAtStalk_eq_of_equiv eH,
    Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank _ hr] at h1
  have h2 := hBr p
  have h3 := hQr p
  have h4 := C.tailEulerCharacteristic_add_tailEulerCharacteristic_succ (i + 1)
  have h5 := alternatingRankSum_add_alternatingRankSum_succ r hi
  rw [h1]
  push_cast
  omega

/-- The invariant holds in every degree, by descending induction from the top degree. -/
private theorem cokernelGood (r : ℤ → ℕ) {m : ℤ} (hm : ∀ j, m < j → C.rank j = 0)
    (hr : ∀ j, Module.IsFiniteLocallyFreeOfRank A (C.toCochainComplex.homology j) (r j))
    (i : ℤ) : C.CokernelGood r m i := by
  suffices H : ∀ k : ℕ, ∀ i, m - k ≤ i → C.CokernelGood r m i from
    H (m - i).toNat i (by omega)
  intro k
  induction k with
  | zero => exact fun i hi => C.cokernelGood_of_le r hm (by simpa using hi)
  | succ k ih =>
    intro i hi
    by_cases hmi : m ≤ i
    · exact C.cokernelGood_of_le r hm hmi
    · exact C.cokernelGood_of_succ (hr (i + 1)) (by omega) (ih (i + 1) (by push_cast at hi; omega))

/-- **The rank of the cokernel of a differential.** Let `C` be a bounded complex of finite free
modules, of ranks `r_j`, vanishing above degree `m`, whose cohomology modules `H^j` are finite
locally free of rank `h_j`. Then the cokernel of `d^i` is finite locally free of rank
`r_{i+1} - ρ_i`, where `ρ_i = χ_{≥ i+1}(C) - (h_{i+1} - h_{i+2} + ⋯)`. -/
theorem isFiniteLocallyFreeOfRank_cokernelD {m : ℤ} (hm : ∀ j, m < j → C.rank j = 0)
    (r : ℤ → ℕ)
    (hr : ∀ j, Module.IsFiniteLocallyFreeOfRank A (C.toCochainComplex.homology j) (r j))
    (i : ℤ) :
    Module.IsFiniteLocallyFreeOfRank A (C.cokernelD i)
      ((C.rank (i + 1) : ℤ) -
        (C.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i)).toNat := by
  obtain ⟨hproj, hrank⟩ := C.cokernelGood r hm hr i
  refine Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq _ fun p => ?_
  have := hrank p
  omega

/-- Over a nontrivial ring, the integer `ρ_i = χ_{≥ i+1}(C) - (h_{i+1} - h_{i+2} + ⋯)` lies
between `0` and `r_{i+1}`: it is the rank of the image of `d^i`. -/
theorem tailEulerCharacteristic_sub_alternatingRankSum_mem_Icc [Nontrivial A] {m : ℤ}
    (hm : ∀ j, m < j → C.rank j = 0) (r : ℤ → ℕ)
    (hr : ∀ j, Module.IsFiniteLocallyFreeOfRank A (C.toCochainComplex.homology j) (r j))
    (i : ℤ) :
    0 ≤ C.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i ∧
      C.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i ≤ C.rank (i + 1) := by
  obtain ⟨hproj, hrank⟩ := C.cokernelGood r hm hr i
  obtain ⟨-, hB⟩ := C.projective_range_d_and_rankAtStalk i
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  have h1 := hrank ⟨M, hM.isPrime⟩
  have h2 := hB ⟨M, hM.isPrime⟩
  omega

/-- **The minors of a differential of a complex with finite locally free cohomology.** With
`ρ_i = χ_{≥ i+1}(C) - (h_{i+1} - h_{i+2} + ⋯)` as in `isFiniteLocallyFreeOfRank_cokernelD`, the
`ρ_i × ρ_i` minors of the matrix of `d^i` generate the unit ideal and its `(ρ_i + 1) × (ρ_i + 1)`
minors vanish. -/
theorem minorIdeal_d_eq_top_and_minorIdeal_d_succ_eq_bot {m : ℤ}
    (hm : ∀ j, m < j → C.rank j = 0) (r : ℤ → ℕ)
    (hr : ∀ j, Module.IsFiniteLocallyFreeOfRank A (C.toCochainComplex.homology j) (r j))
    (i : ℤ) :
    minorIdeal (C.d i) (C.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i).toNat = ⊤ ∧
      minorIdeal (C.d i)
        ((C.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i).toNat + 1) = ⊥ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  set ρ := C.tailEulerCharacteristic (i + 1) - alternatingRankSum r m i with hρ
  obtain ⟨h0, hle⟩ := C.tailEulerCharacteristic_sub_alternatingRankSum_mem_Icc hm r hr i
  have hn : ρ.toNat ≤ C.rank (i + 1) := by omega
  have hfit := ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := A) (M := C.cokernelD i)
    ((C.rank (i + 1) : ℤ) - ρ).toNat).out 1 2).1 (C.isFiniteLocallyFreeOfRank_cokernelD hm r hr i)
  have hc : (((C.rank (i + 1) : ℤ) - ρ).toNat : ℤ) = ((C.rank (i + 1) - ρ.toNat : ℕ) : ℤ) := by
    omega
  have hc' : (((C.rank (i + 1) : ℤ) - ρ).toNat : ℤ) - 1 = (C.rank (i + 1) : ℤ) - ρ.toNat - 1 := by
    omega
  rw [hc', C.fittingIdeal_cokernelD_sub_one i hn, hc, C.fittingIdeal_cokernelD i hn] at hfit
  exact ⟨hfit.2, hfit.1⟩

/-! ### Projective resolutions of length one of the cohomology -/

/-- If the `ρ × ρ` minors of the matrix of `d^i` generate an ideal `(g)` with `g` a
nonzerodivisor and its `(ρ + 1) × (ρ + 1)` minors vanish, then the image of `d^i` is a projective
module: by [Stacks, Tag 0F7M] the cokernel of `d^i` has projective dimension at most one. -/
theorem projective_range_d_of_minorIdeal (i : ℤ) {ρ : ℕ} {g : A} (hg : IsRegular g)
    (hρ : minorIdeal (C.d i) ρ = Ideal.span {g}) (hρ' : minorIdeal (C.d i) (ρ + 1) = ⊥) :
    Module.Projective A (LinearMap.range (C.d i).mulVecLin) := by
  by_cases hle : ρ ≤ C.rank (i + 1)
  · have hk := C.fittingIdeal_cokernelD i hle
    have hk1 := C.fittingIdeal_cokernelD_sub_one i hle
    rw [hρ] at hk
    rw [hρ'] at hk1
    have hk1' : fittingIdeal (R := A) (M := C.cokernelD i)
        (((C.rank (i + 1) - ρ : ℕ) : ℤ) - 1) = ⊥ := by
      rw [← hk1]
      congr 1
      omega
    obtain ⟨hpd, -⟩ :=
      hasProjectiveDimensionLE_one_and_split_of_fittingIdeal_eq_span_singleton _ g hg hk hk1'
    have hpd' : HasProjectiveDimensionLE (ModuleCat.of A (C.cokernelD i)) 1 :=
      hasProjectiveDimensionLT_of_iso (ULift.moduleEquiv.toModuleIso) _
    let S := (LinearMap.range (C.d i).mulVecLin).mkQ.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective _)
    have hX₂ : Projective S.X₂ := (IsProjective.iff_projective _).1 inferInstance
    have hX₁ : HasProjectiveDimensionLT S.X₁ 1 := (hS.hasProjectiveDimensionLT_X₃_iff 0 hX₂).1 hpd'
    have : Projective S.X₁ := projective_iff_hasProjectiveDimensionLT_one.2 hX₁
    rw [← Submodule.ker_mkQ (LinearMap.range (C.d i).mulVecLin)]
    exact (IsProjective.iff_projective _).2 this
  · have hbot : minorIdeal (C.d i) ρ = ⊥ :=
      minorIdeal_eq_bot_of_card_lt _ _ (Or.inl (by simp only [Fintype.card_fin]; omega))
    rw [hbot, eq_comm, Ideal.span_singleton_eq_bot] at hρ
    subst hρ
    have : Subsingleton A := by
      by_contra hA
      rw [not_subsingleton_iff_nontrivial] at hA
      exact not_isRegular_zero hg
    have : Subsingleton (LinearMap.range (C.d i).mulVecLin) := Module.subsingleton A _
    infer_instance

/-- If the image of `d^i` is projective then the kernel of `d^i` is finite and projective: it is
the kernel of the split surjection `A^{r_i} → im d^i`. -/
theorem finite_projective_ker_d (i : ℤ) [Module.Projective A (LinearMap.range (C.d i).mulVecLin)] :
    Module.Finite A (LinearMap.ker (C.d i).mulVecLin) ∧
      Module.Projective A (LinearMap.ker (C.d i).mulVecLin) := by
  obtain ⟨hfin, hproj, -⟩ := finite_projective_ker_and_rankAtStalk_of_surjective
    (C.d i).mulVecLin.rangeRestrict (LinearMap.surjective_rangeRestrict _)
  rw [LinearMap.ker_rangeRestrict] at hfin hproj
  exact ⟨hfin, hproj⟩

/-- If the images of `d^i` and `d^{i+1}` are projective, the cohomology `H^{i+1}` has the
resolution `0 → im d^i → ker d^{i+1} → H^{i+1} → 0` by finite projective modules. -/
theorem exists_shortExact_homology_succ (i : ℤ)
    [Module.Projective A (LinearMap.range (C.d i).mulVecLin)]
    [Module.Projective A (LinearMap.range (C.d (i + 1)).mulVecLin)] :
    ∃ S : ShortComplex (ModuleCat.{u} A), S.ShortExact ∧
      Module.Finite A S.X₁ ∧ Module.Projective A S.X₁ ∧
      Module.Finite A S.X₂ ∧ Module.Projective A S.X₂ ∧
      Nonempty (S.X₃ ≅ C.toCochainComplex.homology (i + 1)) := by
  obtain ⟨hfin, hproj⟩ := C.finite_projective_ker_d (i + 1)
  let K := LinearMap.ker (C.d (i + 1)).mulVecLin
  let R : Submodule A K := (LinearMap.range (C.d i).mulVecLin).comap K.subtype
  let eR : R ≃ₗ[A] LinearMap.range (C.d i).mulVecLin :=
    Submodule.comapSubtypeEquivOfLe (C.range_d_le_ker_d i)
  let S : ShortComplex (ModuleCat.{u} A) :=
    ModuleCat.shortComplexOfCompEqZero R.subtype R.mkQ (by ext; simp)
  refine ⟨S, ModuleCat.shortComplex_shortExact S (LinearMap.exact_subtype_mkQ R)
    R.injective_subtype R.mkQ_surjective, Module.Finite.equiv eR.symm,
    Module.Projective.of_equiv eR.symm, hfin, hproj,
    ⟨(LinearEquiv.toModuleIso ((homologyEquivQuotientComap (C.shortComplexD i)).symm)) ≪≫
      (C.homologyIsoShortComplexD i).symm⟩⟩

/-- **Projective resolutions of the cohomology.** Let `C` be a bounded complex of finite free
modules, and suppose that for every `i` the `ρ_i × ρ_i` minors of the matrix of `d^i` generate the
ideal `(g_i)` of a nonzerodivisor `g_i` while its `(ρ_i + 1) × (ρ_i + 1)` minors vanish. Then every
cohomology module `H^i` has a resolution `0 → P₁ → P₀ → H^i → 0` by finite projective modules. -/
theorem exists_shortExact_homology_of_minorIdeal (ρ : ℤ → ℕ) (g : ℤ → A)
    (hg : ∀ i, IsRegular (g i)) (hρ : ∀ i, minorIdeal (C.d i) (ρ i) = Ideal.span {g i})
    (hρ' : ∀ i, minorIdeal (C.d i) (ρ i + 1) = ⊥) (i : ℤ) :
    ∃ S : ShortComplex (ModuleCat.{u} A), S.ShortExact ∧
      Module.Finite A S.X₁ ∧ Module.Projective A S.X₁ ∧
      Module.Finite A S.X₂ ∧ Module.Projective A S.X₂ ∧
      Nonempty (S.X₃ ≅ C.toCochainComplex.homology i) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by ring⟩
  have := C.projective_range_d_of_minorIdeal k (hg k) (hρ k) (hρ' k)
  have := C.projective_range_d_of_minorIdeal (k + 1) (hg (k + 1)) (hρ (k + 1)) (hρ' (k + 1))
  exact C.exists_shortExact_homology_succ k

end BoundedComplex

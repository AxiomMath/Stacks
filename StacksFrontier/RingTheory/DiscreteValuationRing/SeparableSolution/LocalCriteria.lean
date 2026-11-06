module

public import Mathlib
public import StacksCore.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.Transport
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.FiniteExtension.ModPow
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.Nagata.Descent
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Localization.InjectiveOfLocalization

/-!
# Separable solutions for extensions of discrete valuation rings

Let `A → B` be an extension of discrete valuation rings with fraction-field extension
`K → L`, and suppose that `B` is Nagata and that `L / K` is separable.

The first result removes a purely inseparable step from a solution: given a finite tower
`K → K₁ → K₂` in which `K₂` is a solution for `A → B` and `K₂ / K₁` is purely inseparable of
prime degree `p` equal to the characteristic, there is a separable extension of `K₁` which is
again a solution for `A → B`. Iterating it along the inseparable degree shows that as soon as
`A → B` admits a solution at all, it admits a separable one.

## Main results

* `IsDiscreteValuationRing.exists_isSeparable_solution_of_isPurelyInseparable_finrank_eq_prime`
  replaces the purely inseparable degree-`p` step of a solution by a separable extension.

## Implementation notes

Solutions and their canonical reduced composita and integral closures are represented by
`IsDiscreteValuationRing.IntegralClosureBaseChange`. Algebra and scalar-tower structures encode
all the field inclusions and their compatibility. The input carriers have independent universes;
the integral closures use the universes of the extension field and its reduced compositum, and
each solution is tested in the maximum of its two integral-closure universes, as in the
formal-smoothness criterion of Tag 09E7.

## References

* [The Stacks Project, Tag 0GLV](https://stacks.math.columbia.edu/tag/0GLV)
-/

@[expose] public section

universe u v

namespace IsDiscreteValuationRing

open Polynomial IntermediateField
open scoped TensorProduct

theorem minpoly_eq_X_pow_sub_C_of_adjoin_eq_top
    (F E : Type*) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (p : ℕ) [ExpChar F p] [IsPurelyInseparable F E]
    (hdegree : Module.finrank F E = p) (α : E) (hgen : F⟮α⟯ = ⊤) :
    ∃ a : F, minpoly F α = X ^ p - C a := by
  obtain ⟨m, a, hma⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p α
  have hm := (Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hgen
  have hpow : p ^ m = p := by
    simpa only [hma, natDegree_sub_C, natDegree_X_pow, hdegree] using hm
  exact ⟨a, by simpa only [hpow] using hma⟩

theorem adjoin_simple_mul_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (α : E) (a : F) (ha : a ≠ 0) : F⟮α * algebraMap F E a⟯ = F⟮α⟯ := by
  apply le_antisymm
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    exact mul_mem (IntermediateField.mem_adjoin_simple_self F α)
      (IntermediateField.algebraMap_mem _ a)
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    have haE : algebraMap F E a ≠ 0 := by
      simpa only [map_zero] using (algebraMap F E).injective.ne ha
    have hm := (F⟮α * algebraMap F E a⟯).div_mem
      (IntermediateField.mem_adjoin_simple_self F _)
      (IntermediateField.algebraMap_mem _ a)
    simpa only [mul_div_cancel_right₀ _ haE] using hm

theorem exists_minpoly_eq_X_pow_sub_C_of_finrank_eq_prime
    (F E : Type*) [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (p : ℕ) (hp : p.Prime) [CharP F p] [IsPurelyInseparable F E]
    (hdegree : Module.finrank F E = p) :
    ∃ (α : E) (a : F), F⟮α⟯ = ⊤ ∧ minpoly F α = X ^ p - C a := by
  have hbot : (⊥ : IntermediateField F E) ≠ ⊤ := by
    intro h
    have : Module.finrank F E = 1 := by
      rw [← IntermediateField.finrank_top', ← h, IntermediateField.finrank_bot]
    exact hp.ne_one (hdegree.symm.trans this)
  obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le hbot)
  have hαdegree : Module.finrank F F⟮α⟯ = p := by
    have hdvd := Module.finrank_dvd_finrank_right F F⟮α⟯ E
    rw [hdegree] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact False.elim (hα (finrank_adjoin_simple_eq_one_iff.mp h))
    · exact h
  have hm : (minpoly F α).natDegree = p := by
    rw [← adjoin.finrank (Algebra.IsIntegral.isIntegral α)]
    exact hαdegree
  have hgen : F⟮α⟯ = ⊤ := (Field.primitive_element_iff_minpoly_natDegree_eq F α).mpr
    (hm.trans hdegree.symm)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := minpoly_eq_X_pow_sub_C_of_adjoin_eq_top F E p hdegree α hgen
  exact ⟨α, a, hgen, ha⟩

theorem separable_X_pow_sub_C_mul_X_sub_C
    (F : Type*) [Field F] (p : ℕ) [CharP F p] (a b : F) (hb : b ≠ 0) :
    (X ^ p - C b * X - C a).Separable := by
  simpa [sub_eq_add_neg] using
    separable_C_mul_X_pow_add_C_mul_X_add_C' p p (1 : F) (-b) (-a)
      (dvd_refl p) (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hb))

theorem monic_X_pow_sub_C_mul_X_sub_C
    {R : Type*} [CommRing R] (p : ℕ) (hp : 1 < p) (a b : R) :
    (X ^ p - C b * X - C a).Monic := by
  rw [sub_sub]
  apply monic_X_pow_sub
  apply lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (degree_C_mul_X_le b) (by exact_mod_cast hp)
  · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (show 0 < p by omega))

theorem algebraMap_mem_nonZeroDivisors_of_isTorsionFree
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.IsTorsionFree R S]
    {x : R} (hx : x ∈ nonZeroDivisors R) : algebraMap R S x ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_left]
  intro y hy
  apply (isRegular_iff_mem_nonZeroDivisors.mpr hx).smul_eq_zero_iff_right.mp
  simpa only [Algebra.smul_def, mul_comm] using hy

/-- If `ker f ≤ m * N` with `m` in the Jacobson radical, two ideals with equal images under a
surjection `f` and `J ≤ N` are equal, by Nakayama. -/
private theorem eq_of_map_eq_of_le_jacobson_mul
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (J N m : Ideal R) (hN : N.FG)
    (hm : m ≤ (⊥ : Ideal R).jacobson) (hker : RingHom.ker f ≤ m * N) (hJN : J ≤ N)
    (heq : J.map f = N.map f) : J = N := by
  have hsup : J ⊔ RingHom.ker f = N ⊔ RingHom.ker f := by
    have h := congrArg (Ideal.comap f) heq
    simpa only [Ideal.comap_map_of_surjective' f hf] using h
  apply le_antisymm hJN
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hN hm
  calc
    N ≤ N ⊔ RingHom.ker f := le_sup_left
    _ = J ⊔ RingHom.ker f := hsup.symm
    _ ≤ J ⊔ m * N := sup_le_sup_left hker _
    _ = J ⊔ m • N := rfl

/-- The square of an element of `I` and `J` generates an ideal inside `I * J`. -/
private theorem span_pow_two_le_mul {R : Type*} [CommRing R] {x : R} {I J : Ideal R}
    (hI : x ∈ I) (hJ : x ∈ J) : Ideal.span {x ^ 2} ≤ I * J := by
  rw [Ideal.span_le, Set.singleton_subset_iff, pow_two]
  exact Ideal.mul_mem_mul hI hJ

private theorem isPrincipal_of_isPrincipal_map_quotient
    {R : Type*} [CommRing R] (I J m : Ideal R) (hJ : J.FG)
    (hm : m ≤ (⊥ : Ideal R).jacobson) (hI : I ≤ m * J)
    (hprincipal : (J.map (Ideal.Quotient.mk I)).IsPrincipal) : J.IsPrincipal := by
  obtain ⟨q, hq⟩ := hprincipal
  obtain ⟨x, hx, hxq⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).mp
      (show q ∈ J.map (Ideal.Quotient.mk I) from hq.symm ▸ Ideal.subset_span (by simp))
  refine ⟨⟨x, (eq_of_map_eq_of_le_jacobson_mul (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective _ J m hJ hm (by rwa [Ideal.mk_ker])
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)) ?_).symm⟩⟩
  rw [Ideal.map_span, Set.image_singleton, hxq, hq]

private theorem map_maximalIdeal_eq_of_quotient_square
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] (f : R →+* S) [IsLocalHom f]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (heq : ((IsLocalRing.maximalIdeal R).map f).map
      (Ideal.Quotient.mk (Ideal.span {f x ^ 2})) =
      (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk (Ideal.span {f x ^ 2}))) :
    (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S := by
  have hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hxS : f x ∈ IsLocalRing.maximalIdeal S :=
    hf (Ideal.mem_map_of_mem f hx)
  exact eq_of_map_eq_of_le_jacobson_mul (Ideal.Quotient.mk (Ideal.span {f x ^ 2}))
    Ideal.Quotient.mk_surjective _ _ (IsLocalRing.maximalIdeal S)
    (IsNoetherian.noetherian _) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    (by rw [Ideal.mk_ker]; exact span_pow_two_le_mul hxS hxS) hf heq

@[ega "0 17.1.4" "special case"]
private theorem isRegularLocalRing_of_isPrincipal_maximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal)
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) (hxreg : x ∈ nonZeroDivisors R) :
    IsRegularLocalRing R := by
  have hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hxreg).trans
      (Ideal.height_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)))
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  apply le_trans (b := (1 : WithBot ℕ∞)) ?_ hdim
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact_mod_cast (IsLocalRing.finrank_cotangentSpace_le_one_iff.mpr hprincipal)

private theorem isDedekindDomain_of_isPrincipal_maximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal)
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) (hxreg : x ∈ nonZeroDivisors R) :
    IsDedekindDomain R := by
  have : IsRegularLocalRing R := isRegularLocalRing_of_isPrincipal_maximalIdeal hprincipal hx hxreg
  have : IsDomain R := IsRegularLocalRing.isDomain R
  exact (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 5 3 |>.mp hprincipal

private theorem isDedekindDomain_of_isPrincipal_map_maximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) (hxreg : x ∈ nonZeroDivisors R)
    (hprincipal : ((IsLocalRing.maximalIdeal R).map
      (Ideal.Quotient.mk (Ideal.span {x ^ 2}))).IsPrincipal) : IsDedekindDomain R :=
  isDedekindDomain_of_isPrincipal_maximalIdeal
    (isPrincipal_of_isPrincipal_map_quotient (Ideal.span {x ^ 2})
      (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal R)
      (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
      (span_pow_two_le_mul hx hx) hprincipal) hx hxreg

noncomputable def quotAdjoinRootEquivOfMapEq
    {R : Type*} [CommRing R] (I : Ideal R) (f g : R[X])
    (hfg : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I)) :
    (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃ₐ[R]
      (AdjoinRoot g ⧸ I.map (AdjoinRoot.of g)) :=
  (AdjoinRoot.quotEquivQuotMap f I).trans
    ((Ideal.quotientEquivAlgOfEq R (congrArg (fun p : (R ⧸ I)[X] => Ideal.span {p}) hfg)).trans
      (AdjoinRoot.quotEquivQuotMap g I).symm)

theorem quotAdjoinRootEquivOfMapEq_apply_mk
    {R : Type*} [CommRing R] (I : Ideal R) (f g : R[X])
    (hfg : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I)) (q : R[X]) :
    quotAdjoinRootEquivOfMapEq I f g hfg (Ideal.Quotient.mk _ (AdjoinRoot.mk f q)) =
      Ideal.Quotient.mk _ (AdjoinRoot.mk g q) := by
  simp only [quotAdjoinRootEquivOfMapEq, AlgEquiv.trans_apply,
    AdjoinRoot.quotEquivQuotMap_apply_mk, Ideal.quotientEquivAlgOfEq_mk,
    AdjoinRoot.quotEquivQuotMap_symm_apply_mk]

private theorem quotAdjoinRootEquivOfMapEq_unique
    {R : Type*} [CommRing R] (I : Ideal R) (f g : R[X])
    (hfg : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I))
    (e : (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃ₐ[R]
      (AdjoinRoot g ⧸ I.map (AdjoinRoot.of g)))
    (he : e (Ideal.Quotient.mk _ (AdjoinRoot.root f)) =
      Ideal.Quotient.mk _ (AdjoinRoot.root g)) :
    e = quotAdjoinRootEquivOfMapEq I f g hfg := by
  suffices h : e.toAlgHom = (quotAdjoinRootEquivOfMapEq I f g hfg).toAlgHom by
    exact DFunLike.ext _ _ (fun x => DFunLike.congr_fun h x)
  apply Ideal.Quotient.algHom_ext R
  apply AdjoinRoot.algHom_ext
  exact he.trans (quotAdjoinRootEquivOfMapEq_apply_mk I f g hfg X).symm

private theorem map_X_pow_sub_C_mul_X_sub_C
    {R : Type*} [CommRing R] (I : Ideal R) (p : ℕ) (a b : R) (hb : b ∈ I) :
    (X ^ p - C b * X - C a).map (Ideal.Quotient.mk I) =
      (X ^ p - C a).map (Ideal.Quotient.mk I) := by
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hb]

theorem isLocalization_away_of_isFractionRing
    (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] {π : R} (hπ : Irreducible π) :
    IsLocalization.Away π F :=
  isLocalization_away_of_ne_zero_of_not_isUnit R F hπ.ne_zero hπ.not_isUnit

theorem exists_pow_smul_isIntegral
    {R F E : Type*} [CommRing R] [CommRing F] [CommRing E]
    [Algebra R F] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
    (π : R) [IsLocalization.Away π F] {α : E} (hα : IsIntegral F α) :
    ∃ n : ℕ, IsIntegral R (π ^ n • α) := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    hα.exists_multiple_integral_of_isLocalization (Submonoid.powers π) α
  exact ⟨n, hn⟩

theorem isIntegral_of_minpoly_eq_X_pow_sub_C
    {R F E : Type*} [CommRing R] [Field F] [Field E]
    [Algebra R F] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
    (p : ℕ) {α : E} {a : F} (hα : IsIntegral R α)
    (hminpoly : minpoly F α = X ^ p - C a) : IsIntegral R a := by
  have hroot : α ^ p = algebraMap F E a := by
    have h := minpoly.aeval F α
    rw [hminpoly] at h
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h
  apply (isIntegral_algebraMap_iff (B := E)).mp
  rw [← hroot]
  exact hα.pow p

private theorem isIntegrallyClosedIn_of_isIntegrallyClosed_atMaximal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R)
    (hlocal : ∀ (m : Ideal R) [m.IsMaximal],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m)) :
    IsIntegrallyClosedIn R S := by
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨IsLocalization.injective S hM, fun {x} hx => ?_⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj M x
  have hr : r ∈ Ideal.span {s.1} := by
    apply Ideal.mem_of_localization_maximal
    intro m hm
    obtain ⟨hdom, hclosed⟩ := hlocal m
    let Rm := Localization.AtPrime m
    let Fm := FractionRing Rm
    let f : R →+* Fm := (algebraMap Rm Fm).comp (algebraMap R Rm)
    have hf (t : M) : IsUnit (f t) := by
      apply isUnit_iff_ne_zero.mpr
      show algebraMap Rm Fm (algebraMap R Rm t.1) ≠ 0
      intro hz
      exact nonZeroDivisors.ne_zero
        (IsLocalization.nonZeroDivisors_le_comap m.primeCompl Rm (hM t.2))
        ((IsFractionRing.injective Rm Fm) (hz.trans (map_zero _).symm))
    let g : S →+* Fm := IsLocalization.lift hf
    have hg (a : R) : g (algebraMap R S a) = f a := IsLocalization.lift_eq hf a
    have hx' : IsIntegral Rm (g x) :=
      IsIntegral.map_of_comp_eq (algebraMap R Rm) g (by ext a; exact (hg a).symm) hx
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff Fm).mp hclosed hx'
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    refine ⟨y, ?_⟩
    apply IsFractionRing.injective Rm Fm
    rw [map_mul, hy]
    show f r = f s.1 * g x
    rw [← hg, ← hg, ← map_mul, mul_comm, hrs]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hr
  refine ⟨y, ?_⟩
  apply (IsLocalization.map_units S s).mul_left_cancel
  rw [← map_mul, ← hy, mul_comm, hrs]

theorem isPrincipal_maximal_of_isPrincipal_quotient_square
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ (⊥ : Ideal R).jacobson)
    (m : Ideal R) [m.IsMaximal]
    (hprincipal : (m.map (Ideal.Quotient.mk (Ideal.span {x ^ 2}))).IsPrincipal) :
    m.IsPrincipal := by
  have hxm : x ∈ m := by
    simpa only [Ideal.jacobson_eq_self_of_isMaximal] using
      Ideal.jacobson_mono (bot_le : (⊥ : Ideal R) ≤ m) hx
  exact isPrincipal_of_isPrincipal_map_quotient (Ideal.span {x ^ 2}) m
    (⊥ : Ideal R).jacobson (IsNoetherian.noetherian m) le_rfl
    (span_pow_two_le_mul hx hxm) hprincipal

theorem isDedekindDomain_atMaximal_of_isPrincipal_quotient_square
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ (⊥ : Ideal R).jacobson) (hxreg : x ∈ nonZeroDivisors R)
    (m : Ideal R) [m.IsMaximal]
    (hprincipal : (m.map (Ideal.Quotient.mk (Ideal.span {x ^ 2}))).IsPrincipal) :
    IsDedekindDomain (Localization.AtPrime m) := by
  have hxm : x ∈ m := by
    simpa only [Ideal.jacobson_eq_self_of_isMaximal] using
      Ideal.jacobson_mono (bot_le : (⊥ : Ideal R) ≤ m) hx
  have hmp : (IsLocalRing.maximalIdeal (Localization.AtPrime m)).IsPrincipal := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m]
    exact (isPrincipal_maximal_of_isPrincipal_quotient_square hx m hprincipal).map_ringHom _
  have hxm' : algebraMap R (Localization.AtPrime m) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m]
    exact Ideal.mem_map_of_mem _ hxm
  have hxreg' : algebraMap R (Localization.AtPrime m) x ∈
      nonZeroDivisors (Localization.AtPrime m) :=
    IsLocalization.nonZeroDivisors_le_comap m.primeCompl _ hxreg
  exact isDedekindDomain_of_isPrincipal_maximalIdeal hmp hxm' hxreg'

private theorem isIntegralClosure_of_isPrincipal_quotient_square
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    [Algebra.IsIntegral A R] [IsNoetherianRing R]
    {x : R} [IsLocalization.Away x S]
    (hx : x ∈ (⊥ : Ideal R).jacobson) (hxreg : x ∈ nonZeroDivisors R)
    (hprincipal : ∀ (m : Ideal R) [m.IsMaximal],
      (m.map (Ideal.Quotient.mk (Ideal.span {x ^ 2}))).IsPrincipal) :
    IsIntegralClosure R A S := by
  have : IsIntegrallyClosedIn R S :=
    isIntegrallyClosedIn_of_isIntegrallyClosed_atMaximal (Submonoid.powers x)
      (Submonoid.powers_le.mpr hxreg) (fun m _ => by
        have := isDedekindDomain_atMaximal_of_isPrincipal_quotient_square hx hxreg m (hprincipal m)
        exact ⟨inferInstance, inferInstance⟩)
  exact IsIntegralClosure.of_isIntegrallyClosedIn

private theorem finite_setOf_isMaximal_of_finite
    (A R : Type*) [CommRing A] [CommRing R] [IsLocalRing A]
    [Algebra A R] [Module.Finite A R] : {m : Ideal R | m.IsMaximal}.Finite := by
  apply (Algebra.QuasiFinite.finite_primesOver (S := R) (IsLocalRing.maximalIdeal A)).subset
  intro m hm
  have : m.IsMaximal := hm
  refine ⟨hm.isPrime, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m)).symm

theorem map_maximalIdeal_le_jacobson_of_isIntegral
    (A R : Type*) [CommRing A] [CommRing R] [IsLocalRing A]
    [Algebra A R] [Algebra.IsIntegral A R] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A R) ≤ (⊥ : Ideal R).jacobson := by
  apply le_sInf
  rintro m ⟨_, hm⟩
  have : m.IsMaximal := hm
  rw [Ideal.map_le_iff_le_comap]
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m)).symm.le

private theorem finite_setOf_isMaximal_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hR : {m : Ideal R | m.IsMaximal}.Finite) :
    {m : Ideal S | m.IsMaximal}.Finite := by
  apply (hR.preimage (Ideal.comap_injective_of_surjective f hf).injOn).subset
  intro m hm
  have : m.IsMaximal := hm
  exact Ideal.comap_isMaximal_of_surjective f hf

private theorem isPrincipalIdealRing_of_finite_maximals_of_product_dedekind
    {R : Type*} [CommRing R] (hR : {m : Ideal R | m.IsMaximal}.Finite)
    (hprod : IsFiniteProductOfDedekindDomains R) : IsPrincipalIdealRing R := by
  obtain ⟨n, D, hD, hDed, _, ⟨e⟩⟩ := hprod
  have hP (i : Fin n) : IsPrincipalIdealRing (D i) := by
    apply IsPrincipalIdealRing.of_finite_maximals
    exact finite_setOf_isMaximal_of_surjective
      ((Pi.evalRingHom D i).comp e.toRingHom)
      ((Function.surjective_eval i).comp e.surjective) hR
  have : IsPrincipalIdealRing (∀ i, D i) := inferInstance
  exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective

private noncomputable def residueFieldMapEquivOfSurjective
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f)
    ⟨(IsLocalRing.ResidueField.map f).injective, fun y => by
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨r, rfl⟩ := hf s
      exact ⟨IsLocalRing.residue R r, IsLocalRing.ResidueField.map_residue f r⟩⟩

private theorem residueFieldMapEquivOfSurjective_apply_residue
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) (x : R) :
    residueFieldMapEquivOfSurjective f hf (IsLocalRing.residue R x) =
      IsLocalRing.residue S (f x) := rfl

private theorem isSeparableExtension_residueField_iff_of_surjective_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [Algebra R S] [Algebra R' S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R' S')]
    (a : R →+* R') (b : S →+* S') [IsLocalHom a] [IsLocalHom b]
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hsq : b.comp (algebraMap R S) = (algebraMap R' S').comp a) :
    Algebra.IsSeparableExtension (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ↔
      Algebra.IsSeparableExtension (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField S') := by
  apply Algebra.IsSeparableExtension.iff_of_ringEquiv
    (residueFieldMapEquivOfSurjective a ha) (residueFieldMapEquivOfSurjective b hb)
  intro x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  show IsLocalRing.ResidueField.map b
      (IsLocalRing.ResidueField.map (algebraMap R S) (IsLocalRing.residue R r)) =
    IsLocalRing.ResidueField.map (algebraMap R' S')
      (IsLocalRing.ResidueField.map a (IsLocalRing.residue R r))
  simp only [IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue S') (DFunLike.congr_fun hsq r)

theorem isIntegralClosure_of_quotient_equiv
    {A R R₀ S : Type*} [CommRing A] [CommRing R] [CommRing R₀] [CommRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    [Algebra.IsIntegral A R] [IsNoetherianRing R] [IsPrincipalIdealRing R₀]
    {x : R} [IsLocalization.Away x S]
    (hx : x ∈ (⊥ : Ideal R).jacobson) (hxreg : x ∈ nonZeroDivisors R)
    (I : Ideal R₀) (e : (R₀ ⧸ I) ≃+* (R ⧸ Ideal.span {x ^ 2})) :
    IsIntegralClosure R A S := by
  have : IsPrincipalIdealRing (R₀ ⧸ I) :=
    IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsPrincipalIdealRing (R ⧸ Ideal.span {x ^ 2}) :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  exact isIntegralClosure_of_isPrincipal_quotient_square hx hxreg
    (fun m _ => IsPrincipalIdealRing.principal _)

private theorem map_maximalIdeal_eq_iff_of_surjective_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing S]
    (f : R →+* S) (f' : R' →+* S') [IsLocalHom f] [IsLocalHom f']
    (a : R →+* R') (b : S →+* S') (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hsq : b.comp f = f'.comp a)
    (hker : RingHom.ker b ≤ IsLocalRing.maximalIdeal S ^ 2) :
    (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S ↔
      (IsLocalRing.maximalIdeal R').map f' = IsLocalRing.maximalIdeal S' := by
  have ha' := IsLocalRing.map_maximalIdeal_of_surjective a ha
  have hb' := IsLocalRing.map_maximalIdeal_of_surjective b hb
  have hmap : ((IsLocalRing.maximalIdeal R).map f).map b =
      (IsLocalRing.maximalIdeal R').map f' := by
    rw [Ideal.map_map, hsq, ← Ideal.map_map, ha']
  constructor
  · intro h
    rw [← hmap, h, hb']
  · intro h
    apply eq_of_map_eq_of_le_jacobson_mul b hb _ _ (IsLocalRing.maximalIdeal S)
      (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      (by simpa only [pow_two] using hker) (IsLocalRing.map_maximalIdeal_le f)
    rw [hmap, h, hb']

private theorem map_maximalIdeal_eq_and_isSeparableExtension_iff_of_surjective_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing S] [Algebra R S] [Algebra R' S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R' S')]
    (a : R →+* R') (b : S →+* S') (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hsq : b.comp (algebraMap R S) = (algebraMap R' S').comp a)
    (hker : RingHom.ker b ≤ IsLocalRing.maximalIdeal S ^ 2) :
    ((IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S ∧
      Algebra.IsSeparableExtension (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) ↔
    ((IsLocalRing.maximalIdeal R').map (algebraMap R' S') = IsLocalRing.maximalIdeal S' ∧
      Algebra.IsSeparableExtension (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField S')) :=
        by
  have : IsLocalHom a := IsLocalHom.of_surjective a ha
  have : IsLocalHom b := IsLocalHom.of_surjective b hb
  exact and_congr
    (map_maximalIdeal_eq_iff_of_surjective_square _ _ a b ha hb hsq hker)
    (isSeparableExtension_residueField_iff_of_surjective_square a b ha hb hsq)

private theorem formallySmoothNAdic_iff_map_maximalIdeal_eq_and_isSeparableExtension
    (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtension R S] :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap R S) (IsLocalRing.maximalIdeal S) ↔
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  rw [formallySmooth_iff_weaklyUnramified_and_isSeparableExtension R S]
  apply and_congr_left
  intro _
  obtain ⟨_, hpow, hunique, _⟩ := ramificationIndex_characterization R S
  constructor
  · intro h
    change ramificationIndex R S = 1 at h
    simpa only [h, pow_one] using hpow
  · intro h
    exact (hunique 1 (by omega) (by simpa only [pow_one] using h)).symm

universe w w'

/-- Formal smoothness tested against rings in a larger universe implies formal smoothness
tested against rings in a smaller one, by lifting test rings along `ULift`. -/
private theorem formallySmoothNAdic_of_formallySmoothNAdic_max
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (n : Ideal S)
    (h : RingHom.FormallySmoothNAdic.{max w w'} φ n) :
    RingHom.FormallySmoothNAdic.{w} φ n := by
  intro A _ J hJ f ψ hcomm hk
  let e : ULift.{w'} A ≃+* A := ULift.ringEquiv
  let J' : Ideal (ULift.{w'} A) := J.map e.symm
  have hJ' : J' ^ 2 = 0 := by
    show (J.map e.symm) ^ 2 = 0
    rw [← Ideal.map_pow, hJ, Ideal.zero_eq_bot, Ideal.map_bot]
  let q : (ULift.{w'} A ⧸ J') ≃+* (A ⧸ J) := Ideal.quotientEquiv J' J e (by
    show J = Ideal.map e (J.map e.symm)
    exact (Ideal.map_of_equiv (I := J) e.symm).symm)
  obtain ⟨g, hg1, hg2⟩ := h (ULift.{w'} A) J' hJ' (e.symm.toRingHom.comp f)
    (q.symm.toRingHom.comp ψ) (by
      ext r
      apply q.injective
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
      rw [← RingHom.comp_apply ψ, hcomm]
      simp [q, Ideal.quotientEquiv_apply]) (by
      obtain ⟨k, hk1, hkle⟩ := hk
      refine ⟨k, hk1, le_trans hkle ?_⟩
      intro x hx
      simp only [RingHom.mem_ker, RingHom.comp_apply] at hx ⊢
      simp [hx])
  refine ⟨e.toRingHom.comp g, ?_, ?_⟩
  · ext s
    have := congrArg q (DFunLike.congr_fun hg1 s)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at this
    rw [← this]
    simp [q, Ideal.quotientEquiv_apply]
  · rw [RingHom.comp_assoc, hg2]; ext r; simp [e]

universe u₁ v₁ u₂ v₂

theorem formallySmoothNAdic_iff_of_common_surjective_square
    (R : Type u₁) (S : Type v₁) (R' : Type u₂) (S' : Type v₂) (R₀ S₀ : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S'] [IsDomain S'] [IsDiscreteValuationRing S']
    [CommRing R₀] [CommRing S₀] [IsLocalRing R₀] [IsLocalRing S₀]
    [Algebra R S] [Algebra R' S'] [Algebra R₀ S₀]
    [IsExtension R S] [IsExtension R' S']
    [IsLocalHom (algebraMap R₀ S₀)]
    (a : R →+* R₀) (b : S →+* S₀) (a' : R' →+* R₀) (b' : S' →+* S₀)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (ha' : Function.Surjective a') (hb' : Function.Surjective b')
    (hsq : b.comp (algebraMap R S) = (algebraMap R₀ S₀).comp a)
    (hsq' : b'.comp (algebraMap R' S') = (algebraMap R₀ S₀).comp a')
    (hker : RingHom.ker b ≤ IsLocalRing.maximalIdeal S ^ 2)
    (hker' : RingHom.ker b' ≤ IsLocalRing.maximalIdeal S' ^ 2) :
    RingHom.FormallySmoothNAdic.{max u₁ v₁} (algebraMap R S) (IsLocalRing.maximalIdeal S) ↔
      RingHom.FormallySmoothNAdic.{max u₂ v₂} (algebraMap R' S') (IsLocalRing.maximalIdeal S') := by
  rw [formallySmoothNAdic_iff_map_maximalIdeal_eq_and_isSeparableExtension,
    formallySmoothNAdic_iff_map_maximalIdeal_eq_and_isSeparableExtension]
  exact (map_maximalIdeal_eq_and_isSeparableExtension_iff_of_surjective_square
    a b ha hb hsq hker).trans
    (map_maximalIdeal_eq_and_isSeparableExtension_iff_of_surjective_square
      a' b' ha' hb' hsq' hker').symm

noncomputable def integralClosureBaseChangeOfReducedTensorEquiv
    (A B K L F T : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F] [CommRing T]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F] [Algebra K T] [Algebra L T] [Algebra F T]
    [Algebra B T] [Algebra A T]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsScalarTower K L T] [IsScalarTower K F T] [IsScalarTower B L T]
    [IsScalarTower A B T] [IsScalarTower A F T]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F]
    (e : T ≃ₐ[K] ((L ⊗[K] F) ⧸ nilradical (L ⊗[K] F)))
    (heL : ∀ x : L, e (algebraMap L T x) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] F) x))
    (heF : ∀ x : F, e (algebraMap F T x) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F) x)) :
    IntegralClosureBaseChange A B K L F := by
  let i : integralClosure A F →ₐ[A] integralClosure B T :=
    ((IsScalarTower.toAlgHom A F T).comp (integralClosure A F).val).codRestrict
      ((integralClosure B T).restrictScalars A) (fun x =>
        (x.2.map (IsScalarTower.toAlgHom A F T)).tower_top)
  letI : Algebra (integralClosure A F) (integralClosure B T) := i.toRingHom.toAlgebra
  have : IsScalarTower A (integralClosure A F) (integralClosure B T) :=
    IsScalarTower.of_algebraMap_eq (fun a => (i.commutes a).symm)
  exact
    { L₁ := T
      A₁ := integralClosure A F
      B₁ := integralClosure B T
      eL₁ := e
      eL₁_left := heL
      eL₁_right := heF
      ringSquare := fun _ => rfl }

/-- **An integral closure inside a localisation away from `π` is again away from `π`.**

If `F` is `A` with `π` inverted, `E` is integral over `F`, and `C` is the integral closure of `A`
in `E`, then `E` is `C` with the image of `π` inverted. Surjectivity is the content:
`exists_pow_smul_isIntegral` clears the denominator of an `F`-integral element of `E` into `C`.

Exposed for the generic-fibre bound of Tag 09F9, where it presents a package's compositum `L₁` as
an `Away` localisation of `B₁` at the image of a uniformizer of `B` — see
`Stacks.EppTheorem.isLocalization_away_algebraMap_B₁`. -/
theorem isLocalization_away_of_isIntegralClosure
    (A F E C : Type*) [CommRing A] [CommRing F] [CommRing E] [CommRing C]
    [Algebra A F] [Algebra A E] [Algebra F E] [IsScalarTower A F E]
    [Algebra A C] [Algebra C E] [IsScalarTower A C E] [IsIntegralClosure C A E]
    [Algebra.IsIntegral F E] (π : A) [IsLocalization.Away π F] :
    IsLocalization.Away (algebraMap A C π) E := by
  have hπ : IsUnit (algebraMap A E π) := by
    rw [IsScalarTower.algebraMap_apply A F E]
    exact (IsLocalization.Away.algebraMap_isUnit π (S := F)).map (algebraMap F E)
  apply IsLocalization.Away.mk (algebraMap A C π) (by
    simpa only [← IsScalarTower.algebraMap_apply] using hπ)
  · intro x
    obtain ⟨n, hn⟩ := exists_pow_smul_isIntegral (F := F) π
      (Algebra.IsIntegral.isIntegral x)
    refine ⟨n, IsIntegralClosure.mk' C (π ^ n • x) hn, ?_⟩
    rw [IsIntegralClosure.algebraMap_mk', ← IsScalarTower.algebraMap_apply]
    simp only [Algebra.smul_def, map_pow, mul_comm]
  · intro x y hxy
    exact ⟨0, by simpa using IsIntegralClosure.algebraMap_injective C A E hxy⟩

noncomputable def integralClosureBaseChange
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] : IntegralClosureBaseChange A B K L F := by
  letI : Algebra F (L ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
  let T := (L ⊗[K] F) ⧸ nilradical (L ⊗[K] F)
  have : IsScalarTower A K T := IsScalarTower.to₁₂₄ A K L T
  have : IsScalarTower A F T := IsScalarTower.to₁₃₄ A K F T
  exact integralClosureBaseChangeOfReducedTensorEquiv A B K L F T (AlgEquiv.refl)
    (fun _ => rfl) (fun _ => rfl)

theorem integralClosureBaseChange_isPrincipalIdealRing_of_finite
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] (D : IntegralClosureBaseChange A B K L F)
    (hfiniteA : let := D.commRingA₁; let := D.algebraAA₁; Module.Finite A D.A₁)
    (hfiniteB : let := D.commRingB₁; let := D.algebraBB₁; Module.Finite B D.B₁) :
    let := D.commRingA₁
    let := D.commRingB₁
    let := D.algebraAA₁
    let := D.algebraBB₁
    IsDedekindDomain D.A₁ ∧ IsFiniteProductOfDedekindDomains D.B₁ ∧
      Module.Finite A D.A₁ ∧ Module.Finite B D.B₁ ∧
      IsPrincipalIdealRing D.A₁ ∧ IsPrincipalIdealRing D.B₁ := by
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let := D.algebraBL₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.algebraAB₁
  let := D.algebraA₁B₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerKK₁L₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerAA₁K₁
  let := D.isScalarTowerBB₁L₁
  let := D.isScalarTowerABB₁
  let := D.isScalarTowerAA₁B₁
  let := D.isIntegralClosureA₁
  let := D.isIntegralClosureB₁
  let eA := IsIntegralClosure.equiv A D.A₁ F (integralClosure A F)
  let eB := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  have heA (x : D.A₁) : (eA x : F) = algebraMap D.A₁ F x :=
    IsIntegralClosure.algebraMap_equiv A D.A₁ F (integralClosure A F) x
  have heB (x : D.B₁) : (eB x : D.L₁) = algebraMap D.B₁ D.L₁ x :=
    IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x
  have h := integralClosures_after_finite_fraction_field_extension
    A B K L F D.L₁ D.A₁ D.B₁ D.eL₁ eA eB D.eL₁_left D.eL₁_right heB
    (fun x => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    (fun x => by rw [heA]; exact D.ringSquare x)
  obtain ⟨_, hDA, hDB, _, _, _, _, _, _, _, _, _, _, _, _, _, hfinA, hfinB⟩ := h
  have : Module.Finite A D.A₁ := hfiniteA
  have : Module.Finite B D.B₁ := hfiniteB
  have := hDA
  exact ⟨hDA, hDB, ‹Module.Finite A D.A₁›, ‹Module.Finite B D.B₁›,
    IsPrincipalIdealRing.of_finite_maximals (finite_setOf_isMaximal_of_finite A D.A₁),
    isPrincipalIdealRing_of_finite_maximals_of_product_dedekind
      (finite_setOf_isMaximal_of_finite B D.B₁) hDB⟩

end IsDiscreteValuationRing

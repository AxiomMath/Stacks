module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Blowup.Affine
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksCore.Tactic.StacksAttribute

/-!
# Formal arcs: the generic kernel

The sequence of blowups along a formal arc, regularity of stalks at the kernel prime, and
generators of the kernel at the generic point of the arc together with the power relations
they satisfy.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

universe u

/-- The successive blowups at the centers of a formal arc, together with the
compatible lifted arcs. -/
structure ArcBlowupSequence (A R : Type u) [CommRing A] [CommRing R]
    [IsLocalRing R] (f : A →+* R) where
  scheme : ℕ → Scheme.{u}
  arc : ∀ i, Spec (.of R) ⟶ scheme i
  base : scheme 0 ≅ Spec (.of A)
  base_arc : arc 0 ≫ base.hom = Spec.map (CommRingCat.ofHom f)
  center_closed (i : ℕ) : IsClosed ({arc i (closedPoint R)} : Set (scheme i))
  step (i : ℕ) : scheme (i + 1) ⟶ scheme i
  step_arc (i : ℕ) : arc (i + 1) ≫ step i = arc i
  step_blowup (i : ℕ) :
    ∃ e : scheme (i + 1) ≅
      blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨{arc i (closedPoint R)}, center_closed i⟩ : Closeds (scheme i))),
      e.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{arc i (closedPoint R)}, center_closed i⟩ : Closeds (scheme i))) =
        step i

/-- The underlying open of an element of `AlgebraicGeometry.Scheme.affineOpens` is affine. -/
theorem isAffineOpen_coe {X : Scheme.{u}} (U : X.affineOpens) : IsAffineOpen U.1 := U.2

/-- Regularity of a scheme stalk transfers along an isomorphism of schemes. -/
theorem regular_stalk_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X)
    (h : IsRegularLocalRing (Y.presheaf.stalk (e.hom x))) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  have := h
  .of_ringEquiv (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

/-- The stalk of an affine scheme at a prime is regular exactly when the localization at that
prime is. -/
private theorem regular_stalk_iff_localization {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) [p.asIdeal.IsPrime] :
    IsRegularLocalRing ((Spec (.of A)).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  let e := (Spec.stalkIso (.of A) p).commRingCatIsoToRingEquiv
  exact ⟨fun h => have := h; .of_ringEquiv e, fun h => have := h; .of_ringEquiv e.symm⟩

/-- The image of the generic point of `Spec R` under `Spec f` is the kernel prime of `f`. -/
private theorem map_genericPoint_eq_ker {A R : Type u} [CommRing A] [CommRing R]
    [IsDomain R] (f : A →+* R) :
    Spec.map (CommRingCat.ofHom f) (genericPoint (Spec (.of R))) =
      ⟨RingHom.ker f, RingHom.ker_isPrime f⟩ := by
  apply PrimeSpectrum.ext
  show (PrimeSpectrum.comap f (genericPoint (Spec (.of R)))).asIdeal = RingHom.ker f
  rw [genericPoint_eq_bot_of_affine]
  rfl

/-- The generic point of the target arc maps to the kernel prime, whose scheme stalk is
the localization of the original ring at that prime. -/
private theorem regular_generic_stalk_iff_localization_at_ker
    {A R : Type u} [CommRing A] [CommRing R] [IsDomain R]
    (f : A →+* R) :
    IsRegularLocalRing ((Spec (.of A)).presheaf.stalk
      (Spec.map (CommRingCat.ofHom f) (genericPoint (Spec (.of R))))) ↔
      (letI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f;
        IsRegularLocalRing (Localization.AtPrime (RingHom.ker f))) := by
  rw [map_genericPoint_eq_ker f]
  exact @regular_stalk_iff_localization _ _ ⟨_, RingHom.ker_isPrime f⟩ (RingHom.ker_isPrime f)

/-- At step zero of an arc blowup sequence, regularity of the localization at the kernel gives
regularity of the stalk at the arc centre's generic point. -/
private theorem regular_generic_stalk_first
    {A R : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : A →+* R)
    (hkernel : letI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
      IsRegularLocalRing (Localization.AtPrime (RingHom.ker f)))
    (s : ArcBlowupSequence A R f) :
    IsRegularLocalRing ((s.scheme 0).presheaf.stalk
      (s.arc 0 (genericPoint (Spec (.of R))))) := by
  have hgeneric : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk
      (Spec.map (CommRingCat.ofHom f) (genericPoint (Spec (.of R))))) :=
    (regular_generic_stalk_iff_localization_at_ker f).mpr hkernel
  have hpoint : s.base.hom (s.arc 0 (genericPoint (Spec (.of R)))) =
      Spec.map (CommRingCat.ofHom f) (genericPoint (Spec (.of R))) :=
    congrArg (fun g : Spec (.of R) ⟶ Spec (.of A) => g (genericPoint (Spec (.of R)))) s.base_arc
  exact regular_stalk_of_iso s.base _ (hpoint ▸ hgeneric)

/-- Regularity of the stalk of `Spec A` at the kernel prime is regularity of the localization
of `A` at that prime. -/
private theorem regular_localization_at_kernel
    {A R : Type u} [CommRing A] [CommRing R] [IsDomain R]
    (f : A →+* R)
    (hgeneric : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk
      (Spec.map (CommRingCat.ofHom f) (genericPoint (Spec (.of R)))))) :
    (letI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f;
      IsRegularLocalRing (Localization.AtPrime (RingHom.ker f))) :=
  (regular_generic_stalk_iff_localization_at_ker f).mp hgeneric

/-- A nonzero, nonmaximal prime of a two-dimensional Noetherian local domain has height
one. For a surjection to a DVR, the kernel is such a prime. -/
private theorem ker_height_eq_one_of_dim_two_surjective_dvr
    {A R : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsDiscreteValuationRing R]
    (hA : ringKrullDim A = 2) (f : A →+* R) (hf : Function.Surjective f) :
    (RingHom.ker f).height = 1 := by
  let p : Ideal A := RingHom.ker f
  have hp : p.IsPrime := RingHom.ker_isPrime f
  let := hp
  have hpnebot : p ≠ ⊥ := by
    intro h
    have hinj : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).mpr h
    have hdim := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective f ⟨hinj, hf⟩)
    rw [hA, IsDiscreteValuationRing.ringKrullDim_eq_one R] at hdim
    norm_num at hdim
  have hpnemax : p ≠ maximalIdeal A := by
    intro h
    have hmap : (maximalIdeal A).map f = maximalIdeal R :=
      IsLocalRing.map_maximalIdeal_of_surjective f hf
    rw [← h, (Ideal.map_eq_bot_iff_le_ker f).2 le_rfl] at hmap
    exact IsDiscreteValuationRing.not_a_field R hmap.symm
  have hp_lt_max : p < maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p) hpnemax
  have hpheight_lt : p.height < 2 := by
    have hlt' : (p.height : WithBot ℕ∞) < ringKrullDim A := by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)]
      exact_mod_cast Ideal.height_strict_mono_of_isPrime hp_lt_max
    rw [hA] at hlt'
    exact WithBot.coe_lt_coe.mp hlt'
  exact le_antisymm (ENat.lt_two_iff.mp hpheight_lt)
    (Order.one_le_iff_ne_zero.mpr fun h => hpnebot (Ideal.height_eq_zero_iff_eq_bot.mp h))

/-- Regularity of the generic stalk makes the kernel principal after localizing at itself.
In dimension two, the kernel prime has height one. -/
private theorem exists_generator_of_regular_generic_kernel
    {A R : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsDiscreteValuationRing R]
    (hA : ringKrullDim A = 2) (f : A →+* R) (hf : Function.Surjective f)
    (hgeneric : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk
      (Spec.map (CommRingCat.ofHom f) (genericPoint (Spec (.of R)))))) :
    letI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    ∃ x₂ : A, x₂ ∈ RingHom.ker f ∧
      (RingHom.ker f).map (algebraMap A (Localization.AtPrime (RingHom.ker f))) =
        Ideal.span {algebraMap A (Localization.AtPrime (RingHom.ker f)) x₂} := by
  let p : Ideal A := RingHom.ker f
  let : p.IsPrime := RingHom.ker_isPrime f
  let L := Localization.AtPrime p
  have hpheight := ker_height_eq_one_of_dim_two_surjective_dvr hA f hf
  have hdim : ringKrullDim L = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p L, hpheight]
    rfl
  have hfin : (maximalIdeal L).spanFinrank = 1 := by
    have h := (isRegularLocalRing_iff L).mp (regular_localization_at_kernel f hgeneric)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨b, hb⟩ := ((Submodule.spanFinrank_eq_one_iff (maximalIdeal L)).mp hfin).1
  have hmap : p.map (algebraMap A L) = maximalIdeal L :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p L
  obtain ⟨a, s, has⟩ := IsLocalization.exists_mk'_eq p.primeCompl b
  have hmem : (IsLocalization.mk' L a s : L) ∈ p.map (algebraMap A L) := by
    rw [has, hmap, hb]
    exact Ideal.subset_span (Set.mem_singleton b)
  obtain ⟨t, ht, hta⟩ :=
    (IsLocalization.mk'_mem_map_algebraMap_iff p.primeCompl L p a s).mp hmem
  have hspan : Ideal.span {algebraMap A L a} = Ideal.span {(IsLocalization.mk' L a s : L)} := by
    rw [← IsLocalization.mk'_spec L a s]
    exact Ideal.span_singleton_mul_right_unit (IsLocalization.map_units L s) _
  exact ⟨a, (Ideal.IsPrime.mem_or_mem inferInstance hta).resolve_left ht,
    by rw [hmap, hb, hspan, has]⟩

/-- In a local ring, a nonempty family generating a principal ideal contains
an element generating that ideal. -/
private theorem exists_span_singleton_eq_of_isPrincipal
    {S ι : Type*} [CommRing S] [IsLocalRing S] [Nonempty ι]
    (I : Ideal S) (hI : I.IsPrincipal) (z : ι → S)
    (hz : Ideal.span (Set.range z) = I) : ∃ i, Ideal.span {z i} = I := by
  classical
  have hzmem (i : ι) : z i ∈ I := hz ▸ Ideal.subset_span ⟨i, rfl⟩
  by_cases hbot : I = ⊥
  · let i := Classical.choice (inferInstance : Nonempty ι)
    have hzi : z i = 0 := by simpa [hbot] using hzmem i
    exact ⟨i, by simp [hzi, hbot]⟩
  obtain ⟨b, hb⟩ := hI
  have hdiv (i : ι) : ∃ c : S, z i = b * c := by
    have h := hzmem i
    rw [hb, Ideal.mem_span_singleton] at h
    exact h
  choose c hc using hdiv
  by_cases hunit : ∃ i, IsUnit (c i)
  · obtain ⟨i, hi⟩ := hunit
    exact ⟨i, by rw [hc i, Ideal.span_singleton_mul_right_unit hi, hb]⟩
  have hmem (i : ι) : c i ∈ maximalIdeal S := fun h => hunit ⟨i, h⟩
  have hle : I ≤ maximalIdeal S • I := by
    rw [← hz]
    apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    rw [hc, Ideal.smul_eq_mul, mul_comm b (c i)]
    apply Ideal.mul_mem_mul (hmem i)
    rw [hz, hb]
    exact Ideal.subset_span rfl
  exact (hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (maximalIdeal S) I (hb ▸ Submodule.fg_span_singleton b) hle
      (maximalIdeal_le_jacobson ⊥))).elim

/-- A generating family of the arc kernel contains a generator at the generic
point, where the kernel ideal is principal. -/
theorem exists_generic_generator_in_family
    {A R ι : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Nonempty ι] (hA : ringKrullDim A = 2)
    (f : A →+* R) (hf : Function.Surjective f)
    (hgeneric : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk
      (Spec.map (CommRingCat.ofHom f) (genericPoint (Spec (.of R))))))
    (x : ι → A) (hx : RingHom.ker f = Ideal.span (Set.range x)) :
    letI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    ∃ k : ι, (RingHom.ker f).map
      (algebraMap A (Localization.AtPrime (RingHom.ker f))) =
        Ideal.span {algebraMap A (Localization.AtPrime (RingHom.ker f)) (x k)} := by
  let : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  let L := Localization.AtPrime (RingHom.ker f)
  obtain ⟨b, _, hb⟩ := exists_generator_of_regular_generic_kernel hA f hf hgeneric
  have hprincipal : ((RingHom.ker f).map (algebraMap A L)).IsPrincipal := hb ▸ inferInstance
  have hspan : Ideal.span (Set.range fun i => algebraMap A L (x i)) =
      (RingHom.ker f).map (algebraMap A L) := by
    rw [congrArg (Ideal.map (algebraMap A L)) hx, Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨k, hk⟩ := exists_span_singleton_eq_of_isPrincipal _ hprincipal _ hspan
  exact ⟨k, hk.symm⟩

/-- The product of two elements of an ideal lies in its square. -/
private theorem mul_mem_sq {A : Type u} [CommRing A] {p : Ideal A} {a b : A}
    (ha : a ∈ p) (hb : b ∈ p) : a * b ∈ p ^ 2 :=
  pow_two p ▸ Ideal.mul_mem_mul ha hb

/-- If `s` is congruent modulo `p` to a unit `u` times `x₁ ^ n`, then the relation
`s * xᵢ - a * x₂ ∈ p²` gives `x₁ ^ n * xᵢ - u⁻¹ * a * x₂ ∈ p²`. -/
private theorem power_relation_of_denominator_relation
    {A : Type u} [CommRing A]
    (p : Ideal A) (x₁ xᵢ x₂ s a : A) (n : ℕ) (u : Aˣ)
    (hxi : xᵢ ∈ p) (hden : s - (u : A) * x₁ ^ n ∈ p)
    (hrel : s * xᵢ - a * x₂ ∈ p ^ 2) :
    x₁ ^ n * xᵢ - (↑(u⁻¹) : A) * a * x₂ ∈ p ^ 2 := by
  convert Ideal.mul_mem_left (p ^ 2) (↑(u⁻¹) : A)
    (Ideal.sub_mem (p ^ 2) hrel (mul_mem_sq hden hxi)) using 1
  linear_combination (-(x₁ ^ n * xᵢ)) * u.inv_mul

/-- A relation in the localization at a prime clears to a relation in the original
domain. The extra denominator is cancellable because it lies outside the prime. -/
private theorem exists_denominator_relation_of_localized_equality
    {A : Type u} [CommRing A] [IsDomain A]
    (p : Ideal A) [p.IsPrime] (xᵢ x₂ : A)
    (b : Localization.AtPrime p)
    (h : algebraMap A (Localization.AtPrime p) xᵢ =
      b * algebraMap A (Localization.AtPrime p) x₂) :
    ∃ s : p.primeCompl, ∃ a : A, (s : A) * xᵢ = a * x₂ := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl b
  refine ⟨s, a, sub_eq_zero.mp ((IsLocalization.to_map_eq_zero_iff (M := p.primeCompl)
    (S := Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors).mp ?_)⟩
  rw [map_sub, map_mul, map_mul, h, ← mul_assoc, IsLocalization.mk'_spec', sub_self]

/-- If the prime ideal is generated by `x₂` after localizing at itself, every
generator of that prime is a multiple of `x₂` there; clearing denominators gives
the relation on the original ring. -/
private theorem exists_denominator_relation_of_localized_generator
    {A : Type u} [CommRing A] [IsDomain A]
    (p : Ideal A) [p.IsPrime] (xᵢ x₂ : A) (hxi : xᵢ ∈ p)
    (hgen : p.map (algebraMap A (Localization.AtPrime p)) =
      Ideal.span {algebraMap A (Localization.AtPrime p) x₂}) :
    ∃ s : p.primeCompl, ∃ a : A, (s : A) * xᵢ = a * x₂ := by
  have hmem : algebraMap A (Localization.AtPrime p) xᵢ ∈
      Ideal.span {algebraMap A (Localization.AtPrime p) x₂} :=
    hgen ▸ Ideal.mem_map_of_mem _ hxi
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  exact exists_denominator_relation_of_localized_equality p xᵢ x₂ b hb.symm

/-- In the quotient DVR, every nonzero denominator is a unit times a power of the
chosen uniformizer. Surjectivity lifts the unit, so the same factorization holds
modulo the kernel prime in the original local ring. -/
private theorem denominator_eq_unit_mul_uniformizer_power_mod_kernel
    {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [IsDomain R] [IsDiscreteValuationRing R]
    (f : A →+* R) (hf : Function.Surjective f) (p : Ideal A) [p.IsPrime]
    (hp : RingHom.ker f = p) (x₁ s : A)
    (hs : s ∉ p)
    (hπ : maximalIdeal R = Ideal.span {f x₁}) :
    ∃ (n : ℕ) (u : Aˣ), s - (u : A) * x₁ ^ n ∈ p := by
  have hlocal : IsLocalHom f := IsLocalHom.of_surjective f hf
  have hs0 : f s ≠ 0 := fun h => hs (hp ▸ RingHom.mem_ker.mpr h)
  have hπ0 : f x₁ ≠ 0 := fun h => IsDiscreteValuationRing.not_a_field R (by simp [hπ, h])
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (f x₁) hπ0 hπ)
  obtain ⟨u, hu⟩ := surjective_units_map_of_local_ringHom f hf hlocal v
  refine ⟨n, u, ?_⟩
  have huv : f (u : A) = (v : R) := congrArg Units.val hu
  rw [← hp, RingHom.mem_ker, map_sub, map_mul, map_pow, huv, hv]
  ring

/-- If the kernel prime is generated by `x₂` at its generic point, each chosen
element `xᵢ` of the kernel satisfies `x₁ ^ n * xᵢ - a * x₂ ∈ p²` for some `n` and `a`. -/
private theorem exists_power_relation_from_generic_generator
    {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [IsDomain A] [IsDomain R] [IsDiscreteValuationRing R]
    (f : A →+* R) (hf : Function.Surjective f) (p : Ideal A) [p.IsPrime]
    (hp : RingHom.ker f = p) (x₁ xᵢ x₂ : A)
    (hxi : xᵢ ∈ p)
    (hgen : p.map (algebraMap A (Localization.AtPrime p)) =
      Ideal.span {algebraMap A (Localization.AtPrime p) x₂})
    (hπ : maximalIdeal R = Ideal.span {f x₁}) :
    ∃ (n : ℕ) (a : A), x₁ ^ n * xᵢ - a * x₂ ∈ p ^ 2 := by
  obtain ⟨s, a, hs⟩ := exists_denominator_relation_of_localized_generator p xᵢ x₂ hxi hgen
  obtain ⟨n, u, hden⟩ :=
    denominator_eq_unit_mul_uniformizer_power_mod_kernel f hf p hp x₁ (s : A) s.2 hπ
  have hrel : (s : A) * xᵢ - a * x₂ ∈ p ^ 2 := by
    rw [hs]
    simp
  exact ⟨n, (↑(u⁻¹) : A) * a,
    power_relation_of_denominator_relation p x₁ xᵢ x₂ (s : A) a n u hxi hden hrel⟩

/-- Refine the relation obtained from the generic point so that both coefficients
are powers of the chosen parameter. The coefficient of the kernel generator may
vanish in the quotient DVR; in that case its contribution is already in `p²`. -/
private theorem exists_power_relation_with_two_exponents
    {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [IsDomain A] [IsDomain R] [IsDiscreteValuationRing R]
    (f : A →+* R) (hf : Function.Surjective f) (p : Ideal A) [p.IsPrime]
    (hp : RingHom.ker f = p) (x₁ xᵢ x₂ : A)
    (hxi : xᵢ ∈ p) (hx₂ : x₂ ∈ p)
    (hgen : p.map (algebraMap A (Localization.AtPrime p)) =
      Ideal.span {algebraMap A (Localization.AtPrime p) x₂})
    (hπ : maximalIdeal R = Ideal.span {f x₁}) :
    ∃ (n m : ℕ) (u : A), (u = 0 ∨ IsUnit u) ∧
      x₁ ^ n * xᵢ - u * x₁ ^ m * x₂ ∈ p ^ 2 := by
  obtain ⟨n, a, hrel⟩ := exists_power_relation_from_generic_generator
    f hf p hp x₁ xᵢ x₂ hxi hgen hπ
  by_cases ha : a ∈ p
  · refine ⟨n, 1, 0, Or.inl rfl, ?_⟩
    simpa using Ideal.add_mem (p ^ 2) hrel (mul_mem_sq ha hx₂)
  · obtain ⟨m, v, hfac⟩ := denominator_eq_unit_mul_uniformizer_power_mod_kernel
      f hf p hp x₁ a ha hπ
    refine ⟨n, m, ↑v, Or.inr v.isUnit, ?_⟩
    convert Ideal.add_mem (p ^ 2) hrel (mul_mem_sq hfac hx₂) using 1
    ring

/-- A finite family which generates a rank-one generic kernel admits a common
parameter-power relation to a single member. The coefficients are chosen by
principalizing their images in the quotient discrete valuation ring. -/
theorem exists_balanced_power_relations
    {A R ι : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Fintype ι] [Nonempty ι]
    (f : A →+* R) (hf : Function.Surjective f) (p : Ideal A) [p.IsPrime]
    (hp : RingHom.ker f = p) (a : A)
    (hπ : maximalIdeal R = Ideal.span {f a})
    (x : ι → A) (hx : ∀ i, x i ∈ p) (k₀ : ι)
    (hgen : p.map (algebraMap A (Localization.AtPrime p)) =
      Ideal.span {algebraMap A (Localization.AtPrime p) (x k₀)}) :
    ∃ (N : ℕ) (k : ι) (c : ι → A),
      ∀ i, a ^ N * x i - c i * a ^ N * x k ∈ p ^ 2 := by
  classical
  have hr (i : ι) : ∃ (n : ℕ) (b : A), a ^ n * x i - b * x k₀ ∈ p ^ 2 :=
    exists_power_relation_from_generic_generator f hf p hp a (x i) (x k₀)
      (hx i) hgen hπ
  choose n b hb using hr
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  let d : ι → A := fun i => if i = k₀ then a ^ N else a ^ (N - n i) * b i
  have hd (i : ι) : a ^ N * x i - d i * x k₀ ∈ p ^ 2 := by
    by_cases hi : i = k₀
    · subst i
      simp [d]
    · have h := Ideal.mul_mem_left (p ^ 2) (a ^ (N - n i)) (hb i)
      have he : a ^ (N - n i) * a ^ n i = a ^ N := by
        rw [← pow_add, Nat.sub_add_cancel (hn i)]
      convert h using 1
      dsimp [d]
      rw [if_neg hi, mul_sub, ← mul_assoc, he]
      ring
  let J : Ideal R := Ideal.span (Set.range fun i => f (d i))
  obtain ⟨k, hk⟩ := exists_span_singleton_eq_of_isPrincipal
    J (IsPrincipalIdealRing.principal J) (fun i => f (d i)) rfl
  have hc (i : ι) : ∃ c : A, d i - c * d k ∈ p := by
    have hmem : f (d i) ∈ Ideal.span {f (d k)} := by
      rw [hk]
      exact Ideal.subset_span ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmem
    obtain ⟨c, rfl⟩ := hf r
    refine ⟨c, ?_⟩
    rw [← hp, RingHom.mem_ker, map_sub, map_mul, hr]
    ring
  choose c hc using hc
  refine ⟨N, k, c, fun i => ?_⟩
  have hrel : a ^ N * (x i - c i * x k) ∈ p ^ 2 := by
    have h₁ := (p ^ 2).sub_mem (hd i) ((p ^ 2).mul_mem_left (c i) (hd k))
    (convert (p ^ 2).add_mem h₁ (mul_mem_sq (hc i) (hx k₀)) using 1; ring)
  (convert hrel using 1; ring)

end AlgebraicGeometry

end
